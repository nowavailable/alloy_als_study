open h9
module h9_order
/*-------------------------------------------------------------------------------------------*/
-- ビジネスロジック上自明な
fact {
  -- 未決の注文明細の日付は、本日以降であること。
  all d: OrderDetail | eq[#(d<:requested_deliveries), 0] => gt[d.expected_date.val, Now.val]
  -- 配達希望日は注文日より未来
  all o: Order |
    all e_date: o.order_details.expected_date | gt[e_date.val, o.ordered_at.val]
  -- 取扱がある店が配達 
  -- TODO: 取り扱い終了もありえるけどそれは？
  all r: RequestedDelivery |
    (r.shop.rule_for_ships<:merchandise:>r.order_detail.merchandise).Merchandise != none

  -- 値の異なっていて欲しい、マスタ系レコード
  all c,c': City | c != c' => not eq[c.label.val, c'.label.val]
  all s,s': Shop | s != s' => not eq[s.label.val, s'.label.val] && not eq[s.code.val, s'.code.val]
  all m,m': Merchandise | m != m' => not eq[m.label.val, m'.label.val]
  -- コードの一貫性
  all d: OrderDetail |
    let codVal = d.order.order_code.val |
    all req, req': d.requested_deliveries.order_code.val |
      req != req' => eq[req.order_code.val, req'.order_code.val]
        && eq[req.order_code.val, codVal]
  -- 明細がすべて未決の注文もある。
  some o: Order | o.order_details.requested_deliveries = none
  //-- 部分的に明細が未決の注文は、無いものとする？あるいは許容？
  //one o: Order | not eq[#(o.order_details.requested_deliveries), #(o.order_details)]
}
-- 数量整合性
fact {
  -- 数量のキャパシティに沿った受注がなされていること
  -- TODO: 数量のキャパシティ変更もありえるけどそれは？
  all req: RequestedDelivery |
    lte[req.quantity.val, QUANTITY_LIMIT_BY_REQ[req].val]
  all d: OrderDetail |
    (
      -- 配達指示の個数が注文明細の個数と合っていること
      eq[#(d<:requested_deliveries), 1] implies
        all req: d.requested_deliveries | eq[d.quantity.val, req.quantity.val]
    ) && (
      -- また、ひとつの注文明細に複数の配達指示がある場合、
      -- そのどちらかはRuleForShipのリミットに達している
      gt[#(d<:requested_deliveries), 1] iff
        gt[d.quantity.val, 1]
        && (let req = d.requested_deliveries |
          gte[#(req.quantity.val:>(QUANTITY_LIMIT_BY_REQ[req].val)), 1])
        -- 配達指示の個数が注文明細の個数合計と合っていること
        && eq[d.quantity.val, sum[d.requested_deliveries.quantity.val]]
    )
}
-- 配達可能地域
fact {
  all d: OrderDetail |
    -- 配達可能地域定義に沿った受注がなされていること
    -- TODO: 配達可能地域定義の変更のありえるけどそれは？
    OrderDetail.(d<:requested_deliveries.shop) in CAN_DELIVERY_SHOPS[d]
}
-- 配達リソース整合性
fact {
  all shop: Shop |
    all date: Shop.(shop<:requested_deliveries.order_detail.expected_date) |
      let theDay = (Boundary<:val:>(date.val)).Int,
        limit = shop.ship_limits, 
        details = shop.requested_deliveries.order_detail |
      -- 配達実績数は日毎配達可能数と矛盾していない。
      -- TODO: 日毎配達可能数の変更もありえるけどそれは？
      eq[#((details<:expected_date.val):>theDay.val), shop.delivery_limit_per_day.val]
        -- 配達実績とship_limitsの数が一致している。
        && lte[#((details<:expected_date.val):>theDay.val), #((limit<:expected_date.val):>theDay.val)]
}
/*-------------------------------------------------------------------------------------------*/
-- その日は既にふさがっている
pred theDayIsFull(date: Boundary, shop: Shop) {
  let theDay = (Boundary<:val:>(date.val)).Int,
    limit = shop.ship_limits,
    details = shop.requested_deliveries.order_detail |
  not eq[#((limit<:expected_date.val):>theDay.val), 0]
    -- さらに配達実績数が日毎配達可能数と矛盾していないか見る。
    // 厳密にチェックするならね
    //&& gte[#((details<:expected_date.val):>theDay.val), shop.delivery_limit_per_day.val]
}
-- 受注候補店舗が、明細すべてに対して、全条件をクリアできている
pred canRecieveDetailAll(o: Order, candidate_shop: Shop) {
  all detail: o.order_details |
    let rule = (candidate_shop.rule_for_ships<:merchandise:>detail.merchandise).Merchandise |
      (rule != none)
      -- 明細完受注可
      && gte[QUANTITY_LIMIT[detail.expected_date, rule].val, detail.quantity.val]
      && candidate_shop in CAN_DELIVERY_SHOPS[detail]
      // candidate_shopは、"Orderで"束ねた群なのでさらに絞る
      && candidate_shop in detail.merchandise.rule_for_ships.shop
      && not theDayIsFull[detail.expected_date, candidate_shop]
}
-- 明細完受注NG店舗在り
pred canRecieveDetailPartly(d: OrderDetail) {
  (some rule: d.merchandise.rule_for_ships |
    not gte[QUANTITY_LIMIT[d.expected_date, rule].val, d.quantity.val]
    and rule.shop in CAN_DELIVERY_SHOPS[d]
    and not theDayIsFull[d.expected_date, rule.shop]
  ) //and (
    //some rule: d.merchandise.rule_for_ships |
    //  gte[QUANTITY_LIMIT[d.expected_date, rule].val, d.quantity.val]
    //  and rule.shop not in CAN_DELIVERY_SHOPS[d]
    //  and not theDayIsFull[d.expected_date, rule.shop]
  //)
}
/*-------------------------------------------------------------------------------------------*/
-- 数量リミット
fun QUANTITY_LIMIT(date: Boundary, rule: RuleForShip) : Boundary {
  gte[date.val.minus[Now.val], rule.interval_day.val] implies
    rule.quantity_limit else rule.quantity_available
}
fun QUANTITY_LIMIT_BY_REQ (req: RequestedDelivery) : one Boundary {
  let rule = (req.shop.rule_for_ships<:merchandise:>req.order_detail.merchandise).Merchandise |
    QUANTITY_LIMIT[req.order_detail.expected_date, rule]
}
-- そこにそれを配達が可能な店舗
fun CAN_DELIVERY_SHOPS (d: OrderDetail) : set Shop {
  CitiesShop.(((CitiesShop<:city:>d.city).City)<:shop)
}
/*-------------------------------------------------------------------------------------------*/
-- テスト上恣意的な
fact {
  -- quantity系としきい値系はなるべく小さく。
  all r: RuleForShip | lte[r.interval_day.val, 4] 
    && lte[r.quantity_limit.val, 6] && lte[r.quantity_available.val, 6]
  all s: Shop | lte[s.delivery_limit_per_day.val, 6]
  all d: OrderDetail | lte[d.quantity.val, 8] 
  all r: RequestedDelivery | lte[r.quantity.val, 6]
  -- 出荷ルールの多様性
  all r,r': RuleForShip |
    r != r' => not eq[r.quantity_limit.val, r'.quantity_limit.val]
      && not eq[r.quantity_available.val, r'.quantity_available.val]
  -- マージンの多様性
  all s,s': Shop | s != s' => not eq[s.mergin.val, s'.mergin.val]
  -- 複数分担の配達指示
  some d: OrderDetail | gt[#(d<:requested_deliveries), 1]
  -- 配達先のカーディナリティ
  gt[#(CitiesShop.city), 3]
  -- 配達指示はいくつか発されている。
  gte[#(RequestedDelivery), 3]
  -- ひとつの明細が複数の配達にわかれている例が
  some d: OrderDetail | gte[#d.requested_deliveries, 2]
}
-- 受注余力があって、まだ受注していない店舗がいくつかあること
pred notYetDetailsAndShopsAll {
  some o: Order | 
    (o.order_details.requested_deliveries = none) 
    && (o.order_details.merchandise.rule_for_ships.shop != none)
    && let candidates = o.order_details.merchandise.rule_for_ships.shop |
      /** 受注候補店舗が3つ以上ある状態を作る */
      gt[#candidates,3]
      && all candidate1, candidate2, candidate3: candidates |
        (candidate1 != candidate2) 
        && (candidate2 != candidate3) 
        && (candidate1 != candidate3) implies
          canRecieveDetailAll[o,candidate1] 
          && canRecieveDetailAll[o,candidate2] 
          && canRecieveDetailAll[o,candidate3]
}
pred notYetDetailsAndShopsPartly {
  some o: Order | (o.order_details.requested_deliveries = none) 
    && (some d: o.order_details | canRecieveDetailPartly[d])
}

// run での sig の絞り込みは最小限に。また、
// 全体のscope数と大きく差のあるsig絞り込みを設定すると、正しく動作しないことがある。
// なおこのalsは alloy* (alloystar) での実行を前提としている。
run {
  notYetDetailsAndShopsAll
  // notYetDetailsAndShopsPartly
} for 8 but 5 City, 3 ShipLimit, // 4 Merchandise, 
1..20 Int, 20 seq
//5 Int, 15 seq
