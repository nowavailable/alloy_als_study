# 記述のポイント

## 整数（自然数）の扱いについて

alloyでの整数（自然数）の扱いは不自由なので、alloy* http://alloy.mit.edu/alloy/hola/ を使用することで解決した。
 `Int` の値域の指定方式が、記述ルール上の、本家から拡張ポイント。

## 任意の数の様相データの作成（一律同じ条件で）

```
some 変数 : 型 | 〜
```
という記述方式は、複雑な条件でも自由に記述ができて便利。
だが、現出させるインスタンス数をコントロールできない。
それ故に、リスト機能なので、ソート条件をテストするのに、十分な数のデータを用意するのは苦手。

この問題に対しては、 `allDetailOK.als` および `partlyOKVariation.als` では、以下のような対応をした。
```
--
-- 注文明細すべてを受けられる店舗が複数ある.
--
pred allDetailOK {
  some o: Order | 
    (o.order_details.requested_deliveries = none) 
    && gt[#o.order_details, 1]
    && (o.order_details.merchandise.rule_for_ships.shop != none)
    && let candidates = o.order_details.merchandise.rule_for_ships.shop |
      /** 受注候補店舗が3つ以上ある状態を作る。
          同一制約下で、任意の数のatomインスタンスを確保する方策 */
      gt[#candidates,3]
      && all disj candidate1, candidate2, candidate3: candidates |
        canRecieveAllDetail[o,candidate1] 
        && canRecieveAllDetail[o,candidate2] 
        && canRecieveAllDetail[o,candidate3]
}
```
 `some` を使わず、 `all disj` を使う。互いに素なエイリアス変数を3つ定義して、3つそれぞれに（同じ）制約づけをする。
 そうすることで、同じ制約に沿った異なるデータを、確実に3つ、現出させている。
 
## 任意の数の様相データの作成（各々異なる条件で）

上記の `all disj` を使う方式だと、各エイリアス変数に、各々異なる条件を与える場合にはうまく動作しない。
そこで、 `allDetailOKAndPartlyOK.als` では、次のようなやり方を採った。
```--
-- 注文完受注可能店舗と、明細のみ完受注可能店舗の混在する状態
--
pred allOKAndPartlyOK {
  some o: Order | 
    (o.order_details.requested_deliveries = none) 
    && (o.order_details.merchandise.rule_for_ships != none)
    // ここがキモ。エイリアスと結び込み。
    && (CandidateShop.shops[Int] = o.order_details.merchandise.rule_for_ships.shop)
    && eq[#CandidateShop.shops, 3]
    && lte[#o.order_details, 3]
    // 注文完受注可能店舗
    && canRecieveAllDetail[o, CandidateShop.shops.subseq[0,0][Int]] 
    // 明細のみ完受注可能店舗
    && (some detail: o.order_details |
      canRecieveDetailComplete[o, CandidateShop.shops.subseq[1,1][Int], detail])
    && not canRecieveAllDetail[o, CandidateShop.shops.subseq[1,1][Int]] 
    && (some detail: o.order_details |
      canRecieveDetailComplete[o, CandidateShop.shops.subseq[2,2][Int], detail])
    && not canRecieveAllDetail[o, CandidateShop.shops.subseq[2,2][Int]] 
}
/** エイリアス用途のsig。
    atomインスタンスを指定して、別々の制約を与えるために。 */
sig CandidateShop { shops: seq Shop}
fact { 
  // FIXME: 上記のseq、放っとくと、シーケンス（Int）とShopが1:nになったり、
  // 同じShopが何度も出現してしまったりするので
  // ・インデックスがユニ−クであること→要素数とインデックス数とが等しければそうなる。
  // ・要素が（このフィ−ルド全体として）ユニ−クであること
  // を制約づける必要がある。もっとよい書き方は無いか。
  eq[#CandidateShop.shops.inds, #CandidateShop.shops.elems] 
  && eq[#CandidateShop.shops, #CandidateShop.shops.inds]
}
```
任意のatom群 `o.order_details.merchandise.rule_for_ships.shop` を、
 `seq` を持つ、別sigの別フィールドへのマッピングを制約付ける。
 こうすることで、別sigを経由して（別sigのフィールド要素に `subseq` 関数を利用してアクセスして）
 任意のatomそれぞれに別の制約付けをおこなうことが可能になる。

 ## `sum` の扱いについて
 
 動作が不安定？なので、その `sum` を補完するような条件を併用して、緩やかに絞り込む？
 
 ## その他
 - 受注候補店舗が、明細すべてに対して、全条件をクリアできていることを制約する `canRecieveDetailAll` は、
 まず `Order` 全体の候補店舗を対象とし、そこから、明細ごとの候補店舗を絞り込んでいる。
 - マスタ系の整数（自然数）は、値域を明示している。
 - 単項の絞り込みには、 `:>` が便利。
 
