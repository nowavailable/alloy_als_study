# 記述のポイント

## 整数（自然数）の扱いについて

alloyでの整数（自然数）の扱いは不自由なので、alloy* http://alloy.mit.edu/alloy/hola/ を使用することで解決した。
 `Int` の値域の指定方式が、記述ルール上の、本家から拡張ポイント。

## 任意の数の様相データの作成

```
some 変数 : 型 | 〜
```
という記述方式は、複雑な条件でも自由に記述ができて便利。
だが、現出させるインスタンス数をコントロールできない。
それ故に、リスト機能なので、ソート条件をテストするのに、十分な数のデータを用意するのは苦手。

この問題に対しては、 `h9_order.als` では、以下のような対応をした。
```
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
```
 `some` を使わず、 `all` を使う。その代理変数を３つ定義して3つそれぞれに（同じ）制約づけをする。
 そうすることで、同じ制約に沿った3つの、IDの異なるデータを現出させている。
 
 ## `sum` の扱いについて
 
 動作が不安定？なので、その `sum` を補完するような条件を併用して、緩やかに絞り込む。
 
 ## その他
 - 受注候補店舗が、明細すべてに対して、全条件をクリアできていることを制約する `canRecieveDetailAll` は、
 まず `Order` 全体の候補店舗を対象とし、そこから、明細ごとの候補店舗を絞り込んでいる。
 - マスタ系の整数（自然数）は、値域を明示している。
 - 単項の絞り込みには、 `:>` が便利。
 
