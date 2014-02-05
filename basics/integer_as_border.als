/*
Intの定数は、この世界に登場し得る全てのIntを並べた順、および範囲、
の中で適切な設定を考えた結果のもの。
*/
one sig MinInterval { val: one Int  } { val = 4 }
//one sig Border { val: one Int } { val = 2 }
one sig Border { val: one Int } { val = 4 }
//one sig Border { val: one Int } { val >=  MinInterval.val.div[2]}
//one sig Border { val: one Int } { val = MinInterval.val.div[2]}

abstract sig Year { val: one Int }
one sig ThisYear extends Year {}
sig SinceYear extends Year {
  whose: one Craftman
}

sig Craftman {
  sinceYear: one SinceYear
} 

abstract sig Career {
  guys: set Craftman
}
one sig Rookie, FullGrown extends Career {}

fact generic {
  // CraftmanのsinceYearとして作用していないSinceYearは、不要。
  sinceYear = ~whose
  // rookieGuysとfullGrownGuysは互いに素。
  disj[Rookie.guys, FullGrown.guys]
  // 開始年は過去である。そして開始年と当年の間隔も設定された通りに空いていること。
  all sYear:SinceYear, tYear:ThisYear | 
    tYear.val >= sYear.val &&
    tYear.val.minus[sYear.val] >= MinInterval.val 
}
fact bizLogic {
  all c:Craftman, r:Rookie, f:FullGrown, y:ThisYear, b:Border |
    let rGuys = r.guys, fGuys = f.guys |
      y.val.minus[c.sinceYear.val]  > b.val implies 
        c in fGuys else
        c in rGuys
}

run {} for 4 Int, 4 Craftman, 6 Year
//run {} for 6 but 4 Int
