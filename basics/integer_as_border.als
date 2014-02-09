/*
  石の上にも三年。
*/
abstract sig Border { val: one Int }
one sig BorderThree extends Border {} { val = 4 } // 0〜7
one sig BorderZero extends Border {} { val = 0 }

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
  // 開始年は過去である、等。
  all sYear:SinceYear, tYear:ThisYear | 
    tYear.val >= sYear.val && 
    sYear.val >= BorderZero.val
}
fact bizLogic {
  all c:Craftman, r:Rookie, f:FullGrown, y:ThisYear, b:BorderThree |
    let rGuys = r.guys, fGuys = f.guys |
      y.val.minus[c.sinceYear.val]  > b.val implies 
        c in fGuys else
        c in rGuys
}

run {} for 4 Int, 4 Craftman, 6 Year

