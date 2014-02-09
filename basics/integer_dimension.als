// 距離(km)
abstract sig Border { val: one Int }
one sig DistanceNorthSouth extends Border {} { val = 5 } // 0〜7
one sig DistanceEastWest extends Border {} { val = 5 } // 0〜7
one sig Zero extends Border {} { val = 0 }
fun abs(num:Int) : one Int { num < 0 implies num.mul[-1] else num }

// 緯度経度の1目盛りが、距離(km)と等価である世界観を構築。
sig Latitude { val: one Int }
sig Longitude { val: one Int }

abstract sig Place {
  lat: one Latitude,
  lon: one Longitude
}
one sig CurrentPlace extends Place {
} {
  lat.val = Zero.val
  lon.val = Zero.val
}
sig Shop extends Place {}

one sig Convenience {
  shops: set Shop
}
one sig NotConvenience {
  shops: set Shop
}

fact generic {
  all lt: Latitude | lt in Place.lat
  all ln: Longitude | ln in Place.lon
}
fact bizLogic {
  all conv:Convenience, notConv:NotConvenience |
    disj[conv.shops, notConv.shops]
  all c:CurrentPlace, s:Shop |
    let latDiff = abs[s.lat.val.minus[c.lat.val]], 
      lonDiff = abs[s.lon.val.minus[c.lon.val]] |
        latDiff <= DistanceNorthSouth.val && lonDiff <= DistanceEastWest.val implies
          s in Convenience.shops else
          s in NotConvenience.shops
}
run {} for 4 Int
