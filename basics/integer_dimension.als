/*
  緯度経度を使って、現在地に近い地点と遠い地点をモデリング。
*/
sig Latitude { val: disj one Int }
sig Longitude { val: disj one Int }
// 緯度経度の1目盛りが、距離(km)と等価である世界観を構築。
abstract sig Distance { val: one Int }                     // 緯度差、経度差
one sig NorthSouthDistance extends Distance {} { val = 5 } // 5km相当の、緯度差を表現
one sig EastWestDistance extends Distance {} { val = 5 }   // 5km相当の、経度差を表現
// 汎用ロジック
one sig Zero { val: one Int } { val = 0 }
fun abs(num:Int) : one Int { num < 0 implies num.mul[-1] else num }

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
        latDiff <= NorthSouthDistance.val && lonDiff <= EastWestDistance.val implies
          s in Convenience.shops else
          s in NotConvenience.shops
}

run {} for 4 Int, 4 Place, 4 Latitude, 4 Longitude
