/*
	var a, x, y;
	// 1) 代入その一
	a = x + 1;
	// 2) 分岐
	if (a == 1) {
	    y = 1;
	} else {
	    y = a;
	}
	// 3) 代入その二
	y = x + 1;
 */
open util/integer
sig Env { x: Int }

pred fin [x,y: Int] {
  // 3) の事後
  eq[y, x + 1]
}
pred proc_1 (x,a: Int) {
  // 2) の事後 = if文そのもの && 3) の事後に引数を渡す
  ((a = 1 and fin[x,1]) or (a != 1 and fin[x,a]))
}
pred start (x: Int) {
  // 1) の事後 = 2) の事後に引数を渡す
  proc_1[x, x + 1]
}

run { all env: Env | start[env.x]}
check { all env: Env | start[env.x]}

/*
pred fin [x,y: Int] {
  // 3) の事後
  eq[y, add[x,1]]
}
pred proc_1 (x,a: Int) {
  // 2) の事後 = if文そのもの && 3) の事後に引数を渡す
  ((eq[a,1] and fin[x,1]) or (not(eq[a,1]) and fin[x,a]))
}
pred start (x: Int) {
  // 1) の事後 = 2) の事後に引数を渡す
  proc_1[x,add[x,1]]
}
*/
