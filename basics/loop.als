/*
	var x = 1;  // 0 以上であること
	var y = 0;
	while(x > y) {
	  y = y + 1;
	  console.log("y is " + y);
	  console.log("x is " + x);
	}
	console.log("-- break --");
	x = y;
	console.log("y is " + y);
	console.log("x is " + x);
	console.log("fin.");
*/
open util/integer
sig Env { x,y: Int }

pred fin(x,y: Int) { x = y }

pred loopIdentity(x,y: Int) { x >= y }
pred loopBreak(x,y: Int) {
  (x = y and loopIdentity[x, y]) implies fin[x, y]
}
pred loopProc(x,y: Int) {
  loopIdentity[x, y + 1]
}
pred loopGoOn(x,y: Int) {
  not(x = y) and loopIdentity[x, y] implies loopProc[x, y]
}

pred start(x: Int) {
  loopIdentity[x, 0]
}

check {
  all env: Env | env.x >= 0 => start[env.x] 
  all env: Env | loopGoOn[env.x, env.y]
  all env: Env | loopBreak[env.x, env.y] 
}
/*
pred fin(x,y: Int) {
  eq[x, y]
}

pred loopIdentity(x,y: Int) {
  gte[x, y]
}
pred loopBreak(x,y: Int) {
  (eq[x, y] and loopIdentity[x, y]) implies fin[x, y]
}
pred loopProc(x,y: Int) {
  loopIdentity[x, add[y, 1]]
}
pred loopGoOn(x,y: Int) {
  not(eq[x, y]) and loopIdentity[x, y] implies loopProc[x, y]
}

pred start(x: Int) {
  loopIdentity[x, 0]
}

check {
  all env: Env | gte[env.x, 0] => start[env.x] 
  all env: Env | loopGoOn[env.x, env.y]
  all env: Env | loopBreak[env.x, env.y] 
}
*/
