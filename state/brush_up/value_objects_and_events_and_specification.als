open state_transition_support

module main
/*------------------------------------------------------------
 * （入出力に絡む？）状態群
 *------------------------------------------------------------*/
sig Idle extends State {} {
  igniter = none && 
    previous = none  // 推移の性質を定義
}
sig Success extends State {} {
  igniter != none &&
    previous != none  // 推移の性質を定義
}
sig Fail extends State {} {
  igniter != none &&
    previous != none  // 推移の性質を定義
}
// 有限状態であることを制約するなら
fact {
  Idle in State && 
    Success in State && 
      Fail in State
}
/*------------------------------------------------------------
 * ユーザーランドのモデル群
 *------------------------------------------------------------*/
enum Password {correct, incorrect}
some sig UserAccount extends ValueObj {
  password: one correct
}
sig Session extends ValueObj {
  whose: disj one UserAccount
}
sig Visitor extends ValueObj {
  signIn: disj lone Session
}
// 同一性をチェックする対象のエンティティはこうする。
fact {
  Visitor in WatchedObj
}

/* 
 * Formをモデリングしているが、
 * ログインという行為、即ちイベントであるともいえる？
 */
sig InputForm extends Event {
  currentVisitor: disj one Visitor,
  targetUser: one UserAccount,
  input: targetUser -> one Password
}

/* 
 * その他ビジネスルール
 */
fact local_1 {
  all sess:Session | sess in Visitor.signIn
}
fact local_2 {
  // サインインして記録されるUserは、InputFormに入力されたUser
  all vis:Visitor | 
    vis.signIn != none implies
      vis.signIn.whose = (currentVisitor.vis).targetUser
}
fact local_3 {
  /**
   * 各状態を、値オブジェクトの様相でもって定義づける。
   *   （※状態sig毎に独立して記述したほうがよい？）
   */
  // SuccessならSessionがあり、そうでなければSessionは無い。
  (all s:State | s in Success iff s.visitor.signIn != none)  &&
    // FailならInputFormはある。
    (all f:Fail | let v = f.visitor | ~(currentVisitor :> v)[v] != none)  &&
      // IdleならInputFormは無い
      (all i:Idle | let v = i.visitor | ~(currentVisitor :> v)[v] = none)
}

/*------------------------------------------------------------
 * ボイラープレート？
 * 状態と各種エンティティを、結びこむ。
 *------------------------------------------------------------*/
sig StateExt in State {
  visitor: one Visitor
}
// 状態の発火者と各種エンティティを、結びこむ必要がある。（直感的には分かりにくい）
fact stateIgniter {
  all s:StateExt | 
    s.igniter != none implies 
      // 各状態の発火者（存在すれば）は、その状態に属するVisitor　が操作したイベント。
      igniter[s] = (~(InputForm<:currentVisitor))[s.visitor]
}
/*------------------------------------------------------------
 * 状態遷移そのものの表現
 *------------------------------------------------------------*/
// 推移的なやつのときは以下を
fact {
  transientBasic[visitor] && 
    終端設定[Success] && 
      推移閉包設定[Idle]
}

/** TODO: 推移上、隣接する状態の、繰返し数制限 */


run {} for 7
