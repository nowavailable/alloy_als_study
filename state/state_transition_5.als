open state_transition_support_2[ValueObj, Event]

/*------------------------------------------------------------
 * 値オブジェクト（とイベント）
 *------------------------------------------------------------*/
module main
abstract sig ValueObj {}
abstract sig Event {}

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
sig InputForm extends Event {
  /* 
   * Formをモデリングしているが、
   * ログインという行為、即ちイベントであるともいえる？
   */
  currentVisitor: disj one Visitor,
  targetUser: one UserAccount,
  input: targetUser -> one Password
}

fact {
  all sess:Session | sess in Visitor.signIn
}
fact {
  // サインインして記録されるUserは、InputFormに入力されたUser
  all vis:Visitor | 
    vis.signIn != none implies
      vis.signIn.whose = (currentVisitor.vis).targetUser
}

/*------------------------------------------------------------
 * 状態とその遷移 ボイラープレート
 *------------------------------------------------------------*/
// 状態が参照するSigを、フィールドとして持つホルダー。
// それを、Stateを継承して作成。
sig StateExt in State {
  visitor: one Visitor
}
fact {
  Visitor in WatchedObj &&
  useStateTransition[StateExt] && 
  transientBasic[visitor]
}
/*------------------------------------------------------------
 * 状態の発火者を定義
 *------------------------------------------------------------*/
fact stateIgniter {
  all s:StateExt | 
    s.igniter != none implies 
      igniter[s] = ~currentVisitor[s.visitor]
}
/*------------------------------------------------------------
 * 状態遷移と値オブジェクトとを組み合わせたときの制約
 * 状態を、値オブジェクトの様相でもって定義づける。
 *------------------------------------------------------------*/
fact businessLogic {
  // SuccessならSessionがあり、そうでなければSessionは無い。
  (all s:State | s in Success iff s.visitor.signIn != none) 
  &&
  // FailならInputFormはある。
  (all f:Fail | let v = f.visitor | ~(currentVisitor :> v)[v] != none)
  &&
  // IdleならInputFormは無い
  (all i:Idle | let v = i.visitor | ~(currentVisitor :> v)[v] = none)
}

run {} for 7
