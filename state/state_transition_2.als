abstract sig State {
  previous: lone State,
  visitor: one Visitor
  }
sig Idle extends State {} {
  previous = none
  }
sig Success extends State {} {
  previous != none
  }
sig Fail extends State { } {
  previous != none
  }
fact {
  /**
   * Successしたらその次のStateは無い。つまり、
   * Successがpreviousとして指されることはない。
   */
  no s:Success | s in State.previous 
  }
fact {
  all s:State | 
    let transitive = (^previous)[s] | // あるStateから、推移的に到達可能なprevious

      s not in Idle implies 
        /**
         * あるStateが、previousとして指すStateは、
         * 他のStateからはpreviousとして指されていないこと
         */
        s = previous.(s.previous)
 
        && 
        /**
         * 遷移の起点は必ずIdle。なので
         * あるStateから、推移的に到達可能なpreviousには、
         * 必ずIdleStateが含まれていないとおかしい.
         * （Idleのpreviousは無いので、Idleがtransitiveに含まれていれば、
         *  それは必ず起点であるといってよい）
         */
        transitive - Idle != transitive 
  }

/*------------------------------------------------------------*/
enum Password {correct, incorrect}
some sig UserAccount {
  // 照合の成否（状態？）
  password: one correct
  }
sig Session {
  whose: disj one UserAccount
  }
sig Visitor {
  // ログイン済みかどうか（状態？）
  signIn: disj lone Session,
  state: one State
  }
sig InputForm {
  /* 
   * Formをモデリングしているが、ログインという行為、即ちイベントであるともいえる。
   */
  currentVisitor: disj one Visitor,
  targetUser: one UserAccount,
  // 状態？
  input: targetUser -> one Password
  }

fact {
  all sess:Session | sess in Visitor.signIn
 }
fact {
  // サインインして記録されれるUserは、InputFormに入力されたUser
  all vis:Visitor | 
    vis.signIn != none implies
      vis.signIn.whose = (currentVisitor.vis).targetUser
  }
/*------------------------------------------------------------*/
fact {
  Visitor <: state = ~(State <: visitor)
 }
fact {
  // SuccessならSessionがあり、そうでなければSessionは無い。
  (all s:State | s in Success iff s.visitor.signIn != none) 
  &&
  // FailならInputFormはある。
  (all f:Fail | let v = f.visitor | ~(currentVisitor :> v)[v] != none)
  &&
  // IdleならInputFormは無い
  (all i:Idle | let v = i.visitor | ~(currentVisitor :> v)[v] = none)
  }

run {} for 6
