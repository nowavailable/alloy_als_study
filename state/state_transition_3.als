/*------------------------------------------------------------
 * 値オブジェクト（とイベント）
 *------------------------------------------------------------*/
enum Password {correct, incorrect}
some sig UserAccount {
  password: one correct
  }
sig Session {
  whose: disj one UserAccount
  }
sig Visitor {
  signIn: disj lone Session,

  /** 同一性担保のためのフィールド */
  identity: one Pkey

  }
sig InputForm {
  /* 
   * Formをモデリングしているが、ログインという行為、即ちイベントであるともいえる？
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

/*------------------------------------------------------------*/
sig Pkey { /*val: one Int*/ } { 
  /** Pkeyは、この場合、Visitorに保持されるかたちでのみ存在する。 */
  all pkey:Pkey | pkey in (Visitor<:identity)[Visitor]
  }

/*------------------------------------------------------------
 * 状態とその遷移
 *------------------------------------------------------------*/
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
  all s:(State - Idle) | 
    let transitive = (^previous)[s] | // あるStateから、推移的に到達可能なprevious
      /**
       * あるStateが、previousとして指すStateは、
       * 他のStateからはpreviousとして指されていないこと。反射的関係。
       */
      s = previous.(s.previous)
      /**
       * 遷移の起点は必ずIdle。なので
       * あるStateから、推移的に到達可能なpreviousには、
       * 必ずIdleStateが含まれていないとおかしい.
       * （Idleのpreviousは無いので、Idleがtransitiveに含まれていれば、
       *  それは必ず起点であるといってよい）
       */
      && 
      transitive - Idle != transitive 
  }

/*------------------------------------------------------------
 * 状態遷移と値オブジェクトとを組み合わせたときの制約
 *------------------------------------------------------------*/
fact transientBase {
  /**
   * 反射的関係。あるStateが指すVisitorは、
   * 他のStateからvisitorとして指されていないこと。
   */
  (all s:State | s = visitor.(s.visitor))
  /**
   * Visitorは必ずStateに保持されている。
   */
  &&
  all v:Visitor | v in (State <: visitor)[State]
  }
fact identified {
  /** 
   * 終端として参照されていないStateを起点にして 
   * そこから辿れるすべての状態に属するVisitorのidentityは同一。
   */
  let terminated = State - previous[State] |
    (all s:terminated | s.^previous.visitor.identity = s.visitor.identity)
    /** 
     * そのうえで且つ、終端状態の数とPkeyの数は同じであるはず。
     */
    && #(terminated) = #(Pkey)
  }
/** 
 * 状態を、値オブジェクトの様相でもって定義づける。
 */
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

run {} for 10
