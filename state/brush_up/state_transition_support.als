/*------------------------------------------------------------
 * 状態とその遷移
 *------------------------------------------------------------*/
module state_transition_support

/*------------------------------------------------------------
 * 基本エンティティ
 *------------------------------------------------------------*/
abstract sig ValueObj {}
abstract sig Event {}

sig WatchedObj in ValueObj {
  /** 同一性担保のためのフィールド */
  identity: one Pkey
}
sig Pkey { /*val: one Int*/ } { 
  /** Pkeyは、この場合、Visitorに保持されるかたちでのみ存在する。 */
  all pkey:Pkey | pkey in (WatchedObj<:identity)[WatchedObj]
}

abstract sig State {
  previous: lone State,  // TODO: ユーザーランドへ？
  igniter: lone Event
}

/*------------------------------------------------------------
 * 推移的なやつ
 *------------------------------------------------------------*/
pred 終端設定(terminal: State) {
  /**
   * Successしたらその次のStateは無い。つまり、
   * Successがpreviousとして指されることはない。
   */
  no s:terminal | s in State.previous 
}

pred 推移閉包設定(idol: State) {
  all s:(State - idol) | 
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
      transitive - idol != transitive 
}

pred transientBasic(refferdFeild: State->WatchedObj) {
  /**
   * 反射的関係。あるStateが指すVisitorは、
   * 他のStateからvisitorとして指されていないこと。
   */
  (all s:State | s = refferdFeild.(s.refferdFeild))
  /**
   * Visitorは必ずStateに保持されている。
   */
  &&
  all v:WatchedObj | v in refferdFeild[State]
  &&
  (
  /** 
   * 終端、つまり、previousとして参照されていないStateを起点にして 
   * そこから辿れるすべての状態に属するVisitorのidentityは同一。
   */
  let terminated = State - previous[State] |
    (all s:terminated | s.^previous.refferdFeild.identity = s.refferdFeild.identity)
    /** 
     * そのうえで且つ、終端状態の数とPkeyの数は同じであるはず。
     */
    && #(terminated) = #(Pkey))
}

