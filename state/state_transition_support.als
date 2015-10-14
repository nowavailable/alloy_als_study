/*------------------------------------------------------------
 * 状態とその遷移
 *------------------------------------------------------------*/
module state_transition_support[exactly vObj]

abstract sig State {
  previous: lone State
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

pred useStateTransition(stateExt:State) {
  Idle in stateExt && 
  Success in stateExt && 
  Fail in stateExt
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

/*------------------------------------------------------------*/
sig WatchedObj in vObj {
  /** 同一性担保のためのフィールド */
  identity: one Pkey
}
sig Pkey { /*val: one Int*/ } { 
  /** Pkeyは、この場合、Visitorに保持されるかたちでのみ存在する。 */
  all pkey:Pkey | pkey in (WatchedObj<:identity)[WatchedObj]
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

