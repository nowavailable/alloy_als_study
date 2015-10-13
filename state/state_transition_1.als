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

run {} for 8
