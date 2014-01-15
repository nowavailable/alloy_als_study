module self_referance
sig Current {
  // 複数インスタンスから参照されるpreviousは無い
  previous: disj lone Current
}
fact HistoryOfChain {
  // 自己参照結合時、自インスタンスは指さないこと。循環参照許容なら
  // no c: Current | c in c.previous
  // 循環参照禁止なら
  no c: Current | c in c.^previous
}
run {}
