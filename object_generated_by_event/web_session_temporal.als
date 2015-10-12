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

/*
*/
fact {
  // ログイン済み者と未ログイン/ログイン失敗者がいる。
  all vis:Visitor |
    vis.signIn.whose in currentVisitor.vis.targetUser
}

fact {
  // ログイン済み者と未ログイン/ログイン失敗者がいる。
  all f:InputForm |
    f.targetUser.(f.input) = f.targetUser.password 
      iff f.currentVisitor.signIn in Session
    ||
    f.targetUser.(f.input) != f.targetUser.password 
      iff f.currentVisitor.signIn = none
}

run {}
