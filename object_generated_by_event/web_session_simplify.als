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
fact {
  // サインインして記録されれるUserは、InputFormに入力されたUser
  all vis:Visitor | 
    vis.signIn != none iff
      vis.signIn.whose = (currentVisitor.vis).targetUser
}

run {} for 6
