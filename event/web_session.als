enum Password {correct, incorrect}
some sig UserAccount {
  password: one correct
}
sig Session {
  whose: disj one UserAccount
}
sig Visitor {
  signIn: disj lone Session,
}

sig InputForm {
  currentVisitor: disj one Visitor,
  targetUser: one UserAccount,
  input: targetUser -> one Password
}

fact {
  all sess:Session | sess in Visitor.signIn
}
fact {
  all vis:Visitor |
   vis.signIn.whose in currentVisitor.vis.targetUser

}
/*
pred login[f:InputForm] {
  f.targetUser.(f.input) = f.targetUser.password 
    iff f.currentVisitor.signIn in Session
  &&
  !(f.targetUser.(f.input) != f.targetUser.password 
      iff f.currentVisitor.signIn = none)
}
check Login {
  all f:InputForm |
    !login[f]
    implies 
      f.targetUser.(f.input) = incorrect && f.currentVisitor.signIn = none
}

*/
fact {
  all f:InputForm |
    f.targetUser.(f.input) = f.targetUser.password 
      iff f.currentVisitor.signIn in Session
    ||
    f.targetUser.(f.input) != f.targetUser.password 
      iff f.currentVisitor.signIn = none
}

run {}
