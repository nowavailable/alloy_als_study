module one_to_one
sig Dad {
  son: lone Son
}
sig Son {
  dad: one Dad
}
fact RelDadSon {
  // 相互的な参照には必須
  // 「"父を持つ子"の、親子関係を反転させると、それは"子を持つ父"に等しい」
  Dad <: son = ~(Son <: dad)
}
run {} //for 5
