module composite_unique_constraint
/**
 * 複合ユニーク制約の実現。（単独ユニークフィールドとの共存）
 */
/*
sig Entity_0 {
  disj pkey: one Int
}
*/
sig Entity_1 {
  field_a: one Int,
  field_b: one Int
}
fact {
  all e,e':Entity_1 |
    e != e' => e.field_a -> e.field_a != e'.field_a -> e'.field_a
}

run {} // for 6
