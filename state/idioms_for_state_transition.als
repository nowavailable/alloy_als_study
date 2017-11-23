module main

// Boundaryは、何らかの1次元の位置、つまり何らかの値を表す。
sig Boundary { val: one Int }  
sig Entity {
  some_field: one Boundary,
  // 状態変化を表現することを目的に付加したフィールド
  meta_identifier: one Int,
  meta_state: one Int
}

fact {
  /** meta_state は、-1か0しかない。つまり、事前と事後。*/
  all e:Entity | e.meta_state = 0 or e.meta_state = -1
  /** 
   ID が等しいふたつAtomがあったら、
   それはひとつのAtomの事前状態と事後状態であると考える。
  */
  all e,e':Entity |
    (e != e' and e.meta_identifier = e'.meta_identifier) => 
      (e.meta_state != e'.meta_state)
}

run {} for 3 but 4 Entity, 3 Int
