module composite_foreign_keys
/**
 * 複合ユニーク外部キー（および複合ユニーク制約）の表現。
 */
sig Actor {
  charactors: set Charactor
}
sig Movie {
  charactors: set Charactor
}
sig Charactor {
  actor: lone Actor,
  movie: lone Movie,
  novelty_items: set NoveltyItem
}
sig NoveltyItem {
  charactor: one Charactor
}

fact {
  Actor<:charactors = ~(Charactor<:actor)
  Movie<:charactors = ~(Charactor<:movie)
  Charactor<:novelty_items = ~(NoveltyItem<:charactor)
  all e,e':Charactor | e != e' => (e.actor -> e.movie != e'.actor -> e'.movie)
  all e,e':NoveltyItem | e != e' => (e.charactor.actor -> e.charactor.movie != e'.charactor.actor -> e'.charactor.movie)
}

run {}
