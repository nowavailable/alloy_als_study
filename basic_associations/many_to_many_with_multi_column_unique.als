module many_to_many
sig Movie {
  actors: set Actor,    // rdb-orientedな観点からは、省略可。
  mv_act: set MoviesActors
} {
  actors = mv_act.actor // ショートカット。rdb-orientedな観点からは、省略可。
}
sig Actor {
  movies: set Movie,    // rdb-orientedな観点からは、省略可。
  act_mv: set MoviesActors
} { 
  movies = act_mv.movie // ショートカット。rdb-orientedな観点からは、省略可。
}
sig MoviesActors {
  actor: one Actor,
  movie: one Movie
}
fact { 
  // 相互的な参照関係
  Movie <: mv_act = ~(MoviesActors <: movie)
  Actor <: act_mv = ~(MoviesActors <: actor)
  // 中間テーブルが作る関連は、互いに素。つまりactor と movie の複合ユニーク制約と同等。
  all disj ms, ms': MoviesActors | ms.(MoviesActors<:movie + MoviesActors<:actor) != ms'.(MoviesActors<:movie + MoviesActors<:actor)
}
run {}
