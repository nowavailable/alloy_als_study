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
  // actor と movie の複合ユニーク制約なし。つまり無駄なMoviesActorsが生じうる状態。
}
run {}
