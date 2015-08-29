module many_to_many
sig Movie {
  mv_act: set MoviesActors
} 
sig Actor {
  act_mv: set MoviesActors
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
