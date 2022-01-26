open Aez.Smt

val num_of_float : float -> Num.num

include
  module type of Backend
    with type time_term = Term.t
     and type constraints = Formula.t
