open Aez.Smt

val num_of_float : float -> Num.num

include
  module type of Backend
    with type time_term = Term.t
     and type constraints = Formula.t
(*
val make_delta_p :
  Context.t -> string -> (Smt.Term.t -> Formula.t) * (Smt.Term.t -> Formula.t)

exception FalseProperty of int
exception TrueProperty of int
exception DontKnow of int

val k_induction :
  ?max:int ->
  (Smt.Term.t -> Formula.t) ->
  (Smt.Term.t -> Formula.t) ->
  int ->
  'a *)
