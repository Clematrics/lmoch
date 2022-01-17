open Ir.Ast
open Aez
open Smt

val num_of_float : float -> Num.num

val make_delta_p :
  (node_id * node) list ->
  node ->
  (Smt.Term.t -> Formula.t) * (Smt.Term.t -> Formula.t)

exception FalseProperty of int
exception TrueProperty of int
exception DontKnow of int

val k_induction :
  ?max:node_id ->
  (Smt.Term.t -> Formula.t) ->
  (Smt.Term.t -> Formula.t) ->
  node_id ->
  'a
