open Ir.Ast
open Z3.Expr

val make_delta_p :
  (node_id * node) list -> node -> (expr -> expr list) * (expr -> expr list)

exception FalseProperty of int
exception TrueProperty of int
exception DontKnow of int

val k_induction :
  ?max:node_id -> (expr -> expr list) -> (expr -> expr list) -> node_id -> 'a
