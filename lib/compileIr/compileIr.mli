open Frontend
open Ir

val of_node : Context.t -> Typed_ast.t_node -> Ast.node
(** Generate a node from a {!type:t_node} *)

val of_file : Typed_ast.t_file -> Context.t
(** Generate a context from a {!type:t_file} *)
