open Ir

(** The interface of a backend *)

type time_term
(** The type of the time's term *)

type constraints
(** The type of constraints of a backend *)

type constraint_builder = time_term -> constraints
(** the type of a the function building [Delta_incr(n)] and [P_incr(n)] from a
    term [n] *)

exception FalseProperty of int
exception TrueProperty of int
exception DontKnow of int

val required_transformations : Transform.t list
(** The list of transformations that are necessary. The order matters *)

val make_delta_p :
  Context.t -> string -> constraint_builder * constraint_builder
(** Function to build Delta_incr and P_incr from a context and the name of a
    node *)

val k_induction :
  ?max:int -> constraint_builder -> constraint_builder -> int -> 'a
