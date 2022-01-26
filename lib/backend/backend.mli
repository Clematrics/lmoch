open Ir

(** The interface of a backend *)

type time_term
(** The type of the time's term *)

type constraints
(** The type of constraints of a backend *)

type constraint_builder = time_term -> constraints
(** the type of a the function building [Delta_incr(n)] and [P_incr(n)] from a
    term [n] *)

type counter_example
type proof

exception FalseProperty of int * counter_example
exception TrueProperty of int * proof
exception DontKnow of int

val name : string

val required_transformations : Transform.t list
(** The list of transformations that are necessary. The order matters *)

val make_delta_p :
  Context.t -> string -> constraint_builder * constraint_builder
(** Function to build Delta_incr and P_incr from a context and the name of a
    node *)

val k_induction :
  ?max:int -> constraint_builder -> constraint_builder -> int -> 'a
(** [k_induction ~max delta_incr p_incr n] performs a k-induction starting from
    {i k=n}. The [max] value is set to 20 by default *)

val pp_counter_example : Format.formatter -> counter_example -> unit
(** Pretty-print a counter example given by an instance of the backend *)

val pp_proof : Format.formatter -> proof -> unit
(** Pretty-print a proof given by an instance of the backend *)
