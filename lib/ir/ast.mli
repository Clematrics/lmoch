(** Describes the type of the values in a stream *)
type stream_type = Boolean | Integer | Real | Tuple of stream_type list

type stream = { name : string; ty : stream_type }
(** Stream description. The [name] is not garanteed to be unique but should be. *)

(** Term type *)
type term =
  | N  (** Time variable *)
  | Bool of bool
  | Int of int
  | Float of float
  | Var of stream * term
  | TupleTerm of term list
  | Function of string * term * term list
      (** Function with its name, its time expression and the list of arguments *)
  | Add of term list
  | Sub of term * term
  | Neg of term
  | Mul of term list
  | Div of term * term
  | Mod of term * term
  | IfThenElse of formula * term * term
  | IntOfReal of term
  | RealOfInt of term
  | Formula of formula * term
      (** A formula is annotated by a time term, useful for some transformations *)

and formula =
  | Term of term
  | Imply of formula * formula
  | And of formula list
  | Or of formula list
  | Not of formula
  | Equal of term list
  | NotEqual of term * term
  | Less of term * term
  | LessOrEqual of term * term
  | Greater of term * term
  | GreaterOrEqual of term * term

type node = {
  name : string;
  original_name : string;
  inputs : stream list;
  variables : stream list;
  outputs : stream list;
  equations : formula list;
}
(** Structure of a node *)

val print_term : Format.formatter -> term -> unit
(** Pretty-printing of a term *)

val print_formula : Format.formatter -> formula -> unit
(** Pretty-printing of a formula *)
