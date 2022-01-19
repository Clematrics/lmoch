(** Describes the type of the values in a stream *)
type stream_type = Boolean | Integer | Real | Tuple of stream_type list

type stream = { name : string; ty : stream_type }

type term =
  | N (* time *)
  | Bool of bool
  | Int of int
  | Float of float
  | Var of stream * term
  | TupleTerm of term list
  | Function of string * term * term list (* name * time * args *)
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
(* the term indicates the local time of this formula *)

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
val print_formula : Format.formatter -> formula -> unit
