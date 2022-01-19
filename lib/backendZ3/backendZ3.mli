open Z3.Expr

include
  module type of Backend
    with type time_term = expr
     and type constraints = expr list

(*
   val make_delta_p :
     Context.t -> string -> (expr -> expr list) * (expr -> expr list)

   exception FalseProperty of int
   exception TrueProperty of int
   exception DontKnow of int

   val k_induction :
     ?max:int -> (expr -> expr list) -> (expr -> expr list) -> int -> 'a *)
