open Frontend

module type Backend = sig
  type t
  type model
  type result = Unsat of model | Sat | Unknown

  val translate : t -> Typed_ast.t_node -> unit
  val solve : t -> result
end
