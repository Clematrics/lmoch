open Z3.Expr

include
  module type of Backend
    with type time_term = expr
     and type constraints = expr list
