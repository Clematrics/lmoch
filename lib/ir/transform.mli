type t =
  | FullInlining
  | NoTuples
  | NoFormulaInTerm
      (** Transformations available on a node

          - {!constr:FullInlining} modifies a node to inline all nodes it
            contains. This transforms the node in place
          - {!constr:NoTuples} removes all tuple expressions from the equations
            of a node. It might inline other nodes if necessary (if the inputs
            or outputs contain tuples), but not if that node has equations with
            tuples.
          - {!constr:NoFormulaInTerm} removes formulas in terms, adding new
            streams with new equations such that the added streams are
            equivalent to the formulas. This transforms the node in-place.
            Necessary for the Alt-ergo Zero backend *)

val apply_transform : Context.t -> string -> t -> string
(** [apply_transform context name transform] applies a [transformation] to the
    node with [name] in the [context]. It returns the name of the node
    transformed. It might be the same one if the transformation is in-place. *)
