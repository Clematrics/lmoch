open Ast

exception NameDuplicate of string

type t
(** A context contains all the nodes declared. It is garanteed that no nodes
    have the same name. This structure is modified in-place. *)

val create : unit -> t
(** Create a new context *)

val add : t -> node -> unit
(** [adds context node] adds a new [node] to the [context]

    @raise {!exception:NameDuplicate} if another node with the same name exists *)

val find : t -> string -> node
(** [find context name] finds the node with this [name] in the [context]

    @raise {!exception:Not_found} if no node with this [name] exists *)

val find_opt : t -> string -> node option
(** [find_opt context name] returns [Some node] if [node] has the [name] in the
    [context], or [None] if no such node exists *)

val replace : t -> node -> unit
(** [replace context node] changes the [node] with the same name in the
    [context], replacing the equations and variables.

    @raise {!exception:Not_found}
      if no node with this name exists in the [context] *)
