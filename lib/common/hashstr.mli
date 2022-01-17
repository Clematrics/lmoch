module HashedString : sig
  include module type of String

  val equal : t -> t -> bool
  val hash : t -> int
end

include Hashtbl.S with type key = String.t
