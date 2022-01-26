(** Extension of the {!Stdlib.Int64} module, with some bit operators *)

include module type of Stdlib.Int64

val ( #+ ) : t -> t -> t
val ( #- ) : t -> t -> t
val ( #* ) : t -> t -> t
val ( #/ ) : t -> t -> t
val ( #% ) : t -> t -> t
val ( #& ) : t -> t -> t
val ( #| ) : t -> t -> t
val ( #^ ) : t -> t -> t
val ( #<< ) : t -> int -> t
val ( #>> ) : t -> int -> t
val extract : t -> int -> int -> t
val test_bit : t -> int -> bool
val pp_int64_bin : Format.formatter -> t -> unit
