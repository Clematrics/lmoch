(** Module type encapsulating some state *)
module type STATE = sig
  type t
  (** The type of a state *)

  val attach : 'a -> t -> t * 'a
  (** [attach x state] binds the result of a function with a state *)
end

(** Functor generating functions to manage states transparently in the code *)
module Make (State : STATE) : sig
  val ( let* ) :
    (State.t -> State.t * 'a) -> ('a -> State.t -> 'b) -> State.t -> 'b
  (** Let-binding to mask state passing. To return the state at the end, the
      {!val:(!)} can be used. If the state must be recovered, use a function
      taking the state as a parameter.

      Example, without explicit state manipulation:

      {[
        let func x y state =
        	let f, g = (fun x state -> state, x), (fun y state -> state, y)
        	state
        	|>	let* x = f x in
        		let* y = g y in
        		! (x + y)
      ]}

      Example, with state manipulation:

      {[
        let func x y state =
        	let f, g = (fun x state -> state, x), (fun y state -> state, y)
        	state
        	|>	let* x = f x in
        		let* y = g y in
        		function state ->
        			! (x + y) (change state)
      ]}

      Because [state] is the last argument of [func], it can be omitted

      {[
        let func x y =
        	let f, g = (fun x state -> state, x), (fun y state -> state, y)
        	let* x = f x in
        	let* y = g y in
        	! (x + y)
      ]} *)

  val map :
    ('a -> State.t -> State.t * 'b) -> 'a list -> State.t -> State.t * 'b list
  (** [map f \[a1; a2; ...\]] applies [f] to [a1], then [a2], ..., passing the
      state at each step *)

  val ( ! ) : 'a -> State.t -> State.t * 'a
  (** Attach a value to a state so that it can be matched by a [let*] *)
end
