module type STATE = sig
  type t

  val attach : 'a -> t -> t * 'a
end

module Make (State : STATE) = struct
  let ( let* ) (f : 's -> 's * 'a) (continuation : 'a -> 's -> 'b) state =
    let state', result = f state in
    continuation result state'

  let ( ! ) = State.attach

  let map f l state =
    List.fold_left_map (fun state x -> ( let* ) (f x) ( ! ) state) state l
end
