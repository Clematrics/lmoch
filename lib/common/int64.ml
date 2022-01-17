include Stdlib.Int64

let ( #+ ) = add

let ( #- ) = sub

let ( #* ) = mul

let ( #/ ) = div

let ( #% ) = rem

let ( #& ) = logand

let ( #| ) = logor

let ( #^ ) = logxor

let ( #<< ) = shift_left

let ( #>> ) = shift_right_logical

exception InvalidBitIndex

let mask i =
  if i < 0 || i > 64
  then raise InvalidBitIndex
  else if i = 0
  then zero
  else one #<< i #- one


let extract n high low =
  if high < 0 || high > 63 || low < 0 || low > 63 || high < low
  then raise InvalidBitIndex
  else n #>> low #& (mask (high - low + 1))


let test_bit n i =
  if i < 0 || i > 63 then raise InvalidBitIndex else one #<< i #& n <> zero


let pp_int64_bin fmt x =
  let bits_of x n = List.init n (fun i -> Some (test_bit x (n - 1 - i))) in
  let bits =
    List.concat
      [ [ Some (test_bit x 63) ]
      ; [ None ]
      ; bits_of (extract x 62 52) 11
      ; [ None ]
      ; bits_of (extract x 51 0) 52
      ]
  in
  let pp_nothing _ () = () in
  let pp_digit fmt = function
  | Some b -> Format.fprintf fmt "%c" (if b then '1' else '0')
  | None -> Format.fprintf fmt " "
in
  Format.(fprintf fmt "0b%a" (pp_print_list ~pp_sep:pp_nothing pp_digit) bits)
