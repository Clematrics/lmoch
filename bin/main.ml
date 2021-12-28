let rec fact = function
  | n when n <= 0 ->
      raise
        (Invalid_argument "Cannot compute the factorial of a negative number")
  | 1 -> 1
  | n -> fact (n - 1) * n

let () =
  print_int (fact 10);
  print_newline ();
  print_endline "Hello, World!"
