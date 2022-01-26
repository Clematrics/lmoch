type 'a tree = Leaf of 'a | Node of 'a tree list

let rec map f = function
  | Leaf x -> Leaf (f x)
  | Node l -> Node (List.map (map f) l)

let rec map2 f t1 t2 =
  match (t1, t2) with
  | Leaf x, Leaf y -> Leaf (f x y)
  | Node l, Node l' -> Node (List.map2 (map2 f) l l')
  | _ -> raise (Invalid_argument "map2 called with different trees")

let try_leaf = function
  | Leaf x -> x
  | Node _ -> raise (Invalid_argument "Not a leaf")

let leaves tree =
  let rec dfs acc = function
    | Leaf x -> x :: acc
    | Node l -> List.fold_left dfs acc l
  in
  dfs [] tree |> List.rev

let rec flatten forest =
  let rec flatten_leaves ?(acc = []) = function
    | [] -> List.rev acc
    | Leaf x :: l -> flatten_leaves ~acc:(x :: acc) l
    | Node _ :: _ ->
        raise (Invalid_argument "Cannot flatten to a list of atoms")
  in
  (* Take the first element of every list and put it in a list, returns the shrunk list of list [ll] *)
  let rec take_first firsts ll = function
    | [] -> (List.rev ll, List.rev firsts)
    | Node (x :: l) :: forest -> take_first (x :: firsts) (Node l :: ll) forest
    | _ :: _ ->
        raise
          (Invalid_argument
             "Cannot take the first element of an empty node or a leaf. The \
              trees could have different sizes")
  in
  (* Take a list of nodes with [n] children and create a node with [n] lists of trees as children *)
  let transpose_forest forest =
    match forest with
    | [] -> []
    | Leaf _ :: _ -> assert false
    | Node witness :: _ ->
        (* Repeat an operation with an accumulator on a list as long as a witness has elements *)
        let fold_left f obj witness =
          let rec aux acc next = function
            | [] -> List.rev acc
            | _ :: l ->
                let next, x = f next in
                aux (x :: acc) next l
          in
          aux [] obj witness
        in
        fold_left (take_first [] []) forest witness
  in
  match forest with
  | [] -> []
  | Leaf _ :: _ -> [ flatten_leaves forest ]
  | Node _ :: _ -> List.concat (List.map flatten (transpose_forest forest))
