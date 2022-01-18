type 'a tree = Leaf of 'a | Node of 'a tree list

let rec tree_map f = function
  | Leaf x -> Leaf (f x)
  | Node l -> Node (List.map (tree_map f) l)

let rec tree_map2 f t1 t2 =
  match (t1, t2) with
  | Leaf x, Leaf y -> Leaf (f x y)
  | Node l, Node l' -> Node (List.map2 (tree_map2 f) l l')
  | _ -> raise (Invalid_argument "tree_map2 called with different trees")

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
  let rec flatten_nodes acc = function
    | [] -> List.concat_map (fun forest -> flatten (List.rev forest)) acc
    | Leaf _ :: _ ->
        raise (Invalid_argument "Cannot flatten to a list of tuples")
    | Node t :: l ->
        let rec f ?(acc = []) = function
          | [], [] -> acc
          | x :: t, y :: t' -> f ~acc:((x :: y) :: acc) (t, t')
          | _ ->
              raise
                (Invalid_argument "Cannot flatten when not of the same size")
        in
        let acc = f (t, acc) in
        flatten_nodes acc l
  in
  match forest with
  | [] -> []
  | Leaf _ :: _ -> [ flatten_leaves forest ]
  | Node l :: _ -> flatten_nodes (List.map (fun _ -> []) l) forest
