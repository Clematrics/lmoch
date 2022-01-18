type 'a tree = Leaf of 'a | Node of 'a tree list

val tree_map : ('a -> 'b) -> 'a tree -> 'b tree
val tree_map2 : ('a -> 'b -> 'c) -> 'a tree -> 'b tree -> 'c tree
val try_leaf : 'a tree -> 'a
val leaves : 'a tree -> 'a list
val flatten : 'a tree list -> 'a list list
