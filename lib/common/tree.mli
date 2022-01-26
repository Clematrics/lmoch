(** Module implementing trees and operations on them *)

type 'a tree = Leaf of 'a | Node of 'a tree list

val map : ('a -> 'b) -> 'a tree -> 'b tree
(** [map f t] applies [f] to all the leaves of [t], returning a tree with the
    same structure as [t] *)

val map2 : ('a -> 'b -> 'c) -> 'a tree -> 'b tree -> 'c tree
(** [map2 f t1 t2] applies the matching leaves of [t1] and [t2] with [f] and
    returns the corresponding tree. [t1] and [t2] must have the same structure. *)

val try_leaf : 'a tree -> 'a
(** Returns the value of a leaf.

    @raise {!exception:Invalid_argument} if the tree is not a leaf *)

val leaves : 'a tree -> 'a list
(** Returns the list of the leaves of a tree, in the same order as a depth-first
    search would have covered them. *)

val flatten : 'a tree list -> 'a list list
(** [flatten forest] links all corresponding leaves of a forest in a list.
    [forest] must be a list of trees with the same structure.

    Example:

    {[
      flatten
        [
          Node [ Leaf 1; Node [ Leaf 2; Leaf 3 ] ];
          Node [ Leaf 4; Node [ Leaf 5; Leaf 6 ] ];
          Node [ Leaf 7; Node [ Leaf 8; Leaf 9 ] ];
        ]
    ]}

    returns [\[1; 2; 3\]; \[4; 5; 6\]; \[7; 8; 9\]] *)
