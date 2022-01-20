open Ast
open Common

exception NameDuplicate of string

type t = node Hashstr.t

let create () = Hashstr.create 8

let add ctx node =
  if Hashstr.mem ctx node.name then raise (NameDuplicate node.name);
  Hashstr.add ctx node.name node

let find ctx name = Hashstr.find ctx name
let find_opt ctx name = Hashstr.find_opt ctx name

let replace ctx node =
  match find_opt ctx node.name with
  | Some { original_name; _ } ->
      Hashstr.add ctx node.name { node with original_name }
  | None -> Hashstr.add ctx node.name node
