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

let replace ctx { name; inputs; outputs; variables; equations; _ } =
  let { original_name; _ } = find ctx name in
  let node = { name; original_name; inputs; variables; outputs; equations } in
  Hashstr.add ctx name node

(* TODO: DELETE
   type local_context = {
     mutable next_id : stream_id;
     mutable auxiliaries : (stream_id * string) list;
     (* auxiliaries are always of type boolean *)
     tbl : (stream_id * stream_type) Hashstr.t;
     mutable additionnal_eqs : formula list;
   }

   let create_local_ctx () =
   {
     next_id = 0;
     auxiliaries = [];
     tbl = Hashstr.create 8;
     additionnal_eqs = [];
   }
*)
