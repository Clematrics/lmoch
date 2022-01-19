type stream_type = Boolean | Integer | Real | Tuple of stream_type list
type stream = { name : string; ty : stream_type }

type term =
  | N (* time *)
  | Bool of bool
  | Int of int
  | Float of float
  | Var of stream * term
  | TupleTerm of term list
  | Function of string * term * term list (* name * time * args *)
  | Add of term list
  | Sub of term * term
  | Neg of term
  | Mul of term list
  | Div of term * term
  | Mod of term * term
  | IfThenElse of formula * term * term
  | IntOfReal of term
  | RealOfInt of term
  | Formula of formula * term

and formula =
  | Term of term
  | Imply of formula * formula
  | And of formula list
  | Or of formula list
  | Not of formula
  | Equal of term list
  | NotEqual of term * term
  | Less of term * term
  | LessOrEqual of term * term
  | Greater of term * term
  | GreaterOrEqual of term * term

type node = {
  name : string;
  original_name : string;
  inputs : stream list;
  variables : stream list;
  outputs : stream list;
  equations : formula list;
}

let rec print_term fmt =
  let open Format in
  function
  | N -> fprintf fmt "N"
  | Bool b -> fprintf fmt "%a" pp_print_bool b
  | Int i -> fprintf fmt "%a" pp_print_int i
  | Float f -> fprintf fmt "%f" f
  | Var (var, time) -> fprintf fmt "var(%s, %a)" var.name print_term time
  | TupleTerm l ->
      fprintf fmt "(@[<h>%a@])"
        (pp_print_list
           ~pp_sep:(fun fmt () -> pp_print_string fmt ", ")
           print_term)
        l
  | Function (name, time, exprs) ->
      fprintf fmt "func(@[<h>%s, %a, %a@])" name print_term time
        (pp_print_list
           ~pp_sep:(fun fmt () -> pp_print_string fmt ", ")
           print_term)
        exprs
  | Add ts ->
      fprintf fmt "(@[<h>%a@])"
        (pp_print_list
           ~pp_sep:(fun fmt () -> pp_print_string fmt " + ")
           print_term)
        ts
  | Sub (x, y) -> fprintf fmt "(%a - %a)" print_term x print_term y
  | Neg t -> fprintf fmt "(- %a)" print_term t
  | Mul ts ->
      fprintf fmt "(@[<h>%a@])"
        (pp_print_list
           ~pp_sep:(fun fmt () -> pp_print_string fmt " * ")
           print_term)
        ts
  | Div (x, y) -> fprintf fmt "(%a / %a)" print_term x print_term y
  | Mod (x, y) -> fprintf fmt "(%a %% %a)" print_term x print_term y
  | IfThenElse (cond, t1, t2) ->
      fprintf fmt
        "(@[<v>@[<v 2>if@ %a@]@ @[<v 2>then@ %a@]@ @[<v 2>else@ %a@]@])"
        print_formula cond print_term t1 print_term t2
  | IntOfReal t -> fprintf fmt "int(%a)" print_term t
  | RealOfInt t -> fprintf fmt "real(%a)" print_term t
  | Formula (f, _) -> print_formula fmt f

and print_formula fmt =
  let open Format in
  function
  | Term t -> print_term fmt t
  | Imply (p, q) ->
      fprintf fmt "@[<h>%a@ =>@ %a@]" print_formula p print_formula q
  | And l ->
      fprintf fmt "(and@[<v 2>@ %a@])"
        (pp_print_list
           (* ~pp_sep:(fun fmt () -> pp_print_string fmt " /\\ ") *)
           print_formula)
        l
  | Or l ->
      fprintf fmt "(or@[<v 2>@ %a@])"
        (pp_print_list
           (* ~pp_sep:(fun fmt () -> pp_print_string fmt " \\/ ") *)
           print_formula)
        l
  | Not f -> fprintf fmt "~%a" print_formula f
  | Equal l ->
      fprintf fmt "(=@[<v 2>@ %a@])"
        (pp_print_list
           (* ~pp_sep:(fun fmt () -> pp_print_string fmt "=") *)
           print_term)
        l
  | NotEqual (x, y) -> fprintf fmt "%a <> %a" print_term x print_term y
  | Less (x, y) -> fprintf fmt "%a < %a" print_term x print_term y
  | LessOrEqual (x, y) -> fprintf fmt "%a <= %a" print_term x print_term y
  | Greater (x, y) -> fprintf fmt "%a > %a" print_term x print_term y
  | GreaterOrEqual (x, y) -> fprintf fmt "%a >= %a" print_term x print_term y

(*
  open Common
type node = {
  name : string;
  inputs : (stream_id * string * stream_type) list;
  variables : (stream_id * string * stream_type) list;
  outputs : (stream_id * string * stream_type) list;
  equations : formula list;
}

type context = {
  mutable next_id : int;
  tbl : node_id Hashstr.t;
  mutable nodes : (node_id * node) list;
}

let create_context () = { next_id = 0; tbl = Hashstr.create 8; nodes = [] }

let add_node ctx name node =
  let id = ctx.next_id in
  ctx.next_id <- id + 1;
  Hashstr.add ctx.tbl name id;
  ctx.nodes <- (id, node) :: ctx.nodes

let find_node ctx name =
  try Hashstr.find ctx.tbl name
  with Not_found ->
    raise (Invalid_argument ("Could not find node " ^ name ^ "in context"))

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

let add_stream_variable lctx name ty =
  let id = lctx.next_id in
  lctx.next_id <- id + 1;
  Hashstr.add lctx.tbl name (id, ty);
  id

let add_aux_variable lctx =
  let id = lctx.next_id in
  let name = "aux" ^ string_of_int id in
  lctx.next_id <- id + 1;
  lctx.auxiliaries <- (id, name) :: lctx.auxiliaries;
  (id, name)

let add_formula lctx f = lctx.additionnal_eqs <- f :: lctx.additionnal_eqs

let find_stream lctx name =
  try fst @@ Hashstr.find lctx.tbl name
  with Not_found ->
    raise (Invalid_argument ("Could not find " ^ name ^ " in local context"))

open Frontend
open Asttypes
open Ident
open Typed_ast

let rec convert_to_term time_expr ctx local_ctx (expr : t_expr) =
  let convert = convert_to_term time_expr ctx local_ctx in
  match expr.texpr_desc with
  | TE_const (Cbool b) -> Bool b
  | TE_const (Cint i) -> Int i
  | TE_const (Creal f) -> Float f
  | TE_ident id -> Var (find_stream local_ctx id.name, id.name, time_expr)
  | TE_app (id, exprs) ->
      Function (find_node ctx id.name, time_expr, List.map convert exprs)
  | TE_prim (id, [ expr ]) when id = Typing.int_of_real ->
      IntOfReal (convert expr)
  | TE_prim (id, [ expr ]) when id = Typing.real_of_int ->
      RealOfInt (convert expr)
  | TE_arrow (init, expr) ->
      IfThenElse (Equal [ time_expr; Int 0 ], convert init, convert expr)
  | TE_pre expr -> convert_to_term (Sub (time_expr, Int 1)) ctx local_ctx expr
  | TE_tuple exprs -> TupleTerm (List.map convert exprs)
  | TE_op ((Op_add | Op_add_f), exprs) -> Add (List.map convert exprs)
  | TE_op ((Op_sub | Op_sub_f), [ e ]) -> Neg (convert e)
  | TE_op ((Op_sub | Op_sub_f), [ e1; e2 ]) -> Sub (convert e1, convert e2)
  | TE_op ((Op_mul | Op_mul_f), exprs) -> Mul (List.map convert exprs)
  | TE_op ((Op_div | Op_div_f), [ e1; e2 ]) -> Div (convert e1, convert e2)
  | TE_op (Op_mod, [ e1; e2 ]) -> Mod (convert e1, convert e2)
  | TE_op (Op_if, [ pred; e1; e2 ]) ->
      IfThenElse
        (convert_to_formula time_expr ctx local_ctx pred, convert e1, convert e2)
  | TE_op
      ( ( Op_eq | Op_neq | Op_lt | Op_le | Op_gt | Op_ge | Op_not | Op_and
        | Op_or | Op_impl ),
        _ ) ->
      let formula = convert_to_formula time_expr ctx local_ctx expr in
      let fresh_stream, fresh_name = add_aux_variable local_ctx in
      let var = Var (fresh_stream, fresh_name, time_expr) in
      let new_eq =
        And [ Imply (Term var, formula); Imply (formula, Term var) ]
      in
      add_formula local_ctx new_eq;
      var
  | TE_op ((Op_sub | Op_sub_f | Op_div | Op_div_f | Op_mod | Op_if), l) ->
      Format.eprintf "%d@." (List.length l);
      raise (Invalid_argument "Whut?")
  | TE_prim (_, _) as t ->
      ignore t;
      raise (Invalid_argument "Whut?")

and convert_to_formula time_expr ctx local_ctx (expr : t_expr) =
  let to_term ?(t = time_expr) = convert_to_term t ctx local_ctx in
  let to_form ?(t = time_expr) = convert_to_formula t ctx local_ctx in
  match expr.texpr_desc with
  | TE_const (Cbool b) -> Term (Bool b)
  | TE_ident id ->
      Term (Var (find_stream local_ctx id.name, id.name, time_expr))
  | TE_app (id, exprs) ->
      Term (Function (find_node ctx id.name, time_expr, List.map to_term exprs))
  | TE_arrow (init, expr) ->
      Term (IfThenElse (Equal [ time_expr; Int 0 ], to_term init, to_term expr))
  | TE_pre expr -> Term (to_term ~t:(Sub (time_expr, Int 1)) expr)
  | TE_op (Op_if, [ pred; e1; e2 ]) ->
      Term (IfThenElse (to_form pred, to_term e1, to_term e2))
  | TE_op (Op_eq, exprs) -> Equal (List.map to_term exprs)
  | TE_op (Op_neq, exprs) -> Not (Equal (List.map to_term exprs))
  | TE_op (Op_lt, [ e1; e2 ]) -> Less (to_term e1, to_term e2)
  | TE_op (Op_le, [ e1; e2 ]) -> LessOrEqual (to_term e1, to_term e2)
  | TE_op (Op_gt, [ e1; e2 ]) -> Greater (to_term e1, to_term e2)
  | TE_op (Op_ge, [ e1; e2 ]) -> GreaterOrEqual (to_term e1, to_term e2)
  | TE_op (Op_not, [ e ]) -> Not (to_form e)
  | TE_op (Op_and, exprs) -> And (List.map to_form exprs)
  | TE_op (Op_or, exprs) -> Or (List.map to_form exprs)
  | TE_op (Op_impl, [ e1; e2 ]) -> Imply (to_form e1, to_form e2)
  | TE_prim _ | TE_const _ | TE_tuple _ | TE_op (_, _) ->
      raise (Invalid_argument "Whut?")

let convert_patt local_ctx { tpatt_desc; _ } =
  match tpatt_desc with
  | [] -> raise (Invalid_argument "tpatt_desc should not be empty")
  | [ x ] -> Var (find_stream local_ctx x.name, x.name, N)
  | l ->
      TupleTerm
        (List.map
           (fun { name; _ } -> Var (find_stream local_ctx name, name, N))
           l)

let convert_equation ctx local_ctx eq =
  let patt = convert_patt local_ctx eq.teq_patt in
  let expr = convert_to_term N ctx local_ctx eq.teq_expr in
  Equal [ patt; expr ]

let convert_ty = function Tbool -> Boolean | Tint -> Integer | Treal -> Real

let of_node (ctx : context) (node : t_node) =
  let register_stream lctx ({ name; _ }, ty) =
    let ty = convert_ty ty in
    (add_stream_variable lctx name ty, name, ty)
  in
  let local_ctx = create_local_ctx () in
  let inputs = List.map (register_stream local_ctx) node.tn_input
  and variables = List.map (register_stream local_ctx) node.tn_local
  and outputs = List.map (register_stream local_ctx) node.tn_output in
  let equations = List.map (convert_equation ctx local_ctx) node.tn_equs in
  let equations = equations @ local_ctx.additionnal_eqs in
  let variables =
    List.map (fun (id, name) -> (id, name, Boolean)) local_ctx.auxiliaries
    @ variables
  in
  add_node ctx node.tn_name.name
    { name = node.tn_name.name; inputs; variables; outputs; equations };
  ()

let of_file (file : t_file) =
  let ctx = create_context () in
  List.iter (of_node ctx) file;
  ctx *)
