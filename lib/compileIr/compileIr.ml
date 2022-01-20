open Common
open Ir
open Ast

type local_context = {
  (* mutable aux_cnt : int; *)
  (* mutable auxiliaries : stream list; *)
  (* auxiliaries are always of type boolean *)
  tbl : stream Hashstr.t; (* mutable additionnal_eqs : formula list; *)
}

let create_local_ctx () =
  {
    (* aux_cnt = 0;
       auxiliaries = []; *)
    tbl = Hashstr.create 8 (* additionnal_eqs = []; *);
  }

let add_stream_variable lctx name ty =
  let var = { name; ty } in
  Hashstr.add lctx.tbl name var;
  var

(* let add_aux_variable lctx =
   let name = Printf.sprintf "aux%d" lctx.aux_cnt in
   lctx.aux_cnt <- lctx.aux_cnt + 1;
   let aux_var = { name; ty = Boolean } in
   lctx.auxiliaries <- aux_var :: lctx.auxiliaries;
   aux_var *)

let find_stream lctx name =
  try Hashstr.find lctx.tbl name
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
  | TE_ident id -> Var (find_stream local_ctx id.name, time_expr)
  | TE_app (id, exprs) -> Function (id.name, time_expr, List.map convert exprs)
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
      Formula (formula, time_expr)
      (* let fresh_stream, fresh_name = add_aux_variable local_ctx in
         let var = Var (fresh_stream, fresh_name, time_expr) in
         let new_eq =
           And [ Imply (Term var, formula); Imply (formula, Term var) ]
         in
         add_formula local_ctx new_eq; *)
      (* var *)
  | TE_op ((Op_sub | Op_sub_f | Op_div | Op_div_f | Op_mod | Op_if), l) ->
      Format.eprintf "%d@." (List.length l);
      raise (Invalid_argument "Invalid terms")
  | TE_prim (_, _) as t ->
      ignore t;
      raise (Invalid_argument "Invalid terms")

and convert_to_formula time_expr ctx local_ctx (expr : t_expr) =
  let to_term ?(t = time_expr) = convert_to_term t ctx local_ctx in
  let to_form ?(t = time_expr) = convert_to_formula t ctx local_ctx in
  match expr.texpr_desc with
  | TE_const (Cbool b) -> Term (Bool b)
  | TE_ident id -> Term (Var (find_stream local_ctx id.name, time_expr))
  | TE_app (id, exprs) ->
      Term (Function (id.name, time_expr, List.map to_term exprs))
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
      (* TODO: change WHUT *)
      raise (Invalid_argument "Whut?")

let convert_patt local_ctx { tpatt_desc; _ } =
  match tpatt_desc with
  | [] -> raise (Invalid_argument "tpatt_desc should not be empty")
  | [ x ] -> Var (find_stream local_ctx x.name, N)
  | l ->
      TupleTerm
        (List.map (fun { name; _ } -> Var (find_stream local_ctx name, N)) l)

let convert_equation ctx local_ctx eq =
  let patt = convert_patt local_ctx eq.teq_patt in
  let expr = convert_to_term N ctx local_ctx eq.teq_expr in
  Equal [ patt; expr ]

let convert_ty = function Tbool -> Boolean | Tint -> Integer | Treal -> Real

let of_node ctx node =
  let register_stream lctx ({ name; _ }, ty) =
    add_stream_variable lctx name (convert_ty ty)
  in
  let local_ctx = create_local_ctx () in
  let inputs = List.map (register_stream local_ctx) node.tn_input
  and variables = List.map (register_stream local_ctx) node.tn_local
  and outputs = List.map (register_stream local_ctx) node.tn_output in
  let equations = List.map (convert_equation ctx local_ctx) node.tn_equs in
  {
    name = node.tn_name.name;
    original_name = node.tn_name.name;
    inputs;
    variables;
    outputs;
    equations;
  }

let of_file file =
  let open Context in
  let ctx = create () in
  List.iter (fun node -> add ctx (of_node ctx node)) file;
  ctx
