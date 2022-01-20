open Ast

type t = FullInlining | NoTuples | NoFormulaInTerm

type inlining_state = {
  eqs_acc : formula list;
  var_acc : stream list;
  inst_cnt : int;
}
(** - [eqs_acc] accumulates the equations added by the inlining
    - [inst_cnt] is the number of instantiations done before, to give different
      names to every variable instantiated *)

let initial_state () = { eqs_acc = []; var_acc = []; inst_cnt = 0 }

type inlined_node = {
  inputs : stream list;
  variables : stream list;
  outputs : stream list;
  equations : formula list;
}
(** Stores the data of an inlined node, that is, all the variables it contains,
    its inputs, its outputs and all its equations *)

(* - [prefix_name] is the prefix of the current instantiation
   - [time_term] is the expression of the local time in the node instantiated
   - [node_name] is the name of the node being instantiated
   - [inst_cnt] is the offset on the number of instances
   Returns a pair [(i, inlined_node)] where
   [i] is the number of instances created inside,
    and [inlined_node] is the node inlined *)
let rec instantiate_node ctx prefix_name node_name time_term inst_cnt =
  let inst_name = Printf.sprintf "%s$%s_%d" prefix_name node_name inst_cnt in
  let localize_stream { name; ty } =
    let name = Printf.sprintf "%s$%s" inst_name name in
    { name; ty }
  in
  let state = { eqs_acc = []; var_acc = []; inst_cnt = inst_cnt + 1 } in
  let rec scan_formula state = function
    | Term t ->
        let next_state, t = scan_term state t in
        (next_state, Term t)
    | Imply (p, q) ->
        let state_1, p = scan_formula state p in
        let state_2, q = scan_formula state_1 q in
        (state_2, Imply (p, q))
    | And fs ->
        let next_state, fs = List.fold_left_map scan_formula state fs in
        (next_state, And fs)
    | Or fs ->
        let next_state, fs = List.fold_left_map scan_formula state fs in
        (next_state, Or fs)
    | Not f ->
        let next_state, f = scan_formula state f in
        (next_state, Not f)
    | Equal ts ->
        let next_state, ts = List.fold_left_map scan_term state ts in
        (next_state, Equal ts)
    | NotEqual (x, y) ->
        let state_1, x = scan_term state x in
        let state_2, y = scan_term state_1 y in
        (state_2, NotEqual (x, y))
    | Less (x, y) ->
        let state_1, x = scan_term state x in
        let state_2, y = scan_term state_1 y in
        (state_2, Less (x, y))
    | LessOrEqual (x, y) ->
        let state_1, x = scan_term state x in
        let state_2, y = scan_term state_1 y in
        (state_2, LessOrEqual (x, y))
    | Greater (x, y) ->
        let state_1, x = scan_term state x in
        let state_2, y = scan_term state_1 y in
        (state_2, Greater (x, y))
    | GreaterOrEqual (x, y) ->
        let state_1, x = scan_term state x in
        let state_2, y = scan_term state_1 y in
        (state_2, GreaterOrEqual (x, y))
  and scan_term state = function
    | N -> (state, time_term)
    | (Bool _ | Int _ | Float _) as t -> (state, t)
    | Var (stream, time) ->
        let stream = localize_stream stream in
        let next_state, time = scan_term state time in
        (next_state, Var (stream, time))
    | TupleTerm ts ->
        let next_state, ts = List.fold_left_map scan_term state ts in
        (next_state, TupleTerm ts)
    | Function (name, time, args) ->
        let state_1, function_time = scan_term state time in
        let state_2, args = List.fold_left_map scan_term state_1 args in
        let inst_cnt, { inputs; variables; outputs; equations } =
          instantiate_node ctx inst_name name function_time state_2.inst_cnt
        in
        let arg_eqs =
          List.map2 (fun x s -> Equal [ x; Var (s, function_time) ]) args inputs
        in
        let output_streams =
          List.map (fun s -> Var (s, function_time)) outputs
        in
        let output =
          match output_streams with
          | [] ->
              assert false (* a function returning nothing should not exists *)
          | [ o ] -> o
          | l -> TupleTerm l
        in
        ( {
            inst_cnt;
            eqs_acc =
              List.(rev_append arg_eqs (rev_append equations state_2.eqs_acc));
            var_acc =
              List.concat [ inputs; variables; outputs; state_2.var_acc ];
          },
          output )
    | Add ts ->
        let next_state, ts = List.fold_left_map scan_term state ts in
        (next_state, Add ts)
    | Sub (x, y) ->
        let state_1, x = scan_term state x in
        let state_2, y = scan_term state_1 y in
        (state_2, Sub (x, y))
    | Neg t ->
        let next_state, t = scan_term state t in
        (next_state, Neg t)
    | Mul ts ->
        let next_state, ts = List.fold_left_map scan_term state ts in
        (next_state, Mul ts)
    | Div (x, y) ->
        let state_1, x = scan_term state x in
        let state_2, y = scan_term state_1 y in
        (state_2, Div (x, y))
    | Mod (x, y) ->
        let state_1, x = scan_term state x in
        let state_2, y = scan_term state_1 y in
        (state_2, Mod (x, y))
    | IfThenElse (cond, x, y) ->
        let state_1, cond = scan_formula state cond in
        let state_2, x = scan_term state_1 x in
        let state_3, y = scan_term state_2 y in
        (state_3, IfThenElse (cond, x, y))
    | IntOfReal t ->
        let next_state, t = scan_term state t in
        (next_state, IntOfReal t)
    | RealOfInt t ->
        let next_state, t = scan_term state t in
        (next_state, RealOfInt t)
    | Formula (f, time) ->
        let state_1, f = scan_formula state f in
        let state_2, time = scan_term state_1 time in
        (state_2, Formula (f, time))
  in
  let ({ inputs; outputs; equations; variables; _ } : node) =
    Context.find ctx node_name
  in
  let state, equations = List.fold_left_map scan_formula state equations in
  let inputs = List.map localize_stream inputs
  and variables = List.map localize_stream variables
  and outputs = List.map localize_stream outputs in
  let variables = List.rev_append variables state.var_acc in
  ( state.inst_cnt,
    {
      inputs;
      variables;
      outputs;
      equations = List.rev_append equations state.eqs_acc;
    } )

(** Modify a node to inline all nodes it contains *)
let full_inlining ctx root_node_name =
  let _, { inputs; variables; outputs; equations; _ } =
    instantiate_node ctx "" root_node_name N 0
  in
  let root_node = Context.find ctx root_node_name in
  let node = { root_node with inputs; variables; outputs; equations } in
  Context.replace ctx node;
  root_node_name

(* -------------------------- *)
(* Removing tuples from nodes *)
(* -------------------------- *)

open Common.Tree

(* Decompose a variable into a tree of variables with no tuples *)
let decompose_var { ty; name } =
  let rec decompose prefix = function
    | Tuple tys ->
        let proj_name = Printf.sprintf "%s$%d" prefix in
        Node (List.mapi (fun i ty -> decompose (proj_name i) ty) tys)
    | ty -> Leaf { ty; name = prefix }
  in
  decompose name ty

let flatten_variables vars =
  let forest = List.map decompose_var vars in
  let flat_vars = List.concat (List.map leaves forest) in
  flat_vars

type tuple_status = HasTupleOutput | HasTupleInputs | HasNoTuples

(* Check if a node can be used in a {!constr:NoTuples} AST *)
let node_tuple_status ctx name =
  let ({ inputs; outputs; _ } : node) = Context.find ctx name in
  match outputs with
  | _ :: _ :: _ -> HasTupleOutput
  | [] | [ _ ] ->
      let has_tuple_inputs =
        List.exists (function { ty = Tuple _; _ } -> true | _ -> false) inputs
      in
      if has_tuple_inputs then HasTupleInputs else HasNoTuples

(** Remove tuple expressions from the node, recreating new nodes with new
    definitions if a node call with tuple is detected *)
let rec no_tuples ctx node_name =
  let rec transform_simple_term state t =
    let state, t = transform_term state t in
    (state, try_leaf t)
  and transform_term state t =
    let transform_terms = List.fold_left_map transform_term in
    let transform_simple_terms = List.fold_left_map transform_simple_term in
    match t with
    | (N | Bool _ | Int _ | Float _) as t -> (state, Leaf t)
    | Var (stream, time) ->
        let stream_tree = decompose_var stream in
        let next_state, time = transform_simple_term state time in
        (next_state, map (fun stream -> Var (stream, time)) stream_tree)
    | TupleTerm ts ->
        let next_state, ts = transform_terms state ts in
        (next_state, Node ts)
    | Function (name, time, args) -> (
        let state_1, time = transform_simple_term state time in
        let state_2, args = transform_terms state_1 args in
        match node_tuple_status ctx name with
        | HasTupleOutput ->
            let inst_cnt, { inputs; variables; outputs; equations } =
              instantiate_node ctx node_name name time state_2.inst_cnt
            in
            let state_3, equations =
              List.fold_left_map transform_formula state_2 equations
            in
            let input_forest = List.map decompose_var inputs in
            let flat_inputs = List.concat (List.map leaves input_forest) in
            let flat_variables = flatten_variables variables in
            let flat_outputs = flatten_variables outputs in
            let arg_eq_trees =
              List.map2
                (map2 (fun x s -> Equal [ x; Var (s, time) ]))
                args input_forest
            in
            let arg_eqs = List.concat (List.map leaves arg_eq_trees) in
            let output_streams =
              List.map (fun s -> Leaf (Var (s, time))) outputs
            in
            let output =
              Node output_streams
              (* is always a tuple, since it was established that this node indeed has a tuple output *)
            in
            ( {
                inst_cnt;
                eqs_acc =
                  List.(
                    rev_append arg_eqs (rev_append equations state_3.eqs_acc));
                var_acc =
                  List.concat
                    [
                      flat_inputs; flat_variables; flat_outputs; state_3.var_acc;
                    ];
              },
              output )
        | HasTupleInputs ->
            let new_node_name = no_tuples ctx name in
            let args = List.concat (List.map leaves args) in
            (state_2, Leaf (Function (new_node_name, time, args)))
        | HasNoTuples ->
            let args = List.map try_leaf args in
            (state_2, Leaf (Function (name, time, args)))
        (* Multiple options: if the node outputs a tuple, inline the node and flatten its inputs,
           and if the node has inputs as tuples, apply [no_tuples] ont this node and call it.
           Otherhwise, keep this expression. [time] and [args] are transformed in all cases *)
        )
    | Add ts ->
        let next_state, ts = transform_simple_terms state ts in
        (next_state, Leaf (Add ts))
    | Sub (x, y) ->
        let state_1, x = transform_simple_term state x in
        let state_2, y = transform_simple_term state_1 y in
        (state_2, Leaf (Sub (x, y)))
    | Neg t ->
        let next_state, t = transform_simple_term state t in
        (next_state, Leaf (Neg t))
    | Mul ts ->
        let next_state, ts = transform_simple_terms state ts in
        (next_state, Leaf (Mul ts))
    | Div (x, y) ->
        let state_1, x = transform_simple_term state x in
        let state_2, y = transform_simple_term state_1 y in
        (state_2, Leaf (Div (x, y)))
    | Mod (x, y) ->
        let state_1, x = transform_simple_term state x in
        let state_2, y = transform_simple_term state_1 y in
        (state_2, Leaf (Mod (x, y)))
    | IfThenElse (cond, x, y) ->
        let state_1, cond = transform_formula state cond in
        let state_2, x = transform_term state_1 x in
        let state_3, y = transform_term state_2 y in
        (state_3, map2 (fun x y -> IfThenElse (cond, x, y)) x y)
    | IntOfReal t ->
        let next_state, t = transform_simple_term state t in
        (next_state, Leaf (IntOfReal t))
    | RealOfInt t ->
        let next_state, t = transform_simple_term state t in
        (next_state, Leaf (RealOfInt t))
    | Formula (f, time) ->
        let state_1, f = transform_formula state f in
        let state_2, time = transform_simple_term state_1 time in
        (state_2, Leaf (Formula (f, time)))
  and transform_formula state f =
    let transform_formulas = List.fold_left_map transform_formula in
    match f with
    | Term t ->
        let next_state, t = transform_simple_term state t in
        (next_state, Term t)
    | Imply (p, q) ->
        let state_1, p = transform_formula state p in
        let state_2, q = transform_formula state_1 q in
        (state_2, Imply (p, q))
    | And fs ->
        let next_state, fs = transform_formulas state fs in
        (next_state, And fs)
    | Or fs ->
        let next_state, fs = transform_formulas state fs in
        (next_state, Or fs)
    | Not f ->
        let next_state, f = transform_formula state f in
        (next_state, Not f)
    | Equal ts -> (
        let next_state, eq_trees = List.fold_left_map transform_term state ts in
        let eqs = List.map (fun ts -> Equal ts) (flatten eq_trees) in
        ( next_state,
          match eqs with [] -> Term (Bool true) | [ x ] -> x | _ -> And eqs ))
    | NotEqual (x, y) -> (
        let state_1, x_tree = transform_term state x in
        let state_2, y_tree = transform_term state_1 y in
        let neq_tree = map2 (fun x y -> NotEqual (x, y)) x_tree y_tree in
        ( state_2,
          match leaves neq_tree with
          | [] -> Term (Bool false)
          | [ x ] -> x
          | neqs -> Or neqs ))
    | Less (x, y) ->
        let state_1, x = transform_simple_term state x in
        let state_2, y = transform_simple_term state_1 y in
        (state_2, Less (x, y))
    | LessOrEqual (x, y) ->
        let state_1, x = transform_simple_term state x in
        let state_2, y = transform_simple_term state_1 y in
        (state_2, LessOrEqual (x, y))
    | Greater (x, y) ->
        let state_1, x = transform_simple_term state x in
        let state_2, y = transform_simple_term state_1 y in
        (state_2, Greater (x, y))
    | GreaterOrEqual (x, y) ->
        let state_1, x = transform_simple_term state x in
        let state_2, y = transform_simple_term state_1 y in
        (state_2, GreaterOrEqual (x, y))
  in
  let state = initial_state () in
  let ({ name; original_name; inputs; variables; outputs; equations } : node) =
    Context.find ctx node_name
  in
  let state, equations = List.fold_left_map transform_formula state equations in
  let new_name = Printf.sprintf "%s{no_tuples}" name in
  let node =
    {
      name = new_name;
      original_name;
      inputs = flatten_variables inputs;
      variables = List.concat [ state.var_acc; flatten_variables variables ];
      outputs = flatten_variables outputs;
      equations = List.concat [ state.eqs_acc; equations ];
    }
  in
  Context.replace ctx node;
  new_name

(* ----------------------------- *)
(* Separating terms and formulas *)
(* ----------------------------- *)

(** Create a new node in which boolean streams have nontrivial boolean terms
    replaced by new boolean streams equivalent to the formula replaced *)
let no_formula_in_term ctx node_name =
  let rec transform_formula state f =
    let transform_formulas = List.fold_left_map transform_formula in
    match f with
    | Term t ->
        let next_state, t = transform_term state t in
        (next_state, Term t)
    | Imply (p, q) ->
        let state_1, p = transform_formula state p in
        let state_2, q = transform_formula state_1 q in
        (state_2, Imply (p, q))
    | And fs ->
        let next_state, fs = transform_formulas state fs in
        (next_state, And fs)
    | Or fs ->
        let next_state, fs = transform_formulas state fs in
        (next_state, Or fs)
    | Not f ->
        let next_state, f = transform_formula state f in
        (next_state, Not f)
    | Equal ts ->
        let next_state, ts = List.fold_left_map transform_term state ts in
        (next_state, Equal ts)
    | NotEqual (x, y) ->
        let state_1, x = transform_term state x in
        let state_2, y = transform_term state_1 y in
        (state_2, NotEqual (x, y))
    | Less (x, y) ->
        let state_1, x = transform_term state x in
        let state_2, y = transform_term state_1 y in
        (state_2, Less (x, y))
    | LessOrEqual (x, y) ->
        let state_1, x = transform_term state x in
        let state_2, y = transform_term state_1 y in
        (state_2, LessOrEqual (x, y))
    | Greater (x, y) ->
        let state_1, x = transform_term state x in
        let state_2, y = transform_term state_1 y in
        (state_2, Greater (x, y))
    | GreaterOrEqual (x, y) ->
        let state_1, x = transform_term state x in
        let state_2, y = transform_term state_1 y in
        (state_2, GreaterOrEqual (x, y))
  and transform_term state t =
    let transform_terms = List.fold_left_map transform_term in
    match t with
    | (N | Bool _ | Int _ | Float _) as t -> (state, t)
    | Var (stream, time) ->
        let next_state, time = transform_term state time in
        (next_state, Var (stream, time))
    | TupleTerm ts ->
        let next_state, ts = transform_terms state ts in
        (next_state, TupleTerm ts)
    | Function (name, time, args) ->
        let state_1, time = transform_term state time in
        let state_2, args = transform_terms state_1 args in
        (state_2, Function (name, time, args))
    | Add ts ->
        let next_state, ts = transform_terms state ts in
        (next_state, Add ts)
    | Sub (x, y) ->
        let state_1, x = transform_term state x in
        let state_2, y = transform_term state_1 y in
        (state_2, Sub (x, y))
    | Neg t ->
        let next_state, t = transform_term state t in
        (next_state, Neg t)
    | Mul ts ->
        let next_state, ts = transform_terms state ts in
        (next_state, Mul ts)
    | Div (x, y) ->
        let state_1, x = transform_term state x in
        let state_2, y = transform_term state_1 y in
        (state_2, Div (x, y))
    | Mod (x, y) ->
        let state_1, x = transform_term state x in
        let state_2, y = transform_term state_1 y in
        (state_2, Mod (x, y))
    | IfThenElse (cond, x, y) ->
        let state_1, cond = transform_formula state cond in
        let state_2, x = transform_term state_1 x in
        let state_3, y = transform_term state_2 y in
        (state_3, IfThenElse (cond, x, y))
    | IntOfReal t ->
        let next_state, t = transform_term state t in
        (next_state, IntOfReal t)
    | RealOfInt t ->
        let next_state, t = transform_term state t in
        (next_state, RealOfInt t)
    | Formula (f, time) ->
        let state_1, f = transform_formula state f in
        let state_2, time = transform_term state_1 time in
        let new_var =
          { name = Printf.sprintf "aux_%d" state_2.inst_cnt; ty = Boolean }
        in
        let eq_left = Imply (Term (Var (new_var, time)), f)
        and eq_right = Imply (f, Term (Var (new_var, time))) in
        ( {
            inst_cnt = state_2.inst_cnt + 1;
            eqs_acc = eq_left :: eq_right :: state_2.eqs_acc;
            var_acc = new_var :: state_2.var_acc;
          },
          Var (new_var, time) )
  in
  let state = initial_state () in
  let (({ variables; equations; _ } : node) as node) =
    Context.find ctx node_name
  in
  let state, equations = List.fold_left_map transform_formula state equations in
  let node =
    {
      node with
      variables = List.rev_append state.var_acc variables;
      equations = List.rev_append state.eqs_acc equations;
    }
  in
  Context.replace ctx node;
  node_name

let apply_transform context node_name transformation =
  let f =
    match transformation with
    | FullInlining -> full_inlining
    | NoTuples -> no_tuples
    | NoFormulaInTerm -> no_formula_in_term
  in
  f context node_name
