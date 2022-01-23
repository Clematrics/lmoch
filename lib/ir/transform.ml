open Ast
open Common

type t = FullInlining | NoTuples | NoFormulaInTerm

module InliningState = struct
  type t = { eqs_acc : formula list; var_acc : stream list; inst_cnt : int }
  (** - [eqs_acc] accumulates the equations added by the inlining
      - [inst_cnt] is the number of instantiations done before, to give
        different names to every variable instantiated *)

  let initial_state () = { eqs_acc = []; var_acc = []; inst_cnt = 0 }
  let attach x state = (state, x)
end

open InliningState
module S = StateManagement.Make (InliningState)
open S

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
  let rec scan_formulas l state = map scan_formula l state
  and scan_terms l state = map scan_term l state
  and scan_formula formula =
    match formula with
    | Term t ->
        let* t = scan_term t in
        !(Term t)
    | Imply (p, q) ->
        let* p = scan_formula p in
        let* q = scan_formula q in
        !(Imply (p, q))
    | And fs ->
        let* fs = scan_formulas fs in
        !(And fs)
    | Or fs ->
        let* fs = scan_formulas fs in
        !(Or fs)
    | Not f ->
        let* f = scan_formula f in
        !(Not f)
    | Equal ts ->
        let* ts = scan_terms ts in
        !(Equal ts)
    | NotEqual (x, y) ->
        let* x = scan_term x in
        let* y = scan_term y in
        !(NotEqual (x, y))
    | Less (x, y) ->
        let* x = scan_term x in
        let* y = scan_term y in
        !(Less (x, y))
    | LessOrEqual (x, y) ->
        let* x = scan_term x in
        let* y = scan_term y in
        !(LessOrEqual (x, y))
    | Greater (x, y) ->
        let* x = scan_term x in
        let* y = scan_term y in
        !(Greater (x, y))
    | GreaterOrEqual (x, y) ->
        let* x = scan_term x in
        let* y = scan_term y in
        !(GreaterOrEqual (x, y))
  and scan_term term =
    match term with
    | N -> attach time_term
    | (Bool _ | Int _ | Float _) as t -> attach t
    | Var (stream, time) ->
        let stream = localize_stream stream in
        let* time = scan_term time in
        !(Var (stream, time))
    | TupleTerm ts ->
        let* ts = scan_terms ts in
        !(TupleTerm ts)
    | Function (name, time, args) ->
        let* function_time = scan_term time in
        let* args = scan_terms args in
        fun state ->
          let inst_cnt, { inputs; variables; outputs; equations } =
            instantiate_node ctx inst_name name function_time state.inst_cnt
          in
          let arg_eqs =
            List.map2
              (fun x s -> Equal [ x; Var (s, function_time) ])
              args inputs
          in
          let output_streams =
            List.map (fun s -> Var (s, function_time)) outputs
          in
          let output =
            match output_streams with
            | [] ->
                assert false
                (* a function returning nothing should not exists *)
            | [ o ] -> o
            | l -> TupleTerm l
          in
          ( {
              inst_cnt;
              eqs_acc =
                List.(rev_append arg_eqs (rev_append equations state.eqs_acc));
              var_acc =
                List.concat [ inputs; variables; outputs; state.var_acc ];
            },
            output )
    | Add ts ->
        let* ts = scan_terms ts in
        !(Add ts)
    | Sub (x, y) ->
        let* x = scan_term x in
        let* y = scan_term y in
        !(Sub (x, y))
    | Neg t ->
        let* t = scan_term t in
        !(Neg t)
    | Mul ts ->
        let* ts = scan_terms ts in
        !(Mul ts)
    | Div (x, y) ->
        let* x = scan_term x in
        let* y = scan_term y in
        !(Div (x, y))
    | Mod (x, y) ->
        let* x = scan_term x in
        let* y = scan_term y in
        !(Mod (x, y))
    | IfThenElse (cond, x, y) ->
        let* cond = scan_formula cond in
        let* x = scan_term x in
        let* y = scan_term y in
        !(IfThenElse (cond, x, y))
    | IntOfReal t ->
        let* t = scan_term t in
        !(IntOfReal t)
    | RealOfInt t ->
        let* t = scan_term t in
        !(RealOfInt t)
    | Formula (f, time) ->
        let* f = scan_formula f in
        let* time = scan_term time in
        !(Formula (f, time))
  in
  let ({ inputs; outputs; equations; variables; _ } : node) =
    Context.find ctx node_name
  in
  state
  |> let* equations = scan_formulas equations in
     fun state ->
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

open Tree

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
  let rec transform_simple_term t =
    let* t = transform_term t in
    !(try_leaf t)
  and transform_simple_terms ts state = S.map transform_simple_term ts state
  and transform_terms ts state = S.map transform_term ts state
  and transform_formulas fs state = S.map transform_formula fs state
  and transform_term t =
    match t with
    | (N | Bool _ | Int _ | Float _) as t -> !(Leaf t)
    | Var (stream, time) ->
        let stream_tree = decompose_var stream in
        let* time = transform_simple_term time in
        !(map (fun stream -> Var (stream, time)) stream_tree)
    | TupleTerm ts ->
        let* ts = transform_terms ts in
        !(Node ts)
    | Function (name, time, args) -> (
        let* time = transform_simple_term time in
        let* args = transform_terms args in
        match node_tuple_status ctx name with
        | HasTupleOutput ->
            fun state ->
              let inst_cnt, { inputs; variables; outputs; equations } =
                instantiate_node ctx node_name name time state.inst_cnt
              in
              { state with inst_cnt }
              |> let* equations = transform_formulas equations in
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
                 fun state ->
                   ( {
                       inst_cnt;
                       eqs_acc =
                         List.(
                           rev_append arg_eqs
                             (rev_append equations state.eqs_acc));
                       var_acc =
                         List.concat
                           [
                             flat_inputs;
                             flat_variables;
                             flat_outputs;
                             state.var_acc;
                           ];
                     },
                     output )
        | HasTupleInputs ->
            let new_node_name = no_tuples ctx name in
            let args = List.concat (List.map leaves args) in
            !(Leaf (Function (new_node_name, time, args)))
        | HasNoTuples ->
            let args = List.map try_leaf args in
            !(Leaf (Function (name, time, args)))
        (* Multiple options: if the node outputs a tuple, inline the node and flatten its inputs,
           and if the node has inputs as tuples, apply [no_tuples] ont this node and call it.
           Otherhwise, keep this expression. [time] and [args] are transformed in all cases *)
        )
    | Add ts ->
        let* ts = transform_simple_terms ts in
        !(Leaf (Add ts))
    | Sub (x, y) ->
        let* x = transform_simple_term x in
        let* y = transform_simple_term y in
        !(Leaf (Sub (x, y)))
    | Neg t ->
        let* t = transform_simple_term t in
        !(Leaf (Neg t))
    | Mul ts ->
        let* ts = transform_simple_terms ts in
        !(Leaf (Mul ts))
    | Div (x, y) ->
        let* x = transform_simple_term x in
        let* y = transform_simple_term y in
        !(Leaf (Div (x, y)))
    | Mod (x, y) ->
        let* x = transform_simple_term x in
        let* y = transform_simple_term y in
        !(Leaf (Mod (x, y)))
    | IfThenElse (cond, x, y) ->
        let* cond = transform_formula cond in
        let* x = transform_term x in
        let* y = transform_term y in
        !(map2 (fun x y -> IfThenElse (cond, x, y)) x y)
    | IntOfReal t ->
        let* t = transform_simple_term t in
        !(Leaf (IntOfReal t))
    | RealOfInt t ->
        let* t = transform_simple_term t in
        !(Leaf (RealOfInt t))
    | Formula (f, time) ->
        let* f = transform_formula f in
        let* time = transform_simple_term time in
        !(Leaf (Formula (f, time)))
  and transform_formula f =
    match f with
    | Term t ->
        let* t = transform_simple_term t in
        !(Term t)
    | Imply (p, q) ->
        let* p = transform_formula p in
        let* q = transform_formula q in
        !(Imply (p, q))
    | And fs ->
        let* fs = transform_formulas fs in
        !(And fs)
    | Or fs ->
        let* fs = transform_formulas fs in
        !(Or fs)
    | Not f ->
        let* f = transform_formula f in
        !(Not f)
    | Equal ts ->
        let* eq_trees = transform_terms ts in
        let eqs = List.map (fun ts -> Equal ts) (flatten eq_trees) in
        !(match eqs with [] -> Term (Bool true) | [ x ] -> x | _ -> And eqs)
    | NotEqual (x, y) ->
        let* x_tree = transform_term x in
        let* y_tree = transform_term y in
        let neq_tree = map2 (fun x y -> NotEqual (x, y)) x_tree y_tree in
        !(match leaves neq_tree with
         | [] -> Term (Bool false)
         | [ x ] -> x
         | neqs -> Or neqs)
    | Less (x, y) ->
        let* x = transform_simple_term x in
        let* y = transform_simple_term y in
        !(Less (x, y))
    | LessOrEqual (x, y) ->
        let* x = transform_simple_term x in
        let* y = transform_simple_term y in
        !(LessOrEqual (x, y))
    | Greater (x, y) ->
        let* x = transform_simple_term x in
        let* y = transform_simple_term y in
        !(Greater (x, y))
    | GreaterOrEqual (x, y) ->
        let* x = transform_simple_term x in
        let* y = transform_simple_term y in
        !(GreaterOrEqual (x, y))
  in
  let ({ name; original_name; inputs; variables; outputs; equations } : node) =
    Context.find ctx node_name
  in
  let state, equations = transform_formulas equations (initial_state ()) in
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
  let rec transform_formulas fs state = S.map transform_formula fs state
  and transform_terms ts state = S.map transform_term ts state
  and transform_formula f =
    match f with
    | Term t ->
        let* t = transform_term t in
        !(Term t)
    | Imply (p, q) ->
        let* p = transform_formula p in
        let* q = transform_formula q in
        !(Imply (p, q))
    | And fs ->
        let* fs = transform_formulas fs in
        !(And fs)
    | Or fs ->
        let* fs = transform_formulas fs in
        !(Or fs)
    | Not f ->
        let* f = transform_formula f in
        !(Not f)
    | Equal ts ->
        let* ts = transform_terms ts in
        !(Equal ts)
    | NotEqual (x, y) ->
        let* x = transform_term x in
        let* y = transform_term y in
        !(NotEqual (x, y))
    | Less (x, y) ->
        let* x = transform_term x in
        let* y = transform_term y in
        !(Less (x, y))
    | LessOrEqual (x, y) ->
        let* x = transform_term x in
        let* y = transform_term y in
        !(LessOrEqual (x, y))
    | Greater (x, y) ->
        let* x = transform_term x in
        let* y = transform_term y in
        !(Greater (x, y))
    | GreaterOrEqual (x, y) ->
        let* x = transform_term x in
        let* y = transform_term y in
        !(GreaterOrEqual (x, y))
  and transform_term t =
    match t with
    | (N | Bool _ | Int _ | Float _) as t -> !t
    | Var (stream, time) ->
        let* time = transform_term time in
        !(Var (stream, time))
    | TupleTerm ts ->
        let* ts = transform_terms ts in
        !(TupleTerm ts)
    | Function (name, time, args) ->
        let* time = transform_term time in
        let* args = transform_terms args in
        !(Function (name, time, args))
    | Add ts ->
        let* ts = transform_terms ts in
        !(Add ts)
    | Sub (x, y) ->
        let* x = transform_term x in
        let* y = transform_term y in
        !(Sub (x, y))
    | Neg t ->
        let* t = transform_term t in
        !(Neg t)
    | Mul ts ->
        let* ts = transform_terms ts in
        !(Mul ts)
    | Div (x, y) ->
        let* x = transform_term x in
        let* y = transform_term y in
        !(Div (x, y))
    | Mod (x, y) ->
        let* x = transform_term x in
        let* y = transform_term y in
        !(Mod (x, y))
    | IfThenElse (cond, x, y) ->
        let* cond = transform_formula cond in
        let* x = transform_term x in
        let* y = transform_term y in
        !(IfThenElse (cond, x, y))
    | IntOfReal t ->
        let* t = transform_term t in
        !(IntOfReal t)
    | RealOfInt t ->
        let* t = transform_term t in
        !(RealOfInt t)
    | Formula (f, time) ->
        let* f = transform_formula f in
        let* time = transform_term time in
        fun state ->
          let new_var =
            { name = Printf.sprintf "aux_%d" state.inst_cnt; ty = Boolean }
          in
          let eq_left = Imply (Term (Var (new_var, time)), f)
          and eq_right = Imply (f, Term (Var (new_var, time))) in
          ( {
              inst_cnt = state.inst_cnt + 1;
              eqs_acc = eq_left :: eq_right :: state.eqs_acc;
              var_acc = new_var :: state.var_acc;
            },
            Var (new_var, time) )
  in
  let (({ variables; equations; _ } : node) as node) =
    Context.find ctx node_name
  in
  let state, equations = transform_formulas equations (initial_state ()) in
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
