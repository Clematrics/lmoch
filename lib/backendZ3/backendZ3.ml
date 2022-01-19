open Ir
open Ast
open Z3

type time_term = Expr.expr
type constraints = Expr.expr list
type constraint_builder = time_term -> constraints

let required_transformations = Transform.[ FullInlining; NoTuples ]
let ctx = mk_context []
let bool_sort = Boolean.mk_sort ctx
let int_sort = Arithmetic.Integer.mk_sort ctx
let real_sort = Arithmetic.Real.mk_sort ctx

let declare_stream name ty =
  let out_sort =
    match ty with
    | Boolean -> bool_sort
    | Integer -> int_sort
    | Real -> real_sort
    | Tuple _ -> assert false
  in
  FuncDecl.mk_func_decl_s ctx name [ int_sort ] out_sort

let mk_mutually_eq ctx terms =
  let rec equalities = function
    | [] | [ _ ] -> assert false
    | [ f1; f2 ] -> [ Boolean.mk_eq ctx f1 f2 ]
    | f1 :: f2 :: l -> Boolean.mk_eq ctx f1 f2 :: equalities (f2 :: l)
  in
  Boolean.mk_and ctx (equalities terms)

let instantiate_node time_expr node =
  let equalities = ref [] in
  let { name = node_name; inputs; variables; outputs; equations; _ } = node in
  let declare_streams =
    List.map (fun { name; ty } ->
        (name, declare_stream (Printf.sprintf "%s$%s" node_name name) ty))
  in
  let inputs = declare_streams inputs in
  let variables = declare_streams variables in
  let outputs = declare_streams outputs in
  let get_stream ({ name; _ } : stream) =
    try List.assoc name inputs
    with Not_found -> (
      try List.assoc name variables
      with Not_found -> (
        try List.assoc name outputs with Not_found -> assert false))
  in
  let rec convert_formula = function
    | Term (Bool true) -> Boolean.mk_true ctx
    | Term (Bool false) -> Boolean.mk_false ctx
    | Term (Var (stream, time)) ->
        FuncDecl.apply (get_stream stream) [ convert_term time ]
    | Term _ ->
        raise
          (Invalid_argument
             "This term should not have occurred in convert_formula")
    | Imply (f1, f2) ->
        Boolean.mk_implies ctx (convert_formula f1) (convert_formula f2)
    | And fs ->
        assert (fs <> []) (* ensure there is at least one term *);
        Boolean.mk_and ctx (List.map convert_formula fs)
    | Or fs ->
        assert (fs <> []) (* ensure there is at least one term *);
        Boolean.mk_or ctx (List.map convert_formula fs)
    | Not f -> Boolean.mk_not ctx (convert_formula f)
    | Equal ts -> mk_mutually_eq ctx (List.map convert_term ts)
    | NotEqual (t1, t2) ->
        Boolean.mk_not ctx
          (mk_mutually_eq ctx [ convert_term t1; convert_term t2 ])
    | Less (t1, t2) -> Arithmetic.mk_lt ctx (convert_term t1) (convert_term t2)
    | LessOrEqual (t1, t2) ->
        Arithmetic.mk_le ctx (convert_term t1) (convert_term t2)
    | Greater (t1, t2) ->
        Arithmetic.mk_gt ctx (convert_term t1) (convert_term t2)
    | GreaterOrEqual (t1, t2) ->
        Arithmetic.mk_ge ctx (convert_term t1) (convert_term t2)
  and convert_term = function
    | N -> time_expr
    | Bool true -> Boolean.mk_true ctx
    | Bool false -> Boolean.mk_false ctx
    | Int i -> Arithmetic.Integer.mk_numeral_i ctx i
    | Float f -> Arithmetic.Real.mk_numeral_s ctx (string_of_float f)
    | Var (stream, time) ->
        FuncDecl.apply (get_stream stream) [ convert_term time ]
    | TupleTerm _ ->
        assert false
        (* should not happen if the NoTuples transformation was applied *)
    | Function _ ->
        assert false
        (* should not happen if the FullInlining transformation was applied *)
    | Add ts -> Arithmetic.mk_add ctx (List.map convert_term ts)
    | Sub (t1, t2) -> Arithmetic.mk_sub ctx [ convert_term t1; convert_term t2 ]
    | Neg t -> Arithmetic.mk_unary_minus ctx (convert_term t)
    | Mul ts -> Arithmetic.mk_add ctx (List.map convert_term ts)
    | Div (t1, t2) -> Arithmetic.mk_div ctx (convert_term t1) (convert_term t2)
    | Mod (t1, t2) ->
        Arithmetic.Integer.mk_mod ctx (convert_term t1) (convert_term t2)
    | IfThenElse (cond, t1, t2) ->
        Boolean.mk_ite ctx (convert_formula cond) (convert_term t1)
          (convert_term t2)
    | IntOfReal t -> Arithmetic.Real.mk_real2int ctx (convert_term t)
    | RealOfInt t -> Arithmetic.Integer.mk_int2real ctx (convert_term t)
    | Formula (f, _) -> convert_formula f
  in
  let equations = List.map convert_formula equations in
  (inputs, outputs, equations @ !equalities)

let make_delta_p ctx node_name =
  let node = Context.find ctx node_name in
  let delta_incr n =
    let _, _, equations = instantiate_node n node in
    equations
  and p_incr n =
    let _, outputs, _ = instantiate_node n node in
    let equations =
      List.map (fun (_, decl) -> FuncDecl.apply decl [ n ]) outputs
    in
    equations
  in
  (delta_incr, p_incr)

exception FalseProperty of int
exception TrueProperty of int
exception DontKnow of int

let check_assumptions solver =
  let res = Solver.check solver [] in
  match res with
  | SATISFIABLE -> ()
  | UNSATISFIABLE -> raise (Error "Assumptions are inconsistent")
  | UNKNOWN ->
      raise (Error "It is unknown whether assumptions are consistent or not")

let check_entails solver =
  let res = Solver.check solver [] in
  match res with
  | SATISFIABLE ->
      let exprs = Solver.get_assertions solver in
      let model = Option.get (Solver.get_model solver) in
      let funcs = Model.get_func_decls model in
      let func_vals =
        List.filter_map
          (fun func ->
            let sym = FuncDecl.get_name func in
            Option.map
              (fun interp -> (sym, interp))
              (Model.get_func_interp model func))
          funcs
      in
      List.iter
        (fun (sym, e) ->
          Format.printf "%s : %s@." (Symbol.to_string sym)
            (Model.FuncInterp.to_string e))
        func_vals;
      List.iter (fun e -> Format.printf "%s@." (Expr.to_string e)) exprs;
      false
  | UNSATISFIABLE -> true
  | UNKNOWN ->
      raise (Error "It is unknown whether assumptions are consistent or not")

let k_induction ?(max = 20) delta_incr p_incr =
  let bmc_solver = Solver.mk_simple_solver ctx
  and ind_solver = Solver.mk_simple_solver ctx in
  let n = Expr.mk_const_s ctx "N" int_sort in
  Solver.add ind_solver
  @@ Arithmetic.mk_le ctx (Arithmetic.Integer.mk_numeral_i ctx 0) n
     :: delta_incr n;
  let rec iteration k =
    if k > max then raise (DontKnow k);
    let base =
      Solver.add bmc_solver
      @@ delta_incr (Arithmetic.Integer.mk_numeral_i ctx k);
      check_assumptions bmc_solver;
      Solver.push bmc_solver;
      Solver.add bmc_solver
        [
          Boolean.mk_not ctx
            (Boolean.mk_and ctx
               (p_incr (Arithmetic.Integer.mk_numeral_i ctx k)));
        ];
      let res = check_entails bmc_solver in
      Solver.pop bmc_solver 1;
      res
    in
    if not base then raise @@ FalseProperty k;
    let ind =
      Solver.add ind_solver
      @@ delta_incr
           (Arithmetic.mk_add ctx
              [ n; Arithmetic.Integer.mk_numeral_i ctx (k + 1) ]);
      Solver.add ind_solver
      @@ p_incr
           (Arithmetic.mk_add ctx [ n; Arithmetic.Integer.mk_numeral_i ctx k ]);
      check_assumptions ind_solver;
      Solver.push ind_solver;
      Solver.add ind_solver
        [
          Boolean.mk_not ctx
            (Boolean.mk_and ctx
               (p_incr
                  (Arithmetic.mk_add ctx
                     [ n; Arithmetic.Integer.mk_numeral_i ctx (k + 1) ])));
        ];
      let res = check_entails ind_solver in
      Solver.pop ind_solver 1;
      res
    in
    if ind then raise @@ TrueProperty k;
    iteration (k + 1)
  in
  iteration 0
