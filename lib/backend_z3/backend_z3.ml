open Common
open Ir.Ast
open Tree
open Z3

let ctx = mk_context []
let bool_sort = Boolean.mk_sort ctx
let int_sort = Arithmetic.Integer.mk_sort ctx
let real_sort = Arithmetic.Real.mk_sort ctx

let rec declare_stream name ty =
  match ty with
  | Tuple tys ->
      Node
        (List.mapi
           (fun i ty -> declare_stream (name ^ "$" ^ string_of_int i) ty)
           tys)
  | _ ->
      let out_sort =
        match ty with
        | Boolean -> bool_sort
        | Integer -> int_sort
        | Real -> real_sort
        | Tuple _ -> assert false
      in
      let func = FuncDecl.mk_func_decl_s ctx name [ int_sort ] out_sort in
      Leaf func

let mk_mutually_eq ctx terms =
  let rec equalities = function
    | [] | [ _ ] -> assert false
    | [ f1; f2 ] -> [ Boolean.mk_eq ctx f1 f2 ]
    | f1 :: f2 :: l -> Boolean.mk_eq ctx f1 f2 :: equalities (f2 :: l)
  in
  Boolean.mk_and ctx (equalities terms)

let rec instantiate_node ?(inst_cnt = ref 0) ?(inst_name = "") nodes time_expr
    node =
  let equalities = ref [] in
  let { name; inputs; variables; outputs; equations } = node in
  let inst_name = inst_name ^ "$" ^ name ^ string_of_int !inst_cnt in
  let instantiate = instantiate_node ~inst_cnt ~inst_name nodes in
  let declare_streams =
    List.map (fun (id, name, ty) ->
        (id, declare_stream (inst_name ^ "$" ^ name ^ "_" ^ string_of_int id) ty))
  in
  let inputs = declare_streams inputs in
  let variables = declare_streams variables in
  let outputs = declare_streams outputs in
  let get_stream id =
    try List.assoc id inputs
    with Not_found -> (
      try List.assoc id variables
      with Not_found -> (
        try List.assoc id outputs with Not_found -> assert false))
  in
  let rec convert_formula = function
    | Term (Bool true) -> Leaf (Boolean.mk_true ctx)
    | Term (Bool false) -> Leaf (Boolean.mk_false ctx)
    | Term (Var (id, _, time)) ->
        let var_tree = get_stream id in
        let time_expr = try_leaf @@ convert_term time in
        tree_map (fun stream -> FuncDecl.apply stream [ time_expr ]) var_tree
    | Term _ ->
        raise
          (Invalid_argument
             "This term should not have occurred in convert_formula")
    | Imply (f1, f2) ->
        let f1 = try_leaf @@ convert_formula f1
        and f2 = try_leaf @@ convert_formula f2 in
        Leaf (Boolean.mk_implies ctx f1 f2)
    | And fs ->
        let fs = List.map (fun f -> try_leaf @@ convert_formula f) fs in
        assert (fs <> []) (* ensure there is at least one term *);
        Leaf (Boolean.mk_and ctx fs)
    | Or fs ->
        let fs = List.map (fun f -> try_leaf @@ convert_formula f) fs in
        assert (fs <> []) (* ensure there is at least one term *);
        Leaf (Boolean.mk_or ctx fs)
    | Not f ->
        let f = try_leaf @@ convert_formula f in
        Leaf (Boolean.mk_not ctx f)
    | Equal ts ->
        let forest = List.map convert_term ts in
        let fs =
          List.map (fun terms -> mk_mutually_eq ctx terms) (flatten forest)
        in
        Leaf (Boolean.mk_and ctx fs)
    | NotEqual (t1, t2) ->
        let t1 = convert_term t1 and t2 = convert_term t2 in
        let fs =
          List.map
            (fun terms -> Boolean.mk_not ctx (mk_mutually_eq ctx terms))
            (flatten [ t1; t2 ])
        in
        Leaf (Boolean.mk_or ctx fs)
    | Less (t1, t2) ->
        let t1 = try_leaf @@ convert_term t1
        and t2 = try_leaf @@ convert_term t2 in
        Leaf (Arithmetic.mk_lt ctx t1 t2)
    | LessOrEqual (t1, t2) ->
        let t1 = try_leaf @@ convert_term t1
        and t2 = try_leaf @@ convert_term t2 in
        Leaf (Arithmetic.mk_le ctx t1 t2)
    | Greater (t1, t2) ->
        let t1 = try_leaf @@ convert_term t1
        and t2 = try_leaf @@ convert_term t2 in
        Leaf (Arithmetic.mk_gt ctx t1 t2)
    | GreaterOrEqual (t1, t2) ->
        let t1 = try_leaf @@ convert_term t1
        and t2 = try_leaf @@ convert_term t2 in
        Leaf (Arithmetic.mk_ge ctx t1 t2)
  and convert_term = function
    | N -> Leaf time_expr
    | Bool true -> Leaf (Boolean.mk_true ctx)
    | Bool false -> Leaf (Boolean.mk_false ctx)
    | Int i -> Leaf (Arithmetic.Integer.mk_numeral_i ctx i)
    | Float f -> Leaf (Arithmetic.Real.mk_numeral_s ctx (string_of_float f))
    | Var (id, _, time) ->
        let var_tree = get_stream id in
        let time_expr = try_leaf @@ convert_term time in
        tree_map (fun stream -> FuncDecl.apply stream [ time_expr ]) var_tree
    | TupleTerm ts -> Node (List.map convert_term ts)
    | Function (id, time_expr, args) -> (
        Format.eprintf "Instantiating node with id %d@." id;
        let function_time = try_leaf @@ convert_term time_expr
        and args = List.map convert_term args in
        incr inst_cnt;
        let inputs, outputs, eqs =
          instantiate function_time (List.assoc id nodes)
        in
        let pp_connection fmt (id, func_tree) =
          let pp_func_decl fmt func_decl =
            Format.fprintf fmt "%s" (FuncDecl.to_string func_decl)
          in
          Format.fprintf fmt "(%d, %a)" id
            (Format.pp_print_list pp_func_decl)
            (leaves func_tree)
        in
        let pp_z3_expr fmt e = Format.fprintf fmt "%s" (Expr.to_string e) in
        Format.eprintf "With inputs@ %a@."
          (Format.pp_print_list pp_connection)
          inputs;
        Format.eprintf "With outputs@ %a@."
          (Format.pp_print_list pp_connection)
          outputs;
        Format.eprintf "With equations@ %a@."
          (Format.pp_print_list pp_z3_expr)
          eqs;
        let args_equalities =
          List.map2
            (fun (_, inp) arg ->
              tree_map2
                (fun x y -> Boolean.mk_eq ctx x y)
                (tree_map (fun inp -> FuncDecl.apply inp [ function_time ]) inp)
                arg)
            inputs args
          |> flatten |> List.concat
        in
        Format.eprintf "With argument equalities@ %a@."
          (Format.pp_print_list pp_z3_expr)
          args_equalities;
        equalities := args_equalities @ eqs @ !equalities;
        (* returns output as tuple of terms *)
        match outputs with
        | [] -> assert false
        | [ (_, o) ] -> tree_map (fun o -> FuncDecl.apply o [ function_time ]) o
        | _ ->
            tree_map
              (fun o -> FuncDecl.apply o [ function_time ])
              (Node (List.map snd outputs)))
    | Add ts ->
        let ts = List.map (fun t -> try_leaf @@ convert_term t) ts in
        Leaf (Arithmetic.mk_add ctx ts)
    | Sub (t1, t2) ->
        let t1 = try_leaf @@ convert_term t1
        and t2 = try_leaf @@ convert_term t2 in
        Leaf (Arithmetic.mk_sub ctx [ t1; t2 ])
    | Neg t ->
        let t = try_leaf @@ convert_term t in
        Leaf (Arithmetic.mk_unary_minus ctx t)
    | Mul ts ->
        let ts = List.map (fun t -> try_leaf @@ convert_term t) ts in
        Leaf (Arithmetic.mk_add ctx ts)
    | Div (t1, t2) ->
        let t1 = try_leaf @@ convert_term t1
        and t2 = try_leaf @@ convert_term t2 in
        Leaf (Arithmetic.mk_div ctx t1 t2)
    | Mod (t1, t2) ->
        let t1 = try_leaf @@ convert_term t1
        and t2 = try_leaf @@ convert_term t2 in
        Leaf (Arithmetic.Integer.mk_mod ctx t1 t2)
    | IfThenElse (cond, t1, t2) ->
        let cond = try_leaf @@ convert_formula cond in
        let t1 = convert_term t1 and t2 = convert_term t2 in
        tree_map2 (fun t1 t2 -> Boolean.mk_ite ctx cond t1 t2) t1 t2
    | IntOfReal t ->
        let t = try_leaf @@ convert_term t in
        Leaf (Arithmetic.Real.mk_real2int ctx t)
    | RealOfInt t ->
        let t = try_leaf @@ convert_term t in
        Leaf (Arithmetic.Integer.mk_int2real ctx t)
  in
  let equations =
    List.map (fun eq -> try_leaf @@ convert_formula eq) equations
  in
  (inputs, outputs, equations @ !equalities)

let make_delta_p nodes node =
  let delta_incr n =
    let _, _, equations = instantiate_node nodes n node in
    equations
  and p_incr n =
    let _, outputs, _ = instantiate_node nodes n node in
    let output_tree =
      match outputs with [ (_, o) ] -> o | _ -> assert false
    in
    let tree = tree_map (fun o -> FuncDecl.apply o [ n ]) output_tree in
    let equations = [ tree ] |> flatten |> List.concat in
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
