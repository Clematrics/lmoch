open Common
open Ir.Ast
open Z3

let ctx = mk_context []

(* type tuple_sym = TupleName of tuple_sym list | AtomName of string

   let rec get_sort = function
   | Boolean -> Boolean.mk_sort ctx
   | Integer -> Arithmetic.Integer.mk_sort ctx
   | Real -> Arithmetic.Real.mk_sort ctx
   | Tuple _ as ty ->
       (* returns the name, the symbol and the sort associated to a tuple to build upper tuples *)
       let rec dfs ty = match ty with
       | Boolean -> "b", Symbol.mk_string ctx "b", get_sort ty
       | Integer -> "i", Symbol.mk_string ctx "i", get_sort ty
       | Real -> "r", Symbol.mk_string ctx "r", get_sort ty
       | Tuple tys ->
         let infos = List.map dfs tys in
         let sub_names = List.map (fun (name, _, _) -> name) infos in
         let sub_sorts = List.map (fun (_, _, sort) -> sort) infos in
         let tuple_name = Printf.sprintf "(%s)" @@ String.concat "_" sub_names in
         let proj_names = List.mapi (fun i _ -> Printf.sprintf "proj_%s_%d" tuple_name i) sub_names in
         let proj_syms = List.map (Symbol.mk_string ctx) proj_names in
         let tuple_sym = Symbol.mk_string ctx tuple_name in
         tuple_name, tuple_sym, Tuple.mk_sort ctx tuple_sym proj_syms sub_sorts
       in
       let _, _, sort = dfs ty in
       sort

   let declare_stream name ty =
     let sort = get_sort ty in
     let sym = Z3.Symbol.mk_string ctx name in
     Z3.FuncDecl.mk_const_decl ctx sym sort *)

type 'a tree =
  | Atom of 'a
  | Tuple of 'a tree list

let rec tree_map f = function
  | Atom x ->
      Atom (f x)
  | Tuple l ->
      Tuple (List.map (tree_map f) l)


let rec tree_map2 f t1 t2 =
  match (t1, t2) with
  | Atom x, Atom y ->
      Atom (f x y)
  | Tuple l, Tuple l' ->
      Tuple (List.map2 (tree_map2 f) l l')
  | _ ->
      raise (Invalid_argument "tree_map2 called with different trees")


let try_leaf = function
  | Atom x ->
      x
  | Tuple _ ->
      raise (Invalid_argument "Not a leaf")


let rec flatten forest =
  let rec flatten_atoms ?(acc = []) = function
    | [] ->
        List.rev acc
    | Atom x :: l ->
        flatten_atoms ~acc:(x :: acc) l
    | Tuple _ :: _ ->
        raise (Invalid_argument "Cannot flatten to a list of atoms")
  in
  let rec flatten_tuples acc = function
    | [] ->
        List.concat_map (fun forest -> flatten (List.rev forest)) acc
    | Atom _ :: _ ->
        raise (Invalid_argument "Cannot flatten to a list of tuples")
    | Tuple t :: l ->
        let rec f ?(acc = []) = function
          | [], [] ->
              acc
          | x :: t, y :: t' ->
              f ~acc:((x :: y) :: acc) (t, t')
          | _ ->
              raise (Invalid_argument "Cannot flatten when not of the same size")
        in
        let acc = f (t, acc) in
        flatten_tuples acc l
  in
  match forest with
  | [] ->
      []
  | Atom _ :: _ ->
      [ flatten_atoms forest ]
  | Tuple l :: _ ->
      flatten_tuples (List.map (fun _ -> []) l) forest


let rec declare_stream name ty =
  match ty with
  | Ir.Ast.Tuple tys ->
      Tuple
        (List.mapi
           (fun i ty -> declare_stream (name ^ "$" ^ string_of_int i) ty)
           tys )
  | _ ->
      let h = Hstring.make name in
      ( try
          Symbol.declare
            h
            [ Type.type_int ]
            ( match ty with
            | Boolean ->
                Type.type_bool
            | Integer ->
                Type.type_int
            | Real ->
                Type.type_real
            | Tuple _ ->
                assert false )
        with
      | Aez.Smt.(Error (DuplicateTypeName _)) ->
          () ) ;
      Atom h


let mk_equals ctx fs =
  (* TODO *)
  ()


let rec instantiate_node
    ?(inst_cnt = ref 0) ?(inst_name = "") nodes time_expr node =
  let equalities = ref [] in
  let { name; inputs; variables; outputs; equations } = node in
  let inst_name = inst_name ^ "_" ^ name ^ string_of_int !inst_cnt in
  let instantiate = instantiate_node ~inst_cnt ~inst_name nodes in
  (* let time = try_leaf @@ declare_stream (inst_name ^ "_n") Integer in *)
  let declare_streams =
    List.map (fun (id, name, ty) ->
        (id, declare_stream (inst_name ^ "$" ^ name ^ "_" ^ string_of_int id) ty) )
  in
  let inputs = declare_streams inputs in
  let variables = declare_streams variables in
  let outputs = declare_streams outputs in
  let get_stream id =
    try List.assoc id inputs with
    | Not_found ->
      ( try List.assoc id variables with
      | Not_found ->
        (try List.assoc id outputs with Not_found -> assert false) )
  in
  let rec convert_formula = function
    | Term (Bool true) ->
        Atom (Boolean.mk_true ctx)
    | Term (Bool false) ->
        Atom (Boolean.mk_false ctx)
    | Term (Var (id, _, time)) ->
        let var_tree = get_stream id in
        let time_expr = try_leaf @@ convert_term time in
        tree_map (fun stream -> FuncDecl.apply stream [ time_expr ]) var_tree
    | Term _ ->
        raise
          (Invalid_argument
             "This term should not have occurred in convert_formula" )
    | Imply (f1, f2) ->
        let f1 = try_leaf @@ convert_formula f1
        and f2 = try_leaf @@ convert_formula f2 in
        Atom (Boolean.mk_implies ctx f1 f2)
    | And fs ->
        let fs = List.map (fun f -> try_leaf @@ convert_formula f) fs in
        assert (fs <> []) (* ensure there is at least one term *) ;
        Atom (Boolean.mk_and ctx fs)
    | Or fs ->
        let fs = List.map (fun f -> try_leaf @@ convert_formula f) fs in
        assert (fs <> []) (* ensure there is at least one term *) ;
        Atom (Boolean.mk_or ctx fs)
    | Not f ->
        let f = try_leaf @@ convert_formula f in
        Atom (Boolean.mk_not ctx f)
    | Equal ts ->
        let forest = List.map convert_term ts in
        let fs =
          List.map
            (fun terms -> Formula.make_lit Formula.Eq terms)
            (flatten forest)
        in
        Atom (Boolean.mk_and ctx fs)
    | NotEqual (t1, t2) ->
        let t1 = convert_term t1
        and t2 = convert_term t2 in
        let fs =
          List.map
            (fun terms -> Boolean.mk_not ctx (Boolean.mk_eq ctx terms))
            (flatten [ t1; t2 ])
        in
        Atom (Boolean.mk_or ctx fs)
    | Less (t1, t2) ->
        let t1 = try_leaf @@ convert_term t1
        and t2 = try_leaf @@ convert_term t2 in
        Atom (Arithmetic.mk_lt ctx t1 t2)
    | LessOrEqual (t1, t2) ->
        let t1 = try_leaf @@ convert_term t1
        and t2 = try_leaf @@ convert_term t2 in
        Atom (Arithmetic.mk_le ctx t1 t2)
    | Greater (t1, t2) ->
        let t1 = try_leaf @@ convert_term t1
        and t2 = try_leaf @@ convert_term t2 in
        Atom (Arithmetic.mk_gt ctx t1 t2)
    | GreaterOrEqual (t1, t2) ->
        let t1 = try_leaf @@ convert_term t1
        and t2 = try_leaf @@ convert_term t2 in
        Atom (Arithmetic.mk_ge ctx t1 t2)
  and convert_term = function
    | N ->
        Atom time_expr (* Atom (Term.make_app time []) *)
    | Bool true ->
        Atom (Boolean.mk_true ctx)
    | Bool false ->
        Atom (Boolean.mk_false ctx)
    | Int i ->
        Atom (Arithmetic.Integer.mk_numeral_i ctx i)
    | Float f ->
        Atom (Arithmetic.Real.mk_numeral_s ctx (string_of_float f))
    | Var (id, _, time) ->
        let var_tree = get_stream id in
        let time_expr = try_leaf @@ convert_term time in
        tree_map (fun stream -> FuncDecl.apply stream [ time_expr ]) var_tree
    | TupleTerm ts ->
        Tuple (List.map convert_term ts)
    | Function (id, time_expr, args) ->
        let function_time = try_leaf @@ convert_term time_expr
        and args = List.map convert_term args in
        incr inst_cnt ;
        (* let time, inputs, outputs, eqs = instantiate (List.assoc id nodes) in *)
        let inputs, outputs, eqs =
          instantiate function_time (List.assoc id nodes)
        in
        (* link time with time and args with inputs *)
        (* let time_equality = Formula.make_lit Formula.Eq [ time; function_time ] *)
        let args_equalities =
          List.map2
            (fun (_, inp) arg ->
              tree_map2
                (fun x y -> Boolean.mk_eq ctx x y)
                (tree_map (fun inp -> FuncDecl.apply inp [ function_time ]) inp)
                arg )
            inputs
            args
          |> flatten
          |> List.concat
        in
        (* equalities := (time_equality :: args_equalities) @ eqs ; *)
        equalities := args_equalities @ eqs ;
        (* returns output as tuple of terms *)
        ( match outputs with
        | [] ->
            assert false
        | [ (_, o) ] ->
            tree_map (fun o -> FuncDecl.apply o [ function_time ]) o
        | _ ->
            tree_map
              (fun o -> FuncDecl.apply o [ function_time ])
              (Tuple (List.map snd outputs)) )
    | Add ts ->
        let ts = List.map (fun t -> try_leaf @@ convert_term t) ts in
        Atom (Arithmetic.mk_add ctx ts)
    | Sub (t1, t2) ->
        let t1 = try_leaf @@ convert_term t1
        and t2 = try_leaf @@ convert_term t2 in
        Atom (Arithmetic.mk_sub ctx [ t1; t2 ])
    | Neg t ->
        let t = try_leaf @@ convert_term t in
        Atom (Arithmetic.mk_unary_minus ctx t)
    | Mul ts ->
        let ts = List.map (fun t -> try_leaf @@ convert_term t) ts in
        Atom (Arithmetic.mk_add ctx ts)
    | Div (t1, t2) ->
        let t1 = try_leaf @@ convert_term t1
        and t2 = try_leaf @@ convert_term t2 in
        Atom (Arithmetic.mk_div ctx t1 t2)
    | Mod (t1, t2) ->
        let t1 = try_leaf @@ convert_term t1
        and t2 = try_leaf @@ convert_term t2 in
        Atom (Arithmetic.Integer.mk_mod ctx t1 t2)
    | IfThenElse (cond, t1, t2) ->
        let cond = try_leaf @@ convert_formula cond in
        let t1 = convert_term t1
        and t2 = convert_term t2 in
        tree_map2 (fun t1 t2 -> Boolean.mk_ite ctx cond t1 t2) t1 t2
    | IntOfReal _t ->
        raise (Invalid_argument "int_of_real not implemented")
    | RealOfInt _t ->
        raise (Invalid_argument "real_of_int not implemented")
  in
  let equations =
    List.map (fun eq -> try_leaf @@ convert_formula eq) equations @ !equalities
  in
  (* let time = Term.make_app time [] in *)
  (* (time, inputs, outputs, equations) *)
  (inputs, outputs, equations)


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


(* let delta_incr n =
     Formula.make
       Formula.Imp
       [ Formula.make_lit Formula.Eq [ n; time ]
       ; logical_combinator Formula.And equations
       ]
   and p_incr n =
     let tree =
       tree_map
         (fun o ->
           Formula.make_lit Formula.Eq [ Term.make_app o [ n ]; Term.t_true ] )
         output_tree
     in
     let eqs = [ tree ] |> flatten |> List.concat in
     logical_combinator Formula.And eqs
   in
   (delta_incr, p_incr) *)

exception FalseProperty of int

exception TrueProperty of int

exception DontKnow of int

(* let k_induction ?(max = 20) delta_incr p_incr =
   let module Bmc = Smt.Make () in
   let module Ind = Smt.Make () in
   let n =
     let n = Hstring.make "N" in
     Symbol.declare n [] Type.type_int ;
     Term.make_app n []
   in
   Ind.assume
     ~id:0
     (Formula.make_lit Formula.Le [ Term.make_int (Num.num_of_int 0); n ]) ;
   Ind.assume
     ~id:0
     (delta_incr
        (Term.make_arith Term.Plus n (Term.make_int (Num.num_of_int 0))) ) ;
   let rec iteration k =
     if k > max then raise (DontKnow k) ;
     let base =
       Bmc.assume ~id:0 (delta_incr (Term.make_int (Num.num_of_int k))) ;
       Bmc.check () ;
       Bmc.entails ~id:0 (p_incr (Term.make_int (Num.num_of_int (k + 1))))
     in
     if not base then raise @@ FalseProperty k ;
     let ind =
       Ind.assume
         ~id:0
         (delta_incr
            (Term.make_arith
               Term.Plus
               n
               (Term.make_int (Num.num_of_int (k + 1))) ) ) ;
       Ind.assume
         ~id:0
         (p_incr
            (Term.make_arith
               Term.Plus
               n
               (Term.make_int (Num.num_of_int k)) ) ) ;
       Ind.check () ;
       Ind.entails
         ~id:0
         (p_incr
            (Term.make_arith
               Term.Plus
               n
               (Term.make_int (Num.num_of_int (k + 1))) ) )
     in
     if ind then raise @@ TrueProperty k ;
     iteration (k + 1)
   in
   iteration 0
*)
