open Common
open Ir.Ast
open Aez
open Smt

let num_of_float f =
  match Float.classify_float f with
  | FP_normal ->
      (* Conversion of normal floating-point numbers
         Sign | Biased exponent from 62 to 52 | Mantissa from 51 to 0
      *)
      let bits = Int64.bits_of_float f in
      let sign = Int64.test_bit bits 63
      and biased_exp = Int64.extract bits 62 52
      and mantissa = Int64.(one #<< 52 #| (extract bits 51 0)) in
      let num_of_int64 n = Num.num_of_big_int (Big_int.big_int_of_int64 n) in
      let two = Num.num_of_int 2 in
      Num.(
        num_of_int (if sign then -1 else 1)
        */ num_of_int64 mantissa
        // (two **/ num_of_int 52)
        */ (two **/ (num_of_int64 biased_exp -/ num_of_int 1023)))
  | FP_subnormal ->
      (* Conversion of subnormal floating-point numbers
         Sign | Biased exponent from 62 to 52 is 0 | Mantissa from 51 to 0
      *)
      let bits = Int64.bits_of_float f in
      let sign = Int64.test_bit bits 63
      and mantissa = Int64.(extract bits 51 0) in
      let num_of_int64 n = Num.num_of_big_int (Big_int.big_int_of_int64 n) in
      let two = Num.num_of_int 2 in
      Num.(
        num_of_int (if sign then -1 else 1)
        */ num_of_int64 mantissa
        // (two **/ num_of_int 52)
        // (two **/ num_of_int 1022))
  | FP_zero ->
      Num.num_of_int 0
  | FP_infinite ->
      Num.(num_of_int 1 // num_of_int 0)
  | FP_nan ->
      Num.(num_of_int 0 // num_of_int 0)


open Tree

let rec declare_stream name ty =
  match ty with
  | Tuple tys ->
      Node
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
      Leaf h


let rec commutative_op op = function
  | [] ->
      raise (Invalid_argument "Must have at least one term")
  | [ t ] ->
      t
  | t :: (_ :: _ as l) ->
      Term.make_arith op t (commutative_op op l)


let logical_combinator comb fs =
  assert (List.mem comb Formula.[ And; Or ]) ;
  match fs with [] -> assert false | [ x ] -> x | _ -> Formula.make comb fs


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
        Leaf Formula.f_true
    | Term (Bool false) ->
        Leaf Formula.f_false
    | Term (Var (id, _, time)) ->
        let var_tree = get_stream id in
        let time_expr = try_leaf @@ convert_term time in
        tree_map
          (fun stream ->
            Formula.make_lit
              Formula.Eq
              [ Term.make_app stream [ time_expr ]; Term.t_true ] )
          var_tree
    | Term _ ->
        raise
          (Invalid_argument
             "This term should not have occurred in convert_formula" )
    | Imply (f1, f2) ->
        let f1 = try_leaf @@ convert_formula f1
        and f2 = try_leaf @@ convert_formula f2 in
        Leaf (Formula.make Formula.Imp [ f1; f2 ])
    | And fs ->
        let fs = List.map (fun f -> try_leaf @@ convert_formula f) fs in
        assert (fs <> []) (* ensure there is at least one term *) ;
        Leaf (logical_combinator Formula.And fs)
    | Or fs ->
        let fs = List.map (fun f -> try_leaf @@ convert_formula f) fs in
        assert (fs <> []) (* ensure there is at least one term *) ;
        Leaf (logical_combinator Formula.Or fs)
    | Not f ->
        let f = try_leaf @@ convert_formula f in
        Leaf (Formula.make Formula.Not [ f ])
    | Equal ts ->
        let forest = List.map convert_term ts in
        let fs =
          List.map
            (fun terms -> Formula.make_lit Formula.Eq terms)
            (flatten forest)
        in
        Leaf (logical_combinator Formula.And fs)
    | NotEqual (t1, t2) ->
        let t1 = convert_term t1
        and t2 = convert_term t2 in
        let fs =
          List.map
            (fun terms -> Formula.make_lit Formula.Neq terms)
            (flatten [ t1; t2 ])
        in
        Leaf (logical_combinator Formula.Or fs)
    | Less (t1, t2) ->
        let t1 = try_leaf @@ convert_term t1
        and t2 = try_leaf @@ convert_term t2 in
        Leaf (Formula.make_lit Formula.Lt [ t1; t2 ])
    | LessOrEqual (t1, t2) ->
        let t1 = try_leaf @@ convert_term t1
        and t2 = try_leaf @@ convert_term t2 in
        Leaf (Formula.make_lit Formula.Le [ t1; t2 ])
    | Greater (t1, t2) ->
        let t1 = try_leaf @@ convert_term t1
        and t2 = try_leaf @@ convert_term t2 in
        Leaf (Formula.make_lit Formula.Lt [ t2; t1 ])
    | GreaterOrEqual (t1, t2) ->
        let t1 = try_leaf @@ convert_term t1
        and t2 = try_leaf @@ convert_term t2 in
        Leaf (Formula.make_lit Formula.Le [ t2; t1 ])
  and convert_term = function
    | N ->
        Leaf time_expr (* Leaf (Term.make_app time []) *)
    | Bool true ->
        Leaf Term.t_true
    | Bool false ->
        Leaf Term.t_false
    | Int i ->
        Leaf (Term.make_int (Num.num_of_int i))
    | Float f ->
        Leaf (Term.make_real (num_of_float f))
    | Var (id, _, time) ->
        let var_tree = get_stream id in
        let time_expr = try_leaf @@ convert_term time in
        tree_map (fun stream -> Term.make_app stream [ time_expr ]) var_tree
    | TupleTerm ts ->
        Node (List.map convert_term ts)
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
                (fun x y -> Formula.make_lit Formula.Eq [ x; y ])
                (tree_map (fun inp -> Term.make_app inp [ function_time ]) inp)
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
            tree_map (fun o -> Term.make_app o [ function_time ]) o
        | _ ->
            tree_map
              (fun o -> Term.make_app o [ function_time ])
              (Node (List.map snd outputs)) )
    | Add ts ->
        let ts = List.map (fun t -> try_leaf @@ convert_term t) ts in
        Leaf (commutative_op Term.Plus ts)
    | Sub (t1, t2) ->
        let t1 = try_leaf @@ convert_term t1
        and t2 = try_leaf @@ convert_term t2 in
        Leaf (Term.make_arith Term.Minus t1 t2)
    | Neg t ->
        let t = try_leaf @@ convert_term t in
        let zero =
          (if Term.is_int t then Term.make_int else Term.make_real)
            (Num.num_of_int 0)
        in
        Leaf (Term.make_arith Term.Minus zero t)
    | Mul ts ->
        let ts = List.map (fun t -> try_leaf @@ convert_term t) ts in
        Leaf (commutative_op Term.Mult ts)
    | Div (t1, t2) ->
        let t1 = try_leaf @@ convert_term t1
        and t2 = try_leaf @@ convert_term t2 in
        Leaf (Term.make_arith Term.Div t1 t2)
    | Mod (t1, t2) ->
        let t1 = try_leaf @@ convert_term t1
        and t2 = try_leaf @@ convert_term t2 in
        Leaf (Term.make_arith Term.Modulo t1 t2)
    | IfThenElse (cond, t1, t2) ->
        let cond = try_leaf @@ convert_formula cond in
        let t1 = convert_term t1
        and t2 = convert_term t2 in
        tree_map2 (fun t1 t2 -> Term.make_ite cond t1 t2) t1 t2
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
    logical_combinator Formula.And equations
  and p_incr n =
    let _, outputs, _ = instantiate_node nodes n node in
    let output_tree =
      match outputs with [ (_, o) ] -> o | _ -> assert false
    in
    let tree =
      tree_map
        (fun o ->
          Formula.make_lit Formula.Eq [ Term.make_app o [ n ]; Term.t_true ] )
        output_tree
    in
    let eqs = [ tree ] |> flatten |> List.concat in
    logical_combinator Formula.And eqs
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

let k_induction ?(max = 20) delta_incr p_incr =
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
           (Term.make_arith Term.Plus n (Term.make_int (Num.num_of_int k))) ) ;
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

(* if k > max then raise (DontKnow k) ;
   let base =
     let module Bmc = Smt.Make () in
     for i = 0 to k do
       let d = delta (Term.make_int (Num.num_of_int i)) in
       Format.eprintf "%a@." Formula.print d ;
       Bmc.assume ~id:0 d
     done ;
     Bmc.check () ;
     let ps =
       List.init (k + 1) (fun i -> p (Term.make_int (Num.num_of_int i)))
     in
     let p = match ps with [ p ] -> p | ps -> Formula.make Formula.And ps in
     Format.eprintf "%a@." Formula.print p ;
     Bmc.entails ~id:0 p
   in
   if not base then raise (FalseProperty k) ;
   let ind =
     let module Ind = Smt.Make () in
     let n = Hstring.make "N" in
     Symbol.declare n [] Type.type_int ;
     let n = Term.make_app n [] in
     Ind.assume
       ~id:0
       (Formula.make_lit Formula.Le [ Term.make_int (Num.num_of_int 0); n ]) ;
     for i = 0 to k + 1 do
       let d =
         delta (Term.make_arith Term.Plus n (Term.make_int (Num.num_of_int i)))
       in
       Format.eprintf "%a@." Formula.print d ;
       Ind.assume ~id:0 d
     done ;
     for i = 0 to k do
       let p =
         p (Term.make_arith Term.Plus n (Term.make_int (Num.num_of_int i)))
       in
       Format.eprintf "%a@." Formula.print p ;
       Ind.assume ~id:0 p
     done ;
     Ind.check () ;
     let p =
       p (Term.make_arith Term.Plus n (Term.make_int (Num.num_of_int (k + 1))))
     in
     Format.eprintf "%a@." Formula.print p ;
     Ind.entails ~id:0 p
   in
   if ind then raise (TrueProperty k) ;
   k_induction delta p (k + 1) *)

(* let rec k_induction ?(max = 20) delta p k =
   if k > max then raise (DontKnow k) ;
   let base =
     let module Bmc = Smt.Make () in
     for i = 0 to k do
       let d = delta (Term.make_int (Num.num_of_int i)) in
       Format.eprintf "%a@." Formula.print d ;
       Bmc.assume ~id:0 d
     done ;
     Bmc.check () ;
     let ps =
       List.init (k + 1) (fun i -> p (Term.make_int (Num.num_of_int i)))
     in
     let p = match ps with [ p ] -> p | ps -> Formula.make Formula.And ps in
     Format.eprintf "%a@." Formula.print p ;
     Bmc.entails ~id:0 p
   in
   if not base then raise (FalseProperty k) ;
   let ind =
     let module Ind = Smt.Make () in
     let n = Hstring.make "N" in
     Symbol.declare n [] Type.type_int ;
     let n = Term.make_app n [] in
     Ind.assume
       ~id:0
       (Formula.make_lit Formula.Le [ Term.make_int (Num.num_of_int 0); n ]) ;
     for i = 0 to k + 1 do
       let d =
         delta (Term.make_arith Term.Plus n (Term.make_int (Num.num_of_int i)))
       in
       Format.eprintf "%a@." Formula.print d ;
       Ind.assume ~id:0 d
     done ;
     for i = 0 to k do
       let p =
         p (Term.make_arith Term.Plus n (Term.make_int (Num.num_of_int i)))
       in
       Format.eprintf "%a@." Formula.print p ;
       Ind.assume ~id:0 p
     done ;
     Ind.check () ;
     let p =
       p (Term.make_arith Term.Plus n (Term.make_int (Num.num_of_int (k + 1))))
     in
     Format.eprintf "%a@." Formula.print p ;
     Ind.entails ~id:0 p
   in
   if ind then raise (TrueProperty k) ;
   k_induction delta p (k + 1) *)
