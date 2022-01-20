open Common
open Ir
open Ast
open Aez
open Smt

type time_term = Term.t
type constraints = Formula.t
type constraint_builder = time_term -> constraints
type counter_example = unit

let name = "Alt-Ergo Zero"

let required_transformations =
  Transform.[ FullInlining; NoTuples; NoFormulaInTerm ]

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
  | FP_zero -> Num.num_of_int 0
  | FP_infinite -> Num.(num_of_int 1 // num_of_int 0)
  | FP_nan -> Num.(num_of_int 0 // num_of_int 0)

let declare_stream name ty =
  let h = Hstring.make name in
  try
    Symbol.declare h [ Type.type_int ]
      (match ty with
      | Boolean -> Type.type_bool
      | Integer -> Type.type_int
      | Real -> Type.type_real
      | Tuple _ ->
          assert false
          (* There is a tuple left, should have applied the transformation NoTuples first *))
  with Aez.Smt.(Error (DuplicateTypeName _)) -> assert false
(* if make_delta_p is called only once, this should not happen *)

let rec commutative_op op = function
  | [] -> raise (Invalid_argument "Must have at least one term")
  | [ t ] -> t
  | t :: (_ :: _ as l) -> Term.make_arith op t (commutative_op op l)

let logical_combinator comb fs =
  assert (List.mem comb Formula.[ And; Or ]);
  match fs with [] -> assert false | [ x ] -> x | _ -> Formula.make comb fs

let instantiate_node time_expr node =
  let { name = _node_name; inputs; outputs; equations; _ } = node in
  let get_stream (stream : stream) = Hstring.make stream.name in
  (* the variables and their name coincide by the Hstring construction *)
  let rec convert_formula = function
    | Term (Bool true) -> Formula.f_true
    | Term (Bool false) -> Formula.f_false
    | Term (Var (stream, time)) ->
        let time_expr = convert_term time in
        let app = get_stream stream in
        Formula.make_lit Formula.Eq
          [ Term.make_app app [ time_expr ]; Term.t_true ]
    | Term _ ->
        raise
          (Invalid_argument
             "This term should not have occurred in convert_formula")
    | Imply (f1, f2) ->
        Formula.make Formula.Imp [ convert_formula f1; convert_formula f2 ]
    | And fs ->
        assert (fs <> []) (* ensure there is at least one term *);
        let fs = List.map convert_formula fs in
        logical_combinator Formula.And fs
    | Or fs ->
        assert (fs <> []) (* ensure there is at least one term *);
        let fs = List.map convert_formula fs in
        logical_combinator Formula.Or fs
    | Not f -> Formula.make Formula.Not [ convert_formula f ]
    | Equal ts -> Formula.make_lit Formula.Eq (List.map convert_term ts)
    | NotEqual (t1, t2) ->
        Formula.make_lit Formula.Neq [ convert_term t1; convert_term t2 ]
    | Less (t1, t2) ->
        Formula.make_lit Formula.Lt [ convert_term t1; convert_term t2 ]
    | LessOrEqual (t1, t2) ->
        Formula.make_lit Formula.Le [ convert_term t1; convert_term t2 ]
    | Greater (t1, t2) ->
        Formula.make_lit Formula.Lt [ convert_term t2; convert_term t1 ]
    | GreaterOrEqual (t1, t2) ->
        Formula.make_lit Formula.Le [ convert_term t2; convert_term t1 ]
  and convert_term = function
    | N -> time_expr
    | Bool true -> Term.t_true
    | Bool false -> Term.t_false
    | Int i -> Term.make_int (Num.num_of_int i)
    | Float f -> Term.make_real (num_of_float f)
    | Var (stream, time) ->
        let time_expr = convert_term time in
        let app = get_stream stream in
        Term.make_app app [ time_expr ]
    | TupleTerm _ ->
        assert false
        (* This should not happen if the transformation NoTuples was applied *)
    | Function _ ->
        assert false
        (* This should not happen if a full inlining transformation was applied *)
    | Add ts ->
        let ts = List.map convert_term ts in
        commutative_op Term.Plus ts
    | Sub (t1, t2) ->
        Term.make_arith Term.Minus (convert_term t1) (convert_term t2)
    | Neg t ->
        let t = convert_term t in
        let zero =
          (if Term.is_int t then Term.make_int else Term.make_real)
            (Num.num_of_int 0)
        in
        Term.make_arith Term.Minus zero t
    | Mul ts -> commutative_op Term.Mult (List.map convert_term ts)
    | Div (t1, t2) ->
        Term.make_arith Term.Div (convert_term t1) (convert_term t2)
    | Mod (t1, t2) ->
        Term.make_arith Term.Modulo (convert_term t1) (convert_term t2)
    | IfThenElse (cond, t1, t2) ->
        Term.make_ite (convert_formula cond) (convert_term t1) (convert_term t2)
    | IntOfReal _t -> raise (Invalid_argument "int_of_real not implemented")
    | RealOfInt _t -> raise (Invalid_argument "real_of_int not implemented")
    | Formula _ -> assert false
    (* should not happen if the no_formulas_in_term was applied *)
  in
  let equations = List.map convert_formula equations in
  (inputs, outputs, equations)

let make_delta_p ctx node_name =
  let ({ inputs; variables; outputs; _ } as node) =
    Context.find ctx node_name
  in
  let declare_streams =
    List.iter (fun { name; ty } -> declare_stream name ty)
  in
  declare_streams inputs;
  declare_streams variables;
  declare_streams outputs;
  let delta_incr n =
    let _, _, equations = instantiate_node n node in
    logical_combinator Formula.And equations
  and p_incr n =
    let _, outputs, _ = instantiate_node n node in
    let get_stream ({ name; _ } : stream) = Hstring.make name in
    let eqs =
      List.map
        (fun stream ->
          Formula.make_lit Formula.Eq
            [ Term.make_app (get_stream stream) [ n ]; Term.t_true ])
        outputs
    in
    logical_combinator Formula.And eqs
  in
  (delta_incr, p_incr)

exception FalseProperty of int * counter_example
exception TrueProperty of int
exception DontKnow of int

let k_induction ?(max = 20) delta_incr p_incr =
  let module Bmc = Smt.Make () in
  let module Ind = Smt.Make () in
  let n =
    let n = Hstring.make "N" in
    Symbol.declare n [] Type.type_int;
    Term.make_app n []
  in
  Ind.assume ~id:0
    (Formula.make_lit Formula.Le [ Term.make_int (Num.num_of_int 0); n ]);
  Ind.assume ~id:0 (delta_incr n);
  let rec iteration k =
    if k > max then raise (DontKnow k);
    let base =
      Bmc.assume ~id:0 (delta_incr (Term.make_int (Num.num_of_int k)));
      Bmc.check ();
      Bmc.entails ~id:0 (p_incr (Term.make_int (Num.num_of_int k)))
    in
    if not base then raise @@ FalseProperty (k, ());
    let ind =
      Ind.assume ~id:0
        (delta_incr
           (Term.make_arith Term.Plus n
              (Term.make_int (Num.num_of_int (k + 1)))));
      Ind.assume ~id:0
        (p_incr
           (Term.make_arith Term.Plus n (Term.make_int (Num.num_of_int k))));
      Ind.check ();
      Ind.entails ~id:0
        (p_incr
           (Term.make_arith Term.Plus n
              (Term.make_int (Num.num_of_int (k + 1)))))
    in
    if ind then raise @@ TrueProperty k;
    iteration (k + 1)
  in
  iteration 0

let pp_counter_example fmt () =
  Format.fprintf fmt "Counter examples are not supported with Alt-Ergo Zero"
