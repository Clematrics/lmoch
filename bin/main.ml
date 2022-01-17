open Format
open Lexing
open Frontend
open Lexer
open Common

let usage = "usage: " ^ Sys.argv.(0) ^ " [options] file.lus main"

let parse_only = ref false

let type_only = ref false

let norm_only = ref false

let lucy_printer = ref false

let ocaml_printer = ref true

let verbose = ref false

let spec =
  [ ("-parse-only", Arg.Set parse_only, "  stops after parsing")
  ; ("-type-only", Arg.Set type_only, "  stops after typing")
  ; ("-norm-only", Arg.Set norm_only, "  stops after normalization")
  ; ("-verbose", Arg.Set verbose, "print intermediate transformations")
  ; ("-v", Arg.Set verbose, "print intermediate transformations")
  ]


let file, main_node =
  let file = ref None in
  let main = ref None in
  let set_file s =
    if not (Filename.check_suffix s ".lus")
    then raise (Arg.Bad "no .lus extension") ;
    file := Some s
  in
  let set_main s = main := Some s in
  let cpt = ref 0 in
  let set s =
    incr cpt ;
    match !cpt with
    | 1 ->
        set_file s
    | 2 ->
        set_main s
    | _ ->
        raise (Arg.Bad "Too many arguments")
  in
  Arg.parse spec set usage ;
  ( ( match !file with
    | Some f ->
        f
    | None ->
        Arg.usage spec usage ;
        exit 1 )
  , match !main with
    | Some n ->
        n
    | None ->
        Arg.usage spec usage ;
        exit 1 )


let report_loc (b, e) =
  let l = b.pos_lnum in
  let fc = b.pos_cnum - b.pos_bol + 1 in
  let lc = e.pos_cnum - b.pos_bol + 1 in
  eprintf "File \"%s\", line %d, characters %d-%d:\n" file l fc lc


let () =
  let c = open_in file in
  let lb = Lexing.from_channel c in
  try
    let f = Parser.file Lexer.token lb in
    close_in c ;
    if !parse_only then exit 0 ;
    let ft = Typing.type_file f main_node in
    if !verbose
    then (
      Format.printf "/**************************************/@." ;
      Format.printf "/* Typed ast                          */@." ;
      Format.printf "/**************************************/@." ;
      Typed_ast_printer.print_node_list_std ft ) ;
    if !type_only then exit 0 ;
    if main_node = "" then exit 0 ;
    (* Solve part *)
    let open Backend_aez in
    let ctx = Ir.Ast.of_file ft in
    let main_id = Hashstr.find ctx.tbl main_node in
    let main = List.assoc main_id ctx.nodes in
    List.iter (Format.printf "%a@." Ir.Ast.print_formula) main.equations;
    let delta, p = make_delta_p ctx.nodes main in
    ( try k_induction delta p 0 with
    | FalseProperty k ->
        printf "False property! Delta_0, ..., Delta_%i does not entail P_0, ..., P_%i@." k k
    | TrueProperty k ->
        printf "True property, proved after a %d-induction@." k
    | DontKnow k ->
        printf "Could not prove anything, stopped after a %d-induction@." k
    | Assert_failure (s, a, b) ->
        eprintf "Fatal failure: %s %d %d@." s a b ;
        Printexc.print_backtrace stderr) ;
    exit 0
  with
  | Lexical_error s ->
      report_loc (lexeme_start_p lb, lexeme_end_p lb) ;
      eprintf "lexical error: %s\n@." s ;
      exit 1
  | Parsing.Parse_error ->
      report_loc (lexeme_start_p lb, lexeme_end_p lb) ;
      eprintf "syntax error\n@." ;
      exit 1
  | Typing.Error (l, e) ->
      report_loc l ;
      eprintf "%a\n@." Typing.report e ;
      exit 1
  | e ->
      Printexc.register_printer (function Aez.(Smt.Error (Smt.DuplicateTypeName f)) -> Some (Aez.Hstring.view f) | _ -> None);
      eprintf "Anomaly: %s\n@." (Printexc.to_string e) ;
      Printexc.print_backtrace stderr;
      exit 2

(* open Aez
   open Smt

   let declare_symbol name t_in t_out =
     let x = Hstring.make name in
     (* création d'un symbole *)
     Symbol.declare x t_in t_out;
     (* déclaration de son type *)
     x

   let tic = declare_symbol "tic" [ Type.type_int ] Type.type_bool
   let ok = declare_symbol "ok" [ Type.type_int ] Type.type_bool
   let cpt = declare_symbol "cpt" [ Type.type_int ] Type.type_int
   let aux = declare_symbol "aux" [ Type.type_int ] Type.type_bool
   let zero = Term.make_int (Num.Int 0) (* constante 0 *)

   let one = Term.make_int (Num.Int 1) (* constante 1 *)

   let def_cpt n =
     (* cpt(n) = ite(n = 0, 0, cpt(n-1)) + ite(tic(n), 1, 0) *)
     let ite1 =
       (* ite(n = 0, 0, cpt(n-1)) *)
       Term.make_ite
         (Formula.make_lit Formula.Eq [ n; zero ])
         zero
         (Term.make_app cpt [ Term.make_arith Term.Minus n one ])
     in
     let ite2 =
       (* ite(tic(n), 1, 0) *)
       Term.make_ite
         (Formula.make_lit Formula.Eq [ Term.make_app tic [ n ]; Term.t_true ])
         one zero
     in
     (* cpt(n) = ite1 + ite2 *)
     Formula.make_lit Formula.Eq
       [ Term.make_app cpt [ n ]; Term.make_arith Term.Plus ite1 ite2 ]

   let def_ok n =
     (* ok(n) = ite(n = 0, true, aux(n)) *)
     Formula.make_lit Formula.Eq
       [
         Term.make_app ok [ n ];
         Term.make_ite
           (Formula.make_lit Formula.Eq [ n; zero ])
           Term.t_true
           (Term.make_app aux [ n ]);
       ]

   let def_aux n =
     let aux_n =
       (* aux(n) = true *)
       Formula.make_lit Formula.Eq [ Term.make_app aux [ n ]; Term.t_true ]
     in
     let pre_cpt_le_cpt =
       (* cpt(n-1) <= cpt(n) *)
       Formula.make_lit Formula.Le
         [
           Term.make_app cpt [ Term.make_arith Term.Minus n one ];
           Term.make_app cpt [ n ];
         ]
     in
     Formula.make Formula.And
       [
         Formula.make Formula.Imp [ aux_n; pre_cpt_le_cpt ];
         Formula.make Formula.Imp [ pre_cpt_le_cpt; aux_n ];
       ]

   let delta_incr n = Formula.make Formula.And [ def_cpt n; def_ok n; def_aux n ]

   let p_incr n =
     Formula.make_lit Formula.Eq [ Term.make_app ok [ n ]; Term.t_true ]

   module BMC_solver = Smt.Make ()
   module IND_solver = Smt.Make ()

   let base =
     BMC_solver.assume ~id:0 (delta_incr zero);
     BMC_solver.assume ~id:0 (delta_incr one);
     BMC_solver.check ();
     BMC_solver.entails ~id:0
       (Formula.make Formula.And [ p_incr zero; p_incr one ])

   let ind =
     let n = Term.make_app (declare_symbol "n" [] Type.type_int) [] in
     let n_plus_one = Term.make_arith Term.Plus n one in
     IND_solver.assume ~id:0 (Formula.make_lit Formula.Le [ zero; n ]);
     IND_solver.assume ~id:0 (delta_incr n);
     IND_solver.assume ~id:0 (delta_incr n_plus_one);
     IND_solver.assume ~id:0 (p_incr n);
     IND_solver.check ();
     IND_solver.entails ~id:0 (p_incr n_plus_one)

   let () =
     if not base then Format.printf "FALSE PROPERTY"
     else if ind then Format.printf "TRUE PROPERTY"
     else Format.printf "Don't know" *)
