open Format
open Lexing
open Frontend
open Lexer

let usage = "usage: " ^ Sys.argv.(0) ^ " [options] file.lus main"
let parse_only = ref false
let type_only = ref false
let norm_only = ref false
let lucy_printer = ref false
let ocaml_printer = ref true
let verbose = ref false

let spec =
  [
    ("-parse-only", Arg.Set parse_only, "  stops after parsing");
    ("-type-only", Arg.Set type_only, "  stops after typing");
    ("-norm-only", Arg.Set norm_only, "  stops after normalization");
    ("-verbose", Arg.Set verbose, "print intermediate transformations");
    ("-v", Arg.Set verbose, "print intermediate transformations");
  ]

let file, main_node =
  let file = ref None in
  let main = ref None in
  let set_file s =
    if not (Filename.check_suffix s ".lus") then
      raise (Arg.Bad "no .lus extension");
    file := Some s
  in
  let set_main s = main := Some s in
  let cpt = ref 0 in
  let set s =
    incr cpt;
    match !cpt with
    | 1 -> set_file s
    | 2 -> set_main s
    | _ -> raise (Arg.Bad "Too many arguments")
  in
  Arg.parse spec set usage;
  ( (match !file with
    | Some f -> f
    | None ->
        Arg.usage spec usage;
        exit 1),
    match !main with
    | Some n -> n
    | None ->
        Arg.usage spec usage;
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
    close_in c;
    if !parse_only then exit 0;
    let ft = Typing.type_file f main_node in
    if !verbose then (
      Format.printf "/**************************************/@.";
      Format.printf "/* Typed ast                          */@.";
      Format.printf "/**************************************/@.";
      Typed_ast_printer.print_node_list_std ft);
    if !type_only then exit 0;
    if main_node = "" then exit 0;
    (* Solve part *)
    let open BackendAez in
    let open Ir in
    let ctx = CompileIr.of_file ft in
    let main = Context.find ctx main_node in
    let main_name =
      (* main.name *)
      (* Transform.(apply_transform ctx main.name FullInlining) *)
      List.fold_left
        (Transform.apply_transform ctx)
        main.name
        [
          Transform.FullInlining; Transform.NoTuples; Transform.NoFormulaInTerm;
        ]
    in
    let main = Context.find ctx main_name in
    List.iter (Format.printf "%a@." Ir.Ast.print_formula) main.equations;
    let delta, p = make_delta_p ctx main.name in
    (try k_induction delta p 0 with
    | FalseProperty k ->
        printf
          "False property! Delta_0, ..., Delta_%i does not entail P_0, ..., \
           P_%i@."
          k k
    | TrueProperty k -> printf "True property, proved after a %d-induction@." k
    | DontKnow k ->
        printf "Could not prove anything, stopped after a %d-induction@." k
    | Assert_failure (s, a, b) ->
        eprintf "Fatal failure: %s %d %d@." s a b;
        Printexc.print_backtrace stderr);
    exit 0
  with
  | Lexical_error s ->
      report_loc (lexeme_start_p lb, lexeme_end_p lb);
      eprintf "lexical error: %s\n@." s;
      exit 1
  | Parsing.Parse_error ->
      report_loc (lexeme_start_p lb, lexeme_end_p lb);
      eprintf "syntax error\n@.";
      exit 1
  | Typing.Error (l, e) ->
      report_loc l;
      eprintf "%a\n@." Typing.report e;
      exit 1
  | e ->
      Printexc.register_printer (function
        | Aez.(Smt.Error (Smt.DuplicateTypeName f)) -> Some (Aez.Hstring.view f)
        | Aez.(Smt.Error (Smt.UnknownSymb f)) -> Some (Aez.Hstring.view f)
        | _ -> None);
      eprintf "Anomaly: %s\n@." (Printexc.to_string e);
      Printexc.print_backtrace stderr;
      exit 2
