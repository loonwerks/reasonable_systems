open preamble basis 
open ml_translatorLib;
open ml_progLib;
open fromSexpTheory astToSexprLib;
open HolKernel Parse boolLib bossLib lcsymtacs;
open combinTheory pairTheory listTheory stringLib;

open ptltlTheory traceTheory


fun main () = (let

val flagMapRef =
  ref [
    ("lex", false),
    ("gram", false),
    ("bigstep", false),
    ("smallstep", false),
    ("dotgraph", false),
    ("smallstep_monitor", false),
    ("dfa_monitor", false),
    ("help", false)
  ]

fun printHelp () = (
  print (
   "Usage: synthesize [options]\n" ^
   "\n" ^
   "Options: \n" ^
   "  lex <spec.pt>\n" ^
   "  gram <spec.pt>\n"^
   "  bigstep <spec.pt>\n"^
   "  smallstep <spec.pt>\n"^
   "  smallstep_monitor <spec.pt>\n"^
   "  dfa_monitor <spec.pt>\n"^
   "  dotgraph <spec.pt>\n"^
   "  help \n"^
   "\n"
  )
)

fun readFile filename = (
  (TextIO.openIn filename) handle (IO.Io {name, function, cause}) =>
    (print ("File \"" ^ name ^ "\" cannot be processed\n"); raise (Fail ""))
)

fun mkOutputFilename filename suffix = (let 
  val inStream = readFile filename
  val revtokens = List.rev (String.tokens (fn c => c = #"/") filename)
  val file_token = hd revtokens
  val rev_path_tokens = tl revtokens 
  val rev_derived_tokens = (file_token ^ suffix) :: rev_path_tokens 
in
  String.concatWith "/" (rev rev_derived_tokens) 
end)

fun printError filename (msg, line, col) = (let
  val posString = "[" ^ Int.toString line ^ ":" ^ Int.toString col ^ "] "
in
  print (filename ^ posString ^ msg ^ "\n")
end)


fun readStream inStream n = 
  case (TextIO.endOfStream inStream) of
    true => "" |
    false => TextIO.inputN (inStream, n)


fun lex [filename] = (let
  val inStream = readFile filename
  val lexer = PtltlChars.makeLexer (readStream inStream)

  val lexicon_filename = mkOutputFilename filename ".lexicon"
  val outStream = TextIO.openOut lexicon_filename 

  fun loop nextToken =
  let
    val tok = nextToken ()
    val _ = TextIO.output (outStream, (PtltlToken.format tok) ^ "\n") 
  in
    if PtltlToken.isEOF tok then () else (loop nextToken)
  end
in
  (loop lexer; TextIO.closeIn inStream; TextIO.closeOut outStream)
end)


fun gram [filename] = (let
  val inStream = readFile filename
  val tokenStream = PtltlCharStream.makeTokenStream (readStream inStream)
  val (tree, rem) = PtltlTokenStream.parse (15, tokenStream, printError filename)  
  val () = TextIO.closeIn inStream
  val grammar_filename = mkOutputFilename filename ".gram" 
  val outStream = TextIO.openOut grammar_filename
in
  TextIO.output (outStream, (PtltlTree.toString tree) ^ "\n")
end)


val common_hol_defs =  [
  K_DEF,
  NULL_DEF,
  HD,
  TL_DEF,
  FST,
  SND,
  FOLDL,
  FOLDR,
  REVERSE_DEF,
  IN_DEF,
  LIST_TO_SET_DEF,
  nub_def,
  EVERY_DEF,
  o_DEF,
  INDEX_FIND_def,
  OPTION_MAP_DEF,
  INDEX_OF_def,
  FIND_def,
  EL,
  SPLITP,
  FILTER,
  MAP,
  TOKENS_def,

  other_elm_def,
  empty_state_def,
  mk_subforms_def,
  decide_formula_start_def,
  decide_formula_def,
  transition_start_def,
  transition_def,
  mk_elm_def,
  mk_trace_def
]

fun bigstep [filename]  = (let
  val inStream = readFile filename
  val tokenStream = PtltlCharStream.makeTokenStream (readStream inStream)
  val (form, rem) = PtltlTokenStream.parse (15, tokenStream, printError filename)  
  val () = TextIO.closeIn inStream

  val spec_bigstep_term = ``\ trace . bigstep ^(PtltlTree.to_hol_form form) trace``;
  val spec_bigstep_def = Define `spec_bigstep = ^spec_bigstep_term`;
  (* translate HOL to CakeML*)
  val _ = map (fn hol_def => translate hol_def) common_hol_defs
  (* for some unknown reason, cakeml can't find the wellfoundedness proof *)
  val _ = translate bigstep_def 
  val _ = translate spec_bigstep_def 

  val _ = print "3";

  val lib_tm = get_ml_prog_state() |> get_prog

  val main_tm = process_topdecs `
    fun main u = (let
      val cl = CommandLine.arguments ()
      val str = String.concatWith " " cl
      val trace = mk_trace (String.explode str)
      val b_result = spec_bigstep trace
      val _ = TextIO.print (
        if b_result then
          "ACCEPTED"
        else
          "REJECTED"
      )
    in
      TextIO.output1 TextIO.stdOut #"\n"
    end)
  `;


  val call_tm =
  ``
    (Dlet unknown_loc (Pcon NONE [])
      (App Opapp [Var (Short "main"); Con NONE []]))
  ``

  val prog_tm = ``(^lib_tm ++ ^main_tm ++ [^call_tm])`` |> EVAL |> concl |> rhs
  
  val _ = write_ast_to_file (filename ^ ".bigstep.cml.sexp") prog_tm;

in
  ()
end)


fun smallstep [filename]  = (let
  val inStream = readFile filename
  val tokenStream = PtltlCharStream.makeTokenStream (readStream inStream)
  val (form, rem) = PtltlTokenStream.parse (15, tokenStream, printError filename)  
  val () = TextIO.closeIn inStream

  val spec_smallstep_term = ``smallstep ^(PtltlTree.to_hol_form form)`` |> EVAL  |> concl |> rhs
  val spec_smallstep_def = Define `spec_smallstep = ^spec_smallstep_term`;

  (* translate HOL to CakeML*)
  val _ = map (fn hol_def => translate hol_def) common_hol_defs
  val _ = translate spec_smallstep_def 

  val lib_tm = get_ml_prog_state() |> get_prog

  val main_tm = process_topdecs `
    fun main u = (let
      val cl = CommandLine.arguments ()
      val str = String.concatWith " " cl
      val trace = mk_trace (String.explode str)
      val b_result = spec_smallstep trace
      val _ = TextIO.print (
        if b_result then
          "ACCEPTED"
        else
          "REJECTED"
      )
    in
      TextIO.output1 TextIO.stdOut #"\n"
    end)
  `;


  val call_tm =
  ``
    (Dlet unknown_loc (Pcon NONE [])
      (App Opapp [Var (Short "main"); Con NONE []]))
  ``

  val prog_tm = ``(^lib_tm ++ ^main_tm ++ [^call_tm])`` |> EVAL |> concl |> rhs
  
  val _ = write_ast_to_file (filename ^ ".smallstep.cml.sexp") prog_tm;

in
  ()
end)



fun dfa_monitor [filename]  = (let

  val inStream = readFile filename
  val tokenStream = PtltlCharStream.makeTokenStream (readStream inStream)
  val (form, rem) = PtltlTokenStream.parse (15, tokenStream, printError filename)  
  val () = TextIO.closeIn inStream

  val top_form_term = (PtltlTree.to_hol_form form)

  val _ = print "ooga 1"

  val relational_data_term = (
    ``mk_relational_data (^top_form_term) T``
  ) |> EVAL |> concl |> rhs

  val _ = print "ooga 2"

  val table_data_term = (
    ``mk_table_data (^relational_data_term)``
  ) (* |> EVAL |> concl |> rhs ---- TODO: figure out problem with early stage evaluation *)

  val (dir_name, just_filename) = (let
    val path = OS.FileSys.fullPath filename
    val toks = (String.tokens (fn c => c = #"/") path)
    val prefix = List.take (toks, (List.length toks) - 1)
    val dir_name = "/" ^ (String.concatWith "/" prefix)
    val just_filename = List.last toks
  in
    (dir_name, just_filename)
  end)

  val _ = print "ooga 4"

  val _ = OS.FileSys.chDir dir_name

  val thy_name = (String.translate (fn c =>
    if c = #"." then
      "_"
    else
      (Char.toString c)
  ) (just_filename ^ "_dfa_monitor"))


  (*** NEW THEORY ***)
  val _ = new_theory thy_name

  val table_data_def = Define `table_data = ^table_data_term`;

  val _ = map (fn hol_def => translate hol_def) common_hol_defs
  val _ = translate extract_ids_def;
  val _ = translate mk_power_list_def;
  val _ = translate LENGTH;
  val _ = translate find_reachable_edges_def;
  val _ = translate mk_relational_data_def;
  val _ = translate mk_table_data_def;
  val _ = translate table_transition_def;
  val _ = translate table_data_def;

  val _ = export_theory();
  (*** EXPORT THEORY ***)


  val lib_tm = get_ml_prog_state() |> get_prog

  val main_tm = (process_topdecs `
    fun main u = (let

      val (state_to_index, (elm_to_idx, (finals, (table, start_idx)))) = table_data

      fun verify_trace (state_idx, trace) = (case trace of
        [] => state_idx |
        (elm :: trace') => (let
          val elm_idx = elm_to_idx elm
        in
          verify_trace ((table_transition table state_idx elm_idx), trace')
        end)
      )


      fun verify_input (state_idx, input) = (let
        val trace = mk_trace (String.explode input)
        val state_idx' = verify_trace (state_idx, trace)

        val result_string = 
          (if (List.nth finals state_idx') then
            "ACCEPTED"
          else
            "REJECTED"
          )
        val _ = print (result_string ^ "\n")
      in
        state_idx'
      end)


      fun repl state_idx = (let
        val _ = print "> "
        val line_op = (TextIO.inputLine TextIO.stdIn)
        val _ = Option.map (fn line => 
          repl (verify_input (state_idx, line))
        ) line_op
      in
        ()
      end) 

      val _ = repl start_idx 

    in 
      ()
    end)

  `);

  val call_tm =
  ``
    (Dlet unknown_loc (Pcon NONE [])
      (App Opapp [Var (Short "main"); Con NONE []]))
  ``

  val prog_tm = ``(^lib_tm ++ ^main_tm ++ [^call_tm])`` |> EVAL |> concl |> rhs

  val _ = write_ast_to_file (filename ^ ".dfa_monitor.cml.sexp") prog_tm

in
  ()
end)


fun default [filename]  = (let

  val inStream = readFile filename
  val tokenStream = PtltlCharStream.makeTokenStream (readStream inStream)
  val (form, rem) = PtltlTokenStream.parse (15, tokenStream, printError filename)  
  val () = TextIO.closeIn inStream

  val top_form_term = (PtltlTree.to_hol_form form)

  val relational_data_term = (
    ``mk_relational_data (^top_form_term) F``
  ) |> EVAL |> concl |> rhs

  val dotgraph_term = (
    ``to_dotgraph (^relational_data_term)``
  ) |> EVAL |> concl |> rhs

  val graph_str = stringSyntax.fromHOLstring dotgraph_term 

  val graph_filename = filename ^ ".dotgraph"
  val out_stream = TextIO.openOut graph_filename
  val () = TextIO.output (out_stream, graph_str)
  val () = TextIO.closeOut out_stream


  val table_data_term = (
    ``mk_table_data (^relational_data_term)``
  ) (* |> EVAL |> concl |> rhs ---- TODO: figure out problem with early stage evaluation *)

  val (dir_name, just_filename) = (let
    val path = OS.FileSys.fullPath filename
    val toks = (String.tokens (fn c => c = #"/") path)
    val prefix = List.take (toks, (List.length toks) - 1)
    val dir_name = "/" ^ (String.concatWith "/" prefix)
    val just_filename = List.last toks
  in
    (dir_name, just_filename)
  end)


  val _ = OS.FileSys.chDir dir_name

  val thy_name = (String.translate (fn c =>
    if c = #"." then
      "_"
    else
      (Char.toString c)
  ) (just_filename))


  (*** NEW THEORY ***)
  val _ = new_theory thy_name

  val table_data_def = Define `table_data = ^table_data_term`;

  val _ = map (fn hol_def => translate hol_def) common_hol_defs
  val _ = translate extract_ids_def;
  val _ = translate mk_power_list_def;
  val _ = translate LENGTH;
  val _ = translate find_reachable_edges_def;
  val _ = translate mk_relational_data_def;
  val _ = translate mk_table_data_def;
  val _ = translate table_transition_def;
  val _ = translate table_data_def;

  val _ = export_theory();
  (*** EXPORT THEORY ***)


  val lib_tm = get_ml_prog_state() |> get_prog

  val main_tm = (process_topdecs `
    fun main u = (let

      val (state_to_index, (elm_to_idx, (finals, (table, start_idx)))) = table_data

      fun verify_trace (state_idx, trace) = (case trace of
        [] => state_idx |
        (elm :: trace') => (let
          val elm_idx = elm_to_idx elm
        in
          verify_trace ((table_transition table state_idx elm_idx), trace')
        end)
      )


      fun verify_input (state_idx, input) = (let
        val trace = mk_trace (String.explode input)
        val state_idx' = verify_trace (state_idx, trace)

        val result_string = 
          (if (List.nth finals state_idx') then
            "ACCEPTED"
          else
            "REJECTED"
          )
        val _ = print (result_string ^ "\n")
      in
        state_idx'
      end)


      fun repl state_idx = (let
        val _ = print "> "
        val line_op = (TextIO.inputLine TextIO.stdIn)
        val _ = Option.map (fn line => 
          repl (verify_input (state_idx, line))
        ) line_op
      in
        ()
      end) 

      val _ = repl start_idx 

    in 
      ()
    end)

  `);

  val call_tm =
  ``
    (Dlet unknown_loc (Pcon NONE [])
      (App Opapp [Var (Short "main"); Con NONE []]))
  ``

  val prog_tm = ``(^lib_tm ++ ^main_tm ++ [^call_tm])`` |> EVAL |> concl |> rhs

  val _ = write_ast_to_file (filename ^ ".cml.sexp") prog_tm

in
  ()
end)



fun smallstep_monitor [filename]  = (let

  val inStream = readFile filename
  val tokenStream = PtltlCharStream.makeTokenStream (readStream inStream)
  val (form, rem) = PtltlTokenStream.parse (15, tokenStream, printError filename)  
  val () = TextIO.closeIn inStream

  val top_form_def = Define `top_form = ^(PtltlTree.to_hol_form form)`;
  val subforms_term = ``REVERSE (nub (mk_subforms top_form))`` |> EVAL |> concl |> rhs;
  val delta_start_term = ``transition_start ^subforms_term`` |> EVAL |> concl |> rhs;
  val delta_term = ``transition ^subforms_term`` |> EVAL |> concl |> rhs;
  val delta_start_def = Define `delta_start = ^delta_start_term`;
  val delta_def = Define `delta = ^delta_term`;

  val _ = map (fn hol_def => translate hol_def) common_hol_defs
  val _ = translate top_form_def 
  val _ = translate delta_start_def 
  val _ = translate delta_def 

  val lib_tm = get_ml_prog_state() |> get_prog


  val main_tm = (process_topdecs `
    fun main u = (let

      fun verify_trace (state_op, trace) = (case (state_op, trace) of
     
        (_, []) => state_op |

        (None, elm :: trace') => 
          verify_trace (Some (delta_start elm), trace') |


        (Some state, elm :: trace') => 
          verify_trace (Some (delta state elm), trace')

      )

      fun verify_input (state_op, input) = (let
        val trace = mk_trace (String.explode input)
        val state_op' = verify_trace (state_op, trace)

        val result_string = (case state_op' of
          None => "" |
          Some state' =>
            (if List.exists (fn subform => subform = top_form) state'  then
              "ACCEPTED"
            else
              "REJECTED"
            )
        )
        val _ = print (result_string ^ "\n")
      in
        state_op'
      end)


      fun repl state_op = (let
        val _ = print "> "
        val line_op = (TextIO.inputLine TextIO.stdIn)
        val _ = Option.map (fn line => 
          repl (verify_input (state_op, line))
        ) line_op
      in
        ()
      end) 

    in 
      repl None
    end)

  `);

  val call_tm =
  ``
    (Dlet unknown_loc (Pcon NONE [])
      (App Opapp [Var (Short "main"); Con NONE []]))
  ``

  val prog_tm = ``(^lib_tm ++ ^main_tm ++ [^call_tm])`` |> EVAL |> concl |> rhs
  
  val _ = write_ast_to_file (filename ^ ".smallstep_monitor.cml.sexp") prog_tm;

in
  ()
end)

fun dotgraph [filename]  = (let

  val inStream = readFile filename
  val tokenStream = PtltlCharStream.makeTokenStream (readStream inStream)
  val (form, rem) = PtltlTokenStream.parse (15, tokenStream, printError filename)  
  val () = TextIO.closeIn inStream

  val _ = print "... DFA concretization HOL4 ..."
  val dotgraph_term = ``to_dotgraph (mk_relational_data ^(PtltlTree.to_hol_form form) F)`` |> EVAL |> concl |> rhs
  val _ = print " completed\n"

  val graph_str = stringSyntax.fromHOLstring dotgraph_term 

  val graph_filename = filename ^ ".dotgraph"
  val out_stream = TextIO.openOut graph_filename
  val () = TextIO.output (out_stream, graph_str)
  val () = TextIO.closeOut out_stream
in
  ()
end)



fun lookup (map, key) =
  case (List.find (fn (k, v) => k = key) map) of
    SOME (_, v) => SOME v |
    NONE => NONE 


fun insert (map, key, v) = (key, v) :: map


fun flagSet flagMap str = (
  case (List.find (fn (k, v) => k = str) flagMap) of
    SOME (_, b) => b |
    NONE => false
)

fun handleRequest flagMap args = (
  List.app (fn (key, f) => 
    if (flagSet flagMap key) then (f args) else ()
  ) [
    ("lex", lex),
    ("gram", gram),
    ("smallstep", smallstep),
    ("smallstep_monitor", smallstep_monitor),
    ("dfa_monitor", dfa_monitor),
    ("dotgraph", dotgraph),
    ("default", default)
  ]
) handle 
   Fail m => (printHelp (); print ("failed : " ^ m)) |
   x => (printHelp (); raise x)


val argsRef = ref [] 


fun run () = (let
  val _ = (List.app
    (fn s => case (lookup (!flagMapRef, s)) of
      SOME _ => flagMapRef := (insert (!flagMapRef, s, true)) |
      NONE => (
        argsRef := (!argsRef) @ [s] 
      )
    )
    (CommandLine.arguments ())
  )

  fun hasTrue bs =
    case bs of
      [] => false |
      b :: bs' => b orelse (hasTrue bs')
  
  val hasFlag = (hasTrue (map (fn (k,v) => v) (!flagMapRef)))
  val helpReq = lookup (!flagMapRef, "help")
  
  val _ =
    case (hasFlag, helpReq, !argsRef) of
      (true, SOME false, args) => handleRequest (!flagMapRef) args |
      (false, SOME false, args) => handleRequest [("default", true)] args |
      _ => printHelp ()
  
in
  ()
end)


in
  (run () handle
    Fail x => print ("Failed with " ^ x) |
    x => raise x
  )
end)