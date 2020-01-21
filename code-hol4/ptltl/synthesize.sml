open preamble basis 

open ml_translatorLib;
open ml_progLib;
open fromSexpTheory astToSexprLib;

open ptltlTheory traceTheory

fun main () = (let

val flagMapRef =
  ref [
    ("lex", false),
    ("gram", false),
    ("bigstep", false),
    ("dfa", false),
    ("graph", false),
    ("monitor", false),
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
   "  dfa <spec.pt>\n"^
   "  graph <spec.pt>\n"^
   "  monitor <spec.pt>\n"^
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


(*
fun bigstep [filename]  = (let
  val inStream = readFile filename
  val tokenStream = PtltlCharStream.makeTokenStream (readStream inStream)
  val (form, rem) = PtltlTokenStream.parse (15, tokenStream, printError filename)  
  val () = TextIO.closeIn inStream

  val hol_form = PtltlTree.to_hol_form form

in
  ()
end)
*)


<<<<<<< HEAD
val common_hol_defs =  [
  K_DEF,
  NULL_DEF,
  HD,
  TL_DEF,
  FOLDL,
  REVERSE_DEF,
  IN_DEF,
  LIST_TO_SET_DEF,
  nub_def,
  FST,
  SND,
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
  mk_transitions_def,
  dfa_loop_def,
  mk_elm_def,
  mk_trace_def
]


=======
>>>>>>> origin/master
fun dfa [filename]  = (let
  val inStream = readFile filename
  val tokenStream = PtltlCharStream.makeTokenStream (readStream inStream)
  val (form, rem) = PtltlTokenStream.parse (15, tokenStream, printError filename)  
<<<<<<< HEAD
  val () = TextIO.closeIn inStream

  val hol_form = PtltlTree.to_hol_form form
  val hol_dfa_term = EVAL (SPEC hol_form to_dfa_def |> concl |> rhs) |> concl |> rhs;
  val hol_dfa_def = Define `dfa = ^hol_dfa_term`;

  (* translate HOL to CakeML*)
  val _ = map (fn hol_def => translate hol_def) common_hol_defs
  val _ = translate hol_dfa_def 
=======
  val _ = TextIO.print ("tree: " ^ (PtltlTree.toString form))
  val () = TextIO.closeIn inStream

  val hol_form = PtltlTree.to_hol_form form

  val hol_dfa_term = EVAL (SPEC hol_form to_dfa_def |> concl |> rhs) |> concl |> rhs;

  val hol_dfa_def = Define `dfa = ^hol_dfa_term`;


  (* compile HOL to CakeML*)
  
  val _ = map (fn hol_def => translate hol_def) [ 
    K_DEF,
    NULL_DEF,
    HD,
    TL_DEF,
    FOLDL,
    REVERSE_DEF,
    IN_DEF,
    LIST_TO_SET_DEF,
    nub_def,
    FST,
    SND,
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
    mk_transitions_def,
    dfa_loop_def,
    hol_dfa_def,
    mk_elm_def,
    mk_trace_def
  ]
>>>>>>> origin/master

  val lib_tm = get_ml_prog_state() |> get_prog

  val main_tm = process_topdecs `
<<<<<<< HEAD
    fun main u = (let
      val cl = CommandLine.arguments ()
      val str = String.concatWith " " cl
      val trace = mk_trace (String.explode str)
      val b_result = dfa trace
      val _ = TextIO.print (
        if b_result then
          "ACCEPTED!!"
        else
          "REJECTED!!"
      )
    in
      TextIO.output1 TextIO.stdOut #"\n"
    end)
=======
    fun main u =
        let
          val cl = CommandLine.arguments ()
          val str = String.concatWith " " cl
          val trace = mk_trace (String.explode str)
          val b_result = dfa trace
          val _ = TextIO.print (
            if b_result then
              "ACCEPTED!!"
            else
              "REJECTED!!"
          )
        in TextIO.output1 TextIO.stdOut #"\n" end
>>>>>>> origin/master
  `;


  val call_tm =
  ``
    (Dlet unknown_loc (Pcon NONE [])
      (App Opapp [Var (Short "main"); Con NONE []]))
  ``

  val prog_tm = ``(^lib_tm ++ ^main_tm ++ [^call_tm])`` |> EVAL |> concl |> rhs
  
  val _ = write_ast_to_file (filename ^ ".dfa.cml.sexp") prog_tm;

in
  ()
end)

<<<<<<< HEAD

fun monitor [filename]  = (let
  val inStream = readFile filename
  val tokenStream = PtltlCharStream.makeTokenStream (readStream inStream)
  val (form, rem) = PtltlTokenStream.parse (15, tokenStream, printError filename)  
  val () = TextIO.closeIn inStream

  val hol_form = PtltlTree.to_hol_form form
  val top_form_def = Define `top_form = ^hol_form`;


  val hol_transitions_term = EVAL (SPEC hol_form mk_transitions_def |> concl |> rhs) |> concl |> rhs;
  val hol_transitions_def = Define `transitions = ^hol_transitions_term`;

  val _ = map (fn hol_def => translate hol_def) common_hol_defs

  val _ = translate top_form_def 
  val _ = translate hol_transitions_def 

  val lib_tm = get_ml_prog_state() |> get_prog

  val main_tm = (process_topdecs `
    fun main u = (let
      val (transition_start, transition) = transitions 

      fun verify_trace (state_op, trace) = (case (state_op, trace) of
     
        (_, []) => state_op |

        (None, elm :: trace') => 
          verify_trace (Some (transition_start elm), trace') |


        (Some state, elm :: trace') => 
          verify_trace (Some (transition state elm), trace')

      )

      fun verify_input (state_op, input) = (let
        val trace = mk_trace (String.explode input)
        val state_op' = verify_trace (state_op, trace)

        val result_string = (case state_op' of
          None => "" |
          Some state' =>
            (if state' top_form  then
              "ACCEPTED!!"
            else
              "REJECTED!!"
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
  
  val _ = write_ast_to_file (filename ^ ".monitor.cml.sexp") prog_tm;


in
  ()
end)

=======
(*

fun monitor [filename]  = (let
  val inStream = readFile filename
  val tokenStream = CharStream.makeTokenStream (readStream inStream)
  val (form, rem) = TokenStream.parse (15, tokenStream, printError filename)  
  val () = TextIO.closeIn inStream


  val (transition_start, transition) = Tree.mk_transitions form

  fun verify_trace (state_op, trace) = (case (state_op, trace) of

    (_, []) => state_op |

    (NONE, elm :: trace') => 
      verify_trace (SOME (transition_start elm), trace') |

    (SOME state, elm :: trace') => 
      verify_trace (SOME (transition (state, elm)), trace')

  )

  fun verify_input (state_op, input) = (let
    val trace = Trace.mk_trace input 
    val state_op' = verify_trace (state_op, trace)
    val result_string = (case state_op' of
      NONE => "" |
      SOME state' =>
        (if state' form then
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
    val input_op = TextIO.inputLine TextIO.stdIn
  in
    (case input_op of
      NONE => () |
      SOME input => 
        repl (verify_input (state_op, input))
    )
  end)

in
  repl (NONE)
end)

*)
>>>>>>> origin/master

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
  if flagSet flagMap "lex" then lex args else ();
  if flagSet flagMap "gram" then gram args else ();
  if flagSet flagMap "dfa" then dfa args else ();
  if flagSet flagMap "monitor" then monitor args else ()
  (*
  ;
  fail ()
  if flagSet flagMap "bigstep" then mk_bigstep args else ();
  if flagSet flagMap "graph" then mk_graph args else ();
  *)
) handle 
   Fail m => print ("failed : " ^ m) |
   x => (raise x)


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

  (** DEBUG **)
  (*
  ** val _ = print ("hasFlag: " ^ (Bool.toString hasFlag) ^ "\n")

  ** val _ = (case helpReq of
  **   SOME b => print ("Some helpReq: " ^ (Bool.toString b) ^ "\n") |
  **   NONE => print ("None helpReq\n")
  ** )
  *)
  (****)
  
  val _ =
    case (hasFlag, helpReq, !argsRef) of
      (true, SOME false, args) => handleRequest (!flagMapRef) args |
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