structure StringMap = MapFn(
  type hash_key = string
  val hashVal = HashString.hashString
  val sameKey = (op =)
) 

val flagMapRef =
  ref (StringMap.insertList (StringMap.empty, [
    ("--lex", false),
    ("--parse", false),
    ("--verify", false),
    ("--dfa", false),
    ("--help", false)
    ]))

fun printHelp () = (
  print "Usage: ptltl [options]\n" ;
  print "\n" ;
  print "Options: \n" ;
  print "  --lex <spec.pt>\n" ;
  print "  --parse <spec.pt>\n";
  print "  --verify <spec.pt> [trace]\n";
  print "  --dfa  <spec.pt> [trace]\n";
  print "  --help \n";
  print "\n" ;
  print "Trace: \n" ;
  print "  \"a a b a b a a b b\"\n";
  print "\n"
)

fun readFile filename =
  (TextIO.openIn filename) handle (IO.Io {name, function, cause}) =>
    (print ("File \"" ^ name ^ "\" cannot be processed\n"); raise (Fail ""))

fun mkOutputFilename filename suffix =
let 
  val inStream = readFile filename
  val revtokens = List.rev (String.tokens (fn c => c = #"/") filename)
  val file_token = hd revtokens
  val rev_path_tokens = tl revtokens 
  val rev_derived_tokens = (file_token ^ suffix) :: rev_path_tokens 
in
  String.concatWith "/" (rev rev_derived_tokens) 
end

fun printError filename (msg, line, col) =
let
  val posString = "[" ^ Int.toString line ^ ":" ^ Int.toString col ^ "] "
in
  print (filename ^ posString ^ msg ^ "\n")
end


fun readStream inStream n = 
  case (TextIO.endOfStream inStream) of
    true => "" |
    false => TextIO.inputN (inStream, n)


fun lex [filename] = let
  val inStream = readFile filename
  val lexer = Chars.makeLexer (readStream inStream)

  fun loop nextToken =
  let
    val tok = nextToken ()
    val _ = print ((Token.format tok) ^ "\n") 
  in
    if Token.isEOF tok then () else (loop nextToken)
  end
in
  (loop lexer; TextIO.closeIn inStream)
end


fun parse [filename] =
let
  val inStream = readFile filename
  val tokenStream = CharStream.makeTokenStream (readStream inStream)
  val (tree, rem) = TokenStream.parse (15, tokenStream, printError filename)  
  val () = TextIO.closeIn inStream
  (*
  val parsedFilename = mkOutputFilename filename ".parsed" 
  val outStream = TextIO.openOut parsedFilename
  *)
in
  print ((Tree.toString tree) ^ "\n") 
end


fun verify [filename, trace_str]  = (let
  val inStream = readFile filename
  val tokenStream = CharStream.makeTokenStream (readStream inStream)
  val (form, rem) = TokenStream.parse (15, tokenStream, printError filename)  
  val () = TextIO.closeIn inStream

  val trace = rev (String.split_pattern (trace_str, "[ \t\n]+"))
  val answer = (
    if (Tree.verify (trace, form)) then
      "ACCEPTED"
    else
      "REJECTED"
  )

in
  print (answer ^ "\n")
end)

fun verify_via_dfa [filename, trace_str]  = (let
  val inStream = readFile filename
  val tokenStream = CharStream.makeTokenStream (readStream inStream)
  val (form, rem) = TokenStream.parse (15, tokenStream, printError filename)  
  val () = TextIO.closeIn inStream

  val dfa = Tree.to_dfa form
  val trace = (String.split_pattern (trace_str, "[ \t\n]+"))

  val answer = (
    if (dfa trace) then
      "ACCEPTED"
    else
      "REJECTED"
  )

in
  print (answer ^ "\n")
end)



fun flagSet flagMap str =
  case StringMap.lookup (flagMap, str) of
    SOME b => b |
    NONE => false

fun handleRequest flagMap args = (
  if flagSet flagMap "--lex" then lex args else ();
  if flagSet flagMap "--parse" then parse args else ();
  if flagSet flagMap "--verify" then verify args else ();
  if flagSet flagMap "--dfa" then verify_via_dfa args else ()
) handle 
   Fail m => print ("failed : " ^ m) |
   x => (raise x)


val argsRef = ref [] 


fun run () =
let
  val _ = app
    (fn s => case StringMap.lookup (!flagMapRef, s) of
      SOME _ => flagMapRef := StringMap.insert (!flagMapRef, s, true) |
      NONE => (
        if (not (String.isPrefix "--" s)) then
          argsRef := (!argsRef) @ [s] 
        else
          flagMapRef := (StringMap.insert (!flagMapRef, "--help", true))
      )
   )
   (CommandLine.arguments ())

  fun hasTrue bs =
    case bs of
      [] => false |
      b :: bs' => b orelse (hasTrue bs')
  
  val hasFlag = (hasTrue (StringMap.listValues (!flagMapRef)))
  val helpReq = StringMap.lookup (!flagMapRef, "--help")

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
  
in ()
end

val _ = run () handle
  Fail x => print ("Failed with " ^ x) |
  x => raise x