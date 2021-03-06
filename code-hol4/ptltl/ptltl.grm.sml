functor PtltlLrValsFun(structure Token : TOKEN)
 : sig structure ParserData : PARSER_DATA
       structure Tokens : Ptltl_TOKENS
   end
 =
struct
structure ParserData=
struct
structure Header =
struct
open PtltlTree
end
structure LrTable = Token.LrTable
structure Token = Token
local open LrTable in
val table=let val actionRows =
"\
\\001\000\001\000\013\000\002\000\012\000\009\000\011\000\010\000\010\000\
\\011\000\009\000\012\000\008\000\013\000\007\000\014\000\006\000\
\\015\000\005\000\017\000\004\000\000\000\
\\001\000\003\000\019\000\004\000\018\000\005\000\017\000\006\000\016\000\
\\007\000\015\000\008\000\014\000\016\000\033\000\000\000\
\\001\000\016\000\039\000\018\000\039\000\000\000\
\\001\000\016\000\040\000\018\000\040\000\000\000\
\\001\000\016\000\041\000\018\000\041\000\000\000\
\\001\000\016\000\042\000\018\000\042\000\000\000\
\\001\000\016\000\043\000\018\000\043\000\000\000\
\\001\000\016\000\044\000\018\000\044\000\000\000\
\\001\000\018\000\000\000\000\000\
\\035\000\003\000\019\000\004\000\018\000\005\000\017\000\006\000\016\000\
\\007\000\015\000\008\000\014\000\000\000\
\\036\000\000\000\
\\037\000\000\000\
\\038\000\000\000\
\\045\000\000\000\
\\046\000\000\000\
\\047\000\000\000\
\\048\000\000\000\
\\049\000\000\000\
\\050\000\000\000\
\\051\000\000\000\
\"
val actionRowNumbers =
"\000\000\009\000\010\000\000\000\
\\000\000\000\000\000\000\000\000\
\\000\000\000\000\012\000\011\000\
\\000\000\000\000\000\000\000\000\
\\000\000\000\000\001\000\018\000\
\\017\000\016\000\015\000\014\000\
\\013\000\007\000\006\000\005\000\
\\004\000\003\000\002\000\019\000\
\\008\000"
val gotoT =
"\
\\001\000\032\000\002\000\001\000\000\000\
\\000\000\
\\000\000\
\\002\000\018\000\000\000\
\\002\000\019\000\000\000\
\\002\000\020\000\000\000\
\\002\000\021\000\000\000\
\\002\000\022\000\000\000\
\\002\000\023\000\000\000\
\\002\000\024\000\000\000\
\\000\000\
\\000\000\
\\002\000\025\000\000\000\
\\002\000\026\000\000\000\
\\002\000\027\000\000\000\
\\002\000\028\000\000\000\
\\002\000\029\000\000\000\
\\002\000\030\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\"
val numstates = 33
val numrules = 17
val s = ref "" and index = ref 0
val string_to_int = fn () =>
let val i = !index
in index := i+2; Char.ord(String.sub(!s,i)) + Char.ord(String.sub(!s,i+1)) * 256
end
val string_to_list = fn s' =>
    let val len = String.size s'
        fun f () =
           if !index < len then string_to_int() :: f()
           else nil
   in index := 0; s := s'; f ()
   end
val string_to_pairlist = fn (conv_key,conv_entry) =>
     let fun f () =
         case string_to_int()
         of 0 => EMPTY
          | n => PAIR(conv_key (n-1),conv_entry (string_to_int()),f())
     in f
     end
val string_to_pairlist_default = fn (conv_key,conv_entry) =>
    let val conv_row = string_to_pairlist(conv_key,conv_entry)
    in fn () =>
       let val default = conv_entry(string_to_int())
           val row = conv_row()
       in (row,default)
       end
   end
val string_to_table = fn (convert_row,s') =>
    let val len = String.size s'
        fun f ()=
           if !index < len then convert_row() :: f()
           else nil
     in (s := s'; index := 0; f ())
     end
local
  val memo = Array.array(numstates+numrules,ERROR)
  val _ =let fun g i=(Array.update(memo,i,REDUCE(i-numstates)); g(i+1))
       fun f i =
            if i=numstates then g i
            else (Array.update(memo,i,SHIFT (STATE i)); f (i+1))
          in f 0 handle Subscript => ()
          end
in
val entry_to_action = fn 0 => ACCEPT | 1 => ERROR | j => Array.sub(memo,(j-2))
end
val gotoT=Array.fromList(string_to_table(string_to_pairlist(NT,STATE),gotoT))
val actionRows=string_to_table(string_to_pairlist_default(T,entry_to_action),actionRows)
val actionRowNumbers = string_to_list actionRowNumbers
val actionT = let val actionRowLookUp=
let val a=Array.fromList(actionRows) in fn i=>Array.sub(a,i) end
in Array.fromList(map actionRowLookUp actionRowNumbers)
end
in LrTable.mkLrTable {actions=actionT,gotos=gotoT,numRules=numrules,
numStates=numstates,initialState=STATE 0}
end
end
local open Header in
type pos = int
type arg = unit
structure MlyValue =
struct
datatype svalue = VOID | ntVOID of unit ->  unit
 | ID of unit ->  (string) | form_nt of unit ->  (formula)
 | tree_nt of unit ->  (formula)
end
type svalue = MlyValue.svalue
type result = formula
end
structure EC=
struct
open LrTable
val is_keyword =
fn _ => false
val preferred_change =
nil
val noShift =
fn (T 17) => true | _ => false
val showTerminal =
fn (T 0) => "TRUE"
  | (T 1) => "FALSE"
  | (T 2) => "LONGARROW"
  | (T 3) => "DARROW"
  | (T 4) => "VEE"
  | (T 5) => "DPLUS"
  | (T 6) => "WEDGE"
  | (T 7) => "SINCE"
  | (T 8) => "HISTOR"
  | (T 9) => "ONCE"
  | (T 10) => "PREV"
  | (T 11) => "START"
  | (T 12) => "END"
  | (T 13) => "TILDE"
  | (T 14) => "LPAREN"
  | (T 15) => "RPAREN"
  | (T 16) => "ID"
  | (T 17) => "EOF"
  | (T 18) => "BAD"
  | _ => "bogus-term"
local open Header in
val errtermvalue=
fn _ => MlyValue.VOID
end
val terms = (T 0) :: (T 1) :: (T 2) :: (T 3) :: (T 4) :: (T 5) :: (T 6
) :: (T 7) :: (T 8) :: (T 9) :: (T 10) :: (T 11) :: (T 12) :: (T 13)
 :: (T 14) :: (T 15) :: (T 17) :: (T 18) :: nil
end
structure Actions =
struct
type int = Int.int
exception mlyAction of int
local open Header in
val actions =
fn (i392:int,defaultPos,stack,
    (()):arg) =>
case (i392,stack)
of (0,(_,(MlyValue.form_nt form_nt1,form_nt1left,form_nt1right))::
rest671) => let val result=MlyValue.tree_nt(fn _ => let val form_nt as
form_nt1=form_nt1 ()
 in (form_nt) end
)
 in (LrTable.NT 0,(result,form_nt1left,form_nt1right),rest671) end
| (1,(_,(MlyValue.ID ID1,ID1left,ID1right))::rest671) => let val result
=MlyValue.form_nt(fn _ => let val ID as ID1=ID1 ()
 in (Eid ID) end
)
 in (LrTable.NT 1,(result,ID1left,ID1right),rest671) end
| (2,(_,(_,TRUE1left,TRUE1right))::rest671) => let val result=
MlyValue.form_nt(fn _ => (Prim true))
 in (LrTable.NT 1,(result,TRUE1left,TRUE1right),rest671) end
| (3,(_,(_,FALSE1left,FALSE1right))::rest671) => let val result=
MlyValue.form_nt(fn _ => (Prim false))
 in (LrTable.NT 1,(result,FALSE1left,FALSE1right),rest671) end
| (4,(_,(MlyValue.form_nt form_nt2,_,form_nt2right))::_::(_,(
MlyValue.form_nt form_nt1,form_nt1left,_))::rest671) => let val result
=MlyValue.form_nt(fn _ => let val form_nt1=form_nt1 ()
val form_nt2=form_nt2 ()
 in (Imp (form_nt1, form_nt2)) end
)
 in (LrTable.NT 1,(result,form_nt1left,form_nt2right),rest671) end
| (5,(_,(MlyValue.form_nt form_nt2,_,form_nt2right))::_::(_,(
MlyValue.form_nt form_nt1,form_nt1left,_))::rest671) => let val result
=MlyValue.form_nt(fn _ => let val form_nt1=form_nt1 ()
val form_nt2=form_nt2 ()
 in (Equiv (form_nt1, form_nt2)) end
)
 in (LrTable.NT 1,(result,form_nt1left,form_nt2right),rest671) end
| (6,(_,(MlyValue.form_nt form_nt2,_,form_nt2right))::_::(_,(
MlyValue.form_nt form_nt1,form_nt1left,_))::rest671) => let val result
=MlyValue.form_nt(fn _ => let val form_nt1=form_nt1 ()
val form_nt2=form_nt2 ()
 in (Or (form_nt1, form_nt2)) end
)
 in (LrTable.NT 1,(result,form_nt1left,form_nt2right),rest671) end
| (7,(_,(MlyValue.form_nt form_nt2,_,form_nt2right))::_::(_,(
MlyValue.form_nt form_nt1,form_nt1left,_))::rest671) => let val result
=MlyValue.form_nt(fn _ => let val form_nt1=form_nt1 ()
val form_nt2=form_nt2 ()
 in (Xor (form_nt1, form_nt2)) end
)
 in (LrTable.NT 1,(result,form_nt1left,form_nt2right),rest671) end
| (8,(_,(MlyValue.form_nt form_nt2,_,form_nt2right))::_::(_,(
MlyValue.form_nt form_nt1,form_nt1left,_))::rest671) => let val result
=MlyValue.form_nt(fn _ => let val form_nt1=form_nt1 ()
val form_nt2=form_nt2 ()
 in (And (form_nt1, form_nt2)) end
)
 in (LrTable.NT 1,(result,form_nt1left,form_nt2right),rest671) end
| (9,(_,(MlyValue.form_nt form_nt2,_,form_nt2right))::_::(_,(
MlyValue.form_nt form_nt1,form_nt1left,_))::rest671) => let val result
=MlyValue.form_nt(fn _ => let val form_nt1=form_nt1 ()
val form_nt2=form_nt2 ()
 in (Since (form_nt1, form_nt2)) end
)
 in (LrTable.NT 1,(result,form_nt1left,form_nt2right),rest671) end
| (10,(_,(MlyValue.form_nt form_nt1,_,form_nt1right))::(_,(_,
HISTOR1left,_))::rest671) => let val result=MlyValue.form_nt(fn _ =>
let val form_nt as form_nt1=form_nt1 ()
 in (Histor form_nt) end
)
 in (LrTable.NT 1,(result,HISTOR1left,form_nt1right),rest671) end
| (11,(_,(MlyValue.form_nt form_nt1,_,form_nt1right))::(_,(_,ONCE1left
,_))::rest671) => let val result=MlyValue.form_nt(fn _ => let val
form_nt as form_nt1=form_nt1 ()
 in (Once form_nt) end
)
 in (LrTable.NT 1,(result,ONCE1left,form_nt1right),rest671) end
| (12,(_,(MlyValue.form_nt form_nt1,_,form_nt1right))::(_,(_,PREV1left
,_))::rest671) => let val result=MlyValue.form_nt(fn _ => let val
form_nt as form_nt1=form_nt1 ()
 in (Prev form_nt) end
)
 in (LrTable.NT 1,(result,PREV1left,form_nt1right),rest671) end
| (13,(_,(MlyValue.form_nt form_nt1,_,form_nt1right))::(_,(_,
START1left,_))::rest671) => let val result=MlyValue.form_nt(fn _ => let
val form_nt as form_nt1=form_nt1 ()
 in (Start form_nt) end
)
 in (LrTable.NT 1,(result,START1left,form_nt1right),rest671) end
| (14,(_,(MlyValue.form_nt form_nt1,_,form_nt1right))::(_,(_,END1left,
_))::rest671) => let val result=MlyValue.form_nt(fn _ => let val
form_nt as form_nt1=form_nt1 ()
 in (End form_nt) end
)
 in (LrTable.NT 1,(result,END1left,form_nt1right),rest671) end
| (15,(_,(MlyValue.form_nt form_nt1,_,form_nt1right))::(_,(_,
TILDE1left,_))::rest671) => let val result=MlyValue.form_nt(fn _ => let
val form_nt as form_nt1=form_nt1 ()
 in (Not form_nt) end
)
 in (LrTable.NT 1,(result,TILDE1left,form_nt1right),rest671) end
| (16,(_,(_,_,RPAREN1right))::(_,(MlyValue.form_nt form_nt1,_,_))::(_,
(_,LPAREN1left,_))::rest671) => let val result=MlyValue.form_nt(fn _
 => let val form_nt as form_nt1=form_nt1 ()
 in (form_nt) end
)
 in (LrTable.NT 1,(result,LPAREN1left,RPAREN1right),rest671) end
| _ => raise (mlyAction i392)
end
val void = MlyValue.VOID
val extract = fn a => (fn MlyValue.tree_nt x => x
| _ => let exception ParseInternal
	in raise ParseInternal end) a ()
end
end
structure Tokens : Ptltl_TOKENS =
struct
type svalue = ParserData.svalue
type ('a,'b) token = ('a,'b) Token.token
fun TRUE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 0,(
ParserData.MlyValue.VOID,p1,p2))
fun FALSE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 1,(
ParserData.MlyValue.VOID,p1,p2))
fun LONGARROW (p1,p2) = Token.TOKEN (ParserData.LrTable.T 2,(
ParserData.MlyValue.VOID,p1,p2))
fun DARROW (p1,p2) = Token.TOKEN (ParserData.LrTable.T 3,(
ParserData.MlyValue.VOID,p1,p2))
fun VEE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 4,(
ParserData.MlyValue.VOID,p1,p2))
fun DPLUS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 5,(
ParserData.MlyValue.VOID,p1,p2))
fun WEDGE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 6,(
ParserData.MlyValue.VOID,p1,p2))
fun SINCE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 7,(
ParserData.MlyValue.VOID,p1,p2))
fun HISTOR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 8,(
ParserData.MlyValue.VOID,p1,p2))
fun ONCE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 9,(
ParserData.MlyValue.VOID,p1,p2))
fun PREV (p1,p2) = Token.TOKEN (ParserData.LrTable.T 10,(
ParserData.MlyValue.VOID,p1,p2))
fun START (p1,p2) = Token.TOKEN (ParserData.LrTable.T 11,(
ParserData.MlyValue.VOID,p1,p2))
fun END (p1,p2) = Token.TOKEN (ParserData.LrTable.T 12,(
ParserData.MlyValue.VOID,p1,p2))
fun TILDE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 13,(
ParserData.MlyValue.VOID,p1,p2))
fun LPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 14,(
ParserData.MlyValue.VOID,p1,p2))
fun RPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 15,(
ParserData.MlyValue.VOID,p1,p2))
fun ID (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 16,(
ParserData.MlyValue.ID (fn () => i),p1,p2))
fun EOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 17,(
ParserData.MlyValue.VOID,p1,p2))
fun BAD (p1,p2) = Token.TOKEN (ParserData.LrTable.T 18,(
ParserData.MlyValue.VOID,p1,p2))
end
end
