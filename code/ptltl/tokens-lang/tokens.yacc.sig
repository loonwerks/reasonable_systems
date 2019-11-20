signature Spec_TOKENS =
sig
type ('a,'b) token
type svalue
val BAD:  'a * 'a -> (svalue,'a) token
val EOF:  'a * 'a -> (svalue,'a) token
val ID: (string) *  'a * 'a -> (svalue,'a) token
val RPAREN:  'a * 'a -> (svalue,'a) token
val LPAREN:  'a * 'a -> (svalue,'a) token
val TILDE:  'a * 'a -> (svalue,'a) token
val END:  'a * 'a -> (svalue,'a) token
val START:  'a * 'a -> (svalue,'a) token
val PREV:  'a * 'a -> (svalue,'a) token
val ONCE:  'a * 'a -> (svalue,'a) token
val ALWAYS:  'a * 'a -> (svalue,'a) token
val SINCE:  'a * 'a -> (svalue,'a) token
val WEDGE:  'a * 'a -> (svalue,'a) token
val DPLUS:  'a * 'a -> (svalue,'a) token
val VEE:  'a * 'a -> (svalue,'a) token
val DARROW:  'a * 'a -> (svalue,'a) token
val LONGARROW:  'a * 'a -> (svalue,'a) token
val FALSE:  'a * 'a -> (svalue,'a) token
val TRUE:  'a * 'a -> (svalue,'a) token
end
signature Spec_LRVALS=
sig
structure Tokens : Spec_TOKENS
structure ParserData:PARSER_DATA
sharing type ParserData.Token.token = Tokens.token
sharing type ParserData.svalue = Tokens.svalue
end
