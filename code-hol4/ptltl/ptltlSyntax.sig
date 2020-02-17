signature ptltlSyntax =
sig

include Abbrev

val formula : hol_type

val mk_Eid   : term -> term
val mk_Prim  : term -> term
val mk_Not   : term -> term
val mk_Imp   : term * term -> term
val mk_Equiv : term * term -> term
val mk_Or    : term * term -> term
val mk_Xor   : term * term -> term
val mk_And   : term * term -> term
val mk_Since : term * term -> term
val mk_Histor : term -> term
val mk_Once  : term -> term
val mk_Prev  : term -> term
val mk_Start : term -> term
val mk_End   : term -> term

val dest_And    : term -> term * term
val dest_Eid    : term -> term
val dest_End    : term -> term
val dest_Equiv  : term -> term * term
val dest_Histor : term -> term
val dest_Imp    : term -> term * term
val dest_Not    : term -> term
val dest_Once   : term -> term
val dest_Or     : term -> term * term
val dest_Prev   : term -> term
val dest_Prim   : term -> term
val dest_Since  : term -> term * term
val dest_Start  : term -> term
val dest_Xor    : term -> term * term

val is_And    : term -> bool
val is_Eid    : term -> bool
val is_End    : term -> bool
val is_Equiv  : term -> bool
val is_Histor : term -> bool
val is_Imp    : term -> bool
val is_Not    : term -> bool
val is_Once   : term -> bool
val is_Or     : term -> bool
val is_Prev   : term -> bool
val is_Prim   : term -> bool
val is_Since  : term -> bool
val is_Start  : term -> bool
val is_Xor    :  term -> bool

end
