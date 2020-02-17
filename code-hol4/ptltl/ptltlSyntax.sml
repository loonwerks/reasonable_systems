structure ptltlSyntax :> ptltlSyntax =
struct

open Feedback Lib HolKernel boolLib ptltlTheory;

val ERR = mk_HOL_ERR "ptltlSyntax";

val ptltl_ty = mk_thy_type{Tyop="formula",Thy="ptltl",Args = []};

val const_Eid   = prim_mk_const{Thy = "ptltl", Name = "Eid"};
val const_Prim  = prim_mk_const{Thy = "ptltl", Name = "Prim"};
val const_Not   = prim_mk_const{Thy = "ptltl", Name = "Not"};
val const_Imp   = prim_mk_const{Thy = "ptltl", Name = "Imp"};
val const_Equiv = prim_mk_const{Thy = "ptltl", Name = "Equiv"};
val const_Or    = prim_mk_const{Thy = "ptltl", Name = "Or"};
val const_Xor   = prim_mk_const{Thy = "ptltl", Name = "Xor"};
val const_And   = prim_mk_const{Thy = "ptltl", Name = "And"};
val const_Since = prim_mk_const{Thy = "ptltl", Name = "Since"};
val const_Histor = prim_mk_const{Thy = "ptltl", Name = "Histor"};
val const_Once  = prim_mk_const{Thy = "ptltl", Name = "Once"};
val const_Prev  = prim_mk_const{Thy = "ptltl", Name = "Prev"};
val const_Start = prim_mk_const{Thy = "ptltl", Name = "Start"};
val const_End   = prim_mk_const{Thy = "ptltl", Name = "End"};

fun mk_Eid t  = mk_comb(const_Eid,t);
fun mk_Prim t = mk_comb(const_Prim,t);
fun mk_Not t  = mk_comb(const_Not,t);
fun mk_Imp(t1,t2) = list_mk_comb (const_Imp,[t1,t2]);
fun mk_Equiv(t1,t2) = list_mk_comb (const_Equiv,[t1,t2]);
fun mk_Or(t1,t2) = list_mk_comb (const_Or,[t1,t2]);
fun mk_Xor(t1,t2) = list_mk_comb (const_Xor,[t1,t2]);
fun mk_And(t1,t2) = list_mk_comb (const_And,[t1,t2]);
fun mk_Since(t1,t2) = list_mk_comb (const_Since,[t1,t2]);
fun mk_Histor t = mk_comb(const_Histor,t);
fun mk_Once t = mk_comb(const_Once,t);
fun mk_Prev t = mk_comb(const_Prev,t);
fun mk_Start t = mk_comb(const_Start,t);
fun mk_End t = mk_comb(const_End,t);

val dest_Eid   = dest_monop const_Eid    (ERR "dest_Eid" "")
val dest_Prim  = dest_monop const_Prim   (ERR "dest_Prim" "")
val dest_Not   = dest_monop const_Not    (ERR "dest_Not" "")
val dest_Imp   = dest_binop const_Imp    (ERR "dest_Imp" "")
val dest_Equiv = dest_binop const_Equiv  (ERR "dest_Equiv" "")
val dest_Or    = dest_binop const_Or     (ERR "dest_Or" "")
val dest_Xor   = dest_binop const_Xor    (ERR "dest_Xor" "")
val dest_And   = dest_binop const_And    (ERR "dest_And" "")
val dest_Since = dest_binop const_Since  (ERR "dest_Since" "")
val dest_Histor = dest_monop const_Histor (ERR "dest_Histor" "")
val dest_Once  = dest_monop const_Once   (ERR "dest_Once" "")
val dest_Prev  = dest_monop const_Prev   (ERR "dest_Prev" "")
val dest_Start = dest_monop const_Start  (ERR "dest_Start" "")
val dest_End   = dest_monop const_End    (ERR "dest_End" "")
;

val is_Eid = Lib.can dest_Eid
val is_Prim = Lib.can dest_Prim
val is_Not  = Lib.can dest_Not
val is_Imp = Lib.can dest_Imp
val is_Equiv = Lib.can dest_Equiv
val is_Or = Lib.can dest_Or
val is_Xor = Lib.can dest_Xor
val is_And = Lib.can dest_And
val is_Since = Lib.can dest_Since
val is_Histor = Lib.can dest_Histor
val is_Once = Lib.can dest_Once
val is_Prev = Lib.can dest_Prev
val is_Start = Lib.can dest_Start
val is_End = Lib.can dest_End
;

end
