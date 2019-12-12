open HolKernel Parse boolLib bossLib lcsymtacs;
open combinTheory pairTheory listTheory stringLib;

val _ = new_theory "ptltl";

Datatype
 `formula
   = Id string
   | Prim bool
   | Imp formula formula
   | Equiv formula formula
   | Or formula formula
   | Xor formula formula
   | And formula formula
   | Since formula formula
   | Always formula
   | Once formula
   | Prev formula
   | Start formula
   | End formula
   | Not formula`
;


Definition other_elm_def :
 other_elm = K F
End

Definition empty_state_def :
 empty_state = K F
End

val _ = DefnBase.add_cong LEFT_AND_CONG;

(*---------------------------------------------------------------------------*)
(* Start and End clauses are expanded versions of the original.              *)
(*---------------------------------------------------------------------------*)

Definition verify_def :
 verify trace form <=>
   let (elm,trace_prev) =
         (if NULL trace then (other_elm,[])
          else (HD trace, TL trace))
   in
    case form
     of Id str      => elm str
      | Prim b      => b
      | Not f       => ~verify trace f
      | Imp f1 f2   => (verify trace f1 ==> verify trace f2)
      | Equiv f1 f2 => (verify trace f1 <=> verify trace f2)
      | Or f1 f2    => (verify trace f1 \/ verify trace f2)
      | Xor f1 f2   => (verify trace f1 <> verify trace f2)
      | And f1 f2   => (verify trace f1 /\ verify trace f2)
      | Since f1 f2 => (verify trace f2 \/
                        (~NULL trace_prev /\ verify trace f1 /\
                         verify trace_prev (Since f1 f2)))
      | Always f    => (verify trace f /\
                        (NULL trace_prev \/
                         (~NULL trace_prev /\ verify trace_prev (Always f))))
      | Once f      => (verify trace f \/
                        (~NULL trace_prev /\ verify trace_prev (Once f)))
      | Prev f      => ((NULL trace_prev /\ verify trace f) \/ verify trace_prev f)
      | Start f     => verify trace f /\
                       ~((NULL trace_prev /\ verify trace f) \/ verify trace_prev f)
      | End f       => ((NULL trace_prev /\ verify trace f) \/ verify trace_prev f)
                        /\ ~verify trace f
Termination
WF_REL_TAC `inv_image ($< LEX $<) (\(x,y). (formula_size y, LENGTH x))`
 >> rw_tac list_ss [NULL_EQ,other_elm_def,combinTheory.K_DEF]
 >> TRY (Cases_on `trace` >> fs[])
 >> metis_tac[]
End

val _ = export_theory();
