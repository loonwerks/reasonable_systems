open preamble basis;
open HolKernel Parse boolLib bossLib lcsymtacs;
open combinTheory pairTheory listTheory stringLib;

(*
open preamble basis MapProgTheory open ml_translatorLib ml_progLib basisFunctionsLib ml_translatorTheory cfTacticsBaseLib cfDivTheory cfDivLib charsetTheory regexpTheory regexp_compilerTheory;
*)

open ml_translatorLib;
open ml_progLib;
open fromSexpTheory astToSexprLib;

val _ = new_theory "ptltl";

Datatype `formula = Eid string | Prim bool
   | Imp formula formula
   | Equiv formula formula
   | Or formula formula
   | Xor formula formula
   | And formula formula
   | Since formula formula
   | Histor formula
   | Once formula
   | Prev formula
   | Start formula
   | End formula
   | Not formula`
;


Definition other_elm_def :
 other_elm : string -> bool = K F
End


(*---------------------------------------------------------------------------*)
(* Start and End clauses are expanded versions of the original. Need an      *)
(* extra congruence rule to extract the right termination conditions         *)
(*---------------------------------------------------------------------------*)


val _ = DefnBase.add_cong LEFT_AND_CONG;

Definition verify_def :
 verify trace form <=>
   let (elm,trace_prev) =
         (if NULL trace then (other_elm,[])
          else (HD trace, TL trace))
   in
    case form
     of Eid eid      => elm eid 
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
      | Histor f    => (verify trace f /\
                        (NULL trace_prev \/
                         (~NULL trace_prev /\ verify trace_prev (Histor f))))
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

(* state machine *)

Definition empty_state_def :
 empty_state = K F
End

Definition mk_subforms_def :
  mk_subforms form = (case form
  of Eid eid => [Eid eid]
   | Prim b => [Prim b]
   | Imp f1 f2 =>
       Imp f1 f2 :: (mk_subforms f1) ++ (mk_subforms f2)
   | Equiv f1 f2 =>
       Equiv f1 f2 :: (mk_subforms f1) ++ (mk_subforms f2)
   | Or f1 f2 =>
       Or f1 f2 :: (mk_subforms f1) ++ (mk_subforms f2)
   | Xor f1 f2 =>
       Xor f1 f2 :: (mk_subforms f1) ++ (mk_subforms f2)
   | And f1 f2 =>
       And f1 f2 :: (mk_subforms f1) ++ (mk_subforms f2)
   | Since f1 f2 =>
       Since f1 f2 :: (mk_subforms f1) ++ (mk_subforms f2)
   | Histor f =>
       Histor f :: (mk_subforms f)
   | Once f =>
       Once f :: (mk_subforms f)
   | Prev f =>
       Prev f :: (mk_subforms f)
   | Start f =>
       Start f :: (mk_subforms f)
   | End f =>
       End f :: (mk_subforms f)
   | Not f =>
       Not f :: (mk_subforms f)
  )

End


Definition decide_formula_start_def :
 decide_formula_start fm st elm =
  (case fm of
      Eid eid     => elm eid
    | Prim b      => b
    | Not f       => ~st f
    | Imp f1 f2   => (~ st f1) \/ st f2
    | Equiv f1 f2 => (st f1 = st f2)
    | Or f1 f2    => (st f1 \/ st f2)
    | Xor f1 f2   => ~(st f1 = st f2)
    | And f1 f2   => (st f1 /\ st f2)
    | Since f1 f2 => (st f1 /\ st f2)
    | Histor f    => st f
    | Once f      => st f
    | Prev f      => st f
    | Start f     => F
    | End f       => F
  )
End


Definition decide_formula_def :
 decide_formula fm st st_acc elm =
  (case fm of
     Eid eid => elm eid 
   | Prim b => b
   | Not f  => ~st_acc f
   | Imp f1 f2   => (~st_acc f1) \/ st_acc f2
   | Equiv f1 f2 => (st_acc f1 = st_acc f2)
   | Or f1 f2    => (st_acc f1 \/ st_acc f2)
   | Xor f1 f2   => ~(st_acc f1 = st_acc f2)
   | And f1 f2   => (st_acc f1 /\ st_acc f2)
   | Since f1 f2 => (st_acc f2 \/ (st_acc f1 /\ st (Since f1 f2)))
   | Histor f    => (st_acc f /\ st (Histor f))
   | Once f      => (st_acc f \/ st (Once f))
   | Prev f      => st f
   | Start f     => (st_acc f /\ ~st f)
   | End f       => (~st_acc f /\ st f)
 )
End

Definition transition_start_def :
 transition_start sforms elm =
   FOLDL
     (\st_acc fm.
         let decision = decide_formula_start fm st_acc elm
         in (\fm'. if fm = fm' then decision else (st_acc fm')))
     empty_state
     sforms
End

Definition transition_def:
 transition sforms st elm =
   FOLDL
     (\st_acc fm.
         let decision = decide_formula fm st st_acc elm
         in (\fm'. if fm = fm' then decision else (st_acc fm')))
      empty_state
      sforms
End

Definition mk_transitions_def :
 mk_transitions form =
   let subforms = REVERSE (nub (mk_subforms form));
   in (transition_start subforms,
       transition subforms)
End

Definition dfa_loop_def :
 dfa_loop delta form elms st =
   (case elms
     of [] => st form
      | elm :: elms' => dfa_loop delta form elms' (delta st elm))
End

Definition to_dfa_def :
 to_dfa form =
   let (delta_start, delta) = mk_transitions form;
   in \elms. case elms
              of [] => (delta_start other_elm) form 
               | elm :: elms' => dfa_loop delta form elms' (delta_start elm)
End





val _ = export_theory();