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
   | Histor formula
   | Once formula
   | Prev formula
   | Start formula
   | End formula
   | Not formula`
;


Definition other_elm_def :
 other_elm = K F
End

Definition remove_dups_f_def :
  remove_dups_f xs f =
  (case xs
  of [] => []
   | x :: xs' =>
     let xs'' = FILTER (\ y . (f y) <> (f x)) xs' in
     x :: (remove_dups_f xs'' f)
  )
Termination
WF_REL_TAC `measure (\(xs, _). (LENGTH xs))`
>> (Induct_on `xs'`
   >- fs []
   >- (rw [LENGTH]
      >- fs []
      >- (fs [LENGTH]
         >> `LENGTH (FILTER (λy. f y ≠ f x) xs') < SUC (LENGTH xs')` by rw []
         >> rw []
      )
   )
)
End


Definition remove_dups_def :
  remove_dups xs = remove_dups_f xs (\x.x)
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
  of Id str => [Id str]
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
 decide_formula_start fm state elm =
  (case fm
    of Id str     => elm str
    | Prim b      => b
    | Not f       => ~state f
    | Imp f1 f2   => ~(state f1 \/ state f2)
    | Equiv f1 f2 => (state f1 = state f2)
    | Or f1 f2    => (state f1 \/ state f2)
    | Xor f1 f2   => ~(state f1 = state f2)
    | And f1 f2   => (state f1 /\ state f2)
    | Since f1 f2 => (state f1 /\ state f2)
    | Always f    => state f
    | Once f      => state f
    | Prev f      => state f
    | Start f     => F
    | End f       => F
  )
End

Definition decide_formula_def :
 decide_formula fm state state_acc elm =
  (case fm of
     Id str => elm str
   | Prim b => b
   | Not f  => ~state_acc f
   | Imp f1 f2   => (~state_acc f1 \/ state_acc f2)
   | Equiv f1 f2 => (state_acc f1 = state_acc f2)
   | Or f1 f2    => (state_acc f1 \/ state_acc f2)
   | Xor f1 f2   => ~(state_acc f1 = state_acc f2)
   | And f1 f2   => (state_acc f1 /\ state_acc f2)
   | Since f1 f2 => (state_acc f2 \/ (state_acc f1 /\ state (Since f1 f2)))
   | Always f    => (state_acc f /\ state (Always f))
   | Once f      => (state_acc f \/ state (Once f))
   | Prev f      => state f
   | Start f     => (state_acc f /\ ~state f)
   | End f       => (~state_acc f /\ state f)
 )
End

Definition transition_start_def :
 transition_start sforms elm =
   FOLDL
     (\state_acc fm.
         let decision = decide_formula_start fm state_acc elm
         in (\fm'. if fm = fm' then decision else (state_acc fm')))
     empty_state
     sforms
End

Definition transition_def:
 transition sforms state elm =
   FOLDL
     (\state_acc fm.
         let decision = decide_formula fm state state_acc elm
         in (\fm'. if fm = fm' then decision else (state_acc fm')))
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
 dfa_loop delta form elms state =
   (case elms
     of [] => state form
      | elm :: elms' => dfa_loop delta form elms' (delta state elm))
End

Definition to_dfa_def :
 to_dfa form =
   let (transition_start, transition) = mk_transitions form;
   in \elms. case elms
              of [] => dfa_loop transition form [] (transition_start other_elm)
               | elm :: elms' => dfa_loop transition form elms' (transition_start elm)
End

val _ = export_theory();


(* ****interactive proof scrap work: *****
val TODO_def = Hol_defn "TODO" `


`
Defn.tgoal TODO_def
*)
