open HolKernel Parse boolLib bossLib lcsymtacs;
open combinTheory pairTheory listTheory rich_listTheory stringLib;


val _ = new_theory "ptltl";

Datatype:
 formula
   = Eid string
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
   | Not formula
End

Definition Trigger_def :
  Trigger A B <=> Not(Since (Not A) (Not B))
End

(*---------------------------------------------------------------------------*)
(* These have to be revisited in light of the R&H semantics below for Prev.  *)
(*---------------------------------------------------------------------------*)

Definition Yester_def :
 Yester P <=> Prev P
End

Definition Zyester_def :
 Zyester P <=> Prev P
End

Definition other_elm_def :
 other_elm : string list = []
End


(*---------------------------------------------------------------------------*)
(* Start and End clauses are expanded versions of the original. Need an      *)
(* extra congruence rule to extract the right termination conditions         *)
(*---------------------------------------------------------------------------*)
val _ = DefnBase.add_cong LEFT_AND_CONG;

Definition bigstep_def :
 bigstep form trace <=>
   let (elm,trace_prev) =
         (if NULL trace then (other_elm,[])
          else (HD trace, TL trace))
   in
    case form
     of Eid eid     => MEM eid elm
      | Prim b      => b
      | Not f       => ~bigstep f trace
      | Imp f1 f2   => (bigstep f1 trace ==> bigstep f2 trace)
      | Equiv f1 f2 => (bigstep f1 trace <=> bigstep f2 trace)
      | Or f1 f2    => (bigstep f1 trace \/ bigstep f2 trace)
      | Xor f1 f2   => (bigstep f1 trace <> bigstep f2 trace)
      | And f1 f2   => (bigstep f1 trace /\ bigstep f2 trace)
      | Since f1 f2 => (bigstep f2 trace \/
                        (~NULL trace_prev /\ bigstep f1 trace /\
                         bigstep (Since f1 f2) trace_prev))
      | Histor f    => (bigstep f trace /\
                        (NULL trace_prev \/
                         (~NULL trace_prev /\ bigstep (Histor f) trace_prev)))
      | Once f      => (bigstep f trace \/
                        (~NULL trace_prev /\ bigstep (Once f) trace_prev))

      | Prev f      => ((NULL trace_prev /\ bigstep f trace) \/ bigstep f trace_prev)
      | Start f     => bigstep f trace /\
                       ~((NULL trace_prev /\ bigstep f trace) \/ bigstep f trace_prev)
      | End f       => ((NULL trace_prev /\ bigstep f trace) \/ bigstep f trace_prev)
                        /\ ~bigstep f trace
Termination
WF_REL_TAC `inv_image ($< LEX $<) (\(x,y). (formula_size x, LENGTH y))`
 >> rw_tac list_ss [NULL_EQ,other_elm_def,combinTheory.K_DEF]
 >> TRY (Cases_on `trace` >> fs[])
 >> metis_tac[]
End


(* state machine *)

Definition empty_state_def :
 empty_state = []
End


Definition mk_childforms_def : 
  (mk_childforms (Eid eid) = []) /\
  (mk_childforms (Prim b) = []) /\
  (mk_childforms (Imp f1 f2) = [f1; f2]) /\
  (mk_childforms (Equiv f1 f2) = [f1; f2]) /\
  (mk_childforms (Or f1 f2) = [f1; f2]) /\
  (mk_childforms (Xor f1 f2) = [f1; f2]) /\
  (mk_childforms (And f1 f2) = [f1; f2]) /\
  (mk_childforms (Since f1 f2) = [f1; f2]) /\
  (mk_childforms (Histor f) = [f]) /\
  (mk_childforms (Once f) = [f]) /\
  (mk_childforms (Prev f) = [f]) /\
  (mk_childforms (Start f) = [f]) /\
  (mk_childforms (End f) = [f]) /\
  (mk_childforms (Not f) = [f])
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
  (decide_formula_start (Eid eid) st elm     <=> MEM eid elm) /\
  (decide_formula_start (Prim b) st elm      <=> b) /\
  (decide_formula_start (Not f) st elm       <=> ~MEM f st) /\
  (decide_formula_start (Imp f1 f2) st elm   <=> (~ MEM f1 st) \/ MEM f2 st) /\
  (decide_formula_start (Equiv f1 f2) st elm <=> (MEM f1 st = MEM f2 st)) /\
  (decide_formula_start (Or f1 f2) st elm    <=> (MEM f1 st \/ MEM f2 st)) /\
  (decide_formula_start (Xor f1 f2) st elm   <=> ~(MEM f1 st = MEM f2 st)) /\
  (decide_formula_start (And f1 f2) st elm   <=> (MEM f1 st /\ MEM f2 st)) /\
  (decide_formula_start (Since f1 f2) st elm <=> (MEM f1 st /\ MEM f2 st)) /\
  (decide_formula_start (Histor f) st elm    <=> MEM f st) /\
  (decide_formula_start (Once f) st elm      <=> MEM f st) /\
  (decide_formula_start (Prev f) st elm      <=> MEM f st) /\
  (decide_formula_start (Start f) st elm     <=> F) /\
  (decide_formula_start (End f) st elm       <=> F)
End

Definition decide_formula_def :
 decide_formula fm st st_acc elm =
  (case fm of
     Eid eid => MEM eid elm
   | Prim b => b
   | Not f  => ~MEM f st_acc
   | Imp f1 f2   => (~MEM f1 st_acc) \/ MEM f2 st_acc
   | Equiv f1 f2 => (MEM f1 st_acc = MEM f2 st_acc)
   | Or f1 f2    => (MEM f1 st_acc \/ MEM f2 st_acc)
   | Xor f1 f2   => ~(MEM f1 st_acc = MEM f2 st_acc)
   | And f1 f2   => (MEM f1 st_acc /\ MEM f2 st_acc)
   | Since f1 f2 => (MEM f2 st_acc \/ (MEM f1 st_acc /\ MEM (Since f1 f2) st))
   | Histor f    => (MEM f st_acc /\ MEM (Histor f) st)
   | Once f      => (MEM f st_acc \/ MEM (Once f) st)
   | Prev f      => MEM f st
   | Start f     => (MEM f st_acc /\ ~MEM f st)
   | End f       => (~MEM f st_acc /\ MEM f st)
 )
End


Definition transition_start_def :
 transition_start sforms elm =
   FOLDL
     (\ st_acc fm .
         let decision = decide_formula_start fm st_acc elm
         in (if decision then
           fm :: st_acc
         else
           st_acc
         )
     )
     empty_state
     sforms
End

Definition transition_def:
 transition sforms st elm =
   FOLDL
     (\ st_acc fm .
         let decision = decide_formula fm st st_acc elm
         in (if decision then
           fm :: st_acc
         else
           st_acc
         )
     )
     empty_state
     sforms
End

Definition smallstep_loop_def :
 smallstep_loop delta form trace st =
   (case trace 
     of [] => MEM form st
      | elm :: trace' => smallstep_loop delta form trace' (delta st elm))
End


Definition smallstep_def :
 smallstep form =
   let
      subforms = REVERSE (nub (mk_subforms form));
      delta_start = transition_start subforms;
      delta = transition subforms;
   in \ elms. case elms
              of [] => MEM form (delta_start other_elm)
               | elm :: elms' => smallstep_loop delta form elms' (delta_start elm)
End

Definition  mk_power_list_def :
 mk_power_list [] = [[]] /\
 mk_power_list (x :: xs') =
   let
     rm = mk_power_list xs';
   in
     MAP (\l. x :: l) rm ++ rm

End

Definition extract_ids_def :
  extract_ids form = nub (case form of
    Eid eid => [eid] |
    Prim b => [] |
    Imp f1 f2 => extract_ids f1 ++ extract_ids f2 |
    Equiv  f1 f2 => extract_ids f1 ++ extract_ids f2 |
    Or f1 f2 => extract_ids f1 ++ extract_ids f2 |
    Xor f1 f2 => extract_ids f1 ++ extract_ids f2 |
    And f1 f2 => extract_ids f1 ++ extract_ids f2 |
    Since  f1 f2 => extract_ids f1 ++ extract_ids f2 |
    Histor f => extract_ids f |
    Once f => extract_ids f |
    Prev f => extract_ids f |
    Start f => extract_ids f |
    End f => extract_ids f |
    Not f => extract_ids f
  )
End


Definition find_reachable_edges_def :
  find_reachable_edges max_state_num elms delta states expl_states edges =
  if (max_state_num <= LENGTH expl_states) then
    (expl_states, edges)
  else (case states of
    [] => (expl_states, edges) |
    st :: tl_states => (let
      new_edges = (MAP (\ elm . (st, elm, delta st elm)) elms);
      edges' = new_edges ++ edges;

      expl_states' = st :: expl_states;

      new_states = (FILTER (\ st' .
        ~ (MEM st' expl_states') /\
        ~ (MEM st' tl_states)
      ) (MAP (\ (st, elm, st') . st') new_edges));

      states' = new_states ++ tl_states;

    in
      (find_reachable_edges
        max_state_num elms delta
        states'
        expl_states'
        edges'
      )
    )
  )
Termination
WF_REL_TAC `measure (
  \ (max_state_num, elms, delta, states, expl_states, edges). max_state_num - LENGTH expl_states)`
>> rw []
End

Definition mk_relational_data_def :
  mk_relational_data form has_par_evts = (let

    ids = extract_ids form;
    par_elms = (mk_power_list ids);
    elms = (if has_par_evts then
      par_elms
    else
      FILTER (\ elm . LENGTH elm = 1) par_elms
    );

    subforms = REVERSE (nub (mk_subforms form));
    delta_start = transition_start subforms;
    delta = transition subforms;
    total_states = mk_power_list subforms;
    max_state_num = LENGTH total_states;
    start_edges = MAP (\ elm . (elm, delta_start elm)) elms;
    start_states = nub (MAP (\ ( _, st') . st') start_edges);
    (expl_states, edges) = find_reachable_edges max_state_num elms delta start_states [] [];
    accept_states = (FILTER (\ st . MEM form st) expl_states);
  in
    (expl_states, elms, accept_states, start_edges, edges)
  )
End

Definition mk_table_data_def :
  mk_table_data (expl_states, elms, accept_states, start_edges, edges) = (let
    reject_idx = LENGTH expl_states;
    start_idx = reject_idx + 1;
    finals = (MAP (\ st . MEM st accept_states) expl_states) ++ [F; F];

    elm_contains = (\ elm1 elm2 .
      (* elm1 contains elm2 *)
      (EVERY (\ id . MEM id elm1) elm2)
    );

    empty_index = LENGTH elms - 1;
    elm_to_index = (\ elm . case (INDEX_FIND 0 (elm_contains elm) elms) of
      SOME (i, _ ) => i |
      NONE => empty_index
    );

    state_to_index = (\ st . case (INDEX_OF st expl_states) of
      SOME i => i |
      NONE => reject_idx
    );

    mk_row = (\ st .
      MAP (\ elm . case (FIND (\ (st_x, elm_x, st') . st_x = st /\ elm_x = elm) edges) of
        SOME (_, _, st') => state_to_index st' |
        NONE => reject_idx
      ) elms
    );

    rows = MAP mk_row expl_states;

    reject_row = MAP (\ _ . reject_idx) elms;

    start_row = (MAP (\ elm . case (FIND (\ (elm_x, _) . elm_x = elm) start_edges) of
      SOME (_, st') => state_to_index st' |
      NONE => reject_idx
    ) elms);

    table = rows ++ [reject_row; start_row];

  in
    (state_to_index, elm_to_index, finals, table, start_idx)
  )

End


(* This should stay at the SML level
Definition to_dotgraph_def :
  to_dotgraph (expl_states, elms, accept_states, start_edges, edges) = (let

    error_state_str = "error";
    start_state_str = "start";

    concat_with = (\ join_str str_list . case str_list of
      [] => "" |
      x :: xs =>
        (FOLDL (\ str_acc str .
          str_acc ++ join_str ++ str
        ) x xs)
    );

    mk_label = (\ (st : formula list) . case (INDEX_OF st expl_states) of
      SOME i => toString i |
      NONE => error_state_str
    );

    accept_state_labels = (MAP mk_label accept_states);

    start_edge_labels = (MAP (\ (elm, st') .
      ("start", concat_with "." elm, mk_label st')
    ) start_edges);

    edge_labels = start_edge_labels ++ (MAP (\ (st, elm, st') .
      (
        mk_label st,
        (if (elm = []) then
          "_"
        else
          (concat_with "." elm)
        ),
        mk_label st'
      )
    ) edges);

    graph_str = (
      "digraph finite_state_machine {\n" ++
      "  rankdir = LR;\n" ++
      "  node [shape = circle]; \"" ++ start_state_str ++ "\";\n" ++
      (if (NULL accept_states) then "" else
      "  node [shape = doublecircle]; " ++
           (concat_with "; " accept_state_labels) ++ ";\n"
      ) ++
      "  node [shape = plaintext];\n" ++
      "  \"\" -> \"" ++ start_state_str ++ "\" [label = \"\"];\n" ++
      "  node [shape = circle];\n" ++
      (concat_with "" (MAP (\ (st, elm, st') .
        st ++ "->" ++ st' ++ "[label = \"" ++ elm ++ "\"];\n"
      ) edge_labels)) ++
      "}"
    );
  in
    graph_str
  )
End
*)

Definition table_transition_def:
  table_transition table state_idx elm_idx = EL elm_idx (EL state_idx table)
End


Definition dfa_loop_def :
  dfa_loop table state_idx idx_trace = (case idx_trace of [] => state_idx |
    (elm_idx :: idx_trace') => (
      dfa_loop table (table_transition table state_idx elm_idx) idx_trace'
    )
  )
End


Definition dfa_def :
 dfa form =
   (let
      relational_data = mk_relational_data form T;
      (state_to_index, elm_to_idx, finals, table, start_idx) = mk_table_data relational_data;
      is_accepted = (\ idx . EL idx finals);
   in
     (\ trace . (let
       idx_trace = MAP (\ elm . elm_to_idx elm) trace;
     in case idx_trace of
       [] => is_accepted (table_transition table start_idx (elm_to_idx other_elm)) |
       elm_idx :: idx_trace' =>
         is_accepted (dfa_loop table start_idx (elm_idx :: idx_trace'))
     ))
   )
End


Definition transition_start_right_def :
 transition_start_right sforms elm =
   FOLDR
     (\ fm st_acc .
         let decision = decide_formula_start fm st_acc elm
         in (if decision then
           fm :: st_acc
         else
           st_acc
         )
     )
     empty_state
     sforms
End


Definition transition_start_rec_def :
 (transition_start_rec [] elm = empty_state) /\
 (transition_start_rec (fm :: forms) elm =
   (if (decide_formula_start fm (transition_start_rec forms elm) elm) then
     fm :: (transition_start_rec forms elm)
   else
     (transition_start_rec forms elm)
   )
 )
End


Definition list_step_start_def :
  (list_step_start [] elm form = F) /\
  (list_step_start (f :: fs) elm form =
  (if (form <> f) then
    (list_step_start fs elm form)
  else
    (∀ eid . f = Eid eid ==> MEM eid elm) /\
    (∀ b . f = Prim b ==> b) /\

    (∀ form1 form2 . f = Imp form1 form2 ==>
      ~ list_step_start fs elm form1 \/ list_step_start fs elm form2 
    ) /\

    (∀ form1 form2 . f = Equiv form1 form2 ==>
      list_step_start fs elm form1 = list_step_start fs elm form2 
    ) /\

    (∀ form1 form2 . f = Or form1 form2 ==>
      list_step_start fs elm form1 \/ list_step_start fs elm form2 
    ) /\

    (∀ form1 form2 . f = Xor form1 form2 ==>
      list_step_start fs elm form1 <> list_step_start fs elm form2 
    ) /\

    (∀ form1 form2 . f = And form1 form2 ==>
      list_step_start fs elm form1 /\ list_step_start fs elm form2 
    ) /\

    (∀ form1 form2 . f = Since form1 form2 ==>
      list_step_start fs elm form1 /\ list_step_start fs elm form2 
    ) /\

    (∀ form' . f = Histor form' ==>
      list_step_start fs elm form' 
    ) /\

    (∀ form' . f = Once form' ==>
      list_step_start fs elm form' 
    ) /\

    (∀ form' . f = Prev form' ==>
      list_step_start fs elm form' 
    ) /\

    (∀ form' . f = Start form' ==> F) /\

    (∀ form' . f = End form' ==> F) /\

    (∀ form' . f = Not form' ==> ~ list_step_start fs elm form')

  ))

End

(*
    (EXISTS (\ f' . MEM f' (mk_childforms f)) fs) /\
*)

Definition list_wellformed_def :
  (list_wellformed [] <=> T) /\
  (list_wellformed (f::fs) <=>
    (EVERY (\ f' . MEM f' fs) (mk_childforms f)) /\
    (EVERY (\ f' . ~MEM f (mk_childforms f')) fs) /\
    (~ MEM f fs) /\
    (list_wellformed fs)
  )
End



val transition_start_REVERSE_right_equiv_thm = Q.store_thm (
  "transition_start_REVERSE_right_equiv_thm",
  (`∀ sforms elm . 
    transition_start (REVERSE sforms) elm = transition_start_right sforms elm
  `),
  rw [transition_start_def, transition_start_right_def, FOLDL_REVERSE]
)


val transition_start_rec_thm = Q.store_thm (
  "transition_start_rec_thm",
  `∀ sforms elm . transition_start_rec sforms elm = transition_start_right sforms elm`,
  Induct_on `sforms` >> fs [transition_start_rec_def, transition_start_right_def]
)

val transition_start_REVERSE_rec_equiv_thm = Q.store_thm (
  "transition_start_REVERSE_rec_equiv_thm",
  (`∀ sforms elm . 
    transition_start (REVERSE sforms) elm = transition_start_rec sforms elm
  `),
  metis_tac [transition_start_REVERSE_right_equiv_thm, transition_start_rec_thm]
)


val MEM_subforms_refl_thm = Q.store_thm (
  "MEM_subforms_refl_thm",
  `∀ f . MEM f (mk_subforms f)`,
  (GEN_TAC >> ONCE_REWRITE_TAC [mk_subforms_def] >> CASE_TAC >> fs [])
)


val MEM_subforms_onestep_thm = Q.store_thm (
  "MEM_subforms_onestep_thm",
  (`∀ x y .
    MEM x (mk_childforms y)
    ==> 
    MEM x (mk_subforms y)
  `),
  Cases_on `y` >>
  rw [mk_childforms_def, Once mk_subforms_def] >>
  rw [MEM_subforms_refl_thm]
)


val MEM_subforms_multistep_thm = Q.store_thm (
  "MEM_subforms_multistep_thm",
  (`∀ x y z .
    MEM x (mk_childforms y) /\ MEM y (mk_subforms z) ==> 
    MEM x (mk_subforms z)
  `),
  Cases_on `y` >> rw [mk_childforms_def] >> ( 
     Induct_on `z` >> (
       TRY (ONCE_REWRITE_TAC [mk_subforms_def] >> CASE_TAC >> rw [] >> rw []) >>
       TRY (metis_tac [MEM_subforms_refl_thm]) >>
       rw [mk_subforms_def]
     )
  )
)


val MEM_subforms_elim_thm = Q.store_thm (
  "MEM_subforms_elim_thm",
  (`∀ x z .
    MEM x (mk_subforms z) ==> 
    (
      (x = z) \/
      (MEM x (mk_childforms z)) \/ 
      (∃y. MEM x (mk_childforms y) /\ MEM y (mk_subforms z))
    )
  `),
  rw [] >>
  Induct_on `z` >| [
    fs [Once mk_subforms_def, mk_childforms_def],
    fs [Once mk_subforms_def, mk_childforms_def]
  ] @ (List.tabulate (12, fn _ =>

    DISCH_TAC >>
    POP_ASSUM (fn thm =>
      MP_TAC (REWRITE_RULE [Once mk_subforms_def] thm)
    ) >> fs [] >> DISCH_TAC >>


    REWRITE_TAC [Once mk_childforms_def] >>
    REWRITE_TAC [Once mk_subforms_def] >>
    rw [] >> fs [] >>
    metis_tac [MEM_subforms_refl_thm]
  ))
)


val MEM_subforms_thm = Q.store_thm (
  "MEM_subforms_thm",
  (`∀ x z .
    MEM x (mk_subforms z) <=> (
      x = z \/
      (MEM x (mk_childforms z)) \/ 
      (∃ y . (MEM x (mk_childforms y) /\ MEM y (mk_subforms z)))
    )
  `),
  metis_tac [
    MEM_subforms_elim_thm,
    MEM_subforms_refl_thm,
    MEM_subforms_onestep_thm,
    MEM_subforms_multistep_thm
  ]
)


val MEM_childforms_anti_refl_thm = Q.store_thm (
  "MEM_childforms_anti_refl_thm",
  (` ∀ x y .
    MEM x (mk_childforms y) ==>
    ~ (x = y)
  `),
  (
  Cases_on `y` >> rw [mk_childforms_def] >>
  TRY (Q.SPEC_TAC (`f0`, `f0`) >> Induct_on `f` >> fs [] >> metis_tac []) >>
  TRY (Q.SPEC_TAC (`f`, `f`) >> Induct_on `f0` >> fs [] >> metis_tac [])
  )
)


val MEM_subforms_acyclic_thm = Q.store_thm (
  "MEM_subforms_acyclic_thm",
  (`∀ x y .
    (MEM x (mk_childforms y)) ==>
    ~ (MEM y (mk_subforms x))
  `),
  (let
  
    fun form_tac_pair_1 con a1 a2 =
    (
      DISCH_TAC >>
      ASSUME_TAC (Q.SPECL [`(^(con) ^(a1) ^(a2))`, `y`, `^(a1)`] MEM_subforms_multistep_thm) >>
      POP_ASSUM (fn imp_thm => POP_ASSUM (fn arg1_thm => POP_ASSUM (fn arg2_thm =>
        MP_TAC (MP imp_thm (CONJ arg2_thm arg1_thm)) 
      ))) >>
      POP_ASSUM (fn _ => POP_ASSUM (fn thm => 
        MP_TAC (Q.SPEC `(^(con) ^(a1) ^(a2))` thm) 
      )) >>
      rw [mk_childforms_def]
    )
    
    fun form_tac_pair_2 con a1 a2 =
    (
      DISCH_TAC >>
      ASSUME_TAC (Q.SPECL [`(^(con) ^(a1) ^(a2))`, `y`, `^(a2)`] MEM_subforms_multistep_thm) >>
      POP_ASSUM (fn imp_thm => POP_ASSUM (fn arg1_thm => POP_ASSUM (fn arg2_thm =>
        MP_TAC (MP imp_thm (CONJ arg2_thm arg1_thm)) 
      ))) >>
      POP_ASSUM (fn thm => POP_ASSUM (fn _ => 
        MP_TAC (Q.SPEC `(^(con) ^(a1) ^(a2))` thm) 
      )) >>
      rw [mk_childforms_def]
    )
    
    fun form_tac con a =
    (
      DISCH_TAC >>
      ASSUME_TAC (Q.SPECL [`(^(con) ^(a))`, `y`, `^(a)`] MEM_subforms_multistep_thm) >>
      POP_ASSUM (fn imp_thm => POP_ASSUM (fn arg1_thm => POP_ASSUM (fn arg2_thm =>
        MP_TAC (MP imp_thm (CONJ arg2_thm arg1_thm)) 
      ))) >>
      POP_ASSUM (fn thm => 
        MP_TAC (Q.SPEC `(^(con) ^(a))` thm) 
      ) >>
      rw [mk_childforms_def]
    )
  
  in
    Induct_on `x` >|
    (
       [fs [mk_subforms_def, mk_childforms_def], fs [mk_subforms_def, mk_childforms_def]] @

       (List.map (fn con =>
         ONCE_REWRITE_TAC [mk_subforms_def] >> CASE_TAC >> rw [] >|
         [
           fs [MEM_childforms_anti_refl_thm],
           (form_tac_pair_1 con ``f : formula`` ``f0 : formula``),
           (form_tac_pair_2 con ``f : formula`` ``f0 : formula``)
         ]
       ) [``Imp``, ``Equiv``, ``Or``, ``Xor``, ``And``, ``Since``]) @

       (List.map (fn con =>
         ONCE_REWRITE_TAC [mk_subforms_def] >> CASE_TAC >> rw [] >|
         [
           fs [MEM_childforms_anti_refl_thm],
           (form_tac con ``f : formula``)
         ]
       ) [``Histor``,``Once``, ``Prev``, ``Start``, ``End``, ``Not``])
    )

  end)
)


val subforms_self_first_thm = Q.store_thm (
  "subforms_self_first_thm",
  `∀ f . ∃ fs . mk_subforms f = f :: fs`,
  Cases_on `f` >> rw [Once (mk_subforms_def)]
)

val MEM_subforms_self_thm = Q.store_thm (
  "MEM_subforms_self_thm",
  `∀ f . MEM f (mk_subforms f)`,
  Cases_on `f` >> rw [Once (mk_subforms_def)]
)

val nub_subforms_self_first_thm = Q.store_thm (
  "nub_subforms_self_first_thm",
  `∀ f . ∃ fs . nub (mk_subforms f) = f :: fs`,
  Cases_on `f` >> rw [
    Once (mk_subforms_def), nub_def,
    MEM_subforms_acyclic_thm, mk_childforms_def
  ]
)

val nub_subforms_MEM_thm = Q.store_thm (
  "nub_subforms_MEM_thm",
  `∀ f . ∃ fs . nub (mk_subforms f) = fs /\ MEM f fs`,
  Cases_on `f` >> rw [
    Once (mk_subforms_def), nub_def,
    MEM_subforms_acyclic_thm, mk_childforms_def
  ]
)


val MEM_nub_thm = Q.store_thm (
  "MEM_nub_thm",
  (`∀ x xs . MEM x (nub xs) <=> MEM x xs `),
  Induct_on `xs` >> rw [nub_def]
)

val FILTER_nub_thm = Q.store_thm (
  "FILTER_nub_thm",
  `∀ l P . FILTER P (nub l) = nub (FILTER P l)`,
  Induct_on `l` >> rw [nub_def, FILTER, MEM_FILTER]
)


val MEM_transition_start_rec_constrained_thm = Q.store_thm (
  "MEM_transition_start_rec_constrained_thm",
  `∀ f fs elm .
    ~MEM f fs ==>
    ~ MEM f (transition_start_rec fs elm)
  `,
  rw [] >>
  Induct_on `fs` >> rw [transition_start_rec_def, empty_state_def] 
)


val MEM_transition_start_rec_APPEND_thm = Q.store_thm (
  "MEM_transition_start_rec_APPEND_thm",
  (`∀ f fs xs .
     MEM f (transition_start_rec fs other_elm) ==>
     MEM f (transition_start_rec (xs ++ fs) other_elm)
  `),
  Induct_on `xs` >> rw [transition_start_rec_def]
)





val MEM_transition_start_rec_imp_Q_thm = Q.store_thm (
  "MEM_transition_start_rec_imp_Q_thm",
  (`∀ form fs form' fs' .
    MEM form' (transition_start_rec fs' other_elm) ==>
    list_wellformed fs ==>
    list_wellformed fs' ==>
    (MEM (Imp form form') (transition_start_rec
      (Imp form form':: (FILTER (λx. ~MEM x (fs')) fs ++ fs'))
      other_elm
    ))
  `),
  GEN_TAC >> GEN_TAC >> GEN_TAC >> GEN_TAC >>
  DISCH_TAC >> DISCH_TAC >> DISCH_TAC >>
  REWRITE_TAC [Once transition_start_rec_def] >>
  (`∀ st_acc . decide_formula_start (Imp form form') st_acc other_elm <=>
    (~ MEM form st_acc \/ MEM form' st_acc)
  `) by (rw [decide_formula_start_def]) >>
  POP_ASSUM (fn rw_thm => REWRITE_TAC [rw_thm]) >>
  fs [MEM_transition_start_rec_APPEND_thm]
)






val MEM_transition_start_rec_drop_thm = Q.store_thm (
  "MEM_transition_start_rec_drop_thm",
  (`∀ f fs xs .
     list_wellformed (xs ++ (f :: fs)) ==>
     MEM f (transition_start_rec (xs ++ (f :: fs)) other_elm) ==>
     MEM f (transition_start_rec (f :: fs) other_elm)
  `),
  rw [] >>
  Induct_on `xs` >| [
    rw [] 
    ,

    GEN_TAC >>
    fs [Once CONS_APPEND] >>
    DISCH_TAC >>
    POP_ASSUM (fn thm =>
      ASSUME_TAC (REWRITE_RULE [list_wellformed_def] thm)
    ) >>

    DISCH_TAC >>
    POP_ASSUM (fn thm =>
      ASSUME_TAC (REWRITE_RULE [transition_start_rec_def] thm)
    ) >>

    Cases_on `decide_formula_start h (transition_start_rec (xs ++ f::fs) other_elm) other_elm` >>
    (fs [EVERY_MEM, EXISTS_MEM] >> fs [])

  ] 
)


val list_wellformed_anti_super_thm = Q.store_thm (
  "list_wellformed_anti_super_thm",
  (`∀ x xs f .
    list_wellformed (x :: xs) ==>
    MEM x (mk_childforms f) ==>
    ~ MEM f (x :: xs)
  `),
  GEN_TAC >> GEN_TAC >> GEN_TAC >>
  DISCH_TAC >> DISCH_TAC >>
  (rw [] >- rw [MEM_childforms_anti_refl_thm]) >>
  fs [list_wellformed_def, EVERY_MEM] >>
  (Cases_on `xs` >- fs []) >>
  fs [] >> (
    qpat_x_assum `∀f'. f' = h ∨ MEM f' t ⇒ ¬MEM x (mk_childforms f')` (fn thm =>
      ASSUME_TAC (Q.SPEC `f` thm)
    ) >>
    metis_tac []
  )
)

val list_step_start_Eid_elim_thm = Q.store_thm (
  "list_step_start_Eid_elim_thm",
  (`∀ s forms .
    ~ list_step_start forms other_elm (Eid s)
  `),
  rw [] >>
  Induct_on `forms`
  >| [
    fs [list_step_start_def, other_elm_def, empty_state_def]
    ,

    GEN_TAC >>
    fs [list_step_start_def, other_elm_def, empty_state_def] >>
    rw [] >>
    (Cases_on `h = Eid s` >> fs [])
  ]
)

val list_step_start_Prim_false_elim_thm = Q.store_thm (
  "list_step_start_Prim_false_elim_thm",
  (`∀ forms .
    ~ list_step_start forms other_elm (Prim F)
  `),
  rw [] >>
  Induct_on `forms`
  >| [
    fs [list_step_start_def, other_elm_def, empty_state_def]
    ,

    GEN_TAC >>
    fs [list_step_start_def, other_elm_def, empty_state_def] >>
    rw [] >>
    (Cases_on `h = Prim F` >> fs [])
  ]
)

val list_step_start_constrained_thm = Q.store_thm (
  "list_step_start_constrained_thm",
  `∀ forms elm form .
    list_step_start forms elm form ==> 
    MEM form forms
  `,
  rw [] >>
  Induct_on `forms` >> rw [list_step_start_def, empty_state_def] 
)


val list_step_start_Imp_elim_thm = Q.store_thm (
  "list_step_start_Imp_elim_thm",
  (`∀ forms f1 f2 .
    list_wellformed forms ==>
    list_step_start forms other_elm (Imp f1 f2) ==>
    list_step_start forms other_elm f1 ==>
    list_step_start forms other_elm f2 
  `),
  rw [] >>
  Induct_on `forms`
  >| [
    rw [list_step_start_def]
    ,

    GEN_TAC >>
    Cases_on `h = Imp f1 f2`
    >| [
      `h <> f1` by (fs [MEM_childforms_anti_refl_thm, mk_childforms_def]) >>
      `h <> f2` by (fs [MEM_childforms_anti_refl_thm, mk_childforms_def]) >>
      rw [list_step_start_def] >>
      fs []
      ,

      DISCH_TAC >> POP_ASSUM (fn thm =>
        ASSUME_TAC (REWRITE_RULE [list_wellformed_def] thm)
      ) >>
      fs [] >>

      rw [Once list_step_start_def] >>
      fs [] >>

      `MEM (Imp f1 f2) forms` by (metis_tac [list_step_start_constrained_thm]) >>
      fs [EVERY_MEM] >>

      qpat_assum `MEM (Imp f1 f2) forms` (fn arg_thm =>
      qpat_assum `∀f'. MEM f' forms ==> ~MEM h (mk_childforms f')` (fn thm =>
        ASSUME_TAC (MP (Q.SPEC `Imp f1 f2` thm) arg_thm)
      )) >>
      fs [mk_childforms_def] >>
      fs [list_step_start_def] >>
      rw [list_step_start_def] 
    ]

  ]
)

val list_step_start_Equiv_elim_thm = Q.store_thm (
  "list_step_start_Equiv_elim_thm",
  (`∀ forms f1 f2 .
    list_wellformed forms ==>
    list_step_start forms other_elm (Equiv f1 f2) ==>
    list_step_start forms other_elm f1 = list_step_start forms other_elm f2 
  `),
  rw [] >>
  Induct_on `forms`
  >| [
    rw [list_step_start_def]
    ,

    GEN_TAC >>
    Cases_on `h = Equiv f1 f2`
    >| [
      `h <> f1` by (fs [MEM_childforms_anti_refl_thm, mk_childforms_def]) >>
      `h <> f2` by (fs [MEM_childforms_anti_refl_thm, mk_childforms_def]) >>
      rw [list_step_start_def] >>
      fs []
      ,

      DISCH_TAC >> POP_ASSUM (fn thm =>
        ASSUME_TAC (REWRITE_RULE [list_wellformed_def] thm)
      ) >>
      fs [] >>

      rw [Once list_step_start_def] >>
      fs [] >>

      `MEM (Equiv f1 f2) forms` by (metis_tac [list_step_start_constrained_thm]) >>
      fs [EVERY_MEM] >>

      qpat_assum `MEM (Equiv f1 f2) forms` (fn arg_thm =>
      qpat_assum `∀f'. MEM f' forms ==> ~MEM h (mk_childforms f')` (fn thm =>
        ASSUME_TAC (MP (Q.SPEC `Equiv f1 f2` thm) arg_thm)
      )) >>
      fs [mk_childforms_def] >>
      fs [list_step_start_def] >>
      rw [list_step_start_def] 
    ]

  ]
)

val list_step_start_Or_elim_thm = Q.store_thm (
  "list_step_start_Or_elim_thm",
  (`∀ forms f1 f2 .
    list_wellformed forms ==>
    list_step_start forms other_elm (Or f1 f2) ==>
    list_step_start forms other_elm f1 \/ list_step_start forms other_elm f2 
  `),
  rw [] >>
  Induct_on `forms`
  >| [
    rw [list_step_start_def]
    ,

    GEN_TAC >>
    Cases_on `h = Or f1 f2`
    >| [
      `h <> f1` by (fs [MEM_childforms_anti_refl_thm, mk_childforms_def]) >>
      `h <> f2` by (fs [MEM_childforms_anti_refl_thm, mk_childforms_def]) >>
      rw [list_step_start_def] >>
      fs []
      ,

      DISCH_TAC >> POP_ASSUM (fn thm =>
        ASSUME_TAC (REWRITE_RULE [list_wellformed_def] thm)
      ) >>
      fs [] >>

      rw [Once list_step_start_def] >>
      fs [] >>

      `MEM (Or f1 f2) forms` by (metis_tac [list_step_start_constrained_thm]) >>
      fs [EVERY_MEM] >>

      qpat_assum `MEM (Or f1 f2) forms` (fn arg_thm =>
      qpat_assum `∀f'. MEM f' forms ==> ~MEM h (mk_childforms f')` (fn thm =>
        ASSUME_TAC (MP (Q.SPEC `Or f1 f2` thm) arg_thm)
      )) >>
      fs [mk_childforms_def] >>
      fs [list_step_start_def] >>
      rw [list_step_start_def] 
    ]

  ]
)

val list_step_start_Xor_elim_thm = Q.store_thm (
  "list_step_start_Xor_elim_thm",
  (`∀ forms f1 f2 .
    list_wellformed forms ==>
    list_step_start forms other_elm (Xor f1 f2) ==>
    list_step_start forms other_elm f1 <> list_step_start forms other_elm f2 
  `),
  rw [] >>
  Induct_on `forms`
  >| [
    rw [list_step_start_def]
    ,

    GEN_TAC >>
    Cases_on `h = Xor f1 f2`
    >| [
      `h <> f1` by (fs [MEM_childforms_anti_refl_thm, mk_childforms_def]) >>
      `h <> f2` by (fs [MEM_childforms_anti_refl_thm, mk_childforms_def]) >>
      rw [list_step_start_def] >>
      fs []
      ,

      DISCH_TAC >> POP_ASSUM (fn thm =>
        ASSUME_TAC (REWRITE_RULE [list_wellformed_def] thm)
      ) >>
      fs [] >>

      rw [Once list_step_start_def] >>
      fs [] >>

      `MEM (Xor f1 f2) forms` by (metis_tac [list_step_start_constrained_thm]) >>
      fs [EVERY_MEM] >>

      qpat_assum `MEM (Xor f1 f2) forms` (fn arg_thm =>
      qpat_assum `∀f'. MEM f' forms ==> ~MEM h (mk_childforms f')` (fn thm =>
        ASSUME_TAC (MP (Q.SPEC `Xor f1 f2` thm) arg_thm)
      )) >>
      fs [mk_childforms_def] >>
      fs [list_step_start_def] >>
      rw [list_step_start_def] 
    ]

  ]
)

val list_step_start_And_elim_thm = Q.store_thm (
  "list_step_start_And_elim_thm",
  (`∀ forms f1 f2 .
    list_wellformed forms ==>
    list_step_start forms other_elm (And f1 f2) ==>
    list_step_start forms other_elm f1 /\ list_step_start forms other_elm f2 
  `),
  GEN_TAC >> GEN_TAC >> GEN_TAC >>
  Induct_on `forms`
  >| [
    rw [list_step_start_def]
    ,

    GEN_TAC >>
    Cases_on `h = And f1 f2`
    >| [
      `h <> f1` by (fs [MEM_childforms_anti_refl_thm, mk_childforms_def]) >>
      `h <> f2` by (fs [MEM_childforms_anti_refl_thm, mk_childforms_def]) >>
      rw [list_step_start_def] >>
      fs []
      ,

      DISCH_TAC >> POP_ASSUM (fn thm =>
        ASSUME_TAC (REWRITE_RULE [list_wellformed_def] thm)
      ) >>
      fs [] >>

      rw [Once list_step_start_def] >>
      fs [] >>

      `MEM (And f1 f2) forms` by (metis_tac [list_step_start_constrained_thm]) >>
      fs [EVERY_MEM] >>

      qpat_assum `MEM (And f1 f2) forms` (fn arg_thm =>
      qpat_assum `∀f'. MEM f' forms ==> ~MEM h (mk_childforms f')` (fn thm =>
        ASSUME_TAC (MP (Q.SPEC `And f1 f2` thm) arg_thm)
      )) >>
      fs [mk_childforms_def] >>
      fs [list_step_start_def] >>
      rw [list_step_start_def] 
    ]

  ]
)

val list_step_start_Since_elim_thm = Q.store_thm (
  "list_step_start_Since_elim_thm",
  (`∀ forms f1 f2 .
    list_wellformed forms ==>
    list_step_start forms other_elm (Since f1 f2) ==>
    list_step_start forms other_elm f1 /\ list_step_start forms other_elm f2 
  `),
  GEN_TAC >> GEN_TAC >> GEN_TAC >>
  Induct_on `forms`
  >| [
    rw [list_step_start_def]
    ,

    GEN_TAC >>
    Cases_on `h = Since f1 f2`
    >| [
      `h <> f1` by (fs [MEM_childforms_anti_refl_thm, mk_childforms_def]) >>
      `h <> f2` by (fs [MEM_childforms_anti_refl_thm, mk_childforms_def]) >>
      rw [list_step_start_def] >>
      fs []
      ,

      DISCH_TAC >> POP_ASSUM (fn thm =>
        ASSUME_TAC (REWRITE_RULE [list_wellformed_def] thm)
      ) >>
      fs [] >>

      rw [Once list_step_start_def] >>
      fs [] >>

      `MEM (Since f1 f2) forms` by (metis_tac [list_step_start_constrained_thm]) >>
      fs [EVERY_MEM] >>

      qpat_assum `MEM (Since f1 f2) forms` (fn arg_thm =>
      qpat_assum `∀f'. MEM f' forms ==> ~MEM h (mk_childforms f')` (fn thm =>
        ASSUME_TAC (MP (Q.SPEC `Since f1 f2` thm) arg_thm)
      )) >>
      fs [mk_childforms_def] >>
      fs [list_step_start_def] >>
      rw [list_step_start_def] 
    ]

  ]
)


val list_step_start_Histor_elim_thm = Q.store_thm (
  "list_step_start_Histor_elim_thm",
  (`∀ forms f .
    list_wellformed forms ==>
    list_step_start forms other_elm (Histor f) ==>
    list_step_start forms other_elm f 
  `),
  rw [] >>
  Induct_on `forms`
  >| [
    rw [list_step_start_def]
    ,

    GEN_TAC >>
    Cases_on `h = Histor f`
    >| [
      `h <> f` by (fs [MEM_childforms_anti_refl_thm, mk_childforms_def]) >>
      rw [list_step_start_def] >>
      fs []
      ,

      DISCH_TAC >> POP_ASSUM (fn thm =>
        ASSUME_TAC (REWRITE_RULE [list_wellformed_def] thm)
      ) >>
      fs [] >>

      rw [Once list_step_start_def] >>
      fs [] >>

      `MEM (Histor f) forms` by (metis_tac [list_step_start_constrained_thm]) >>
      fs [EVERY_MEM] >>

      qpat_assum `MEM (Histor f) forms` (fn arg_thm =>
      qpat_assum `∀f'. MEM f' forms ==> ~MEM h (mk_childforms f')` (fn thm =>
        ASSUME_TAC (MP (Q.SPEC `Histor f` thm) arg_thm)
      )) >>
      fs [mk_childforms_def] >>
      fs [list_step_start_def] >>
      rw [list_step_start_def] 
    ]

  ]
)

val list_step_start_Once_elim_thm = Q.store_thm (
  "list_step_start_Once_elim_thm",
  (`∀ forms f .
    list_wellformed forms ==>
    list_step_start forms other_elm (Once f) ==>
    list_step_start forms other_elm f 
  `),
  rw [] >>
  Induct_on `forms`
  >| [
    rw [list_step_start_def]
    ,

    GEN_TAC >>
    Cases_on `h = Once f`
    >| [
      `h <> f` by (fs [MEM_childforms_anti_refl_thm, mk_childforms_def]) >>
      rw [list_step_start_def] >>
      fs []
      ,

      DISCH_TAC >> POP_ASSUM (fn thm =>
        ASSUME_TAC (REWRITE_RULE [list_wellformed_def] thm)
      ) >>
      fs [] >>

      rw [Once list_step_start_def] >>
      fs [] >>

      `MEM (Once f) forms` by (metis_tac [list_step_start_constrained_thm]) >>
      fs [EVERY_MEM] >>

      qpat_assum `MEM (Once f) forms` (fn arg_thm =>
      qpat_assum `∀f'. MEM f' forms ==> ~MEM h (mk_childforms f')` (fn thm =>
        ASSUME_TAC (MP (Q.SPEC `Once f` thm) arg_thm)
      )) >>
      fs [mk_childforms_def] >>
      fs [list_step_start_def] >>
      rw [list_step_start_def] 
    ]

  ]
)

val list_step_start_Prev_elim_thm = Q.store_thm (
  "list_step_start_Prev_elim_thm",
  (`∀ forms f .
    list_wellformed forms ==>
    list_step_start forms other_elm (Prev f) ==>
    list_step_start forms other_elm f 
  `),
  rw [] >>
  Induct_on `forms`
  >| [
    rw [list_step_start_def]
    ,

    GEN_TAC >>
    Cases_on `h = Prev f`
    >| [
      `h <> f` by (fs [MEM_childforms_anti_refl_thm, mk_childforms_def]) >>
      rw [list_step_start_def] >>
      fs []
      ,

      DISCH_TAC >> POP_ASSUM (fn thm =>
        ASSUME_TAC (REWRITE_RULE [list_wellformed_def] thm)
      ) >>
      fs [] >>

      rw [Once list_step_start_def] >>
      fs [] >>

      `MEM (Prev f) forms` by (metis_tac [list_step_start_constrained_thm]) >>
      fs [EVERY_MEM] >>

      qpat_assum `MEM (Prev f) forms` (fn arg_thm =>
      qpat_assum `∀f'. MEM f' forms ==> ~MEM h (mk_childforms f')` (fn thm =>
        ASSUME_TAC (MP (Q.SPEC `Prev f` thm) arg_thm)
      )) >>
      fs [mk_childforms_def] >>
      fs [list_step_start_def] >>
      rw [list_step_start_def] 
    ]

  ]
)

val list_step_start_Not_elim_thm = Q.store_thm (
  "list_step_start_Not_elim_thm",
  (`∀ forms f .
    list_wellformed forms ==>
    list_step_start forms other_elm (Not f) ==>
    ~list_step_start forms other_elm f 
  `),
  rw [] >>
  Induct_on `forms`
  >| [
    rw [list_step_start_def]
    ,

    GEN_TAC >>
    Cases_on `h = Not f`
    >| [
      `h <> f` by (fs [MEM_childforms_anti_refl_thm, mk_childforms_def]) >>
      rw [list_step_start_def] >>
      fs []
      ,

      DISCH_TAC >> POP_ASSUM (fn thm =>
        ASSUME_TAC (REWRITE_RULE [list_wellformed_def] thm)
      ) >>
      fs [] >>

      rw [Once list_step_start_def] >>
      fs [] >>

      `MEM (Not f) forms` by (metis_tac [list_step_start_constrained_thm]) >>
      fs [EVERY_MEM] >>

      qpat_assum `MEM (Not f) forms` (fn arg_thm =>
      qpat_assum `∀f'. MEM f' forms ==> ~MEM h (mk_childforms f')` (fn thm =>
        ASSUME_TAC (MP (Q.SPEC `Not f` thm) arg_thm)
      )) >>
      fs [mk_childforms_def] >>
      fs [list_step_start_def] >>
      rw [list_step_start_def] 
    ]

  ]
)


val list_step_start_Start_elim_thm = Q.store_thm (
  "list_step_start_Start_elim_thm",
  (`∀ forms f .
    ~ list_step_start forms other_elm (Start f)
  `),
  rw [] >>
  Induct_on `forms`
  >| [
    rw [list_step_start_def]
    ,

    GEN_TAC >>
    Cases_on `h = Start f`
    >| [
      `h <> f` by (fs [MEM_childforms_anti_refl_thm, mk_childforms_def]) >>
      rw [list_step_start_def] >>
      fs []
      ,

      DISCH_TAC >> POP_ASSUM (fn thm =>
        ASSUME_TAC (REWRITE_RULE [list_wellformed_def] thm)
      ) >>
      fs [] >>

      fs [Once list_step_start_def] >>
      metis_tac []
    ]
  ]
)

val list_step_start_End_elim_thm = Q.store_thm (
  "list_step_start_End_elim_thm",
  (`∀ forms f .
    ~ list_step_start forms other_elm (End f)
  `),
  rw [] >>
  Induct_on `forms`
  >| [
    rw [list_step_start_def]
    ,

    GEN_TAC >>
    Cases_on `h = End f`
    >| [
      `h <> f` by (fs [MEM_childforms_anti_refl_thm, mk_childforms_def]) >>
      rw [list_step_start_def] >>
      fs []
      ,

      DISCH_TAC >> POP_ASSUM (fn thm =>
        ASSUME_TAC (REWRITE_RULE [list_wellformed_def] thm)
      ) >>
      fs [] >>

      fs [Once list_step_start_def] >>
      metis_tac []
    ]
  ]
)



val list_step_start_MEM_transition_start_eq_thm = Q.store_thm (
  "list_step_start_MEM_transition_start_eq_thm",
  (`∀ form forms .
    list_wellformed forms ==>
    (
      list_step_start forms other_elm form <=>
      MEM form (transition_start_rec forms other_elm)
    )
  `),
  Induct_on `forms`
  >| [
    fs [list_step_start_def] >>
    fs [transition_start_rec_def] >>
    fs [empty_state_def]
    ,
    
    GEN_TAC >> GEN_TAC >>
    (Cases_on `form <> h` >- rw [list_wellformed_def, list_step_start_def, transition_start_rec_def]) >>
    fs [] >>
    rw [list_wellformed_def] >>
    fs [] >>
    qpat_x_assum `∀ form . list_step_start _ _ _ <=> MEM _ _` (fn rw_thm =>
       ASSUME_TAC (GSYM rw_thm)
    ) >>
    Cases_on `form`
    >| [
      rw [list_step_start_def, transition_start_rec_def, decide_formula_start_def] >>
      rw [list_step_start_Eid_elim_thm]
      ,

      rw [list_step_start_def, transition_start_rec_def, decide_formula_start_def] >>
      rw [list_step_start_Prim_false_elim_thm]
      ,

      rw [transition_start_rec_def, decide_formula_start_def, list_step_start_def] >>
      metis_tac [list_step_start_Imp_elim_thm]
      ,

      rw [transition_start_rec_def, decide_formula_start_def, list_step_start_def] >>
      metis_tac [list_step_start_Equiv_elim_thm]
      ,

      rw [transition_start_rec_def, decide_formula_start_def, list_step_start_def] >>
      metis_tac [list_step_start_Or_elim_thm]
      ,

      rw [transition_start_rec_def, decide_formula_start_def, list_step_start_def] >>
      metis_tac [list_step_start_Xor_elim_thm]
      ,

      rw [transition_start_rec_def, decide_formula_start_def, list_step_start_def] >>
      metis_tac [list_step_start_And_elim_thm]
      ,

      rw [transition_start_rec_def, decide_formula_start_def, list_step_start_def] >>
      metis_tac [list_step_start_Since_elim_thm]
      ,

      rw [transition_start_rec_def, decide_formula_start_def, list_step_start_def] >>
      metis_tac [list_step_start_Histor_elim_thm]
      ,

      rw [transition_start_rec_def, decide_formula_start_def, list_step_start_def] >>
      metis_tac [list_step_start_Once_elim_thm]
      ,

      rw [transition_start_rec_def, decide_formula_start_def, list_step_start_def] >>
      metis_tac [list_step_start_Prev_elim_thm]
      ,

      rw [transition_start_rec_def, decide_formula_start_def, list_step_start_def] >>
      metis_tac [list_step_start_Start_elim_thm]
      ,

      rw [transition_start_rec_def, decide_formula_start_def, list_step_start_def] >>
      metis_tac [list_step_start_End_elim_thm]
      ,

      rw [transition_start_rec_def, decide_formula_start_def, list_step_start_def] >>
      metis_tac [list_step_start_Not_elim_thm]
    ]
  ]
)


val list_step_start_APPEND_thm = Q.store_thm (
  "list_step_start_APPEND_thm",
  (`∀ fs form' fs' .
    list_wellformed fs ==>
    list_wellformed fs' ==>
    MEM form' fs' ==>
    (
      list_step_start (FILTER (\ x . ~ MEM x fs') fs ++ fs') other_elm form' <=>
      list_step_start fs' other_elm form'
    )
  `),
  GEN_TAC >> GEN_TAC >> GEN_TAC >>
  (Induct_on `fs` >- rw []) >>
  GEN_TAC >>

  rw [Once list_wellformed_def] >>
  (Cases_on `h = form'` >- fs []) >>
  rw [Once list_step_start_def]
)


val list_wellformed_childform_included_thm = Q.store_thm (
  "list_wellformed_childform_included_thm",
  (`∀ fs f f' .
    list_wellformed fs ==>
    MEM f fs ==>
    MEM f' (mk_childforms f) ==>
    MEM f' fs
  `),
  rw [] >>
  (Induct_on `fs` >- rw []) >>
  GEN_TAC >>
  rw [Once list_wellformed_def, EVERY_MEM] >> fs []
)



val list_wellformed_append_thm = Q.store_thm (
  "list_wellformed_append_thm",
  (`∀ fs fs' .
    list_wellformed fs ==>
    list_wellformed fs' ==>
    list_wellformed ((FILTER (\ x. ~MEM x fs') fs) ⧺ fs')
  `),
  rw [] >>
  (Induct_on `fs` >- rw []) >>
  GEN_TAC >>
  rw [Once list_wellformed_def] >>
  fs [EVERY_MEM] >>
  rw [Once list_wellformed_def, EVERY_MEM]
  >| [
    qpat_x_assum `∀ f' . MEM f' (mk_childforms h) ==> _` (fn thm =>
      ASSUME_TAC (Q.SPEC `f'` thm)
    ) >>

    qpat_assum `MEM f' (mk_childforms h)` (fn arg_thm =>
    qpat_assum `MEM f' (mk_childforms h) ==> _` (fn imp_thm =>
      ASSUME_TAC (MP imp_thm arg_thm)
    )) >>

    fs [MEM_FILTER]
    ,

    `MEM f' fs` by (fs [MEM_FILTER]) >>
    qpat_x_assum `∀ f' . MEM f' fs ==> _` (fn thm =>
      ASSUME_TAC (Q.SPEC `f'` thm)
    ) >>

    qpat_assum `MEM f' fs` (fn arg_thm =>
    qpat_assum `MEM f' fs ==> _` (fn imp_thm =>
      ASSUME_TAC (MP imp_thm arg_thm)
    )) >>

    fs []
    ,

    metis_tac [list_wellformed_childform_included_thm]
    ,

    fs [MEM_FILTER]
  ]
)

val list_wellformed_nub_subforms_thm = Q.store_thm (
  "list_wellformed_nub_subforms_thm",
  `∀ form . list_wellformed (nub (mk_subforms form))`,
  Induct_on `form`
  >| [
    rw [mk_subforms_def, nub_def, list_wellformed_def, mk_childforms_def]
    ,

    rw [mk_subforms_def, nub_def, list_wellformed_def, mk_childforms_def]
    ,

    `~ MEM (Imp form form') (mk_subforms form)` by (fs [MEM_subforms_acyclic_thm, mk_childforms_def]) >>
    `~ MEM (Imp form form') (mk_subforms form')` by (fs [MEM_subforms_acyclic_thm, mk_childforms_def]) >>
    rw [Once mk_subforms_def, nub_def] >>
    rw [Once list_wellformed_def]
    >| [
      rw [mk_childforms_def] >> rw [MEM_subforms_self_thm]
      ,
      rw [EVERY_MEM] >> ( 
        DISCH_TAC >>
        `~MEM f' (mk_subforms (Imp form form'))` by (metis_tac [MEM_subforms_acyclic_thm]) >>
        fs [Once mk_subforms_def]
      )
      ,

      rw [nub_append, GSYM FILTER_nub_thm] >>
      `(\ x. ~ MEM x (mk_subforms form')) = (\ x. ~ MEM x (nub (mk_subforms form')))` by (
        fs [Once (GSYM MEM_nub_thm)]
      ) >>
      POP_ASSUM (fn rw_thm => FULL_SIMP_TAC std_ss [Once rw_thm]) >>
      rw [list_wellformed_append_thm]
    
    ]
    ,

    `~ MEM (Equiv form form') (mk_subforms form)` by (fs [MEM_subforms_acyclic_thm, mk_childforms_def]) >>
    `~ MEM (Equiv form form') (mk_subforms form')` by (fs [MEM_subforms_acyclic_thm, mk_childforms_def]) >>
    rw [Once mk_subforms_def, nub_def] >>
    rw [Once list_wellformed_def]
    >| [
      rw [mk_childforms_def] >> rw [MEM_subforms_self_thm]
      ,
      rw [EVERY_MEM] >> ( 
        DISCH_TAC >>
        `~MEM f' (mk_subforms (Equiv form form'))` by (metis_tac [MEM_subforms_acyclic_thm]) >>
        fs [Once mk_subforms_def]
      )
      ,

      rw [nub_append, GSYM FILTER_nub_thm] >>
      `(\ x. ~ MEM x (mk_subforms form')) = (\ x. ~ MEM x (nub (mk_subforms form')))` by (
        fs [Once (GSYM MEM_nub_thm)]
      ) >>
      POP_ASSUM (fn rw_thm => FULL_SIMP_TAC std_ss [Once rw_thm]) >>
      rw [list_wellformed_append_thm]
    
    ]
    ,

    `~ MEM (Or form form') (mk_subforms form)` by (fs [MEM_subforms_acyclic_thm, mk_childforms_def]) >>
    `~ MEM (Or form form') (mk_subforms form')` by (fs [MEM_subforms_acyclic_thm, mk_childforms_def]) >>
    rw [Once mk_subforms_def, nub_def] >>
    rw [Once list_wellformed_def]
    >| [
      rw [mk_childforms_def] >> rw [MEM_subforms_self_thm]
      ,
      rw [EVERY_MEM] >> ( 
        DISCH_TAC >>
        `~MEM f' (mk_subforms (Or form form'))` by (metis_tac [MEM_subforms_acyclic_thm]) >>
        fs [Once mk_subforms_def]
      )
      ,

      rw [nub_append, GSYM FILTER_nub_thm] >>
      `(\ x. ~ MEM x (mk_subforms form')) = (\ x. ~ MEM x (nub (mk_subforms form')))` by (
        fs [Once (GSYM MEM_nub_thm)]
      ) >>
      POP_ASSUM (fn rw_thm => FULL_SIMP_TAC std_ss [Once rw_thm]) >>
      rw [list_wellformed_append_thm]
    ]
    ,

    `~ MEM (Xor form form') (mk_subforms form)` by (fs [MEM_subforms_acyclic_thm, mk_childforms_def]) >>
    `~ MEM (Xor form form') (mk_subforms form')` by (fs [MEM_subforms_acyclic_thm, mk_childforms_def]) >>
    rw [Once mk_subforms_def, nub_def] >>
    rw [Once list_wellformed_def]
    >| [
      rw [mk_childforms_def] >> rw [MEM_subforms_self_thm]
      ,
      rw [EVERY_MEM] >> ( 
        DISCH_TAC >>
        `~MEM f' (mk_subforms (Xor form form'))` by (metis_tac [MEM_subforms_acyclic_thm]) >>
        fs [Once mk_subforms_def]
      )
      ,

      rw [nub_append, GSYM FILTER_nub_thm] >>
      `(\ x. ~ MEM x (mk_subforms form')) = (\ x. ~ MEM x (nub (mk_subforms form')))` by (
        fs [Once (GSYM MEM_nub_thm)]
      ) >>
      POP_ASSUM (fn rw_thm => FULL_SIMP_TAC std_ss [Once rw_thm]) >>
      rw [list_wellformed_append_thm]
    ]
    ,
    
    `~ MEM (And form form') (mk_subforms form)` by (fs [MEM_subforms_acyclic_thm, mk_childforms_def]) >>
    `~ MEM (And form form') (mk_subforms form')` by (fs [MEM_subforms_acyclic_thm, mk_childforms_def]) >>
    rw [Once mk_subforms_def, nub_def] >>
    rw [Once list_wellformed_def]
    >| [
      rw [mk_childforms_def] >> rw [MEM_subforms_self_thm]
      ,
      rw [EVERY_MEM] >> ( 
        DISCH_TAC >>
        `~MEM f' (mk_subforms (And form form'))` by (metis_tac [MEM_subforms_acyclic_thm]) >>
        fs [Once mk_subforms_def]
      )
      ,

      rw [nub_append, GSYM FILTER_nub_thm] >>
      `(\ x. ~ MEM x (mk_subforms form')) = (\ x. ~ MEM x (nub (mk_subforms form')))` by (
        fs [Once (GSYM MEM_nub_thm)]
      ) >>
      POP_ASSUM (fn rw_thm => FULL_SIMP_TAC std_ss [Once rw_thm]) >>
      rw [list_wellformed_append_thm]
    ]
    ,

    `~ MEM (Since form form') (mk_subforms form)` by (fs [MEM_subforms_acyclic_thm, mk_childforms_def]) >>
    `~ MEM (Since form form') (mk_subforms form')` by (fs [MEM_subforms_acyclic_thm, mk_childforms_def]) >>
    rw [Once mk_subforms_def, nub_def] >>
    rw [Once list_wellformed_def]
    >| [
      rw [mk_childforms_def] >> rw [MEM_subforms_self_thm]
      ,
      rw [EVERY_MEM] >> ( 
        DISCH_TAC >>
        `~MEM f' (mk_subforms (Since form form'))` by (metis_tac [MEM_subforms_acyclic_thm]) >>
        fs [Once mk_subforms_def]
      )
      ,

      rw [nub_append, GSYM FILTER_nub_thm] >>
      `(\ x. ~ MEM x (mk_subforms form')) = (\ x. ~ MEM x (nub (mk_subforms form')))` by (
        fs [Once (GSYM MEM_nub_thm)]
      ) >>
      POP_ASSUM (fn rw_thm => FULL_SIMP_TAC std_ss [Once rw_thm]) >>
      rw [list_wellformed_append_thm]
    ]
    ,

    `~ MEM (Histor form) (mk_subforms form)` by (fs [MEM_subforms_acyclic_thm, mk_childforms_def]) >>
    rw [Once mk_subforms_def, nub_def] >>
    rw [Once list_wellformed_def]
    >| [
      rw [mk_childforms_def] >> rw [MEM_subforms_self_thm]
      ,
      rw [EVERY_MEM] >> ( 
        DISCH_TAC >>
        `~MEM f' (mk_subforms (Histor form))` by (metis_tac [MEM_subforms_acyclic_thm]) >>
        fs [Once mk_subforms_def]
      )
    ]
    ,

    `~ MEM (Once form) (mk_subforms form)` by (fs [MEM_subforms_acyclic_thm, mk_childforms_def]) >>
    rw [Once mk_subforms_def, nub_def] >>
    rw [Once list_wellformed_def]
    >| [
      rw [mk_childforms_def] >> rw [MEM_subforms_self_thm]
      ,
      rw [EVERY_MEM] >> ( 
        DISCH_TAC >>
        `~MEM f' (mk_subforms (Once form))` by (metis_tac [MEM_subforms_acyclic_thm]) >>
        fs [Once mk_subforms_def]
      )
    ]
    ,

    `~ MEM (Prev form) (mk_subforms form)` by (fs [MEM_subforms_acyclic_thm, mk_childforms_def]) >>
    rw [Once mk_subforms_def, nub_def] >>
    rw [Once list_wellformed_def]
    >| [
      rw [mk_childforms_def] >> rw [MEM_subforms_self_thm]
      ,
      rw [EVERY_MEM] >> ( 
        DISCH_TAC >>
        `~MEM f' (mk_subforms (Prev form))` by (metis_tac [MEM_subforms_acyclic_thm]) >>
        fs [Once mk_subforms_def]
      )
    ]
    ,

    `~ MEM (Start form) (mk_subforms form)` by (fs [MEM_subforms_acyclic_thm, mk_childforms_def]) >>
    rw [Once mk_subforms_def, nub_def] >>
    rw [Once list_wellformed_def]
    >| [
      rw [mk_childforms_def] >> rw [MEM_subforms_self_thm]
      ,
      rw [EVERY_MEM] >> ( 
        DISCH_TAC >>
        `~MEM f' (mk_subforms (Start form))` by (metis_tac [MEM_subforms_acyclic_thm]) >>
        fs [Once mk_subforms_def]
      )
    ]
    ,

    `~ MEM (End form) (mk_subforms form)` by (fs [MEM_subforms_acyclic_thm, mk_childforms_def]) >>
    rw [Once mk_subforms_def, nub_def] >>
    rw [Once list_wellformed_def]
    >| [
      rw [mk_childforms_def] >> rw [MEM_subforms_self_thm]
      ,
      rw [EVERY_MEM] >> ( 
        DISCH_TAC >>
        `~MEM f' (mk_subforms (End form))` by (metis_tac [MEM_subforms_acyclic_thm]) >>
        fs [Once mk_subforms_def]
      )
    ]
    ,

    `~ MEM (Not form) (mk_subforms form)` by (fs [MEM_subforms_acyclic_thm, mk_childforms_def]) >>
    rw [Once mk_subforms_def, nub_def] >>
    rw [Once list_wellformed_def]
    >| [
      rw [mk_childforms_def] >> rw [MEM_subforms_self_thm]
      ,
      rw [EVERY_MEM] >> ( 
        DISCH_TAC >>
        `~MEM f' (mk_subforms (Not form))` by (metis_tac [MEM_subforms_acyclic_thm]) >>
        fs [Once mk_subforms_def]
      )
    ]
  ]
)


(* SCRATCH: *)


val list_step_start_FILTER_APPEND_thm = Q.store_thm (
  "list_step_start_FILTER_APPEND_thm",
  (`∀ form fs fs' .
    list_wellformed fs ==>
    list_wellformed fs' ==>
    MEM form fs ==>
    (
      list_step_start (FILTER (\ x . ~ MEM x fs') fs ++ fs') other_elm form <=>
      list_step_start fs other_elm form
    )
  `),
  rw [] >>
  (* TODO *)
  cheat
)




val list_step_start_imp_gen_thm = Q.store_thm (
  "list_step_start_imp_gen_thm",
  (`∀ form fs form' fs' .
    list_wellformed fs ==>
    MEM form fs ==>
    list_wellformed fs' ==>
    MEM form' fs' ==>
    (
      (list_step_start
        (Imp form form' :: (FILTER (\x. ~MEM x fs') fs) ++ fs')
        other_elm
        (Imp form form')
      ) <=> (
        (list_step_start fs other_elm) form ==>
        (list_step_start fs' other_elm) form'
      )
    )
  `),

  GEN_TAC >> GEN_TAC >> GEN_TAC >> GEN_TAC >>
  rw [Once list_step_start_def] >>
  fs [] >>

  ASSUME_TAC list_step_start_APPEND_thm >> 
  ASSUME_TAC list_step_start_FILTER_APPEND_thm >> 
  fs [] >>
  metis_tac []
)

val list_step_start_imp_thm = Q.store_thm (
  "list_step_start_imp_thm",
  (`∀ form form' .
    (list_step_start (nub (mk_subforms (Imp form form'))) other_elm (Imp form form')) <=>
    (
      list_step_start (nub (mk_subforms form)) other_elm form ==>
      list_step_start (nub (mk_subforms form')) other_elm form'
    )
  `),
  GEN_TAC >> GEN_TAC >>
  rw [Once mk_subforms_def] >>
  FULL_SIMP_TAC std_ss [Once nub_def] >>

  `~MEM (Imp form form') (mk_subforms form)` by (fs [MEM_subforms_acyclic_thm, mk_childforms_def]) >>
  `~MEM (Imp form form') (mk_subforms form')` by (fs [MEM_subforms_acyclic_thm, mk_childforms_def]) >>
  fs [] >>
  fs [Once nub_append] >>
  fs [Once (GSYM FILTER_nub_thm)] >>

  `(\ x. ~ MEM x (mk_subforms form')) = (\ x. ~ MEM x (nub (mk_subforms form')))` by (
    fs [Once (GSYM MEM_nub_thm)]
  ) >>
  POP_ASSUM (fn rw_thm => FULL_SIMP_TAC std_ss [Once rw_thm]) >>


  `list_wellformed (nub (mk_subforms form))` by (fs [list_wellformed_nub_subforms_thm]) >>
  `list_wellformed (nub (mk_subforms form'))` by (fs [list_wellformed_nub_subforms_thm]) >>

  `∃ fs . nub (mk_subforms form) = fs /\ MEM form fs` by (fs [nub_subforms_MEM_thm]) >>
  `∃ fs' . nub (mk_subforms form') = fs' /\ MEM form' fs'` by (fs [nub_subforms_MEM_thm]) >>
  FULL_SIMP_TAC std_ss [] >>
  ASSUME_TAC (list_step_start_imp_gen_thm) >>
  fs []
)  


  `form = form' ==> nub (mk_subforms form) = nub (mk_subforms form')` by (fs []) >>

val bigstep_equiv_smallstep_empty_trace_thm = Q.store_thm (
 "bigstep_equiv_smallstep_empty_trace_thm",
 `∀ form . bigstep form [] <=> smallstep form []`,

  GEN_TAC >>
  fs [Once smallstep_def] >> fs [transition_start_REVERSE_rec_equiv_thm] >>
  fs [GSYM (MP 
   (Q.SPECL [`form`, `nub (mk_subforms form)`] list_step_start_MEM_transition_start_eq_thm)
   (Q.SPEC `form `list_wellformed_nub_subforms_thm)
  )] >>

  Induct_on `form`
  >| [
    rw [
      bigstep_def, other_elm_def, mk_subforms_def,
      nub_def, list_step_start_def,
      empty_state_def
    ]
    ,

    rw [
      bigstep_def, other_elm_def, mk_subforms_def,
      nub_def, list_step_start_def,
      empty_state_def
    ]
    ,

    rw [Once bigstep_def] >>
    metis_tac [list_step_start_imp_thm]
    ,

    (* TODO *)
    cheat
    ,

    (* TODO *)
    cheat
    ,

    (* TODO *)
    cheat
    ,

    (* TODO *)
    cheat
    ,

    (* TODO *)
    cheat
    ,

    (* TODO *)
    cheat
    ,

    (* TODO *)
    cheat
    ,

    (* TODO *)
    cheat
    ,

    (* TODO *)
    cheat
    ,

    (* TODO *)
    cheat
    ,

    (* TODO *)
    cheat
 ]
 
)


val bigstep_equiv_smallstep_thm = Q.store_thm (
 "bigstep_equiv_smallstep_thm",
 `∀ form trace . bigstep form trace <=> smallstep form trace`,
 Cases_on `trace` >| [
   (* TODO *)
 ]
)


val smallstep_equiv_dfa_thm = Q.store_thm (
 "smallstep_equiv_dfa_thm",
 `∀ form trace . smallstep form trace <=> dfa form trace`,
 (* TODO *)
)



val bigtep_equiv_dfa_thm = Q.store_thm (
 "bigtep_equiv_dfa_thm",
 `∀ form trace . bigstep form trace <=> dfa form trace`,
 (* TODO *)
)



val _ = export_theory();
