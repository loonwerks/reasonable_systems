open HolKernel Parse boolLib bossLib lcsymtacs;
open combinTheory pairTheory listTheory stringLib;

open preamble basis 
open ml_translatorLib;
open ml_progLib;
open fromSexpTheory astToSexprLib;


open ptltlTheory traceTheory

val _ = new_theory "scratch";

(*

val common_hol_defs =  [
  K_DEF,
  NULL_DEF,
  HD,
  TL_DEF,
  FST,
  SND,
  FOLDL,
  REVERSE_DEF,
  IN_DEF,
  LIST_TO_SET_DEF,
  nub_def,
  EVERY_DEF,
  o_DEF,
  INDEX_FIND_def,
  OPTION_MAP_DEF,
  INDEX_OF_def,
  FIND_def,
  EL,
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
  dfa_loop_def,
  mk_elm_def,
  mk_trace_def
]

  val _ = map (fn hol_def => translate hol_def) common_hol_defs

  val hol_form = ``(Histor
    (And
      (Imp
        (Eid "b")
        (Prev
          (Since
            (Not
              (Eid "b")
            )
            (Eid "a")
          )
        )
      )
      (Not
        (And
          (Eid "a")
          (Eid "b")
        )
      )
    )
  )`` ;


  val _ = translate extract_ids_def;
  val _ = translate mk_power_list_def;
  val _ = translate LENGTH;
  val _ = translate find_reachable_edges_def;
  val _ = translate mk_relational_data_def;
  val _ = translate mk_table_data_def;

  val relational_data_term = (``
    (mk_relational_data ^(hol_form))
  ``) |> EVAL |> concl |> rhs;

  val table_data_term = (``
    mk_table_data ^(relational_data_term)
  ``) |> EVAL |> concl |> rhs;

  val table_data_def = Define `table_data = ^table_data_term`;

  val _ = translate table_transition_def;

(*
  val _ = translate option_case_def;
  val _ = translate GSPEC_DEF;
  val _ = translate INSERT_DEF;
*)


  val _ = translate ABS;
  val _ = translate COMMA_DEF;
  val _ = translate table_data_def;

*)


val _ = export_theory();