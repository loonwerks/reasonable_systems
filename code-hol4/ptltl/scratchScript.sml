open HolKernel Parse boolLib bossLib lcsymtacs;
open combinTheory pairTheory listTheory stringLib;

open preamble basis 
open ml_translatorLib;
open ml_progLib;
open fromSexpTheory astToSexprLib;


open ptltlTheory traceTheory

val _ = new_theory "scratch";


(*

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

  val hol_dfa_term = EVAL (SPEC hol_form to_dfa_def |> concl |> rhs) |> concl |> rhs;

  val hol_dfa_def = Define `dfa = ^hol_dfa_term`;



  val _ = map (fn hol_def => translate hol_def) [ 
    K_DEF,
    NULL_DEF,
    HD,
    TL_DEF,
    FOLDL,
    REVERSE_DEF,
    IN_DEF,
    LIST_TO_SET_DEF,
    nub_def,
    FST,
    SND,
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
    mk_transitions_def,
    dfa_loop_def,
    hol_dfa_def,
    mk_elm_def,
    mk_trace_def
  ]

  val lib_tm = get_ml_prog_state() |> get_prog

  val main_tm = process_topdecs `
    fun main u =
        let
          val cl = CommandLine.arguments ()
          val str = String.concatWith " " cl
          val trace = mk_trace (String.explode str)
          val b_result = dfa trace
          val _ = TextIO.print (
            if b_result then
              "ACCEPTED"
            else
              "REJECTED"
          )
        in TextIO.output1 TextIO.stdOut #"\n"
        end
  `;


  val call_tm =
  ``
    (Dlet unknown_loc (Pcon NONE [])
      (App Opapp [Var (Short "main"); Con NONE []]))
  ``

  val prog_tm = ``^lib_tm ++ ^main_tm ++ [^call_tm]`` |> EVAL |> concl |> rhs
  
  val _ = write_ast_to_file ("test.dfa.cml.sexp") prog_tm;
*)

val _ = export_theory();