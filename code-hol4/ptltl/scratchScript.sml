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



  val table_data_term = ``mk_table_data (mk_relational_data (Prim T))`` |> EVAL |> concl |> rhs;
  val table_data_def = Define `table_data = ^table_data_term`;

  val _ = map (fn hol_def => translate hol_def) common_hol_defs
  val _ = translate extract_ids_def;
  val _ = translate mk_power_list_def;
  val _ = translate LENGTH;
  val _ = translate find_reachable_edges_def;
  val _ = translate mk_relational_data_def;
  val _ = translate mk_table_data_def;
  val _ = translate table_transition_def;
  val _ = translate table_data_def;

  val lib_tm = get_ml_prog_state() |> get_prog

  val main_tm = (process_topdecs `
    fun main u = (let

      val (state_to_index, (elm_to_idx, (finals, (table, start_idx)))) = table_data


      fun verify_trace (state_idx, trace) = (case trace of
        [] => state_idx |
        (elm :: trace') => (let
          val elm_idx = elm_to_idx elm
        in
          verify_trace ((table_transition table state_idx elm_idx), trace')
        end)
      )


      fun verify_input (state_idx, input) = (let
        val trace = mk_trace (String.explode input)
        val state_idx' = verify_trace (state_idx, trace)

        val result_string = 
          (if (List.nth finals state_idx') then
            "ACCEPTED!!"
          else
            "REJECTED!!"
          )
        val _ = print (result_string ^ "\n")
      in
        state_idx'
      end)


      fun repl state_idx = (let
        val _ = print "> "
        val line_op = (TextIO.inputLine TextIO.stdIn)
        val _ = Option.map (fn line => 
          repl (verify_input (state_idx, line))
        ) line_op
      in
        ()
      end) 

      val _ = repl start_idx 

    in 
      ()
    end)

  `);

  val call_tm =
  ``
    (Dlet unknown_loc (Pcon NONE [])
      (App Opapp [Var (Short "main"); Con NONE []]))
  ``

  val prog_tm = ``(^lib_tm ++ ^main_tm ++ [^call_tm])`` |> EVAL |> concl |> rhs

(*
  val _ = write_ast_to_file ("test.tablestep_monitor.cml.sexp") prog_tm
*)


*)

val _ = export_theory();