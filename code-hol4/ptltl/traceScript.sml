open HolKernel Parse boolLib bossLib lcsymtacs;
open combinTheory pairTheory listTheory stringLib;

(*
open preamble basis MapProgTheory open ml_translatorLib ml_progLib basisFunctionsLib ml_translatorTheory cfTacticsBaseLib cfDivTheory cfDivLib charsetTheory regexpTheory regexp_compilerTheory;
*)

open ml_translatorLib;
open ml_progLib;
open fromSexpTheory astToSexprLib;

open ptltlTheory


val _ = new_theory "trace";

Definition mk_elm_def :
  mk_elm (str : string) = (TOKENS (\ c . c = #".") str)
End

Definition mk_trace_def :
  mk_trace (str : string) =
  let elm_str_list = (TOKENS (\ c . MEM c " \t\r\n\f\v") str);
      trimmed_elm_str_list = FILTER (\str . str <> "") elm_str_list; 
  in (MAP mk_elm trimmed_elm_str_list)
End


val _ = export_theory();
