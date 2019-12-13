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

val _ = export_theory();


(* ****interactive proof scrap work: *****
val TODO_def = Hol_defn "TODO" ` 


`
Defn.tgoal TODO_def
*)


(*
fun mk_transitions form = (let 
  val subforms = unique (mk_subforms form)
  val size = List.length subforms
  
  fun decide_formula_start (fm, state, elm) = (case fm of
    Id str =>
      (elm str) |

    Prim b =>
      b |

    Imp (f1, f2) => 
      not (state f1) orelse
      (state f2) |

    Equiv (f1, f2) => 
      (state f1) = (state f2) |

    Or (f1, f2) =>
      (state f1) orelse (state f2) |

    Xor (f1, f2) =>
      not ((state f1) = (state f2)) |

    And (f1, f2) =>
      (state f1) andalso (state f2) |

    Since (f1, f2) =>
      (state f1) andalso 
      (state f2) |

    Histor f => 
      (state f) |

    Once f => 
      (state f) |

    Prev f => 
      (state f) |

    Start f =>
      false |

    End f => 
      false |

    Not f => 
      not (state f)
  )


  (* the state is represented as a mapping from subformulas to booleans *) 
    
  
  fun transition_start elm = (List.foldl
    (fn (fm, state_acc) => let
      val decision =
        decide_formula_start (fm, state_acc, elm)
    in
      (fn fm' => 
        if fm = fm' then
          decision
        else
          (state_acc fm')
      )
    end)
    empty_state 
    (rev subforms)
  )

  fun decide_formula (fm, state, state_acc, elm) = (case fm of
    Id str =>
      (elm str) |

    Prim b =>
      b |

    Imp (f1, f2) => 
      not (state_acc f1) orelse
      (state_acc f2) |

    Equiv (f1, f2) =>
      (state_acc f1) = (state_acc f2) |

    Or (f1, f2) =>
      (state_acc f1) orelse (state_acc f2) |

    Xor (f1, f2) =>
      not ((state_acc f1) = (state_acc f2)) |

    And (f1, f2) =>
      (state_acc f1) andalso (state_acc f2) |

    Since (f1, f2) =>
      (state_acc f2) orelse (
        state_acc f1 andalso
        state (Since (f1, f2))
      ) |

    Histor f =>
      (state_acc f) andalso
      (state (Histor f)) |

    Once f =>
      (state_acc f) orelse
      (state (Once f)) |

    Prev f =>
      (state f) |

    Start f =>
      (state_acc f) andalso
      not (state f) |

    End f =>
      not (state_acc f) andalso
      (state f) |

    Not f => 
      not (state_acc f) 
    
  )

  fun transition (state, elm) = (List.foldl
    (fn (fm, state_acc) => let
      val decision =
        decide_formula (fm, state, state_acc, elm)
    in
      (fn fm' => 
        if fm = fm' then
          decision
        else
          (state_acc fm')
      )
    end)
    empty_state
    (rev subforms)
  )


in
  (transition_start, transition) 
end)

fun to_dfa form = (let
  val (transition_start, transition) = mk_transitions form

  fun loop (elms, state) = (case elms of
    [] => state form |
    elm :: elms' => (let
      val state' = transition (state, elm)
    in
      loop (elms', state')
    end)
  )

  fun dfa elms = (case elms of
    [] =>
      dfa [other_elm] |

    elm :: elms' =>
      loop (elms', transition_start elm)
  )

in
  dfa
end)



*)






