structure Tree = struct

  datatype formula =
  
    Id of string |
    Prim of bool |
  
    Imp of (formula * formula) |
    Equiv of (formula * formula) |
    Or of (formula * formula) |
    Xor of (formula * formula) |
    And of (formula * formula) |
    Since of (formula * formula) |
  
    Always of formula |
    Once of formula |
    Prev of formula |
    Start of formula |
    End of formula |
    Not of formula
  
  val other_token = "_other_"

  fun surround tag body = (let
    val abc = "(" ^ tag
    val bodyLines = String.tokens (fn c => c = #"\n") body
    val indentedLines = map (fn l => "  " ^ l) bodyLines
    val indentedBody = String.concatWith "\n" indentedLines 
    val xyz = if body = "" then ")" else "\n" ^ indentedBody ^ "\n)"
  in
    abc ^ xyz 
  end)


  fun toString form = (case form of
    Id str => "(Id " ^ str ^ ")"  |
    Prim b => "(Prim " ^ (Bool.toString b) ^ ")" |
  
    Imp (f1, f2) => surround "Imp" (
      (toString f1) ^ ",\n" ^ (toString f2)
    ) |

    Equiv (f1, f2) => surround "Equiv" (
      (toString f1) ^ ",\n" ^ (toString f2)
    ) |

    Or (f1, f2) => surround "Or" (
      (toString f1) ^ ",\n" ^ (toString f2)
    ) |

    Xor (f1, f2) => surround "Xor" (
      (toString f1) ^ ",\n" ^ (toString f2)
    ) |

    And (f1, f2) => surround "And" (
      (toString f1) ^ ",\n" ^ (toString f2)
    ) |

    Since (f1, f2) => surround "Since" (
      (toString f1) ^ ",\n" ^ (toString f2)
    ) |
  
    Always f =>
      surround "Always" (toString f) |

    Once f => 
      surround "Once" (toString f) |

    Prev f => 
      surround "Prev" (toString f) |

    Start f => 
      surround "Start" (toString f) |

    End f => 
      surround "End" (toString f) |

    Not f => 
      surround "Not" (toString f)
  )

  (* trace has most recent label on top *)
  fun verify (trace, form) = (let

    (*
    ** val _ = print ("stack: [" ^ (String.concatWith ", " trace) ^ "]\n") 
    *)

    val (l_now, trace_prev) = (case trace of
      [] => (other_token, []) |
      [x] => (x, []) |
      x :: xs => (x, xs)
    )

  in
    (case form of
      Id str => (str = l_now) | 

      Prim b => b |

      Imp (f1, f2) =>
        not (verify (trace, f1)) orelse
        verify (trace, f2) |

      Equiv (f1, f2) =>
        verify (trace, f1) =
        verify (trace, f2) |

      Or (f1, f2) =>
        verify (trace, f1) orelse 
        verify (trace, f2) |

      Xor (f1, f2) =>
        not (
          verify (trace, f1) =
          verify (trace, f2)
        ) |

      And (f1, f2) =>
        verify (trace, f1) andalso 
        verify (trace, f2) |

      Since (f1, f2) =>
        verify (trace, f2) orelse (
          not (null trace_prev) andalso
          verify (trace, f1) andalso
          verify (trace_prev, Since (f1, f2))
        ) |

      Always f =>
        verify (trace, f) andalso (
          (null trace_prev) orelse
          verify (trace_prev, Always f)
        ) |

     
      Once f =>
        verify (trace, f) orelse (
          not (null trace_prev) andalso 
          verify (trace_prev, Once f)
        ) |

      Prev f =>
        (
          (null trace_prev) andalso 
          verify (trace, f)
        ) orelse (
          verify (trace_prev, f)
        ) |

      Start f =>
        verify (trace, f) andalso
        not (verify (trace, Prev f)) |

      End f => 
        verify (trace, Prev f) andalso 
        not (verify (trace, f)) |

      Not f => 
        not (verify (trace, f)) 
     
    )
  end)


  fun mk_subforms form = (case form of
    Id str =>
      [Id str] |

    Prim b =>
      [Prim b] |
  
    Imp (f1, f2) =>
      Imp (f1, f2) ::
      (mk_subforms f1) @
      (mk_subforms f2) |

    Equiv (f1, f2) =>
      Equiv (f1, f2) ::
      (mk_subforms f1) @
      (mk_subforms f2) |

    Or (f1, f2) =>
      Or (f1, f2) ::
      (mk_subforms f1) @
      (mk_subforms f2) |

    Xor (f1, f2) =>
      Xor (f1, f2) ::
      (mk_subforms f1) @
      (mk_subforms f2) |

    And (f1, f2) =>
      And (f1, f2) ::
      (mk_subforms f1) @
      (mk_subforms f2) |

    Since (f1, f2) =>
      Since (f1, f2) ::
      (mk_subforms f1) @
      (mk_subforms f2) |
  
    Always f =>
      Always f :: (mk_subforms f) |

    Once f =>
      Once f :: (mk_subforms f) |

    Prev f =>
      Prev f :: (mk_subforms f) |

    Start f =>
      Start f :: (mk_subforms f) |

    End f =>
      End f :: (mk_subforms f) |

    Not f =>
      Not f :: (mk_subforms f)
  )


  fun to_dfa form = (let 
    val subforms = mk_subforms form
    val size = List.length subforms
    
    fun decide_formula_start (fm, state, tk) = (case fm of
      Id str =>
        str = tk |

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

      Always f => 
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

    fun transition_start tk = (List.foldl
      (fn (fm, state_acc) => let
        val decision =
          decide_formula_start (fm, state_acc, tk)
      in
        (fn fm' => 
          if fm = fm' then
            decision
          else
            (state_acc fm')
        )
      end)
      (fn fm => false)
      (rev subforms)
    )

    fun decide_formula (fm, state, state_acc, tk) = (case fm of
      Id str =>
        str = tk |

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

      Always f =>
        (state_acc f) andalso
        (state (Always f)) |

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

    fun transition (state, tk) = (List.foldl
      (fn (fm, state_acc) => let
        val decision =
          decide_formula (fm, state, state_acc, tk)
      in
        (fn fm' => 
          if fm = fm' then
            decision
          else
            (state_acc fm')
        )
      end)
      (fn fm => false)
      (rev subforms)
    )

    fun dfa tokens = (case tokens of
      [] =>
        dfa [other_token] |

      tk :: tks => (let
        fun loop (tokens, state) = (case tokens of
          [] => state form |
          tk :: tks => (let
            val state' = transition (state, tk)
          in
            (state' form) andalso 
            loop (tks, state')
          end)
        )
      in
        loop (tks, transition_start tk)
      end)
    )

  in
    dfa
  end)

end