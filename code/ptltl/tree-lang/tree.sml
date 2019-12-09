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
  
    Histor of formula |
    Once of formula |
    Prev of formula |
    Start of formula |
    End of formula |
    Not of formula
  
  val other_elm = (fn id => false) 

  val empty_state = (fn fm => false)

  fun unique_f xs f = (case xs of
    [] => [] |
    x :: xs' => (case (List.find
      (fn y => (f y) = (f x))
      xs'
    ) of
      NONE => x :: (unique_f xs' f) |
      SOME _ => (unique_f xs' f) 
    )
  )

  fun unique xs = unique_f xs (fn x => x)

  fun toString form = (case form of
    Id str => "(Id " ^ str ^ ")"  |
    Prim b => "(Prim " ^ (Bool.toString b) ^ ")" |
  
    Imp (f1, f2) => String.surround "Imp" (
      (toString f1) ^ ",\n" ^ (toString f2)
    ) |

    Equiv (f1, f2) => String.surround "Equiv" (
      (toString f1) ^ ",\n" ^ (toString f2)
    ) |

    Or (f1, f2) => String.surround "Or" (
      (toString f1) ^ ",\n" ^ (toString f2)
    ) |

    Xor (f1, f2) => String.surround "Xor" (
      (toString f1) ^ ",\n" ^ (toString f2)
    ) |

    And (f1, f2) => String.surround "And" (
      (toString f1) ^ ",\n" ^ (toString f2)
    ) |

    Since (f1, f2) => String.surround "Since" (
      (toString f1) ^ ",\n" ^ (toString f2)
    ) |
  
    Histor f =>
      String.surround "Histor" (toString f) |

    Once f => 
      String.surround "Once" (toString f) |

    Prev f => 
      String.surround "Prev" (toString f) |

    Start f => 
      String.surround "Start" (toString f) |

    End f => 
      String.surround "End" (toString f) |

    Not f => 
      String.surround "Not" (toString f)
  )

  (* trace has most recent label on top *)
  fun verify (trace, form) = (let

    (*
    ** val _ = print ("stack: [" ^ (String.concatWith ", " trace) ^ "]\n") 
    *)

    val (elm, trace_prev) = (case trace of
      [] => (other_elm, []) |
      [x] => (x, []) |
      x :: xs => (x, xs)
    )

  in
    (case form of
      Id str =>
        (elm str) | 

      Prim b =>
        b |

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

      Histor f =>
        verify (trace, f) andalso (
          (null trace_prev) orelse
          verify (trace_prev, Histor f)
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
  
    Histor f =>
      Histor f :: (mk_subforms f) |

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


  fun power_set xs = (case xs of
    [] =>
      [[]] |
    x :: xs' => (let
      val remainder = power_set xs'
    in
      (map (fn st => x :: st) remainder) @
      remainder
    end)
  )

  fun extract_prims form = unique (case form of
    Id str => [str] |
    Prim b => [] |
    Imp (f1, f2) =>
      extract_prims f1 @ extract_prims f2 |

    Equiv (f1, f2) =>
      extract_prims f1 @ extract_prims f2 |

    Or (f1, f2) =>
      extract_prims f1 @ extract_prims f2 |

    Xor (f1, f2) =>
      extract_prims f1 @ extract_prims f2 |

    And (f1, f2) => 
      extract_prims f1 @ extract_prims f2 |

    Since (f1, f2) =>
      extract_prims f1 @ extract_prims f2 |
  
    Histor f =>
      extract_prims f |

    Once f => 
      extract_prims f |

    Prev f => 
      extract_prims f |

    Start f => 
      extract_prims f |

    End f => 
      extract_prims f |

    Not f => 
      extract_prims f
  )

  fun map xs f = List.map f xs
  fun flat_map xs f = List.concat (map xs f)
  fun map_part xs f = List.mapPartial f xs

  val start_state_str = "_"

  fun to_dfa_graph form = (let

    val other_elm_id = "_"
    val prim_list = extract_prims form

    val elm_pairs = unique_f (List.map
      (fn prims => (
        String.concatWith "." prims,
        (fn q_prim => (case (List.find
          (fn prim => q_prim = prim)
          prims 
        ) of
          NONE => false |
          SOME _ => true
        ))
      ))
      (* simplify*)
      (map prim_list (fn x => [x]))
      (* (power_set (other_elm_id :: elm_id_list)) *)
    ) (fn (str, f) => str)

    val (transition_start, transition) = mk_transitions form



    fun first_index (xs, f) = (case xs of
      [] => 0 |
      x :: xs' =>
        if (f x) then
          0
        else
          1 + (first_index (xs', f))
    )

    val subforms = unique (mk_subforms form)
    val subform_sets = power_set subforms


    fun mk_state_str state_fn = (let

      val true_subforms = (List.filter
        (fn subform => state_fn subform)
        subforms 
      )

      val idx = first_index (
        subform_sets, 
        (fn st => st = true_subforms)
      )


      val check = List.nth (subform_sets, idx) 

      (*
      fun formset_to_string subforms = 
        "[" ^ (String.concatWith ", " (map subforms toString)) ^ "]"

      val _ = print ("expected: " ^ (formset_to_string true_subforms) ^ "\n")
      val _ = print ("actual: " ^ (formset_to_string check) ^ "\n")
      val _ = print ("\n")
      *)

      val _ = if (not (check = true_subforms)) then 
        (print ("ALERT:\n"); raise (Fail "ALERT!"))
      else ()
    in
      (Int.toString idx)
    end)


    
    val start_edges = (map elm_pairs (fn (elm_str, elm_fn) => let
      val state_fn = (transition_start elm_fn)
      val state_str = mk_state_str state_fn
    in
      ((start_state_str, empty_state), (elm_str, elm_fn), (state_str, state_fn))
    end))



    fun mk_state_fn subforms = (fn (subform) =>
      (case (List.find
        (fn sf => sf = subform)
        subforms
      ) of
        NONE => false |
        SOME _ => true
      )
    )


    fun find_reachable_edges edges = (let
      val new_edges =
      (flat_map edges (fn (_, _, (state_str', state_fn')) => 
      (flat_map elm_pairs (fn (elm_str, elm_fn) => let
        val state_fn'' = transition (state_fn', elm_fn)
        val state_str'' = mk_state_str state_fn''
        val is_new_edge = (case (List.find
          (fn ((old_st, _), (old_elm, _), (old_st', _)) =>
            old_st = state_str' andalso
            old_elm = elm_str andalso
            old_st' = state_str''
          )
          edges
        ) of NONE => true | SOME _ => false)
      in
        if is_new_edge then
          [((state_str', state_fn'), (elm_str, elm_fn), (state_str'', state_fn''))]
        else
          []
      end))
      ))
    in
      if (null new_edges) then
        edges
      else
        (find_reachable_edges (new_edges @ edges))
    end)

    val edges = unique_f (find_reachable_edges start_edges)
      (fn ((st,_), (label, _), (st', _)) => (st, label, st'))

    fun is_reachable state_str = (case (List.find
      (fn (_, _, (reachable_state_str, _)) =>
        state_str = reachable_state_str
      )
      edges
    ) of 
      NONE => false |
      SOME _ => true
    )

    val accept_state_strs = (map_part subform_sets (fn subform_set => let
      val state_fn = mk_state_fn subform_set

      val ss_size = List.length subform_set
      val state_str = mk_state_str state_fn 

      
    in
      if (is_reachable state_str) andalso (state_fn form) then
        SOME state_str
      else
        NONE
    end))

  in
    {
      accept_states = accept_state_strs,
      edges = edges
    }
  end)



  fun to_dot_graph {accept_states, edges} = (let
    val graph_str =
    "digraph finite_state_machine {\n" ^
    "  rankdir = LR;\n" ^ 
    "  node [shape = circle]; \"" ^ start_state_str ^ "\";\n" ^
    (if (null accept_states) then "" else 
    "  node [shape = doublecircle]; " ^
         (String.concatWith "; " accept_states) ^ ";\n"
    ) ^
    "  node [shape = plaintext];\n" ^
    "  \"\" -> \"" ^ start_state_str ^ "\" [label = \"start\"];\n" ^
    "  node [shape = circle];\n" ^
    (String.concat (map edges (fn ((st, _), (label, _), (st', _)) =>
      st ^ "->" ^ st' ^ "[label = \"" ^ label ^ "\"];\n"
    ))) ^
    "}"
  in
    graph_str
  end)


  


end