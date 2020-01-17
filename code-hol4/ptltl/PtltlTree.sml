structure PtltlTree = struct

  datatype formula =
  
    Eid of string |
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
    Eid str => "(Eid " ^ str ^ ")"  |
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
  
    Histor f =>
      surround "Histor" (toString f) |

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


  fun to_hol_form form = (case form of
    Eid str => ``Eid ^(stringSyntax.fromMLstring str)`` |
    Prim b => (
      if b then
        ``Prim T``
      else
        ``Prim F``
    ) |

    Imp (f1, f2) =>
      ``Imp ^(to_hol_form f1) ^(to_hol_form f2)`` |

    Equiv (f1, f2) =>
      ``Equiv ^(to_hol_form f1) ^(to_hol_form f2)`` |

    Or (f1, f2) =>
      ``Or ^(to_hol_form f1) ^(to_hol_form f2)`` |

    Xor (f1, f2) =>
      ``Xor ^(to_hol_form f1) ^(to_hol_form f2)`` |

    And (f1, f2) =>
      ``And ^(to_hol_form f1) ^(to_hol_form f2)`` |

    Since (f1, f2) =>
      ``Since ^(to_hol_form f1) ^(to_hol_form f2)`` |

    Histor f =>
      ``Histor ^(to_hol_form f)`` |

    Once f => 
      ``Once ^(to_hol_form f)`` |

    Prev f => 
      ``Prev ^(to_hol_form f)`` |

    Start f => 
      ``Start ^(to_hol_form f)`` |

    End f => 
      ``End ^(to_hol_form f)`` |

    Not f => 
      ``Not ^(to_hol_form f)``
  )


end
