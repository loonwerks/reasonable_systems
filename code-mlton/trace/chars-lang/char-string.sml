structure Char_String = struct

  fun mk_elm str = (let
    val elm_id_list = (String.split_pattern (str, "(\\.)+"))
    val elm  = (List.foldl
      (fn (elm_id, elm_fn_acc) =>
        (fn id =>
          (elm_id = id) orelse 
          (elm_fn_acc id)
        )
      )
      (fn id => false)
      elm_id_list
    )
  in
    elm
  end)
  
  fun mk_trace str = (let
    val trimmed_str = String.substring (str, 0, (String.size str) - 1)
    val elm_str_list = (String.split_pattern (trimmed_str, "[ \t\r\n\f\v]+"))
    val trace_length = List.length elm_str_list
    val trace = (List.map mk_elm elm_str_list)
  in
    trace
  end)

end