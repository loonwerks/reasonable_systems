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
    val elm_str_list = (String.split_pattern (str, "[ \t\r\n\f\v]+"))
    val trimmed_elm_str_list = List.filter (fn str => str <> "") elm_str_list
    val trace = (List.map mk_elm trimmed_elm_str_list)
  in
    trace
  end)

end