open helloProgTheory
  preamble basis 
  fromSexpTheory astToSexprLib

val hello_tm = hello_fun_def |> concl |> rhs 

val maincall_tm =
``
  (Dlet unknown_loc (Pcon NONE [])
    (App Opapp [Var (Short "hello"); Con NONE []]))
``

val prog_tm = ``SNOC ^maincall_tm  ^hello_tm``
           |> EVAL |> concl |> rhs

fun main () = write_ast_to_file "hello.scake" prog_tm


