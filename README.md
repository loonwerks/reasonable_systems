# Reasonable Systems 

This repo holds tools for verifying data, programs, and execution traces 
against specifications written in various logics, including Past Time LTL.

## Getting Started
Clone or download the repo.  Let's assume your local copy is in a directory called "reasonable_systems".  `cd reasonable_systems` and run `make`.  The built tools will be inside the directory `bin`.  The code targetted at mlton is in the directory `code-mlton`.  Example specifications are in `specs`.

### Prerequisites
PolyML - https://www.polyml.org/  
HOL4   - https://hol-theorem-prover.org/  
CakeML - https://cakeml.org/  
Python - https://www.python.org/
Retdec - https://retdec.com/  

### PTLTL 
The specification `histor ((b --> prev (~b since a)) /\ ~(a /\ b))` is stored in `specs/ptltl/spec_1.pt`.  It says that if there is a `b` then the preceding tokens since an `a` are not `b`s, and their was certainly a preceding `a`.  Additionally, `a` and `b` cannot occur simultaneously.

#### build step
```bash
$ cd code-hol4/ptltl
$ Holmake
```
#### synthesis step
```bash
$ ./synthesize.sh tablestep_monitor ../../specs/ptltl/spec_1.pt
```
multiple kinds of artifacts may be synthesized using the keywords `lex`, `gram`, `bigstep`, `smallstep`, `smallstep_monitor` and `tablestep_monitor`, and `dotgraph`.
for each of `bigstep`, `smallstep`, `smallstep_monitor` and `tablestep_monitor`, 4 kinds of artifacts are produced with extensions `.cakeml.sexp`, `.S`, `.exe`, and `.C`.

#### run step
```bash
$ ../../specs/ptltl/spec_1.pt.tablestep_monitor.exe
> a a a
ACCEPTED
> a b
ACCEPTED
> a b.c a.c
ACCEPTED
> b
ACCEPTED
> b
REJECTED
> a a a
REJECTED
```

Example specifications are in `specs/ptltl`.  The tokens are separated by white space.  A token containing words with dots in between means that each word of that token is active simultaneously.  That is, the formula accepts the token if the formula requires a subset of those words.  

The smallstep DFA synthesis is based on Havelund/Rosu's ["Synthesizing Monitors for Safety Properties"](https://ti.arc.nasa.gov/m/pub-archive/345h/0345%20(Havelund).pdf)  


#### PTLTL Proof Story

The top level correctness theorems state the equivalence between three defintions of
PTLTL machines: bigstep, smallstep, and dfa.
```
∀ form trace . bigstep form trace <=> smallstep form trace

∀ form trace . smallstep form trace <=> dfa form trace

∀ form trace . bigstep form trace <=> dfa form trace
```

smallstep is defined in terms of transition functions, each over a list of subformulas.
The transition functions are transition_start and transition.  
These are defined using FOLDL for speed.  For proof, it's useful to find an equivalent defintion that is structurally recursive over the list.

```
∀ sforms elm . transition_start (REVERSE sforms) elm = transition_start_rec sforms elm
```

The resulting value of the smallstep is the same as the membership of a formula in the result of the transition
functions.  To make reasoning over this easier, a more direct recursive boolean function called is used.

```
∀ form forms .
  list_wellformed forms ==> (
    list_step_start forms other_elm form <=> MEM form (transition_start_rec forms other_elm)
  )
  
```

bigstep is structural recursive over formulas, which is structurally binary trees.
formulas map to a corresponding operation in the host logic.
e.g. for implication:
```
∀ f1 f2 . bigstep (Imp f1 f2) <=> (bigstep f1 trace ==> bigstep f2 trace)
```

To show equivalence between bigstep and smallstep, we show that smallstep definitions can maintain
isomorphic mappings to the host logic.
```
∀ form form' .
  (list_step_start (nub (mk_subforms (Imp form form'))) other_elm (Imp form form')) <=>
  (
    list_step_start (nub (mk_subforms form)) other_elm form ==>
    list_step_start (nub (mk_subforms form')) other_elm form'
  )
```

Since transition_start_rec is structurally recursive over lists, but formulas are binary trees,
inducting over formulas won't work.  Instead we neew a way to characterize the list that's produced by
`mk_subforms`. `list_wellformed` is an attempt at this.  It states that if a formula exists in a list, then its subformulas exist in the remainder of the list.  Additionaly, the formula cannot be a child or equal to any formula in the remainder of the list, which entails that it cannot be a subform of any formula, since all children, and children of children, etc, are required to be in the list.     
Given list_wellformed is implied by mk_subforms, we can generalize:
```
∀ form fs form' fs' .
  list_wellformed fs ==>
  MEM form fs ==>
  list_wellformed fs' ==>
  MEM form' fs' ==>
  (
    (list_step_start
      (Imp form form' :: (FILTER (\x. ~MEM x fs') fs) ++ fs')
      other_elm
      (Imp form form')
    ) <=> (
      (list_step_start fs other_elm) form ==>
      (list_step_start fs' other_elm) form'
    )
  )
```

#### PTLTL Proof Dead Ends and Obstacles 
A handful of stragies were too difficult or infeasable.

 - Splitting equivalence into two implication lemmas. 
   - This weakened the induction hypothesis too much.

 - Inducting over FOLDL and characterizing the accumulator and the subforms list input.
   - This was too cumbersome. Switching to a natural recursive defintion appears simpler and removes the need for reversing the list.

 - Defining using case operater instead of parameter patterns  
   - This complicated rewriting
 








