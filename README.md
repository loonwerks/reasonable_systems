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

# build step
```bash
$ cd code-hol4/ptltl
$ Holmake
```
# synthesis step
```bash
$ ./synthesize.sh tablestep_monitor ../../specs/ptltl/spec_1.pt
```
multiple kinds of artifacts may be synthesized using the keywords `lex`, `gram`, `bigstep`, `smallstep`, `smallstep_monitor` and `tablestep_monitor`, and `dotgraph`.
for each of `bigstep`, `smallstep`, `smallstep_monitor` and `tablestep_monitor`, 4 kinds of artifacts are produced with extensions `.cakeml.sexp`, `.S`, `.exe`, and `.C`.

# run step
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