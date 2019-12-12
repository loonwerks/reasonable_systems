# Reasonable Systems 

This repo holds tools for verifying data, programs, and execution traces 
against specifications written in various logics, including Past Time LTL.

## Getting Started
Clone or download the repo.  Let's assume your local copy is in a directory called "reasonable_systems".  `cd reasonable_systems` and run `make`.  The built tools will be inside the directory `bin`.  The code targetted at mlton is in the directory `code-mlton`.  Example specifications are in `specs`.

### Prerequisites
Make sure you have MLton (http://mlton.org/) installed.


### PTLTL
The specification `histor ((b --> prev (~b since a)) /\ ~(a /\ b))` is stored in `specs/ptltl/spec_1.pt`.  It says that if there is a `b` then the preceding tokens since an `a` are not `b`s, and their was certainly a preceding `a`.  Additionally, `a` and `b` cannot occur simultaneously.

The following sorts of commands are possible with the `ptltl` program:
```bash
$ bin/ptltl --lex specs/ptltl/spec_1.pt
1:1 HISTOR 
1:3 LPAREN
1:4 LPAREN
1:5 ID
1:7 LONGARROW
1:9 PREV
1:11 LPAREN
...

$ bin/ptltl --parse specs/ptltl/spec_1.pt
(Histor
  (And
    (Imp
      (Id b),
      (Prev
        ...
      )
    ),
    ...
  )
)


$ bin/ptltl --verify specs/ptltl/spec_1.pt "a a b a b a.c a"
ACCEPTED

$ bin/ptltl --dfa specs/ptltl/spec_1.pt "a a b a b.c a a"
ACCEPTED

$ bin/ptltl --monitor specs/ptltl/spec_1.pt
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


$ bin/ptltl --graph specs/ptltl/spec_1.pt 
$ ./show_graph specs/ptltl/spec_1.pt.graph 

```

The `--lex` flag generates a list of tokens from the specification.
The `--parse` flag generates a tree from the specification.
The `--verify` flag checks the specification against the string of tokens.
The `--dfa` flag synthesizes a DFA from the specification and runs the DFA on the tokens.
The `--monitor` flag synthesizes DFA transitions from the specification and runs the transitions on the sequences of tokens on interactive inputs.
The `--graph` flag syntehsizes a DFA graph and writes a DOT graph representation to `<input_file>.graph`. Running `./show_graph <input_file>.graph` will convert the DOT file to a PNG and open in Google Chrome.

Example specifications are in `specs/ptltl`.  The tokens are separated by white space.  A token containing words with dots in between means that each word of that token is active simultaneously.  That is, the formula accepts the token if the formula requires a subset of those words.
The concrete syntax of PTLTL is described in `code-mlton/ptltl/chars.lex` and `code-mlton/ptltl/tokens.yacc`.
The abstract syntax of PTLTL is in  `code-mlton/ptltl/tree-lang/tree.sml` in the datatype called `formula`.
Implementation of the verify functionality is in `code-mlton/ptltl/tree-lang/tree.sml` in the function called `verify`.
Implementation of the synthesis of the DFA is in `code-mlton/ptltl/tree-lang/tree.sml` in the function called `to_dfa`.
The DFA synthesis is based on Havelund/Rosu's ["Synthesizing Monitors for Safety Properties"](https://ti.arc.nasa.gov/m/pub-archive/345h/0345%20(Havelund).pdf)
