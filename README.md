# Reasonable Systems 

This repo holds tools for verifying data, programs, and execution traces 
against specifications written in various logics, including Past Time LTL.

## Getting Started
Clone or download the repo.  Let's assume your local copy is in a directory called "reasonable_systems".  `cd reasonable_systems` and run `make`.  The built tools will be inside the directory `bin`.  The code is in the directory `code`.  Example specifications are in `specs`.

### Prerequisites
Make sure you have MLton (http://mlton.org/) installed.


### PTLTL
The following types of commands are possible for the ptltl program:
```bash
bin/ptltl --lex specs/ptltl/spec_1.pt
bin/ptltl --parse specs/ptltl/spec_1.pt
bin/ptltl --verify specs/ptltl/spec_1.pt "a a b a b a.c a"
bin/ptltl --dfa specs/ptltl/spec_1.pt "a a b a b.c a a"
```

The `--lex` flag generates a list of tokens from the specification.
The `--parse` flag generates a tree from the specification.
The `--verify` flag checks the specification against the string of tokens.
The `--dfa` flag synthesizes a DFA from the specification and runs the DFA on the tokens.

Example specifications are in `specs/ptltl`.  The tokens are separated by white space.  A token containing words with dots in between means that each word of that token is active simultaneously.  That is, the formula accepts the token if the formula requires a subset of those words.
The concrete syntax of PTLTL is described in `code/ptltl/chars.lex` and `code/ptltl/tokens.yacc`.
The abstract syntax of PTLTL is in  `code/ptltl/tree-lang/tree.sml` in the datatype called `formula`.
Implementation of the verify functionality is in `code/ptltl/tree-lang/tree.sml` in the function called `verify`.
Implementation of the synthesis of the DFA is in `code/ptltl/tree-lang/tree.sml` in the function called `to_dfa`.
The DFA synthesis is based on Havelund/Rosu's ["Synthesizing Monitors for Safety Properties"](https://ti.arc.nasa.gov/m/pub-archive/345h/0345%20(Havelund).pdf)
