#!/bin/sh

option=$1
filename=$2

./synthesize.exe $option $filename

$CAKE/cake --sexp=true < $filename.$option.cml.sexp > $filename.$option.S;

cc -o $filename.$option.exe $CAKEMLDIR/basis/basis_ffi.c $filename.$option.S
