#!/bin/sh

option=$1
filename=$2

./synthesize.exe $option $filename

if [ "$option" = "dotgraph" ] ; then
    dot -Tpng $filename.dotgraph -o $filename.dotgraph.png;
    google-chrome $filename.dotgraph.png
fi

if
    [ "$option" = "bigstep" ] || [ "$option" = "smallstep" ] ||
    [ "$option" = "smallstep_monitor" ]  || [ "$option" = "tablestep_monitor" ]
then
    $CAKE/cake --sexp=true < $filename.$option.cml.sexp > $filename.$option.S;
    cc -o $filename.$option.exe $CAKEMLDIR/basis/basis_ffi.c $filename.$option.S;
    #retdec-decompiler.py -o $filename.$option.c $filename.$option.exe;
fi
