#!/bin/sh


if [ "$#" = 1 ]; then
    filename=$1

    ./synthesize.exe $filename
    
    dot -Tpng $filename.dotgraph -o $filename.dotgraph.png;
    $CAKE/cake --sexp=true < $filename.cml.sexp > $filename.S;
    cc -o $filename.exe $CAKEMLDIR/basis/basis_ffi.c $filename.S;
fi

if [ "$#" = 2 ]; then
    option=$1
    filename=$2

    ./synthesize.exe $option $filename
    
    if [ "$option" = "dotgraph" ] ; then
        dot -Tpng $filename.dotgraph -o $filename.dotgraph.png;
    fi
    
    if
        [ "$option" = "bigstep" ] || [ "$option" = "smallstep" ] ||
        [ "$option" = "smallstep_monitor" ]  || [ "$option" = "dfa_monitor" ]
    then
        $CAKE/cake --sexp=true < $filename.$option.cml.sexp > $filename.$option.S;
        cc -o $filename.$option.exe $CAKEMLDIR/basis/basis_ffi.c $filename.$option.S;
        #retdec-decompiler.py -o $filename.$option.c $filename.$option.exe;
    fi

fi
