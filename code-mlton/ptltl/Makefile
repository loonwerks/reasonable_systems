all: ../../bin/ptltl

../../bin/ptltl:chars-lang/chars.lex.sml tokens-lang/tokens.yacc.sml
	mkdir -p ../../bin; mlton -output ../../bin/ptltl config.mlb

chars-lang/chars.lex.sml:
	mllex chars-lang/chars.lex

tokens-lang/tokens.yacc.sig tokens-lang/tokens.yacc.sml:
	mlyacc tokens-lang/tokens.yacc

clean:
	git clean -Xf; rm -r ../../bin/*
