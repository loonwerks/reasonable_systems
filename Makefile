all: bin/ptltl

bin/ptltl: code-mlton/ptltl/chars-lang/chars.lex.sml code-mlton/ptltl/tokens-lang/tokens.yacc.sml
	mkdir -p bin; mlton -output bin/ptltl code-mlton/ptltl/config.mlb

code-mlton/ptltl/chars-lang/chars.lex.sml:
	mllex code-mlton/ptltl/chars-lang/chars.lex

code-mlton/ptltl/tokens-lang/tokens.yacc.sig code-mlton/ptltl/tokens-lang/tokens.yacc.sml:
	mlyacc code-mlton/ptltl/tokens-lang/tokens.yacc

clean:
	git clean -Xf; rm -r bin/*
