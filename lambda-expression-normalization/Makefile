all:
	ocamlc -c expr.ml
	ocamlc -c deBruijn.ml
	ocamllex lexer.mll
	ocamlyacc parser.mly
	ocamlc -c parser.mli
	ocamlc -c lexer.ml
	ocamlc -c parser.ml
	ocamlc -g lexer.cmo parser.cmo main.ml

run:
	./a.out
