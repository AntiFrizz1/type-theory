all:
	ocamlc -c expr.ml
	ocamllex lexer.mll
	ocamlyacc parser.mly
	ocamlc -c parser.mli
	ocamlc -c lexer.ml
	ocamlc -c parser.ml
	ocamlc -c main.ml
	ocamlc lexer.cmo parser.cmo main.cmo

run:
	./a.out
