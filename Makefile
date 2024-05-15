make:
	ocamllex lexer.mll
	ocamlyacc parser.mly
	ocamlc -c types.ml
	ocamlc -o main.exe types.ml parser.mli parser.ml lexer.ml main.ml
	./main.exe

clean:
	del lexer.ml parser.ml parser.mli 
	del *.c*
	del main.exe