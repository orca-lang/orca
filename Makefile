OCAMLBUILD = ocamlbuild -use-ocamlfind -yaccflags --infer

default:
	tools/menhir-clean.sh
	tools/merlin-init.sh
	$(OCAMLBUILD) src/orca.byte

test: default
	tools/tests.sh

menhir:
	menhir --explain src/parser.mly

clean:
	$(OCAMLBUILD) -clean
	rm .merlin

all: default test
