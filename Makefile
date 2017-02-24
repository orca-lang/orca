OCAMLBUILD = ocamlbuild -use-ocamlfind -yaccflags --infer

default:
	tools/menhir-clean.sh
	$(OCAMLBUILD) src/orca.byte

test: default
	tools/tests.sh

menhir:
	menhir --explain src/parser.mly

clean:
	$(OCAMLBUILD) -clean

all: default test
