OCAMLBUILD = ocamlbuild -use-ocamlfind -yaccflags --infer

default:
	utils/menhir-clean.sh
	$(OCAMLBUILD) src/nanuq.byte

test: default
	utils/tests.sh

menhir:
	menhir --explain --infer src/parser.mly

clean:
	$(OCAMLBUILD) -clean

all: default test
