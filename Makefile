default:
	utils/menhir-clean.sh
	ocamlbuild -use-ocamlfind src/nanuq.byte

test: default
	utils/tests.sh

menhir:
	menhir --explain src/parser.mly 

clean:
	ocamlbuild -clean

all: default test
