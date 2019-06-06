OPAMDIR   := $(shell opam config var lib)
ZARITHDIR := $(OPAMDIR)/zarith
OCB = ocamlbuild

all:
	dune build main.exe && time ./_build/default/main.exe

clean:
	$(OCB) -clean

exec:
