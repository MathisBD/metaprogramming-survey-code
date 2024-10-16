all:
	dune build
	lake build

install: all
	dune install

clean:
	dune clean
	lake clean