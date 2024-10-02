all:
	dune build
	lake build

install:
	dune install

clean:
	dune clean
	lake clean