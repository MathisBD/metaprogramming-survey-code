# Description 

This project contains several example Coq tactics and commands written in Elpi, Ltac2, MetaCoq and Ocaml.

# Setup

Setup a local opam switch with coq :
```
opam switch create . 5.2.0 --repos default,coq-released=https://coq.inria.fr/opam/released
```
and select yes (Y) when asked to create as a new package.

Optionally install development packages. For instance if using VSCode :
```
opam install ocaml-lsp-server ocamlformat user-setup
opam user-setup install
```

Use `dune build` to build the examples, and `dune install` if you want to step through the Coq files interactively.