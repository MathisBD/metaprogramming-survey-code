# Description 

This project contains several example tactics and commands written in Coq (Elpi, Ltac2, MetaCoq and Ocaml) and Lean.
-   DeriveMap : defines a command `DeriveMap myind` which derives a mapping function on the inductive `myind`.
    It assumes `myind` has exactly one uniform parameter, and builds a function of type `forall A B, (A -> B) -> myind A -> myind B`.

# Building and running

Use the Makefile : `make` and `make install`.

# Coq Setup

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

Use `dune build` to build the Coq examples, and `dune install` if you want to step through the Coq files interactively.

# Lean Setup

Install the Lean toolchain :
```
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

You might need to run `lake update` in the root directory of the project.

Use `lake build` to build the Lean examples.