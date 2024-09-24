# Description 

This project contains several example tactics and commands written in Elpi, Ltac2, MetaCoq and Ocaml.

# Setup

Setup a local opam switch with coq :
```
opam switch create . 5.2.0
opam install coq.8.19.2
opam pin add coq 8.19.2
```

Install elpi :
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-elpi
```