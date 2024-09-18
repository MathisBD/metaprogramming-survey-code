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
opem install coq-elpi
```