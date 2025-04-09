All the implementations are independent.

# Agda

Install Agda (version 2.7.0.1). 
Then install the [`agda-stdlib`](https://github.com/agda/agda-stdlib) and [`agda-stdlib-classes`](https://github.com/agda/agda-stdlib-classes) libraries (installation instructions can be found in the linked repositories).

# Lean 

Follow https://lean-lang.org/lean4/doc/quickstart.html.

Inside the `Lean` subdirectory, run `lake build`. 
This will locally install Lean (version 4.12.0), and build and run the code.

# Rocq

Assuming you have the `opam` package manager installed, you can install Rocq (version 8.20.1) and the required packages in an opam switch named `rocq-metaprogramming`:
```
opam update
opam switch create rocq-metaprogramming 4.14.2
eval $(opam env --switch=rocq-metaprogramming)
opam repo add coq-released https://coq.inria.fr/opam/released
opam pin add -n coq-metacoq-utils https://github.com/MetaCoq/metacoq.git#d19cfb9
opam pin add -n coq-metacoq-common https://github.com/MetaCoq/metacoq.git#d19cfb9
opam pin add -n coq-metacoq-template https://github.com/MetaCoq/metacoq.git#d19cfb9
opam install coq.8.20.1 coq-elpi coq-metacoq-template
```

To build the OCaml plugins, navigate to the relevant folder (`OCaml_de_Bruijn` or `OCaml_locally_nameless`) and run `dune build && dune install`. 

Examples can always be found in the file `DeriveFunctor.v` and stepped through interactively.
Files can also be built with `coqc DeriveFunctor.v`.
