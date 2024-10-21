### Questions

Lean: building fixpoints (/let-rec) in Expr directly 
  -> lookup "predef"
  -> ask Mario if needed

MetaCoq: "open recursors" for [term] : are they in metacoq ? Should they be added ?

API: give me an example where "mk_tLambda" is *actually* useful (better than "kp_tLambda").

API: state_old, state_replace and state_scope is a mess, can we get rid of them ?

API: why do mk_tLambda, kp_tLambda etc take an [option ident] as input ?

### Bugs

- MetaCoq : noccur_between is incorrect. In the tRel case it should be || instead of &&.

### Thoughts on the languages

# Elpi 
- HOAS very good but needs relational programming

# Ltac2
- no support for open terms (e.g. can't typecheck or unify open terms) makes it horrible
- de Bruijn indices
- not made for commands (can't interact with global environment)

# Ocaml
- the API is terrible
- threading state by hand
- de Bruijn indices

# MetaCoq
- the API is a cleaned version of Ocaml's one
- threading state by hand     
- de Bruijn indices
- error handling is painful (as is any other effect, such as printing)
- no unification
