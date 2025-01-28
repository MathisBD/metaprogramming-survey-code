### Questions

MetaCoq: Where are "open recursors" for [term] ? Should I add them ?

Lean: building fixpoints (or let-rec) in Expr directly 
  -> lookup "predef"
  -> ask Mario if needed

### Nice metaprogramming features

relevance indicated by number of (+).
- good binder representation +++
- unification ++
- quoting/unquoting ++
- tactics +
- nice state management +

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
