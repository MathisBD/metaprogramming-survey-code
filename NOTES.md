### Questions

Coq: weird typeclass errors, especially when using monads --> this is what made Louise quit MetaCoq.

Coq: pretty printing library ? ==> reimplement a cleaner version of TemplateCoq/Pretty.v (which deals with indentation correctly).

MetaCoq: Where are "open recursors" for [term] ?

API vs Locally Nameless : context management.
  if tracking several terms in a same context : C |- t1, C |- t2, C |- t3
  opening a binder in (t1 = tProd _ A B) requires adding a declaration for A in C, and thus lifting t2 and t3

  if tracking several terms in different contexes : C1 |- t1, C2 |- t2, C3 |- t3
  opening a binder in (t1 = tProd _ A B) is OK : simply add a declaration for A in C1.
  !! but now you can't use A in t2 or t3 !!

Lean: building fixpoints (/let-rec) in Expr directly 
  -> lookup "predef"
  -> ask Mario if needed

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
