Parameter TemplateMonad : Type -> Type.
Parameter (term typed_term string constant_entry mutual_inductive_entry 
  global_reference reduction_strategy context : Type).

(** * Logging. *)

Inductive log_level :=
  | Debug 
  | Info 
  | Notice 
  | Warning 
  | Error.

Definition tmLog {A : Type} (lvl : log_level) (contents : A) : TemplateMonad unit.
Admitted.

(* Backward compat *)
Definition tmMsg (s : string) := tmLog Info s. (* Is this one correct ? *)
Definition tmPrint {A} (contents : A) := tmLog Info contents.

(** * Unquoting. *)

Definition tmUnquote' (solve_typeclasses : bool) (t : term) : TemplateMonad typed_term.
Admitted.

Definition tmUnquoteTyped' {A} (solve_typeclasses : bool) (ty : A) (t : term) : TemplateMonad A.
Admitted.

(* Backward compat *)
Definition tmUnquote t := tmUnquote' false t.
Definition tmUnquoteTyped {A} (ty : A) (t : term) := tmUnquoteTyped' false ty t.

(** * Extending the environment. *)

Definition tmConstantEntry (unquote_fresh_univs : bool) (entry : constant_entry) : TemplateMonad global_reference.
Admitted.

Definition tmInductiveEntry (unquote_fresh_univs : bool) (entry : mutual_inductive_entry) : TemplateMonad global_reference.
Admitted.

(* Backward compat *)

(** * Typeclasses. *)

Definition tmExistingClass (ref : global_reference) : TemplateMonad unit.
Admitted.

Definition tmInferInstance' (s : option reduction_strategy) (ctx : context) (ty : term) : TemplateMonad (option term).
Admitted.

(* QUESTIONS

- Why are there two version (e.g. TmInferInstance/TmInferInstanceTerm or TmEval/TmEvalTerm)
  for many functions ? Can't one be defined in terms of the other ? Why are some implemented in Plugin_core.ml 
  and some directly in run_template_monad.ml ?

- How to properly deal with the evar map (and thus universes) in tmMkDefinition/tmMkInductive ?
  Why do we refresh universes ?

*)