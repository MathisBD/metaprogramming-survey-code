(** Derive the mapping function for an inductive type,
    and add the function to the global environment. *)
val derive : Libnames.qualid -> unit

(** Add the given mapping function to the database,
    so that it can be used when generating  *)
val add : Constrexpr.constr_expr -> unit
