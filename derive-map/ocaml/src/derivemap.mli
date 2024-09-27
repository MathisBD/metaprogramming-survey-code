(** Derive the mapping function for an inductive type,
   and add the function to the global environment. *)
val derive : Libnames.qualid -> unit

(** A debug command. *)
val test : Libnames.qualid -> unit
