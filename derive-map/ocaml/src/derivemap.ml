(** Since we are in a command, there is no default evar map to grab from the proof state.
    Instead we create our own evar map (from the global environment) whenever the DeriveMap command
    is called, and store it in this global reference.
*)
let global_evd : Evd.evar_map ref = ref Evd.empty

(** This module provides printf-style functions over the basic printing functions
    provided by Coq.  *)
module Log = struct
  let printf fmt = Format.ksprintf (fun res -> Feedback.msg_notice (Pp.str res)) fmt
  let error fmt = Format.ksprintf (fun res -> CErrors.user_err (Pp.str res)) fmt

  (* Print an EConstr.t to a string. *)
  let show_econstr t : string =
    Pp.string_of_ppcmds
    @@ Printer.pr_constr_env (Global.env ()) !global_evd
    @@ EConstr.to_constr !global_evd t
end

let build_map (ind : Names.inductive) : EConstr.t =
  let open EConstr in
  let bind name ty body =
    mkLambda
      ({ binder_name = Name (Names.Id.of_string name); binder_relevance = Relevant }, ty, body)
  in
  bind "A" (mkType @@ Univ.Universe.make @@ UnivGen.fresh_level ())
  @@ bind "B" (mkType @@ Univ.Universe.make @@ UnivGen.fresh_level ())
  @@ bind "f" (mkProd ({ binder_name = Anonymous; binder_relevance = Relevant }, mkRel 2, mkRel 2))
  @@ mkRel 3 (* TODO *)

(** [DeriveMap] command entry point. *)
let derive (ind_name : Libnames.qualid) : unit =
  (* Create the evar map. *)
  global_evd := Evd.from_env (Global.env ());
  (* Resolve the inductive name to an inductive. *)
  let ind =
    match Smartlocate.locate_global_with_alias ind_name with
    | exception Not_found -> Log.error "Unknown reference %s" (Libnames.string_of_qualid ind_name)
    | IndRef ind -> ind
    | _ -> Log.error "%s is not an inductive" (Libnames.string_of_qualid ind_name)
  in
  (* Build the mapping function. *)
  let func = build_map ind in
  Log.printf "The mapping function :\n%s" (Log.show_econstr func)
