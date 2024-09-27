(** In this file I try out a "locally nameless" style of programming, 
    by (ab)using the [Var] constructor of terms instead of using de Bruijn indices
    with the [Rel] constructor. 
*)

(** Right-to-left function composition. *)
let ( <<< ) f g x = f (g x)

(** Left-to-right function composition. *)
let ( >>> ) f g x = g (f x)

(** Since we are in a command, there is no default evar map to grab from the proof state.
    Instead we create our own evar map (from the global environment) whenever the DeriveMap command
    is called, and store it in this global reference.
*)
let global_evd : Evd.evar_map ref = ref Evd.empty

(**************************************************************************************)
(** Logging. *)
(**************************************************************************************)

(** This module provides printf-style functions over the basic printing functions
    provided by Coq.  *)
module Log = struct
  (** [Log.printf] is a standard [printf] function, except it automatically adds 
      a newline at the end. *)
  let printf fmt = Format.ksprintf (Feedback.msg_notice <<< Pp.str) fmt

  let error fmt = Format.ksprintf (fun res -> CErrors.user_err (Pp.str res)) fmt

  (** Print an [EConstr.t] to a string. *)
  let show_econstr t : string =
    Pp.string_of_ppcmds
    @@ Printer.pr_constr_env (Global.env ()) !global_evd
    @@ EConstr.to_constr !global_evd t

  (** Print the internal representation of an [EConstr.t] to a string. *)
  let debug_econstr t : string =
    t |> EConstr.to_constr !global_evd |> Constr.debug_print |> Pp.string_of_ppcmds
end

(**************************************************************************************)
(** Manipulating terms. *)
(**************************************************************************************)

(** [fresh_ident basename] returns a fresh identifier built from [basename] 
    and which is guaranteed to be distinct from all identifiers returned by this function so far. *)
let fresh_ident : string -> Names.Id.t =
  let used_names = ref Names.Id.Set.empty in
  fun basename ->
    let name = Namegen.next_ident_away (Names.Id.of_string_soft basename) !used_names in
    used_names := Names.Id.Set.add name !used_names;
    name

(** [namedLambda ?relevance name ty body] makes a lambda abstraction with the given parameters,
    in the locally nameless style. *)
let namedLambda ?(relevance = EConstr.ERelevance.relevant) (name : string) (ty : EConstr.types)
    (body : Names.Id.t -> EConstr.constr) : EConstr.constr =
  let id = fresh_ident name in
  EConstr.mkNamedLambda !global_evd { binder_name = id; binder_relevance = relevance } ty (body id)

(** Generalizes [namedLambda] to multiple variables in a [EConstr.rel_context]. 

    The body receives the variables in the same order they are stored in the context, 
    i.e. the most recent (= inner-most) variable first. 
*)
let namedLambdaContext (ctx : EConstr.rel_context) (body : Names.Id.t list -> EConstr.t) : EConstr.t
    =
  let open EConstr in
  let open Context in
  let open Rel in
  (* Generate identifiers for the variables in the context. *)
  let ids =
    ctx
    |> List.map @@ fun decl ->
       match Declaration.get_name decl with
       | Name n -> fresh_ident (Names.Id.to_string n)
       | Anonymous -> fresh_ident "x"
  in
  (* Build the body and substitute de Bruijn indices for the identifiers. *)
  let body = Vars.subst_vars !global_evd ids (body ids) in
  (* Add lambda abstractions. *)
  List.fold_left
    (fun body decl ->
      mkLambda
        ( { binder_name = Declaration.get_name decl
          ; binder_relevance = Declaration.get_relevance decl
          }
        , Declaration.get_type decl
        , body ))
    body ctx

(** Create a [Type] term with a fresh universe level. *)
let fresh_type () : EConstr.t =
  let level = UnivGen.fresh_level () in
  global_evd := Evd.add_global_univ !global_evd level;
  EConstr.mkType @@ Univ.Universe.make level

(**************************************************************************************)
(** Derive Map. *)
(**************************************************************************************)

(** A small record to hold the parameters of the mapping function while 
    we build its body. *)
type params = { a : Names.Id.t; b : Names.Id.t; f : Names.Id.t; _x : Names.Id.t }

let build_arg (p : params) (arg : EConstr.t) (arg_ty : EConstr.t) : EConstr.t =
  let open EConstr in
  if eq_constr !global_evd (mkVar p.a) arg_ty then mkApp (mkVar p.f, [| arg |]) else arg

let build_branch (p : params) (ca : Inductiveops.constructor_summary)
    (cb : Inductiveops.constructor_summary) : EConstr.t =
  let open EConstr in
  (* Bind the arguments of the constructor. *)
  namedLambdaContext ca.cs_args @@ fun args ->
  (* Map the correct function over each argument. *)
  let arg_tys = List.map Context.Rel.Declaration.get_type ca.cs_args in
  let mapped_args = List.map2 (build_arg p) (List.map mkVar args) arg_tys in
  (* Apply the constructor to the arguments. *)
  mkApp (mkConstructU cb.cs_cstr, Array.of_list (mkVar p.b :: (List.rev @@ mapped_args)))

let build_map (ind : Names.inductive) : EConstr.t =
  let open EConstr in
  (* Helper function to apply the inductive to a single parameter. *)
  let apply_ind t : EConstr.t =
    let (_, inst), _ = UnivGen.fresh_inductive_instance (Global.env ()) ind in
    mkApp (mkIndU (ind, EInstance.make inst), [| t |])
  in
  (* Helper function to get the array of [constructor_summary] for a given parameter [x]. *)
  let constructors x : Inductiveops.constructor_summary array =
    let (_, inst), _ = UnivGen.fresh_inductive_instance (Global.env ()) ind in
    Inductiveops.make_ind_family ((ind, EInstance.make inst), [ x ])
    |> Inductiveops.get_constructors (Global.env ())
  in
  (* Abstract over the input variables. *)
  namedLambda "a" (fresh_type ()) @@ fun a ->
  namedLambda "b" (fresh_type ()) @@ fun b ->
  namedLambda "f" (mkArrowR (mkVar a) (mkVar b)) @@ fun f ->
  namedLambda "x" (apply_ind @@ mkVar a) @@ fun x ->
  (* Construct the case return clause. *)
  let case_return = namedLambda "_" (apply_ind @@ mkVar a) @@ fun _ -> apply_ind @@ mkVar b in
  (* Construct the case branches. *)
  let branches =
    Array.map2 (build_branch { a; b; f; _x = x }) (constructors @@ mkVar a) (constructors @@ mkVar b)
  in
  (* Finally construct the case expression. *)
  Inductiveops.simple_make_case_or_project (Global.env ()) !global_evd
    (Inductiveops.make_case_info (Global.env ()) ind Constr.RegularStyle)
    (case_return, ERelevance.relevant)
    Constr.NoInvert (mkVar x) branches

(** [DeriveMap] command entry point. *)
let derive (ind_name : Libnames.qualid) : unit =
  (* Create the evar map. *)
  global_evd := Evd.from_env @@ Global.env ();
  (* Resolve the inductive name to an inductive. *)
  let ind =
    match Smartlocate.locate_global_with_alias ind_name with
    | exception Not_found -> Log.error "Unknown reference %s" (Libnames.string_of_qualid ind_name)
    | IndRef ind -> ind
    | _ -> Log.error "%s is not an inductive" (Libnames.string_of_qualid ind_name)
  in
  (* Build the mapping function. *)
  let func = build_map ind in
  Log.printf "The mapping function :\n%s" (Log.show_econstr func);
  (* Type-check to make sure everything went right. *)
  let _ = Typing.type_of (Global.env ()) !global_evd func in
  Log.printf "Typechecked!"

(** [TestCommand] command entry point. *)
let test (id : Libnames.qualid) : unit =
  global_evd := Evd.from_env @@ Global.env ();
  let decl =
    match Smartlocate.locate_global_with_alias id with
    | ConstRef cst -> Environ.lookup_constant cst (Global.env ())
    | _ -> Log.error "Not found"
  in
  let body =
    match decl.const_body with Def body -> EConstr.of_constr body | _ -> Log.error "No body"
  in
  let _info, _, _, ((_, ret), _), _inv, _x, branches = EConstr.destCase !global_evd body in
  Log.printf "RET %s" @@ Log.show_econstr ret;
  Array.iter (fun (_, b) -> Log.printf "BRANCH %s" @@ Log.show_econstr b) branches
