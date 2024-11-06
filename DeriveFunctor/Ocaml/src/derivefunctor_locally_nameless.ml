(** In this file I try out a "locally nameless" style of programming, 
    by (ab)using the [Var] constructor of terms instead of using de Bruijn indices
    with the [Rel] constructor. 
*)

open Utils

(** [functor_kname] is the kernel name of the [Functor] typeclass. *)
let functor_kname = mk_kername [ "DeriveFunctor"; "Functor"; "Functor" ] "Functor"

(** [fmap_kname] is the kernel name of the [Functor.fmap] projection. *)
let fmap_kname = mk_kername [ "DeriveFunctor"; "Functor"; "Functor" ] "fmap"

(** A small record to hold the parameters of the mapping function while
      we build its body. *)
type inputs = { fmap : Names.Id.t; a : Names.Id.t; b : Names.Id.t; f : Names.Id.t; _x : Names.Id.t }

let build_arg env sigma (inp : inputs) (arg : EConstr.t) (arg_ty : EConstr.t) :
    Evd.evar_map * EConstr.t =
  let open EConstr in
  (* If [A] does not occur in [arg_ty], no need to map. *)
  if var_noccur sigma inp.a arg_ty
  then (sigma, arg)
  else
    (* Otherwise try to map over [arg].
       We use an evar in place of the [Functor] instance, which gets solved later on. *)
    let sigma, t = fresh_type sigma in
    let fct =
      mkLambda
        ( { binder_name = Names.Name (Names.Id.of_string "a")
          ; binder_relevance = ERelevance.relevant
          }
        , t
        , Vars.subst_var sigma inp.a arg_ty )
    in
    let sigma, inst = fresh_evar env sigma None in
    let sigma, fmap_func = fresh_global env sigma (ConstRef (Names.Constant.make1 fmap_kname)) in
    let new_arg = mkApp (fmap_func, [| fct; inst; mkVar inp.a; mkVar inp.b; mkVar inp.f; arg |]) in
    (sigma, new_arg)

let build_branch env sigma (inp : inputs) (ca : Inductiveops.constructor_summary)
    (cb : Inductiveops.constructor_summary) : Evd.evar_map * EConstr.t =
  let open EConstr in
  (* Bind the arguments of the constructor. *)
  namedLambdaContext env sigma ca.cs_args @@ fun env sigma args ->
  (* Map the correct function over each argument. *)
  (* We would really want to use something like List.mapM here instead of a recursive function. *)
  let arg_tys = List.map Context.Rel.Declaration.get_type ca.cs_args in
  let rec loop sigma acc args arg_tys =
    match (args, arg_tys) with
    | [], [] -> (sigma, acc)
    | arg :: args, ty :: arg_tys ->
        let sigma, new_arg = build_arg env sigma inp arg ty in
        loop sigma (new_arg :: acc) args arg_tys
    | _ -> Log.error "build_branch : length mismatch"
  in
  let sigma, mapped_args = loop sigma [] (List.map mkVar args) arg_tys in
  (* Apply the constructor to the arguments. *)
  (sigma, mkApp (mkConstructU cb.cs_cstr, Array.of_list (mkVar inp.b :: mapped_args)))

let build_fmap env sigma (ind : Names.inductive) : Evd.evar_map * EConstr.t =
  let open EConstr in
  (* Helper function to get the array of [constructor_summary] for a given parameter value [x]. *)
  let constructors env x : Inductiveops.constructor_summary list =
    let (_, inst), _ = UnivGen.fresh_inductive_instance env ind in
    Inductiveops.make_ind_family ((ind, EInstance.make inst), [ x ])
    |> Inductiveops.get_constructors env |> Array.to_list
  in
  (* Make the type of the recursive mapping function. *)
  let sigma, ta = fresh_type sigma in
  let sigma, tb = fresh_type sigma in
  let sigma, fmap_ty =
    namedProd env sigma "a" ta @@ fun env sigma a ->
    namedProd env sigma "b" tb @@ fun env sigma b ->
    ( sigma
    , mkArrowR
        (mkArrowR (mkVar a) (mkVar b))
        (mkArrowR (apply_ind env ind @@ mkVar a) (apply_ind env ind @@ mkVar b)) )
  in
  (* Abstract over the input variables. *)
  namedFix env sigma "fmap" 3 fmap_ty @@ fun env sigma fmap ->
  namedLambda env sigma "a" ta @@ fun env sigma a ->
  namedLambda env sigma "b" tb @@ fun env sigma b ->
  namedLambda env sigma "f" (mkArrowR (mkVar a) (mkVar b)) @@ fun env sigma f ->
  namedLambda env sigma "x" (apply_ind env ind @@ mkVar a) @@ fun env sigma x ->
  (* Add a let-binding for the recursive instance. *)
  let sigma, ev = fresh_evar env sigma None in
  let sigma, constr_t =
    fresh_global env sigma (ConstructRef ((Names.MutInd.make1 functor_kname, 0), 1))
  in
  let sigma, functor_t = fresh_global env sigma (IndRef (Names.MutInd.make1 functor_kname, 0)) in
  let sigma, ind_t = fresh_global env sigma (IndRef ind) in
  let rec_inst_body = mkApp (constr_t, [| ind_t; mkVar fmap |]) in
  let rec_inst_ty = mkApp (functor_t, [| ind_t |]) in
  namedLetIn env sigma "rec_inst" rec_inst_body rec_inst_ty @@ fun env sigma _ ->
  (* Construct the case return clause. *)
  let sigma, case_return =
    namedLambda env sigma "_" (apply_ind env ind @@ mkVar a) @@ fun env sigma _ ->
    (sigma, apply_ind env ind @@ mkVar b)
  in
  (* Construct the case branches. *)
  let rec loop sigma acc ctrs_a ctrs_b =
    match (ctrs_a, ctrs_b) with
    | [], [] -> (sigma, Array.of_list @@ List.rev acc)
    | ca :: ctrs_a, cb :: ctrs_b ->
        let sigma, branch = build_branch env sigma { fmap; a; b; f; _x = x } ca cb in
        loop sigma (branch :: acc) ctrs_a ctrs_b
    | _ -> Log.error "build_map : different lengths"
  in
  let sigma, branches = loop sigma [] (constructors env @@ mkVar a) (constructors env @@ mkVar b) in
  (* Finally construct the case expression. *)
  ( sigma
  , Inductiveops.simple_make_case_or_project env sigma
      (Inductiveops.make_case_info env ind Constr.RegularStyle)
      (case_return, ERelevance.relevant)
      Constr.NoInvert (mkVar x) branches )

(** [Derive Functor] command entry point. *)
let derive (ind_name : Libnames.qualid) : unit =
  (* Create the initial environment and evar map. *)
  let env = Global.env () in
  let sigma = Evd.from_env env in
  (* Resolve the inductive name to an inductive. *)
  let ind =
    match Smartlocate.locate_global_with_alias ind_name with
    | exception Not_found -> Log.error "Unknown reference %s" (Libnames.string_of_qualid ind_name)
    | IndRef ind -> ind
    | _ -> Log.error "%s is not an inductive" (Libnames.string_of_qualid ind_name)
  in
  (* Build the mapping function. *)
  let sigma, func = build_fmap env sigma ind in
  (* Package it in a [Functor] instance. *)
  let constr_name = ((Names.MutInd.make1 functor_kname, 0), 1) in
  let sigma, constr_t = EConstr.fresh_global env sigma (ConstructRef constr_name) in
  let sigma, ind_t = EConstr.fresh_global env sigma (IndRef ind) in
  let inst = EConstr.mkApp (constr_t, [| ind_t; func |]) in
  (* Type-check to make sure everything went right. *)
  let sigma, inst_ty = Typing.type_of env sigma inst in
  (* Solve typeclasses. *)
  let sigma = Typeclasses.resolve_typeclasses env sigma in
  (* To get around the guardchecker not performing enough reductions,
     we fully reduce the instance before declaring it.
     Without this, the current functor instance still typechecks but
     functions which use this instance might get rejected by the guard checker.
     This might be a hacky fix but it works well enough. *)
  let inst = Reductionops.nf_all env sigma inst in
  (* Choose a fresh name for the function. *)
  let basename =
    Names.Id.of_string_soft
    @@ (Names.Id.to_string @@ Libnames.qualid_basename ind_name)
    ^ "_functor"
  in
  (* Ensure it is fresh. *)
  let name = Namegen.next_global_ident_away basename Names.Id.Set.empty in
  (* Add the instance to the global environment. *)
  let info =
    Declare.Info.make ~kind:(Decls.IsDefinition Decls.Fixpoint)
      ~scope:(Locality.Global Locality.ImportDefaultBehavior) ()
  in
  let inst_ref =
    Declare.declare_definition ~info
      ~cinfo:(Declare.CInfo.make ~name ~typ:(Some inst_ty) ())
      ~opaque:false ~body:inst sigma
  in
  (* The global environment has changed. *)
  let env = Global.env () in
  let sigma = Evd.from_env env in
  (* Mark it as a typeclass instance. *)
  Classes.declare_instance env sigma None Hints.Export inst_ref
