(**************************************************************************************)
(** Manipulating terms. *)
(**************************************************************************************)

(** [fresh_type sigma] creates a [Type] term with a fresh universe level, 
    and adds the new universe level to the evar map. *)
let fresh_type sigma : Evd.evar_map * EConstr.t =
  let level = UnivGen.fresh_level () in
  let sigma = Evd.add_global_univ sigma level in
  (sigma, EConstr.mkType @@ Univ.Universe.make level)

(** [app f x] is a lightweight notation for an application to one argument. *)
let app (f : EConstr.t) (x : EConstr.t) : EConstr.t = EConstr.mkApp (f, [| x |])

(** [apps f xs] is a lightweight notation for an application to several arguments. *)
let apps (f : EConstr.t) (xs : EConstr.t array) : EConstr.t = EConstr.mkApp (f, xs)

(** [lambda env sigma name ty body] builds a lambda abstraction.
    The [body] has access to the environment extended with a local declaration for the bound variable. *)
let lambda env sigma (name : string) (ty : EConstr.t)
    (body : Environ.env -> Evd.evar_map * EConstr.t) : Evd.evar_map * EConstr.t =
  let open EConstr in
  let binder_name = Names.Name (Names.Id.of_string_soft name) in
  let inner_env =
    Environ.push_rel
      (LocalAssum ({ binder_name; binder_relevance = Sorts.Relevant }, EConstr.to_constr sigma ty))
      env
  in
  let sigma, body = body inner_env in
  (sigma, mkLambda ({ binder_name; binder_relevance = ERelevance.relevant }, ty, body))

(** [prod env sigma name ty body] builds a dependent product.
    The [body] has access to the environment extended with a local declaration for the bound variable. *)
let prod env sigma (name : string) (ty : EConstr.t) (body : Environ.env -> Evd.evar_map * EConstr.t)
    : Evd.evar_map * EConstr.t =
  let open EConstr in
  let binder_name = Names.Name (Names.Id.of_string_soft name) in
  let inner_env =
    Environ.push_rel
      (LocalAssum ({ binder_name; binder_relevance = Sorts.Relevant }, EConstr.to_constr sigma ty))
      env
  in
  let sigma, body = body inner_env in
  (sigma, mkProd ({ binder_name; binder_relevance = ERelevance.relevant }, ty, body))

(** [fix env sigma name rec_arg_idx ty body] makes a single fixpoint with the given parameters.
    - [name] is the name of the fixpoint parameter.
    - [rec_arg_idx] is the index of the (structurally) recursive argument, starting at [0].
    - [ty] is the type of the fixpoint parameter.
    - [body] is the body of the fixpoint, which has access to the extended environment.

    For instance to build the fixpoint [fix add (n : nat) (m : nat) {struct_ m} : nat := ...]
    one could use [fix env sigma "add" 1 '(nat -> nat -> nat) (fun env -> ...)].
*)
let fix env sigma (name : string) (rec_arg_idx : int) (ty : EConstr.t)
    (body : Environ.env -> Evd.evar_map * EConstr.t) : Evd.evar_map * EConstr.t =
  let open EConstr in
  let binder_name = Names.Name (Names.Id.of_string_soft name) in
  let inner_env =
    Environ.push_rel
      (LocalAssum ({ binder_name; binder_relevance = Sorts.Relevant }, EConstr.to_constr sigma ty))
      env
  in
  let sigma, body = body inner_env in
  ( sigma
  , mkFix
      ( ([| rec_arg_idx |], 0)
      , ( [| { binder_name = Name (Names.Id.of_string_soft name)
             ; binder_relevance = ERelevance.relevant
             }
          |]
        , [| ty |]
        , [| body |] ) ) )

(** [arr t1 t2] constructs the non-dependent product [t1 -> t2]. It takes care of lifting [t2]. *)
let arr (t1 : EConstr.t) (t2 : EConstr.t) : EConstr.t = EConstr.mkArrowR t1 (EConstr.Vars.lift 1 t2)

(** [subterm x t] checks whether [x] occurs in [t], modulo alpha equivalence.
    It takes time [O(size(x) * size(t))]. *)
let rec subterm sigma (x : EConstr.t) (t : EConstr.t) : bool =
  EConstr.fold_with_binders sigma (EConstr.Vars.lift 1)
    (fun x b subt -> b || subterm sigma x subt)
    x (EConstr.eq_constr sigma x t) t

(* Helper function to apply the inductive to a single parameter. *)
let apply_ind env (ind : Names.Ind.t) (t : EConstr.t) : EConstr.t =
  let (_, inst), _ = UnivGen.fresh_inductive_instance env ind in
  app (EConstr.mkIndU (ind, EConstr.EInstance.make inst)) t

(**************************************************************************************)
(** Lifting mapping functions. *)
(**************************************************************************************)

(** This module handles lifting of functions from basic types to more elaborate types. *)
module Lift = struct
  (** A lifting problem consists in lifting a function [f : A -> B] to a function [T -> U].
      It is assumed that U is equal to T with A replaced by B. *)
  type problem = { a : EConstr.t; b : EConstr.t; f : EConstr.t; t : EConstr.t; u : EConstr.t }

  (** A lifting rule takes as input a lifting problem, and either :
      - Fails by returning [None]
      - Succeeds by returning a function [Some f'] where [f' : T -> U].

      Formally lifting rules form a (simple) monad, and this would indeed be the ideal
      way to program with them IMO. This way the standard functions defined below (such as [sequence])
      could be automatically generated using some kind of functor. In the interest of keeping this
      example simple I stick to a simpler approach.
    *)
  type rule = Environ.env -> Evd.evar_map -> problem -> (Evd.evar_map * EConstr.t) option

  (** Basic lifting rule when [T] = [A].
      In this case we solve with [f' = f] *)
  let apply_rule : rule =
   fun env sigma lp ->
    Log.printf "LIFT APPLY on %s" (Log.show_econstr env sigma lp.t);
    match Unification.w_unify env sigma Conversion.CONV lp.a lp.t with
    | exception _ -> None
    | sigma -> Some (sigma, lp.f)

  (** Basic lifting rule when [A] does not occur in [T].
      In this case we solve with [f' x = x]. *)
  let id_rule : rule =
   fun env sigma lp ->
    Log.printf "LIFT ID on %s" (Log.show_econstr env sigma lp.t);
    if subterm sigma lp.a lp.t
    then None
    else Some (lambda env sigma "x" lp.t @@ fun env -> (sigma, EConstr.mkRel 1))

  (** [mzero] is a lifting rule which always fails. *)
  let mzero : rule = fun _ _ _ -> None

  (** [msum r1 r2] tries the rule [r1], and if it fails applies [r2]. *)
  let msum (r1 : rule) (r2 : rule) : rule =
   fun env sigma lp -> match r1 env sigma lp with None -> r2 env sigma lp | Some res -> Some res

  (** [sequence rs] combines the lifting rules [rs] by trying them out in order from first to last
      until one succeeds. *)
  let sequence (rs : rule list) : rule =
    match rs with [] -> mzero | r :: rs -> List.fold_left msum r rs

  (** Fixpoints for rules. Using [let-rec] manually might trigger infinite recursion :
      one has to take care of eta-expanding the definition (as is done in [fix]). *)
  let rec fix (f : rule -> rule) : rule = fun env sigma lp -> f (fix f) env sigma lp

  (** [detruct_map f] checks that [f] is a mapping function i.e. has type [forall (A B : Type), (A -> B) -> T A -> T B]
      and returns [Some T] if it succeeds or [None] if it fails. *)
  let destruct_map env sigma (map_func : EConstr.t) : (Evd.evar_map * EConstr.t) option =
    let open EConstr in
    let sigma, t1 = fresh_type sigma in
    let sigma, t2 = fresh_type sigma in
    let sigma, ta = fresh_type sigma in
    let sigma, tb = fresh_type sigma in
    let sigma, type_former = Evarutil.new_evar env sigma @@ mkArrowR t1 t2 in
    let sigma, pat =
      prod env sigma "a" ta @@ fun env ->
      prod env sigma "b" tb @@ fun env ->
      ( sigma
      , arr
          (arr (mkRel 2) (mkRel 1))
          (arr (app type_former @@ mkRel 2) (app type_former @@ mkRel 1)) )
    in
    let map_ty = Retyping.get_type_of env sigma map_func in
    match Unification.w_unify env sigma Conversion.CONV pat map_ty with
    | exception _ -> None
    | sigma -> Some (sigma, type_former)

  let custom_rule (rec_rule : rule) (map_ref : Names.GlobRef.t) : rule =
   fun env sigma lp ->
    (* Instantiate the mapping function. *)
    let map_func, _cs = UnivGen.fresh_global_instance env map_ref in
    (* Extract the type former. *)
    match destruct_map env sigma @@ EConstr.of_constr map_func with
    | None -> Log.error "Lift.custom_rule : error"
    | Some (sigma, type_former) -> begin
        Log.printf "RULE %s on %s"
          (Log.show_econstr env sigma type_former)
          (Log.show_econstr env sigma lp.t);
        (* Create unification variables ?alpha and ?beta. *)
        let sigma, talpha = fresh_type sigma in
        let sigma, tbeta = fresh_type sigma in
        let sigma, alpha = Evarutil.new_evar env sigma talpha in
        let sigma, beta = Evarutil.new_evar env sigma tbeta in
        (* Unify [T =?= type_former ?alpha] and [U =?= type_former ?beta]. *)
        match Unification.w_unify env sigma Conversion.CONV lp.t (app type_former alpha) with
        | exception e -> None
        | sigma -> begin
            match Unification.w_unify env sigma Conversion.CONV lp.u (app type_former beta) with
            | exception e -> None
            | sigma -> begin
                (* Recurse to lift [f : A -> B] to [f' : alpha -> beta]. *)
                Log.printf "RECURSING on %s" (Log.show_econstr env sigma alpha);
                match rec_rule env sigma { lp with t = alpha; u = beta } with
                | None -> None
                | Some (sigma, f') ->
                    Some (sigma, apps (EConstr.of_constr map_func) [| alpha; beta; f' |])
              end
          end
      end
end

(**************************************************************************************)
(** AddMap and DeriveMap commands. *)
(**************************************************************************************)

(** We store some mapping rules in a database :
      - AddMap adds rules to the database.
      - DeriveMap uses the rules in the database.
 *)
let map_db : Names.GlobRef.t list ref = Summary.ref ~name:"Derivemap_de_bruijn Rule Database" []

(** A small record to hold the parameters of the mapping function while
    we build its body. *)
type params = { ind : Names.Ind.t; map : int; a : int; b : int; f : int; x : int }

(** [lift_params n params] lifts the parameters [params] under [n] binders. *)
let lift_params (n : int) (p : params) : params =
  { p with map = p.map + n; a = p.a + n; b = p.b + n; f = p.f + n; x = p.x + n }

(** [replace_rel sigma a b t] replaces [Rel a] with [Rel b] in [t]. *)
let rec replace_rel sigma (a : int) (b : int) (t : EConstr.t) : EConstr.t =
  if EConstr.isRelN sigma a t
  then EConstr.mkRel b
  else EConstr.map_with_binders sigma (( + ) 1) (replace_rel sigma a) b t

let build_arg env sigma (p : params) (arg : EConstr.t) (arg_ty : EConstr.t) :
    Evd.evar_map * EConstr.t =
  let open EConstr in
  (* Construct the lifting problem. *)
  let lp =
    Lift.
      { a = mkRel p.a
      ; b = mkRel p.b
      ; f = mkRel p.f
      ; t = arg_ty
      ; (* [u] is equal to [t] with [a] replaced by [b]. *)
        u = replace_rel sigma p.a p.b arg_ty
      }
  in
  Log.printf "build arg : { a=%s ; b=%s ; f=%s ; t=%s ; u=%s }" (Log.show_econstr env sigma lp.a)
    (Log.show_econstr env sigma lp.b) (Log.show_econstr env sigma lp.f)
    (Log.show_econstr env sigma lp.t) (Log.show_econstr env sigma lp.u);
  (* Build a custom rule for [T = Ind A]. *)
  let map_rule : Lift.rule =
   fun env sigma lp ->
    if eq_constr sigma lp.t (apply_ind env p.ind lp.a)
    then Some (sigma, apps (mkRel p.map) [| lp.a; lp.b; lp.f |])
    else None
  in
  (* Build the rule we will use to solve our lifting problem.
     We use the rules in the database in addition to [map_rule]. *)
  let rule =
    let open Lift in
    fix @@ fun rec_rule ->
    sequence (apply_rule :: id_rule :: map_rule :: List.map (custom_rule rec_rule) !map_db)
  in
  (* Solve the lifting problem. *)
  match rule env sigma lp with
  | Some (sigma, f') -> (sigma, app f' arg)
  | None ->
      Log.error "Failed to lift mapping function of type [%s -> %s] on argument of type [%s]"
        (Log.show_econstr env sigma lp.a) (Log.show_econstr env sigma lp.b)
        (Log.show_econstr env sigma lp.t)

let build_branch env sigma (p : params) (ca : Inductiveops.constructor_summary)
    (cb : Inductiveops.constructor_summary) : Evd.evar_map * EConstr.t =
  let open EConstr in
  let open Context.Rel.Declaration in
  Log.printf "build branch";
  (* Map the correct function over each argument.
     We process the arguments from outermost to innermost. *)
  let rec loop env sigma i acc decls =
    match decls with
    | [] -> (sigma, acc)
    | decl :: decls ->
        let env = Environ.push_rel decl env in
        let sigma, new_arg =
          (* We call build_arg at a depth which is consistent with the local context of the environment,
             and we lift the result to bring it at depth [n]. *)
          build_arg env sigma
            (lift_params (i + 1) p)
            (mkRel 1)
            (Vars.lift 1 @@ EConstr.of_constr @@ get_type decl)
        in
        loop env sigma (i + 1) (Vars.lift (ca.cs_nargs - i - 1) new_arg :: acc) decls
  in
  let sigma, mapped_args =
    loop env sigma 0 [] (List.rev @@ EConstr.to_rel_context sigma ca.cs_args)
  in
  (* Apply the constructor to the arguments. Careful about the order of the arguments. *)
  let body =
    mkApp
      (mkConstructU cb.cs_cstr, Array.of_list (mkRel (ca.cs_nargs + p.b) :: List.rev mapped_args))
  in
  (* Bind the constructor arguments. *)
  let branch =
    EConstr.it_mkLambda body
    @@ List.map
         (function LocalAssum (binder, ty) | LocalDef (binder, _, ty) -> (binder, ty))
         ca.cs_args
  in
  (sigma, branch)

let build_map env sigma (ind : Names.inductive) : Evd.evar_map * EConstr.t =
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
  let sigma, map_ty =
    prod env sigma "a" ta @@ fun env ->
    prod env sigma "b" tb @@ fun env ->
    ( sigma
    , arr
        (arr (mkRel 2) (mkRel 1))
        (arr (apply_ind env ind @@ mkRel 2) (apply_ind env ind @@ mkRel 1)) )
  in
  (* Abstract over the input parameters. *)
  fix env sigma "map" 3 map_ty @@ fun env ->
  lambda env sigma "a" ta @@ fun env ->
  lambda env sigma "b" tb @@ fun env ->
  lambda env sigma "f" (arr (mkRel 2) (mkRel 1)) @@ fun env ->
  lambda env sigma "x" (apply_ind env ind @@ mkRel 3) @@ fun env ->
  (* Construct the case return clause. *)
  let sigma, case_return =
    lambda env sigma "_" (apply_ind env ind @@ mkRel 4) @@ fun env ->
    (sigma, apply_ind env ind @@ mkRel 4)
  in
  (* Construct the case branches. *)
  let rec loop sigma acc ctrs_a ctrs_b =
    match (ctrs_a, ctrs_b) with
    | [], [] -> (sigma, Array.of_list @@ List.rev acc)
    | ca :: ctrs_a, cb :: ctrs_b ->
        let sigma, branch =
          build_branch env sigma { ind; map = 5; a = 4; b = 3; f = 2; x = 1 } ca cb
        in
        loop sigma (branch :: acc) ctrs_a ctrs_b
    | _ -> Log.error "build_map : different lengths"
  in
  let sigma, branches = loop sigma [] (constructors env @@ mkRel 4) (constructors env @@ mkRel 3) in
  (* Finally construct the case expression. *)
  ( sigma
  , Inductiveops.simple_make_case_or_project env sigma
      (Inductiveops.make_case_info env ind Constr.RegularStyle)
      (case_return, ERelevance.relevant)
      Constr.NoInvert (mkRel 1) branches )

(** [DeriveMap] command entry point. *)
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
  let sigma, func = build_map env sigma ind in
  Log.printf "The mapping function :\n%s" (Log.show_econstr env sigma func);
  (* Type-check to make sure everything went right. *)
  let sigma, ty = Typing.type_of env sigma func in
  Log.printf "Typechecked!";
  (* Choose a fresh name for the function. *)
  let basename =
    Names.Id.of_string_soft @@ (Names.Id.to_string @@ Libnames.qualid_basename ind_name) ^ "_map"
  in
  let name = Namegen.next_global_ident_away basename Names.Id.Set.empty in
  (* Add the function to the global environment. *)
  let info =
    Declare.Info.make ~kind:(Decls.IsDefinition Decls.Fixpoint)
      ~scope:(Locality.Global Locality.ImportDefaultBehavior) ()
  in
  ignore
  @@ Declare.declare_definition ~info
       ~cinfo:(Declare.CInfo.make ~name ~typ:(Some ty) ())
       ~opaque:false ~body:func sigma

(** [AddMap] command entry point. *)
let add (map_ref : Libnames.qualid) : unit =
  (* Create the initial environment and evar map. *)
  let env = Global.env () in
  let sigma = Evd.from_env env in
  (* Locate the global reference. *)
  let map_ref = Smartlocate.locate_global_with_alias map_ref in
  (* Check it is indeed a mapping function (so that we can fail now instead of in DeriveMap). *)
  let map_func, _ = UnivGen.fresh_global_instance env map_ref in
  match Lift.destruct_map env sigma @@ EConstr.of_constr map_func with
  | None -> Log.error "Provided function is not a mapping function."
  | Some _ ->
      (* Add the function to the map database. *)
      map_db := map_ref :: !map_db
