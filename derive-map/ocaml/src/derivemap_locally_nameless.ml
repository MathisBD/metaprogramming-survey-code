(** In this file I try out a "locally nameless" style of programming, 
    by (ab)using the [Var] constructor of terms instead of using de Bruijn indices
    with the [Rel] constructor. 
*)

(**************************************************************************************)
(** Manipulating terms. *)
(**************************************************************************************)

(** [fresh_type sigma] creates a [Type] term with a fresh universe level, 
    and adds the new universe level to the evar map. *)
let fresh_type sigma : Evd.evar_map * EConstr.t =
  let level = UnivGen.fresh_level () in
  let sigma = Evd.add_global_univ sigma level in
  (sigma, EConstr.mkType @@ Univ.Universe.make level)

(** [fresh_ident basename] returns a fresh identifier built from [basename] 
    and which is guaranteed to be distinct from all identifiers returned by this function so far. *)
let fresh_ident : string -> Names.Id.t =
  let used_names = ref Names.Id.Set.empty in
  fun basename ->
    let name = Namegen.next_ident_away (Names.Id.of_string_soft basename) !used_names in
    used_names := Names.Id.Set.add name !used_names;
    name

(** [with_fresh_var env sigma basename ty k] generates a fresh identifier built from [basename], 
    adds a corresponding declaration to [env] and executes the continuation [k]
    in this augmented environment. *)
let with_fresh_var env sigma (basename : string) (ty : EConstr.t)
    (k : Environ.env -> Evd.evar_map -> Names.Id.t -> 'a) : 'a =
  let id = fresh_ident basename in
  let decl =
    Context.Named.Declaration.LocalAssum
      ({ binder_name = id; binder_relevance = Sorts.Relevant }, EConstr.to_constr sigma ty)
  in
  k (Environ.push_named decl env) sigma id

(** Generalizes [with_fresh_var] to several variables. The last variables in the list 
    are introduced first in the context. 
    
    The continuation receives the variables in the same order they are given to [with_fresh_vars]. *)
let rec with_fresh_vars env sigma (basenames : string list) (tys : EConstr.t list)
    (k : Environ.env -> Evd.evar_map -> Names.Id.t list -> Evd.evar_map * 'a) : Evd.evar_map * 'a =
  match (basenames, tys) with
  | [], [] -> k env sigma []
  | b :: basenames, t :: tys ->
      with_fresh_vars env sigma basenames tys (fun env sigma ids ->
          with_fresh_var env sigma b t @@ fun env sigma id -> k env sigma (id :: ids))
  | _ -> failwith "with_fresh_var: lengths differ"

(** [app f x] is a lightweight notation for [mkApp (f, [| x |])]. *)
let app (f : EConstr.t) (x : EConstr.t) : EConstr.t = EConstr.mkApp (f, [| x |])

(** [apps f xs] is a lightweight notation for [mkApp (f, xs )]. *)
let apps (f : EConstr.t) (xs : EConstr.t array) : EConstr.t = EConstr.mkApp (f, xs)

(** [namedLambda env sigma ?relevance name ty body] makes a lambda abstraction with the given parameters,
    in the locally nameless style. 

    Inside [body], the global environment is augmented with a declaration for the new identifier. *)
let namedLambda env sigma ?(relevance = EConstr.ERelevance.relevant) name ty body :
    Evd.evar_map * EConstr.constr =
  with_fresh_var env sigma name ty @@ fun env sigma id ->
  let sigma, b = body env sigma id in
  (sigma, EConstr.mkNamedLambda sigma { binder_name = id; binder_relevance = relevance } ty b)

(** [namedProd env sigma ?relevance name ty body] makes a dependent with the given parameters,
    in the locally nameless style. *)
let namedProd env sigma ?(relevance = EConstr.ERelevance.relevant) name ty body :
    Evd.evar_map * EConstr.constr =
  with_fresh_var env sigma name ty @@ fun env sigma id ->
  let sigma, b = body env sigma id in
  (sigma, EConstr.mkNamedProd sigma { binder_name = id; binder_relevance = relevance } ty b)

(** Generalizes [namedLambda] to multiple variables in a [EConstr.rel_context]. 

    The body receives the variables in the same order they are stored in the context, 
    i.e. the most recent (= inner-most) variable first. 
*)
let namedLambdaContext env sigma (ctx : EConstr.rel_context)
    (body : Environ.env -> Evd.evar_map -> Names.Id.t list -> Evd.evar_map * EConstr.t) :
    Evd.evar_map * EConstr.t =
  let open EConstr in
  let open Context in
  let open Rel in
  (* Get the names and types of the variables in the context. *)
  let names =
    ctx
    |> List.map @@ fun decl ->
       match Declaration.get_name decl with Name n -> Names.Id.to_string n | Anonymous -> "x"
  in
  let tys = List.map Declaration.get_type ctx in
  with_fresh_vars env sigma names tys @@ fun env sigma ids ->
  (* Build the body. *)
  let sigma, body = body env sigma ids in
  (* Add lambda abstractions. *)
  ( sigma
  , List.fold_left
      (fun body decl ->
        mkLambda
          ( { binder_name = Declaration.get_name decl
            ; binder_relevance = Declaration.get_relevance decl
            }
          , Declaration.get_type decl
          , Vars.subst_vars sigma ids body ))
      body ctx )

(** [namedFix env sigma ?relevance name rec_arg_idx ty body] makes a single fixpoint with the given parameters,
    in the locally nameless style :
    - [name] is the name of the fixpoint parameter.
    - [rec_arg_idx] is the index of the (structurally) recursive argument, starting at [0].
    - [ty] is the type of the fixpoint parameter.
    - [body] is the body of the fixpoint, which has access to the fixpoint parameter.

    For instance to build the fixpoint [fix add (n : nat) (m : nat) {struct_ m} : nat := ...]
    one could use [namedFix env sigma "add" 1 '(nat -> nat -> nat) (fun add -> ...)].
*)
let namedFix env sigma ?(relevance = EConstr.ERelevance.relevant) (name : string)
    (rec_arg_idx : int) (ty : EConstr.types)
    (body : Environ.env -> Evd.evar_map -> Names.Id.t -> Evd.evar_map * EConstr.constr) :
    Evd.evar_map * EConstr.constr =
  with_fresh_var env sigma name ty @@ fun env sigma id ->
  let sigma, body = body env sigma id in
  ( sigma
  , EConstr.mkFix
      ( ([| rec_arg_idx |], 0)
      , ( [| { binder_name = Name id; binder_relevance = relevance } |]
        , [| ty |]
        , [| EConstr.Vars.subst_var sigma id body |] ) ) )

(** [subterm x t] checks whether [x] occurs in [t], modulo alpha equivalence.
      It takes time [O(size(x) * size(t))]. *)
let rec subterm sigma (x : EConstr.t) (t : EConstr.t) : bool =
  EConstr.fold sigma (fun b subt -> b || subterm sigma x subt) (EConstr.eq_constr sigma x t) t

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
    else Some (namedLambda env sigma "x" lp.t @@ fun _ sigma x -> (sigma, EConstr.mkVar x))

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
      namedProd env sigma "a" ta @@ fun env sigma a ->
      namedProd env sigma "b" tb @@ fun env sigma b ->
      ( sigma
      , mkArrowR
          (mkArrowR (mkVar a) (mkVar b))
          (mkArrowR (app type_former @@ mkVar a) (app type_former @@ mkVar b)) )
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
let map_db : Names.GlobRef.t list ref = Summary.ref ~name:"Derivemap_explicit Rule Database" []

(** A small record to hold the parameters of the mapping function while
      we build its body. *)
type params =
  { ind : Names.Ind.t
  ; map : Names.Id.t
  ; a : Names.Id.t
  ; b : Names.Id.t
  ; f : Names.Id.t
  ; _x : Names.Id.t
  }

let build_arg env sigma (p : params) (arg : EConstr.t) (arg_ty : EConstr.t) :
    Evd.evar_map * EConstr.t =
  let open EConstr in
  (* Construct the lifting problem. *)
  let lp =
    Lift.
      { a = mkVar p.a
      ; b = mkVar p.b
      ; f = mkVar p.f
      ; t = arg_ty
      ; u = Vars.replace_vars sigma [ (p.a, mkVar p.b) ] arg_ty
      }
  in
  (* Build a custom rule for [T = Ind A]. *)
  let map_rule : Lift.rule =
   fun env sigma lp ->
    if eq_constr sigma lp.t (apply_ind env p.ind lp.a)
    then Some (sigma, apps (mkVar p.map) [| lp.a; lp.b; lp.f |])
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
  (* Bind the arguments of the constructor. *)
  namedLambdaContext env sigma ca.cs_args @@ fun env sigma args ->
  (* Map the correct function over each argument. *)
  (* We would really want to use something like List.mapM here instead of a recursive function. *)
  let arg_tys = List.map Context.Rel.Declaration.get_type ca.cs_args in
  let rec loop sigma acc args arg_tys =
    match (args, arg_tys) with
    | [], [] -> (sigma, acc)
    | arg :: args, ty :: arg_tys ->
        let sigma, new_arg = build_arg env sigma p arg ty in
        loop sigma (new_arg :: acc) args arg_tys
    | _ -> Log.error "build_branch : length mismatch"
  in
  let sigma, mapped_args = loop sigma [] (List.map mkVar args) arg_tys in
  (* Apply the constructor to the arguments. *)
  (sigma, mkApp (mkConstructU cb.cs_cstr, Array.of_list (mkVar p.b :: mapped_args)))

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
    namedProd env sigma "a" ta @@ fun env sigma a ->
    namedProd env sigma "b" tb @@ fun env sigma b ->
    ( sigma
    , mkArrowR
        (mkArrowR (mkVar a) (mkVar b))
        (mkArrowR (apply_ind env ind @@ mkVar a) (apply_ind env ind @@ mkVar b)) )
  in
  (* Abstract over the input variables. *)
  namedFix env sigma "map" 3 map_ty @@ fun env sigma map ->
  namedLambda env sigma "a" ta @@ fun env sigma a ->
  namedLambda env sigma "b" tb @@ fun env sigma b ->
  namedLambda env sigma "f" (mkArrowR (mkVar a) (mkVar b)) @@ fun env sigma f ->
  namedLambda env sigma "x" (apply_ind env ind @@ mkVar a) @@ fun env sigma x ->
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
        let sigma, branch = build_branch env sigma { ind; map; a; b; f; _x = x } ca cb in
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
  (* TODO : ensure it is fresh. *)
  let name = basename in
  (*let name = (*Namegen.next_global_ident_away basename @@ Environ *) in*)
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
