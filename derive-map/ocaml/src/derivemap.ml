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
(** Manipulating terms. *)
(**************************************************************************************)

(** [kername path name] creates the kernel name with given [path] and [name]. 
    For instance [kername ["Coq" ; "Init" ; "Datatypes"] "nat"] creates the kernel name of the inductive [nat]. *)
let kername (path : string list) (name : string) =
  let open Names in
  let dir = DirPath.make (path |> List.rev |> List.map Id.of_string) in
  KerName.make (ModPath.MPfile dir) (Label.make name)

(** [fresh_type ()] creates a [Type] term with a fresh universe level, 
    and adds the new universe level to the global evar state. *)
let fresh_type () : EConstr.t =
  let level = UnivGen.fresh_level () in
  global_evd := Evd.add_global_univ !global_evd level;
  EConstr.mkType @@ Univ.Universe.make level

(** [fresh_evar ?ty] creates a fresh existential variable with type [ty], 
    and adds it to the global evar state. 
    
    If [ty] is omitted the evar will have type [Type u] for [u] a fresh universe level. *)
let fresh_evar ?(ty : EConstr.t option) () : EConstr.t =
  (* Choose a type for the evar. *)
  let ty = match ty with Some ty -> ty | None -> fresh_type () in
  (* Generate the new evar while updating the evar state. *)
  let new_evd, evar = Evarutil.new_evar (Global.env ()) !global_evd ty in
  global_evd := new_evd;
  evar

(** [unify t u] tries to unify [t] with [u] :
    - If it succeeds it returns [true] and updates the global evar state. 
    - If it fails it returnts [false] and does *not* update the global evar state. *)
let unify (t : EConstr.t) (u : EConstr.t) : bool =
  global_evd := Unification.w_unify (Global.env ()) !global_evd Conversion.CONV t u;
  true

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

(** [namedProd ?relevance name ty body] makes a dependent with the given parameters,
    in the locally nameless style. *)
let namedProd ?(relevance = EConstr.ERelevance.relevant) (name : string) (ty : EConstr.types)
    (body : Names.Id.t -> EConstr.constr) : EConstr.constr =
  let id = fresh_ident name in
  EConstr.mkNamedProd !global_evd { binder_name = id; binder_relevance = relevance } ty (body id)

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

(** [namedFix ?relevance name rec_arg_idx ty body] makes a single fixpoint with the given parameters,
    in the locally nameless style :
    - [name] is the name of the fixpoint parameter.
    - [rec_arg_idx] is the index of the (structurally) recursive argument, starting at [0].
    - [ty] is the type of the fixpoint parameter.
    - [body] is the body of the fixpoint, which has access to the fixpoint parameter.

    For instance to build the fixpoint [fix add (n : nat) (m : nat) {struct_ m} : nat := ...]
    one could use [namedFix "add" 1 '(nat -> nat -> nat) (fun add -> ...)].
*)
let namedFix ?(relevance = EConstr.ERelevance.relevant) (name : string) (rec_arg_idx : int)
    (ty : EConstr.types) (body : Names.Id.t -> EConstr.constr) : EConstr.constr =
  let id = fresh_ident name in
  EConstr.mkFix
    ( ([| rec_arg_idx |], 0)
    , ( [| { binder_name = Name id; binder_relevance = relevance } |]
      , [| ty |]
      , [| EConstr.Vars.subst_var !global_evd id @@ body id |] ) )

(** [subterm x t] checks whether [x] occurs in [t], modulo alpha equivalence. 
    It takes time [O(size(x) * size(t))]. *)
let rec subterm (x : EConstr.t) (t : EConstr.t) : bool =
  EConstr.fold !global_evd (fun b subt -> b || subterm x subt) (EConstr.eq_constr !global_evd x t) t

(* Helper function to apply the inductive to a single parameter. *)
let apply_ind (ind : Names.Ind.t) (t : EConstr.t) : EConstr.t =
  let (_, inst), _ = UnivGen.fresh_inductive_instance (Global.env ()) ind in
  EConstr.mkApp (EConstr.mkIndU (ind, EConstr.EInstance.make inst), [| t |])

(**************************************************************************************)
(** Derive Map. *)
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
  type rule = problem -> EConstr.t option

  (** Basic lifting rule when [T] = [A]. 
      In this case we solve with [f' = f] *)
  let apply_rule : rule =
   fun lp ->
    Log.printf "LIFT APPLY on %s" (Log.show_econstr !global_evd lp.t);
    if EConstr.eq_constr !global_evd lp.a lp.t
    then (
      Log.printf "SUCCESS";
      Some lp.f)
    else (
      Log.printf "FAIL";
      None)

  (** Basic lifting rule when [A] does not occur in [T].
      In this case we solve with [f' x = x]. *)
  let id_rule : rule =
   fun lp ->
    Log.printf "LIFT ID on %s" (Log.show_econstr !global_evd lp.t);
    if subterm lp.a lp.t
    then (
      Log.printf "FAIL";
      None)
    else (
      Log.printf "SUCCESS";
      Some (namedLambda "x" lp.t @@ fun x -> EConstr.mkVar x))

  (** [mzero] is a lifting rule which always fails. *)
  let mzero : rule = fun _ -> None

  (** [msum r1 r2] tries the rule [r1], and if it fails applies [r2]. *)
  let msum (r1 : rule) (r2 : rule) : rule =
   fun lp -> match r1 lp with None -> r2 lp | Some f' -> Some f'

  (** [sequence rs] combines the lifting rules [rs] by trying them out in order from first to last
      until one succeeds. *)
  let sequence (rs : rule list) : rule =
    match rs with [] -> mzero | r :: rs -> List.fold_left msum r rs

  (** Fixpoints for rules. Using [let-rec] manually might trigger infinite recursion : 
      one has to take care of eta-expanding the definition (as is done in [fix]). *)
  let rec fix (f : rule -> rule) : rule = fun lp -> f (fix f) lp

  (** An example rule for lists. *)
  let list_rule (rec_rule : rule) : rule =
   fun lp ->
    let open EConstr in
    Log.printf "RULE LIST on %s" (Log.show_econstr !global_evd lp.t);
    (* Create unification variables ?alpha and ?beta. *)
    let alpha = fresh_evar () in
    let beta = fresh_evar () in
    Log.printf "created alpha and beta";
    Log.printf "alpha=%s\nbeta=%s"
      (Log.show_econstr !global_evd alpha)
      (Log.show_econstr !global_evd beta);
    (*Evd.fold (fun ev ev_info _ -> Log.printf "EVAR %s" ev_info.) !global_evd ();*)
    (* Unify [T =?= list ?alpha] and [U = list ?beta]. *)
    let list_ind = (Names.MutInd.make1 @@ kername [ "Coq"; "Init"; "Datatypes" ] "list", 1) in
    let pat = apply_ind list_ind alpha in
    Log.printf "made pat";
    let b1 = unify lp.t pat in
    Log.printf "unify b1=%b" b1;
    let b2 = unify lp.u (apply_ind list_ind beta) in
    if b1 && b2
    then (
      (* Recurse to lift [f : A -> B] to [f' : alpha -> beta]. *)
      Log.printf "RECURSING on %s" (Log.show_econstr !global_evd alpha);
      match rec_rule lp with
      | None ->
          Log.printf "FAIL";
          None
      | Some f' ->
          Log.printf "SUCCESS";
          let (list_map, map_inst), _ =
            UnivGen.fresh_constant_instance (Global.env ())
            @@ Names.Constant.make1
            @@ kername [ "Coq"; "Lists"; "List" ] "map"
          in
          Some (mkApp (mkConstU (list_map, EInstance.make map_inst), [| alpha; beta; f' |])))
    else (
      Log.printf "FAIL";
      None)
end

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

let build_arg (p : params) (arg : EConstr.t) (arg_ty : EConstr.t) : EConstr.t =
  let open EConstr in
  (* Construct the lifting problem. *)
  let lp =
    Lift.
      { a = mkVar p.a
      ; b = mkVar p.b
      ; f = mkVar p.f
      ; t = arg_ty
      ; u = Vars.replace_vars !global_evd [ (p.a, mkVar p.b) ] arg_ty
      }
  in
  (* Build a custom rule for [T = Ind A]. *)
  let map_rule : Lift.rule =
   fun lp ->
    if eq_constr !global_evd lp.t (apply_ind p.ind lp.a)
    then Some (mkApp (mkVar p.map, [| lp.a; lp.b; lp.f |]))
    else None
  in
  (* Build the rule we will use to solve our lifting problem. *)
  let rule =
    let open Lift in
    fix @@ fun rec_rule -> sequence [ apply_rule; id_rule; map_rule; list_rule rec_rule ]
  in
  (* Solve the lifting problem. *)
  match rule lp with
  | Some f' -> mkApp (f', [| arg |])
  | None ->
      Log.error "Failed to lift mapping function of type [%s -> %s] on argument of type [%s]"
        (Log.show_econstr !global_evd lp.a)
        (Log.show_econstr !global_evd lp.b)
        (Log.show_econstr !global_evd lp.t)

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
  (* Helper function to get the array of [constructor_summary] for a given parameter value [x]. *)
  let constructors x : Inductiveops.constructor_summary array =
    let (_, inst), _ = UnivGen.fresh_inductive_instance (Global.env ()) ind in
    Inductiveops.make_ind_family ((ind, EInstance.make inst), [ x ])
    |> Inductiveops.get_constructors (Global.env ())
  in
  (* Make the type of the recursive mapping function. *)
  let map_ty =
    namedProd "a" (fresh_type ()) @@ fun a ->
    namedProd "b" (fresh_type ()) @@ fun b ->
    mkArrowR
      (mkArrowR (mkVar a) (mkVar b))
      (mkArrowR (apply_ind ind @@ mkVar a) (apply_ind ind @@ mkVar b))
  in
  (* Abstract over the input variables. *)
  namedFix "map" 3 map_ty @@ fun map ->
  namedLambda "a" (fresh_type ()) @@ fun a ->
  namedLambda "b" (fresh_type ()) @@ fun b ->
  namedLambda "f" (mkArrowR (mkVar a) (mkVar b)) @@ fun f ->
  namedLambda "x" (apply_ind ind @@ mkVar a) @@ fun x ->
  (* Construct the case return clause. *)
  let case_return =
    namedLambda "_" (apply_ind ind @@ mkVar a) @@ fun _ -> apply_ind ind @@ mkVar b
  in
  (* Construct the case branches. *)
  let branches =
    Array.map2
      (build_branch { ind; map; a; b; f; _x = x })
      (constructors @@ mkVar a)
      (constructors @@ mkVar b)
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
  Log.printf "The mapping function :\n%s" (Log.show_econstr !global_evd func);
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
  Log.printf "RET %s" @@ Log.show_econstr !global_evd ret;
  Array.iter (fun (_, b) -> Log.printf "BRANCH %s" @@ Log.show_econstr !global_evd b) branches
