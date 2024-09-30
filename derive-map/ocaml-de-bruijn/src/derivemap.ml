(** In this file I try out a "locally nameless" style of programming, 
    by (ab)using the [Var] constructor of terms instead of using de Bruijn indices
    with the [Rel] constructor. 
*)

(**************************************************************************************)
(** Globals. *)
(**************************************************************************************)

(** Since we are in a command, there is no default evar map to grab from the proof state.
    Instead we create our own evar map (from the global environment) whenever the DeriveMap command
    is called, and store it in this global reference.

    This seems perfectly reasonable.
*)
let global_evd : Evd.evar_map ref = ref Evd.empty

(** To support the locally nameless style of programming, we need to store the types of 
    the named variables introduced so far. Since we are not in a proof and we obviously do not wish
    to use section variables for this purpose, we cannot simply store this information in the global
    environment (or at least I did not find how to do it). Instead we use a global [Context.Named.pt]
    that we pass explicitly to the functions where it matters. 
    
    This is very hacky.
*)
let global_ctx : (Constr.constr, Constr.types, Sorts.relevance) Context.Named.pt ref =
  ref Context.Named.empty

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

(** [unify sigma t u] tries to unify [t] with [u] in evar map [sigma] :
    - If it succeeds it returns [true] and updates the global evar map. 
    - If it fails it returns [false]. *)
let unify (t : EConstr.t) (u : EConstr.t) : bool =
  try
    (* Don't forget : we do unification in a custom named context. *)
    let env = Environ.push_named_context !global_ctx (Global.env ()) in
    global_evd := Unification.w_unify env !global_evd Conversion.CONV t u;
    true
  with _ -> false

(** [fresh_ident basename] returns a fresh identifier built from [basename] 
    and which is guaranteed to be distinct from all identifiers returned by this function so far. *)
let fresh_ident : string -> Names.Id.t =
  let used_names = ref Names.Id.Set.empty in
  fun basename ->
    let name = Namegen.next_ident_away (Names.Id.of_string_soft basename) !used_names in
    used_names := Names.Id.Set.add name !used_names;
    name

(** [with_fresh_var basename ty k] generates a fresh identifier built from [basename], 
    adds a corresponding declaration to [global_ctx] and executes the continuation [k]
    in this augmented context. The declaration is removed when this function returns. *)
let with_fresh_var (basename : string) (ty : EConstr.t) (k : Names.Id.t -> 'a) : 'a =
  let id = fresh_ident basename in
  global_ctx :=
    LocalAssum
      ({ binder_name = id; binder_relevance = Sorts.Relevant }, EConstr.to_constr !global_evd ty)
    :: !global_ctx;
  let res = k id in
  (global_ctx := match !global_ctx with [] -> [] | _ :: ctx -> ctx);
  res

(** Generalizes [with_fresh_var] to several variables. The last variables in the list 
    are introduced first in the context. 
    
    The continuation receives the variables in the same order they are given to [with_fresh_vars]. *)
let rec with_fresh_vars (basenames : string list) (tys : EConstr.t list) (k : Names.Id.t list -> 'a)
    : 'a =
  match (basenames, tys) with
  | [], [] -> k []
  | b :: basenames, t :: tys ->
      with_fresh_vars basenames tys (fun ids -> with_fresh_var b t @@ fun id -> k (id :: ids))
  | _ -> failwith "with_fresh_var: lengths differ"

(** [app f x] is a lightweight notation for [mkApp (f, [| x |])]. *)
let app (f : EConstr.t) (x : EConstr.t) : EConstr.t = EConstr.mkApp (f, [| x |])

(** [apps f xs] is a lightweight notation for [mkApp (f, xs )]. *)
let apps (f : EConstr.t) (xs : EConstr.t array) : EConstr.t = EConstr.mkApp (f, xs)

(** [namedLambda ?relevance name ty body] makes a lambda abstraction with the given parameters,
    in the locally nameless style. 

    Inside [body], the global context is augmented with a declaration for the new identifier. *)
let namedLambda ?(relevance = EConstr.ERelevance.relevant) (name : string) (ty : EConstr.types)
    (body : Names.Id.t -> EConstr.constr) : EConstr.constr =
  with_fresh_var name ty @@ fun id ->
  EConstr.mkNamedLambda !global_evd { binder_name = id; binder_relevance = relevance } ty (body id)

(** [namedProd ?relevance name ty body] makes a dependent with the given parameters,
    in the locally nameless style. *)
let namedProd ?(relevance = EConstr.ERelevance.relevant) (name : string) (ty : EConstr.types)
    (body : Names.Id.t -> EConstr.constr) : EConstr.constr =
  with_fresh_var name ty @@ fun id ->
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
  (* Get the names and types of the variables in the context. *)
  let names =
    ctx
    |> List.map @@ fun decl ->
       match Declaration.get_name decl with Name n -> Names.Id.to_string n | Anonymous -> "x"
  in
  let tys = List.map Declaration.get_type ctx in
  with_fresh_vars names tys @@ fun ids ->
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
  with_fresh_var name ty @@ fun id ->
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
  type rule = problem -> EConstr.t option

  (** Basic lifting rule when [T] = [A]. 
      In this case we solve with [f' = f] *)
  let apply_rule : rule =
   fun lp ->
    Log.printf "LIFT APPLY on %s" (Log.show_econstr !global_evd lp.t);
    if unify lp.a lp.t
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
  (*let list_rule (rec_rule : rule) : rule =
    fun lp ->
     let open EConstr in
     Log.printf "RULE LIST on %s" (Log.show_econstr !global_evd lp.t);
     (* Create a unification variable ?alpha which takes lp.a as a parameter. *)
     let alpha = fresh_evar ~ty:(mkArrowR (fresh_type ()) (fresh_type ())) () in
     (* Unify [T =?= list (?alpha A)] and [U =?= list (?alpha B)]. *)
     let list_ind = (Names.MutInd.make1 @@ kername [ "Coq"; "Init"; "Datatypes" ] "list", 0) in
     let b1 = unify lp.t (apply_ind list_ind @@ app alpha lp.a ) in
     let b2 = unify lp.u (apply_ind list_ind @@ app alpha lp.b ) in
     if b1 && b2
     then (
       (* Recurse to lift [f : A -> B] to [f' : alpha -> beta]. *)
       Log.printf "RECURSING on %s" (Log.show_econstr !global_evd @@ app alpha lp.a ));
       match rec_rule { lp with t = app alpha lp.a ; u = app alpha lp.b  } with
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
           Some
             (app
                ( mkConstU (list_map, EInstance.make map_inst)
                , [| mkApp (alpha, [| lp.a |]); mkApp (alpha, [| lp.b |]); f' |] )))
     else (
       Log.printf "FAIL";
       None)*)

  (** [detruct_map f] checks that [f] is a mapping function i.e. has type [forall (A B : Type), (A -> B) -> T A -> T B]
      and returns [Some T] if it succeeds or [None] if it fails. *)
  let destruct_map (map_func : EConstr.t) : EConstr.t option =
    let open EConstr in
    let t = fresh_evar ~ty:(mkArrowR (fresh_type ()) (fresh_type ())) () in
    let pat =
      namedProd "a" (fresh_type ()) @@ fun a ->
      namedProd "b" (fresh_type ()) @@ fun b ->
      mkArrowR (mkArrowR (mkVar a) (mkVar b)) (mkArrowR (app t @@ mkVar a) (app t @@ mkVar b))
    in
    let map_ty = Retyping.get_type_of (Global.env ()) !global_evd map_func in
    let success = unify pat map_ty in
    if success then Some t else None

  let custom_rule (rec_rule : rule) (map_func : EConstr.t) : rule =
    (* Extract the type former. *)
    match destruct_map map_func with
    | None -> Log.error "Lift.custom_rule : error"
    | Some type_former ->
        fun lp ->
          Log.printf "RULE %s on %s"
            (Log.show_econstr !global_evd type_former)
            (Log.show_econstr !global_evd lp.t);
          (* Create a unification variable ?alpha which takes lp.a as a parameter. *)
          let alpha = fresh_evar ~ty:(EConstr.mkArrowR (fresh_type ()) (fresh_type ())) () in
          (* Unify [T =?= type_former (?alpha A)] and [U =?= type_former (?alpha B)]. *)
          let b1 = unify lp.t (app type_former @@ app alpha lp.a) in
          let b2 = unify lp.u (app type_former @@ app alpha lp.b) in
          if b1 && b2
          then begin
            (* Recurse to lift [f : A -> B] to [f' : alpha A -> alpha B]. *)
            Log.printf "RECURSING on %s" (Log.show_econstr !global_evd @@ app alpha lp.a);
            match rec_rule { lp with t = app alpha lp.a; u = app alpha lp.b } with
            | None ->
                Log.printf "FAIL";
                None
            | Some f' ->
                Log.printf "SUCCESS";
                Some (apps map_func [| app alpha lp.a; app alpha lp.b; f' |])
          end
          else (
            Log.printf "FAIL";
            None)
end

(**************************************************************************************)
(** AddMap and DeriveMap commands. *)
(**************************************************************************************)

(** We store some mapping rules in a database :
    - AddMap adds rules to the database. 
    - DeriveMap uses the rules in the database.   
*)
let map_db : EConstr.t list ref = Summary.ref ~name:"DeriveMap Rule Database" []

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
  (* Build the rule we will use to solve our lifting problem.
     We use the rules in the database in addition to [map_rule]. *)
  let rule =
    let open Lift in
    fix @@ fun rec_rule ->
    sequence (apply_rule :: id_rule :: map_rule :: List.map (custom_rule rec_rule) !map_db)
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
  let evd, ty = Typing.type_of (Global.env ()) !global_evd func in
  global_evd := evd;
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
       ~opaque:false ~body:func !global_evd

(** [AddMap] command entry point. *)
let add (map_func : Constrexpr.constr_expr) : unit =
  (* Create the evar map. *)
  global_evd := Evd.from_env @@ Global.env ();
  (* Internalize the function. *)
  let evd, map_func = Constrintern.interp_constr_evars (Global.env ()) !global_evd map_func in
  global_evd := evd;
  (* Check it is indeed a mapping function (so that we can fail now instead of in DeriveMap). *)
  match Lift.destruct_map map_func with
  | None -> Log.error "Provided function is not a mapping function."
  | Some _ ->
      (* Add the function to the map database. *)
      map_db := map_func :: !map_db
