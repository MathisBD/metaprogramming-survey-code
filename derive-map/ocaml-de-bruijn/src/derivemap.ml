(**************************************************************************************)
(** Globals. *)
(**************************************************************************************)

(** Since we are in a command, there is no default evar map to grab from the proof state.
    Instead we create our own evar map (from the global environment) whenever the DeriveMap command
    is called, and store it in this global reference.

    This seems quite reasonable.
*)
let global_evd : Evd.evar_map ref = ref Evd.empty

(**************************************************************************************)
(** Manipulating terms. *)
(**************************************************************************************)

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

(** [unify sigma t u] tries to unify [t] with [u] in the global evar map :
    - If it succeeds it returns [true] and updates the global evar map. 
    - If it fails it returns [false]. *)
let unify (t : EConstr.t) (u : EConstr.t) : bool =
  try
    global_evd := Unification.w_unify (Global.env ()) !global_evd Conversion.CONV t u;
    true
  with _ -> false

(** [app f x] is a lightweight notation for [mkApp (f, [| x |])]. *)
let app (f : EConstr.t) (x : EConstr.t) : EConstr.t = EConstr.mkApp (f, [| x |])

(** [apps f xs] is a lightweight notation for [mkApp (f, xs )]. *)
let apps (f : EConstr.t) (xs : EConstr.t array) : EConstr.t = EConstr.mkApp (f, xs)

(** [arr t1 t2] makes the non-dependent arrow [t1 -> t2].
    It takes care of lifting the de Bruijn indices in [t2] by [1]. *)
let arr (t1 : EConstr.t) (t2 : EConstr.t) : EConstr.t = EConstr.mkArrowR t1 (EConstr.Vars.lift 1 t2)

let prod (name : string) (ty : EConstr.t) (body : EConstr.t) : EConstr.t =
  EConstr.mkProd
    ( { binder_name = Name (Names.Id.of_string_soft name)
      ; binder_relevance = EConstr.ERelevance.relevant
      }
    , ty
    , body )

let lambda (name : string) (ty : EConstr.t) (body : EConstr.t) : EConstr.t =
  EConstr.mkLambda
    ( { binder_name = Name (Names.Id.of_string_soft name)
      ; binder_relevance = EConstr.ERelevance.relevant
      }
    , ty
    , body )

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

  (** [detruct_map f] checks that [f] is a mapping function i.e. has type [forall (A B : Type), (A -> B) -> T A -> T B]
      and returns [Some T] if it succeeds or [None] if it fails. *)
  (*let destruct_map (map_func : EConstr.t) : EConstr.t option =
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
              None)*)
end

(**************************************************************************************)
(** AddMap and DeriveMap commands. *)
(**************************************************************************************)

(** We store some mapping rules in a database :
    - AddMap adds rules to the database. 
    - DeriveMap uses the rules in the database.   
*)
(*let map_db : EConstr.t list ref = Summary.ref ~name:"DeriveMap Rule Database" []*)

(** A small record to hold the parameters (as de Bruijn indices) of the mapping function while 
    we build its body. *)
type params = { ind : Names.Ind.t; map : int; a : int; b : int; f : int; x : int }

let build_arg (p : params) (n : int) (arg : int) (arg_ty : EConstr.t) : EConstr.t =
  let open EConstr in
  (* Construct the lifting problem. *)
  let lp =
    Lift.{ a = mkRel (p.a + n); b = mkRel (p.b + n); f = mkRel (p.f + n); t = arg_ty; u = arg_ty }
  in
  (* Build a custom rule for [T = Ind A]. *)
  (*let map_rule : Lift.rule =
     fun lp ->
      if eq_constr !global_evd lp.t (apply_ind p.ind lp.a)
      then Some (mkApp (mkVar p.map, [| lp.a; lp.b; lp.f |]))
      else None
    in*)
  (* Build the rule we will use to solve our lifting problem.
     We use the rules in the database in addition to [map_rule]. *)
  (*let rule =
      let open Lift in
      fix @@ fun rec_rule ->
      sequence (apply_rule :: id_rule :: map_rule :: List.map (custom_rule rec_rule) !map_db)
    in*)
  let rule = Lift.sequence [ Lift.apply_rule; Lift.id_rule ] in
  (* Solve the lifting problem. *)
  match rule lp with
  | Some f' -> app f' (mkRel arg)
  | None ->
      Log.error
        "Failed to lift mapping function of type [Rel %s -> Rel %s] on argument of type [%s]"
        (Log.show_econstr !global_evd (n + lp.a))
        (Log.show_econstr !global_evd (n + lp.b))
        (Log.show_econstr !global_evd lp.t)

let build_branch (p : params) (ca : Inductiveops.constructor_summary)
    (cb : Inductiveops.constructor_summary) : EConstr.t =
  let open EConstr in
  (* Map the correct function over each argument. *)
  let n = List.length ca.cs_args in
  let arg_tys = List.map Context.Rel.Declaration.get_type ca.cs_args in
  let mapped_args = List.mapi (fun i ty -> build_arg p n (i + 1) ty) arg_tys in
  (* Apply the constructor to the arguments. *)
  let body =
    mkApp (mkConstructU cb.cs_cstr, Array.of_list (mkRel (n + p.b) :: List.rev mapped_args))
  in
  (* Bind the arguments of the constructor. *)
  List.fold_left
    (fun body decl ->
      let open Context.Rel.Declaration in
      mkLambda
        ({ binder_name = get_name decl; binder_relevance = get_relevance decl }, get_type decl, body))
    body ca.cs_args

let build_map (ind : Names.inductive) : EConstr.t =
  let open EConstr in
  (* Helper function to get the array of [constructor_summary] for a given parameter value [x]. *)
  let constructors x : Inductiveops.constructor_summary array =
    let (_, inst), _ = UnivGen.fresh_inductive_instance (Global.env ()) ind in
    Inductiveops.make_ind_family ((ind, EInstance.make inst), [ x ])
    |> Inductiveops.get_constructors (Global.env ())
  in
  (* Make the type of the recursive mapping function. *)
  (*let map_ty =
      prod "a" (fresh_type ())
      @@ prod "b" (fresh_type ())
      @@ arr (arr (mkRel 2) (mkRel 1)) (arr (apply_ind ind @@ mkRel 2) (apply_ind ind @@ mkRel 1))
    in*)
  (* Abstract over the input variables. *)
  (*fix "map" 3 map_ty @@ fun map ->*)
  lambda "a" (fresh_type ())
  @@ lambda "b" (fresh_type ())
  @@ lambda "f" (arr (mkRel 2) (mkRel 1))
  @@ lambda "x" (apply_ind ind @@ mkRel 3)
  @@
  let p = { ind; map = 5; a = 4; b = 3; f = 2; x = 1 } in
  (* Construct the case return clause. *)
  let case_return = lambda "_" (apply_ind ind @@ mkRel p.a) @@ apply_ind ind @@ mkRel (p.b + 1) in
  (* Construct the case branches. *)
  let branches =
    Array.map2 (build_branch p) (constructors @@ mkRel p.a) (constructors @@ mkRel p.b)
  in
  (* Finally construct the case expression. *)
  Inductiveops.simple_make_case_or_project (Global.env ()) !global_evd
    (Inductiveops.make_case_info (Global.env ()) ind Constr.RegularStyle)
    (case_return, ERelevance.relevant)
    Constr.NoInvert (mkRel p.x) branches

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
let add (_map_func : Constrexpr.constr_expr) : unit = ()
(* Create the evar map. *)
(*global_evd := Evd.from_env @@ Global.env ();
  (* Internalize the function. *)
  let evd, map_func = Constrintern.interp_constr_evars (Global.env ()) !global_evd map_func in
  global_evd := evd;
  (* Check it is indeed a mapping function (so that we can fail now instead of in DeriveMap). *)
  match Lift.destruct_map map_func with
  | None -> Log.error "Provided function is not a mapping function."
  | Some _ ->
      (* Add the function to the map database. *)
      map_db := map_func :: !map_db*)
