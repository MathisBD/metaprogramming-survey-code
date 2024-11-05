(** [mk_kername path label] makes the kernel name with directory path [path] and label [label]. 
    For instance to create the kernel name of [Nat.add] you can use 
    [mk_kername ["Coq"; "Init"; "Nat"] "add"]. *)
let mk_kername (dir : string list) (label : string) : Names.KerName.t =
  let dir = Names.ModPath.MPfile (Names.DirPath.make @@ List.rev_map Names.Id.of_string_soft dir) in
  let label = Names.Label.make label in
  Names.KerName.make dir label

(** [fresh_type sigma] creates a [Type] term with a fresh universe level, 
    and adds the new universe level to the evar map. *)
let fresh_type sigma : Evd.evar_map * EConstr.t =
  let level = UnivGen.fresh_level () in
  let sigma = Evd.add_global_univ sigma level in
  (sigma, EConstr.mkType @@ Univ.Universe.make level)

(** [fresh_evar env sigma ty] creates a fresh evar with type [ty] (if provided).
    If [ty] is not provided, it creates another fresh evar (of type [Type]) for the type. *)
let fresh_evar env sigma (ty : EConstr.t option) : Evd.evar_map * EConstr.t =
  match ty with
  | Some ty -> Evarutil.new_evar env sigma ty
  | None ->
      let sigma, t = fresh_type sigma in
      let sigma, ty = Evarutil.new_evar env sigma t in
      Evarutil.new_evar env sigma ty

(** [replace_rel sigma a b t] replaces [Rel a] with [Rel b] in [t]. *)
let rec replace_rel sigma (a : int) (b : int) (t : EConstr.t) : EConstr.t =
  if EConstr.isRelN sigma a t
  then EConstr.mkRel b
  else EConstr.map_with_binders sigma (( + ) 1) (replace_rel sigma a) b t

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

(** [letin env sigma name def ty body] builds a local let-binding.
    The [body] has access to the environment extended with a local definition for the bound variable. *)
let letin env sigma (name : string) (def : EConstr.t) (ty : EConstr.t)
    (body : Environ.env -> Evd.evar_map * EConstr.t) : Evd.evar_map * EConstr.t =
  let open EConstr in
  let binder_name = Names.Name (Names.Id.of_string_soft name) in
  let inner_env =
    Environ.push_rel
      (LocalDef
         ( { binder_name; binder_relevance = Sorts.Relevant }
         , EConstr.to_constr sigma def
         , EConstr.to_constr sigma ty ))
      env
  in
  let sigma, body = body inner_env in
  (sigma, mkLetIn ({ binder_name; binder_relevance = ERelevance.relevant }, def, ty, body))

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
