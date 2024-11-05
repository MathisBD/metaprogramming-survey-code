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

(** [var_noccur sigma x t] checks if [x] does _not_ occur in [t]. *)
let rec var_noccur (sigma : Evd.evar_map) (x : Names.Id.t) (t : EConstr.t) : bool =
  if EConstr.isVarId sigma x t
  then false
  else EConstr.fold sigma (fun b sub_t -> b && var_noccur sigma x sub_t) true t

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

(** [letiIn env sigma name def ty body] builds a local let-binding.
    The [body] has access to the environment extended with a local definition for the bound variable. *)
let letIn env sigma (name : string) (def : EConstr.t) (ty : EConstr.t)
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

(** [fresh_ident basename] returns a fresh identifier built from [basename] 
    and which is guaranteed to be distinct from all identifiers returned by this function so far. *)
let fresh_ident : string -> Names.Id.t =
  let used_names = ref Names.Id.Set.empty in
  fun basename ->
    let name = Namegen.next_ident_away (Names.Id.of_string_soft basename) !used_names in
    used_names := Names.Id.Set.add name !used_names;
    name

(** [with_fresh_var env sigma basename ?def ty k] generates a fresh identifier built from [basename], 
    adds a corresponding declaration to [env] and executes the continuation [k]
    in this augmented environment. *)
let with_fresh_var env sigma (basename : string) ?(def : EConstr.t option) (ty : EConstr.t)
    (k : Environ.env -> Evd.evar_map -> Names.Id.t -> 'a) : 'a =
  let id = fresh_ident basename in
  let decl =
    match def with
    | None ->
        Context.Named.Declaration.LocalAssum
          ({ binder_name = id; binder_relevance = Sorts.Relevant }, EConstr.to_constr sigma ty)
    | Some def ->
        Context.Named.Declaration.LocalDef
          ( { binder_name = id; binder_relevance = Sorts.Relevant }
          , EConstr.to_constr sigma def
          , EConstr.to_constr sigma ty )
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

(** [namedLambda env sigma name ty body] makes a lambda abstraction with the given parameters,
    in the locally nameless style. 

    Inside [body], the global environment is augmented with a declaration for the new identifier. *)
let namedLambda env sigma name ty body : Evd.evar_map * EConstr.constr =
  with_fresh_var env sigma name ty @@ fun env sigma id ->
  let sigma, b = body env sigma id in
  ( sigma
  , EConstr.mkNamedLambda sigma
      { binder_name = id; binder_relevance = EConstr.ERelevance.relevant }
      ty b )

(** [namedProd env sigma name ty body] makes a dependent product with the given parameters,
in the locally nameless style. *)
let namedProd env sigma name ty body : Evd.evar_map * EConstr.constr =
  with_fresh_var env sigma name ty @@ fun env sigma id ->
  let sigma, b = body env sigma id in
  ( sigma
  , EConstr.mkNamedProd sigma
      { binder_name = id; binder_relevance = EConstr.ERelevance.relevant }
      ty b )

(** [namedLetIn env sigma name def ty body] makes a local let-binding with the given parameters,
    in the locally nameless style. *)
let namedLetIn env sigma name def ty body : Evd.evar_map * EConstr.constr =
  with_fresh_var env sigma name ~def ty @@ fun env sigma id ->
  let sigma, b = body env sigma id in
  ( sigma
  , EConstr.mkNamedLetIn sigma
      { binder_name = id; binder_relevance = EConstr.ERelevance.relevant }
      def ty b )

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
one could use [namedFix env sigma "add" 1 '(nat -> nat -> nat) (fun env sigma add -> ...)].
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
