From MetaCoq.Template Require Import All.

(** [iterate n f x] applies [f] [n] times to [x]. *)
Fixpoint iterate {A}  (n : nat) (f : A -> A) (x : A) : A :=
  match n with 
  | 0 => x
  | S n => iterate n f (f x)
  end.

(*******************************************************************************)
(** Open recursors on terms (which should be part of MetaCoq). *)
(*******************************************************************************)

Definition map_def (f : term -> term) (d : def term) : def term :=
  {| dname := d.(dname) ; dtype := f d.(dtype) ; dbody := f d.(dbody) ; rarg := d.(rarg) |}.

Definition map_predicate (f : term -> term) (p : predicate term) : predicate term :=
  {| puinst := p.(puinst) 
  ;  pparams := List.map f p.(pparams) 
  ;  pcontext := p.(pcontext)
  ;  preturn := f p.(preturn) |}.

Definition map_branch (f : term -> term) (b : branch term) : branch term := 
  {| bcontext := b.(bcontext) ; bbody := f b.(bbody) |}.

(** [map_term f t] maps [f] on the immediate subterms of [t].
    It is not recursive and the order with which subterms are processed is not specified. *)
Definition map_term (f : term -> term) (t : term) : term := 
  match t with
  | tRel _ | tVar _ | tSort _ | tConst _ _ | tInd _ _ | tConstruct _ _ _ | tInt _ | tFloat _ | tString _ => t
  | tEvar n ts => tEvar n (List.map f ts)
  | tCast b k t => tCast (f b) k (f t)
  | tProd name ty body => tProd name (f ty) (f body)
  | tLambda name ty body => tLambda name (f ty) (f body)
  | tLetIn name def ty body => tLetIn name (f def) (f ty) (f body)
  | tApp func args => tApp (f func) (List.map f args)
  | tProj proj t => tProj proj (f t)
  | tFix defs i => tFix (List.map (map_def f) defs) i
  | tCoFix defs i => tCoFix (List.map (map_def f) defs) i
  | tCase ci pred x branches => tCase ci (map_predicate f pred) (f x) (List.map (map_branch f) branches)
  | tArray l t def ty => tArray l (List.map f t) (f def) (f ty)
  end.

Definition map_predicate_with_binders {A} (lift : A -> A) (f : A -> term -> term) (acc : A) (p : predicate term) : predicate term :=
  let acc_return := iterate (List.length p.(pcontext)) lift acc in
  {| puinst := p.(puinst) 
  ;  pparams := List.map (f acc) p.(pparams) 
  ;  pcontext := p.(pcontext)
  ;  preturn := f acc_return p.(preturn) |}.

Definition map_branch_with_binders {A} (lift : A -> A) (f : A -> term -> term) (acc : A) (b : branch term) : branch term := 
  let acc_body := iterate (List.length b.(bcontext)) lift acc in
  {| bcontext := b.(bcontext) ; bbody := f acc_body b.(bbody) |}.

(** [map_term_with_binders lift f acc t] maps [f acc] on the immediate subterms of [t].
    It carries an extra data [acc] (typically a lift index) which is processed by [lift] 
    (which typically add 1 to [acc]) at each binder traversal.
    It is not recursive and the order with which subterms are processed is not specified. *)
Definition map_term_with_binders {A} (lift : A -> A) (f : A -> term -> term) (acc : A) (t : term) : term :=
  match t with
  | tRel _ | tVar _ | tSort _ | tConst _ _ | tInd _ _ | tConstruct _ _ _ | tInt _ | tFloat _ | tString _ => t
  | tEvar n ts => tEvar n (List.map (f acc) ts)
  | tCast b k t => tCast (f acc b) k (f acc t)
  | tProd name ty body => tProd name (f acc ty) (f (lift acc) body)
  | tLambda name ty body => tLambda name (f acc ty) (f (lift acc) body)
  | tLetIn name def ty body => tLetIn name (f acc def) (f acc ty) (f (lift acc) body)
  | tApp func args => tApp (f acc func) (List.map (f acc) args)
  | tProj proj t => tProj proj (f acc t)
  (* For [tFix] and [tCoFix] we have to take care to lift the accumulator 
     only when processing the body of the (co)fixpoint. *)
  | tFix defs i => 
    let acc_body := iterate (List.length defs) lift acc in
    let map_def d := 
      {| dname := d.(dname) ; dtype := f acc d.(dtype) ; dbody := f acc_body d.(dbody) ; rarg := d.(rarg) |}
    in
    tFix (List.map map_def defs) i
  | tCoFix defs i => 
    let acc_body := iterate (List.length defs) lift acc in
    let map_def d := 
      {| dname := d.(dname) ; dtype := f acc d.(dtype) ; dbody := f acc_body d.(dbody) ; rarg := d.(rarg) |}
    in
    tCoFix (List.map map_def defs) i
  | tCase ci pred x branches => 
    tCase ci (map_predicate_with_binders lift f acc pred) (f acc x) (List.map (map_branch_with_binders lift f acc) branches)
  | tArray l t def ty => tArray l (List.map (f acc) t) (f acc def) (f acc ty)
  end.
