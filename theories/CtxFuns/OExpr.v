Require Export PredMonad.CtxFuns.OrderedType.
Require Export PredMonad.CtxFuns.OFuns.


(***
 *** Ordered Type Contexts
 ***)

(* A context here is just a list of type expressions *)
Inductive Ctx : Type :=
| CNil
| CCons (ctx:Ctx) A {RA:OType A}
.

Notation "ctx :> A" := (CCons ctx A) (left associativity, at level 50).

(* An element of a context is a nested tuple of elements of its types *)
Fixpoint CtxElem (ctx:Ctx) : Type :=
  match ctx with
  | CNil => unit
  | ctx' :> A => CtxElem ctx' * A
  end.

(* OTRelation instance for any CtxElem type *)
Instance OType_CtxElem ctx : OType (CtxElem ctx).
Proof.
  induction ctx; typeclasses eauto.
Defined.

(* Typeclasses Transparent OType_CtxElem. *)

Definition ctxHead ctx : Type :=
  match ctx with
  | CNil => unit
  | CCons _ A => A
  end.

Instance OType_ctxHead ctx : OType (ctxHead ctx) :=
  match ctx with
  | CNil => OTunit
  | @CCons _ _ RA => RA
  end.

Definition ctxTail ctx :=
  match ctx with
  | CNil => CNil
  | ctx' :> _ => ctx'
  end.


(***
 *** Ordered Expressions and Variables
 ***)

(* An ordered expression in ctx is just a Proper function from ctx *)
Definition OExpr ctx A `{OType A} : Type := CtxElem ctx -o> A.

Arguments OExpr ctx A {_} : simpl never.

(* Application *)
Notation "x @o@ y" :=
  (ofun_apply x y) (left associativity, at level 20).

(* Low-level lambda (we use "ofun", below, to give a nice high-level lambda) *)
Notation "'olambda' e" := (ofun_curry e) (at level 99, right associativity).

Inductive OVar : Ctx -> forall A `{OType A}, Type :=
| OVar_0 {ctx A} `{OType A} : OVar (ctx :> A) A
| OVar_S {ctx B A} `{OType A} `{OType B} (v: OVar ctx A) : OVar (ctx :> B) A
.

(* The last-bound variable in a context *)
Definition var_top {ctx A} `{OType A} : OExpr (ctx :> A) A :=
  {| ofun_app := snd; ofun_Proper := _ |}.

(* Weaken an OExpr by adding a type to the context *)
Definition weaken1 {ctx A B} `{OType A} `{OType B}
           (e: OExpr ctx A) : OExpr (ctx :> B) A :=
  compose_ofun fst_ofun e.

Fixpoint varSemantics {ctx A} `{OType A} (v:OVar ctx A) : OExpr ctx A :=
  match v in OVar ctx' A' return OExpr ctx' A' with
  | OVar_0 => var_top
  | OVar_S v => weaken1 (varSemantics v)
  end.

Coercion varSemantics : OVar >-> OExpr.


(***
 *** Weakening
 ***)

(* Inductive proof that ctx1 can be weakened to ctx2 *)
Inductive weakensTo ctx1 : Ctx -> Type :=
| WeakensRefl : weakensTo ctx1 ctx1
| WeakensCons {ctx2} (w: weakensTo ctx1 ctx2) A `{OType A}  :
    weakensTo ctx1 (ctx2 :> A)
.

Arguments WeakensRefl {_}.
Arguments WeakensCons {_ _} w A {_}.

(* Typeclass version of the above *)
Class WeakensTo ctx1 ctx2 : Type :=
  weakensProof : weakensTo ctx1 ctx2.

Instance WeakensTo_refl ctx : WeakensTo ctx ctx := WeakensRefl.

Instance WeakensTo_cons ctx1 ctx2 A `{OType A} (w: WeakensTo ctx1 ctx2) :
  WeakensTo ctx1 (ctx2 :> A) :=
  WeakensCons w A.

(* Weaken a context by mapping backwardds from the weaker to the stronger one *)
Fixpoint weakenContext {ctx1 ctx2} (w: weakensTo ctx1 ctx2) :
  CtxElem ctx2 -o> CtxElem ctx1 :=
  match w in weakensTo _ ctx2 return CtxElem ctx2 -o> CtxElem ctx1 with
  | WeakensRefl => id_ofun
  | WeakensCons w' _ => compose_ofun fst_ofun (weakenContext w')
  end.

(* Weakening for OExprs *)
Definition weakenExpr {ctx1 ctx2} `{w: WeakensTo ctx1 ctx2} {A} `{OType A}
           (e: OExpr ctx1 A) : OExpr ctx2 A :=
  compose_ofun (weakenContext w) e.

Instance Proper_weakenExpr {ctx1 ctx2} `{w: WeakensTo ctx1 ctx2} {A} `{OType A} :
  Proper (oleq ==> oleq) (weakenExpr (w:=w) (A:=A)).
Proof.
  intros e1 e2 Re. apply Proper_compose_ofun; [ reflexivity | assumption ].
Qed.

(* Weakening for variables *)
Fixpoint weakenVar_h {ctx1 ctx2} (w: weakensTo ctx1 ctx2) :
  forall {A} `{OType A}, OVar ctx1 A -> OVar ctx2 A :=
  match w in weakensTo _ ctx2
        return forall {A} `{OType A}, OVar ctx1 A -> OVar ctx2 A
  with
  | WeakensRefl => fun _ _ v => v
  | WeakensCons w' _ => fun _ _ v => OVar_S (weakenVar_h w' v)
  end.

Definition weakenVar {ctx1 ctx2} `{w:WeakensTo ctx1 ctx2} {A} `{OType A}
           (v:OVar ctx1 A) : OVar ctx2 A :=
  weakenVar_h w v.

(* Weakening is the same whether we do it before or after varSemantics *)
Lemma weakenVar_weakenExpr {ctx1 ctx2} `{w:WeakensTo ctx1 ctx2} {A} `{OType A}
      (v:OVar ctx1 A) : weakenExpr (w:=w) v =o= weakenVar v.
Proof.
  revert v; induction w; intro v; simpl.
  { apply id_compose_ofun. }
  { unfold weaken1. rewrite <- IHw. unfold weakenExpr. simpl.
    rewrite compose_compose_ofun. reflexivity. }
Qed.


(***
 *** Substitution
 ***)

(* A substitution for a single variable in a ctx *)
Fixpoint CtxSubst ctx : Type :=
  match ctx with
  | CNil => False
  | ctx' :> A => CtxSubst ctx' + OExpr ctx' A
  end.

(* The output context of a substitution *)
Fixpoint CtxSubstCtx {ctx} : CtxSubst ctx -> Ctx :=
  match ctx return CtxSubst ctx -> Ctx with
  | CNil => fun empty => match empty with end
  | ctx' :> A => fun subst_or_expr =>
                   match subst_or_expr with
                   | inl subst' => CtxSubstCtx subst' :> A
                   | inr _ => ctx'
                   end
  end.

(* The output type of a substitution *)
Fixpoint CtxSubstType {ctx} : CtxSubst ctx -> Type :=
  match ctx return CtxSubst ctx -> Type with
  | CNil => fun empty => match empty with end
  | ctx' :> A => fun subst_or_expr =>
                   match subst_or_expr with
                   | inl subst' => CtxSubstType subst'
                   | inr _ => A
                   end
  end.

Fixpoint CtxSubstOType {ctx} : forall s, OType (@CtxSubstType ctx s) :=
  match ctx return forall s, OType (@CtxSubstType ctx s) with
  | CNil => fun empty => match empty with end
  | ctx' :> A => fun subst_or_expr =>
                   match subst_or_expr with
                   | inl subst' => CtxSubstOType subst'
                   | inr _ => _
                   end
  end.

Instance OType_CtxSubstType ctx s : OType (@CtxSubstType ctx s) :=
  CtxSubstOType s.

(* Use a substitution like a mapping *)
Fixpoint substContext {ctx} :
  forall (s: CtxSubst ctx), CtxElem (CtxSubstCtx s) -o> CtxElem ctx :=
  match ctx return forall (s: CtxSubst ctx), CtxElem (CtxSubstCtx s) -o>
                                             CtxElem ctx
  with
  | CNil => fun empty => match empty with end
  | ctx' :> A =>
    fun s =>
      match s return CtxElem (@CtxSubstCtx (_ :> _) s) -o> CtxElem (_ :> _) with
      | inl s' => pair_ofun (compose_ofun fst_ofun (substContext s')) snd_ofun
      | inr e => pair_ofun id_ofun e
      end
  end.

Definition substExpr {ctx A} `{OType A} (e: OExpr ctx A) (s: CtxSubst ctx) :
  OExpr (CtxSubstCtx s) A :=
  compose_ofun (substContext s) e.

(* The result of looking up a variable in a substitution; see substVarLookup *)
Inductive VarLookupRes ctx A `{OType A} (s:CtxSubst ctx) : Type :=
| mkVarLookupRes ctx' (w: weakensTo ctx' (CtxSubstCtx s))
                 (v_or_e: OVar ctx' A + OExpr ctx' A) :
    VarLookupRes ctx A s.

(* Weaken a VarLookupRes *)
Definition weakenVarLookupRes {ctx A B} `{OType A} `{OType B} {s}
           (res: VarLookupRes ctx A s) :
  VarLookupRes (ctx :> B) A (inl s) :=
  match res with
  | mkVarLookupRes _ _ _ ctx' w v_or_e =>
    mkVarLookupRes (_:>_) A (inl s) ctx' (WeakensCons w B) v_or_e
  end.

(* Look up a variable in a substitution, getting either an OExpr or a
strengthened variable. We existentially quantify over the returned context so
that we can do one combined weakening, either of the returned variable or oexpr,
rather than having N weakening steps *)
Program Fixpoint substVarLookup {ctx A} `{OType A} (v: OVar ctx A) :
  forall (s:CtxSubst ctx), VarLookupRes ctx A s :=
  match v in OVar ctx A return forall s, VarLookupRes ctx A s with
  | OVar_0 =>
    fun (s: CtxSubst (_ :> _)) =>
      match s return VarLookupRes (_:>_) _ s
      with
      | inl s' =>
        mkVarLookupRes (_:>_) _ (inl s') _ WeakensRefl (inl OVar_0)
      | inr e =>
        mkVarLookupRes (_:>_) _ (inr e) _ WeakensRefl (inr e)
      end
  | OVar_S v' =>
    fun (s: CtxSubst (_:>_)) =>
      match s return VarLookupRes (_:>_) _ s with
      | inl s' =>
        weakenVarLookupRes (substVarLookup v' s')
      | inr e =>
        mkVarLookupRes (_:>_) _ (inr e) _ WeakensRefl (inl v')
      end
  end.

(* Substitute into a variable *)
Definition substVar {ctx A} `{OType A} (v: OVar ctx A) (s:CtxSubst ctx) :
  OExpr (CtxSubstCtx s) A :=
  match substVarLookup v s with
  | mkVarLookupRes _ _ _ ctx' w (inl v') => weakenVar_h w v'
  | mkVarLookupRes _ _ _ ctx' w (inr e) => weakenExpr (w:=w) e
  end.

(* Substitution is the same whether we do it before or after varSemantics *)
Lemma substVar_substExpr {ctx} {A} `{OType A} (v: OVar ctx A)
      (s: CtxSubst ctx) : substExpr v s =o= substVar v s.
Proof.
  revert s; induction v; intro s; unfold substExpr.
  { destruct s as [ s | e ]; simpl; apply funOExt; intro c; reflexivity. }
  { destruct s as [ s | e ]; simpl; apply funOExt; intro c; [ | reflexivity ].
    simpl.
    assert ((substVar (OVar_S v) (inl s)) = weakenExpr (substVar v s)).
    - unfold substVar. simpl. destruct (substVarLookup v s); simpl.
      destruct v_or_e; admit.
    - rewrite H1. rewrite <- IHv. reflexivity. }
Admitted.


(***
 *** Notation for Lambdas
 ***)

(* Helper function to build lambdas *)
Definition mkLam {ctx A B} `{OType A} `{OType B}
           (body : (forall {ctx'} `{WeakensTo (ctx :> A) ctx'}, OVar ctx' A) ->
                   OExpr (ctx :> A) B) :
  OExpr ctx (A -o> B) :=
  ofun_curry (body (fun _ _ => weakenVar OVar_0)).

Notation "'ofun' x => e" :=
  (mkLam (fun (x : forall {ctx'} `{WeakensTo _ ctx'}, OVar ctx' _) => e))
    (right associativity, at level 99).

Notation "'ofun' ( x : A ) => e" :=
  (mkLam (fun (x : forall {ctx'} `{WeakensTo _ ctx'}, OVar ctx' A) => e))
    (right associativity, at level 99, x at level 0).


(***
 *** Ordered Expressions for Pairs
 ***)

Definition opair {ctx A B} `{OType A} `{OType B} : OExpr ctx (A -o> B -o> A*B) :=
  const_ofun (ofun_curry id_ofun).
Definition ofst {ctx A B} `{OType A} `{OType B} : OExpr ctx (A * B -o> A) :=
  const_ofun fst_ofun.
Definition osnd {ctx A B} `{OType A} `{OType B} : OExpr ctx (A * B -o> B) :=
  const_ofun snd_ofun.

Notation "( x ,o, y )" := (opair @o@ x @o@ y : OExpr _ _) (at level 0).

Lemma ofst_opair {ctx A B} `{OType A} `{OType B}
      (e1: OExpr ctx A) (e2: OExpr ctx B) :
  ofst @o@ (e1 ,o, e2) =o= e1.
Proof.
  apply funOExt; intro c. reflexivity.
Qed.

Lemma osnd_opair {ctx A B} `{OType A} `{OType B}
      (e1: OExpr ctx A) (e2: OExpr ctx B) :
  osnd @o@ (e1 ,o, e2) =o= e2.
Proof.
  apply funOExt; intro c. reflexivity.
Qed.

Lemma opair_ext {ctx A B} `{OType A} `{OType B} (e: OExpr ctx (A*B)) :
  opair @o@ (ofst @o@ e) @o@ (osnd @o@ e) =o= e.
Proof.
  apply funOExt; intro c. simpl. destruct (ofun_app e c). reflexivity.
Qed.


(***
 *** Ordered Expressions for Sums
 ***)

Definition oinl {ctx A B} `{OType A} `{OType B} : OExpr ctx (A -o> A + B) :=
  const_ofun inl_ofun.
Definition oinr {ctx A B} `{OType A} `{OType B} : OExpr ctx (B -o> A + B) :=
  const_ofun inr_ofun.
Definition osumElim {ctx A B C} `{OType A} `{OType B} `{OType C} :
  OExpr ctx ((A -o> C) -o> (B -o> C) -o> A + B -o> C) :=
  const_ofun sum_elim_ofun.

Lemma osumElim_oinl {ctx A B C} `{OType A} `{OType B} `{OType C}
      (f1 : OExpr ctx (A -o> C)) (f2 : OExpr ctx (B -o> C)) e :
  osumElim @o@ f1 @o@ f2 @o@ (oinl @o@ e) =o= f1 @o@ e.
Proof.
  apply funOExt; intro c. reflexivity.
Qed.

Lemma osumElim_oinr {ctx A B C} `{OType A} `{OType B} `{OType C}
      (f1 : OExpr ctx (A -o> C)) (f2 : OExpr ctx (B -o> C)) e :
  osumElim @o@ f1 @o@ f2 @o@ (oinr @o@ e) =o= f2 @o@ e.
Proof.
  apply funOExt; intro c. reflexivity.
Qed.


(***
 *** Ordered Expressions for Propositions
 ***)

Definition oforall {ctx A} `{OType A} : OExpr ctx ((A -o> Prop) -o> Prop) :=
  const_ofun forall_ofun.
Definition oexists {ctx A} `{OType A} : OExpr ctx ((A -o> Prop) -o> Prop) :=
  const_ofun exists_ofun.
Definition oexists2 {ctx A} `{OType A} :
  OExpr ctx ((A -o> Prop) -o> (Flip A -o> Prop) -o> Prop) :=
  const_ofun exists2flip_ofun.
Definition oand {ctx} : OExpr ctx (Prop -o> Prop -o> Prop) :=
  const_ofun and_ofun.
Definition oor {ctx} : OExpr ctx (Prop -o> Prop -o> Prop) :=
  const_ofun or_ofun.
Definition oimpl {ctx} : OExpr ctx (Flip Prop -o> Prop -o> Prop) :=
  const_ofun impl_ofun.
Definition oappr {ctx A} `{OType A} : OExpr ctx (Flip A -o> A -o> Prop) :=
  const_ofun oleq_ofun.
