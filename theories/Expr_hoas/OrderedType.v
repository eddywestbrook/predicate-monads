Require Export Coq.Program.Tactics.
Require Export Coq.Setoids.Setoid.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Arith.Arith_base.
Require Export Coq.Relations.Relations.
Require Export Coq.Lists.List.

Import EqNotations.
Import ListNotations.


(***
 *** Ordered Types = Types with a PreOrder
 ***)

Record OType : Type :=
  {
    ot_Type :> Type;
    ot_R : relation ot_Type;
    ot_PreOrder : PreOrder ot_R
  }.

Arguments ot_R {_} _ _.

Instance OType_Reflexive (A:OType) : Reflexive (@ot_R A).
Proof.
  destruct A; auto with typeclass_instances.
Qed.

Instance OType_Transitive (A:OType) : Transitive (@ot_R A).
Proof.
  destruct A; auto with typeclass_instances.
Qed.

(* The equivalence relation for an OrderedType *)
Definition ot_equiv (A:OType) : relation (ot_Type A) :=
  fun x y => ot_R x y /\ ot_R y x.

Arguments ot_equiv {_} _ _.

Instance ot_equiv_Equivalence A : Equivalence (@ot_equiv A).
Proof.
  constructor; intro; intros.
  { split; reflexivity. }
  { destruct H; split; assumption. }
  { destruct H; destruct H0; split; transitivity y; assumption. }
Qed.


(***
 *** Commonly-Used Ordered Types
 ***)

(* The ordered type of propositions *)
Program Definition OTProp : OType :=
  {|
    ot_Type := Prop;
    ot_R := Basics.impl;
  |}.
Next Obligation.
  constructor; auto with typeclass_instances.
Qed.

(* The discrete ordered type, where things are only related to themselves *)
Program Definition OTdiscrete (A:Type) : OType :=
  {|
    ot_Type := A;
    ot_R := eq;
  |}.

(* The only ordered type over unit is the discrete one *)
Definition OTunit : OType := OTdiscrete unit.

(* The ordered type of natural numbers using <= *)
Program Definition OTnat : OType :=
  {|
    ot_Type := nat;
    ot_R := le;
  |}.

(* Flip the ordering of an OType *)
Program Definition OTflip (A:OType) : OType :=
  {|
    ot_Type := ot_Type A;
    ot_R := fun x y => ot_R y x
  |}.
Next Obligation.
  constructor.
  { intro x. reflexivity. }
  { intros x y z; transitivity y; assumption. }
Qed.

(* The pointwise relation on pairs *)
Definition pairR {A B} (RA:relation A) (RB:relation B) : relation (A*B) :=
  fun p1 p2 => RA (fst p1) (fst p2) /\ RB (snd p1) (snd p2).

Instance PreOrder_pairR A B RA RB
         `(PreOrder A RA) `(PreOrder B RB) : PreOrder (pairR RA RB).
Proof.
  constructor.
  { intro p; split; reflexivity. }
  { intros p1 p2 p3 R12 R23; destruct R12; destruct R23; split.
    - transitivity (fst p2); assumption.
    - transitivity (snd p2); assumption. }
Qed.

(* The non-dependent product ordered type, where pairs are related pointwise *)
Definition OTpair (A B:OType) : OType :=
  {|
    ot_Type := ot_Type A * ot_Type B;
    ot_R := pairR (@ot_R A) (@ot_R B);
    ot_PreOrder := PreOrder_pairR _ _ _ _ (ot_PreOrder A) (ot_PreOrder B)
  |}.

(* The sort-of pointwise relation on sum types *)
Inductive sumR {A B} (RA:relation A) (RB:relation B) : A+B -> A+B -> Prop :=
| sumR_inl a1 a2 : RA a1 a2 -> sumR RA RB (inl a1) (inl a2)
| sumR_inr b1 b2 : RB b1 b2 -> sumR RA RB (inr b1) (inr b2).

Instance PreOrder_sumR A B RA RB
         `(PreOrder A RA) `(PreOrder B RB) : PreOrder (sumR RA RB).
Proof.
  constructor.
  { intro s; destruct s; constructor; reflexivity. }
  { intros s1 s2 s3 R12 R23. destruct R12; inversion R23.
    - constructor; transitivity a2; assumption.
    - constructor; transitivity b2; assumption. }
Qed.

(*
Definition sumR {A B} (RA:relation A) (RB:relation B) : relation (A+B) :=
  fun sum1 sum2 =>
    match sum1, sum2 with
    | inl x, inl y => RA x y
    | inl x, inr y => False
    | inr x, inl y => False
    | inr x, inr y => RB x y
    end.

Instance PreOrder_sumR A B RA RB
         `(PreOrder A RA) `(PreOrder B RB) : PreOrder (sumR RA RB).
Proof.
  constructor.
  { intro s; destruct s; simpl; reflexivity. }
  { intros s1 s2 s3 R12 R23.
    destruct s1; destruct s2; destruct s3;
      try (elimtype False; assumption); simpl.
    - transitivity a0; assumption.
    - transitivity b0; assumption. }
Qed.
*)

(* The non-dependent sum ordered type, where objects are only related if they
are both "left"s or both "right"s *)
Definition OTsum (A B : OType) : OType :=
  {|
    ot_Type := ot_Type A + ot_Type B;
    ot_R := sumR (@ot_R A) (@ot_R B);
    ot_PreOrder := PreOrder_sumR _ _ _ _ (ot_PreOrder A) (ot_PreOrder B)
  |}.


(* NOTE: the following definition requires everything above to be polymorphic *)
(* NOTE: The definition we choose for OTType is actually deep: instead of
requiring ot_Type A = ot_Type B, we could just require a coercion function from
ot_Type A to ot_Type B, which would yield something more like HoTT... though
maybe it wouldn't work unless we assumed the HoTT axiom? As it is, we might need
UIP to hold if we want to use the definition given here... *)
(*
Program Definition OTType : OType :=
  {|
    ot_Type := OType;
    ot_R := (fun A B =>
               exists (e:ot_Type A = ot_Type B),
                 forall (x y:A),
                   ot_R A x y ->
                   ot_R B (rew [fun A => A] e in x)
                        (rew [fun A => A] e in y));
  |}.
*)


(***
 *** The Ordered Type for Functions
 ***)

(* The type of continuous, i.e. Proper, functions between ordered types *)
Record Pfun (A B:OType) :=
  {
    pfun_app : ot_Type A -> ot_Type B;
    pfun_Proper : Proper (ot_R ==> ot_R) pfun_app
  }.

Arguments pfun_app [_ _] _ _.
Arguments pfun_Proper [_ _] _ _ _ _.


(* The identity pfun *)
Definition idPfun A : Pfun A A :=
  {| pfun_app := fun x => x; pfun_Proper := fun x1 x2 Rx => Rx |}.

(* The identity pfun *)
Program Definition composePfun A B C (f:Pfun A B) (g:Pfun B C) :=
  {| pfun_app := fun x => pfun_app g (pfun_app f x);
     pfun_Proper := _ |}.
Next Obligation.
  intros x1 x2 Rx. apply pfun_Proper. apply pfun_Proper. assumption.
Qed.


(* The non-dependent function ordered type *)
Definition OTarrow_R (A B : OType) : relation (Pfun A B) :=
  fun f g =>
    forall a1 a2, ot_R a1 a2 -> ot_R (pfun_app f a1) (pfun_app g a2).

Program Definition OTarrow (A B:OType) : OType :=
  {|
    ot_Type := Pfun A B;
    ot_R := OTarrow_R A B;
  |}.
Next Obligation.
  constructor.
  { intros f; apply (pfun_Proper f). }
  { intros f g h Rfg Rgh a1 a2 Ra. transitivity (pfun_app g a1).
    - apply (Rfg a1 a1). reflexivity.
    - apply Rgh; assumption. }
Qed.

(* Curry a Pfun *)
Program Definition pfun_curry {A B C} (pfun : Pfun (OTpair A B) C)
  : Pfun A (OTarrow B C) :=
  {| pfun_app :=
       fun a =>
         {| pfun_app := fun b => pfun_app pfun (a,b);
            pfun_Proper := _ |};
     pfun_Proper := _ |}.
Next Obligation.
Proof.
  intros b1 b2 Rb. apply pfun_Proper.
  split; [ reflexivity | assumption ].
Qed.
Next Obligation.
Proof.
  intros a1 a2 Ra b1 b2 Rb; simpl.
  apply pfun_Proper; split; assumption.
Qed.

(* Uncrry a Pfun *)
Program Definition pfun_uncurry {A B C} (pfun : Pfun A (OTarrow B C))
  : Pfun (OTpair A B) C :=
  {| pfun_app :=
       fun ab => pfun_app (pfun_app pfun (fst ab)) (snd ab);
     pfun_Proper := _ |}.
Next Obligation.
Proof.
  intros ab1 ab2 Rab. destruct Rab as [ Ra Rb ].
  exact (pfun_Proper pfun (fst ab1) (fst ab2) Ra (snd ab1) (snd ab2) Rb).
Qed.

(* Currying and uncurrying of pfuns form an adjunction *)
(* FIXME: figure out the simplest way of stating this adjunction *)


(* OTarrow is right adjoint to OTpair, meaning that (OTarrow (OTpair A B) C) is
isomorphic to (OTarrow A (OTarrow B C)). The following is the first part of this
isomorphism, mapping left-to-right. *)


(* FIXME: could also do a forall type, but need the second type argument, B, to
itself be proper, i.e., to be an element of OTarrow A OType. Would also need a
dependent version of OTContext, below. *)


(* FIXME: maybe these the following two instances are no longer needed...? *)

(* pfun_app is always Proper *)
Instance Proper_pfun_app A B :
  Proper (@ot_R (OTarrow A B) ==> @ot_R A ==> @ot_R B) (@pfun_app A B).
Proof.
  intros f1 f2 Rf a1 a2 Ra. apply Rf; assumption.
Qed.

(* pfun_app is always Proper w.r.t. ot_equiv *)
Instance Proper_pfun_app_equiv A B :
  Proper (@ot_equiv (OTarrow A B) ==> @ot_equiv A ==> @ot_equiv B) (@pfun_app A B).
Proof.
  intros f1 f2 Rf a1 a2 Ra; destruct Rf; destruct Ra.
  split; apply Proper_pfun_app; assumption.
Qed.


(***
 *** Notations
 ***)

(*
Notation "x <o= y" :=
  (ot_R x y) (no associativity, at level 70).
Notation "x =o= y" :=
  (ot_equiv x y) (no associativity, at level 70).
*)

Notation "A '*o*' B" :=
  (OTpair A B) (left associativity, at level 40).
Notation "A '+o+' B" :=
  (OTsum A B) (left associativity, at level 50).
Notation "'~o~' A" :=
  (OTflip A) (right associativity, at level 35).
Notation "A '-o>' B" :=
  (OTarrow A B) (right associativity, at level 99).


(***
 *** Ordered Expressions
 ***)

(* An ordered type context is a list of ordered types *)
Definition OTCtx := list OType.

(* Heterogeneous lists of things indexed by contexts *)
Inductive hlist F : OTCtx -> Type :=
| hnil : hlist F []
| hcons A (x:F A) ctx (xs:hlist F ctx) : hlist F (A::ctx)
.

(* The type of names in expressions *)
Axiom Name : OType -> Type.

Definition names ctx := hlist Name ctx.

(* The type of name-bindings, and its constructor *)
Axiom nabla : forall ctx:OTCtx, (names ctx -> Type) -> Type.
Axiom nu : forall ctx A, (forall names, A names) -> nabla ctx A.



FIXME HERE NOW: old stuff below!



(***
 *** Ordered Type Contexts
 ***)

(* An ordered type context is a list of ordered types *)
Definition OTCtx := list OType.

(* The ordered type of context elements *)
Fixpoint OTCtxElem (ctx:OTCtx) : OType :=
  match ctx with
  | [] => OTunit
  | A::ctx' => OTCtxElem ctx' *o* A
  end.

(* A version of In that is in Type instead of in Prop *)
Inductive OTInCtx B : OTCtx -> Type :=
| OTInCtx_base ctx : OTInCtx B (B::ctx)
| OTInCtx_step ctx A : OTInCtx B ctx -> OTInCtx B (A::ctx)
.

(* Projecting an element out of an OTCtxElem *)
Fixpoint lookupOTInCtx B ctx (pf:OTInCtx B ctx) : OTCtxElem ctx -> B :=
  match pf in OTInCtx _ ctx return OTCtxElem ctx -> B with
  | OTInCtx_base _ _ => fun celem => snd celem
  | OTInCtx_step _ ctx' _ pf' => fun celem => lookupOTInCtx B ctx' pf' (fst celem)
  end.

Instance Proper_lookupOTInCtx B ctx pf :
  Proper (ot_R ==> ot_R) (lookupOTInCtx B ctx pf).
Proof.
  induction pf; intros c1 c2 Rc; destruct Rc.
  assumption.
  apply IHpf; assumption.
Qed.

(* Weaken a context by inserting an ordered type after n steps *)
Fixpoint weakenOTCtx (W:OType) n (ctx:OTCtx) : OTCtx :=
  match n with
  | 0 => W::ctx
  | S n' =>
    match ctx with
    | [] => [W]
    | B::ctx' => B::(weakenOTCtx W n' ctx')
    end
  end.

(* Weakening an OTCtxElem *)
Fixpoint weakenOTCtxElem W n : forall ctx, OTCtxElem (weakenOTCtx W n ctx) -> OTCtxElem ctx :=
  match n return forall ctx, OTCtxElem (weakenOTCtx W n ctx) -> OTCtxElem ctx with
  | 0 => fun _ celem => fst celem
  | S n' =>
    fun ctx =>
      match ctx return OTCtxElem (weakenOTCtx W (S n') ctx) -> OTCtxElem ctx with
      | [] => fun _ => tt
      | A::ctx' =>
        fun celem => (weakenOTCtxElem W n' ctx' (fst celem), snd celem)
      end
  end.

Instance Proper_weakenOTCtxElem W n ctx :
  Proper (ot_R ==> ot_R) (weakenOTCtxElem W n ctx).
Proof.
  revert ctx; induction n; intro ctx.
  intros c1 c2 Rc; destruct Rc; assumption.
  destruct ctx; intros c1 c2 Rc.
  reflexivity.
  destruct Rc; split; [ apply IHn | ]; assumption.
Qed.

(* Weaken an OTInCtx proof *)
Fixpoint weakenOTInCtx W n B : forall ctx, OTInCtx B ctx -> OTInCtx B (weakenOTCtx W n ctx) :=
  match n return forall ctx, OTInCtx B ctx -> OTInCtx B (weakenOTCtx W n ctx) with
  | 0 => fun _ pf => OTInCtx_step _ _ _ pf
  | S n' =>
    fun ctx pf =>
      match pf in OTInCtx _ ctx return OTInCtx B (weakenOTCtx W (S n') ctx) with
      | OTInCtx_base _ _ => OTInCtx_base _ _
      | OTInCtx_step _ ctx' _ pf' =>
        OTInCtx_step _ _ _ (weakenOTInCtx W n' B ctx' pf')
      end
  end.


(***
 *** Ordered Expressions
 ***)

(* Ordered expressions *)
Inductive OExpr : OTCtx -> OType -> Type :=
| OVar ctx A : OTInCtx A ctx -> OExpr ctx A
| OEmbed ctx A : ot_Type A -> OExpr ctx A
| OApp ctx A B : OExpr ctx (A -o> B) -> OExpr ctx A -> OExpr ctx B
| OLam ctx A B : OExpr (A::ctx) B -> OExpr ctx (A -o> B)
.

(* Weakening of ordered expressions *)
Fixpoint weakenOExpr W n ctx A (e:OExpr ctx A) :
  OExpr (weakenOTCtx W n ctx) A :=
  match e with
  | OVar ctx A pf => OVar _ A (weakenOTInCtx W n A ctx pf)
  | OEmbed ctx A x => OEmbed (weakenOTCtx W n ctx) A x
  | OApp ctx A B f arg =>
    OApp (weakenOTCtx W n ctx) A B (weakenOExpr W n ctx (A -o> B) f)
         (weakenOExpr W n ctx A arg)
  | OLam ctx A B f =>
    OLam (weakenOTCtx W n ctx) A B
         (weakenOExpr W (S n) (A::ctx) B f)
  end.

(* A substitution for all the elements of a context *)
Fixpoint OSubst (ctx_from ctx_to:OTCtx) : Type :=
  match ctx_from with
  | [] => unit
  | A::ctx_from' => OSubst ctx_from' ctx_to * OExpr ctx_to A
  end.

(* Weaken a substitution *)
Fixpoint weakenOSubst W n ctx_from ctx_to :
  OSubst ctx_from ctx_to -> OSubst ctx_from (weakenOTCtx W n ctx_to) :=
  match ctx_from return
        OSubst ctx_from ctx_to -> OSubst ctx_from (weakenOTCtx W n ctx_to)
  with
  | [] => fun _ => tt
  | A::ctx_from' =>
    fun s => (weakenOSubst W n ctx_from' ctx_to (fst s),
              weakenOExpr W n _ A (snd s))
  end.

(* Substitution into an ordered expression variable *)
Fixpoint substOVar ctx A (v:OTInCtx A ctx) ctx_to : OSubst ctx ctx_to ->
                                                    OExpr ctx_to A :=
  match v in OTInCtx _ ctx return OSubst ctx ctx_to -> OExpr ctx_to A with
  | OTInCtx_base _ _ =>
    fun s => snd s
  | OTInCtx_step _ ctx' _ v' =>
    fun s => substOVar ctx' A v' ctx_to (fst s)
  end.

(* Substitute into an expression *)
Fixpoint substOExpr ctx A (e:OExpr ctx A) :
  forall ctx_to (s:OSubst ctx ctx_to), OExpr ctx_to A :=
  match e with
  | OVar ctx A pf => fun ctx_to s => substOVar ctx A pf ctx_to s
  | OEmbed ctx A a => fun ctx_to _ => OEmbed ctx_to A a
  | OApp ctx A B e1 e2 =>
    fun ctx_to s =>
      OApp ctx_to A B (substOExpr ctx (A -o> B) e1 ctx_to s)
           (substOExpr ctx A e2 ctx_to s)
  | OLam ctx A B e =>
    fun ctx_to s =>
      OLam ctx_to A B (substOExpr (A::ctx) B e (A::ctx_to)
                                  (weakenOSubst A 0 ctx ctx_to s,
                                   OVar _ _ (OTInCtx_base A ctx_to)))
  end.

(* The identity substitution *)
Fixpoint idSubst ctx : OSubst ctx ctx :=
  match ctx with
  | [] => tt
  | A::ctx' =>
    (weakenOSubst A 0 ctx' ctx' (idSubst ctx'),
     OVar _ _ (OTInCtx_base A ctx'))
  end.



(***
 *** Semantics of Ordered Expressions
 ***)

(* The type of the semantics of an OExpr *)
Definition OTSemantics (ctx:OTCtx) (B:OType) : OType := OTCtxElem ctx -o> B.

(* Embedding into OTSemantics (return / unit for the applicative functor) *)
Definition embedSemantics ctx B (x:ot_Type B) : OTSemantics ctx B :=
  {| pfun_app := fun _ => x;
     pfun_Proper := ltac:(intro; intros; reflexivity) |}.

(* Proper instance for embedding *)
Instance Proper_embedSemantics ctx A :
  Proper (ot_R ==> ot_R) (embedSemantics ctx A).
Proof.
  intros x y Rxy a1 a2 Ra. assumption.
Qed.

(* Weakening for semantics *)
Program Definition weakenSemantics W n ctx B
        (sem:OTSemantics ctx B) : OTSemantics (weakenOTCtx W n ctx) B :=
  {| pfun_app := fun celem => pfun_app sem (weakenOTCtxElem W n ctx celem);
     pfun_Proper := _ |}.
Next Obligation.
  intros c1 c2 Rc. apply pfun_Proper. apply Proper_weakenOTCtxElem. assumption.
Qed.


(* Proper instance for weakening *)
Instance Proper_weakenSemantics W n ctx B :
  Proper (ot_R ==> ot_R) (weakenSemantics W n ctx B).
Proof.
  intros c1 c2 Rc a1 a2 Ra. simpl. apply Proper_pfun_app.
  - assumption.
  - apply Proper_weakenOTCtxElem; assumption.
Qed.

(* The semantics of a variable *)
Definition ovarSemantics ctx B (pf:OTInCtx B ctx) : OTSemantics ctx B :=
  {| pfun_app := lookupOTInCtx B ctx pf;
     pfun_Proper := _ |}.

(* Application in OTSemantics (this is <*> for the Applicative functor) *)
Program Definition applySemantics ctx A B (f : OTSemantics ctx (A -o> B))
        (arg : OTSemantics ctx A) : OTSemantics ctx B :=
  {| pfun_app := fun celem => pfun_app (pfun_app f celem) (pfun_app arg celem);
     pfun_Proper := _ |}.
Next Obligation.
  intros c1 c2 Rc. apply Proper_pfun_app; apply pfun_Proper; assumption.
Qed.

Lemma applySemantics_Proper ctx A B :
  Proper (ot_R ==> ot_R ==> ot_R) (applySemantics ctx A B).
  intros f1 f2 Rf a1 a2 Ra c1 c2 Rc.
  apply Rf; [ assumption | ]. apply Ra; assumption.
Qed.

(* Lambda in OTSemantics: this is just currying for Pfuns *)
Definition lambdaSemantics ctx A B (f : OTSemantics (A::ctx) B) :
  OTSemantics ctx (A -o> B) := pfun_curry f.

(* The semantics for any ordered expression *)
Fixpoint exprSemantics ctx A (e:OExpr ctx A) : OTSemantics ctx A :=
  match e in OExpr ctx A return OTSemantics ctx A with
  | OVar ctx A pf => ovarSemantics ctx A pf
  | OEmbed ctx A a => embedSemantics ctx A a
  | OApp ctx A B e1 e2 =>
    applySemantics ctx A B (exprSemantics ctx (A -o> B) e1)
                   (exprSemantics ctx A e2)
  | OLam ctx A B e => lambdaSemantics ctx A B (exprSemantics (A::ctx) B e)
  end.

(* The ordered type over expressions *)
(* FIXME: need to make OType polymorphic to write this...
Program Definition OExprOType ctx A : OType :=
  {|
    ot_Type := OExpr ctx A;
    ot_R := fun e1 e2 => ot_R (exprSemantics ctx A e1) (exprSemantics ctx A e2);
  |}.
 *)

Definition oexpr_R {ctx A} : relation (OExpr ctx A) :=
  fun e1 e2 => ot_R (exprSemantics ctx A e1) (exprSemantics ctx A e2).
Definition oexpr_equiv {ctx A} : relation (OExpr ctx A) :=
  fun e1 e2 => oexpr_R e1 e2 /\ oexpr_R e2 e1.

Instance oexpr_R_PreOrder ctx A : PreOrder (@oexpr_R ctx A).
Proof.
  unfold oexpr_R; constructor; intro; intros.
  { reflexivity. }
  { transitivity (exprSemantics ctx A y); assumption. }
Qed.

Instance oexpr_equiv_Equivalence ctx A : Equivalence (@oexpr_equiv ctx A).
Proof.
  constructor; intro; intros.
  { split; reflexivity. }
  { destruct H; split; assumption. }
  { destruct H; destruct H0; split; transitivity y; assumption. }
Qed.

Notation "x <o= y" :=
  (oexpr_R x y) (no associativity, at level 70).
Notation "x =o= y" :=
  (oexpr_equiv x y) (no associativity, at level 70).


(***
 *** Rewriting Automation for Expressions
 ***)

Instance oexpr_equiv_expr_R_subrelation ctx A :
  subrelation (@oexpr_equiv ctx A) (@oexpr_R ctx A).
Proof.
  intros x y Rxy; destruct Rxy; assumption.
Qed.

Instance OEmbed_Proper_R ctx A : Proper (ot_R ==> oexpr_R) (OEmbed ctx A).
Proof.
  intros a1 a2 Ra c1 c2 Rc. apply Ra.
Qed.

Instance OEmbed_Proper_equiv ctx A :
  Proper (ot_equiv ==> oexpr_equiv) (OEmbed ctx A).
Proof.
  intros a1 a2 Ra; split; intros c1 c2 Rc; apply Ra.
Qed.

Instance OEmbed_Proper_equiv_R ctx A :
  Proper (ot_equiv ==> oexpr_R) (OEmbed ctx A).
Proof.
  intros a1 a2 Ra; intros c1 c2 Rc; apply Ra.
Qed.

Instance OApp_Proper_R ctx A B :
  Proper (oexpr_R ==> oexpr_R ==> oexpr_R) (OApp ctx A B).
Proof.
  intros f1 f2 Rf e1 e2 Re c1 c2 Rc. simpl.
  apply Rf; [ assumption | ].
  apply Re; assumption.
Qed.

Instance OApp_Proper_equiv ctx A B :
  Proper (oexpr_equiv ==> oexpr_equiv ==> oexpr_equiv) (OApp ctx A B).
Proof.
  intros f1 f2 Rf e1 e2 Re; simpl.
  destruct Rf; destruct Re; split.
  - rewrite H; rewrite H1; reflexivity.
  - rewrite H0; rewrite H2; reflexivity.
Qed.

Instance OLam_Proper_R ctx A B : Proper (oexpr_R ==> oexpr_R) (OLam ctx A B).
Proof.
  intros e1 e2 Re c1 c2 Rc a1 a2 Ra. simpl.
  apply Re. split; assumption.
Qed.

Instance OLam_Proper_equiv ctx A B :
  Proper (oexpr_equiv ==> oexpr_equiv) (OLam ctx A B).
Proof.
  intros e1 e2 Re. destruct Re.
  split; [ rewrite H | rewrite H0]; reflexivity.
Qed.


(***
 *** Beta Rules
 ***)

Fixpoint substSemantics_fun ctx_from ctx_to :
  OSubst ctx_from ctx_to -> OTCtxElem ctx_to -> OTCtxElem ctx_from :=
  match ctx_from return
        OSubst ctx_from ctx_to -> OTCtxElem ctx_to -> OTCtxElem ctx_from
  with
  | [] => fun _ _ => tt
  | A::ctx_from' =>
    fun s celem =>
      (substSemantics_fun ctx_from' ctx_to (fst s) celem,
       pfun_app (exprSemantics _ _ (snd s)) celem)
  end.

Lemma substSemantics_Proper ctx_from ctx_to s :
  Proper (ot_R ==> ot_R) (substSemantics_fun ctx_from ctx_to s).
  induction ctx_from; intros c1 c2 Rc.
  - constructor.
  - split.
    + apply IHctx_from; assumption.
    + apply pfun_Proper; assumption.
Qed.

Definition substSemantics ctx_from ctx_to s :
  OTCtxElem ctx_to -o> OTCtxElem ctx_from :=
  {| pfun_app := substSemantics_fun ctx_from ctx_to s;
     pfun_Proper := substSemantics_Proper ctx_from ctx_to s |}.
