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

Arguments ot_R {_} _ _ : simpl never.

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

(* FIXME: figure out what versions of this we need for rewriting! *)
Instance Proper_ot_R_ot_R A : Proper (ot_R --> ot_R ==> Basics.impl) (@ot_R A).
Proof.
  intros a1 a2 Ra b1 b2 Rb Rab.
  transitivity a1; [ assumption | ]. transitivity b1; assumption.
Qed.

Instance Subrelation_ot_equiv_ot_R A : subrelation (@ot_equiv A) ot_R.
Proof.
  intros a1 a2 Ra; destruct Ra; assumption.
Qed.

Instance Proper_ot_equiv_ot_R A :
  Proper (ot_equiv ==> ot_equiv ==> iff) (@ot_R A).
Proof.
  intros x1 x2 Rx y1 y2 Ry; destruct Rx; destruct Ry; split; intro R.
  transitivity x1; [ assumption | ]; transitivity y1; assumption.
  transitivity x2; [ assumption | ]; transitivity y2; assumption.
Qed.

Instance Proper_ot_equiv A : Proper (ot_equiv ==> ot_equiv ==> iff) (@ot_equiv A).
Proof.
  intros x1 x2 Rx y1 y2 Ry. rewrite Rx. rewrite Ry. reflexivity.
Qed.

Instance Proper_ot_equiv_partial A a : Proper (ot_equiv ==> Basics.flip Basics.impl) (@ot_equiv A a).
Proof.
  intros x1 x2 Rx. rewrite Rx. reflexivity.
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

(* Helper instance for using pair ordered types *)
Instance Proper_pair A B :
  Proper (@ot_R A ==> @ot_R B ==> @ot_R (OTpair A B)) pair.
Proof.
  intros a1 a2 Ra b1 b2 Rb. split; assumption.
Qed.

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

Instance Proper_pfun_app_partial A B f :
  Proper (ot_R ==> ot_R) (@pfun_app A B f).
Proof.
  apply pfun_Proper.
Qed.

Instance Proper_pfun_app_partial_equiv A B f :
  Proper (ot_equiv ==> ot_equiv) (@pfun_app A B f).
Proof.
  apply Proper_pfun_app_equiv; reflexivity.
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
 *** Some Useful Pfuns
 ***)

(* The identity pfun *)
Definition id_pfun {A} : A -o> A :=
  {| pfun_app := fun x => x; pfun_Proper := fun x1 x2 Rx => Rx |}.

(* The identity pfun *)
Program Definition compose_pfun {A B C} (f:A -o> B) (g:B -o> C) : A -o> C :=
  {| pfun_app := fun x => pfun_app g (pfun_app f x);
     pfun_Proper := _ |}.
Next Obligation.
  intros x1 x2 Rx. apply pfun_Proper. apply pfun_Proper. assumption.
Qed.

Instance Proper_compose_pfun A B C :
  Proper (ot_R ==> ot_R ==> ot_R) (@compose_pfun A B C).
  intros f1 f2 Rf g1 g2 Rg a1 a2 Ra.
  apply Rg. apply Rf. assumption.
Qed.

Instance Proper_compose_pfun_equiv A B C :
  Proper (ot_equiv ==> ot_equiv ==> ot_equiv) (@compose_pfun A B C).
  intros f1 f2 Rf g1 g2 Rg.
  split; intros a1 a2 Ra;
    simpl; rewrite Rg; rewrite Rf; rewrite Ra; reflexivity.
Qed.

(* Category theory laws for Pfuns *)
Lemma id_compose_pfun A B (f: A -o> B) :
  ot_equiv (compose_pfun id_pfun f) f.
  split; intros a1 a2 Ra; simpl; apply pfun_Proper; assumption.
Qed.
Lemma compose_id_pfun A B (f: A -o> B) :
  ot_equiv (compose_pfun f id_pfun) f.
  split; intros a1 a2 Ra; simpl; apply pfun_Proper; assumption.
Qed.
Lemma compose_compose_pfun A B C D (f: A -o> B) (g: B -o> C) (h: C -o> D) :
  ot_equiv (compose_pfun f (compose_pfun g h)) (compose_pfun (compose_pfun f g) h).
  split; intros a1 a2 Ra; simpl; repeat apply pfun_Proper; assumption.
Qed.

(* The constant pfun *)
Definition const_pfun {A B} b : A -o> B :=
  {| pfun_app := fun _ => b; pfun_Proper := fun _ _ _ => ltac:(reflexivity) |}.

(* Composing with the constant pfun on the left *)
Lemma compose_const_pfun_f A B C b (f : B -o> C) :
  ot_equiv (compose_pfun (@const_pfun A B b) f) (const_pfun (pfun_app f b)).
  split; intros a1 a2 Ra; reflexivity.
Qed.

(* Composing with the constant pfun on the right *)
Lemma compose_f_const_pfun A B C (f : A -o> B) c :
  ot_equiv (compose_pfun f (@const_pfun B C c)) (const_pfun c).
  split; intros a1 a2 Ra; reflexivity.
Qed.


(* Take the pair of the outputs of two pfuns *)
Program Definition pair_pfun {A B C}
           (f: A -o> B) (g: A -o> C) : A -o> (B *o* C) :=
  {| pfun_app := fun a => (pfun_app f a, pfun_app g a) |}.
Next Obligation.
  intros a1 a2 Ra; split; apply pfun_Proper; assumption.
Qed.

Instance Proper_pair_pfun A B C :
  Proper (ot_R ==> ot_R ==> ot_R) (@pair_pfun A B C).
Proof.
  intros a1 a2 Ra b1 b2 Rb c1 c2 Rc.
  simpl. rewrite Ra. rewrite Rb. rewrite Rc. reflexivity.
Qed.

Instance Proper_pair_pfun_equiv A B C :
  Proper (ot_equiv ==> ot_equiv ==> ot_equiv) (@pair_pfun A B C).
Proof.
  intros a1 a2 Ra b1 b2 Rb; split; intros c1 c2 Rc; split; simpl;
    try rewrite Ra; try rewrite Rb; try rewrite Rc; reflexivity.
Qed.

(* compose commutes with pair *)
Lemma compose_f_pair_pfun A B C D (f: A -o> B) (g: B -o> C) (h: B -o> D) :
  ot_equiv (compose_pfun f (pair_pfun g h))
           (pair_pfun (compose_pfun f g) (compose_pfun f h)).
  split; intros a1 a2 Ra; simpl; rewrite Ra; reflexivity.
Qed.


(* The first projection pfun *)
Program Definition fst_pfun {A B} : A *o* B -o> A := {| pfun_app := fst |}.
Next Obligation.
  intros p1 p2 Rp; destruct Rp; assumption.
Qed.

(* The second projection pfun *)
Program Definition snd_pfun {A B} : A *o* B -o> B := {| pfun_app := snd |}.
Next Obligation.
  intros p1 p2 Rp; destruct Rp; assumption.
Qed.

(* Composing pair with fst gives the first function in the pair *)
Lemma compose_pair_fst A B C (f: A -o> B) (g: A -o> C) :
  ot_equiv (compose_pfun (pair_pfun f g) fst_pfun) f.
  split; intros a1 a2 Ra; simpl; apply pfun_Proper; assumption.
Qed.

(* Composing pair with snd gives the second function in the pair *)
Lemma compose_pair_snd A B C (f: A -o> B) (g: A -o> C) :
  ot_equiv (compose_pfun (pair_pfun f g) snd_pfun) g.
  split; intros a1 a2 Ra; simpl; apply pfun_Proper; assumption.
Qed.

(* Taking the pair of fst and snd is the identity *)
Lemma pair_fst_snd_eta A B :
  ot_equiv (pair_pfun (@fst_pfun A B) (@snd_pfun A B)) id_pfun.
  split; intros p1 p2 Rp; destruct Rp; split; simpl; assumption.
Qed.


(* Curry a Pfun *)
Program Definition pfun_curry {A B C} (pfun : (A *o* B) -o> C)
  : A -o> (B -o> C) :=
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
Program Definition pfun_uncurry {A B C} (pfun : A -o> (B -o> C))
  : (A *o* B) -o> C :=
  {| pfun_app :=
       fun ab => pfun_app (pfun_app pfun (fst ab)) (snd ab);
     pfun_Proper := _ |}.
Next Obligation.
Proof.
  intros ab1 ab2 Rab. destruct Rab as [ Ra Rb ].
  exact (pfun_Proper pfun (fst ab1) (fst ab2) Ra (snd ab1) (snd ab2) Rb).
Qed.


(* pfun_curry is Proper *)
Instance Proper_pfun_curry A B C : Proper (ot_R ==> ot_R) (@pfun_curry A B C).
Proof.
  intros f1 f2 Rf a1 a2 Ra b1 b2 Rb. apply Rf. split; assumption.
Qed.

(* pfun_curry is Proper w.r.t. equivalence *)
Instance Proper_pfun_curry_equiv A B C :
  Proper (ot_equiv ==> ot_equiv) (@pfun_curry A B C).
Proof.
  intros f1 f2 Rf; destruct Rf; split; apply Proper_pfun_curry; assumption.
Qed.

(* FIXME: Proper instance for pfun_uncurry *)

(* Currying and uncurrying of pfuns form an isomorphism: part 1 *)
Lemma pfun_curry_uncurry_eq A B C (f: (A *o* B) -o> C) :
  ot_equiv (pfun_uncurry (pfun_curry f)) f.
  split; intros ab1 ab2 Rab; simpl; apply pfun_Proper;
    destruct Rab; split; assumption.
Qed.

(* Currying and uncurrying of pfuns form an isomorphism: part 2 *)
Lemma pfun_uncurry_curry_eq A B C (f: A -o> B -o> C) :
  ot_equiv (pfun_curry (pfun_uncurry f)) f.
  split; intros a1 a2 Ra b1 b2 Rb; simpl; apply Proper_pfun_app;
    try apply pfun_Proper; assumption.
Qed.


(* The S combinator for pfuns (FIXME: do we need this?) *)
Program Definition pfun_S {A B C} : (A -o> B -o> C) -o> (A -o> B) -o> A -o> C :=
  {| pfun_app :=
       fun f =>
         {| pfun_app :=
              fun g =>
                {| pfun_app := fun a => pfun_app (pfun_app f a) (pfun_app g a) |}
         |}
  |}.
Next Obligation.
  intros a1 a2 Ra; apply Proper_pfun_app; apply pfun_Proper; assumption.
Qed.
Next Obligation.
  intros g1 g2 Rg a1 a2 Ra. simpl. apply Proper_pfun_app.
  - apply pfun_Proper; assumption.
  - apply Rg; assumption.
Qed.
Next Obligation.
  intros f1 f2 Rf g1 g2 Rg a1 a2 Ra. simpl. apply Proper_pfun_app.
  - apply Rf; assumption.
  - apply Rg; assumption.
Qed.

(* This is the S combinator, but partially applied *)
Program Definition pfun_apply {A B C} (f: A -o> B -o> C) (g: A -o> B) : A -o> C :=
  {| pfun_app := fun a => pfun_app (pfun_app f a) (pfun_app g a) |}.
Next Obligation.
  intros a1 a2 Ra; apply Proper_pfun_app; apply pfun_Proper; assumption.
Qed.

Instance Proper_pfun_apply A B C :
  Proper (ot_R ==> ot_R ==> ot_R) (@pfun_apply A B C).
Proof.
  intros a1 a2 Ra b1 b2 Rb c1 c2 Rc. simpl.
  rewrite Ra. rewrite Rb. rewrite Rc. reflexivity.
Qed.

Instance Proper_pfun_apply_equiv A B C :
  Proper (ot_equiv ==> ot_equiv ==> ot_equiv) (@pfun_apply A B C).
Proof.
  intros a1 a2 Ra b1 b2 Rb; split; intros c1 c2 Rc; simpl;
    rewrite Ra; rewrite Rb; rewrite Rc; reflexivity.
Qed.

(* compose commutes with S *)
Lemma compose_pfun_apply A B C D (f : A -o> B) (g: B -o> C -o> D) h :
  ot_equiv (compose_pfun f (pfun_apply g h))
           (pfun_apply (compose_pfun f g) (compose_pfun f h)).
  split; intros a1 a2 Ra; simpl; rewrite Ra; reflexivity.
Qed.

(* compose commutes with currying *)
Lemma compose_pfun_curry A B C D (f: A -o> B) (g: B *o* C -o> D) :
  ot_equiv (compose_pfun f (pfun_curry g))
           (pfun_curry
              (compose_pfun (pair_pfun (compose_pfun fst_pfun f) snd_pfun) g)).
  split; intros a1 a2 Ra c1 c2 Rc; simpl; rewrite Ra; rewrite Rc; reflexivity.
Qed.

(* We can simplify pfun_S used with pfun_curry *)
Lemma pfun_apply_pfun_curry A B C f g :
  ot_equiv (@pfun_apply A B C (pfun_curry f) g)
           (compose_pfun (pair_pfun id_pfun g) f).
  split; intros a1 a2 Ra; simpl; apply pfun_Proper; split;
    try apply pfun_Proper; assumption.
Qed.



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
Fixpoint lookupOTInCtx B ctx (pf:OTInCtx B ctx) : OTCtxElem ctx -o> B :=
  match pf in OTInCtx _ ctx return OTCtxElem ctx -o> B with
  | OTInCtx_base _ _ => snd_pfun
  | OTInCtx_step _ ctx' _ pf' => compose_pfun fst_pfun (lookupOTInCtx B ctx' pf')
  end.

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
Fixpoint weakenOTCtxElem W n :
  forall ctx, OTCtxElem (weakenOTCtx W n ctx) -o> OTCtxElem ctx :=
  match n return forall ctx, OTCtxElem (weakenOTCtx W n ctx) -o> OTCtxElem ctx with
  | 0 => fun _ => fst_pfun
  | S n' =>
    fun ctx =>
      match ctx return OTCtxElem (weakenOTCtx W (S n') ctx) -o> OTCtxElem ctx with
      | [] => @const_pfun _ OTunit tt
      | A::ctx' =>
        pair_pfun (compose_pfun fst_pfun (weakenOTCtxElem W n' ctx')) snd_pfun
      end
  end.

(* Weaken an OTInCtx proof *)
Fixpoint weakenOTInCtx W n B :
  forall ctx, OTInCtx B ctx -> OTInCtx B (weakenOTCtx W n ctx) :=
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


(* Weakening commutes with lookup *)
Lemma lookup_weaken_OTInCtx W n B ctx pf :
  ot_equiv
    (lookupOTInCtx B (weakenOTCtx W n ctx) (weakenOTInCtx W n B ctx pf))
    (compose_pfun (weakenOTCtxElem W n ctx) (lookupOTInCtx B ctx pf)).
  revert n; induction pf; intros; destruct n.
  { reflexivity. }
  { simpl. rewrite compose_pair_snd. reflexivity. }
  { simpl. reflexivity. }
  { simpl. rewrite compose_compose_pfun. rewrite compose_pair_fst.
    rewrite <- compose_compose_pfun. rewrite IHpf. reflexivity. }
Qed.


(***
 *** Ordered Expressions
 ***)

(* Ordered expressions *)
Inductive OExpr : OTCtx -> OType -> Type :=
| OVar {ctx A} : OTInCtx A ctx -> OExpr ctx A
| OEmbed {ctx A} : ot_Type A -> OExpr ctx A
| OApp {ctx A B} : OExpr ctx (A -o> B) -> OExpr ctx A -> OExpr ctx B
| OLam {ctx A B} : OExpr (A::ctx) B -> OExpr ctx (A -o> B)
.

(* Weakening of ordered expressions *)
Fixpoint weakenOExpr W n {ctx A} (e:OExpr ctx A) :
  OExpr (weakenOTCtx W n ctx) A :=
  match e with
  | OVar pf => OVar (weakenOTInCtx W n _ _ pf)
  | OEmbed x => OEmbed x
  | OApp f arg => OApp (weakenOExpr W n f) (weakenOExpr W n arg)
  | OLam f => OLam (weakenOExpr W (S n) f)
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
              weakenOExpr W n (snd s))
  end.

(* Substitution into an ordered expression variable *)
Fixpoint substOVar {ctx A} (v:OTInCtx A ctx) {ctx_to} : OSubst ctx ctx_to ->
                                                        OExpr ctx_to A :=
  match v in OTInCtx _ ctx return OSubst ctx ctx_to -> OExpr ctx_to A with
  | OTInCtx_base _ _ =>
    fun s => snd s
  | OTInCtx_step _ ctx' _ v' =>
    fun s => substOVar v' (fst s)
  end.

(* Substitute into an expression *)
Fixpoint substOExpr {ctx A} (e:OExpr ctx A) :
  forall {ctx_to} (s:OSubst ctx ctx_to), OExpr ctx_to A :=
  match e with
  | OVar pf => fun ctx_to s => substOVar pf s
  | OEmbed a => fun ctx_to _ => OEmbed a
  | OApp e1 e2 =>
    fun ctx_to s =>
      OApp (substOExpr e1 s)
           (substOExpr e2 s)
  | @OLam ctx A _ e =>
    fun ctx_to s =>
      OLam (substOExpr
              e
              (weakenOSubst A 0 ctx _ s, OVar (OTInCtx_base A _)))
  end.

(* The identity substitution *)
Fixpoint idSubst ctx : OSubst ctx ctx :=
  match ctx with
  | [] => tt
  | A::ctx' =>
    (@weakenOSubst A 0 ctx' ctx' (idSubst ctx'),
     OVar (OTInCtx_base A ctx'))
  end.



(***
 *** Semantics of Ordered Expressions
 ***)

(* The type of the semantics of an OExpr *)
Definition OTSemantics (ctx:OTCtx) (B:OType) : OType := OTCtxElem ctx -o> B.

(* Weakening for semantics *)
Definition weakenSemantics W n ctx B
           (sem:OTSemantics ctx B) : OTSemantics (weakenOTCtx W n ctx) B :=
  compose_pfun (weakenOTCtxElem W n ctx) sem.

(* Unfold weakenSemantics *)
Arguments weakenSemantics W n ctx B sem /.

(* The semantics for any ordered expression *)
Fixpoint exprSemantics {ctx A} (e:OExpr ctx A) : OTSemantics ctx A :=
  match e in OExpr ctx A return OTSemantics ctx A with
  | OVar pf => lookupOTInCtx _ _ pf
  | OEmbed a => const_pfun a
  | OApp e1 e2 => pfun_apply (exprSemantics e1) (exprSemantics e2)
  | OLam e => pfun_curry (exprSemantics e)
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
  fun e1 e2 => ot_R (exprSemantics e1) (exprSemantics e2).
Definition oexpr_equiv {ctx A} : relation (OExpr ctx A) :=
  fun e1 e2 => ot_equiv (exprSemantics e1) (exprSemantics e2).

Instance oexpr_R_PreOrder ctx A : PreOrder (@oexpr_R ctx A).
Proof.
  unfold oexpr_R; constructor; intro; intros.
  { reflexivity. }
  { transitivity (exprSemantics y); assumption. }
Qed.

Instance oexpr_equiv_Equivalence ctx A : Equivalence (@oexpr_equiv ctx A).
Proof.
  constructor; intro; intros; unfold oexpr_equiv.
  { reflexivity. }
  { symmetry; assumption. }
  { transitivity (exprSemantics y); assumption. }
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

Instance OEmbed_Proper_R ctx A : Proper (ot_R ==> oexpr_R) (@OEmbed ctx A).
Proof.
  intros a1 a2 Ra c1 c2 Rc. apply Ra.
Qed.

Instance OEmbed_Proper_equiv ctx A :
  Proper (ot_equiv ==> oexpr_equiv) (@OEmbed ctx A).
Proof.
  intros a1 a2 Ra; split; intros c1 c2 Rc; apply Ra.
Qed.

Instance OEmbed_Proper_equiv_R ctx A :
  Proper (ot_equiv ==> oexpr_R) (@OEmbed ctx A).
Proof.
  intros a1 a2 Ra; intros c1 c2 Rc; apply Ra.
Qed.

Instance OApp_Proper_R ctx A B :
  Proper (oexpr_R ==> oexpr_R ==> oexpr_R) (@OApp ctx A B).
Proof.
  intros f1 f2 Rf e1 e2 Re c1 c2 Rc. simpl.
  apply Rf; [ assumption | ].
  apply Re; assumption.
Qed.

Instance OApp_Proper_equiv ctx A B :
  Proper (oexpr_equiv ==> oexpr_equiv ==> oexpr_equiv) (@OApp ctx A B).
Proof.
  intros f1 f2 Rf e1 e2 Re; simpl.
  destruct Rf; destruct Re; split; simpl.
  - rewrite H; rewrite H1; reflexivity.
  - rewrite H0; rewrite H2; reflexivity.
Qed.

Instance OLam_Proper_R ctx A B : Proper (oexpr_R ==> oexpr_R) (@OLam ctx A B).
Proof.
  intros e1 e2 Re c1 c2 Rc a1 a2 Ra. simpl.
  apply Re. split; assumption.
Qed.

Instance OLam_Proper_equiv ctx A B :
  Proper (oexpr_equiv ==> oexpr_equiv) (@OLam ctx A B).
Proof.
  intros e1 e2 Re. destruct Re.
  split; simpl; [ rewrite H | rewrite H0]; reflexivity.
Qed.


(***
 *** Beta Rules
 ***)

Fixpoint substSemantics ctx_from ctx_to :
  OSubst ctx_from ctx_to -> OTCtxElem ctx_to -o> OTCtxElem ctx_from :=
  match ctx_from return
        OSubst ctx_from ctx_to -> OTCtxElem ctx_to -o> OTCtxElem ctx_from
  with
  | [] => fun _ => @const_pfun _ OTunit tt
  | A::ctx_from' =>
    fun s =>
      pair_pfun
        (substSemantics ctx_from' ctx_to (fst s))
        (exprSemantics (snd s))
  end.

Lemma OExpr_Weakening W n {ctx A} (e: OExpr ctx A) :
  ot_equiv
    (exprSemantics (weakenOExpr W n e))
    (weakenSemantics W n ctx A (exprSemantics e)).
  revert n; induction e; intros; simpl.
  { apply lookup_weaken_OTInCtx. }
  { rewrite compose_f_const_pfun; reflexivity. }
  { rewrite IHe1. rewrite IHe2. rewrite compose_pfun_apply. reflexivity. }
  { rewrite (IHe (S n)). simpl. rewrite compose_pfun_curry. reflexivity. }
Qed.

Lemma OSubst_Weakening W ctx_from ctx_to s :
  ot_equiv
    (substSemantics ctx_from (W::ctx_to) (weakenOSubst W 0 _ _ s))
    (compose_pfun fst_pfun (substSemantics ctx_from ctx_to s)).
  revert s; induction ctx_from; intros; simpl.
  { rewrite compose_f_const_pfun. reflexivity. }
  { rewrite IHctx_from. rewrite compose_f_pair_pfun.
    fold (weakenOTCtx W 0 ctx_to).
    rewrite OExpr_Weakening.
    reflexivity. }
Qed.

Lemma OExpr_Substitution {ctx A} (e: OExpr ctx A) {ctx_to} s :
  ot_equiv (exprSemantics (substOExpr e s))
           (compose_pfun
              (substSemantics ctx ctx_to s)
              (exprSemantics e)).
  revert ctx_to s; induction e; intros.
  { induction o.
    - simpl. rewrite compose_pair_snd. reflexivity.
    - simpl. destruct s. apply IHo. }
  { split; intros c1 c2 Rc; reflexivity. }
  { simpl. rewrite IHe1. rewrite IHe2. rewrite compose_pfun_apply. reflexivity. }
  { simpl. rewrite IHe. simpl. rewrite compose_pfun_curry.
    rewrite OSubst_Weakening. reflexivity. }
Qed.

Lemma idSubst_id ctx :
  ot_equiv (substSemantics _ _ (idSubst ctx)) id_pfun.
  induction ctx; simpl.
  { split; intros c1 c2 Rc; destruct c1; destruct c2; simpl; reflexivity. }
  { rewrite OSubst_Weakening. rewrite IHctx. rewrite compose_id_pfun.
    rewrite pair_fst_snd_eta. reflexivity. }
Qed.

Lemma OExpr_beta ctx A B (f: OExpr (A::ctx) B) (arg: OExpr ctx A) :
  OApp (OLam f) arg =o= substOExpr f (idSubst _, arg).
  unfold oexpr_equiv. simpl. rewrite pfun_apply_pfun_curry.
  rewrite OExpr_Substitution. simpl. rewrite idSubst_id. reflexivity.
Qed.


FIXME HERE NOW

(* Reverse l1 and append l2 *)
Fixpoint rev_app {A} (l1 l2: list A) : list A :=
  match l1 with
  | [] => l2
  | x::l1' => rev_app l1' (x::l2)
  end.

Fixpoint weakenOTInCtx_rev_app ctx_pre :
  forall B ctx, OTInCtx B ctx -> OTInCtx B (rev_app ctx_pre ctx) :=
  match ctx_pre
        return forall B ctx, OTInCtx B ctx -> OTInCtx B (rev_app ctx_pre ctx)
  with
  | [] => fun B ctx pf => pf
  | A::ctx_pre' =>
    fun B ctx pf =>
      weakenOTInCtx_rev_app ctx_pre' B (A::ctx) (OTInCtx_step B _ A pf)
  end.

(* Build the weakening substitution, that maps each variable in ctx to the
corresonding variable in rev_app ctx_pre ctx *)
Fixpoint weakenSubst (ctx_pre ctx: OTCtx) : OSubst ctx (rev_app ctx_pre ctx) :=
  match ctx with
  | [] => tt
  | A::ctx' =>
    (weakenSubst (A::ctx_pre) ctx',
     OVar _ _ (weakenOTInCtx_rev_app ctx_pre A (A::ctx') (OTInCtx_base A ctx')))
  end.

FIXME HERE NOW

(* Substitution into a context (which just removes a type) *)
Fixpoint substOTCtx (ctx:OTCtx) B (pf:OTInCtx B ctx) : OTCtx :=
  match pf with
  | OTInCtx_base _ ctx => ctx
  | OTInCtx_step _ ctx A pf' =>
    A :: (substOTCtx ctx B pf')
  end.

(* Substitution into an ordered variable *)
Fixpoint substOVar ctx A (pf: OTInCtx A ctx) :
  forall B pfB, OExpr (substOTCtx ctx B pf) B -> OExpr (substOTCtx ctx B pf) A :=
  match pf in OTInCtx A ctx
        return forall B pfB, OExpr (substOTCtx ctx B pf) B ->
                             OExpr (substOTCtx ctx B pf) A
  with
  | OTInCtx_base _ ctx =>
    fun B pfB s =>
      match pfB with
      | OTInCtx_base _ 

(* Substitution into ordered expressions *)
Fixpoint substOExpr ctx A (e:OExpr ctx A) :
  forall B pf, OExpr (substOTCtx ctx B pf) B -> OExpr (substOTCtx ctx B pf) A :=
  match e return
        forall B pf,
          OExpr (substOTCtx ctx B pf) B -> OExpr (substOTCtx ctx B pf) A
  with
  | OVar ctx A 





(* FIXME HERE NOW: old stuff below... *)

(***
 *** Building Proper Functions
 ***)

Class ProperPair (A:OType) (x y:A) : Prop :=
  proper_pair_pf : ot_R A x y.

Definition ot_Lambda {A B:OType} (f: A -> B)
           {prp:forall x y, ProperPair A x y -> ProperPair B (f x) (f y)}
  : OTarrow A B :=
  {| pfun_app := f; pfun_Proper := prp |}.

Instance ProperPair_refl (A:OType) (x:A) : ProperPair A x x.
Proof.
  unfold ProperPair. reflexivity.
Qed.

Instance ProperPair_pfun_app (A B:OType) (fl fr:OTarrow A B) argl argr
         (prpf:ProperPair (OTarrow A B) fl fr)
         (prpa:ProperPair A argl argr)
 : ProperPair B (pfun_app fl argl) (pfun_app fr argr).
Proof.
  apply prpf; assumption.
Qed.

Instance ProperPair_ot_lambda (A B:OType) (f g:A -> B) prpl prpr
         (pf: forall x y, ProperPair A x y -> ProperPair B (f x) (g y)) :
  ProperPair (OTarrow A B) (@ot_Lambda A B f prpl) (@ot_Lambda A B g prpr).
Proof.
  intros xl xr Rx; apply pf; assumption.
Qed.


(***
 *** Ordered Terms for Pair Operations
 ***)

Program Definition ofst {A B:OType} : OTarrow (OTpair A B) A :=
  @ot_Lambda (OTpair A B) A fst _.
Next Obligation.
  destruct H. assumption.
Qed.

Program Definition osnd {A B:OType} : OTarrow (OTpair A B) B :=
  @ot_Lambda (OTpair A B) _ snd _.
Next Obligation.
  destruct H. assumption.
Qed.

Program Definition opair {A B:OType} : OTarrow A (OTarrow B (OTpair A B)) :=
  @ot_Lambda
    A _
    (fun x =>
       @ot_Lambda
         B (OTpair A B)
         (fun y => pair x y)
         _)
    _.
Next Obligation.
  split; [ reflexivity | assumption ].
Qed.
Next Obligation.
  apply ProperPair_ot_lambda; intros. split; assumption.
Qed.


(***
 *** Notations for Ordered Types
 ***)

Notation "A '-o>' B" :=
  (OTarrow A B) (right associativity, at level 99).
Notation "A '*o*' B" :=
  (OTpair A B) (left associativity, at level 40).
Notation "A '+o+' B" :=
  (OTsum A B) (left associativity, at level 50).
Notation "'~o~' A" :=
  (OTflip A) (right associativity, at level 35).

Notation "x <o= y" :=
  (ot_R _ x y) (no associativity, at level 70).
Notation "x =o= y" :=
  (ot_equiv _ x y) (no associativity, at level 70).

Notation "x @o@ y" :=
  (pfun_app x y) (left associativity, at level 20).

Notation "( x ,o, y )" :=
  (opair @o@ x @o@ y)
    (no associativity, at level 0).

(* FIXME: why don't these work?
Notation "'ofun' ( x : A ) =o> t" :=
  (@ot_Lambda A _ (fun x => t))
    (at level 100, right associativity, x at level 99) : pterm_scope.

Notation "'ofun' x =o> t" :=
  (ot_Lambda (fun x => t))
    (at level 100, right associativity, x at level 99) : pterm_scope.
 *)

Notation ofun := ot_Lambda.


(***
 *** Automation for Ordered Terms
 ***)

(* Don't unfold ot_Lambda when simplifying  *)
Arguments ot_Lambda A B f prp : simpl never.

Instance Proper_ot_R_ot_R A :
  Proper (Basics.flip (ot_R A) ==> ot_R A ==> Basics.impl) (ot_R A).
Proof.
  intros x1 x2 Rx y1 y2 Ry R.
  transitivity x1; [ assumption | ]; transitivity y1; assumption.
Qed.

Instance Proper_ot_equiv_ot_R A :
  Proper (ot_equiv A ==> ot_equiv A ==> iff) (ot_R A).
Proof.
  intros x1 x2 Rx y1 y2 Ry; destruct Rx; destruct Ry; split; intro R.
  transitivity x1; [ assumption | ]; transitivity y1; assumption.
  transitivity x2; [ assumption | ]; transitivity y2; assumption.
Qed.

Instance Proper_ot_R_pfun_app A B :
  Proper (ot_R (A -o> B) ==> ot_R A ==> ot_R B) (@pfun_app A B).
Proof.
  intros f1 f2 Rf x1 x2 Rx. apply Rf; apply Rx.
Qed.

Instance Proper_ot_R_pfun_app_partial A B f :
  Proper (ot_R A ==> ot_R B) (@pfun_app A B f).
Proof.
  apply pfun_Proper.
Qed.


Create HintDb OT.

(* Split ot_equiv equalities into the left and right cases *)
Definition split_ot_equiv A (x y : ot_Type A)
           (pf1: x <o= y) (pf2 : y <o= x) : x =o= y :=
  conj pf1 pf2.

Hint Resolve split_ot_equiv : OT.

(* Extensionality for ot_R *)
Definition ot_arrow_ext (A B:OType) (f1 f2 : A -o> B)
           (pf:forall x y, x <o= y -> f1 @o@ x <o= f2 @o@ y) : f1 <o= f2 := pf.

Hint Resolve ot_arrow_ext : OT.

(* Add the above rules to the OT rewrite set *)
(* Hint Rewrite @mkOTerm_apply @ot_unlift_iso_OTForType_refl_id : OT. *)

(* Eta-equality for pairs *)
Lemma ot_pair_eta (A B:OType) (x : A *o* B) :
  @ot_equiv (A *o* B) (fst x , snd x) x.
  split; split; reflexivity.
Qed.

Hint Rewrite ot_pair_eta : OT.

(* Tactic to apply rewrites in the OT rewrite set *)
Ltac rewrite_OT := rewrite_strat (topdown (hints OT)).

(* General tactic to try to prove theorems about ordered terms *)
(*
Ltac prove_OT :=
  repeat first [simpl_mkOTerm_refl | simpl_mkOTerm_apply];
  try rewrite_OT;
  lazymatch goal with
  | |- ot_equiv _ _ _ => split
  | |- _ => idtac
  end.
  (* repeat (apply ot_arrow_ext; intros). *)
 *)


(***
 *** Examples of Ordered Terms
 ***)

Module OTExamples.

Definition ex1 : OTProp -o> OTProp := ot_Lambda (fun p => p).
(* Eval compute in (pfun_app ex1 : Prop -> Prop). *)

Definition ex2 {A} : (A -o> A) := ot_Lambda (fun p => p).
(* Eval simpl in (fun A:OType => pfun_app (@ex2 A) : A -> A). *)

Definition ex3 {A} : (A -o> A -o> A) :=
  ot_Lambda (fun p1 => ot_Lambda (fun p2 => p1)).
(* Eval simpl in (fun (A:OType) x => pfun_app (pfun_app (@ex3 A) x)). *)

Definition ex4 {A B} : (A *o* B -o> A) := ot_Lambda (fun p => ofst @o@ p).
(* Eval simpl in (fun (A B:OType) => pfun_app ex4 : A * B -> A). *)

Definition ex5 {A B} : A *o* B -o> B *o* A :=
  ot_Lambda (fun p => (osnd @o@ p ,o, ofst @o@ p)).
(* Eval simpl in (fun (A B:OType) => pfun_app ex5 : A *o* B -> B *o* A). *)

Definition ex6 {A B C} : A *o* B *o* C -o> C *o* A :=
  ot_Lambda (fun triple => (osnd @o@ triple ,o, ofst @o@ (ofst @o@ triple))).

Definition ex7 {A B C} : (A *o* B -o> C) -o> C -o> A -o> B -o> C :=
  ot_Lambda (fun (f:(A *o* B -o> C)) =>
               ot_Lambda
                 (fun (c:C) =>
                    ot_Lambda
                      (fun a =>
                         ot_Lambda (fun b => f @o@ (a ,o, b))))).

End OTExamples.
