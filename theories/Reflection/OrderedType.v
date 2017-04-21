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

(* NOTE: The idea with this approach is that each type uniquely determines its
ordered type, but we keep the types separate from the ordered types to make
type inference work properly... *)

Class OTRelation (A:Type) : Type := ot_R : relation A.
Class OType (A:Type) {R:OTRelation A} : Prop :=
  { ot_PreOrder :> PreOrder ot_R }.

Arguments OTRelation A%type.
Arguments OType A%type {R}.

Instance OType_Reflexive A `{OType A} : Reflexive ot_R.
Proof. typeclasses eauto. Qed.

Instance OType_Transitive A `{OType A} : Transitive ot_R.
Proof. typeclasses eauto. Qed.

(* The equivalence relation for an OrderedType *)
Definition ot_equiv {A} `{OTRelation A} : relation A :=
  fun x y => ot_R x y /\ ot_R y x.

Instance ot_equiv_Equivalence A `{OType A} : Equivalence ot_equiv.
Proof.
  constructor; intro; intros.
  { split; reflexivity. }
  { destruct H0; split; assumption. }
  { destruct H0; destruct H1; split; transitivity y; assumption. }
Qed.

Notation "x <o= y" :=
  (ot_R x y) (no associativity, at level 70).
Notation "x =o= y" :=
  (ot_equiv x y) (no associativity, at level 70).

(* FIXME: replace "ot_R" below with "<o=" notation *)

(* FIXME: figure out what versions of this we need for rewriting! *)
Instance Proper_ot_R_ot_R A `{OType A}
  : Proper (ot_R --> ot_R ==> Basics.impl) (@ot_R A _).
Proof.
  intros a1 a2 Ra b1 b2 Rb Rab.
  transitivity a1; [ assumption | ]. transitivity b1; assumption.
Qed.

Instance Subrelation_ot_equiv_ot_R A `{OType A} : subrelation (@ot_equiv A _) ot_R.
Proof.
  intros a1 a2 Ra; destruct Ra; assumption.
Qed.

Instance Proper_ot_equiv_ot_R A `{OType A} :
  Proper (ot_equiv ==> ot_equiv ==> iff) (@ot_R A _).
Proof.
  intros x1 x2 Rx y1 y2 Ry; destruct Rx; destruct Ry; split; intro Rxy.
  transitivity x1; [ assumption | ]; transitivity y1; assumption.
  transitivity x2; [ assumption | ]; transitivity y2; assumption.
Qed.

Instance Proper_ot_equiv A `{OType A} :
  Proper (ot_equiv ==> ot_equiv ==> iff) (@ot_equiv A _).
Proof.
  intros x1 x2 Rx y1 y2 Ry. rewrite Rx. rewrite Ry. reflexivity.
Qed.

Instance Proper_ot_equiv_partial A `{OType A} a :
  Proper (ot_equiv ==> Basics.flip Basics.impl) (@ot_equiv A _ a).
Proof.
  intros x1 x2 Rx. rewrite Rx. reflexivity.
Qed.


(***
 *** Commonly-Used Ordered Types
 ***)

(* The ordered type of propositions *)
Instance OTProp_R : OTRelation Prop := Basics.impl.
Instance OTProp : OType Prop.
Proof. repeat constructor; typeclasses eauto. Qed.

(* The discrete ordered type, where things are only related to themselves; we
make this a definition, not an instance, so that it can be instantiated for
particular types. *)
Definition OTdiscrete_R (A:Type) : OTRelation A := eq.
Definition OTdiscrete A : @OType A (OTdiscrete_R A).
  repeat constructor. typeclasses eauto.
Qed.

(* The only ordered type over unit is the discrete one *)
Instance OTunit_R : OTRelation unit := OTdiscrete_R unit.
Instance OTunit : OType unit := OTdiscrete unit.

(* The ordered type that flips the ordering of an underlying OType; this becomes
a type itself in Coq *)
Inductive Flip A : Type := flip (a:A).
Definition unflip {A} (f:Flip A) : A := let (x) := f in x.

Instance OTFlip_R A (R:OTRelation A) : OTRelation (Flip A) :=
  fun x y => unflip y <o= unflip x.

Instance OTFlip A `{OType A} : OType (Flip A).
Proof.
  repeat constructor; intro; intros.
  - destruct x; compute; reflexivity.
  - destruct x; destruct y; destruct z; compute; transitivity a0; assumption.
Qed.

(* The pointwise relation on pairs *)
Instance OTpair_R A B (RA:OTRelation A) (RB:OTRelation B) : OTRelation (A*B) :=
  fun p1 p2 => ot_R (fst p1) (fst p2) /\ ot_R (snd p1) (snd p2).

Instance OTpair A B `(OType A) `(OType B) : OType (A*B).
Proof.
  repeat constructor.
  - destruct x. reflexivity.
  - destruct x. reflexivity.
  - destruct x; destruct y; destruct z; destruct H1; destruct H2;
      transitivity a0; assumption.
  - destruct x; destruct y; destruct z; destruct H1; destruct H2;
      transitivity b0; assumption.
Qed.


(* The sort-of pointwise relation on sum types *)
Inductive sumR {A B} (RA:OTRelation A) (RB:OTRelation B) : A+B -> A+B -> Prop :=
| sumR_inl a1 a2 : RA a1 a2 -> sumR RA RB (inl a1) (inl a2)
| sumR_inr b1 b2 : RB b1 b2 -> sumR RA RB (inr b1) (inr b2).

Instance OTsum_R A B (RA:OTRelation A) (RB:OTRelation B) : OTRelation (A+B) :=
  sumR RA RB.

Instance OTsum A B `(OType A) `(OType B) : OType (A+B).
Proof.
  repeat constructor; intro; intros.
  { destruct x; constructor; reflexivity. }
  { destruct H1; inversion H2.
    - constructor; transitivity a2; assumption.
    - constructor; transitivity b2; assumption. }
Qed.


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
 *** Proper Instances for Simple Ordered Types
 ***)

Instance Proper_pair A B `{OTRelation A} `{OTRelation B} :
  Proper (ot_R ==> ot_R ==> ot_R) (pair : A -> B -> A*B).
Proof.
  repeat intro; split; assumption.
Qed.

Instance Proper_fst A B `{OTRelation A} `{OTRelation B} :
  Proper (ot_R ==> ot_R) (fst : A*B -> A).
Proof.
  intros p1 p2 Rp; destruct Rp; assumption.
Qed.

Instance Proper_snd A B `{OTRelation A} `{OTRelation B} :
  Proper (ot_R ==> ot_R) (snd : A*B -> B).
Proof.
  intros p1 p2 Rp; destruct Rp; assumption.
Qed.



(***
 *** The Ordered Type for Functions
 ***)

(* The type of continuous, i.e. Proper, functions between ordered types *)
Record Pfun A B {RA:OTRelation A} {RB:OTRelation B} :=
  {
    pfun_app : A -> B;
    pfun_Proper : Proper (ot_R ==> ot_R) pfun_app
  }.

Arguments pfun_app {_ _ _ _} _ _.
Arguments pfun_Proper [_ _ _ _] _ _ _ _.

Notation "A '-o>' B" :=
  (Pfun A B) (right associativity, at level 99).
Notation "x @o@ y" :=
  (pfun_app x y) (left associativity, at level 20).

(* The non-dependent function ordered type *)
Instance OTarrow_R A B {RA:OTRelation A} {RB:OTRelation B} : OTRelation (A -o> B) :=
  fun f g =>
    forall a1 a2, ot_R a1 a2 -> ot_R (pfun_app f a1) (pfun_app g a2).

Instance OTarrow A B `{OType A} `{OType B} : OType (A -o> B).
Proof.
  repeat constructor; intro; intros; intro; intros.
  { apply pfun_Proper; assumption. }
  { transitivity (pfun_app y a1).
    - apply H1; reflexivity.
    - apply H2; assumption. }
Qed.


(* FIXME: could also do a forall type, but need the second type argument, B, to
itself be proper, i.e., to be an element of OTarrow A OType. *)


(* pfun_app is always Proper *)
Instance Proper_pfun_app A B `{OTRelation A} `{OTRelation B} :
  Proper (ot_R ==> ot_R ==> ot_R) (@pfun_app A B _ _).
Proof.
  intros f1 f2 Rf a1 a2 Ra. apply Rf; assumption.
Qed.

(* pfun_app is always Proper w.r.t. ot_equiv *)
Instance Proper_pfun_app_equiv A B `{OTRelation A} `{OTRelation B} :
  Proper (ot_equiv ==> ot_equiv ==> ot_equiv) (@pfun_app A B _ _).
Proof.
  intros f1 f2 Rf a1 a2 Ra; destruct Rf; destruct Ra.
  split; apply Proper_pfun_app; assumption.
Qed.

Instance Proper_pfun_app_partial A B `{OTRelation A} `{OTRelation B} f :
  Proper (ot_R ==> ot_R) (pfun_app (A:=A) (B:=B) f).
Proof.
  apply pfun_Proper.
Qed.

Instance Proper_pfun_app_partial_equiv A B `{OTRelation A} `{OTRelation B} f :
  Proper (ot_equiv ==> ot_equiv) (@pfun_app A B _ _ f).
Proof.
  intros a1 a2 Ra; destruct Ra; split; apply pfun_Proper; assumption.
Qed.


(***
 *** Some Useful Pfuns
 ***)

(* The identity pfun *)
Definition id_pfun {A} `{OTRelation A} : A -o> A :=
  {| pfun_app := fun x => x; pfun_Proper := fun x1 x2 Rx => Rx |}.

(* The identity pfun *)
Program Definition compose_pfun {A B C}
        `{OTRelation A} `{OTRelation B} `{OTRelation C}
        (f:A -o> B) (g:B -o> C) : A -o> C :=
  {| pfun_app := fun x => pfun_app g (pfun_app f x);
     pfun_Proper := _ |}.
Next Obligation.
  intros x1 x2 Rx. apply pfun_Proper. apply pfun_Proper. assumption.
Qed.

Instance Proper_compose_pfun A B C
         `{OTRelation A} `{OTRelation B} `{OTRelation C} :
  Proper (ot_R ==> ot_R ==> ot_R) (@compose_pfun A B C _ _ _).
  intros f1 f2 Rf g1 g2 Rg a1 a2 Ra.
  apply Rg. apply Rf. assumption.
Qed.

Instance Proper_compose_pfun_equiv A B C
         `{OTRelation A} `{OTRelation B} `{OTRelation C} :
  Proper (ot_equiv ==> ot_equiv ==> ot_equiv) (@compose_pfun A B C _ _ _).
Proof.
  intros f1 f2 Rf g1 g2 Rg.
  split; intros a1 a2 Ra; simpl; apply Rg; apply Rf; apply Ra.
Qed.

(* Category theory laws for Pfuns *)
Lemma id_compose_pfun A B `{OTRelation A} `{OTRelation B} (f: A -o> B) :
  ot_equiv (compose_pfun id_pfun f) f.
  split; intros a1 a2 Ra; simpl; apply pfun_Proper; assumption.
Qed.
Lemma compose_id_pfun A B `{OTRelation A} `{OTRelation B} (f: A -o> B) :
  ot_equiv (compose_pfun f id_pfun) f.
  split; intros a1 a2 Ra; simpl; apply pfun_Proper; assumption.
Qed.
Lemma compose_compose_pfun A B C D
      `{OTRelation A} `{OTRelation B} `{OTRelation C} `{OTRelation D}
      (f: A -o> B) (g: B -o> C) (h: C -o> D) :
  ot_equiv (compose_pfun f (compose_pfun g h)) (compose_pfun (compose_pfun f g) h).
  split; intros a1 a2 Ra; simpl; repeat apply pfun_Proper; assumption.
Qed.

(* The constant pfun *)
Program Definition const_pfun {A B} `{OTRelation A} `{OType B} b : A -o> B :=
  {| pfun_app := fun _ => b; pfun_Proper := fun _ _ _ => ltac:(reflexivity) |}.

Instance Proper_const_pfun {A B} `{OTRelation A} `{OType B} :
  Proper (ot_R ==> ot_R) (const_pfun (A:=A) (B:=B)).
Proof.
  intros b1 b2 Rb a1 a2 Ra. apply Rb.
Qed.

Instance Proper_const_pfun_equiv {A B} `{OTRelation A} `{OType B} :
  Proper (ot_equiv ==> ot_equiv) (const_pfun (A:=A) (B:=B)).
Proof.
  intros b1 b2 Rb; split; intros a1 a2 Ra; apply Rb.
Qed.

(* Composing with the constant pfun on the left *)
Lemma compose_const_pfun_f A B C `{OTRelation A} `{OType B} `{OType C}
      b (f : B -o> C) :
  ot_equiv (compose_pfun (const_pfun (A:=A) b) f) (const_pfun (pfun_app f b)).
  split; intros a1 a2 Ra; reflexivity.
Qed.

(* Composing with the constant pfun on the right *)
Lemma compose_f_const_pfun A B C `{OTRelation A} `{OType B} `{OType C}
      (f : A -o> B) c :
  ot_equiv (compose_pfun f (const_pfun c)) (const_pfun c).
  split; intros a1 a2 Ra; reflexivity.
Qed.


(* Take the pair of the outputs of two pfuns *)
Program Definition pair_pfun {A B C}
        `{OTRelation A} `{OTRelation B} `{OTRelation C}
        (f: A -o> B) (g: A -o> C) : A -o> (B * C) :=
  {| pfun_app := fun a => (pfun_app f a, pfun_app g a) |}.
Next Obligation.
  intros a1 a2 Ra; split; apply pfun_Proper; assumption.
Qed.

Instance Proper_pair_pfun A B C `{OTRelation A} `{OTRelation B} `{OTRelation C} :
  Proper (ot_R ==> ot_R ==> ot_R) (pair_pfun (A:=A) (B:=B) (C:=C)).
Proof.
  intros a1 a2 Ra b1 b2 Rb c1 c2 Rc; simpl; split.
  - apply Ra; assumption.
  - apply Rb; assumption.
Qed.

Instance Proper_pair_pfun_equiv A B C
         `{OTRelation A} `{OTRelation B} `{OTRelation C} :
  Proper (ot_equiv ==> ot_equiv ==> ot_equiv)
         (pair_pfun (A:=A) (B:=B) (C:=C)).
Proof.
  intros a1 a2 Ra b1 b2 Rb.
  destruct Ra as [ Ra1 Ra2 ]; destruct Rb as [ Rb1 Rb2 ].
  split; intros c1 c2 Rc; split; simpl;
    first [ apply Ra1 | apply Ra2 | apply Rb1 | apply Rb2 ]; assumption.
Qed.

(* compose commutes with pair *)
Lemma compose_f_pair_pfun A B C D
      `{OTRelation A} `{OTRelation B} `{OTRelation C} `{OTRelation D}
      (f: A -o> B) (g: B -o> C) (h: B -o> D) :
  ot_equiv (compose_pfun f (pair_pfun g h))
           (pair_pfun (compose_pfun f g) (compose_pfun f h)).
  split; intros a1 a2 Ra; simpl; split; repeat apply pfun_Proper; assumption.
Qed.

(* The first projection pfun *)
Definition fst_pfun {A B} `{OTRelation A} `{OTRelation B} : A * B -o> A :=
  {| pfun_app := fst; pfun_Proper := _ |}.

(* The second projection pfun *)
Definition snd_pfun {A B} `{OTRelation A} `{OTRelation B} : A * B -o> B :=
  {| pfun_app := snd; pfun_Proper := _ |}.

(* Composing pair with fst gives the first function in the pair *)
Lemma compose_pair_fst A B C `{OTRelation A} `{OTRelation B} `{OTRelation C}
      (f: A -o> B) (g: A -o> C) :
  ot_equiv (compose_pfun (pair_pfun f g) fst_pfun) f.
  split; intros a1 a2 Ra; simpl; apply pfun_Proper; assumption.
Qed.

(* Composing pair with snd gives the second function in the pair *)
Lemma compose_pair_snd A B C `{OTRelation A} `{OTRelation B} `{OTRelation C}
      (f: A -o> B) (g: A -o> C) :
  ot_equiv (compose_pfun (pair_pfun f g) snd_pfun) g.
  split; intros a1 a2 Ra; simpl; apply pfun_Proper; assumption.
Qed.

(* Taking the pair of fst and snd is the identity *)
Lemma pair_fst_snd_eta A B `{OTRelation A} `{OTRelation B} :
  ot_equiv (pair_pfun (fst_pfun (A:=A) (B:=B)) snd_pfun) id_pfun.
  split; intros p1 p2 Rp; destruct Rp; split; simpl; assumption.
Qed.


(* Curry a Pfun *)
Program Definition pfun_curry {A B C} `{OType A} `{OTRelation B} `{OTRelation C}
        (pfun : (A * B) -o> C)
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
Program Definition pfun_uncurry {A B C}
        `{OTRelation A} `{OTRelation B} `{OTRelation C}
        (pfun : A -o> (B -o> C))
  : (A * B) -o> C :=
  {| pfun_app :=
       fun ab => pfun_app (pfun_app pfun (fst ab)) (snd ab);
     pfun_Proper := _ |}.
Next Obligation.
Proof.
  intros ab1 ab2 Rab. destruct Rab as [ Ra Rb ].
  exact (pfun_Proper pfun (fst ab1) (fst ab2) Ra (snd ab1) (snd ab2) Rb).
Qed.


(* pfun_curry is Proper *)
Instance Proper_pfun_curry A B C `{OType A} `{OTRelation B} `{OTRelation C}
  : Proper (ot_R ==> ot_R) (pfun_curry (A:=A) (B:=B) (C:=C)).
Proof.
  intros f1 f2 Rf a1 a2 Ra b1 b2 Rb. apply Rf. split; assumption.
Qed.

(* pfun_curry is Proper w.r.t. equivalence *)
Instance Proper_pfun_curry_equiv A B C `{OType A} `{OTRelation B} `{OTRelation C} :
  Proper (ot_equiv ==> ot_equiv) (pfun_curry (A:=A) (B:=B) (C:=C)).
Proof.
  intros f1 f2 Rf; destruct Rf; split; apply Proper_pfun_curry; assumption.
Qed.

(* FIXME: Proper instance for pfun_uncurry *)

(* Currying and uncurrying of pfuns form an isomorphism: part 1 *)
Lemma pfun_curry_uncurry_eq A B C `{OType A} `{OTRelation B} `{OTRelation C}
      (f: (A * B) -o> C) :
  pfun_uncurry (pfun_curry f) =o= f.
  split; intros ab1 ab2 Rab; simpl; apply pfun_Proper;
    destruct Rab; split; assumption.
Qed.

(* Currying and uncurrying of pfuns form an isomorphism: part 2 *)
Lemma pfun_uncurry_curry_eq A B C `{OType A} `{OTRelation B} `{OTRelation C}
      (f: A -o> B -o> C) :
  pfun_curry (pfun_uncurry f) =o= f.
  split; intros a1 a2 Ra b1 b2 Rb; simpl; apply Proper_pfun_app;
    try apply pfun_Proper; assumption.
Qed.


(* The S combinator for pfuns (FIXME: do we need this?) *)
Program Definition pfun_S {A B C} `{OTRelation A} `{OTRelation B} `{OTRelation C}
  : (A -o> B -o> C) -o> (A -o> B) -o> A -o> C :=
  {| pfun_app :=
       fun f =>
         {| pfun_app :=
              fun g =>
                {| pfun_app := fun a => pfun_app (pfun_app f a) (pfun_app g a) |}
         |}
  |}.
Next Obligation.
  intros a1 a2 Ra; apply Proper_pfun_app; try apply pfun_Proper; assumption.
Qed.
Next Obligation.
  intros g1 g2 Rg a1 a2 Ra. simpl. apply Proper_pfun_app; try assumption.
  - apply pfun_Proper; assumption.
  - apply Rg; assumption.
Qed.
Next Obligation.
  intros f1 f2 Rf g1 g2 Rg a1 a2 Ra. simpl. apply Proper_pfun_app; try assumption.
  - apply Rf; assumption.
  - apply Rg; assumption.
Qed.

(* This is the S combinator, but partially applied *)
Program Definition pfun_apply {A B C}
        `{OTRelation A} `{OTRelation B} `{OTRelation C}
        (f: A -o> B -o> C) (g: A -o> B) : A -o> C :=
  {| pfun_app := fun a => pfun_app (pfun_app f a) (pfun_app g a) |}.
Next Obligation.
  intros a1 a2 Ra; apply Proper_pfun_app; try apply pfun_Proper; assumption.
Qed.

Instance Proper_pfun_apply A B C `{OTRelation A} `{OTRelation B} `{OTRelation C} :
  Proper (ot_R ==> ot_R ==> ot_R) (pfun_apply (A:=A) (B:=B) (C:=C)).
Proof.
  intros a1 a2 Ra b1 b2 Rb c1 c2 Rc. simpl.
  apply Ra; try assumption. apply Rb; try assumption.
Qed.

Instance Proper_pfun_apply_equiv A B C
         `{OTRelation A} `{OTRelation B} `{OTRelation C} :
  Proper (ot_equiv ==> ot_equiv ==> ot_equiv) (pfun_apply (A:=A) (B:=B) (C:=C)).
Proof.
  intros a1 a2 Ra b1 b2 Rb; split; intros c1 c2 Rc; simpl;
    apply Ra; try apply Rb; assumption.
Qed.

(* compose commutes with S *)
Lemma compose_pfun_apply A B C D `{OType A} `{OType B} `{OType C} `{OType D}
      (f : A -o> B) (g: B -o> C -o> D) h :
  compose_pfun f (pfun_apply g h)
  =o= pfun_apply (compose_pfun f g) (compose_pfun f h).
  split; intros a1 a2 Ra; simpl; rewrite Ra; reflexivity.
Qed.

(* compose commutes with currying *)
Lemma compose_pfun_curry A B C D `{OType A} `{OType B} `{OType C} `{OType D}
      (f: A -o> B) (g: B * C -o> D) :
  ot_equiv (compose_pfun f (pfun_curry g))
           (pfun_curry
              (compose_pfun (pair_pfun (compose_pfun fst_pfun f) snd_pfun) g)).
  split; intros a1 a2 Ra c1 c2 Rc; simpl; rewrite Ra; rewrite Rc; reflexivity.
Qed.

(* Applying a const is just composition *)
Lemma pfun_apply_const A B C `{OType A} `{OType B} `{OType C}
      (f: B -o> C) (g: A -o> B) :
  ot_equiv (pfun_apply (A:=A) (const_pfun f) g) (compose_pfun g f).
  split; intros a1 a2 Ra; simpl; rewrite Ra; reflexivity.
Qed.

(* We can simplify pfun_S used with pfun_curry *)
Lemma pfun_apply_pfun_curry A B C `{OType A} `{OType B} `{OType C} f g :
  ot_equiv (pfun_apply (A:=A) (B:=B) (C:=C) (pfun_curry f) g)
           (compose_pfun (pair_pfun id_pfun g) f).
  split; intros a1 a2 Ra; simpl; apply pfun_Proper; split;
    try apply pfun_Proper; assumption.
Qed.

(* The pair constructor as a pfun *)
Program Definition pair_ctor_pfun {A B} `{OType A} `{OType B}
  : A -o> B -o> A * B :=
  {| pfun_app := fun a => {| pfun_app := fun b => (a,b) |} |}.
Next Obligation.
  intros b1 b2 Rb; rewrite Rb; reflexivity.
Qed.
Next Obligation.
  intros a1 a2 Ra b1 b2 Rb; simpl; rewrite Ra; rewrite Rb; reflexivity.
Qed.

(* Applying pair_ctor_pfun yields a pair_pfun *)
Lemma apply_pair_ctor_pfun {A B C} `{OType A} `{OType B} `{OType C}
      (f: A -o> B) (g: A -o> C) :
  ot_equiv (pfun_apply (pfun_apply (const_pfun pair_ctor_pfun) f) g)
           (pair_pfun f g).
  split; intros a1 a2 Ra; simpl; rewrite Ra; reflexivity.
Qed.


(***
 *** Building Proper Functions
 ***)

Class ProperPair A `{OTRelation A} (x y:A) : Prop :=
  proper_pair_pf : ot_R x y.

Definition ofun {A B} `{OTRelation A} `{OTRelation B} (f: A -> B)
           {prp:forall x y, ProperPair A x y -> ProperPair B (f x) (f y)}
  : A -o> B :=
  {| pfun_app := f; pfun_Proper := prp |}.

Instance ProperPair_refl A `{OType A} (x:A) : ProperPair A x x.
Proof.
  unfold ProperPair. reflexivity.
Qed.

Instance ProperPair_pfun_app A B `{OType A} `{OType B}
         (fl fr:A -o> B) argl argr
         (prpf:ProperPair (A -o> B) fl fr)
         (prpa:ProperPair A argl argr)
 : ProperPair B (pfun_app fl argl) (pfun_app fr argr).
Proof.
  apply prpf; assumption.
Qed.

Instance ProperPair_ofun A B `{OType A} `{OType B} (f g:A -> B) prpl prpr
         (pf: forall x y, ProperPair A x y -> ProperPair B (f x) (g y)) :
  ProperPair (A -o> B) (@ofun A B _ _ f prpl) (@ofun A B _ _ g prpr).
Proof.
  intros xl xr Rx; apply pf; assumption.
Qed.


(***
 *** Ordered Terms and ProperPair Instances for Pair Operations
 ***)

(* Proper function for fst *)
Definition ofst {A B} `{OTRelation A} `{OTRelation B} : A * B -o> A :=
  {| pfun_app := fst; pfun_Proper := _ |}.

(* Proper function for snd *)
Definition osnd {A B} `{OTRelation A} `{OTRelation B} : A * B -o> B :=
  {| pfun_app := snd; pfun_Proper := _ |}.

(* Proper function for pair *)
Program Definition opair {A B} `{OType A} `{OType B} : A -o> B -o> A * B :=
  {| pfun_app :=
       fun a => {| pfun_app := fun b => pair a b;
                   pfun_Proper := _ |};
     pfun_Proper := _ |}.
Next Obligation.
  intros b1 b2 Rb. split; [ reflexivity | assumption ].
Qed.
Next Obligation.
  intros a1 a2 Ra b1 b2 Rb. split; assumption.
Qed.

(* Notation for proper pairs *)
Notation "( x ,o, y )" := (opair @o@ x @o@ y) (at level 0).

(* FIXME: get this notation to work *)
(*
Notation "( x ,o, y ,o, .. ,o, z )" :=
  (pfun_app opair .. (pfun_app (pfun_app opair x) y) .. z)
                                         (at level 0).
*)

(*
Instance ProperPair_fst A B `{OType A} `{OType B} (p1 p2: A*B)
         (pf: ProperPair (A*B) p1 p2) :
  ProperPair A (fst p1) (fst p2).
Proof.
  destruct pf; assumption.
Qed.

Instance ProperPair_snd A B `{OType A} `{OType B} (p1 p2: A*B)
         (pf: ProperPair (A*B) p1 p2) :
  ProperPair B (snd p1) (snd p2).
Proof.
  destruct pf; assumption.
Qed.

Instance ProperPair_pair A B `{OType A} `{OType B}
         (x1 x2:A) (y1 y2:B) (pfx: ProperPair A x1 x2) (pfy: ProperPair B y1 y2) :
  ProperPair (A*B) (pair x1 y1) (pair x2 y2).
Proof.
  split; assumption.
Qed.
 *)


(***
 *** Notations for Ordered Types
 ***)

(* FIXME: why don't these work?
Notation "'pfun' ( x : A ) =o> t" :=
  (@ot_Lambda A _ (fun x => t))
    (at level 100, right associativity, x at level 99) : pterm_scope.

Notation "'pfun' x =o> t" :=
  (ot_Lambda (fun x => t))
    (at level 100, right associativity, x at level 99) : pterm_scope.
 *)


(***
 *** Ordered Type Functions
 ***)

(*
Definition ot_fun_app (TF: forall A `{OType A}, Type) A `{OType A} := TF A.

Notation "F @t@ A" :=
  (ot_fun_app F A%type) (left associativity, at level 20).
*)

Class OTRelationF (TF: forall A `{OType A}, Type) : Type :=
  ot_rel_app : forall A `{OType A}, OTRelation (TF A).

Instance OTRelation_ot_rel_app TF `(OTRelationF TF) A `(OType A) :
  OTRelation (TF A _ _) := ot_rel_app A.

Class OTypeF (TF: forall A `{OType A}, Type) `{OTRelationF TF} : Prop :=
  otype_app : forall A `{OType A}, OType (TF A).

Instance OType_otype_app TF `(OTypeF TF) A `(OType A) :
  OType (TF A _ _) := otype_app A.


(***
 *** Examples of Ordered Terms
 ***)

Module OTExamples.

Definition ex1 : Prop -o> Prop := ofun (fun p => p).
(* Eval compute in (pfun_app ex1 : Prop -> Prop). *)

Definition ex2 {A} `{OType A} : A -o> A := ofun (fun p => p).
(* Eval simpl in (fun A `{OType A} => pfun_app (@ex2 A _ _) : A -> A). *)

Definition ex3 {A} `{OType A} : A -o> A -o> A :=
  ofun (fun p1 => ofun (fun p2 => p1)).
(* Eval simpl in (fun (A:OType) x => pfun_app (pfun_app (@ex3 A) x)). *)

Definition ex4 {A B} `{OType A} `{OType B} : (A * B -o> A) :=
  ofun (fun p => ofst @o@ p).
(* Eval simpl in (fun {A B} `{OType A} `{OType B} =>
                 pfun_app ex4 : A * B -> A). *)

Definition ex5 {A B} `{OType A} `{OType B} : A * B -o> B * A :=
  ofun (fun p => (osnd @o@ p ,o, ofst @o@ p)).
(* Eval simpl in (fun {A B} `{OType A} `{OType B} =>
                 pfun_app ex5 : A * B -> B * A). *)

Definition ex6 {A B C} `{OType A} `{OType B} `{OType C} : A * B * C -o> C * A :=
  ofun (fun triple => (osnd @o@ triple ,o, ofst @o@ (ofst @o@ triple))).

Definition ex7 {A B C} `{OType A} `{OType B} `{OType C}
  : (A * B -o> C) -o> C -o> A -o> B -o> C :=
  ofun (fun f =>
               ofun
                 (fun c =>
                    ofun
                      (fun a =>
                         ofun (fun b => f @o@ (a ,o, b))))).

End OTExamples.
