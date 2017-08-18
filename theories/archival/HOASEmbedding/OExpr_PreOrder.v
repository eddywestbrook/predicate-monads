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

Instance Subrelation_ot_equiv_ot_R A `{OTRelation A} :
  subrelation (@ot_equiv A _) ot_R.
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

Instance Proper_pair_equiv A B `{OTRelation A} `{OTRelation B} :
  Proper (ot_equiv ==> ot_equiv ==> ot_equiv) (pair : A -> B -> A*B).
Proof.
  intros a1 a2 Ra b1 b2 Rb; destruct Ra; destruct Rb; split; split; assumption.
Qed.

Instance Proper_fst A B `{OTRelation A} `{OTRelation B} :
  Proper (ot_R ==> ot_R) (fst : A*B -> A).
Proof.
  intros p1 p2 Rp; destruct Rp; assumption.
Qed.

Instance Proper_fst_equiv A B `{OTRelation A} `{OTRelation B} :
  Proper (ot_equiv ==> ot_equiv) (fst : A*B -> A).
Proof.
  intros p1 p2 Rp. destruct Rp.
  split; eapply Proper_fst; assumption.
Qed.

Instance Proper_snd A B `{OTRelation A} `{OTRelation B} :
  Proper (ot_R ==> ot_R) (snd : A*B -> B).
Proof.
  intros p1 p2 Rp; destruct Rp; assumption.
Qed.

Instance Proper_snd_equiv A B `{OTRelation A} `{OTRelation B} :
  Proper (ot_equiv ==> ot_equiv) (snd : A*B -> B).
Proof.
  intros p1 p2 Rp. destruct Rp.
  split; eapply Proper_snd; assumption.
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
 *** Ordered Expressions
 ***)

(* Helper typeclass to control instantiation of Proper instances when we build
Proper functions in OExpr types *)
Class ProperPfun {A B} {RA:OTRelation A} {RB:OTRelation B} f : Prop :=
  properPFun : Proper (RA ==> RB) f.

(* Helper for building pfuns *)
Definition mkPfun {A B RA RB} f (prp:@ProperPfun A B RA RB f) : A -o> B :=
  {| pfun_app := f; pfun_Proper := prp |}.

Inductive OExpr : forall A {RA:OTRelation A} (a1 a2:A), Type :=
| Embed {A} {RA:OTRelation A} {a1 a2:A} (Ra:RA a1 a2) :
    @OExpr A RA a1 a2
| App {A B} {RA:OTRelation A} {RB:OTRelation B} {f1 f2 a1 a2}
       (e1: OExpr (A -o> B) f1 f2) (e2: OExpr A a1 a2) :
    OExpr B (f1 @o@ a1) (f2 @o@ a2)
| Lam {A B} {RA:OTRelation A} {RB:OTRelation B} {f1 f2}
      (e: forall (a1 a2:A), RA a1 a2 -> OExpr B (f1 a1) (f2 a2))
      {prp1 prp2} :
    OExpr (A -o> B) (mkPfun f1 prp1) (mkPfun f2 prp2)
.

(* An ordered expression is always indexed by related objects *)
Lemma Parametricity {A RA a1 a2} (e:@OExpr A RA a1 a2) : RA a1 a2.
Proof.
  induction e.
  - assumption.
  - apply Proper_pfun_app; assumption.
  - exact H.
Qed.


FIXME HERE NOW: this is not going to work!!


(* Instance to build a ProperPfun for the first function in a Lam constructor *)
Instance ProperPfun_Lam1 {A B} {RA:OTRelation A} {RB:OTRelation B} {f1 f2}
         (e: forall (a1 a2:A), RA a1 a2 -> OExpr B (f1 a1) (f2 a2)) :
  ProperPfun f1.
Proof.
  intros a1 a2 Ra. apply Parametricity. apply e.

Definition mkLam {A B} {RA:OTRelation A} {RB:OTRelation B} {f1 f2}
           (f: forall {a1 a2}, OExpr A a1 a2 -> OExpr B (f1 a1) (f2 a2)) :
  OExpr (A -> B) f1 f2 :=
  Lam (fun a1 a2 Ra => f (Embed Ra)).

Definition OConst A {RA:OTRelation A} {a} : Prop :=
  Proper RA a.

Definition ott : @OConst unit _ tt := eq_refl.

Definition opair {A} {RA:OTRelation A} {B} {RB:OTRelation B} :
  @OConst _ _ (pair (A:=A) (B:=B)).
Proof.
  repeat intro; split; assumption.
Qed.

Definition ofst A {RA:OTRelation A} B {RB:OTRelation B} :
  @OConst _ _ (fst (A:=A) (B:=B)).
Proof.
  intros p1 p2 Rp; destruct Rp; assumption.
Qed.


Check (fun A {RA:OTRelation A} => mkLam (fun (_:A) _ x => x)).
Check (mkLam (A:=unit) (fun _ _ x => Embed ott)).
Check (mkLam (A:=unit -> unit) (fun _ _ f => App f (Embed ott))).
Check (mkLam (fun _ _ f =>
                App f (App (App (Embed opair) (Embed ott)) (Embed ott)))).
