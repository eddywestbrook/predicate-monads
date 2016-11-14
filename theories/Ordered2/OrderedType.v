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
    ot_Type : Type;
    ot_R :> relation ot_Type;
    ot_PreOrder :> PreOrder ot_R
  }.

Instance OType_Reflexive (A:OType) : Reflexive (ot_R A).
Proof.
  destruct A; auto with typeclass_instances.
Qed.

Instance OType_Transitive (A:OType) : Transitive (ot_R A).
Proof.
  destruct A; auto with typeclass_instances.
Qed.

(* The equivalence relation for an OrderedType *)
Definition ot_equiv (A:OType) : relation (ot_Type A) :=
  fun x y => ot_R A x y /\ ot_R A y x.

Instance ot_equiv_Equivalence A : Equivalence (ot_equiv A).
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
    ot_R := fun x y => ot_R A y x
  |}.
Next Obligation.
  constructor.
  { intro x. reflexivity. }
  { intros x y z; transitivity y; assumption. }
Qed.

(* The pointwise relation on pairs *)
Definition pairR {A B} (RA:relation A) (RB:relation B) : relation (A*B) :=
  fun p1 p2 => RA (fst p1) (fst p2) /\ RB (snd p1) (snd p2).

(* The non-dependent product ordered type, where pairs are related pointwise *)
Program Definition OTpair (A:OType) (B: OType) : OType :=
  {|
    ot_Type := ot_Type A * ot_Type B;
    ot_R := pairR A B;
  |}.
Next Obligation.
  constructor.
  { intro p; split; reflexivity. }
  { intros p1 p2 p3 R12 R23; destruct R12; destruct R23; split.
    - transitivity (fst p2); assumption.
    - transitivity (snd p2); assumption. }
Qed.

(* The sort-of pointwise relation on sum types *)
Definition sumR {A B} (RA:relation A) (RB:relation B) : relation (A+B) :=
  fun sum1 sum2 =>
    match sum1, sum2 with
    | inl x, inl y => RA x y
    | inl x, inr y => False
    | inr x, inl y => False
    | inr x, inr y => RB x y
    end.

(* The non-dependent sum ordered type, where objects are only related if they
are both "left"s or both "right"s *)
Program Definition OTsum (A B : OType) : OType :=
  {|
    ot_Type := ot_Type A + ot_Type B;
    ot_R := sumR A B
  |}.
Next Obligation.
  constructor.
  { intro s; destruct s; simpl; reflexivity. }
  { intros s1 s2 s3 R12 R23.
    destruct s1; destruct s2; destruct s3;
      try (elimtype False; assumption); simpl.
    - transitivity o0; assumption.
    - transitivity o0; assumption. }
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
 *** The Ordered Type for Functions
 ***)

(* The type of continuous, i.e. Proper, functions between ordered types *)
Record Pfun (A:OType) (B: OType) :=
  {
    pfun_app : ot_Type A -> ot_Type B;
    pfun_Proper :> Proper (ot_R A ==> ot_R B) pfun_app
  }.

Arguments pfun_app [_ _] _ _.
Arguments pfun_Proper [_ _] _ _ _ _.

(* Infix "@" := pfun_app (at level 50). *)

(* The non-dependent function ordered type *)
Definition OTarrow_R (A B : OType) : relation (Pfun A B) :=
  fun f g =>
    forall a1 a2, ot_R A a1 a2 -> ot_R B (pfun_app f a1) (pfun_app g a2).

Program Definition OTarrow (A:OType) (B: OType) : OType :=
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
(* FIXME HERE: figure out the simplest way of stating this adjunction *)


(* OTarrow is right adjoint to OTpair, meaning that (OTarrow (OTpair A B) C) is
isomorphic to (OTarrow A (OTarrow B C)). The following is the first part of this
isomorphism, mapping left-to-right. *)


(* FIXME: could also do a forall type, but need the second type argument, B, to
itself be proper, i.e., to be an element of OTarrow A OType. Would also need a
dependent version of OTContext, below. *)


(***
 *** Notations for Ordered Types
 ***)

Module OTypeNotations.

  Notation "A '-o>' B" :=
    (OTarrow A B) (right associativity, at level 99).
  Notation "A '*o*' B" :=
    (OTpair A B) (left associativity, at level 40).
  Notation "A '+o+' B" :=
    (OTsum A B) (left associativity, at level 50).
  Notation "'~o~' A" :=
    (OTflip A) (right associativity, at level 35).

  Notation "x <o= ( A ) y" :=
    (ot_R A x y) (no associativity, at level 70).
  Notation "x =o= ( A ) y" :=
    (ot_equiv A x y) (no associativity, at level 70).

End OTypeNotations.


(***
 *** Lifting Proper Functions to Ordered Terms
 ***)

(* Class stating that the Proper elements of AU can be lifted to AO *)
Class OTLift (AU:Type) (R:relation AU) (AO:OType) : Type :=
  {
    ot_lift : forall (au:AU), Proper R au -> ot_Type AO;
    ot_lift_Proper :
      forall au1 au2 (Rau: R au1 au2) prp1 prp2,
        ot_R AO (ot_lift au1 prp1) (ot_lift au2 prp2);
  }.

Arguments OTLift AU%type R%signature AO.

(* Class stating that the lifting from AU to AO can be undone *)
Class OTLiftInv AU R AO :=
  {
    otLiftInv_Lift :> OTLift AU R AO;
    ot_unlift : ot_Type AO -> AU;
    ot_unlift_Proper : Proper (AO ==> R) ot_unlift;
    (* FIXME: these don't work for functions, since R could be non-transitive...
    ot_lift_iso1 : forall au prp, R (ot_unlift (ot_lift au prp)) au;
    ot_lift_iso2 : forall au prp, R au (ot_unlift (ot_lift au prp));
     *)
    (* FIXME: are these needed?
    ot_unlift_iso1 : forall ao prp, ot_R AO (ot_lift (ot_unlift ao) prp) ao;
    ot_unlift_iso2 : forall ao prp, ot_R AO ao (ot_lift (ot_unlift ao) prp);
     *)
  }.
(* FIXME: can we summarize the last 4 axioms above in a shorter way...? *)

Arguments OTLiftInv AU%type R%signature AO.


(* Any ordered type can be lifted to itself *)
(* FIXME: are these what we want...? *)
Program Instance OTLift_any_OType A : OTLift (ot_Type A) A A :=
  {| ot_lift := fun a _ => a; |}.
Program Instance OTLiftInv_any_OType A : OTLiftInv (ot_Type A) A A :=
  {| ot_unlift := fun a => a; |}.
Next Obligation.
  intros a1 a2 Ra; assumption.
Qed.

(* Any PreOrder gets an OTLift instance *)
Program Instance OTLift_PreOrder A R (po:@PreOrder A R) :
  OTLift A R {| ot_Type := A; ot_R := R; ot_PreOrder := po |} :=
  Build_OTLift
    A R {| ot_Type := A; ot_R := R; ot_PreOrder := po |}
    (fun a _ => a) _.

(* Any PreOrder gets an OTLiftInv instance *)
Program Instance OTLiftInv_PreOrder A R (po:@PreOrder A R) :
  OTLiftInv A R {| ot_Type := A; ot_R := R; ot_PreOrder := po |} :=
  {|
    ot_unlift := fun a => a;
  |}.
Next Obligation.
  intros a1 a2 Ra; assumption.
Qed.

(* Pairs can be lifted if their components can be lifted *)
Program Instance OTLift_pair A RA AO B RB BO
        `{OTLift A RA AO} `{OTLift B RB BO}
  : OTLift (A*B) (pairR RA RB) (OTpair AO BO) :=
  {|
    ot_lift := fun p prp =>
                 (ot_lift (fst p) (proj1 prp), ot_lift (snd p) (proj2 prp));
  |}.
Next Obligation.
  destruct Rau; split; apply ot_lift_Proper; assumption.
Qed.

(* Pairs can be unlifted if their components can be unlifted *)
Program Instance OTLiftInv_pair A RA AO B RB BO
        `{OTLiftInv A RA AO} `{OTLiftInv B RB BO}
  : OTLiftInv (A*B) (pairR RA RB) (OTpair AO BO) :=
  {|
    ot_unlift := fun p => (ot_unlift (fst p), ot_unlift (snd p));
  |}.
Next Obligation.
  intros p1 p2 Rp; destruct Rp; split; apply ot_unlift_Proper; assumption.
Qed.
(*
Next Obligation.
  destruct prp; split; apply ot_unlift_iso1.
Qed.
Next Obligation.
  destruct prp; split; apply ot_unlift_iso2.
Qed.
 *)

(* Functions can be lifted if their inputs can be unlifted *)
Program Instance OTLift_fun A RA AO B RB BO
        `{OTLiftInv A RA AO} `{OTLift B RB BO}
  : OTLift (A -> B) (RA ==> RB) (OTarrow AO BO) :=
  {|
    ot_lift :=
      fun f prp => {| pfun_app :=
                        fun a => ot_lift (f (ot_unlift a)) _;
                      pfun_Proper := _ |};
  |}.
Next Obligation.
  apply prp. apply ot_unlift_Proper. reflexivity.
Qed.
Next Obligation.
  intros a1 a2 Ra. apply ot_lift_Proper. apply prp.
  apply ot_unlift_Proper. assumption.
Qed.
Next Obligation.
  intros a1 a2 Ra. apply ot_lift_Proper. apply Rau.
  apply ot_unlift_Proper. assumption.
Qed.

(* Anything is Proper w.r.t. a pre-order *)
Instance Proper_PreOrder `{PreOrder} x : Proper R x :=
  PreOrder_Reflexive x.

(* Functions can be unlifted if their input types are PreOrders *)
Program Instance OTLiftInv_fun A RA (po:@PreOrder A RA) B RB BO
        `{OTLiftInv B RB BO}
  : OTLiftInv (A -> B) (RA ==> RB)
              (OTarrow (Build_OType A RA po) BO) :=
  {|
    ot_unlift := fun pf a => ot_unlift (pfun_app pf (ot_lift a _));
  |}.
Next Obligation.
  auto with typeclass_instances.
Qed.
(*
Next Obligation.
  unfold Proper. reflexivity.
Qed.
*)
Next Obligation.
  intros pf1 pf2 Rpf a1 a2 Ra. apply ot_unlift_Proper. apply Rpf. assumption.
Qed.
(*
Next Obligation.
  intros a1 a2 Ra. transitivity (pfun_app ao a1).
  apply ot_unlift_iso1. apply pfun_Proper; assumption.
Qed.
Next Obligation.
  intros a1 a2 Ra. simpl. transitivity (pfun_app ao a2).
  apply pfun_Proper; assumption. apply ot_unlift_iso2.
Qed.
 *)


(***
 *** Building Proper Instance for Lambdas
 ***)

(* Helper class for proving Proper relations on lambdas *)
Class ProperH {A} (R:relation A) (x y : A) :=
  properH : R x y.

Arguments ProperH {A%type} R%signature x y.

(* If the lhs and rhs are the same, we can use a normal Proper instance *)
Instance ProperH_Proper `{Proper} : ProperH R m m := proper_prf (R:=R).

(* Wrappers for variables, so the typeclass resolution can see pf *)
Definition PH_varL {A} (R:relation A) (xl xr:A) (pf:R xl xr) := xl.
Definition PH_varR {A} (R:relation A) (xl xr:A) (pf:R xl xr) := xr.

(* Proving ProperH for variables is now easy using PH_varL and PH_varR *)
Instance ProperH_var {A} R (xl xr:A) pf :
  ProperH R (PH_varL R xl xr pf) (PH_varR R xl xr pf) := pf.

(* To prove Proper-ness for a lambda, we construct PH_vars for it *)
Instance ProperH_lambda {A B RA RB} (fL fR:A -> B)
         (H: forall xl xr pf,
             ProperH RB (fL (PH_varL RA xl xr pf)) (fR (PH_varR RA xl xr pf))) :
  ProperH (RA ==> RB) (fun x => fL x) (fun x => fR x) | 2.
  exact H.
Qed.

(* Proper-ness instance for applications; note that RA will in general be an
existential variable, because it is not determined by the goal formula here. *)
Instance ProperH_app A RA {B RB} (fL fR: A -> B) argL argR :
  ProperH (RA ==> RB) fL fR -> ProperH RA argL argR ->
  ProperH RB (fL argL) (fR argR).
Proof.
  intros prp1 prp2. apply prp1. assumption.
Qed.

(* Helper wrapper for ot_lift *)
Definition mkOTerm `{OTLift} (trm:AU)
           `{prp:ProperH _ R trm trm} : ot_Type AO :=
  ot_lift trm properH.

Arguments mkOTerm {AU%type} {R%signature} {AO H} trm {prp}.

(***
 *** Proper Instances for Standard Operations
 ***)

(* Proper instance for fst *)
Instance Proper_fst A B : Proper (OTpair A B ==> A) fst.
Proof.
  intros p1 p2 Rp; destruct Rp. assumption.
Qed.

(* Proper instance for snd *)
Instance Proper_snd A B : Proper (OTpair A B ==> B) snd.
Proof.
  intros p1 p2 Rp; destruct Rp. assumption.
Qed.

(* Proper instance for pair *)
Instance Proper_pair (A B:OType) : Proper (A ==> B ==> OTpair A B) pair.
Proof.
  intros a1 a2 Ra b1 b2 Rb; split; assumption.
Qed.


(***
 *** Examples of Ordered Terms
 ***)

Module OTExamples.
Import OTypeNotations.

Definition ex1 : ot_Type (OTProp -o> OTProp) := mkOTerm (fun p => p).
Print ex1.

Goal (OTLift (ot_Type (OTProp -o> OTProp)) (OTProp -o> OTProp) (OTProp -o> OTProp)).
  auto with typeclass_instances.
Qed.

Goal (OTLift (ot_Type (OTProp -o> OTProp -o> OTProp))
             (OTProp -o> OTProp -o> OTProp) (OTProp -o> OTProp -o> OTProp)).
  auto with typeclass_instances.
Qed.

Goal (ProperH (OTProp ==> OTProp ==> OTProp) (fun p1 p2 => p1) (fun p1 p2 => p1)).
  auto with typeclass_instances.
Qed.

Goal ({R:_ & OTLift (ot_Type OTProp -> ot_Type OTProp -> ot_Type OTProp)
                    R (OTProp -o> OTProp -o> OTProp)}).
  eapply existT.
  auto with typeclass_instances.
Qed.

Goal ({R:_
         & OTLift (forall (_ : ot_Type OTProp) (_ : ot_Type OTProp), ot_Type OTProp)
                  R (OTProp -o> OTProp -o> OTProp)
         & ProperH R (fun p1 p2 => p1) (fun p1 p2 => p1)
          }).
  eapply existT2.
  auto with typeclass_instances.
  auto with typeclass_instances.
Qed.


Definition ex2 : ot_Type (OTProp -o> OTProp -o> OTProp) :=
  mkOTerm (R:=_ ==> _ ==> _) (fun p1 p2 => p1).
Eval compute in (ot_unlift ex2 : Prop -> Prop -> Prop).

Definition ex3 {A B} : ot_Type (A *o* B -o> A) :=
  mkOTerm (R:= _ ==> _) fst.
Eval compute in (ot_unlift (@ex3 OTProp OTProp) : Prop * Prop -> Prop).

Definition ex4 {A B} : ot_Type (A *o* B -o> B *o* A) :=
  mkOTerm (R:= _ ==> _) (fun p => (snd p, fst p)).
Eval compute in (ot_unlift (@ex4 OTProp OTProp) : Prop * Prop -> Prop * Prop).

End OTExamples.
