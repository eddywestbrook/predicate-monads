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
    ot_R := pairR (ot_R A) (ot_R B);
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
    ot_R := sumR (ot_R A) (ot_R B)
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

  Notation "x <o= y" :=
    (ot_R _ x y) (no associativity, at level 70).
  Notation "x =o= y" :=
    (ot_equiv _ x y) (no associativity, at level 70).

  Notation "x @o@ y" :=
    (pfun_app x y) (left associativity, at level 20).

End OTypeNotations.


(***
 *** Building Proper Functions
 ***)

Class OTEnrich (A:OType) {AU} (RA:relation AU) : Type :=
  {
    ot_lift : forall a, Proper RA a -> A;
    ot_lift_Proper :
      forall a1 a2 prp1 prp2,
        RA a1 a2 -> ot_R A (ot_lift a1 prp1) (ot_lift a2 prp2);
    ot_unlift : A -> AU;
  }.

Arguments OTEnrich A {AU%type} RA%signature.

Program Instance OTEnrich_refl (A:OType) : OTEnrich A (ot_R A) :=
  {
    ot_lift := fun a _ => a;
    ot_lift_Proper := _;
    ot_unlift := fun a => a;
  }.

Program Instance OTEnrich_fun (A:OType) B BU RB `{OTEnrich B BU RB} :
  OTEnrich (OTarrow A B) (ot_R A ==> RB) :=
  {
    ot_lift := fun f prp => Build_Pfun A B (fun a => ot_lift (f a) _) _;
    ot_lift_Proper := _;
    ot_unlift := fun pfun a => ot_unlift (pfun_app pfun a);
  }.
Next Obligation.
  apply prp. reflexivity.
Qed.
Next Obligation.
  intros a1 a2 Ra. apply ot_lift_Proper. apply prp. assumption.
Qed.
Next Obligation.
  intros x1 x2 Rx. apply ot_lift_Proper. apply H0. assumption.
Qed.


Class OTHasType (A:OType) {AU} (R:relation AU) (x y:AU) : Type :=
  {
    ot_wf_type : OTEnrich A R;
    ot_wf_term : R x y;
  }.

Arguments OTHasType A {AU%type} R%signature x y.

Instance OTHasType_lambda (A B:OType) BU RB `{OTEnrich B BU RB}
         (fl fr:A -> BU)
         (pf: forall xl xr (pf:OTHasType A (ot_R A) xl xr),
             OTHasType B RB (fl xl) (fr xr)) :
  OTHasType (OTarrow A B) (ot_R A ==> RB) fl fr | 4.
Proof.
  constructor.
  auto with typeclass_instances.
  intros xl xr Rx. apply pf. constructor.
  auto with typeclass_instances.
  assumption.
Defined.

Hint Extern 2 (OTHasType _ _ (fun _ => _) (fun _ => _)) =>
apply OTHasType_lambda : typeclass_instances.

Instance OTHasType_app A AU RA B BU RB (fl fr:AU -> BU) argl argr
         `{OTEnrich B BU RB}
         `{OTHasType (OTarrow A B) _ (RA ==> RB) fl fr}
         `{OTHasType A _ RA argl argr}
 : OTHasType B RB (fl argl) (fr argr) | 3.
Proof.
  constructor.
  assumption.
  apply H0. apply ot_wf_term.
Defined.

Instance OTHasType_pfun_app A B (fl fr:OTarrow A B) argl argr
         `{OTHasType (OTarrow A B) _ (ot_R (OTarrow A B)) fl fr}
         `{OTHasType A _ (ot_R A) argl argr}
 : OTHasType B (ot_R B) (pfun_app fl argl) (pfun_app fr argr) | 2.
Proof.
  constructor.
  auto with typeclass_instances.
  apply (ot_wf_term (OTHasType:=H)).
  apply (ot_wf_term (OTHasType:=H0)).
Defined.

Program Definition mkOTerm A {AU R} (x:AU) `{OTHasType A AU R x x} : A :=
  ot_lift (OTEnrich:=ot_wf_type) x ot_wf_term.

Arguments mkOTerm A {AU%type R%signature} x {H}.

(*
Program Definition mkOTerm2 A {AU RA BU RB} (x:AU -> BU)
        `{OTHasType A (AU -> BU) (RA ==> RB) x x} : A :=
  ot_lift (OTEnrich:=ot_wf_type) x ot_wf_term.
 *)


(***
 *** OT Typing Rules for Common Operations
 ***)

Instance OTHasType_fst A B :
  OTHasType (OTarrow (OTpair A B) A) (ot_R (OTpair A B) ==> ot_R A) fst fst.
Proof.
  constructor. auto with typeclass_instances.
  intros p1 p2 Rp; destruct Rp; assumption.
Defined.


(***
 *** Examples of Ordered Terms
 ***)

Module OTExamples.
Import OTypeNotations.

Definition ex1 := mkOTerm (OTProp -o> OTProp) (fun p => p).
Eval compute in (ot_unlift ex1 : OTProp -> OTProp).

Definition ex2 {A} := mkOTerm (A -o> A) (fun p => p).
Eval simpl in (fun A:OType => ot_unlift ex2 : A -> A).

Definition ex3 {A} :=
  mkOTerm (A -o> A -o> A -o> A -o> A) (fun (p1 p2 p3 p4:A) => p1).
Eval simpl in (fun A:OType => ot_unlift ex3 : A -> A  -> A -> A -> A).

Definition ex4 {A B} := mkOTerm (A *o* B -o> A) (fun p => fst p).
Eval simpl in (fun (A B:OType) => ot_unlift ex4 : A * B -> A).

End OTExamples.


(*
FIXME HERE NOW: old stuff below!

(***
 *** Building Proper Functions
 ***)

(* Build the (non-ordered) type A1 -> ... -> An -> B *)
Fixpoint addArrows (As:list OType) (B:OType) : Type :=
  match As with
  | [] => B
  | A::As' => A -> addArrows As' B
  end.

(* Build the ordered type A1 -o> ... -o> An -o> B *)
Fixpoint addOTArrows (As:list OType) (B:OType) : OType :=
  match As with
  | [] => B
  | A::As' => OTarrow A (addOTArrows As' B)
  end.

(* Build the relation ot_R A1 ==> ... ==> ot_R An ==> B *)
Fixpoint arrowsR (As:list OType) (B:OType) : relation (addArrows As B) :=
  match As return relation (addArrows As B) with
  | [] => ot_R B
  | A::As' => (ot_R A ==> arrowsR As' B)%signature
  end.


Definition pfun_maker As B :=
  { m : forall (f:addArrows As B), Proper (arrowsR As B) f -> addOTArrows As B
  | forall f1 f2 prp1 prp2,
      arrowsR As B f1 f2 -> ot_R (addOTArrows As B) (m f1 prp1) (m f2 prp2) }.

Program Definition pfun_maker_nil B : pfun_maker [] B :=
  fun f _ => f.

Program Definition pfun_maker_cons A As B (m:pfun_maker As B)
  : pfun_maker (A::As) B :=
  fun f prp =>
    {| pfun_app := fun a => proj1_sig m (f a) _ |}.
Next Obligation.
  apply prp. reflexivity.
Qed.
Next Obligation.
  intros a1 a2 Ra. apply (proj2_sig m). apply prp. assumption.
Qed.
Next Obligation.
  intros a1 a2 Ra. apply (proj2_sig m). apply H. assumption.
Qed.

Fixpoint pfun_maker_multi As B : pfun_maker As B :=
  match As return pfun_maker As B with
  | [] => pfun_maker_nil B
  | A::As' => pfun_maker_cons A As' B (pfun_maker_multi As' B)
  end.


(***
 *** Typing for Proper Functions
 ***)

Class OTHasType As B (fl fr : addArrows As B) : Prop :=
  ot_has_type : arrowsR As B fl fr.

Instance OTHasType_lambda A As B fl fr
         (pf: forall xl xr (pf:OTHasType [] A xl xr),
             OTHasType As B (fl xl) (fr xr)) :
  OTHasType (A::As) B fl fr | 2.
Proof.
  intros a1 a2 Ra. apply pf. assumption.
Qed.

Instance OTHasType_app A As B (fl fr:
         (pf: forall xl xr (pf:OTHasType [] A xl xr),
             OTHasType As B (fl xl) (fr xr)) :
  OTHasType (A::As) B fl fr | 2.
Proof.
  intros a1 a2 Ra. apply pf. assumption.
Qed.

(*
Instance OTHasType_Proper As B f `{Proper _ (arrowsR As B) f} : OTHasType As B f f.
Proof.
  assumption.
Qed.
*)

Instance OTHasType_fst A B : OTHasType [OTpair A B] A fst fst.
Proof.
  intros p1 p2 Rp. destruct Rp. assumption.
Qed.



Goal (forall A, OTHasType )

Print HintDb typeclass_instances.

(* Wrappers for variables, so the typeclass resolution can see pf *)
(*
Definition OT_varL (A:OType) (xl xr:A) (pf:ot_R A xl xr) := xl.
Definition OT_varR (A:OType) (xl xr:A) (pf:ot_R A xl xr) := xr.

(* Proving ProperH for variables is now easy using PH_varL and PH_varR *)
Instance OTHasType_var (A:OType) (xl xr:A) pf :
  OTHasType A (OT_varL A xl xr pf) (OT_varR A xl xr pf) := pf.
 *)

(* To prove Proper-ness for a lambda, we construct PH_vars for it *)
Definition OTHasType_lambda (A B:OType) BU RB (fL fR:A -> BU)
           `{OTEnriches B BU RB}
           (pf: forall xl xr (pf:OTHasType A (ot_R A) xl xr),
               OTHasType B RB (fL xl) (fR xr)) :
  OTHasType (OTarrow A B) (ot_R A ==> RB)%signature fL fR.
  constructor.
  auto with typeclass_instances.
  

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

(* Proper-ness instance for pfun applications *)
Instance ProperH_pfun_app {A B} (fL fR: OTarrow A B) argL argR :
  ProperH (ot_R (OTarrow A B)) fL fR -> ProperH (ot_R A) argL argR ->
  ProperH (ot_R B) (pfun_app fL argL) (pfun_app fR argR).
Proof.
  intros prp1 prp2. apply prp1. assumption.
Qed.

(* Helper wrapper for ot_lift *)
Definition mkOTerm `{OTLift} (trm:AU)
           `{prp:ProperH _ R trm trm} : ot_Type AO :=
  ot_lift trm properH.

Arguments mkOTerm {AU%type} {R%signature} {AO H} trm {prp}.




FIXME HERE NOW


(***
 *** Building Proper Functions
 ***)

Class OTEnrich (A:OType) AU : Type :=
  {
    ot_lift_R : relation AU;
    ot_lift : forall a, Proper ot_lift_R a -> A;
    ot_lift_Proper :
      forall a1 a2 prp1 prp2,
        ot_lift_R a1 a2 ->
        ot_R A (ot_lift a1 prp1) (ot_lift a2 prp2);
    ot_unlift : A -> AU;
  }.

Program Instance OTEnrich_refl (A:OType) : OTEnrich A A :=
  {
    ot_lift_R := ot_R A;
    ot_lift := fun a _ => a;
    ot_lift_Proper := _;
    ot_unlift := fun a => a;
  }.

Program Instance OTEnrich_fun (A:OType) B BU `{OTEnrich B BU} :
  OTEnrich (OTarrow A B) (A -> BU) :=
  {
    ot_lift_R := (ot_R A ==> ot_lift_R)%signature;
    ot_lift := fun f prp => Build_Pfun A B (fun a => ot_lift (f a) _) _;
    ot_lift_Proper := _;
    ot_unlift := fun pfun a => ot_unlift (pfun_app pfun a);
  }.
Next Obligation.
  apply prp. reflexivity.
Qed.
Next Obligation.
  intros a1 a2 Ra. apply ot_lift_Proper. apply prp. assumption.
Qed.
Next Obligation.
  intros x1 x2 Rx. apply ot_lift_Proper. apply H0. assumption.
Qed.


Class OTHasType (A:OType) {AU} (x y:AU) : Type :=
  {
    ot_wf_type : OTEnrich A AU;
    ot_wf_term : ot_lift_R x y;
  }.


FIXME HERE NOW: old stuff below

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
    ot_unlift_Proper : Proper (ot_R AO ==> R) ot_unlift;
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
Program Instance OTLift_any_OType A : OTLift (ot_Type A) (ot_R A) A :=
  {| ot_lift := fun a _ => a; |}.
Program Instance OTLiftInv_any_OType A : OTLiftInv (ot_Type A) (ot_R A) A :=
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

(* Proper-ness instance for pfun applications *)
Instance ProperH_pfun_app {A B} (fL fR: OTarrow A B) argL argR :
  ProperH (ot_R (OTarrow A B)) fL fR -> ProperH (ot_R A) argL argR ->
  ProperH (ot_R B) (pfun_app fL argL) (pfun_app fR argR).
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
Instance Proper_fst A B : Proper (ot_R (OTpair A B) ==> ot_R A) fst.
Proof.
  intros p1 p2 Rp; destruct Rp. assumption.
Qed.

(* Proper instance for snd *)
Instance Proper_snd A B : Proper (ot_R (OTpair A B) ==> ot_R B) snd.
Proof.
  intros p1 p2 Rp; destruct Rp. assumption.
Qed.

(* Proper instance for pair *)
Instance Proper_pair (A B:OType) :
  Proper (ot_R A ==> ot_R B ==> ot_R (OTpair A B)) pair.
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

Goal (OTLift (Prop -> Prop)
             (ot_R OTProp ==> ot_R OTProp)
             (OTProp -o> OTProp)).
  auto with typeclass_instances.
Qed.

Goal (OTLift (Prop -> Prop -> Prop)
             (ot_R OTProp ==> ot_R OTProp ==> ot_R OTProp)
             (OTProp -o> OTProp -o> OTProp)).
  auto with typeclass_instances.
Qed.

Goal (ProperH (ot_R OTProp ==> ot_R OTProp ==> ot_R OTProp)
              (fun p1 p2 => p1) (fun p1 p2 => p1)).
  auto with typeclass_instances.
Qed.

Goal ({R:_ & OTLift (ot_Type OTProp -> ot_Type OTProp -> ot_Type OTProp)
                    R (OTProp -o> OTProp -o> OTProp)}).
  eapply existT.
  auto with typeclass_instances.
Qed.

Goal ({R:_
         & OTLift (OTProp -> OTProp -> OTProp)
                  R (OTProp -o> OTProp -o> OTProp)
         & ProperH R (fun p1 p2 => p1) (fun p1 p2 => p1)
          }).
  eapply existT2.
  auto with typeclass_instances.
  auto with typeclass_instances.
Qed.


Definition ex2 : OTProp -o> OTProp -o> OTProp :=
  mkOTerm (R:=_ ==> _ ==> _) (fun p1 p2 => p1).
Eval compute in (ot_unlift ex2 : Prop -> Prop -> Prop).

Definition ex3 {A B} : A *o* B -o> A :=
  mkOTerm (R:= _ ==> _) fst.
Eval compute in (ot_unlift (@ex3 OTProp OTProp) : Prop * Prop -> Prop).

Definition ex4 {A B} : A *o* B -o> B *o* A :=
  mkOTerm (R:= _ ==> _) (fun p => (snd p, fst p)).
Eval compute in (ot_unlift (@ex4 OTProp OTProp) : Prop * Prop -> Prop * Prop).

Goal (ex2 <o= ex2). reflexivity. Qed.
Goal (forall {A B}, ex4 (A:=A) (B:=B) <o= ex4). intros. reflexivity. Qed.


Goal (OTLift ((OTProp -o> OTProp) -> OTProp -> OTProp)
             (ot_R (OTProp -o> OTProp) ==> ot_R OTProp ==> ot_R OTProp)
             ((OTProp -o> OTProp) -o> OTProp -o> OTProp)).
  auto with typeclass_instances.
Qed.


Goal ({R:_
         & OTLift ((OTProp -o> OTProp) -> OTProp -> OTProp)
                  R ((OTProp -o> OTProp) -o> OTProp -o> OTProp)
         & ProperH R (fun f a => f @o@ a) (fun f a => f @o@ a)
          }).
  eapply existT2.
  auto with typeclass_instances.
  auto with typeclass_instances.
Qed.

Goal (forall {A B},
         {R:_
            & OTLift ((A -o> B) -> A -> B)
                     R ((A -o> B) -o> A -o> B)
            & ProperH R (fun f a => f @o@ a) (fun f a => f @o@ a)
          }).
  intros; eapply existT2.
  auto with typeclass_instances.
  auto with typeclass_instances.
Defined.
Print Unnamed_thm8.

Goal (forall {A B},
         ProperH (ot_R (A -o> B) ==> ot_R A ==> ot_R B)
                 (fun (f : A -o> B) (a : A) => f @o@ a)
                 (fun (f : A -o> B) (a : A) => f @o@ a)).
  intros. auto with typeclass_instances.
Qed.
Print Unnamed_thm9.

Definition ex5 {A B} : (A -o> B) -o> A -o> B :=
  mkOTerm 
          (fun f a => f @o@ a)
.

Eval compute in (ot_unlift (@ex4 OTProp OTProp) : Prop * Prop -> Prop * Prop).


End OTExamples.
*)