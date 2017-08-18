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
Definition ot_equiv (A:OType) : relation A :=
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
    ot_R := pairR (ot_R A) (ot_R B);
    ot_PreOrder := PreOrder_pairR A B _ _ (ot_PreOrder A) (ot_PreOrder B)
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
    ot_R := sumR (ot_R A) (ot_R B);
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
    pfun_Proper :> Proper (ot_R A ==> ot_R B) pfun_app
  }.

Arguments pfun_app [_ _] _ _.
Arguments pfun_Proper [_ _] _ _ _ _.

(* Infix "@" := pfun_app (at level 50). *)

(* The non-dependent function ordered type *)
Definition OTarrow_R (A B : OType) : relation (Pfun A B) :=
  fun f g =>
    forall a1 a2, ot_R A a1 a2 -> ot_R B (pfun_app f a1) (pfun_app g a2).

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


(* pfun_app is always Proper *)
Instance Proper_pfun_app A B :
  Proper (ot_R (OTarrow A B) ==> ot_R A ==> ot_R B) (@pfun_app A B).
Proof.
  intros f1 f2 Rf a1 a2 Ra. apply Rf; assumption.
Qed.

(* pfun_app is always Proper w.r.t. ot_equiv *)
Instance Proper_pfun_app_equiv A B :
  Proper (ot_equiv (OTarrow A B) ==> ot_equiv A ==> ot_equiv B) (@pfun_app A B).
Proof.
  intros f1 f2 Rf a1 a2 Ra; destruct Rf; destruct Ra.
  split; apply Proper_pfun_app; assumption.
Qed.


(***
 *** Ordered Type Functions
 ***)

(*
Class OTypeF (TF: forall `(A:OType), Type) : Type :=
  otypef_app : forall `(A:OType), OType (TF A).

Arguments otypef_app [TF] _ [T] A _ _.

Instance OType_OTypeF_app `(F:OTypeF) `(A:OType) : OType (TF _ A) := otypef_app _ A.

Class ValidOTypeF `(F:OTypeF) : Prop :=
  {
    otypef_app_PreOrder :>
      forall `(A:OType) {_:ValidOType A}, PreOrder (ot_R (otypef_app F A))
  }.

Instance ValidOType_OTypeF_app `(ValidOTypeF) `(ValidOType) :
  ValidOType (otypef_app F A).
Proof.
  constructor. typeclasses eauto.
Qed.
*)


(***
 *** Finding and Instantiating Ordered Types
 ***)

(* States that A is the default OType for type AU. We expect that AU = ot_Type
A, though the below only implies that A is isomorphic to AU w.r.t. RU. *)
Class OTForType (A:OType) {AU} (RU:relation AU) : Type :=
  {
    ot_lift_iso : AU -> A;
    ot_lift_iso_Proper : Proper (RU ==> ot_R A) ot_lift_iso;
    ot_unlift_iso : A -> AU;
    ot_unlift_iso_Proper : Proper (ot_R A ==> RU) ot_unlift_iso;
    ot_for_type_PreOrder :> PreOrder RU;
    ot_lift_unlift_iso : forall x, ot_unlift_iso (ot_lift_iso x) = x;
    ot_unlift_lift_iso : forall x, ot_lift_iso (ot_unlift_iso x) = x;
  }.

Instance OTForType_refl (A:OType) : OTForType A (ot_R A) :=
  {
    ot_lift_iso := fun a => a;
    ot_lift_iso_Proper := fun a1 a2 Ra => Ra;
    ot_unlift_iso := fun a => a;
    ot_unlift_iso_Proper := fun a1 a2 Ra => Ra;
    ot_for_type_PreOrder := ot_PreOrder A;
    ot_unlift_lift_iso := fun a => eq_refl;
    ot_lift_unlift_iso := fun a => eq_refl;
  }.

(* Hint to use OTForType_refl if AU unifies with (ot_Type A), even if it is not
syntactically equal to (ot_Type A) *)
Hint Extern 1 (OTForType _ _) => apply OTForType_refl : typeclass_instances.

(* The default OType for Prop is OTProp *)
Instance OTForType_OTProp : OTForType OTProp Basics.impl := OTForType_refl _.

(* The default OType for a pair is OTpair of the defaults for the two types *)
Program Instance OTForType_pair A AU RAU B BU RBU
        (otA:@OTForType A AU RAU) (otB:@OTForType B BU RBU) :
  OTForType (OTpair A B) (pairR RAU RBU) :=
    {|
      ot_lift_iso :=
        fun p => (ot_lift_iso (fst p), ot_lift_iso (snd p));
      ot_unlift_iso := fun p => (ot_unlift_iso (fst p), ot_unlift_iso (snd p));
    |}.
Next Obligation.
  intros p1 p2 Rp; destruct Rp.
  split; simpl; apply ot_lift_iso_Proper; assumption.
Qed.
Next Obligation.
  intros p1 p2 Rp; destruct Rp.
  split; simpl; apply ot_unlift_iso_Proper; assumption.
Qed.
Next Obligation.
  repeat rewrite ot_lift_unlift_iso. reflexivity.
Qed.
Next Obligation.
  repeat rewrite ot_unlift_lift_iso. reflexivity.
Qed.

(* The default OType for a sum is OTsum of the defaults for the two types *)
Program Instance OTForType_sum A AU RAU B BU RBU
        (otA:@OTForType A AU RAU) (otB:@OTForType B BU RBU) :
  OTForType (OTsum A B) (sumR RAU RBU) :=
    {|
      ot_lift_iso :=
        fun s =>
          match s with
          | inl a => inl (ot_lift_iso a)
          | inr b => inr (ot_lift_iso b)
          end;
      ot_unlift_iso :=
        fun s =>
          match s with
          | inl a => inl (ot_unlift_iso a)
          | inr b => inr (ot_unlift_iso b)
          end;
    |}.
Next Obligation.
  intros s1 s2 Rs.
  destruct Rs; constructor; apply ot_lift_iso_Proper; assumption.
Qed.
Next Obligation.
  intros s1 s2 Rs.
  destruct Rs; constructor; apply ot_unlift_iso_Proper; assumption.
Qed.
Next Obligation.
  destruct x; rewrite ot_lift_unlift_iso; reflexivity.
Qed.
Next Obligation.
  destruct x; rewrite ot_unlift_lift_iso; reflexivity.
Qed.


(* States that A is a valid OType for the Proper elements of AU *)
Class OTForRel (A:OType) {AU} (RU:relation AU) : Type :=
  {
    ot_lift : forall a, Proper RU a -> A;
    ot_lift_Proper :
      forall a1 a2 prp1 prp2,
        RU a1 a2 -> ot_R A (ot_lift a1 prp1) (ot_lift a2 prp2);
    ot_unlift : A -> AU;
    ot_unlift_Proper : Proper (ot_R A ==> RU) ot_unlift;
    ot_lift_unlift_R : forall a prp, RU a (ot_unlift (ot_lift a prp));

    ot_unlift_lift :
      forall a prp, ot_equiv A (ot_lift (ot_unlift a) prp) a;

    (* NOTE: the case for RU is more complex since it may not be transitive *)
    ot_lift_unlift1 :
      forall a' a prp, RU a' a <-> RU a' (ot_unlift (ot_lift a prp));
    ot_lift_unlift2 :
      forall a' a prp, RU a a' <-> RU (ot_unlift (ot_lift a prp)) a';
  }.

Arguments OTForRel A {AU%type} RU%signature.

(*
Program Instance OTForRel_refl (A:OType) : OTForRel A (ot_R A) :=
  {
    ot_lift := fun a _ => a;
    ot_lift_Proper := _;
    ot_unlift := fun a => a;
  }.
*)

(* If A is the default OType for AU and RU, then it is a valid OType for them *)
Program Instance OTForRel_OTForType A AU RU
        (_:@OTForType A AU RU) : OTForRel A RU | 3 :=
  {|
    ot_lift := fun a _ => ot_lift_iso a;
    ot_unlift := ot_unlift_iso;
  |}.
Next Obligation.
  apply ot_lift_iso_Proper. assumption.
Qed.
Next Obligation.
  intros a1 a2 Ra; apply ot_unlift_iso_Proper; assumption.
Qed.
Next Obligation.
  rewrite ot_lift_unlift_iso. reflexivity.
Qed.
Next Obligation.
  rewrite ot_unlift_lift_iso. reflexivity.
Qed.
Next Obligation.
  rewrite ot_lift_unlift_iso. reflexivity.
Qed.
Next Obligation.
  rewrite ot_lift_unlift_iso. reflexivity.
Qed.


Program Instance OTForRel_fun (A B:OType) AU RAU BU RBU
        (otA:@OTForType A AU RAU) (otB:@OTForRel B BU RBU) :
  OTForRel (OTarrow A B) (RAU ==> RBU) :=
  {|
    ot_lift := fun f prp =>
                 {| pfun_app :=
                      fun a =>
                        ot_lift (OTForRel:=otB) (f (ot_unlift_iso a))
                                (prp _ _ (reflexivity _))|};
    ot_lift_Proper := _;
    ot_unlift := fun pfun a => ot_unlift (pfun_app pfun (ot_lift_iso a));
  |}.
Next Obligation.
  intros a1 a2 Ra. apply ot_lift_Proper. apply prp.
  apply ot_unlift_iso_Proper. assumption.
Qed.
Next Obligation.
  intros x1 x2 Rx. apply ot_lift_Proper. apply H.
  apply ot_unlift_iso_Proper. assumption.
Qed.
Next Obligation.
  intros f1 f2 Rf a1 a2 Ra. apply ot_unlift_Proper.
  apply Rf. apply ot_lift_iso_Proper. assumption.
Qed.
Next Obligation.
  intros a1 a2 Ra. apply ot_lift_unlift1. rewrite ot_lift_unlift_iso.
  apply prp. assumption.
Qed.
Next Obligation.
  split; intros a1 a2 Ra; simpl.
  { transitivity (pfun_app a (ot_lift_iso (ot_unlift_iso a1)));
      [ apply (proj1 (ot_unlift_lift _ _))
      | rewrite ot_unlift_lift_iso; apply pfun_Proper; assumption ]. }
  { transitivity (pfun_app a (ot_lift_iso (ot_unlift_iso a2)));
      [ rewrite ot_unlift_lift_iso; apply pfun_Proper; assumption
      | apply (proj2 (ot_unlift_lift _ _)) ]. }
Qed.
Next Obligation.
  split; intros Ra' a1 a2 Ra.
  { apply ot_lift_unlift1. rewrite ot_lift_unlift_iso. apply Ra'; assumption. }
  { rewrite <- (ot_lift_unlift_iso a2).
    refine (proj2 (ot_lift_unlift1 (a' a1) _ _) (Ra' _ _ _)); assumption. }
Qed.
Next Obligation.
  split; intros Ra' a1 a2 Ra.
  { apply ot_lift_unlift2. rewrite ot_lift_unlift_iso. apply Ra'; assumption. }
  { rewrite <- (ot_lift_unlift_iso a1).
    refine (proj2 (ot_lift_unlift2 (a' a2) _ _) (Ra' _ _ _)). assumption. }
Qed.

(* Tactic to prove OTForRel goals *)
Ltac prove_OTForRel :=
  lazymatch goal with
  | |- @OTForRel ?A (forall x:?AU, ?BU) ?RU =>
    refine (OTForRel_fun _ _ _ _ _ _ _ _)
  | |- @OTForRel (OTarrow ?A ?B) _ _ =>
    apply OTForRel_fun
  | |- @OTForRel _ _ _ => apply OTForRel_OTForType; try apply OTForType_refl
  end.

(*
Ltac prove_OTForRel :=
  lazymatch goal with
  | |- @OTForRel (OTarrow ?A ?B) (forall x:?AU, ?BU) _ =>
    let RBU := fresh "RBU" in
    evar (RBU: forall (x:AU), relation BU);
    assert (forall x, @OTForRel A BU (?RBU x)); [ intro x | ];
    unfold RBU; clear RBU
  | |- @OTForRel _ _ _ => apply OTForRel_OTForType
  end.
*)

(* Hint to use the prove_OTForRel tactic; we need this because often the
relation part is an evar, so will not match any of the instances above *)
Hint Extern 2 (@OTForRel _ _ _) => prove_OTForRel : typeclass_instances.


(***
 *** Building Ordered Terms
 ***)

Class OTHasType (A:OType) {AU} (RU:relation AU) (x y:AU) : Prop :=
  {
    ot_has_type : RU x y
  }.

Arguments OTHasType A {AU%type} RU%signature x y.

Instance OTHasType_app (A:OType) AU RAU (B:OType) BU RBU
         (fl fr:AU -> BU) argl argr
         (otef:OTHasType (OTarrow A B) (RAU ==> RBU) fl fr)
         (otea:OTHasType A RAU argl argr) :
  OTHasType B RBU (fl argl) (fr argr) | 3.
Proof.
  constructor.
  apply (ot_has_type (OTHasType:=otef)).
  apply ot_has_type.
Qed.

Instance OTHasType_pfun_app (A B:OType) (fl fr:OTarrow A B) argl argr
         (otef:OTHasType (OTarrow A B) (ot_R (OTarrow A B)) fl fr)
         (otea:OTHasType A (ot_R A) argl argr)
 : OTHasType B (ot_R B) (pfun_app fl argl) (pfun_app fr argr) | 2.
Proof.
  constructor.
  apply (ot_has_type (OTHasType:=otef)).
  apply (ot_has_type (OTHasType:=otea)).
Qed.

(* NOTE: We only want this to apply to terms that are syntactically lambdas, so
we use an Extern hint, below. *)
Definition OTHasType_lambda (A B:OType) AU RAU BU RBU
         (fl fr:AU -> BU)
         (pf: forall xl xr (pf:OTHasType A RAU xl xr),
             OTHasType B RBU (fl xl) (fr xr)) :
  OTHasType (OTarrow A B) (RAU ==> RBU) fl fr.
Proof.
  constructor.
  intros xl xr Rx; apply pf; constructor; assumption.
Qed.


(*
Ltac OTHasType_tac :=
  lazymatch goal with
  | |- OTHasType _ _ (fun x => ?f) (fun y => ?g) =>
    eapply (OTHasType_lambda _ _ _ _ (fun x => f) (fun y => g))
  | |- OTHasType _ _ (pfun_app ?f ?x) (pfun_app ?g ?y) =>
    apply (OTHasType_pfun_app _ _ f g x y)
  | |- OTHasType _ _ (?f ?x) (?g ?y) =>
    eapply (OTHasType_app _ _ _ _ _ _ f g x y)
  end.

Hint Extern 4 (OTHasType _ _ _ _) => OTHasType_tac : typeclass_instances.
*)

(* Hint to apply OTHasType_lambda on lambdas *)
Ltac try_OTHasType_lambda :=
  lazymatch goal with
  | |- @OTHasType _ _ _ (fun x => ?f) (fun y => ?g) =>
    eapply (OTHasType_lambda _ _ _ _ _ _ (fun x => f) (fun y => g))
  end.

Hint Extern 2 (@OTHasType _ _ _ (fun _ => _) (fun _ => _)) =>
try_OTHasType_lambda : typeclass_instances.

(* NOTE: this is not an instance because it is not syntax-driven, like our other
rules for OTHasType. Instead, this definition is used as a helper to build
other instances of OTHasType. *)
Definition OTHasType_Proper `{OTForRel} (x:AU) :
  Proper RU x -> OTHasType A RU x x.
  intros; constructor; assumption.
Defined.

Instance OTHasType_refl (A:OType) (x:A) : OTHasType A (ot_R A) x x.
Proof.
  apply OTHasType_Proper. unfold Proper. reflexivity.
Defined.

(*
Instance OTHasType_refl_rel {T} (A:relation T) {vA:ValidOType A} (x:T)
  : OTHasType A A x x := OTHasType_refl A x.
*)

Program Definition mkOTerm (A:OType) {AU RU}
        {otfr:OTForRel A RU} (x:AU) {ht:@OTHasType A AU RU x x} : ot_Type A :=
  ot_lift (OTForRel:=otfr) x ot_has_type.

Arguments mkOTerm A {AU%type RU%signature} {otfr} x {ht}.

Instance OTHasType_mkOTerm A AU RU x y otr htx hty (ht:@OTHasType A AU RU x y)
  : OTHasType A (ot_R A) (@mkOTerm A AU RU otr x htx) (@mkOTerm A AU RU otr y hty).
Proof.
  constructor. apply (ot_lift_Proper x y). apply ot_has_type.
Qed.


(***
 *** OT Typing Rules for Common Operations
 ***)

(*
Instance OTHasType_Proper A AU R (x:AU)
           {ote:OTForRel A R} {prp:Proper R x} :
  OTHasType A R x x.
  constructor; assumption.
Qed.

Instance Proper_fst A B : Proper (ot_R (OTpair A B) ==> ot_R A) fst.
Proof.
  intros p1 p2 Rp; destruct Rp; assumption.
Qed.

Instance Proper_snd A B : Proper (ot_R (OTpair A B) ==> ot_R B) snd.
Proof.
  intros p1 p2 Rp; destruct Rp; assumption.
Qed.

Instance Proper_pair A B : Proper (ot_R A ==> ot_R B ==> ot_R (OTpair A B)) pair.
Proof.
  intros a1 a2 Ra b1 b2 Rb; split; assumption.
Qed.
*)

Instance OTHasType_fst A B :
  OTHasType (OTarrow (OTpair A B) A) (pairR (ot_R A) (ot_R B) ==> ot_R A) fst fst.
Proof.
  apply OTHasType_Proper.
  intros p1 p2 Rp; destruct Rp; assumption.
Defined.

(*
Hint Extern 0 (@OTHasType _ _ fst fst) =>
apply OTHasType_fst : typeclass_instances.
*)

Instance OTHasType_snd A B :
  OTHasType (OTarrow (OTpair A B) B) (ot_R (OTpair A B) ==> ot_R B) snd snd.
Proof.
  apply OTHasType_Proper.
  intros p1 p2 Rp; destruct Rp; assumption.
Defined.

(*
Hint Extern 0 (@OTHasType _ _ snd snd) =>
eapply OTHasType_snd : typeclass_instances.
 *)

Instance OTHasType_pair A B :
  OTHasType (OTarrow A (OTarrow B (OTpair A B)))
            (ot_R A ==> ot_R B ==> ot_R (OTpair A B)) pair pair.
Proof.
  apply OTHasType_Proper.
  intros a1 a2 Ra b1 b2 Rb; split; assumption.
Defined.

(*
Hint Extern 0 (OTHasType _ _ pair pair) =>
apply OTHasType_pair : typeclass_instances.
 *)


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

(*
  Notation "F @t@ A" :=
    (otypef_app F A) (left associativity, at level 20).
 *)

Definition ofst {A B} : A *o* B -o> A := mkOTerm _ fst.
Definition osnd {A B} : A *o* B -o> B := mkOTerm _ snd.
Definition opair {A B} : A -o> B -o> A *o* B := mkOTerm _ pair.

Notation "( x ,o, y )" :=
  (opair @o@ x @o@ y)
    (no associativity, at level 0).


(***
 *** Automation for Ordered Terms
 ***)

Create HintDb OT.

(* Split ot_equiv equalities into the left and right cases *)
Definition prove_ot_equiv A (x y : ot_Type A)
           (pf1: x <o= y) (pf2 : y <o= x) : x =o= y :=
  conj pf1 pf2.

Hint Resolve prove_ot_equiv : OT.

(* Extensionality for ot_R *)
Definition ot_arrow_ext (A B:OType) (f1 f2 : A -o> B)
           (pf:forall x y, x <o= y -> f1 @o@ x <o= f2 @o@ y) : f1 <o= f2 := pf.

Hint Resolve ot_arrow_ext : OT.

(* Application commutes with ot_lift *)
(* FIXME: don't use this! *)
(*
Definition ot_lift_apply (A B:OType) AU RAU BU RBU
      (otfA:@OTForType A AU RAU) (otfB:@OTForRel B BU RBU)
      (f:AU -> BU) prp arg :
  ot_lift (OTForRel:=OTForRel_fun A B AU RAU BU RBU otfA otfB) f prp @o@ arg
  = ot_lift (OTForRel:=otfB) (f (ot_unlift_iso arg)) (prp _ _ (reflexivity _))
  := eq_refl.
*)

(* ot_unlift_iso for OTForType_refl is just the identity *)
(* NOTE: also don't use this directly *)
(*
Lemma ot_unlift_iso_OTForType_refl_id (A:OType) x :
  ot_unlift_iso (OTForType:=OTForType_refl A) x = x.
  reflexivity.
Qed.
*)

(* Tactic to simplify ot_unlift_iso x to just x *)
(*
Ltac simpl_ot_unlift_iso :=
  lazymatch goal with
  | |- context ctx [@ot_unlift_iso _ _ _ (OTForType_refl ?A) ?x] =>
    let new_goal := context ctx [x] in
    change new_goal
  end.
 *)

(* Tactic to simplify mkOTerm x to just x *)
(*
Definition simpl_mkOTerm_refl A x ht :
  mkOTerm (otfr:=OTForRel_OTForType _ _ _ (OTForType_refl A)) A x (ht:=ht) = x
  := eq_refl.
*)

Ltac simpl_mkOTerm_refl :=
  lazymatch goal with
  | |- context ctx [@mkOTerm
                      _ _ _
                      (OTForRel_OTForType _ _ _ (OTForType_refl _)) _ ?x _] =>
    let new_goal := context ctx [x] in
    change new_goal
  end.


(* Application commutes with mkOTerm *)
(* NOTE: Don't use this directly; it is just here to inform the change tactic
used in prove_OT, below *)
(*
Definition mkOTerm_apply (A B:OType) AU RAU BU RBU
      (otfA:@OTForType A AU RAU) (otfB:@OTForRel B BU RBU)
      (f:AU -> BU) ht arg :
  mkOTerm (A -o> B) (otfr:=OTForRel_fun A B AU RAU BU RBU otfA otfB)
          f (ht:=ht) @o@ arg
  =
  mkOTerm B (otfr:=otfB)
          (ht:=
             {| ot_has_type :=
                  (ot_has_type (OTHasType:=ht)) _ _ (reflexivity _) |})
          (f (ot_unlift_iso arg))
  := eq_refl.
 *)

(* Tactic to simplify mkOTerm f @o@ x to f (ot_unlift_iso x) *)
Ltac simpl_mkOTerm_apply :=
  lazymatch goal with
  | |- context
         ctx
         [@mkOTerm
            _ _ _
            (OTForRel_fun ?A ?B ?AU ?RAU ?BU ?RBU (OTForType_refl _) ?otfB) ?f ?ht
         @o@ ?arg] =>
    let new_goal :=
        context
          ctx
          [mkOTerm B (otfr:=otfB)
                   (ht:=
                      {| ot_has_type :=
                           (ot_has_type (OTHasType:=ht)) _ _ (reflexivity _) |})
                   (f arg)]
    in change new_goal; cbv beta
(*
  | |- context
         ctx
         [@mkOTerm
            _ _ _
            (OTForRel_fun ?A ?B ?AU ?RAU ?BU ?RBU ?otfA ?otfB) ?f ?ht
         @o@ ?arg] =>
    let new_goal :=
        context
          ctx
          [mkOTerm B (otfr:=otfB)
                   (ht:=
                      {| ot_has_type :=
                           (ot_has_type (OTHasType:=ht)) _ _ (reflexivity _) |})
                   (f (ot_unlift_iso arg))]
    in change new_goal; cbv beta
*)
  end.

(* Add the above rules to the OT rewrite set *)
(* Hint Rewrite @mkOTerm_apply @ot_unlift_iso_OTForType_refl_id : OT. *)

(* Tactic to apply rewrites in the OT rewrite set *)
Ltac rewrite_OT := rewrite_strat (topdown (hints OT)).

(* General tactic to try to prove theorems about ordered terms *)
Ltac prove_OT :=
  repeat first [simpl_mkOTerm_refl | simpl_mkOTerm_apply];
  try rewrite_OT;
  lazymatch goal with
  | |- ot_equiv _ _ _ => split
  | |- _ => idtac
  end.
  (* repeat (apply ot_arrow_ext; intros). *)


(***
 *** Examples of Ordered Terms
 ***)

Module OTExamples.

Definition ex1 := mkOTerm (OTProp -o> OTProp) (fun p => p).
Eval compute in (ot_unlift ex1 : Prop -> Prop).

Definition ex2 {A} := mkOTerm (A -o> A) (fun p => p).
Eval simpl in (fun A:OType => ot_unlift (@ex2 A) : A -> A).

Definition ex2' {A} := mkOTerm (A -o> A -o> A) (fun p1 p2 => p1).
Eval simpl in (fun A:OType => ot_unlift (@ex2' A) : A -> A -> A).

(* FIXME HERE: ex3 does not work without type annotations on fun vars! I think
the problem is that the inferred types of the fun vars are evars that depend on
all the previous vars, so it looks like a dependent forall type and OTForRel_fun
does not apply. *)
Definition ex3 {A} :=
  mkOTerm (A -o> A -o> A -o> A -o> A) (fun p1 p2 p3 p4 => p1).
Eval simpl in (fun A:OType => ot_unlift (@ex3 A) : A -> A -> A -> A -> A).

Definition ex4 {A B} : (A *o* B -o> A) := mkOTerm _ (fun p => fst p).
Eval simpl in (fun (A B:OType) => ot_unlift ex4 : A * B -> A).

Definition ex5 {A B} : A *o* B -o> B *o* A :=
  mkOTerm _ (fun p => (snd p, fst p)).
Eval simpl in (fun (A B:OType) => ot_unlift ex5 : A *o* B -> B *o* A).

(*
Definition ex6 {A B C} : A *o* B *o* C -o> C *o* A :=
  mkOTerm _ (fun triple => (snd triple, fst (fst triple))).
 *)

Definition ex6 {A B C} : A *o* B *o* C -o> C *o* A :=
  mkOTerm _ (fun triple => (osnd @o@ triple , ofst @o@ (ofst @o@ triple))).

Definition ex7 {A B C} : (A *o* B -o> C) -o> C -o> A -o> B -o> C :=
  mkOTerm ((A *o* B -o> C) -o> C -o> A -o> B -o> C)
          (fun (f:A *o* B -o> C) (c:C) a b => f @o@ (a ,o, b)).

End OTExamples.
