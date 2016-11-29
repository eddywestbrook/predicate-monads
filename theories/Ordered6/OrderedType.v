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
 *** Building Proper Functions
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
  }.

Instance OTForType_refl (A:OType) : OTForType A (ot_R A) :=
  {
    ot_lift_iso := fun a => a;
    ot_lift_iso_Proper := fun a1 a2 Ra => Ra;
    ot_unlift_iso := fun a => a;
    ot_unlift_iso_Proper := fun a1 a2 Ra => Ra;
    ot_for_type_PreOrder := ot_PreOrder A;
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


(* States that A is a valid OType for the Proper elements of AU *)
Class OTForRel (A:OType) {AU} (RU:relation AU) : Type :=
  {
    ot_lift : forall a, Proper RU a -> A;
    ot_lift_Proper :
      forall a1 a2 prp1 prp2,
        RU a1 a2 -> ot_R A (ot_lift a1 prp1) (ot_lift a2 prp2);
    ot_unlift : A -> AU;
    ot_unlift_Proper : Proper (ot_R A ==> RU) ot_unlift;
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
        (_:@OTForType A AU RU) : OTForRel A RU :=
  {
    ot_lift := fun a _ => ot_lift_iso a;
    ot_unlift := ot_unlift_iso;
  }.
Next Obligation.
  apply ot_lift_iso_Proper. assumption.
Qed.
Next Obligation.
  intros a1 a2 Ra; apply ot_unlift_iso_Proper; assumption.
Qed.

Program Instance OTForRel_fun (A B:OType) AU RAU BU RBU
        (otA:@OTForType A AU RAU) (otB:@OTForRel B BU RBU) :
  OTForRel (OTarrow A B) (RAU ==> RBU) :=
  {
    ot_lift := fun f prp =>
                 {| pfun_app :=
                      fun a =>
                        ot_lift (OTForRel:=otB) (f (ot_unlift_iso a)) _ |};
    ot_lift_Proper := _;
    ot_unlift := fun pfun a => ot_unlift (pfun_app pfun (ot_lift_iso a));
  }.
Next Obligation.
  apply prp. reflexivity.
Qed.
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

(*
(* Tactic to prove OTForRel goals *)
Ltac prove_OTForRel :=
  lazymatch goal with
  | |- @OTForRel _ _ (_ -> _) _ => apply OTForRel_fun
  | |- OTForRel ?A ?B => apply OTForRel_refl
  end.

(* Hint to use the prove_OTForRel tactic; we need this because often the
relation part is an evar, so will not match any of the instances above *)
Hint Extern 1 (OTForRel _ _) => prove_OTForRel : typeclass_instances.
 *)


(* A version of OTForType that is deferred until all other typeclass
instantiation has finished *)
Class OTForType_Defer (A:OType) {AU} (RU:relation AU) : Type :=
  {
    ot_for_type_defer : OTForType A RU;
  }.

Instance OTForType_Defer_OTForType `(ot:OTForType) : OTForType_Defer A RU | 99 :=
  {| ot_for_type_defer := ot |}.


Class OTHasType (A:OType) {AU} (RU:relation AU) (x y:AU) : Type :=
  {
    ot_wf_type : OTForRel A RU;
    ot_wf_term : RU x y;
  }.

Arguments OTHasType A {AU%type} RU%signature x y.

Instance OTHasType_app (A:OType) AU RAU (B:OType) BU RBU
         (fl fr:AU -> BU) argl argr
         `(OTForRel B BU RBU)
         `(OTHasType (OTarrow A B) _ (RAU ==> RBU) fl fr)
         `(OTHasType A _ RAU argl argr)
 : OTHasType B RBU (fl argl) (fr argr) | 3.
Proof.
  constructor.
  assumption.
  apply H0. apply ot_wf_term.
Defined.

Instance OTHasType_pfun_app (A B:OType) (fl fr:OTarrow A B) argl argr
         (otef:OTHasType (OTarrow A B) (ot_R (OTarrow A B)) fl fr)
         (otea:OTHasType A (ot_R A) argl argr)
 : OTHasType B (ot_R B) (pfun_app fl argl) (pfun_app fr argr) | 2.
Proof.
  constructor.
  typeclasses eauto.
  apply (ot_wf_term (OTHasType:=otef)).
  apply (ot_wf_term (OTHasType:=otea)).
Defined.

(* NOTE: We only want this to apply to terms that are syntactically lambdas, so
we use an Extern hint, below. *)
Definition OTHasType_lambda (A B:OType) AU RAU BU RBU
           (otA:OTForType_Defer A RAU) (otB:OTForRel B RBU)
         (fl fr:AU -> BU)
         (pf: forall xl xr (pf:OTHasType A RAU xl xr),
             OTHasType B RBU (fl xl) (fr xr)) :
  OTHasType (OTarrow A B) (RAU ==> RBU) fl fr.
Proof.
  constructor.
  apply OTForRel_fun; try apply ot_for_type_defer; typeclasses eauto.
  intros xl xr Rx. apply pf. constructor.
  apply OTForRel_OTForType. apply ot_for_type_defer.
  assumption.
Defined.


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
    eapply (OTHasType_lambda _ _ _ _ _ _ _ _ (fun x => f) (fun y => g))
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

Program Definition mkOTerm (A:OType) {AU RU} (x:AU)
        {ht:@OTHasType A AU RU x x} : ot_Type A :=
  ot_lift (OTForRel:=ot_wf_type) x ot_wf_term.

Arguments mkOTerm A {AU%type RU%signature} x {ht}.


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

Module OTNotations.

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

  Definition ot_fst {A B} : A *o* B -o> A := mkOTerm _ fst.
  Definition ot_snd {A B} : A *o* B -o> B := mkOTerm _ snd.
  Definition ot_pair {A B} : A -o> B -o> A *o* B := mkOTerm _ pair.

  Notation "( x ,o, y )" :=
    (ot_pair @o@ x @o@ y)
      (no associativity, at level 0).

End OTNotations.


(***
 *** Examples of Ordered Terms
 ***)

Module OTExamples.
Import OTNotations.

Definition ex1 := mkOTerm (OTProp -o> OTProp) (fun p => p).
Eval compute in (ot_unlift ex1 : Prop -> Prop).

Definition ex2 {A} := mkOTerm (A -o> A) (fun p => p).
Eval simpl in (fun A:OType => ot_unlift (@ex2 A) : A -> A).

Definition ex3 {A} :=
  mkOTerm (A -o> A -o> A -o> A -o> A) (fun p1 p2 p3 p4 => p1).
Eval simpl in (fun A:OType => ot_unlift (@ex3 A) : A -> A  -> A -> A -> A).

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
  mkOTerm _ (fun triple => (ot_snd @o@ triple , ot_fst @o@ (ot_fst @o@ triple))).

Definition ex7 {A B C} : (A *o* B -o> C) -o> C -o> A -o> B -o> C :=
  mkOTerm _ (fun f c a b => f @o@ (a ,o, b)).

End OTExamples.
