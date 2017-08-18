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

Class OType (T:Type) (R:relation T) : Prop :=
  {
    ot_PreOrder :> PreOrder R
  }.

Definition ot_Type `(A:OType) : Type := T.
Coercion ot_Type : OType >-> Sortclass.
Definition ot_R `(A:OType) : relation T := R.

(* The equivalence relation for an OrderedType *)
Definition ot_equiv `(A:OType) : relation T :=
  fun x y => ot_R A x y /\ ot_R A y x.

Instance ot_equiv_Equivalence `(A:OType) : Equivalence (ot_equiv A).
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
Instance OTProp : OType Prop Basics.impl.
Proof.
  constructor; constructor; auto with typeclass_instances.
Qed.

(* The discrete ordered type, where things are only related to themselves *)
Definition OTdiscrete T : OType T eq.
Proof.
  constructor; auto with typeclass_instances.
Qed.

(* The only ordered type over unit is the discrete one *)
Instance OTunit : OType unit eq := OTdiscrete unit.

(* The ordered type of natural numbers using <= *)
Instance OTnat : OType nat le.
Proof.
  constructor; auto with typeclass_instances.
Qed.

(* Flip the ordering of an OType *)
(* NOTE: we don't want this to be an instance, since applying it in proof search
leads to infinite regress... *)
Definition OTflip `(A:OType) : OType T (Basics.flip R).
Proof.
  constructor; auto with typeclass_instances.
Qed.

(* The pointwise relation on pairs *)
Definition pairR {T U} (RT:relation T) (RU:relation U) : relation (T*U) :=
  fun p1 p2 => RT (fst p1) (fst p2) /\ RU (snd p1) (snd p2).

(* The non-dependent product ordered type, where pairs are related pointwise *)
Instance OTpair `(A:OType) `(B: OType) : OType (T*T0) (pairR R R0).
Proof.
  repeat constructor; try reflexivity.
  { destruct H; destruct H0; transitivity (fst y); assumption. }
  { destruct H; destruct H0; transitivity (snd y); assumption. }
Qed.

(* The sort-of pointwise relation on sum types *)
Definition sumR {T U} (RT:relation T) (RU:relation U) : relation (T+U) :=
  fun sum1 sum2 =>
    match sum1, sum2 with
    | inl x, inl y => RT x y
    | inl x, inr y => False
    | inr x, inl y => False
    | inr x, inr y => RU x y
    end.

(* The non-dependent sum ordered type, where objects are only related if they
are both "left"s or both "right"s *)
Instance OTsum `(A:OType) `(B:OType) : OType (T+T0) (sumR R R0).
Proof.
  repeat constructor.
  { intro s; destruct s; simpl; reflexivity. }
  { intros s1 s2 s3 R12 R23.
    destruct s1; destruct s2; destruct s3;
      try (elimtype False; assumption); simpl.
    - transitivity t0; assumption.
    - transitivity t0; assumption. }
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
Record Pfun `(A:OType) `(B: OType) :=
  {
    pfun_app : ot_Type A -> ot_Type B;
    pfun_Proper :> Proper (ot_R A ==> ot_R B) pfun_app
  }.

Arguments pfun_app [_ _ _ _ _ _] _ _.
Arguments pfun_Proper [_ _ _ _ _ _] _ _ _ _.

(* Infix "@" := pfun_app (at level 50). *)

(* The non-dependent function ordered type *)
Definition OTarrow_R `(A:OType) `(B:OType) : relation (Pfun A B) :=
  fun f g =>
    forall a1 a2, ot_R A a1 a2 -> ot_R B (pfun_app f a1) (pfun_app g a2).

Instance OTarrow `(A:OType) `(B:OType) : OType _ (OTarrow_R A B).
Proof.
  repeat constructor.
  { intros f; apply (pfun_Proper f). }
  { intros f g h Rfg Rgh a1 a2 Ra. transitivity (pfun_app g a1).
    - apply (Rfg a1 a1). reflexivity.
    - apply Rgh; assumption. }
Qed.

(* Curry a Pfun *)
Program Definition pfun_curry `(A:OType) `(B:OType) `(C:OType)
        (pfun : Pfun (OTpair A B) C) : Pfun A (OTarrow B C) :=
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
Program Definition pfun_uncurry `(A:OType) `(B:OType) `(C:OType)
        (pfun : Pfun A (OTarrow B C)) : Pfun (OTpair A B) C :=
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
 *** Ordered Type Functions
 ***)

Class OTypeF (TF: forall `(A:OType), Type)
      (RF: forall `(A:OType), relation (TF A)) : Prop :=
  otypef_otype : forall `(A:OType), OType (TF A) (RF A).

Definition OTypeF_app `(F:OTypeF) `(A:OType) : OType (TF _ _ A) (RF _ _ A) :=
  otypef_otype A.

Instance OType_OTypeF_app `(F:OTypeF) `(A:OType) :
  OType (ot_Type (OTypeF_app F A)) (RF _ _ A) :=
  otypef_otype A.


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

  Notation "F @t@ A" :=
    (OTypeF_app F A) (left associativity, at level 20).

End OTNotations.


(***
 *** Building Proper Functions
 ***)

Class OTEnrich `(A:OType) {AU} (RA:relation AU) : Type :=
  {
    ot_lift : forall a, Proper RA a -> A;
    ot_lift_Proper :
      forall a1 a2 prp1 prp2,
        RA a1 a2 -> ot_R A (ot_lift a1 prp1) (ot_lift a2 prp2);
    ot_unlift : A -> AU;
  }.

Arguments OTEnrich {T R} A {AU%type} RA%signature.

Program Instance OTEnrich_refl `(A:OType) : OTEnrich A R :=
  {
    ot_lift := fun a _ => a;
    ot_lift_Proper := _;
    ot_unlift := fun a => a;
  }.

Program Instance OTEnrich_fun `(A:OType) `(B:OType) BU RB
        `{@OTEnrich _ _ B BU RB} :
  OTEnrich (OTarrow A B) (R ==> RB) :=
  {
    ot_lift := fun f prp =>
                 Build_Pfun _ _ A _ _ B (fun a => ot_lift (f a) _) _;
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


Class OTHasType `(A:OType) {AU} (RA:relation AU) (x y:AU) : Type :=
  {
    ot_wf_type : OTEnrich A RA;
    ot_wf_term : RA x y;
  }.

Arguments OTHasType {_ _} A {AU%type} RA%signature x y.

(* NOTE: We only want this to apply to terms that are syntactically lambdas, so
we use an Extern hint, below. *)
Definition OTHasType_lambda `(A:OType) `(B:OType) BU RB `{@OTEnrich _ _ B BU RB}
         (fl fr:T -> BU)
         (pf: forall xl xr (pf:OTHasType A R xl xr),
             OTHasType B RB (fl xl) (fr xr)) :
  OTHasType (OTarrow A B) (R ==> RB) fl fr.
Proof.
  constructor.
  auto with typeclass_instances.
  intros xl xr Rx. apply pf. constructor.
  auto with typeclass_instances.
  assumption.
Defined.

(* Hint to apply OTHasType_lambda on lambdas *)
Hint Extern 2 (OTHasType _ _ (fun _ => _) (fun _ => _)) =>
apply OTHasType_lambda : typeclass_instances.

Instance OTHasType_app `(A:OType) AU RA `(B:OType) BU RB
         (fl fr:AU -> BU) argl argr
         `{@OTEnrich _ _ B BU RB}
         `{@OTHasType _ _ (OTarrow A B) _ (RA ==> RB) fl fr}
         `{@OTHasType _ _ A _ RA argl argr}
 : OTHasType B RB (fl argl) (fr argr) | 3.
Proof.
  constructor.
  assumption.
  apply H0. apply ot_wf_term.
Defined.

Instance OTHasType_pfun_app `(A:OType) `(B:OType) (fl fr:OTarrow A B) argl argr
         `{@OTHasType _ _ (OTarrow A B) _ (OTarrow_R A B) fl fr}
         `{@OTHasType _ _ A _ R argl argr}
 : OTHasType B R0 (pfun_app fl argl) (pfun_app fr argr) | 2.
Proof.
  constructor.
  auto with typeclass_instances.
  apply (ot_wf_term (OTHasType:=H)).
  apply (ot_wf_term (OTHasType:=H0)).
Defined.


(* NOTE: this is not an instance because it is not syntax-driven, like our other
rules for OTHasType. Instead, this definition is used as a helper to build
other instances of OTHasType. *)
Definition OTHasType_Proper `{OTEnrich} (x:AU) :
  Proper RA x -> OTHasType A RA x x.
  intros; constructor; assumption.
Qed.

Instance OTHasType_refl `(A:OType) (x : T) : OTHasType A R x x.
Proof.
  apply OTHasType_Proper. unfold Proper. reflexivity.
Qed.

Program Definition mkOTerm `(A:OType) {AU RA} (x:AU)
        `{@OTHasType _ _ A _ RA x x} : A :=
  ot_lift (OTEnrich:=ot_wf_type) x ot_wf_term.

Arguments mkOTerm {_ _} A {AU%type RA%signature} x {H}.


(***
 *** OT Typing Rules for Common Operations
 ***)

(*
Instance OTHasType_Proper A AU R (x:AU)
           {ote:OTEnrich A R} {prp:Proper R x} :
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

Instance OTHasType_fst `(A:OType) `(B:OType) :
  OTHasType (OTarrow (OTpair A B) A) (pairR R R0 ==> R) fst fst.
Proof.
  apply OTHasType_Proper.
  intros p1 p2 Rp; destruct Rp; assumption.
Defined.

Instance OTHasType_snd `(A:OType) `(B:OType) :
  OTHasType (OTarrow (OTpair A B) B) (pairR R R0 ==> R0) snd snd.
Proof.
  apply OTHasType_Proper.
  intros p1 p2 Rp; destruct Rp; assumption.
Defined.

Instance OTHasType_pair `(A:OType) `(B:OType) :
  OTHasType (OTarrow A (OTarrow B (OTpair A B)))
            (R ==> R0 ==> pairR R R0) pair pair.
Proof.
  apply OTHasType_Proper.
  intros a1 a2 Ra b1 b2 Rb; split; assumption.
Defined.


(***
 *** Examples of Ordered Terms
 ***)

Module OTExamples.
Import OTNotations.

Definition ex1 := mkOTerm (OTProp -o> OTProp) (fun p => p).
Eval compute in (ot_unlift ex1 : OTProp -> OTProp).

Definition ex2 `{A:OType} := mkOTerm (A -o> A) (fun p => p).
Eval simpl in (fun `(A:OType) => ot_unlift ex2 : A -> A).

Definition ex3 `{A:OType} :=
  mkOTerm (A -o> A -o> A -o> A -o> A) (fun (p1 p2 p3 p4:A) => p1).
Eval simpl in (fun `(A:OType) => ot_unlift ex3 : A -> A  -> A -> A -> A).

Definition ex4 `{A:OType} `{B:OType} : (A *o* B -o> A) :=
  mkOTerm _ (fun p => fst p).
Eval compute in (fun `(A:OType) `(B:OType) => ot_unlift ex4 : A * B -> A).

(*
Definition blah {A B:OType} {R}
           `{OTHasType (A *o* B -o> B *o* A) _ R
                       (fun p : A * B => (snd p, fst p))
                       (fun p => (snd p, fst p))} : Prop := True.
Definition blah2 {A B} : Prop := blah (A:=A) (B:=B).
 *)

Definition ex5 `{A:OType} `{B:OType} : A *o* B -o> B *o* A :=
  mkOTerm _ (fun p: A * B => (snd p, fst p)).

Definition ex6 `{A:OType} `{B:OType} `{C:OType} : A *o* B *o* C -o> C *o* A :=
  mkOTerm _ (fun triple : (A * B) * C => (snd triple, fst (fst triple))).

End OTExamples.
