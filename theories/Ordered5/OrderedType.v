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

Class OType (T:Type) : Type :=
  ot_R : relation T.

Arguments ot_R {_} _ _ _.

Class ValidOType `(A:OType) : Prop :=
  { ot_PreOrder :> PreOrder (ot_R A) }.

Definition ot_Type `(A:OType) : Type := T.
Coercion ot_Type : OType >-> Sortclass.

(*
Instance PreOrder_OType `(valid:ValidOType) : PreOrder A.
Proof. auto with typeclass_instances. Qed.

Instance Reflexive_OType `(ValidOType) : Reflexive A.
Proof. auto with typeclass_instances. Qed.

Instance Transitive_OType `(ValidOType) : Transitive A.
Proof. auto with typeclass_instances. Qed.

Instance Reflexive_ValidOType {T} (A:relation T) (valid:ValidOType A) : Reflexive A.
Proof. auto with typeclass_instances. Qed.

Instance Transitive_ValidOType {T} (A:relation T) (valid:ValidOType A) : Transitive A.
Proof. auto with typeclass_instances. Qed.
 *)

Instance PreOrder_ot_R `(valid:ValidOType) : PreOrder (ot_R A).
Proof. typeclasses eauto. Qed.

(* The equivalence relation for an OrderedType *)
Definition ot_equiv `(A:OType) : relation T :=
  fun x y => ot_R A x y /\ ot_R A y x.

Instance ot_equiv_Equivalence `{ValidOType} : Equivalence (ot_equiv A).
Proof.
  constructor; intro; intros.
  { split; reflexivity. }
  { destruct H0; split; assumption. }
  { destruct H0; destruct H1; split; transitivity y; assumption. }
Qed.


(***
 *** Commonly-Used Ordered Types
 ***)

(* The ordered type of propositions *)
Instance OTProp : OType Prop := Basics.impl.
Instance Valid_OTProp : ValidOType OTProp.
Proof.
  constructor; constructor; typeclasses eauto.
Qed.

(* The discrete ordered type, where things are only related to themselves. NOTE:
we don't make this an instance, because we don't want proof search finding it
all the time... *)
Definition OTdiscrete T : OType T := eq.
Instance Valid_OTdiscrete T : ValidOType (OTdiscrete T).
Proof.
  constructor; compute; typeclasses eauto.
Qed.

(* The only ordered type over unit is the discrete one *)
Instance OTunit : OType unit := OTdiscrete unit.
Instance Valid_OTunit : ValidOType OTunit := Valid_OTdiscrete unit.

(* The ordered type of natural numbers using <= *)
Instance OTnat : OType nat := le.
Instance Valid_OTnat : ValidOType OTnat.
Proof.
  constructor; typeclasses eauto.
Qed.

(* Flip the ordering of an OType *)
(* NOTE: we don't want this to be an instance, since applying it in proof search
leads to infinite regress... *)
Definition OTflip `(A:OType) : OType T := Basics.flip A.
Instance Valid_OTflip `(A:OType) (valid:ValidOType A) : ValidOType (OTflip A).
Proof.
  constructor; unfold OTflip, ot_R; fold (ot_R A). typeclasses eauto.
Qed.

(* Avoid infinite regress from repeatedly applying Valid_OTflip *)
Hint Cut [ !*; Valid_OTflip; Valid_OTflip ] : typeclass_instances.

(* The non-dependent product ordered type, where pairs are related pointwise *)
Instance OTpair {TA} (A:OType TA) {TB} (B:OType TB) : OType (TA*TB) :=
  fun p1 p2 => ot_R A (fst p1) (fst p2) /\ ot_R B (snd p1) (snd p2).

Instance Valid_OTpair `(A:OType) `(B: OType) (vA:ValidOType A)
         (vB:ValidOType B) : ValidOType (OTpair A B).
Proof.
  repeat constructor; try reflexivity.
  { destruct H; destruct H0; transitivity (fst y); assumption. }
  { destruct H; destruct H0; transitivity (snd y); assumption. }
Qed.

(* The non-dependent sum ordered type, where objects are only related if they
are both "left"s or both "right"s *)
Instance OTsum {TA TB} (A:OType TA) (B:OType TB) : OType (TA+TB) :=
  fun sum1 sum2 =>
    match sum1, sum2 with
    | inl x, inl y => ot_R A x y
    | inl x, inr y => False
    | inr x, inl y => False
    | inr x, inr y => ot_R B x y
    end.

Instance Valid_OTsum `(A:OType) `(B:OType)
         (vA:ValidOType A) (vB:ValidOType B) : ValidOType (OTsum A B).
Proof.
  repeat constructor; unfold OTsum, ot_R; fold (ot_R A); fold (ot_R B).
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
Record Pfun {TA TB} (A:OType TA) (B: OType TB) :=
  {
    pfun_app : TA -> TB;
    pfun_Proper :> Proper (ot_R A ==> ot_R B) pfun_app
  }.

Arguments pfun_app [_ _ _ _] _ _.
Arguments pfun_Proper [_ _ _ _] _ _ _ _.

(* Infix "@" := pfun_app (at level 50). *)

(* The non-dependent function ordered type *)
Instance OTarrow `(A:OType) `(B:OType) : OType (Pfun A B) :=
  fun f g =>
    forall a1 a2, A a1 a2 -> B (pfun_app f a1) (pfun_app g a2).

Instance Valid_OTarrow `(A:OType) `(B:OType)
  (vA:ValidOType A) (vB:ValidOType B) : ValidOType (OTarrow A B).
Proof.
  repeat constructor.
  { intros f; apply (pfun_Proper f). }
  { fold (ot_R A); fold (ot_R B); intros f g h Rfg Rgh a1 a2 Ra.
    transitivity (pfun_app g a1).
    - apply (Rfg a1 a1). reflexivity.
    - apply Rgh; assumption. }
Qed.

(* Curry a Pfun *)
Program Definition pfun_curry `(A:OType) `(B:OType) `(C:OType)
        {vA:ValidOType A} {vB:ValidOType B} {vC:ValidOType C}
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
        {vA:ValidOType A} {vB:ValidOType B} {vC:ValidOType C}
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

Class OTypeF (TF: forall `(A:OType), Type) : Type :=
  otypef_app : forall `(A:OType), OType (TF A).

Arguments otypef_app [TF] _ [T] A _ _.

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
    (otypef_app F A) (left associativity, at level 20).

End OTNotations.


(***
 *** Building Proper Functions
 ***)

Class OTEnrich `(A:OType) {AU} (RU:relation AU) : Type :=
  {
    ot_lift : forall a, Proper RU a -> T;
    ot_lift_Proper :
      forall a1 a2 prp1 prp2,
        RU a1 a2 -> ot_R A (ot_lift a1 prp1) (ot_lift a2 prp2);
    ot_unlift : T -> AU;
  }.

Arguments OTEnrich {T} A {AU%type} RU%signature.

Program Instance OTEnrich_refl `(A:OType) : OTEnrich A (ot_R A) :=
  {
    ot_lift := fun a _ => a;
    ot_lift_Proper := _;
    ot_unlift := fun a => a;
  }.

Program Instance OTEnrich_fun `(A:OType) `(B:OType) BU RBU
        (vA:ValidOType A) (ote:@OTEnrich _ B BU RBU) :
  OTEnrich (OTarrow A B) (ot_R A ==> RBU) :=
  {
    ot_lift := fun f prp =>
                 {| pfun_app :=
                      fun a => ot_lift (OTEnrich:=ote) (f a) _ |};
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
  intros x1 x2 Rx. apply ot_lift_Proper. apply H. assumption.
Qed.


(* Tactic to prove OTEnrich goals *)
Ltac prove_OTEnrich :=
  lazymatch goal with
  | |- @OTEnrich _ _ (_ -> _) _ => apply OTEnrich_fun
  | |- OTEnrich ?A ?B => apply OTEnrich_refl
  end.

(* Hint to use the prove_OTEnrich tactic; we need this because often the
relation part is an evar, so will not match any of the instances above *)
Hint Extern 1 (OTEnrich _ _) => prove_OTEnrich : typeclass_instances.


Class OTHasType `(A:OType) {AU} (RU:relation AU) (x y:AU) : Type :=
  {
    ot_wf_type : OTEnrich A RU;
    ot_wf_term : RU x y;
  }.

Arguments OTHasType {_} A {AU%type} RU%signature x y.
Hint Mode OTHasType - - + - + +.

(* NOTE: We only want this to apply to terms that are syntactically lambdas, so
we use an Extern hint, below. *)
Definition OTHasType_lambda `(A:OType) `(B:OType)
           {vA:ValidOType A} BU RBU `{@OTEnrich _ B BU RBU}
         (fl fr:T -> BU)
         (pf: forall xl xr (pf:OTHasType A (ot_R A) xl xr),
             OTHasType B RBU (fl xl) (fr xr)) :
  OTHasType (OTarrow A B) (ot_R A ==> RBU) fl fr.
Proof.
  constructor.
  typeclasses eauto.
  intros xl xr Rx. apply pf. constructor.
  typeclasses eauto.
  assumption.
Defined.

Instance OTHasType_app `(A:OType) AU RAU `(B:OType) BU RBU
         (fl fr:AU -> BU) argl argr
         `{@OTEnrich _ B BU RBU}
         `{@OTHasType _ (OTarrow A B) _ (RAU ==> RBU) fl fr}
         `{@OTHasType _ A _ RAU argl argr}
 : OTHasType B RBU (fl argl) (fr argr) | 3.
Proof.
  constructor.
  assumption.
  apply H0. apply ot_wf_term.
Defined.

Instance OTHasType_pfun_app `(A:OType) `(B:OType) (fl fr:OTarrow A B) argl argr
         (otef:OTHasType (OTarrow A B) (ot_R (OTarrow A B)) fl fr)
         (otea:OTHasType A (ot_R A) argl argr)
 : OTHasType B (ot_R B) (pfun_app fl argl) (pfun_app fr argr) | 2.
Proof.
  constructor.
  typeclasses eauto.
  apply (ot_wf_term (OTHasType:=otef)).
  apply (ot_wf_term (OTHasType:=otea)).
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
  | |- OTHasType _ _ (fun x => ?f) (fun y => ?g) =>
    eapply (OTHasType_lambda _ _ _ _ (fun x => f) (fun y => g))
  end.

Hint Extern 2 (OTHasType _ _ (fun _ => _) (fun _ => _)) =>
try_OTHasType_lambda : typeclass_instances.

(* NOTE: this is not an instance because it is not syntax-driven, like our other
rules for OTHasType. Instead, this definition is used as a helper to build
other instances of OTHasType. *)
Definition OTHasType_Proper `{OTEnrich} (x:AU) :
  Proper RU x -> OTHasType A RU x x.
  intros; constructor; assumption.
Defined.

Instance OTHasType_refl `(vA:ValidOType) (x:T) : OTHasType A (ot_R A) x x.
Proof.
  apply OTHasType_Proper. unfold Proper. reflexivity.
Defined.

(*
Instance OTHasType_refl_rel {T} (A:relation T) {vA:ValidOType A} (x:T)
  : OTHasType A A x x := OTHasType_refl A x.
*)

Program Definition mkOTerm `(A:OType) {AU RU} (x:AU)
        `{@OTHasType _ A AU RU x x} : T :=
  ot_lift (OTEnrich:=ot_wf_type) x ot_wf_term.

Arguments mkOTerm {_} A {AU%type RU%signature} x {H}.


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

Instance OTHasType_fst `{ValidOType} `{ValidOType} :
  OTHasType (OTarrow (OTpair A A0) A) (ot_R (OTpair A A0) ==> ot_R A) fst fst.
Proof.
  apply OTHasType_Proper.
  intros p1 p2 Rp; destruct Rp; assumption.
Defined.

Instance OTHasType_snd `{ValidOType} `{ValidOType} :
  OTHasType (OTarrow (OTpair A A0) A0) (ot_R (OTpair A A0) ==> ot_R A0) snd snd.
Proof.
  apply OTHasType_Proper.
  intros p1 p2 Rp; destruct Rp; assumption.
Defined.

Instance OTHasType_pair `{ValidOType} `{ValidOType} :
  OTHasType (OTarrow A (OTarrow A0 (OTpair A A0)))
            (ot_R A ==> ot_R A0 ==> ot_R (OTpair A A0)) pair pair.
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
Eval compute in (ot_unlift ex1 : Prop -> Prop).

Definition ex2 `{ValidOType} := mkOTerm (A -o> A) (fun p => p).
Eval simpl in (fun `{ValidOType} => ot_unlift ex2 : A -> A).

Definition ex3 `{A:OType} {_:ValidOType A} :=
  mkOTerm (A -o> A -o> A -o> A -o> A) (fun p1 p2 p3 p4 => p1).
Eval simpl in (fun `(A:OType) => ot_unlift ex3 : A -> A  -> A -> A -> A).

Definition ex4 `{A:OType} `{B:OType} {_:ValidOType A} {_:ValidOType B}
  : (A *o* B -o> A) :=
  mkOTerm _ (fun p => fst p).
Eval simpl in (fun `{ValidOType} `{ValidOType} =>
                 ot_unlift ex4 : T * T0 -> T).

(*
Definition blah {A B:OType} {R}
           `{OTHasType (A *o* B -o> B *o* A) _ R
                       (fun p : A * B => (snd p, fst p))
                       (fun p => (snd p, fst p))} : Prop := True.
Definition blah2 {A B} : Prop := blah (A:=A) (B:=B).
 *)

Definition ex5 `{A:OType} `{B:OType} {_:ValidOType A} {_:ValidOType B}
  : A *o* B -o> B *o* A :=
  mkOTerm _ (fun p => (snd p, fst p)).
Eval simpl in (fun `{ValidOType} `{ValidOType} =>
                 ot_unlift ex5 : A *o* A0 -> A0 *o* A).


Definition ex6 `{A:OType} `{B:OType} `{C:OType}
           {_:ValidOType A} {_:ValidOType B} {_:ValidOType C}
  : A *o* B *o* C -o> C *o* A :=
  mkOTerm _ (fun triple => (snd triple, fst (fst triple))).

End OTExamples.
