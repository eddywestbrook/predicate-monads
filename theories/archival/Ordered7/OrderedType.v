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
    pfun_Proper : Proper (ot_R A ==> ot_R B) pfun_app
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
