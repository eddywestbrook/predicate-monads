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



(* Infix "@" := pfun_app (at level 50). *)

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

(* Curry a Pfun *)
(*
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
 *)

(* Currying and uncurrying of pfuns form an adjunction *)
(* FIXME: figure out the simplest way of stating this adjunction *)


(* OTarrow is right adjoint to OTpair, meaning that (OTarrow (OTpair A B) C) is
isomorphic to (OTarrow A (OTarrow B C)). The following is the first part of this
isomorphism, mapping left-to-right. *)


(* FIXME: could also do a forall type, but need the second type argument, B, to
itself be proper, i.e., to be an element of OTarrow A OType. Would also need a
dependent version of OTContext, below. *)


(* pfun_app is always Proper *)
Instance Proper_pfun_app A B `{OType A} `{OType B} :
  Proper (ot_R ==> ot_R ==> ot_R) (@pfun_app A B _ _).
Proof.
  intros f1 f2 Rf a1 a2 Ra. apply Rf; assumption.
Qed.

(* pfun_app is always Proper w.r.t. ot_equiv *)
Instance Proper_pfun_app_equiv A B `{OType A} `{OType B} :
  Proper (ot_equiv ==> ot_equiv ==> ot_equiv) (@pfun_app A B _ _).
Proof.
  intros f1 f2 Rf a1 a2 Ra; destruct Rf; destruct Ra.
  split; apply Proper_pfun_app; assumption.
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

Instance Proper_pair A B `{OType A} `{OType B} :
  Proper (ot_R ==> ot_R ==> ot_R) (pair : A -> B -> A*B).
Proof.
  repeat intro; split; assumption.
Qed.

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
 *** Automation for Ordered Terms
 ***)

Instance Proper_ot_R_ot_R A `{OType A} :
  Proper (Basics.flip ot_R ==> ot_R ==> Basics.impl) ot_R.
Proof.
  intros x1 x2 Rx y1 y2 Ry Rxy.
  transitivity x1; [ assumption | ]; transitivity y1; assumption.
Qed.

Instance Proper_ot_equiv_ot_R A `{OType A} :
  Proper (ot_equiv ==> ot_equiv ==> iff) ot_R.
Proof.
  intros x1 x2 Rx y1 y2 Ry; destruct Rx; destruct Ry; split; intro Rxy.
  transitivity x1; [ assumption | ]; transitivity y1; assumption.
  transitivity x2; [ assumption | ]; transitivity y2; assumption.
Qed.

Instance Proper_ot_R_pfun_app A B `{OType A} `{OType B} :
  Proper (ot_R ==> ot_R ==> ot_R) (@pfun_app A B _ _).
Proof.
  intros f1 f2 Rf x1 x2 Rx. apply Rf; apply Rx.
Qed.

Instance Proper_ot_R_pfun_app_partial A B `{OType A} `{OType B} f :
  Proper (ot_R ==> ot_R) (@pfun_app A B _ _ f).
Proof.
  apply pfun_Proper.
Qed.


Create HintDb OT.

(* Split ot_equiv equalities into the left and right cases *)
Definition split_ot_equiv A `{OTRelation A} (x y : A)
           (pf1: x <o= y) (pf2 : y <o= x) : x =o= y :=
  conj pf1 pf2.

Hint Resolve split_ot_equiv : OT.

(* Extensionality for ot_R *)
(*
Definition ot_arrow_ext A B `{OTRelation A} `{OTRelation B} (f1 f2 : A -o> B)
           (pf:forall x y, x <o= y -> f1 @o@ x <o= f2 @o@ y) : f1 <o= f2 := pf.

Hint Resolve ot_arrow_ext : OT.
*)


(* Add the above rules to the OT rewrite set *)
(* Hint Rewrite @mkOTerm_apply @ot_unlift_iso_OTForType_refl_id : OT. *)

(* Eta-equality for pairs *)
Lemma ot_pair_eta A B `{OType A} `{OType B} (x: A*B) :
  (fst x , snd x) =o= x.
  split; split; reflexivity.
Qed.

Hint Rewrite ot_pair_eta : OT.

(* Tactic to apply rewrites in the OT rewrite set *)
Ltac rewrite_OT := rewrite_strat (topdown (hints OT)).

(* General tactic to try to prove theorems about ordered terms *)
Ltac prove_OT :=
  simpl; try (rewrite_OT; simpl);
  lazymatch goal with
  | |- @ot_equiv (_ -o> _) _ _ _ =>
    split; apply ot_arrow_ext; intro; intro; intro; prove_OT
  | |- @ot_R (_ -o> _) _ _ _ =>
    apply ot_arrow_ext; intro; intro; intro; prove_OT
  | |- _ =>
    match goal with
    | H : (?x <o= ?y) |- _ => rewrite H; prove_OT
    | H : (?x =o= ?y) |- _ => rewrite H; prove_OT
    | |- _ => try reflexivity
    end
  end.


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
  ofun (fun p => fst p).
(* Eval simpl in (fun (A B:OType) => pfun_app ex4 : A * B -> A). *)

Definition ex5 {A B} `{OType A} `{OType B} : A * B -o> B * A :=
  ofun (fun p => (snd p , fst p)).
(* Eval simpl in (fun (A B:OType) => pfun_app ex5 : A *o* B -> B *o* A). *)

Definition ex6 {A B C} `{OType A} `{OType B} `{OType C} : A * B * C -o> C * A :=
  ofun (fun triple => (snd triple , fst (fst triple))).

Definition ex7 {A B C} `{OType A} `{OType B} `{OType C}
  : (A * B -o> C) -o> C -o> A -o> B -o> C :=
  ofun (fun f =>
               ofun
                 (fun c =>
                    ofun
                      (fun a =>
                         ofun (fun b => f @o@ (a , b))))).

End OTExamples.
