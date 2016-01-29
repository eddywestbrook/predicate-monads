Require Export PredMonad.Monad.


(***
 *** The Predicate Monad Class
 ***)

(* FIXME: the universe constraints on M and PM could be different...? *)
Class PredMonadOps
            (M: Type -> Type) (PM : Type -> Type) :=
  { forallP: forall {A B: Type}, (A -> PM B) -> PM B;
    existsP: forall {A B: Type}, (A -> PM B) -> PM B;
    impliesP: forall {A: Type}, PM A -> PM A -> PM A;
    liftP: forall {A: Type}, M A -> PM A;
    entailsP: forall {A: Type} `{OrderOp A}, relation (PM A)
  }.

Definition andP
            {M: Type -> Type} {PM : Type -> Type}
            `{PredMonadOps M PM} {A:Type} (P1 P2: PM A) : PM A :=
  forallP (fun b:bool => if b then P1 else P2).

Class PredMonad
            (M: Type -> Type) (PM : Type -> Type)
            `{PredMonadOps M PM} `{MonadOps M} `{MonadOps PM} : Prop :=
  {
    (* Both M and PM must be monads *)
    predmonad_monad_M :> Monad M;
    predmonad_monad_PM :> Monad PM;

    (* Entailment should be a preorder whose symmetric closure is the
    distinguished equality on PM *)
    predmonad_entailsP_preorder
      (A:Type) `{Order A} :> PreOrder (entailsP (A:=A));
    predmonad_entailsP_equalsM {A:Type} `{Order A} (P1 P2: PM A) :
      P1 == P2 <-> (entailsP P1 P2 /\ entailsP P2 P1);

    (* forallP is a complete meet operator. The laws for it being a lower bound
    and the greatest lower bound actually correspond to forall-elimination and
    forall-introduction rules, respectively. *)
    predmonad_forallP_elim :
      forall {A B:Type} `{Order B} (f: A -> PM B) a,
        entailsP (forallP f) (f a);
    predmonad_forallP_intro :
      forall {A B:Type} `{Order B} (f: A -> PM B) P,
        (forall a, entailsP P (f a)) -> entailsP P (forallP f);

    (* existsP is a complete join operator. The laws for it being an upper bound
    and the least upper bound actually correspond to exists-introduction and
    exists-elimination rules, respectively. *)
    predmonad_existsP_intro :
      forall {A B:Type} `{Order B} (f: A -> PM B) a,
        entailsP (f a) (existsP f);
    predmonad_existsP_elim :
      forall {A B:Type} `{Order B} (f: A -> PM B) P,
        (forall a, entailsP (f a) P) -> entailsP (existsP f) P;

    (* impliesP is a right adjoint to andP, the laws for which correspond to
    implication introduction and generalization of implication elimination
    (where taking P1 = (impliesP P2 P3) yields the standard elimination rule) *)
    predmonad_impliesP_intro :
      forall {A:Type} `{Order A} (P1 P2 P3: PM A),
        entailsP (andP P1 P2) P3 -> entailsP P1 (impliesP P2 P3);
    predmonad_impliesP_elim :
      forall {A:Type} `{Order A} (P1 P2 P3: PM A),
        entailsP P1 (impliesP P2 P3) -> entailsP (andP P1 P2) P3;

    (* Introduction and elimination rules for assertP *)
(*
    predmonad_assertP_intro :
      forall {A:Type} `{Order A} (P:PM A),
        entailsP P (assertP True);
    predmonad_assertP_elim :
      forall {A:Type} `{Order A} (P:PM A) (Pr:Prop),
        (Pr -> entailsP (assertP True) P) ->
        entailsP (assertP Pr) P;
*)

    (* laws about liftP *)
    predmonad_liftP_return :
      forall {A:Type} `{Order A} (x:A),
        liftP (returnM x) == returnM x;
    predmonad_liftP_bind :
      forall {A B:Type} `{Order A} `{Order B} m (f:A -> M B),
        liftP (bindM m f) == bindM (liftP m) (fun x => liftP (f x));

    (* FIXME: need laws about how the combinators interact *)

    (* Laws about the operators being proper *)
    predmonad_forallP_proper {A B:Type} `{Order B} :
      Proper ((@eq A ==> entailsP) ==> entailsP) forallP;
    predmonad_existsP_proper {A B:Type} `{Order B} :
      Proper ((@eq A ==> entailsP) ==> entailsP) existsP;
    predmonad_impliesP_proper {A:Type} `{Order A} :
      Proper (Basics.flip entailsP ==> entailsP ==> entailsP) impliesP;
    predmonad_liftP_proper {A:Type} `{Equals A} :
      Proper (equalsM ==> equalsM) liftP;
  }.


(***
 *** Defined Predicate Monad Operators
 ***)

(* We define m |= P as holding iff (liftP m) entails P *)
Definition satisfiesP `{PredMonad} `{Order} (m:M A) (P:PM A) :=
  entailsP (liftP m) P.

(* Notation for satisfaction *)
Infix "|=" := satisfiesP (at level 80).

(* Disjunction is definable in terms of the existential *)
Definition orP `{PredMonadOps} {A} (P1 P2: PM A) : PM A :=
  existsP (fun b:bool => if b then P1 else P2).

(* True and false, which correspond to top and bottom, respectively *)
Definition trueP `{PredMonadOps} {A} : PM A :=
  existsP (fun pm:PM A => pm).
Definition falseP `{PredMonadOps} {A} : PM A :=
  forallP (fun pm:PM A => pm).

(* Negation, which (as in normal Coq) is implication of false *)
Definition notP `{PredMonadOps} {A} (P: PM A) : PM A :=
  impliesP P falseP.

(* An assertion inside a predicate monad *)
Definition assertP `{PredMonadOps} (P:Prop) : PM unit :=
  existsP (fun pf:P => trueP).


(***
 *** Theorems about Predicate Monads
 ***)

Section PredMonad_thms.

Context `{PredMonad}.

(** entailsP is proper w.r.t. equalsM **)
Global Instance predmonad_entailsP_proper_iff `{Order} :
  Proper (equals ==> equals ==> iff) (entailsP (A:=A)).
intros P1 P1' e1 P2 P2' e2.
destruct (predmonad_entailsP_equalsM P1 P1'). destruct (H4 e1).
destruct (predmonad_entailsP_equalsM P2 P2'). destruct (H8 e2).
split.
transitivity P1; [ assumption | transitivity P2; assumption ].
transitivity P1'; [ assumption | transitivity P2'; assumption ].
Qed.

(** True is the top element **)
Lemma predmonad_trueP_intro `{Order} (P: PM A) :
  entailsP P trueP.
apply (predmonad_existsP_intro (fun pm => pm) P).
Qed.

(** False is the bottom element **)
Lemma predmonad_falseP_elim `{Order} (P: PM A) :
  entailsP falseP P.
apply (predmonad_forallP_elim (fun pm => pm) P).
Qed.

(** Conjunction satisfies the usual rules **)
Lemma predmonad_andP_intro `{Order} (P1 P2 P: PM A) :
  entailsP P P1 -> entailsP P P2 -> entailsP P (andP P1 P2).
intros.
apply predmonad_forallP_intro; intro x; destruct x; assumption.
Qed.

Lemma predmonad_andP_elim1 `{Order} (P1 P2: PM A) :
  entailsP (andP P1 P2) P1.
apply (predmonad_forallP_elim (fun b : bool => if b then P1 else P2) true).
Qed.

Lemma predmonad_andP_elim2 `{Order} (P1 P2: PM A) :
  entailsP (andP P1 P2) P2.
apply (predmonad_forallP_elim (fun b : bool => if b then P1 else P2) false).
Qed.

(** Disjunction satisfies the usual rules **)
Lemma predmonad_orP_intro1 `{Order} (P1 P2: PM A) :
  entailsP P1 (orP P1 P2).
apply (predmonad_existsP_intro (fun b : bool => if b then P1 else P2) true).
Qed.

Lemma predmonad_orP_intro2 `{Order} (P1 P2: PM A) :
  entailsP P2 (orP P1 P2).
apply (predmonad_existsP_intro (fun b : bool => if b then P1 else P2) false).
Qed.

Lemma predmonad_orP_elim `{Order} (P1 P2 P: PM A) :
  entailsP P1 P -> entailsP P2 P -> entailsP (orP P1 P2) P.
intros.
apply predmonad_existsP_elim; intro x; destruct x; assumption.
Qed.


(** Nested foralls combine **)
Lemma predmonad_forallP_forallP {A B C} `{Order C}
            (Q : A -> B -> PM C) :
  forallP (fun x => forallP (fun y => Q x y)) ==
  forallP (fun xy => Q (fst xy) (snd xy)).
apply predmonad_entailsP_equalsM; split.
apply predmonad_forallP_intro; intro p; destruct p.
unfold fst, snd.
transitivity (forallP (fun y => Q a y)).
apply (predmonad_forallP_elim (fun x => _) a).
apply (predmonad_forallP_elim (fun y => _) b).
apply predmonad_forallP_intro; intro x.
apply predmonad_forallP_intro; intro y.
apply (predmonad_forallP_elim (fun xy => _) (x,y)).
Qed.

(** Nested exists combine **)
Lemma predmonad_existsP_existsP {A B C} `{Order C}
            (Q : A -> B -> PM C) :
  existsP (fun x => existsP (fun y => Q x y)) ==
  existsP (fun xy => Q (fst xy) (snd xy)).
apply predmonad_entailsP_equalsM; split.
apply predmonad_existsP_elim; intro x.
apply predmonad_existsP_elim; intro y.
apply (predmonad_existsP_intro (fun xy => Q (fst xy) (snd xy)) (x,y)).
apply predmonad_existsP_elim; intro p; destruct p.
unfold fst, snd.
transitivity (existsP (fun y => Q a y)).
apply (predmonad_existsP_intro (fun y => Q a y) b).
apply (predmonad_existsP_intro (fun x : A => existsP (fun y : B => Q x y)) a).
Qed.


(** Commutativity and Associativity of andP and orP **)
Lemma predmonad_andP_commutative `{Order}
            (P1 P2: PM A) : andP P1 P2 == andP P2 P1.
apply predmonad_entailsP_equalsM; split;
repeat (first [ apply predmonad_andP_intro | apply predmonad_andP_elim1
                | apply predmonad_andP_elim2 ]).
Qed.

Lemma predmonad_andP_associative `{Order}
            (P1 P2 P3: PM A) : andP P1 (andP P2 P3) == andP (andP P1 P2) P3.
apply predmonad_entailsP_equalsM; split;
repeat (apply predmonad_andP_intro);
first [ apply predmonad_andP_elim1 | apply predmonad_andP_elim2
      | transitivity (andP P2 P3);
        first [ apply predmonad_andP_elim1 | apply predmonad_andP_elim2 ]
      | transitivity (andP P1 P2);
        first [ apply predmonad_andP_elim1 | apply predmonad_andP_elim2 ]].
Qed.

Lemma predmonad_orP_commutative `{Order}
            (P1 P2: PM A) : orP P1 P2 == orP P2 P1.
apply predmonad_entailsP_equalsM; split;
repeat (first [ apply predmonad_orP_elim | apply predmonad_orP_intro1
                | apply predmonad_orP_intro2 ]).
Qed.

Lemma predmonad_orP_associative `{Order}
            (P1 P2 P3: PM A) : orP P1 (orP P2 P3) == orP (orP P1 P2) P3.
apply predmonad_entailsP_equalsM; split;
repeat (apply predmonad_orP_elim);
first [ apply predmonad_orP_intro1 | apply predmonad_orP_intro2
      | transitivity (orP P2 P3);
        first [ apply predmonad_orP_intro1 | apply predmonad_orP_intro2 ]
      | transitivity (orP P1 P2);
        first [ apply predmonad_orP_intro1 | apply predmonad_orP_intro2 ]].
Qed.


(** Theorems that the combinators mostly mean what we expect for satisfiesP **)
Theorem forallP_forall {A B} `{Order B} m (Q: A -> PM B) :
  m |= forallP Q <-> forall x, m |= Q x.
unfold satisfiesP; split; intros.
transitivity (forallP Q); [ assumption | ].
apply predmonad_forallP_elim.
apply predmonad_forallP_intro; assumption.
Qed.

Theorem andP_and `{Order} m (P1 P2: PM A) :
  m |= andP P1 P2 <-> m |= P1 /\ m |= P2.
unfold andP.
transitivity (forall b:bool, m |= if b then P1 else P2).
apply forallP_forall.
repeat split.
apply (H4 true).
apply (H4 false).
intros; destruct H4; destruct b; assumption.
Qed.

(* NOTE: the converse does not hold; e.g., a stateful computation that satisfies
existsP Q might satisfy Q x for different x depending on the input state *)
Theorem existsP_exists {A B} `{Order B} m (Q: A -> PM B) x :
  m |= Q x -> m |= existsP Q.
  unfold satisfiesP.
  intro.
  transitivity (Q x); [ assumption | apply predmonad_existsP_intro ].
Qed.

(* NOTE: the converse does not hold; e.g., a stateful computation that satisfies
orP P1 P2 might satisfy P1 for some inputs and P2 for others *)
Theorem orP_or `{Order} m (P1 P2: PM A) :
  m |= P1 \/ m |= P2 -> m |= orP P1 P2.
  unfold satisfiesP.
  intros; destruct H4.
  transitivity P1; [ assumption |  apply predmonad_orP_intro1 ].
  transitivity P2; [ assumption |  apply predmonad_orP_intro2 ].
Qed.

(** Distributivity lemmas **)

(* andP distributes over existsP *)
Lemma predmonad_andP_existsP {A B} `{Order B}
            (P: PM B) (Q: A -> PM B) :
  andP P (existsP Q) == existsP (fun x => andP P (Q x)).
apply predmonad_entailsP_equalsM; split.
rewrite predmonad_andP_commutative.
apply predmonad_impliesP_elim.
apply predmonad_existsP_elim; intro a.
apply predmonad_impliesP_intro.
rewrite predmonad_andP_commutative.
apply (predmonad_existsP_intro (fun x => andP P (Q x)) a).
apply predmonad_existsP_elim; intro a.
apply predmonad_andP_intro.
apply predmonad_andP_elim1.
transitivity (Q a).
apply predmonad_andP_elim2.
apply (predmonad_existsP_intro).
Qed.

(* Implication commutes with forall *)
Theorem predmonad_forallP_impliesP {A B} `{Order B}
      P (Q: A -> PM B) :
  impliesP P (forallP Q) == forallP (fun x => impliesP P (Q x)).
  rewrite predmonad_entailsP_equalsM; split.
  apply predmonad_forallP_intro; intro.
  apply predmonad_impliesP_intro.
  transitivity (forallP Q).
  apply predmonad_impliesP_elim; reflexivity.
  apply predmonad_forallP_elim.

  apply predmonad_impliesP_intro.
  apply predmonad_forallP_intro; intro.
  apply predmonad_impliesP_elim.
  apply (predmonad_forallP_elim (fun x : A => impliesP P (Q x)) a).
Qed.

(* impliesP reverse-distributes over orP (the implication only goes one way) *)
Theorem predmonad_existsP_impliesP
            `{Order} P (Q1 Q2: PM A) :
  entailsP (orP (impliesP P Q1) (impliesP P Q2)) (impliesP P (orP Q1 Q2)).
apply predmonad_orP_elim.
apply predmonad_impliesP_proper.
reflexivity.
apply predmonad_orP_intro1.
apply predmonad_impliesP_proper.
reflexivity.
apply predmonad_orP_intro2.
Qed.

(*
Lemma predmonad_commute_existsP_impliesP {A B} P (Q: A -> PM B) :
  impliesP P (existsP Q) == existsP (fun x => impliesP P (Q x)).
  intros; apply predmonad_equivalence; intros.
  repeat (first [ rewrite predmonad_impliesP_implies
                | rewrite predmonad_existsP_exists ]).
  split; intros.
  destruct (H0 H1).
*)

(* FIXME HERE: can we prove that bind commutes with forall? *)

End PredMonad_thms.


(***
 *** The Set monad as a predicate monad for the Identity monad
 ***)

Section IdentityPredMonad.

Definition SetM (X:Type) : Type := X -> Prop.

Instance SetM_MonadOps : MonadOps SetM :=
  { returnM := fun A x z => x = z;
    bindM := fun A B m f z => exists z', m z' /\ f z' z;
    equalsM := fun A e m1 m2 =>
                 forall z1,
                   (m1 z1 -> exists z2, e z1 z2 /\ m2 z2) /\
                   (m2 z1 -> exists z2, e z1 z2 /\ m1 z2) }.

Instance SetM_Monad : Monad SetM.
constructor; unfold returnM, bindM, equalsM, SetM_MonadOps; intros.
split; intros.
destruct H1; destruct H1.
exists z1; split.
apply Equivalence_Reflexive.
rewrite H1; assumption.
exists z1; split.
apply Equivalence_Reflexive.
exists x; split; [ reflexivity | assumption ].
split; intros.
destruct H0; destruct H0.
exists x; split.
rewrite H1; apply Equivalence_Reflexive.
assumption.
exists z1; split.
apply Equivalence_Reflexive.
exists z1; split; [ assumption | reflexivity ].
split; intros.
repeat (destruct H2).
exists z1; split.
apply Equivalence_Reflexive.
exists x0; split; [ assumption | ].
exists x; split; assumption.
repeat (destruct H2); repeat (destruct H3).
exists z1; split; [ apply Equivalence_Reflexive | ].
exists x0; split; [ | assumption ].
exists x; split; assumption.
repeat constructor; intros.
exists z1; split; [ apply Equivalence_Reflexive | assumption ].
exists z1; split; [ apply Equivalence_Reflexive | assumption ].
destruct (H0 z1). destruct (H3 H1); destruct H4.
exists x0; split; assumption.
destruct (H0 z1). destruct (H2 H1); destruct H4.
exists x0; split; assumption.
destruct (H0 z1). destruct (H3 H2). destruct H5.
destruct (H1 x0). destruct (H7 H6). destruct H9.
exists x1; split.
apply (Equivalence_Transitive _ x0); assumption.
assumption.
destruct (H1 z1). destruct (H4 H2). destruct H5.
destruct (H0 x0). destruct (H8 H6). destruct H9.
exists x1; split.
apply (Equivalence_Transitive _ x0); assumption.
assumption.
intros x y e_xy z1; split; intros.
exists y. rewrite <- H0. split; [ assumption | reflexivity ].
exists x. rewrite <- H0.
split; [ apply Equivalence_Symmetric; assumption | reflexivity ].
intros m1 m2 e_m f1 f2 e_f z1.
split; intros; repeat (destruct H1).
destruct (e_m x). destruct (H3 H1). destruct H5.
destruct (e_f x x0 H5 z1). destruct (H7 H2). destruct H9.
exists x1; split; [ assumption | exists x0; split; assumption ].
destruct (e_m x). destruct (H4 H1). destruct H5.
assert (x0 == x); [ apply Equivalence_Symmetric; assumption | ].
destruct (e_f x0 x H7 z1). destruct (H9 H2). destruct H10.
exists x1; split; [ assumption | exists x0; split; assumption ].
Qed.


Instance SetM_PredMonadOps : PredMonadOps Identity SetM :=
  {
    forallP := fun {A B} Q x => forall y, Q y x;
    existsP := fun {A B} Q x => exists y, Q y x;
    impliesP := fun {A} P1 P2 x => P1 x -> P2 x;
    liftP := fun {A} z x => z = x;
    entailsP := fun {A} ord P1 P2 =>
                  forall x y, ord x y -> P1 x -> P2 y
  }.


Instance SetM_PredMonad : PredMonad Identity SetM.
Proof.
  constructor; eauto with typeclass_instances.
  - admit.
  - intros. admit. (* How is this provable? *)
  - 
(*
  unfold returnMeqM, SetM_eqM, IdMonad_eqM.
         bindM, SetM_bindM, IdMonad_bindM,
         satisfiesP, SetM_satisfiesP, forallP, SetM_forallP,
         existsP, SetM_existsP, impliesP, SetM_impliesP;
  intros; try auto with typeclass_instances; try reflexivity.
  split; intros; symmetry; assumption.
  split; intros.
  destruct H as [ x H ]; destruct H.
  exists (fun y => x = y); exists (exist _ x eq_refl); exists (fun _ => m).
  split; [ assumption
         | split; [ intros y e; rewrite <- e; assumption | reflexivity ] ].
  destruct H as [ phi H ]; destruct H as [ m' H ]; destruct H as [ f H ];
  destruct H as [ H H0 ]; destruct H0.
  destruct m'. exists x. split; [ assumption | ].
  rewrite H1. apply H0. assumption.
  split; intros.
  rewrite H; reflexivity.
  split; apply H; intros; assumption.
  intros x1 x2 ex m1 m2 em; rewrite ex; rewrite em; reflexivity.
*)
Abort.


End IdentityPredMonad.
