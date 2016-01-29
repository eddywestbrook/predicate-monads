
Add LoadPath "." as PredMonad.
Require Export PredMonad.Monad.


(***
 *** The Predicate Monad Class
 ***)

(* FIXME: the universe constraints on M and PM could be different...? *)
Polymorphic Class PredMonadOps@{d c}
            (M: Type@{d} -> Type@{c}) (PM : Type@{d} -> Type@{c}) :=
  { forallP: forall {A B: Type@{d}}, (A -> PM B) -> PM B;
    (* existsP: forall {A B: Type@{d}}, (A -> PM B) -> PM B; *)
    orP: forall {A: Type@{d}}, PM A -> PM A -> PM A;
    impliesP: forall {A: Type@{d}}, PM A -> PM A -> PM A;
    assertP: forall {A: Type@{d}}, Prop -> PM A;
    liftP: forall {A: Type@{d}}, M A -> PM A;
    entailsP: forall {A: Type@{d}} `{OrderOp A}, relation (PM A)
  }.

Polymorphic Definition andP@{d c}
            {M: Type@{d} -> Type@{c}} {PM : Type@{d} -> Type@{c}}
            `{PredMonadOps M PM} {A:Type@{d}} (P1 P2: PM A) : PM A :=
  forallP (fun b:bool => if b then P1 else P2).

Polymorphic Class PredMonad@{d c}
            (M: Type@{d} -> Type@{c}) (PM : Type@{d} -> Type@{c})
            `{PredMonadOps M PM} `{MonadOps M} `{MonadOps PM} : Prop :=
  {
    (* Both M and PM must be monads *)
    predmonad_monad_M :> Monad M;
    predmonad_monad_PM :> Monad PM;

    (* Entailment should be a preorder whose symmetric closure is the
    distinguished equality on PM *)
    predmonad_entailsP_preorder
      (A:Type@{d}) `{Order A} :> PreOrder (entailsP (A:=A));
    predmonad_entailsP_equalsM (A:Type@{d}) `{Order A} (P1 P2: PM A) :
      P1 == P2 <-> (entailsP P1 P2 /\ entailsP P2 P1);

    (* forallP is a complete meet operator. The laws for it being a lower bound
    and the greatest lower bound actually correspond to forall-elimination and
    forall-introduction rules, respectively. *)
    predmonad_forallP_elim :
      forall {A B:Type@{d}} `{Order B} (f: A -> PM B) a,
        entailsP (forallP f) (f a);
    predmonad_forallP_intro :
      forall {A B:Type@{d}} `{Order B} (f: A -> PM B) P,
        (forall a, entailsP P (f a)) -> entailsP P (forallP f);

    (* orP is a binary join operator, the laws for which actually corresond to
    the standard or-introduction and or-elimination rules. *)
    predmonad_orP_intro1 :
      forall {A:Type@{d}} `{Order A} (P1 P2: PM A),
        entailsP P1 (orP P1 P2);
    predmonad_orP_intro2 :
      forall {A:Type@{d}} `{Order A} (P1 P2: PM A),
        entailsP P2 (orP P1 P2);
    predmonad_orP_elim :
      forall {A:Type@{d}} `{Order A} (P1 P2 P: PM A),
        entailsP P1 P -> entailsP P2 P ->
        entailsP (orP P1 P2) P;

    (* impliesP is a right adjoint to andP, the laws for which correspond to
    implication introduction and generalization of implication elimination
    (where taking P1 = (impliesP P2 P3) yields the standard elimination rule) *)
    predmonad_impliesP_intro :
      forall {A:Type@{d}} `{Order A} (P1 P2 P3: PM A),
        entailsP (andP P1 P2) P3 -> entailsP P1 (impliesP P2 P3);
    predmonad_impliesP_elim :
      forall {A:Type@{d}} `{Order A} (P1 P2 P3: PM A),
        entailsP P1 (impliesP P2 P3) -> entailsP (andP P1 P2) P3;

    (* Introduction and elimination rules for assertP *)
    predmonad_assertP_intro :
      forall {A:Type@{d}} `{Order A} (P:PM A),
        entailsP P (assertP True);
    predmonad_assertP_elim :
      forall {A:Type@{d}} `{Order A} (P:PM A) (Pr:Prop),
        (Pr -> entailsP (assertP True) P) ->
        entailsP (assertP Pr) P;

    (* laws about liftP *)
    predmonad_liftP_return :
      forall {A:Type@{d}} `{Order A} (x:A),
        liftP (returnM x) == returnM x;
    predmonad_liftP_bind :
      forall {A B:Type@{d}} `{Order A} `{Order B} m (f:A -> M B),
        liftP (bindM m f) == bindM (liftP m) (fun x => liftP (f x));

    (* FIXME: need laws about how the combinators interact *)

    (* FIXME: need laws about proper-ness *)
  }.


(* We define m |= P as holding iff (liftP m) entails P *)
Polymorphic Definition satisfiesP `{PredMonad} `{Order} (m:M A) (P:PM A) :=
  entailsP (liftP m) P.

(* Notation for satisfaction *)
Infix "|=" := satisfiesP (at level 80).

(* True and false, which correspond to top and bottom, respectively *)
Polymorphic Definition trueP `{PredMonadOps} {A} : PM A := assertP True.
Polymorphic Definition falseP `{PredMonadOps} {A} : PM A := assertP False.

(* Negation, which (as in normal Coq) is implication of false *)
Polymorphic Definition notP `{PredMonadOps} {A} (P: PM A) : PM A :=
  impliesP P falseP.


(***
 *** Theorems about Predicate Monads
 ***)

Section PredMonad_thms.

Context `{PredMonad}.

Polymorphic Theorem forallP_forall {A B} `{Order B} m (Q: A -> PM B) :
  m |= forallP Q <-> forall x, m |= Q x.
unfold satisfiesP; split; intros.
transitivity (forallP Q); [ assumption | ].
apply predmonad_forallP_elim.
apply predmonad_forallP_intro; assumption.
Qed.

Polymorphic Theorem andP_and `{Order} m (P1 P2: PM A) :
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
orP P1 P2 might satisfy P1 for some inputs and P2 for others *)
Polymorphic Theorem orP_or `{Order} m (P1 P2: PM A) :
  m |= P1 \/ m |= P2 -> m |= orP P1 P2.
  unfold satisfiesP.
  intros; destruct H4.
  transitivity P1; [ assumption |  apply predmonad_orP_intro1 ].
  transitivity P2; [ assumption |  apply predmonad_orP_intro2 ].
Qed.


(* Implication commutes with forall *)
Polymorphic Theorem predmonad_commute_forallP_impliesP {A B} `{Order B}
      P (Q: A -> PM B) :
  impliesP P (forallP Q) == forallP (fun x => impliesP P (Q x)).
  rewrite predmonad_entailsP_equalsM; [ | assumption]; split.
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

(* Lift entailment from rhs's of implications to whole implications *)
Polymorphic Theorem predmonad_impliesP_rhs
            `{Order} (P Q1 Q2: PM A) :
  entailsP Q1 Q2 -> entailsP (impliesP P Q1) (impliesP P Q2).
intro.
apply predmonad_impliesP_intro.
transitivity Q1.
apply (predmonad_impliesP_elim).
reflexivity.
assumption.
Qed.

(* NOTE: this only works from left to right! *)
Polymorphic Theorem predmonad_commute_existsP_impliesP
            `{Order} P (Q1 Q2: PM A) :
  entailsP (orP (impliesP P Q1) (impliesP P Q2)) (impliesP P (orP Q1 Q2)).
apply predmonad_orP_elim.
apply predmonad_impliesP_rhs.
apply predmonad_orP_intro1.
apply predmonad_impliesP_rhs.
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

Polymorphic Definition SetM (X:Type) : Type := X -> Prop.

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


FIXME HERE


repeat constructor; intros.
unfold bindM.
  constructor; unfold returnM, SetM_returnM, bindM, SetM_bindM; intros.
  intro b; split; intros.
  destruct H as [ y H ]; destruct H; rewrite H; assumption.
  exists x; split; [ reflexivity | assumption ].
  intro x; split; intros.
  destruct H as [ y H ]; destruct H; rewrite <- H0; assumption.
  exists x; split; [ assumption | reflexivity ].
  intro z; split; intros.
  destruct H as [ x H ]; destruct H; destruct H0 as [ y H0 ]; destruct H0.
  exists y; split; [ exists x; split; assumption | assumption ].
  destruct H as [ x H ]; destruct H; destruct H as [ y H1 ]; destruct H1.
  exists y; split; [ assumption | exists x; split; assumption ].
  split; intro; intros; intro.
  reflexivity.
  symmetry; apply H.
  transitivity (y x0); [ apply H | apply H0 ].
  intros m1 m2 eqm f1 f2 eqf x.
  split; intro H; destruct H as [ y H ]; destruct H; exists y; split.
  apply eqm; assumption.
  apply (eqf y y eq_refl); assumption.
  apply eqm; assumption.
  apply (eqf y y eq_refl); assumption.
Qed.


Polymorphic Instance SetM_PredMonadOps : PredMonadOps Identity SetM :=
  {
    forallP := fun {A B} Q x => forall y, Q y x;
    orP := fun {A} P1 P2 x => P1 x \/ P2 x;
    impliesP := fun {A} P1 P2 x => P1 x -> P2 x;
    assertP := fun {A} P x => P;
    liftP := fun {A} z x => z = x;
    entailsP := fun {A} ord P1 P2 =>
                  forall x y, ord x y -> P1 x -> P2 y
  }.


Instance SetM_satisfiesP : PredMonadSatisfaction Identity SetM :=
  fun {A} m P => P m.
Instance SetM_forallP : PredMonadForall SetM :=
  fun {A B} f x => forall y, f y x.
Instance SetM_existsP : PredMonadExists SetM :=
  fun {A B} f x => exists y, f y x.
Instance SetM_impliesP : PredMonadImplication SetM :=
  fun {A} P1 P2 x => P1 x -> P2 x.

Instance SetM_PredMonad : PredMonad Identity SetM.
  constructor;
  unfold returnM, SetM_returnM, IdMonad_returnM, eqM, SetM_eqM, IdMonad_eqM,
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
Qed.


End IdentityPredMonad.
