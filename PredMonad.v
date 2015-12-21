
Require Import Coq.Program.Basics.

Load Monad.


(***
 *** The Predicate Monad Operations
 ***)

Section PredMonad_ops.

Context (M: Type -> Type) (PM : Type -> Type).

(* The satisfaction relation between computations and monadic predicates *)
Class PredMonadSatisfaction : Type :=
  satisfiesP : forall {A}, M A -> PM A -> Prop.

(* Notation for satisfaction *)
Infix "|=" := satisfiesP (at level 80).

(* The quantifiers, which correspond to lattice meet and join, respectively *)
Class PredMonadForall : Type :=
  forallP : forall {A B}, (A -> PM B) -> PM B.
Class PredMonadExists : Type :=
  existsP : forall {A B}, (A -> PM B) -> PM B.

(* Implication, which will form a Heyting Algebra, below *)
Class PredMonadImplication : Type :=
  impliesP : forall {A}, PM A -> PM A -> PM A.

End PredMonad_ops.

Arguments satisfiesP {_ _ _ _} m P.
Arguments impliesP {_ _ _} P1 P2.
Arguments forallP {_ _ _ _} Q.
Arguments existsP {_ _ _ _} Q.

(* Re-declaring notation outside the section *)
Infix "|=" := satisfiesP (at level 80).


(***
 *** Defined Operations in a Predicate Monad
 ***)

Section PredMonad_helpers.

Context
  {M:Type -> Type} {PM:Type -> Type}
  {PredMonadRet:MonadRet PM} {PredMonadBind:MonadBind PM}
  {PredMonadEquiv:MonadEquiv PM}
  {MonadRet:MonadRet M} {MonadBind:MonadBind M} {MonadEquiv:MonadEquiv M}
  {PredMonadSatisfaction:PredMonadSatisfaction M PM}
  {PredMonadForall:PredMonadForall PM}
  {PredMonadExists:PredMonadExists PM} {PredMonadImplication:PredMonadImplication PM}.

(* Defined logical operators, which correspond to binary meet and join *)
Definition andP {A} (P1 P2: PM A) : PM A :=
  forallP (fun (b:bool) => if b then P1 else P2).
Definition orP {A} (P1 P2: PM A) : PM A :=
  existsP (fun (b:bool) => if b then P1 else P2).

(* True and false, which correspond to top and bottom, respectively *)
Definition trueP {A} : PM A := existsP id.
Definition falseP {A} : PM A := forallP id.

(* Negation, which (as in normal Coq) is implication of false *)
Definition notP {A} (P: PM A) : PM A := impliesP P falseP.

(* Lifting a proposition = the join over all proofs of it *)
Definition liftProp {A} (P: Prop) : PM A :=
  existsP (fun (pf:P) => trueP).

(* Predicate monad refinement: refinesP P1 P2 means P1 is stronger than P2 *)
Definition refinesP {A} : relation (PM A) :=
  fun P1 P2 => forall m P, m |= impliesP P P1 -> m |= impliesP P P2.

End PredMonad_helpers.


(***
 *** Predicate Monad Axioms (as a Typeclass)
 ***)

Class PredMonad (M:Type -> Type) (PM:Type -> Type)
  {PredMonadRet:MonadRet PM} {PredMonadBind:MonadBind PM}
  {PredMonadEquiv:MonadEquiv PM}
  {MonadRet:MonadRet M} {MonadBind:MonadBind M} {MonadEquiv:MonadEquiv M}
  {PredMonadSatisfaction:PredMonadSatisfaction M PM}
  {PredMonadForall:PredMonadForall PM}
  {PredMonadExists:PredMonadExists PM}
  {PredMonadImplication:PredMonadImplication PM} : Prop :=
  {
    (* Both M and PM must be monads *)
    predmonad_monad_M :> Monad M;
    predmonad_monad_PM :> Monad PM;

    (* Forall, exists, and implies behave as expected *)
    predmonad_forallP_forall :
      forall {A B} m (P: A -> PM B),
        m |= forallP P <-> forall x, m |= P x;
    predmonad_existsP_exists :
      forall {A B} m (P: A -> PM B),
        m |= existsP P <-> exists x, m |= P x;
    predmonad_impliesP_implies :
      forall {A} m (P1 P2: PM A),
        m |= impliesP P1 P2 <-> (m |= P1 -> m |= P2);

    (* Return in the predicate monad precisely characterizes return in M *)
    predmonad_return_return :
      forall {A} (x:A) m, m |= returnM x <-> m == returnM x;

    (* Bind in the predicate monad characterizes bind in M, where the function
    argument f of the bind in M only needs to satisfy Q for arguments that could
    be returned by the first argument m' of bind *)
    predmonad_bind_bind :
      forall {A B} (m:M B) (P: PM A) (Q: A -> PM B),
        m |= bindM P Q <->
        (exists (phi:A -> Prop) (m': M {x:A | phi x}) (f : A -> M B),
           (bindM m' (fun x => returnM (proj1_sig x))) |= P /\
           (forall x, phi x -> f x |= Q x) /\
           eqM m (bindM m' (fun x => f (proj1_sig x))));

    (* Equality is equivalent to equi-satisfaction under all preconditions *)
    predmonad_equivalence :
      forall {A} (P1 P2: PM A),
        P1 == P2 <-> forall m P, m |= impliesP P P1 <-> m |= impliesP P P2;

    (* Proper-ness of all operations *)
    predmonad_proper_satisfiesP :>
      forall {A}, Proper (eqM (A:=A) ==> eqM ==> iff) satisfiesP

    (* FIXME: need to commute return and bind with logical operators! *)
  }.


(***
 *** Helper stuff for rewriting and proving equivalences
 ***)

Section PredMonad_instances.

Context `{PredMonad}.

Instance refinesP_PreOrder A : PreOrder (refinesP (A:=A)).
  split.
  intros P m Pleft H0; assumption.
  intros P1 P2 P3 r12 r23 m Pleft H0.
  apply r23; apply r12; assumption.
Qed.

Instance predmonad_proper_forallP A B :
  Proper ((eq ==> eqM) ==> eqM) (forallP (A:=A) (B:=B)).
  intros f1 f2 e; apply predmonad_equivalence; intros.
  repeat (rewrite predmonad_impliesP_implies).
  repeat (rewrite predmonad_forallP_forall).
  split; intros.
  rewrite <- (e x x eq_refl); apply H0; assumption.
  rewrite (e x x eq_refl); apply H0; assumption.
Qed.

Instance predmonad_proper_existsP A B :
  Proper ((eq ==> eqM) ==> eqM) (existsP (A:=A) (B:=B)).
  intros f1 f2 e; apply predmonad_equivalence; intros.
  repeat (rewrite predmonad_impliesP_implies).
  repeat (rewrite predmonad_existsP_exists).
  split; intros; destruct (H0 H1); exists x.
  rewrite <- (e x x eq_refl); assumption.
  rewrite (e x x eq_refl); assumption.
Qed.

Instance predmonad_proper_impliesP A :
  Proper (eqM (A:=A) ==> eqM ==> eqM) impliesP.
  intros P1 P2 eP Q1 Q2 eQ; apply predmonad_equivalence; intros.
  repeat (rewrite predmonad_impliesP_implies).
  split; intros; [ rewrite <- eQ | rewrite eQ ];
    apply H0; try assumption;
    [ rewrite eP | rewrite <- eP ]; assumption.
Qed.

End PredMonad_instances.


(***
 *** Theorems about Predicate Monads
 ***)

Section PredMonad_thms.

Context `{PredMonad}.

Theorem andP_and {A} m (P1 P2: PM A) :
  m |= andP P1 P2 <-> m |= P1 /\ m |= P2.
  unfold andP.
  rewrite predmonad_forallP_forall.
  split; intro H0.
  split; [ apply (H0 true) | apply (H0 false) ].
  destruct H0; intro x; destruct x; assumption.
Qed.

Theorem orP_or {A} m (P1 P2: PM A) :
  m |= orP P1 P2 <-> m |= P1 \/ m |= P2.
  unfold orP.
  rewrite predmonad_existsP_exists.
  split; intro H0.
  destruct H0 as [ b H0 ]; destruct b.
  left; assumption.
  right; assumption.
  destruct H0.
  exists true; assumption.
  exists false; assumption.
Qed.


(* Implication commutes with forall *)
Lemma predmonad_commute_forallP_impliesP {A B} P (Q: A -> PM B) :
  impliesP P (forallP Q) == forallP (fun x => impliesP P (Q x)).
  intros; apply predmonad_equivalence; intros.
  repeat (first [ rewrite predmonad_impliesP_implies
                | rewrite predmonad_forallP_forall ]).
  split; intros.
  rewrite predmonad_impliesP_implies; intros.
  apply H0; assumption.
  revert H2; rewrite <- predmonad_impliesP_implies.
  apply H0; assumption.
Qed.

(* NOTE: this only works from left to right! *)
Lemma predmonad_commute_existsP_impliesP {A B} P (Q: A -> PM B) :
  refinesP (existsP (fun x => impliesP P (Q x))) (impliesP P (existsP Q)).
  intros m Pleft.
  repeat (first [ rewrite predmonad_impliesP_implies
                | rewrite predmonad_existsP_exists ]).
  intros.
  destruct H0; [ assumption | ].
  rewrite predmonad_impliesP_implies in H0.
  exists x; apply H0; assumption.
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

Instance SetM_returnM : MonadRet SetM := fun {A} x => eq x.

Instance SetM_bindM : MonadBind SetM :=
  fun {A B} m f x => exists y, m y /\ f y x.

Instance SetM_eqM : MonadEquiv SetM :=
  fun {A} m1 m2 => forall x, m1 x <-> m2 x.

Instance SetM_Monad : Monad SetM.
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
