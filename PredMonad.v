
Require Import Coq.Program.Basics.

Load Monad.


(***
 *** The Predicate Monad Operations
 ***)

Section PredMonad.

Context {M: Type -> Type} {PM : Type -> Type}.

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


(***
 *** Defined Operations in a Predicate Monad
 ***)

Context
  {PredMonadRet:MonadRet PM} {PredMonadBind:MonadBind PM}
  {PredMonadEquiv:MonadEquiv PM}
  {MonadRet:MonadRet M} {MonadBind:MonadBind M} {MonadEquiv:MonadEquiv M}
  {PredMonadSatisfaction:PredMonadSatisfaction}
  {PredMonadForall:PredMonadForall}
  {PredMonadExists:PredMonadExists} {PredMonadImplication:PredMonadImplication}.

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


(***
 *** Predicate Monad Axioms (as a Typeclass)
 ***)

Class PredMonad : Prop :=
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
        m |= impliesP P1 P2 <-> m |= P1 -> m |= P2;

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

    (* Equality is equivalent to equi-satisfaction *)
    predmonad_equivalent_equal :
      forall {A} (P1 P2: PM A),
        P1 == P2 <-> forall m, m |= P1 <-> m |= P2;

    (* Proper-ness of all operations *)
    predmonad_satisfiesP_proper :>
      forall {A}, Proper (eqM (A:=A) ==> eqM ==> iff) satisfiesP;
    predmonad_forallP_proper :>
      forall {A B}, Proper ((@eq A ==> eqM (A:=B)) ==> eqM (A:=B)) forallP;
    predmonad_existsP_proper :>
      forall {A B}, Proper ((@eq A ==> eqM (A:=B)) ==> eqM (A:=B)) existsP;
    predmonad_impliesP_proper :>
      forall {A}, Proper (eqM (A:=A) ==> eqM ==> eqM) impliesP

    (* FIXME: need to commute return and bind with logical operators! *)
  }.

End PredMonad.

(* Re-declaring notation outside the section *)
Infix "|=" := satisfiesP (at level 80).


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
  intros x y eqm z; rewrite eqm; reflexivity.
  intros m1 m2 eqm f1 f2 eqf x.
  split; intro H; destruct H as [ y H ]; destruct H; exists y; split.
  apply eqm; assumption.
  apply (eqf y y eq_refl); assumption.
  apply eqm; assumption.
  apply (eqf y y eq_refl); assumption.
Qed.

Instance SetM_PredMonadSatisfaction :
  PredMonadSatisfaction (M:=Identity) (PM:=SetM) :=
  fun {A} m P => P m.

Instance SetM_PredMonadForall : PredMonadForall (PM:=SetM) :=
  fun {A B} f x => forall y, f y x.
Instance SetM_PredMonadExists : PredMonadExists (PM:=SetM) :=
  fun {A B} f x => exists y, f y x.
Instance SetM_PredMonadImplication : PredMonadImplication (PM:=SetM) :=
  fun {A} P1 P2 x => P1 x -> P2 x.

End IdentityPredMonad.
