Require Import Coq.Setoids.Setoid.
Require Export PredMonad.LogicalRelations.

(***
 *** The monad typeclass
 ***)

Class MonadOps (M : Type -> Type) : Type :=
  { returnM : forall {A : Type}, A -> M A;
    bindM : forall {A B : Type}, M A -> (A -> M B) -> M B;
    equalsM :> forall {A : Type} {EqOp:EqualsOp A}, EqualsOp (M A) }.

Class Monad (M : Type -> Type)
            {MonadOps:MonadOps M} : Prop :=
  {
    monad_return_bind :
      forall (A B:Type) `{Equals A} `{Equals B} x (f:A -> M B),
        bindM (returnM x) f == f x;
    monad_bind_return :
      forall (A:Type) `{Equals A} (m:M A),
        bindM m returnM == m;
    monad_assoc :
      forall (A B C:Type) `{Equals A} `{Equals B} `{Equals C}
             m (f:A -> M B) (g:B -> M C),
        bindM (bindM m f) g == bindM m (fun x => bindM (f x) g);
    monad_equalsM :>
      forall {A:Type} `{Equals A},
        Equals _ (EqOp:=equalsM);
    monad_proper_return :>
      forall (A:Type) `{Equals A},
        Proper (equals ==> equalsM) returnM;
    monad_proper_bind :>
      forall (A B:Type) `{Equals A} `{Equals B},
        Proper (equals ==> (equals ==> equals) ==> equals)
               (bindM (A:=A) (B:=B))
  }.


(***
 *** Helper theorems about monads
 ***)

(* FIXME: Equivalence and friends are not polymorphic... *)
Instance equalsM_Equivalence `{Monad} `{Equals} : Equivalence (equalsM (A:=A)).
  apply monad_equalsM; assumption.
Qed.

(* FIXME: why is this not automatic in the proof of bind_fun_equalsM?!? *)
Instance equalsM_Reflexive `{Monad} `{Equals} : Reflexive (equalsM (A:=A)).
  auto with typeclass_instances.
Qed.

Instance equalsM_Symmetric `{Monad} `{Equals} : Symmetric (equalsM (A:=A)).
  auto with typeclass_instances.
Qed.

Instance equalsM_Transitive `{Monad} `{Equals} : Transitive (equalsM (A:=A)).
  auto with typeclass_instances.
Qed.

Add Parametric Relation `{Monad} `{Equals} : (M A) equalsM
    reflexivity proved by equalsM_Reflexive
    symmetry proved by equalsM_Symmetric
    transitivity proved by equalsM_Transitive
as equalsM_Equivalence2.

Instance equalsM_equals_iff_Proper `{Monad} `{Equals} :
  Proper (equals ==> equals ==> iff) equalsM.
intros m11 m12 e1 m21 m22 e2; split; intros.
transitivity m11; [ symmetry; assumption | transitivity m21; assumption ].
transitivity m12; [ assumption |
                    transitivity m22; try assumption; symmetry; assumption ].
Qed.

Instance equalsM_equals_impl_Proper `{Monad} `{Equals} :
  Proper (equals ==> equals ==> Basics.flip Basics.impl) equalsM.
intros m11 m12 e1 m21 m22 e2 e12.
transitivity m12; [ assumption |
                    transitivity m22; try assumption; symmetry; assumption ].
Qed.

Lemma bind_fun_equalsM `{Monad} {A B:Type}
      `{Equals A} `{Equals B} m (f1 f2:A -> M B) :
  (forall x, f1 x == f2 x) -> bindM m f1 == bindM m f2.
Proof.
  intros e; apply (monad_proper_bind A B (H:=Eq_Equals A) m m).
  (* FIXME: why does the reflexivity tactic not work? *)
  apply (equalsM_Reflexive (H0:=Eq_Equals A)).
  intros x y exy; rewrite exy; apply e.
Qed.


(***
 *** The Identity Monad
 ***)

Definition Identity (X:Type) := X.
Instance IdMonad_MonadOps : MonadOps Identity :=
  { returnM := fun A x => x;
    bindM := fun A B m f => f m;
    equalsM := fun A e => e }.

Instance IdMonad : Monad Identity.
  constructor; intros; try reflexivity.
  split; auto with typeclass_instances.
  intros x y exy; assumption.
  intros m1 m2 eqm f1 f2 eqf; apply eqf; assumption.
Qed.
