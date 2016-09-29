Require Import Coq.Setoids.Setoid.
Require Export Coq.Classes.Morphisms.
Require Export PredMonad.SemiPreOrder.


(***
 *** The monad typeclass
 ***)

Polymorphic Class MonadOps (M : Type -> Type) : Type :=
  { returnM : forall {A : Type}, A -> M A;
    bindM : forall {A B : Type}, M A -> (A -> M B) -> M B;
    lrM :> forall {A : Type} `{LR_Op A}, LR_Op (M A) }.

Polymorphic Class Monad (M : Type -> Type) {MonadOps:MonadOps M} : Prop :=
  {
    monad_LR :> forall `{LR}, LR (M A);

    monad_proper_return :>
      forall {A R} `{@LR A R}, Proper (lr_leq ==> lr_leq) returnM;

    monad_proper_bind :>
      forall {A B RA RB} `{@LR A RA} `{@LR B RB},
        Proper (lr_leq ==> lr_leq ==> lr_leq)
               (bindM (A:=A) (B:=B));

    monad_proper_lrM :>
      forall {A},
        Proper (subrelation ==> subrelation) (@lrM _ MonadOps A);

    monad_return_bind :
      forall {A B RA RB} `{@LR A RA} `{@LR B RB} x (f:A -> M B)
             `{Proper _ lr_leq x} `{Proper _ (lr_leq ==> lr_leq) f},
        bindM (returnM x) f ~~ f x;

    monad_bind_return :
      forall {A RA} `{@LR A RA} (m:M A) `{Proper _ lr_leq m},
        bindM m returnM ~~ m;

    monad_assoc :
      forall {A B C RA RB RC}
             `{@LR A RA} `{@LR B RB} `{@LR C RC}
             m (f:A -> M B) (g:B -> M C)
             `{Proper _ lr_leq m} `{Proper _ (lr_leq ==> lr_leq) f}
             `{Proper _ (lr_leq ==> lr_leq) g},
        bindM (bindM m f) g ~~ bindM m (fun x => bindM (f x) g);

  }.


(***
 *** Helper theorems / utilities about monads
 ***)

(* Helpful bind notation *)
Notation "'do' x <- m1 ; m2" :=
  (bindM m1 (fun x => m2)) (at level 60, right associativity).

Instance Monad_lr_leq_SemiPreOrder `{Monad} `{LR} : SemiPreOrder (lr_leq (A:=M A)).
Proof.
  auto with typeclass_instances.
Qed.

Instance Monad_lr_eq_SemiPreOrder `{Monad} `{LR} : SemiPreOrder (lr_eq (A:=M A)).
Proof.
  apply PER_SemiPreOrder.
Qed.


(*

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

*)


(***
 *** The Identity Monad
 ***)

Polymorphic Definition Identity (X:Type) := X.
Polymorphic Instance IdMonad_MonadOps : MonadOps Identity :=
  { returnM := fun A x => x;
    bindM := fun A B m f => f m;
    lrM := fun A R => R }.

Polymorphic Instance IdMonad : Monad Identity.
constructor; intros.
assumption.
intros x y Rxy; assumption.
intros m1 m2 Rm f1 f2 Rf. apply Rf; apply Rm.
intros R1 R2 sub; assumption.
split; apply H2; apply H1.
split; apply H0.
split; apply H4; apply H3; apply H2.
Qed.
