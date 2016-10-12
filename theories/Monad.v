Require Import Coq.Setoids.Setoid.
Require Export Coq.Classes.Morphisms.
Require Export PredMonad.SemiPreOrder.


(***
 *** The monad typeclass
 ***)

Class MonadOps (M : Type -> Type) : Type :=
  { returnM : forall {A : Type}, A -> M A;
    bindM : forall {A B : Type}, M A -> (A -> M B) -> M B;
    lrM :> forall {A : Type} `{LR_Op A}, LR_Op (M A) }.

Class Monad (M : Type -> Type) {MonadOps:MonadOps M} : Prop :=
  {
    monad_LR :> forall `{LR}, LR (M A);

    monad_proper_return :>
      forall {A R} `{@LR A R}, Proper lr_leq returnM;

    monad_proper_bind :>
      forall {A B RA RB} `{@LR A RA} `{@LR B RB},
        Proper lr_leq (bindM (A:=A) (B:=B));

    monad_proper_lrM :>
      forall {A},
        Proper (subrelation ==> subrelation) (@lrM _ MonadOps A);

    monad_return_bind :
      forall {A B RA RB} `{@LR A RA} `{@LR B RB} x (f:A -> M B)
             `{Proper _ lr_leq x} `{Proper _ lr_leq f},
        bindM (returnM x) f ~~ f x;

    monad_bind_return :
      forall {A RA} `{@LR A RA} (m:M A) `{Proper _ lr_leq m},
        bindM m returnM ~~ m;

    monad_assoc :
      forall {A B C RA RB RC}
             `{@LR A RA} `{@LR B RB} `{@LR C RC}
             m (f:A -> M B) (g:B -> M C)
             `{Proper _ lr_leq m} `{Proper _ lr_leq f}
             `{Proper _ lr_leq g},
        bindM (bindM m f) g ~~ bindM m (fun x => bindM (f x) g);

  }.


(* Helpful bind notation *)
Notation "'do' x <- m1 ; m2" :=
  (bindM m1 (fun x => m2)) (at level 60, right associativity).


(***
 *** Automation for monads
 ***)

Instance Proper_returnM `{Monad} `{LR} :
  Proper (lr_leq ==> lr_leq) returnM.
Proof. prove_lr_proper. Qed.

Instance Proper_bindM `{Monad} {A B} `{LR A} `{LR B} :
  Proper (lr_leq ==> lr_leq ==> lr_leq) (bindM : M A -> (A -> M B) -> M B).
Proof. prove_lr_proper. Qed.

(* Add the monad laws to the LR rewrite set *)
Hint Rewrite @monad_return_bind @monad_bind_return @monad_assoc : LR.


(***
 *** The Identity Monad
 ***)

Definition Identity (X:Type) := X.

Instance IdMonad_MonadOps : MonadOps Identity :=
  { returnM := fun A x => x;
    bindM := fun A B m f => f m;
    lrM := fun A R => R }.

Instance IdMonad : Monad Identity.
constructor; intros; unfold returnM, bindM, lrM, IdMonad_MonadOps;
  try assumption; try prove_lr; try prove_lr_proper.
intros R1 R2 sub; assumption.
Qed.
