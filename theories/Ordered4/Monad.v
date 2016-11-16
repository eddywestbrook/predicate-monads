Require Import Coq.Setoids.Setoid.
Require Export Coq.Classes.Morphisms.
Require Export PredMonad.Ordered4.OrderedType.

Import OTNotations.


(***
 *** The monad typeclass
 ***)

Class MonadOps {MF: forall `(A:OType), Type}
      {MR: forall `(A:OType), relation (MF A)}
      (M: forall `(A:OType), OType (MF A) (MR A)) : Type :=
  { returnM : forall `{A:OType}, A -o> M A;
    bindM : forall `{A:OType} `{B:OType}, M A -o> (A -o> M B) -o> M B }.

Instance OTHasType_returnM `(MonadOps) `(A:OType) :
  OTHasType (A -o> M _ _ A) (ot_R _) returnM returnM.
Proof.
  apply OTHasType_Proper. unfold Proper. reflexivity.
Defined.

Instance OTHasType_bindM `(MonadOps) `(A:OType) `(B:OType) :
  OTHasType (M _ _ A -o> (A -o> M _ _ B) -o> M _ _ B) (ot_R _) bindM bindM.
Proof.
  apply OTHasType_Proper. unfold Proper. reflexivity.
Defined.

Typeclasses eauto := debug.
Definition exM `(MonadOps) `(A:OType) `(B:OType) `(C:OType)
           m (f: A -o> M _ _ B) (g: B -o> M _ _ C) :=
  (mkOTerm (A -o> M _ _ C) (fun x => bindM @o@ (f @o@ x) @o@ g)).

Class Monad `{MonadOps} : Prop :=
  {
    monad_return_bind :
      forall `(A:OType) `(B:OType) (f: A -o> M _ _ B) x,
        bindM @o@ (returnM @o@ x) @o@ f =o= f @o@ x;

    monad_bind_return :
      forall `(A:OType) (m: M _ _ A),
        bindM @o@ m @o@ returnM =o= m;

    monad_assoc :
      forall `(A:OType) `(B:OType) `(C:OType)
             m (f: A -o> M _ _ B) (g: B -o> M _ _ C),
        bindM @o@ (bindM @o@ m @o@ f) @o@ g
        =o=
        bindM @o@ m @o@ (mkOTerm _ (fun x => bindM @o@ (f @o@ x) @o@ g));
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
