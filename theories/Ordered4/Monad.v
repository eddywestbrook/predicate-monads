Require Import Coq.Setoids.Setoid.
Require Export Coq.Classes.Morphisms.
Require Export PredMonad.Ordered4.OrderedType.

Import OTNotations.


(***
 *** The monad typeclass
 ***)

Class MonadOps (MF: forall `(A:OType), Type)
      (MR: forall `(A:OType), relation (MF A))
      (M: forall `(A:OType), OType (MF A) (MR A)) : Type :=
  { returnM : forall `{A:OType}, A -o> M A;
    bindM : forall `{A:OType} `{B:OType}, M A -o> (A -o> M B) -o> M B }.

Instance OTHasType_returnM `(MonadOps) `(A:OType) :
  OTHasType (A -o> M _ _ A) (OTarrow_R A _) returnM returnM.
Proof.
  apply OTHasType_Proper. unfold Proper. reflexivity.
Defined.

Instance OTHasType_bindM `(MonadOps) `(A:OType) `(B:OType) :
  OTHasType (M _ _ A -o> (A -o> M _ _ B) -o> M _ _ B)
            (OTarrow_R (M _ _ A) ((A -o> M _ _ B) -o> M _ _ B))
            bindM bindM.
Proof.
  apply OTHasType_Proper. unfold Proper. reflexivity.
Defined.

Class Monad `(MonadOps) : Prop :=
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
  (bindM @o@ m1 (mkOTerm _ (fun x => m2))) (at level 60, right associativity).


(***
 *** The Identity Monad
 ***)

Definition Identity `(A:OType) : OType (ot_Type A) (ot_R A) := A.

Program Instance IdMonad_MonadOps :
  MonadOps (fun `(A:OType) => T) (fun `(A:OType) => R) (@Identity) :=
  { returnM := fun `(A:OType) => mkOTerm (A -o> Identity A) (fun x => x);
    bindM := fun `(A:OType) `(B:OType) => mkOTerm _ (fun m f => f @o@ m) }.

Instance IdMonad : Monad IdMonad_MonadOps.
Proof.
  constructor; intros; simpl; reflexivity.
Qed.
