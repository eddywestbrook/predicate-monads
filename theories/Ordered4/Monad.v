Require Import Coq.Setoids.Setoid.
Require Export Coq.Classes.Morphisms.
Require Export PredMonad.Ordered4.OrderedType.

Import OTNotations.


(***
 *** The monad typeclass
 ***)

Class MonadOps `(M: OTypeF) : Type :=
  { returnM : forall `{A:OType}, A -o> M @t@ A;
    bindM : forall `{A:OType} `{B:OType},
        M @t@ A -o> (A -o> M @t@ B) -o> M @t@ B }.

Instance OTHasType_returnM `(MonadOps) `(A:OType) :
  OTHasType (A -o> M @t@ A) (OTarrow_R A _) returnM returnM.
Proof.
  apply OTHasType_Proper. unfold Proper. reflexivity.
Defined.

Instance OTHasType_bindM `(MonadOps) `(A:OType) `(B:OType) :
  OTHasType (M @t@ A -o> (A -o> M @t@ B) -o> M @t@ B)
            (OTarrow_R (M @t@ A) ((A -o> M @t@ B) -o> M @t@ B))
            bindM bindM.
Proof.
  apply OTHasType_Proper. unfold Proper. reflexivity.
Defined.

Class Monad `(MonadOps) : Prop :=
  {
    monad_return_bind :
      forall `(A:OType) `(B:OType) (f: A -o> M @t@ B) x,
        bindM @o@ (returnM @o@ x) @o@ f =o= f @o@ x;

    monad_bind_return :
      forall `(A:OType) (m: M @t@ A),
        bindM @o@ m @o@ returnM =o= m;

    monad_assoc :
      forall `(A:OType) `(B:OType) `(C:OType)
             m (f: A -o> M @t@ B) (g: B -o> M @t@ C),
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

Instance Identity : OTypeF (fun `(A:OType) => T) (fun `(A:OType) => R) :=
  fun `(A:OType) => A.

Program Instance IdMonad_MonadOps : MonadOps Identity :=
  { returnM := fun `(A:OType) => mkOTerm (A -o> Identity @t@ A) (fun x => x);
    bindM := fun `(A:OType) `(B:OType) =>
               mkOTerm (Identity @t@ A -o> (A -o> Identity @t@ B) -o> Identity @t@ B)
                       (fun m f => f @o@ m) }.

Instance IdMonad : Monad IdMonad_MonadOps.
Proof.
  constructor; intros; simpl; reflexivity.
Qed.
