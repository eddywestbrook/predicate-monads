Require Export PredMonad.Ordered5.OrderedType.

Import OTNotations.


(***
 *** The monad typeclass
 ***)

Class MonadOps `(M: OTypeF) : Type :=
  { returnM : forall `{ValidOType}, A -o> M @t@ A;
    bindM : forall `{ValidOType} `{B:OType} {_:ValidOType B},
        M @t@ A -o> (A -o> M @t@ B) -o> M @t@ B }.

Class Monad `(MOps:MonadOps) : Prop :=
  {
    monad_ValidOTypeF :> ValidOTypeF M;

    monad_return_bind :
      forall `(A:OType) `(B:OType) `(@ValidOType T A) `(@ValidOType T0 B)
             (f: A -o> M @t@ B) x,
        bindM @o@ (returnM @o@ x) @o@ f =o= f @o@ x;

    monad_bind_return :
      forall `(A:OType) `(@ValidOType T A) m,
        bindM @o@ m @o@ returnM =o= m;

    monad_assoc :
      forall `(A:OType) `(B:OType) `(C:OType)
             `(@ValidOType T A) `(@ValidOType T0 B) `(@ValidOType T1 C)
             m (f: A -o> M @t@ B) (g: B -o> M @t@ C),
        bindM @o@ (bindM @o@ m @o@ f) @o@ g
        =o=
        bindM @o@ m @o@ (mkOTerm _ (fun x => bindM @o@ (f @o@ x) @o@ g));
  }.

(* Helpful bind notation *)
Notation "'do' x <- m1 ; m2" :=
  (bindM @o@ m1 (mkOTerm _ (fun x => m2))) (at level 60, right associativity).


(***
 *** OTHasType Typing Rules
 ***)

(* Typing for returnM *)
Instance OTHasType_returnM `(Monad) `(A:OType) (_:ValidOType A) :
  OTHasType (A -o> M @t@ A) (ot_R (OTarrow A (M @t@ A))) returnM returnM.
Proof.
  apply OTHasType_Proper. unfold Proper. reflexivity.
Defined.

(* Typing for bindM *)
Instance OTHasType_bindM `(Monad) `(A:OType) `(B:OType)
         (_:ValidOType A) (_:ValidOType B) :
  OTHasType (M @t@ A -o> (A -o> M @t@ B) -o> M @t@ B)
            (ot_R (OTarrow (M @t@ A) ((A -o> M @t@ B) -o> M @t@ B)))
            bindM bindM.
Proof.
  apply OTHasType_Proper. unfold Proper. reflexivity.
Defined.


(***
 *** The Identity Monad
 ***)

Instance Identity : OTypeF (fun `(A:OType) => T) :=
  fun `(A:OType) => A.

Instance Valid_Identity : ValidOTypeF Identity.
Proof. constructor; typeclasses eauto. Qed.

Instance IdMonad_MonadOps : MonadOps Identity :=
  { returnM := fun `{ValidOType} =>
                 mkOTerm (A -o> Identity @t@ A) (fun x => x);
    bindM := fun `{ValidOType} `{B:OType} `{@ValidOType T0 B} =>
               mkOTerm (A -o> (A -o> B) -o> B)
                       (fun m (f:Pfun A B) => f @o@ m) }.

Instance IdMonad : Monad IdMonad_MonadOps.
Proof.
  refine ({| monad_ValidOTypeF:=Valid_Identity |}); intros; simpl; reflexivity.
Qed.
