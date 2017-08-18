Require Export PredMonad.Ordered8.OrderedType.


(***
 *** The monad typeclass
 ***)

Class MonadOps M `{OTypeF M} : Type :=
  { returnM : forall {A} `{OType A}, A -o> M A _ _;
    bindM : forall {A B} `{OType A} `{OType B},
        M A _ _ -o> (A -o> M B _ _) -o> M B _ _ }.

Class Monad M `{MonadOps M} : Prop :=
  {
    monad_return_bind :
      forall A B `{OType A} `{OType B} (f: A -o> M B _ _) x,
        bindM @o@ (returnM @o@ x) @o@ f =o= f @o@ x;

    monad_bind_return :
      forall A `{OType A} m,
        bindM @o@ m @o@ returnM =o= m;

    monad_assoc :
      forall A B C `{OType A} `{OType B} `{OType C}
             m (f: A -o> M B _ _) (g: B -o> M C _ _),
        bindM @o@ (bindM @o@ m @o@ f) @o@ g
        =o=
        bindM @o@ m @o@ (ofun (fun x => bindM @o@ (f @o@ x) @o@ g));
  }.

(* Helpful bind notation *)
Notation "'do' x <- m1 ; m2" :=
  (bindM @o@ m1 @o@ (ofun (fun x => m2))) (at level 60, right associativity).

(* Add the monad laws to the OT rewrite set *)
Hint Rewrite @monad_return_bind @monad_bind_return @monad_assoc : OT.


(***
 *** The Identity Monad
 ***)

Definition Identity A `{OType A} := A.

Instance OTRelationF_Identity : OTRelationF Identity :=
  fun _ R _ => R.

Instance OTypeF_Identity : OTypeF Identity :=
  fun _ _ ot => ot.

Instance IdMonad_MonadOps : MonadOps Identity :=
  { returnM := fun A _ _ => ofun (fun x => x);
    bindM := fun A B _ _ _ _ =>
               ofun (fun m => ofun (fun (f:A -o> B) => f @o@ m)) }.

Instance IdMonad : Monad Identity.
Proof.
  econstructor; intros; simpl; reflexivity.
Qed.
