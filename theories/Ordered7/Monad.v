Require Export PredMonad.Ordered7.OrderedType.


(***
 *** The monad typeclass
 ***)

Class MonadOps (M: OType -> OType) : Type :=
  { returnM : forall {A}, A -o> M A;
    bindM : forall {A B}, M A -o> (A -o> M B) -o> M B }.

Class Monad M `{MOps:MonadOps M} : Prop :=
  {
    monad_return_bind :
      forall A B (f: A -o> M B) x,
        bindM @o@ (returnM @o@ x) @o@ f =o= f @o@ x;

    monad_bind_return :
      forall A (m : M A), bindM @o@ m @o@ returnM =o= m;

    monad_assoc :
      forall A B C m (f: A -o> M B) (g: B -o> M C),
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

Definition Identity (A:OType) := A.

Instance IdMonad_MonadOps : MonadOps Identity :=
  { returnM := fun A => ofun (fun x => x);
    bindM := fun A B =>
               ofun (fun m => ofun (fun (f:A -o> B) => f @o@ m)) }.

Instance IdMonad : Monad Identity.
Proof.
  constructor; intros; simpl; reflexivity.
Qed.
