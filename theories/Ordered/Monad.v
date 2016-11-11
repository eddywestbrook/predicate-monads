
Require Export PredMonad.Ordered.OrderedType.
Import OTermNotations.

(***
 *** The monad typeclass
 ***)

Class MonadOps (M : OType -> OType) : Type :=
  { returnM : forall {A}, A -o> M A;
    bindM : forall {A B}, M A -o> (A -o> M B) -o> M B }.

Class Monad (M : OType -> OType) {MonadOps:MonadOps M} : Prop :=
  {
    monad_return_bind :
      forall {A B ctx} (f: OTerm ctx (A -o> M B)) x,
        !bindM @o@ (!returnM @o@ x) @o@ f =o= f @o@ x;

    monad_bind_return :
      forall {A ctx} (m: OTerm ctx (M A)),
        !bindM @o@ m @o@ !returnM =o= m;

    monad_assoc :
      forall {A B C ctx} m (f:OTerm ctx (A -o> M B)) (g:OTerm ctx (B -o> M C)),
        !bindM @o@ (!bindM @o@ m @o@ f) @o@ g
        =o=
        !bindM @o@ m @o@ (pfun (x:::_) ==> !bindM @o@ (!f @o@ !x) @o@ !g);

  }.


(* Helpful bind notation *)
Notation "'do' x <- m1 ; m2" :=
  ((!bindM @o@ m1%pterm @o@ (pfun (x:::_) ==> m2%pterm))%pterm)
    (at level 60, right associativity).

(*
Check (fun `{Monad} => do x <- returnM @o@ ot_fst; !returnM @o@ ot_fst).
 *)

Definition Identity (X:OType) := X.

Instance IdMonad_MonadOps : MonadOps Identity :=
  { returnM := fun A => (pfun (x:::_) ==> x)%pterm;
    bindM := fun A B => (pfun (m:::_) ==> pfun (f:::_) ==> f @o@ !m)%pterm; }.

Instance IdMonad : Monad Identity.
Proof.
  constructor.
  { intros. unfold bindM, returnM, IdMonad_MonadOps.

FIXME HERE NOW: need rewrite rules for beta!
