Require Export PredMonad.Reflection2.PredMonad.
Require Export PredMonad.Reflection2.MonadState.


(***
 *** Predicate Monads with State Effects
 ***)

Class PredMonadState M PM St {FOM: OTypeF1 M} {FOPM: OTypeF1 PM}
      {OSt: OType St} {MOps: @MonadOps M FOM} {PMOps: @MonadOps PM FOPM}
      {PredOps: @PredMonadOps M PM FOM FOPM}
      {MSOps: @MonadStateOps M FOM St OSt}
      {PMSOps: @MonadStateOps PM FOPM St OSt}
  : Prop :=
  {
    (* M and PM must form a predicate monad *)
    predmonadstate_predmonad :> PredMonad M PM;

    (* Lifting for getM and putM *)
    predmonadstate_liftP_getM : liftP @o@ getM =o= getM;
    predmonadstate_liftP_putM :
      forall s, liftP @o@ (putM @o@ s) =o= putM @o@ s;

    (* FIXME HERE: laws for commuting forallP and existsP with getM and putM *)
  }.


(* FIXME HERE: prove that StateT builds a predicate monad for StateT *)
