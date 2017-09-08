Require Export PredMonad.Reflection2.PredMonad.
Require Export PredMonad.Reflection2.MonadState.


(***
 *** Predicate Monads with State Effects
 ***)

Class PredMonadState M PM St {OM} {FOM: FindOTypeF1 M OM}
      {OPM} {FOPM: FindOTypeF1 PM OPM} {OSt: OType St}
      {MOps: @MonadOps M OM FOM} {PMOps: @MonadOps PM OPM FOPM}
      {PredOps: @PredMonadOps M PM OM FOM OPM FOPM}
      {MSOps: @MonadStateOps M OM FOM St OSt}
      {PMSOps: @MonadStateOps PM OPM FOPM St OSt}
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
