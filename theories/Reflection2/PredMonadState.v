Require Export PredMonad.Reflection2.PredMonad.
Require Export PredMonad.Reflection2.MonadState.


(***
 *** Predicate Monads with State Effects
 ***)

Class PredMonadState M PM St {OM: OTypeF1 M} {OPM: OTypeF1 PM} {OSt: OType St}
      {MOps: @MonadOps M OM} {PMOps: @MonadOps PM OPM}
      {PredOps: @PredMonadOps M PM OM OPM}
      {MSOps: @MonadStateOps M OM St OSt} {PMSOps: @MonadStateOps PM OPM St OSt}
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


(***
 *** Hoare Logic using Predicate Monads
 ***)

Definition HoareP `{PredMonadState} `{OType} :
  (St -o> Flip Prop) -o> (St -o> A -o> St -o> Prop) -o> PM A _ :=
  ofun pre =>
  ofun post =>
  do s_pre <- getM;
    assumingP
      @o@ (pre @o@ s_pre)
      @o@ (do x <- trueP;
             do s_post <- getM;
             do unused
                <- assertP @o@ (post @o@ s_pre @o@ x @o@ s_post);
             returnM @o@ x).
