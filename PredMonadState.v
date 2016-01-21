Require Import PredMonad.PredMonad.


Class PredMonadState S M PM
      {MonadRetM:MonadRet M} {MonadBindM:MonadBind M}
      {MonadEquivM:MonadEquiv M} {MonadGetM:MonadGet S M} {MonadPutM:MonadPut S M}
      {MonadRetPM:MonadRet PM} {MonadBindPM:MonadBind PM}
      {MonadEquivPM:MonadEquiv PM} {MonadGetPM:MonadGet S PM} {MonadPutPM:MonadPut S PM}
      {PredMonadSatisfaction:PredMonadSatisfaction M PM}
      {PredMonadForall:PredMonadForall PM}
      {PredMonadExists:PredMonadExists PM} {PredMonadImplication:PredMonadImplication PM}
: Prop :=
  {
    predmonad_state_monad_state_M :> MonadState S M;
    predmonad_state_monad_state_PM :> MonadState S PM;
    predmonad_state_predmonad :> PredMonad M PM;
    predmonad_state_get_get :
      forall m, m |= getM <-> m == getM;
    predmonad_state_put_put :
      forall s m, m |= putM s <-> m == putM s
  }.
