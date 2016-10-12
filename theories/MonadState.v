Require Import PredMonad.SemiPreOrder.
Require Import PredMonad.Monad.

(***
 *** Monads with State Effects
 ***)

Section MonadState.
  Context (S : Type) {R_S} `{LR_S:@LR S R_S} (M : Type -> Type) `{MonadOps M}.

  (* State effects = get and put *)
  Class MonadStateOps : Type :=
  { getM : M S
  ; putM : S -> M unit
  }.

  Class MonadState (ms : MonadStateOps) : Prop :=
  {
    monad_state_monad :> Monad M;
    monad_proper_get :> Proper lr_leq getM;
    monad_proper_put :> Proper lr_leq putM;
    monad_state_get :
      forall {A} `{LR A} (m : M A),
        Proper lr_leq m ->
        bindM getM (fun _ => m) ~~ m ;

    monad_state_get_put :
      forall {A} `{LR A} (f : S -> unit -> M A),
        Proper lr_leq f ->
        bindM getM (fun s => bindM (putM s) (f s)) ~~ bindM getM (fun s => f s tt) ;

    monad_state_put_get :
      forall {A} `{LR A} s (f : unit -> S -> M A),
        Proper lr_leq f ->
        bindM (putM s) (fun u => bindM getM (f u))
              ~~ bindM (putM s) (fun u => f u s) ;

    monad_state_put_put :
      forall {A} `{LR A} s1 s2 (f : unit -> unit -> M A),
        Proper lr_leq f ->
        bindM (putM s1) (fun u => bindM (putM s2) (f u)) ~~ bindM (putM s2) (f tt)
  }.

End MonadState.

(***
 *** The State Monad Transformer
 ***)

Section StateT.

Context (S:Type) {R_S:LR_Op S} `{@LR S R_S} (M:Type -> Type) `{Monad M}.

Definition StateT (X:Type) := S -> M (S * X).

Global Instance StateT_MonadOps : MonadOps StateT :=
  {returnM :=
     fun A x => fun s => returnM (s, x);
   bindM :=
     fun A B m f =>
       fun s => do s_x <- m s; f (snd s_x) (fst s_x);
   lrM := fun {A} _ => LR_Op_fun }.

(* The Monad instance for StateT *)
Global Instance StateT_Monad : Monad (StateT).
Proof.
  constructor; intros; unfold StateT, returnM, bindM, lrM, StateT_MonadOps.
  - auto with typeclass_instances.
  - prove_lr_proper.
  - prove_lr_proper.
  - intros R1 R2 subR; apply LRFun_Proper_subrelation; apply monad_proper_lrM;
      apply LRPair_Proper_subrelation; try assumption; reflexivity.
  - prove_lr.
  - transitivity (fun s => do s_x <- m s; returnM s_x).
    + split; build_lr_fun; apply monad_proper_bind; prove_lr.
    + prove_lr.
  - prove_lr.
Qed.

FIXME HERE NOW

Instance StateT_MonadState `{Monad M}
: @MonadState S StateT (EqualsOp_Libniz S) _ _.
Proof.
  constructor.
  { eapply StateT_Monad. }
  { intros.
    do 3 red. intros.
    unfold bindM. simpl.
    repeat rewrite monad_return_bind; tc.
    reflexivity. }
  { do 3 red; intros. unfold bindM; simpl.
    repeat rewrite monad_return_bind; tc.
    reflexivity. }
  { do 3 red. intros.
    unfold bindM; simpl.
    repeat rewrite monad_return_bind; tc. reflexivity. }
  { do 3 red. intros.
    unfold bindM; simpl.
    repeat rewrite monad_return_bind; tc. reflexivity. }
Qed.

End StateT.

Arguments MonadState _ _ {_ _ _} : clear implicits.
