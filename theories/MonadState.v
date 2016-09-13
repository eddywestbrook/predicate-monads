Require Import PredMonad.Monad.

Global Instance EqualsOp_unit : EqualsOp unit :=
{ equals := fun _ _ => True }.
Instance Equals_unit : Equals unit.
Proof.
  constructor.
  constructor; compute; tauto.
Qed.

Hint Extern 1 (EqualsOp unit) => exact EqualsOp_unit : typeclass_instances.


(***
 *** Monads with State Effects
 ***)

Section State.
  Polymorphic Variables (S : Type) (M : Type -> Type).
  (* State effects = get and put *)
  Polymorphic Class MonadStateOps : Type :=
  { getM : M S
  ; putM : S -> M unit
  }.
  Polymorphic Context `{Equals S} `{MonadOps M}.

  Polymorphic Class MonadState (ms : MonadStateOps) : Prop :=
  {
    monad_state_monad :> Monad M;
    monad_state_get_get :
      forall A `{Eq_A:Equals A} f,
        bindM getM (fun s => bindM getM (f s)) ==
        (bindM getM (fun s => f s s) : M A);
    monad_state_get_put : bindM getM putM == returnM tt ;
    monad_state_put_get :
      forall s, bindM (putM s) (fun _ => getM) ==
                bindM (putM s) (fun _ => returnM s);
    monad_state_put_put :
      forall s1 s2, bindM (putM s1) (fun _ => putM s2) == putM s2
  }.
End State.

(***
 *** The State Monad Transformer
 ***)

Section StateT.

Context (S:Type).

Record StateResult (T : Type) : Type := mkStResult
{ state : S ; result : T }.

Arguments mkStResult {_} _ _.
Arguments state {_} _.
Arguments result {_} _.

(* NOTE: StateT requires that propositional equality, eq, be used as the
distinguished equality for the state type, S. Otherwise, we need to restrict
StateT to only contain Proper functions from S, which seems like a pain. *)
Global Instance S_EqualsOp {A} `{EqualsOp A} : EqualsOp (StateResult A) :=
  fun a b => a.(state) = b.(state) /\ equals a.(result) b.(result).
Global Instance S_Equals {A} `{Equals A} : Equals (StateResult A).
Proof.
  constructor. constructor.
  - constructor; auto. eapply reflexivity.
  - red. destruct 1. constructor; auto. symmetry. auto.
  - red. destruct 1. destruct 1. constructor. congruence. rewrite H1. assumption.
Qed.

(* StateT itself *)
Variable M : Type -> Type.

Definition StateT (X:Type) := S -> M (StateResult X).

Global Instance StateT_EqualsOp {A} `{MonadOps M} `{EqualsOp A} : EqualsOp (StateT A) :=
  pointwise_relation S equals.
Global Instance StateT_Equals {A} `{Monad M} `{Equals A} : Equals (StateT A).
Proof.
  constructor; constructor.
  { red. intro. reflexivity. }
  { red. intro. symmetry. assumption. }
  { red. intro. etransitivity; eauto. }
Qed.

Global Instance StateT_MonadOps `{MonadOps M} : MonadOps StateT :=
  {returnM :=
     fun A x => fun s => returnM (mkStResult s x);
   bindM :=
     fun A B m f =>
       fun s => bindM (m s) (fun sx => let '(mkStResult s' x) := sx in f x s');
   equalsM :=
     fun {A} {EqualsOp} m1 m2 =>
       forall s, (m1 s) == (m2 s) }.

Ltac tc := eauto with typeclass_instances.

(* The Monad instance for StateT *)
Global Instance StateT_Monad `{Monad M} : Monad (StateT).
  constructor; simpl; intros.
  { red. intros.
    rewrite (monad_return_bind (M:=M));
      try auto with typeclass_instances; reflexivity. }
  { red; intros.
    etransitivity.
    eapply (monad_proper_bind (M:=M)). tc. tc. reflexivity.
    instantiate (1 := returnM).
    red. intros. destruct x. eapply monad_proper_return; tc.
    eapply (monad_bind_return (M:=M)). tc. }
  { red. intros.
    rewrite monad_assoc; tc.
    eapply bind_fun_equalsM. intros.
    destruct x. reflexivity. }
  { eapply StateT_Equals. }
  { red. red. intros.
    eapply monad_proper_return; tc.
    split. reflexivity. assumption. }
  { do 4 red. intros.
    eapply monad_proper_bind; tc.
    red. intros.
    destruct x1; destruct y1. destruct H4; simpl in *.
    subst. eapply H3. assumption. }
  { red. red. unfold subrelation.
    intros.
    eapply monad_proper_equalsM. 2: eapply H1.
    red. intros; auto. unfold S_EqualsOp in *.
    destruct H2; split; auto.
    unfold equals in *. eapply H0. assumption. }
Qed.

Global Instance StateT_getM `{Monad M} : MonadStateOps S (StateT) :=
{ getM := fun s => returnM (mkStResult s s)
; putM := fun s_new s => returnM (mkStResult s_new tt) }.

Definition EqualsOp_Libniz (T : Type) : EqualsOp T := @eq T.
Definition Equals_Libniz (T : Type) : @Equals T (EqualsOp_Libniz T).
Proof.
  constructor. compute. tc.
Qed.

Local Existing Instance Equals_Libniz.

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
