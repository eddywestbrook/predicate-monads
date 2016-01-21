
Require Import PredMonad.Monad.


(***
 *** The State Monad
 ***)

(* StateT itself *)
Definition StateT (S:Type) (M: Type -> Type) (X:Type) := S -> M (prod S X).

Instance StateT_MonadOps S {LRS:LogRel_Rel S} `{MonadOps} : MonadOps (StateT S M) :=
  {returnM :=
     fun A x => fun s => returnM (s, x);
   bindM :=
     fun A B m f =>
       fun s => bindM (m s) (fun (sx:S * A) => let (s',x) := sx in f x s');
   equalsM :=
     fun {A} {LR} m1 m2 => forall s, equalsM (m1 s) (m2 s) }.


(* The Monad instance for StateT *)
Instance StateT_Monad S `{LogRel S} `{Monad} : Monad (StateT S M).
  constructor; simpl; intros.

  intro; rewrite (monad_return_bind (M:=M));
    [ reflexivity | auto with typeclass_instances ].

  intro; transitivity (bindM (m s) returnM); [ | apply monad_bind_return ].
  apply bind_fun_equalsM; intros.
  intros p1 p2 ep; destruct p1; destruct p2.
  apply monad_proper_return; [ auto with typeclass_instances | assumption ].
  auto with typeclass_instances.
  destruct x; reflexivity.
  auto with typeclass_instances.

FIXME HERE

  intro; rewrite monad_assoc.
  eapply bind_fun_equalsM. intro sx; destruct sx.
  apply bind_fun_eqM; intro sx; destruct sx.
  reflexivity.
  split; intro; intros; intro; intros.
  reflexivity.
  symmetry; apply H0.
  transitivity (y s); [ apply H0 | apply H1 ].
  intros m1 m2 em f1 f2 ef s.
  rewrite (em s).
  apply bind_fun_eqM; intro sx; destruct sx.
  apply ef; reflexivity.

  constructor; constructor.
  intros m s; reflexivity.
  intros m1 m2 e s; symmetry; apply e.
  intros m1 m2 m3 e1 e2 s; transitivity (m2 s); [ apply e1 | apply e2 ].

  intros x y exy s. apply monad_proper_return.
  auto with typeclass_instances.
  split.
  reflexivity.
  assumption.

Qed.


(* The stateful computations class(es) *)

Class MonadGet (S:Type) (M:Type -> Type) : Type := getM : M S.
Class MonadPut (S:Type) (M:Type -> Type) : Type := putM : S -> M unit.

Class MonadState S M {MonadRet:MonadRet M} {MonadBind:MonadBind M}
      {MonadEquiv:MonadEquiv M} {MonadGet:MonadGet S M} {MonadPut:MonadPut S M}
: Prop :=
  {
    monad_state_monad : @Monad M MonadRet MonadBind MonadEquiv;
    monad_state_get_get :
      forall A f,
        bindM getM (fun s => bindM getM (f s)) ==
        (bindM getM (fun s => f s s) : M A);
    monad_state_get_put : bindM getM putM == returnM tt;
    monad_state_put_get :
      forall s, bindM (putM s) (fun _ => getM) ==
                bindM (putM s) (fun _ => returnM s);
    monad_state_put_put :
      forall s1 s2, bindM (putM s1) (fun _ => putM s2) == putM s2
  }.

(* The MonadState instance for StateT *)

Instance StateT_getM {S} `{MonadRet} : MonadGet S (StateT S M) :=
  fun s => returnM (s, s).
Instance StateT_putM {S} `{MonadRet} : MonadPut S (StateT S M) :=
  fun s_new s => returnM (s_new, tt).

Instance StateT_MonadState S `{Monad} : MonadState S (StateT S M).
  constructor; intros; try apply StateT_Monad;
    unfold returnM, StateT_returnM, bindM, StateT_bindM,
           getM, StateT_getM, putM, StateT_putM; intros;
    try (intros; intro; repeat (rewrite monad_return_bind); reflexivity).
  assumption.
Qed.


FIXME HERE: move all the following to a new file, MonadFix.v

(***
 *** Non-Termination Effects
 ***)

(* approxM m1 m2 means m1 "approximates" m2, i.e., m2 is "at least as
terminating as" m1 *)
Class MonadApprox (M:Type -> Type) : Type :=
  approxM : forall {A}, relation (M A).

Notation "m1 '<<<' m2" := (approxM m1 m2) (at level 80, no associativity).

Class MonadFixM (M:Type -> Type) : Type :=
  fixM : forall {A B}, ((A -> M B) -> (A -> M B)) -> A -> M B.

Class MonadFix M {MonadRet:MonadRet M} {MonadBind:MonadBind M}
      {MonadEquiv:MonadEquiv M} {MonadApprox:MonadApprox M}
      {MonadFixM:MonadFixM M}
: Prop :=
  {
    monad_fix_monad :> @Monad M MonadRet MonadBind MonadEquiv;
    monad_fix_approx_preorder :> forall A, PreOrder (approxM (A:=A));
    monad_fix_approx_antisymmetry :
      forall A (m1 m2:M A), approxM m1 m2 -> approxM m2 m1 -> m1 == m2;
    monad_fix_approx_bind :>
      forall A B,
        Proper
          (approxM (A:=A) ==> (@eq A ==> approxM (A:=B)) ==> approxM (A:=B))
          bindM;
    monad_fix_approx_proper :>
      forall A, Proper (eqM (A:=A) ==> eqM (A:=A) ==> iff) approxM;
    monad_fix_fix_proper :>
      forall A B,
        Proper (((@eq A ==> eqM (A:=B)) ==> @eq A ==> eqM (A:=B))
                  ==> @eq A ==> eqM (A:=B)) fixM;
    monad_fix_fixm :
      forall A B f x,
        Proper (((@eq A) ==> (approxM (A:=B))) ==> @eq A ==> approxM (A:=B)) f ->
        fixM (A:=A) (B:=B) f x == f (fixM f) x
  }.

Add Parametric Relation `{MonadFix} A : (M A) (approxM (A:=A))
  reflexivity proved by PreOrder_Reflexive
  transitivity proved by PreOrder_Transitive
as approxM_morphism.
