
Require Import Coq.Program.Tactics.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Arith.Arith_base.
Require Import Coq.Relations.Relations.


(***
 *** The monad typeclass (unbundled approach)
 ***)

Class MonadRet (M:Type -> Type) : Type :=
  returnM : forall {A:Type}, A -> M A.

Class MonadBind (M:Type -> Type) : Type :=
  bindM : forall {A B:Type}, M A -> (A -> M B) -> M B.

Class MonadEquiv (M:Type -> Type) : Type :=
  eqM : forall {A:Type}, M A -> M A -> Prop.

Notation "m1 '==' m2" := (eqM m1 m2) (at level 80, no associativity).

Class Monad M {MonadRet:MonadRet M} {MonadBind:MonadBind M}
      {MonadEquiv:MonadEquiv M} : Prop :=
  {
    monad_return_bind :
      forall A B x (f:A -> M B), bindM (returnM x) f == f x;
    monad_bind_return : forall A (m:M A), bindM m returnM == m;
    monad_assoc : forall A B C (m:M A) (f: A -> M B) (g: B -> M C),
                    bindM m (fun x => bindM (f x) g) == bindM (bindM m f) g;
    monad_eq_equivalence :> forall A, Equivalence (eqM (A:=A));
    monad_proper_bind :>
      forall A B,
        Proper (eqM (A:=A) ==> ((@eq A) ==> (eqM (A:=B))) ==> eqM (A:=B)) bindM
  }.


(***
 *** Helper theorems about monads
 ***)

Lemma bind_fun_eqM `{Monad} {A B} m (f1 f2:A -> M B) :
  (forall x, f1 x == f2 x) -> bindM m f1 == bindM m f2.
  intro e; apply monad_proper_bind; [ reflexivity | ].
  intros x y e'; rewrite e'; apply e.
Qed.


(***
 *** The Identity Monad
 ***)

Definition Identity (X:Type) := X.
Instance IdMonad_returnM : MonadRet Identity := fun A x => x.
Instance IdMonad_bindM : MonadBind Identity := fun A B m f => f m.
Instance IdMonad_eqM : MonadEquiv Identity := @eq.
Instance IdMonad : Monad Identity.
  constructor; intros; try reflexivity.
  split; auto with typeclass_instances.
  intros m1 m2 eqm f1 f2 eqf.
  rewrite eqm. apply eqf. reflexivity.
Qed.


(***
 *** The State Monad
 ***)

(* StateT itself *)
Definition StateT (S:Type) (M: Type -> Type) (X:Type) := S -> M (prod S X).

Instance StateT_returnM {S} `{MonadRet} : MonadRet (StateT S M) :=
  fun A x => fun s => returnM (s, x).
Instance StateT_bindM {S} `{MonadBind} : MonadBind (StateT S M) :=
  fun A B m f =>
    fun s => bindM (m s) (fun (sx:S * A) => let (s',x) := sx in f x s').
Instance StateT_eqM {S} `{MonadEquiv} : MonadEquiv (StateT S M) :=
  fun {A} m1 m2 => forall s, m1 s == m2 s.

(* The Monad instance for StateT *)
Instance StateT_Monad S `{Monad} : Monad (StateT S M).
  constructor;
    unfold returnM, StateT_returnM, bindM, StateT_bindM; intros.
  intro; rewrite monad_return_bind; reflexivity.
  intro; transitivity (bindM (m s) returnM); [ | apply monad_bind_return ].
  apply bind_fun_eqM; intro sx; destruct sx; reflexivity.
  intro; rewrite <- monad_assoc.
  apply bind_fun_eqM; intro sx; destruct sx.
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
