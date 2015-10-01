
Require Import Coq.Program.Tactics.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.

(***
 *** The monad typeclass (unbundled approach)
 ***)

Class MonadRet (M:Type -> Type) : Type :=
  returnM : forall {A:Type}, A -> M A.

Class MonadBind (M:Type -> Type) : Type :=
  bindM : forall {A B:Type}, M A -> (A -> M B) -> M B.

Class MonadEq (M:Type -> Type) : Type :=
  eqM : forall {A:Type}, M A -> M A -> Prop.

Notation "m1 '==' m2" := (eqM m1 m2) (at level 80, no associativity).

Class Monad M {MonadRet:MonadRet M} {MonadBind:MonadBind M}
      {MonadEq:MonadEq M} : Prop :=
  {
    monad_return_bind :
      forall A B x (f:A -> M B), bindM (returnM x) f == f x;
    monad_bind_return : forall A (m:M A), bindM m returnM == m;
    monad_assoc : forall A B C (m:M A) (f: A -> M B) (g: B -> M C),
                    bindM m (fun x => bindM (f x) g) == bindM (bindM m f) g;
    monad_eq_equivalence :> forall A, Equivalence (eqM (A:=A));
    monad_proper_return : forall A, Proper (@eq A ==> eqM (A:=A)) returnM;
    monad_proper_bind :
      forall A B,
        Proper (eqM (A:=A) ==>
                    respectful (@eq A) (eqM (A:=B)) ==> eqM (A:=B)) bindM
  }.

Add Parametric Relation `{Monad} A : (M A) (eqM (A:=A))
  reflexivity proved by Equivalence_Reflexive
  symmetry proved by Equivalence_Symmetric
  transitivity proved by Equivalence_Transitive
as eqM_morphism.


(***
 *** The Identity Monad
 ***)

Definition Identity (X:Type) := X.
Instance IdMonadRet : MonadRet Identity := fun A x => x.
Instance IdMonadBind : MonadBind Identity := fun A B m f => f m.
Instance IdMonadEq : MonadEq Identity := @eq.
Instance IdMonad : Monad Identity.
  constructor; intros; try reflexivity.
  auto with typeclass_instances.
  intros x y e; assumption.
  intros m1 m2 eqm f1 f2 eqf.
  rewrite eqm; apply eqf; reflexivity.
Qed.


(***
 *** The State Monad
 ***)

(* StateT itself *)
Definition StateT (S:Type) (M: Type -> Type) (X:Type) := S -> M (prod S X).

Instance StateT_returnM {S} `{Monad} : MonadRet (StateT S M) :=
  fun A x => fun s => returnM (s, x).
Instance StateT_bindM {S} `{Monad} : MonadBind (StateT S M) :=
  fun A B m f =>
    fun s => bindM (m s) (fun (sx:S * A) => let (s',x) := sx in f x s').
Instance StateT_eqM {S} `{Monad} : MonadEq (StateT S M) :=
  fun {A} m1 m2 => forall s, eqM (m1 s) (m2 s).

(* The Monad instance for StateT *)
Instance StateT_Monad S `{Monad} : Monad (StateT S M).
  constructor;
  unfold returnM, StateT_returnM, bindM, StateT_bindM, eqM, StateT_eqM; intros.
  rewrite monad_return_bind; reflexivity.
  transitivity (bindM (m s) returnM); [ | apply monad_bind_return ].
  apply monad_proper_bind; [ reflexivity | ].
  intros sx sy e; rewrite e; destruct sy; reflexivity.
  rewrite <- monad_assoc.
  apply monad_proper_bind; [ reflexivity | ].
  intros sx sy e; rewrite e; destruct sy; reflexivity.
  split; intros m1 m2; intros.
  reflexivity.
  symmetry; apply H0.
  transitivity (m2 s); [ apply H0 | apply H1 ].
  intros x y e s; rewrite e; reflexivity.
  intros m1 m2 em f1 f2 ef s.
  apply monad_proper_bind; [ apply em | ].
  intros sx sy es; rewrite es; destruct sy. apply (ef a a eq_refl).
Qed.


(* The stateful computations class(es) *)

Class MonadGet (S:Type) (M:Type -> Type) : Type := getM : M S.
Class MonadPut (S:Type) (M:Type -> Type) : Type := putM : S -> M unit.

Class MonadState S M {MonadRet:MonadRet M} {MonadBind:MonadBind M}
      {MonadEq:MonadEq M} {MonadGet:MonadGet S M} {MonadPut:MonadPut S M}
: Prop :=
  {
    monad_state_monad : @Monad M MonadRet MonadBind MonadEq;
    monad_state_get_get :
      forall A f,
        bindM getM (fun s => bindM getM (f s)) ==
        (bindM getM (fun s => f s s) : M A);
    monad_state_get_put : bindM getM putM == returnM tt;
    monad_state_put_get :
      forall s, bindM (putM s) (fun _ => getM) ==
                bindM (putM s) (fun _ => returnM s);
    monad_state_put_put :
      forall s1 s2, bindM (putM s1) (fun _ => putM s2) == putM s2;
    monad_state_proper_put : Proper (eq ==> eqM) putM
  }.

(* The MonadState instance for StateT *)

Instance StateT_getM {S} `{Monad} : MonadGet S (StateT S M) :=
  fun s => returnM (s, s).
Instance StateT_putM {S} `{Monad} : MonadPut S (StateT S M) :=
  fun s_new s => returnM (s_new, tt).

Instance StateT_MonadState S `{Monad} : MonadState S (StateT S M).
  constructor; intros; try apply StateT_Monad;
    unfold returnM, StateT_returnM, bindM, StateT_bindM, eqM, StateT_eqM,
           getM, StateT_getM, putM, StateT_putM; intros;
    try (repeat (rewrite monad_return_bind); reflexivity).
  intros s1 s2 e s; rewrite e; reflexivity.
Qed.


(***
 *** The Least Fixed-Point / Non-Termination Transformer
 ***)

(* The non-termination monad as sets with at most one element *)
Definition NonTermM X : Type :=
  { S:X -> Prop | forall x y, S x /\ S y -> x = y }.

Program Instance NonTermM_returnM : MonadRet NonTermM :=
  fun A x => (fun y => x = y).

Definition NonTermM_map {X Y} (m:NonTermM X) (f:X -> NonTermM Y) : Y -> Prop :=
  fun y => exists x, proj1_sig m x /\ proj1_sig (f x) y.

Definition NonTermM_map_proof {X Y} (m:NonTermM X) (f:X -> NonTermM Y) :
  forall x y, NonTermM_map m f x /\ NonTermM_map m f y -> x = y.
  unfold NonTermM_map; intros; repeat (destruct H); repeat (destruct H0).
  unfold proj1_sig in * |- *; destruct m.
  rewrite (e x1 x0 $(split; assumption)$) in H2.
  destruct (f x0).
  apply e0; split; assumption.
Qed.

Instance NonTermM_bindM : MonadBind NonTermM :=
  fun (A B:Type) m f =>
    exist _ (NonTermM_map m f) (NonTermM_map_proof m f).

Instance NonTermM_eqM : MonadEq NonTermM :=
  fun {A} m1 m2 => forall x, proj1_sig m1 x <-> proj1_sig m2 x.

Instance NonTermM_Monad : Monad NonTermM.
  constructor;
    unfold returnM, NonTermM_returnM, bindM, NonTermM_bindM, eqM, NonTermM_eqM,
           NonTermM_map, NonTermM_map, proj1_sig;
    intros.
  



  replace f with (fun x => exist _ (proj1_sig (f x)) (proj2_sig (f x)));
   [ | apply functional_extensionality; intros; destruct (f x0); reflexivity ].
  apply eq_dep_eq_sig; apply eq_dep1_dep. eapply eq_dep1_intro.
  Unshelve. Focus 4.
  apply functional_extensionality; intros.

  assert 


  replace f with (fun x => exist _ (proj1_sig_and f x) (proj2_sig_and f x)).
  generalize (proj2_sig_and f).


  generalize (proj1_sig_and f).

   [ | apply functional_extensionality; intros; destruct (f x0); reflexivity ].



(* The empty Type01 *)
Program Definition empty_Type01 X : Type01 X := (fun _ => False).
Obligation 1.
elimtype False; assumption.
Qed.

(* The singleton Type01 *)
Program Definition singleton_Type01 {X} (x:X) : Type01 X := (fun y => x = y).

(* Mapping a Type01 *)
Program Definition map_Type01 {X Y} (f: X -> Type01 )

Definition NonTermT (M: Type -> Type) (X:Type) := M (Type01 X).

Instance NonTermT_returnM `{Monad} : MonadRet (NonTermT M) :=
  fun A x => returnM (singleton_Type01 x).
Instance NonTermT_bindM `{Monad} : MonadBind (NonTermT M) :=
  fun A B m f =>
    bindM m (fun set => )

    fun s => bindM (m s) (fun (sx:S * A) => let (s',x) := sx in f x s').
*)




