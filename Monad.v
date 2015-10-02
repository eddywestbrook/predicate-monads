
Require Import Coq.Program.Tactics.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Arith.Arith_base.


(***
 *** The monad typeclass (unbundled approach)
 ***)

Class MonadRet (M:Type -> Type) : Type :=
  returnM : forall {A:Type}, A -> M A.

Class MonadBind (M:Type -> Type) : Type :=
  bindM : forall {A B:Type}, M A -> (A -> M B) -> M B.

Class MonadOrder (M:Type -> Type) : Type :=
  leqM : forall {A:Type}, M A -> M A -> Prop.

Notation "m1 '<<<' m2" := (leqM m1 m2) (at level 80, no associativity).

Definition eqM `{MonadOrder} {A} : M A -> M A -> Prop :=
  fun m1 m2 => m1 <<< m2 /\ m2 <<< m1.

Notation "m1 '==' m2" := (eqM m1 m2) (at level 80, no associativity).

Instance equiv_leqM_equiv_eqM `{MonadOrder} A {E:Equivalence (leqM (A:=A))} : Equivalence (eqM (A:=A)).
  unfold eqM; constructor.
  intro m; split; reflexivity.
  intros m1 m2 H0; destruct H0; split; assumption.
  intros m1 m2 m3 H1 H2; destruct H1; destruct H2;
    split; transitivity m2; assumption.
Qed.

Class Monad M {MonadRet:MonadRet M} {MonadBind:MonadBind M}
      {MonadOrder:MonadOrder M} : Prop :=
  {
    monad_return_bind :
      forall A B x (f:A -> M B), bindM (returnM x) f == f x;
    monad_bind_return : forall A (m:M A), bindM m returnM == m;
    monad_assoc : forall A B C (m:M A) (f: A -> M B) (g: B -> M C),
                    bindM m (fun x => bindM (f x) g) == bindM (bindM m f) g;
    monad_leq_preorder :> forall A, PreOrder (leqM (A:=A));
    monad_proper_return : forall A, Proper (@eq A ==> leqM (A:=A)) returnM;
    monad_proper_bind :
      forall A B,
        Proper (leqM (A:=A) ==>
                     respectful (@eq A) (leqM (A:=B)) ==> leqM (A:=B)) bindM
  }.


(***
 *** Stuff Needed for Rewriting w.r.t. eqM and leqM
 ***)

Add Parametric Relation `{Monad} A : (M A) (leqM (A:=A))
  reflexivity proved by PreOrder_Reflexive
  transitivity proved by PreOrder_Transitive
as leqM_morphism.

Instance eqM_Equivalence `{Monad} A : Equivalence (eqM (A:=A)).
  constructor.
  intro m; split; reflexivity.
  intros m1 m2 H1; destruct H1; split; assumption.
  intros m1 m2 m3 H1 H2; destruct H1; destruct H2; split; transitivity m2; assumption.
Qed.

Add Parametric Relation `{Monad} A : (M A) (eqM (A:=A))
  reflexivity proved by Equivalence_Reflexive
  symmetry proved by Equivalence_Symmetric
  transitivity proved by Equivalence_Transitive
as eqM_morphism.

Instance proper_eqM_leqM `{Monad} A : Proper (eqM (A:=A) ==> eqM (A:=A) ==> iff) (leqM (A:=A)).
  intros x1 y1 eq1 x2 y2 eq2; destruct eq1; destruct eq2; split; intro.
  transitivity x1; [ assumption | ]; transitivity x2; assumption.
  transitivity y1; [ assumption | ]; transitivity y2; assumption.
Qed.

Instance monad_proper_return_eqM `{Monad} A :
  Proper (@eq A ==> eqM (A:=A)) returnM.
  intros x y e. rewrite e. reflexivity.
Qed.

Instance monad_proper_bind_eqM `{Monad} A B :
  Proper (eqM (A:=A) ==> respectful (@eq A) (eqM (A:=B)) ==> eqM (A:=B)) bindM.
  intros m1 m2 eqm f1 f2 eqf. destruct eqm.
  split; (apply monad_proper_bind; [ assumption | ]; intros x1 x2 e;
          destruct (eqf x1 x2 e)).
  assumption.
  rewrite e; replace (f1 x2) with (f1 x1); [ assumption | rewrite e; reflexivity ].
Qed.


(***
 *** The Identity Monad
 ***)

Definition Identity (X:Type) := X.
Instance IdMonad_returnM : MonadRet Identity := fun A x => x.
Instance IdMonad_bindM : MonadBind Identity := fun A B m f => f m.
Instance IdMonad_leqM : MonadOrder Identity := @eq.
Instance IdMonad : Monad Identity.
  constructor; intros; try reflexivity.
  split; auto with typeclass_instances.
  intros x y e; rewrite e; reflexivity.
  intros m1 m2 leqm f1 f2 leqf.
  rewrite leqm. apply leqf. reflexivity.
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
Instance StateT_leqM {S} `{Monad} : MonadOrder (StateT S M) :=
  fun {A} m1 m2 => forall s, leqM (m1 s) (m2 s).

(* Extensionality law for == on StateT *)
Lemma StateT_eqM_ext {S} `{Monad} A (m1 m2: StateT S M A) :
  (forall s, m1 s == m2 s) -> m1 == m2.
  unfold eqM, leqM, StateT_leqM; intro e; split; intros;
    destruct (e s); assumption.
Qed.

(* The Monad instance for StateT *)
Instance StateT_Monad S `{Monad} : Monad (StateT S M).
  constructor;
    unfold returnM, StateT_returnM, bindM, StateT_bindM;
    intros; try (apply StateT_eqM_ext); intros.
  rewrite monad_return_bind; reflexivity.
  transitivity (bindM (m s) returnM); [ | apply monad_bind_return ].
  apply monad_proper_bind_eqM; [ reflexivity | ].
  intros sx sy e; rewrite e; destruct sy; reflexivity.
  rewrite <- monad_assoc.
  apply monad_proper_bind_eqM; [ reflexivity | ].
  intros sx sy e; rewrite e; destruct sy; reflexivity.
  split; intro; intros; intro; intros.
  reflexivity.
  transitivity (y s); [ apply H0 | apply H1 ].
  intros x y e s; rewrite e; reflexivity.
  intros m1 m2 em f1 f2 ef s.
  apply monad_proper_bind; [ apply em | ].
  intros sx sy es; rewrite es; destruct sy. apply (ef a a eq_refl).
Qed.


(* The stateful computations class(es) *)

Class MonadGet (S:Type) (M:Type -> Type) : Type := getM : M S.
Class MonadPut (S:Type) (M:Type -> Type) : Type := putM : S -> M unit.

Class MonadState S M {MonadRet:MonadRet M} {MonadBind:MonadBind M}
      {MonadOrder:MonadOrder M} {MonadGet:MonadGet S M} {MonadPut:MonadPut S M}
: Prop :=
  {
    monad_state_monad : @Monad M MonadRet MonadBind MonadOrder;
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
    monad_state_proper_put : Proper (eq ==> leqM) putM
  }.

(* The MonadState instance for StateT *)

Instance StateT_getM {S} `{Monad} : MonadGet S (StateT S M) :=
  fun s => returnM (s, s).
Instance StateT_putM {S} `{Monad} : MonadPut S (StateT S M) :=
  fun s_new s => returnM (s_new, tt).

Instance StateT_MonadState S `{Monad} : MonadState S (StateT S M).
  constructor; intros; try apply StateT_Monad;
    unfold returnM, StateT_returnM, bindM, StateT_bindM,
           getM, StateT_getM, putM, StateT_putM; intros;
    try (apply StateT_eqM_ext; intros;
         repeat (rewrite monad_return_bind); reflexivity).
  intros s1 s2 e s; rewrite e; reflexivity.
Qed.


(***
 *** The Least Fixed-Point / Non-Termination Monad
 ***)

(* The non-termination monad as sets with at most one element *)
Definition FixM X : Type :=
  { S:X -> Prop | forall x y, S x /\ S y -> x = y }.

Program Instance FixM_returnM : MonadRet FixM :=
  fun A x => (fun y => x = y).

(* Helper for defining bind on FixM *)
Definition FixM_map {X Y} (m:FixM X) (f:X -> FixM Y) : Y -> Prop :=
  fun y => exists x, proj1_sig m x /\ proj1_sig (f x) y.

(* Helper for the helper for defining bind on FixM *)
Definition FixM_map_proof {X Y} (m:FixM X) (f:X -> FixM Y) :
  forall x y, FixM_map m f x /\ FixM_map m f y -> x = y.
  unfold FixM_map; intros; repeat (destruct H); repeat (destruct H0).
  unfold proj1_sig in * |- *; destruct m.
  rewrite (e x1 x0 $(split; assumption)$) in H2.
  destruct (f x0).
  apply e0; split; assumption.
Qed.

Instance FixM_bindM : MonadBind FixM :=
  fun (A B:Type) m f =>
    exist _ (FixM_map m f) (FixM_map_proof m f).

Instance FixM_leqM : MonadOrder FixM :=
  fun {A} m1 m2 => forall x, proj1_sig m1 x -> proj1_sig m2 x.

(* Extensionality law for <<< on FixM *)
Lemma FixM_leqM_ext A (m1 m2: FixM A) :
  (forall x, proj1_sig m1 x -> proj1_sig m2 x) -> m1 <<< m2.
  intros H x; apply H.
Qed.

(* Extensionality law for == on FixM *)
Lemma FixM_eqM_ext A (m1 m2: FixM A) :
  (forall x, proj1_sig m1 x <-> proj1_sig m2 x) -> m1 == m2.
  intro equiv; split; intros x elem; destruct (equiv x);
    [ apply H | apply H0 ]; assumption.
Qed.

(* Monad instance for FixM *)
Instance FixM_Monad : Monad FixM.
  constructor;
    unfold returnM, FixM_returnM, bindM, FixM_bindM,
           FixM_map, FixM_map, proj1_sig;
    intros; try (apply FixM_eqM_ext; unfold proj1_sig; intros).
  split; intros.
  destruct H; destruct H. rewrite H; assumption.
  exists x; split; [ reflexivity | assumption ].
  split; intros.
  destruct H; destruct H. rewrite <- H0; assumption.
  exists x; split; [ assumption | reflexivity ].
  split; intros.
  destruct H; destruct H; destruct H0; destruct H0.
  exists x1; split; [ | assumption ].
  exists x0; split; assumption.
  destruct H; destruct H; destruct H; destruct H.
  exists x1; split; [ assumption | ].
  exists x0; split; assumption.

  constructor.
  intros x y H; assumption.
  intros m1 m2 m3 H1 H2 x pf; apply H2; apply H1; assumption.

  intros x y e_xy z elem_z; unfold proj1_sig in * |- *.
  rewrite <- e_xy; assumption.

  intros m1 m2 leqm f1 f2 leqf x elem_x; unfold proj1_sig in * |- *.
  destruct elem_x; destruct H. exists x0. split.
  apply leqm; assumption.
  apply (leqf x0 x0 eq_refl); assumption.
Qed.


(* The non-termination effects *)

Class MonadFixM (M:Type -> Type) {MonadOrder:MonadOrder M} : Type :=
  fixM : forall {A B}, ((A -> M B) -> (A -> M B)) -> A -> M B.

Class MonadFix M {MonadRet:MonadRet M} {MonadBind:MonadBind M}
      {MonadOrder:MonadOrder M} {MonadFixM:MonadFixM M}
: Prop :=
  {
    monad_fix_monad : @Monad M MonadRet MonadBind MonadOrder;
    monad_fix_fixm :
      forall A B f x,
        Proper (respectful (@eq A) (leqM (A:=B)) ==> @eq A ==> leqM (A:=B)) f ->
        fixM (A:=A) (B:=B) f x == f (fixM f) x
  }.


(* The MonadFix instances for FixM *)

Definition FixM_Bottom {A} : FixM A :=
  exist (fun P => forall x y, P x /\ P y -> x = y)
        (fun x => False)
        (fun x y (H: False /\ False) => match proj1 H with end).

Fixpoint iterate_f {A} n (f: A -> A) :=
  match n with
    | 0 => fun x => x
    | S n' => fun x => f (iterate_f n' f x)
  end.

Program Instance FixM_fixM : MonadFixM FixM :=
  fun {A B} f x =>
    exist _ (fun y =>
               exists n,
                 proj1_sig (iterate_f n f (fun _ => FixM_Bottom) x) y
                 /\ forall n' y',
                      n' < n ->
                      ~(proj1_sig (iterate_f n' f (fun _ => FixM_Bottom) x) y')) _.
Obligation 1.
destruct (lt_eq_lt_dec H H0) as [ comp | l ]; [ destruct comp | ].
elimtype False; apply (H2 _ _ l H3).
rewrite e in H3.
apply (proj2_sig (iterate_f H0 f (fun _ : A => FixM_Bottom) x)).
split; assumption.
elimtype False; apply (H4 _ _ l H1).
Qed.

(*
Instance FixM_MonadFix : MonadFix FixM.
constructor; [ auto with typeclass_instances | ].
intros. unfold fixM, FixM_fixM.
apply FixM_eqM_ext; intros; unfold proj1_sig.
*)


(***
 *** A Better Fixed-Point Monad
 ***)

(* The idea here is that we only actually care about the first non-None value;
this way, we don't have any proofs in computations. *)
Definition FixM2 A := nat -> option A.

(* Get the first value of m at or below n *)
Fixpoint first_value_below {A} (m:FixM2 A) n : option A :=
  match n with
    | 0 => m 0
    | S n' =>
      match first_value_below m n' with
        | Some x => Some x
        | None => m n
      end
  end.

Lemma first_value_below_correct_None {A} m n :
  @first_value_below A m n = None ->
  (forall n', n' <= n -> m n' = None).
  induction n; intros.
  inversion H0. apply H.
  unfold first_value_below in H; fold (@first_value_below A) in H.
  destruct (first_value_below m n); [ discriminate | ].
  inversion H0.
  assumption.
  apply IHn; [ reflexivity | assumption ].
Qed.

Lemma first_value_below_complete_None {A} m n :
  (forall n', n' <= n -> m n' = None) ->
  @first_value_below A m n = None.
  induction n; intros.
  apply H; apply le_n.
  unfold first_value_below; fold (@first_value_below A).
  rewrite IHn.
  apply H; apply le_n.
  intros; apply H; apply le_S; assumption.
Qed.

Lemma first_value_below_correct_Some {A} m n (x:A) :
  first_value_below m n = Some x ->
  exists n', n' <= n /\ m n' = Some x /\ (forall n'', n'' < n' -> m n'' = None).
  induction n; unfold first_value_below; fold (@first_value_below A); intro H.
  exists 0; split; [ constructor | split; [ assumption | ] ].
  intros; inversion H0.
  case_eq (first_value_below m n); intros; rewrite H0 in * |- *.
  destruct (IHn H) as [ n' H1 ]; destruct H1; destruct H2.
  exists n'. split; [ apply le_S; assumption | split; assumption ].
  exists (S n). split; [ apply le_n | split; [ assumption | ] ].
  intros. apply (first_value_below_correct_None _ n).
  assumption.
  apply le_S_n; assumption.
Qed.

Lemma first_value_below_complete_Some {A} m n n' (x:A) :
  n' <= n -> m n' = Some x -> (forall n'', n'' < n' -> m n'' = None) ->
  first_value_below m n = Some x.
  intro leq; induction leq; intros.
  destruct n'.
  assumption.
  unfold first_value_below; fold (@first_value_below A).
  rewrite first_value_below_complete_None; [ assumption | ].
  intros; apply H0; apply le_n_S; assumption.
  unfold first_value_below; fold (@first_value_below A).
  rewrite IHleq; [ reflexivity | assumption | assumption ].
Qed.

Lemma first_value_below_constant_fun {A} (x:option A) n :
  first_value_below (fun _ => x) n = x.
  induction n.
  reflexivity.
  unfold first_value_below; fold (@first_value_below A).
  rewrite IHn; destruct x; reflexivity.
Qed.

Lemma first_value_below_stable {A} (m:FixM2 A) n n' x :
  n <= n' -> first_value_below m n = Some x ->
  first_value_below m n' = Some x.
  intro l; induction l.
  unfold first_value_below; fold (@first_value_below A).
  intro e; rewrite e; reflexivity.
  unfold first_value_below; fold (@first_value_below A).
  intro. rewrite (IHl H). reflexivity.
Qed.

Lemma first_value_below_idempotent {A} (m:FixM2 A) n :
  first_value_below (fun n' => first_value_below m n') n =
  first_value_below m n.
  induction n.
  reflexivity.
  unfold first_value_below; repeat (fold (@first_value_below A)).
  rewrite IHn.
  destruct (first_value_below m n); reflexivity.
Qed.

(* True iff the "true" value of m is x *)
Definition value_is {A} (m:FixM2 A) (x:A) : Prop :=
  exists n, first_value_below m n = Some x.

Lemma value_is_functional {A} m (x1 x2:A) :
  value_is m x1 -> value_is m x2 -> x1 = x2.
  intros vis1 vis2; destruct vis1; destruct vis2.
  destruct (lt_eq_lt_dec x x0); [ destruct s | ];
  (assert (Some x1 = Some x2) as helper; [ | injection helper; intros; assumption ]).
  assert (x <= x0); [ apply le_S_n; apply le_S; assumption | ].
  rewrite <- H0. rewrite <- (first_value_below_stable _ _ _ _ H1 H). reflexivity.
  rewrite e in H; rewrite <- H; rewrite <- H0; reflexivity.
  assert (x0 <= x); [ apply le_S_n; apply le_S; assumption | ].
  rewrite <- H. rewrite <- (first_value_below_stable _ _ _ _ H1 H0). reflexivity.
Qed.

Instance FixM2_returnM : MonadRet FixM2 :=
  fun {A} x => fun n => Some x.

Instance FixM2_bindM : MonadBind FixM2 :=
  fun {A B} m f =>
    fun n =>
      match first_value_below m n with
        | None => None
        | Some x => first_value_below (f x) n
      end.

Instance FixM2_leqM : MonadOrder FixM2 :=
  fun {A} m1 m2 => forall x, value_is m1 x -> value_is m2 x.

Instance value_is_proper {A} :
  Proper (eqM (A:=A) ==> @eq A ==> iff) value_is.
intros m1 m2 em x1 x2 ex. rewrite ex. destruct em as [ em1 em2 ].
split; intro H.
apply (em1 x2 H).
apply (em2 x2 H).
Qed.

Instance first_value_below_is_proper {A} :
  Proper (respectful (@eq nat) (@eq (option A)) ==> @eq nat ==> @eq (option A)) first_value_below.
intros m1 m2 em x1 x2 ex; rewrite ex.
clear ex; clear x1.
induction x2; unfold first_value_below; fold (@first_value_below A).
apply em; reflexivity.
rewrite IHx2; destruct (first_value_below m2 x2).
reflexivity.
apply em; reflexivity.
Qed.


Lemma first_value_below_commute_constant {A B} x (f:A -> nat -> option B) n :
  first_value_below
    (fun n =>
       match first_value_below (fun _ => Some x) n with
         | Some y => f y n
         | None => None
       end) n
  = first_value_below (f x) n.
  induction n.
  reflexivity.
  unfold first_value_below; fold (@first_value_below A); fold (@first_value_below B).
  rewrite IHn.
  rewrite first_value_below_constant_fun.
  reflexivity.
Qed.

Lemma first_value_below_bind_None {A B} m f n :
  first_value_below m n = None ->
  first_value_below (@FixM2_bindM A B m f) n = None.
  induction n; intros.
  unfold first_value_below, FixM2_bindM; rewrite H; reflexivity.
  unfold first_value_below, FixM2_bindM; fold (@first_value_below B).
  rewrite H.
  unfold FixM2_bindM in IHn. rewrite IHn. reflexivity.
  unfold first_value_below in H; fold (@first_value_below A) in H.
  destruct (first_value_below m n); [ discriminate | reflexivity ].
Qed.

Lemma first_value_below_bind_Some {A B} x m f n :
  first_value_below m n = Some x ->
  first_value_below (@FixM2_bindM A B m f) n = first_value_below (f x) n.
  induction n; intros.
  unfold first_value_below, FixM2_bindM; rewrite H; reflexivity.
  unfold first_value_below, FixM2_bindM.
  fold (@first_value_below B).
  case_eq (first_value_below m n); intros.
  unfold FixM2_bindM in IHn.
  rewrite IHn. rewrite H.
  case_eq (first_value_below (f x) n); intros; [ reflexivity | ].
  unfold first_value_below; fold (@first_value_below B). rewrite H1. reflexivity.
  unfold first_value_below in H; fold (@first_value_below A) in H.
  rewrite H0 in H. rewrite H0. assumption.
  replace (first_value_below
             (fun n0 : nat =>
                match first_value_below m n0 with
                  | Some x0 => first_value_below (f x0) n0
                  | None => None
                end) n) with (@None B).
  rewrite H. reflexivity.
  fold (@FixM2_bindM A B m f); symmetry; apply first_value_below_bind_None; assumption.
Qed.

(* Extensionality law for == on FixM2 *)
Lemma FixM2_eqM_ext A (m1 m2: FixM2 A) :
  (forall x, value_is m1 x <-> value_is m2 x) -> m1 == m2.
  unfold eqM, leqM, FixM2_leqM, value_is; intro e; split; intros; destruct (e x).
  apply (H0 H).
  apply (H1 H).
Qed.

Lemma FixM2_eqM_ext2 A (m1 m2: FixM2 A) :
  (forall n, first_value_below m1 n = first_value_below m2 n) -> m1 == m2.
  unfold eqM, leqM, FixM2_leqM, value_is; intro e; split; intros;
  destruct H as [ n H ]; exists n.
  rewrite <- e; assumption.
  rewrite e; assumption.
Qed.

(*
Lemma FixM2_eqM_ext2 A (m1 m2: FixM2 A) :
  (forall x1 x2 n1 n2,
     first_value_below m1 n1 = Some x1 ->
     first_value_below m2 n2 = Some x2 -> x1 = x2) -> m1 == m2.
  unfold eqM, leqM, FixM2_leqM, value_is; intro H; split; intros x H0;
    destruct H0 as [ n H0 ].

intro e; split; intros; destruct (e x).
  apply (H0 H).
  apply (H1 H).
Qed.
*)

(* The Monad instance for FixM2 *)
Instance FixM2_Monad : Monad FixM2.
  constructor;
    unfold returnM, FixM2_returnM, bindM; intros;
  try (apply FixM2_eqM_ext2; intros).
  unfold FixM2_bindM; rewrite first_value_below_commute_constant;
  apply first_value_below_idempotent.
  unfold FixM2_bindM; rewrite <- (first_value_below_idempotent m).
  apply first_value_below_is_proper; [ | reflexivity ]; intros n1 n2 e; rewrite e.
  case_eq (first_value_below m n2); intros; [ | reflexivity ].
  apply first_value_below_constant_fun.

  case_eq (first_value_below m n); intros.
  rewrite (first_value_below_bind_Some _ _ _ _ H).
  case_eq (first_value_below (f a) n); intros.
  assert (first_value_below (FixM2_bindM A B m f) n = Some b).
  rewrite (first_value_below_bind_Some _ _ _ _ H); assumption.
  rewrite (first_value_below_bind_Some _ _ _ _ H0).
  rewrite (first_value_below_bind_Some _ _ _ _ H1).
  reflexivity.
  assert (first_value_below (FixM2_bindM A B m f) n = None).
  rewrite (first_value_below_bind_Some _ _ _ _ H); assumption.
  rewrite (first_value_below_bind_None _ _ _ H0).
  rewrite (first_value_below_bind_None _ _ _ H1).
  reflexivity.
  rewrite (first_value_below_bind_None _ _ _ H).
  assert (first_value_below (FixM2_bindM A B m f) n = None).
  apply (first_value_below_bind_None _ _ _ H).
  rewrite (first_value_below_bind_None _ _ _ H0).
  reflexivity.

  constructor.
  intros m x vis; assumption.
  intros m1 m2 m3 H1 H2 x vis. apply H2; apply H1; assumption.
  intros x y e z vis. rewrite <- e; assumption.

  intros m1 m2 leqm f1 f2 leqf y vis.
  destruct vis as [ n ].
  assert (exists x, first_value_below m1 n = Some x).
  case_eq (first_value_below m1 n); intros.
  exists a; reflexivity.
  rewrite (first_value_below_bind_None _ _ _ H0) in H; discriminate.
  destruct H0.
  destruct (leqm x (ex_intro _ n H0)) as [ n1 ].
  rewrite (first_value_below_bind_Some _ _ _ _ H0) in H.
  destruct (leqf x x eq_refl y (ex_intro _ n H)) as [ n2 ].
  exists (max n1 n2).
  rewrite (first_value_below_bind_Some x m2 f2).
  apply (first_value_below_stable _ n2); [ apply Nat.le_max_r | assumption ].
  apply (first_value_below_stable _ n1); [ apply Nat.le_max_l | assumption ].
Qed.
