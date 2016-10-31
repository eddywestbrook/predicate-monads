
(* Some attempts to build a fixed-point monad transformer *)

Require Import Coq.Program.Basics.
Require Export PredMonad.Monad.


(***
 *** The Fixed-point Monad Transformer
 ***)

Section FixT.
Context `{Monad}.

(* Build the type M (A + M (A + ... M (A + unit))) with depth n *)
Fixpoint nth_M_sum n A : Type :=
  match n with
    | 0 => unit
    | S n' => M (A + nth_M_sum n' A)
  end.

(* Replace the last M (A + unit) with unit, thereby going from nth_M_sum (S n) A
to nth_M_sum n A. *)
Fixpoint nth_M_sum_truncate {A} {n} :
  nth_M_sum (S n) A -> nth_M_sum n A :=
  match n return nth_M_sum (S n) A -> nth_M_sum n A with
    | 0 => fun _ => tt
    | S n' =>
      fun nMs =>
        bindM
          (A:=A + nth_M_sum (S n') A)
          nMs
          (fun sum =>
             match sum with
               | inl a => returnM (inl a)
               | inr nMs' =>
                 returnM (inr (nth_M_sum_truncate nMs'))
             end)
  end.

(* Distinguished equality on nth_M_sum *)
Fixpoint nth_M_sum_equals {A:Type} {EqOp:EqualsOp A} n :
  EqualsOp (nth_M_sum n A) :=
  match n return EqualsOp (nth_M_sum n A) with
    | 0 => fun _ _ => True
    | S n' =>
      equalsM (EqOp:=Sum_EqualsOp _ _ (EqOp_B:=nth_M_sum_equals n'))
  end.

Instance nth_M_sum_EqualsOp `{EqOp:EqualsOp} n :
  EqualsOp (nth_M_sum n A) := nth_M_sum_equals n.

Instance nth_M_sum_Equals `{Equals} n : Equals (nth_M_sum n A).
  induction n; repeat constructor;
    unfold equals, nth_M_sum_EqualsOp;
    unfold nth_M_sum_equals; fold nth_M_sum_equals; intro; intros.
  reflexivity.
  symmetry; assumption.
  transitivity y; assumption.
Qed.


(* Whether one computation is an extension of another *)
Definition nth_M_sum_extends {A} {n} (EqOp:EqualsOp A)
           (nMs1: nth_M_sum n A)
           (nMs2: nth_M_sum (S n) A) : Prop :=
  nMs1 == nth_M_sum_truncate nMs2.

(* FixT represents the infinite type M (A + M (A + ...)) as sequences of
elements of unit, M (A + unit), M (A + M (A + unit)), etc., such that each
element is an extension of the unit part of the computation before. Intuitively,
an A value at depth n represents termination after n steps, while
non-terminating computations always return unit values. *)
Definition FixT A :=
  { f: forall n, nth_M_sum n A |
    forall n, nth_M_sum_extends (Eq_EqualsOp A) (f n) (f (S n))}.


(* Helper assumptions for defining our monad operations *)
Context {A B:Type}.

Local Instance A_EqualsOp : EqualsOp A := Eq_EqualsOp A.
Local Instance A_Equals : Equals A := Eq_Equals A.
Local Instance B_EqualsOp : EqualsOp B := Eq_EqualsOp B.
Local Instance B_Equals : Equals B := Eq_Equals B.

(* Return gives a value in the very first A type *)
Program Definition FixT_returnM (x:A) : FixT A :=
  fun n =>
    match n with
      | 0 => tt
      | S _ => returnM (inl x)
    end.
Next Obligation.
unfold nth_M_sum_extends.
destruct n.
reflexivity.
unfold nth_M_sum_truncate.
rewrite monad_return_bind.
reflexivity.
auto with typeclass_instances.
auto with typeclass_instances.
Qed.

(* Bind... *)
Fixpoint nth_M_sum_bind n :
  nth_M_sum n A -> (A -> nth_M_sum n B) -> nth_M_sum n B :=
  match n return nth_M_sum n A -> (A -> nth_M_sum n B) -> nth_M_sum n B with
  | 0 => fun _ _ => tt
  | S n' =>
    fun m f =>
      bindM
        (A:=A + nth_M_sum n' A)
        m
        (fun sum =>
           match sum with
           | inl x => returnM (inr (nth_M_sum_truncate (f x)))
           | inr m' =>
             returnM (inr (nth_M_sum_bind n' m' (fun x => nth_M_sum_truncate (f x))))
           end)
  end.

Program Definition FixT_bindM (m: FixT A) (f: A -> FixT B) : FixT B :=
  fun n => nth_M_sum_bind n (m n) (fun x => f x n).
Next Obligation.
unfold nth_M_sum_extends.
destruct n.
reflexivity.
unfold nth_M_sum_bind; fold nth_M_sum_bind.

unfold nth_M_sum_truncate; repeat (fold (nth_M_sum_truncate (n:=n) (A:=B))).

FIXME HERE: old stuff below


(***
 *** A diagonalization function, to surjectively map nat -> nat*nat
 ***)

Section Diagonalization.

(* Diagonalize surjectively maps nat onto nat*nat *)
Definition diagonalize n : nat * nat :=
  (Nat.sqrt n - (n - (Nat.square (Nat.sqrt n))),
   (n - (Nat.square (Nat.sqrt n)))).

(* For any x and y, return the n such that diagonalize n = (x,y) *)
Definition undiagonalize x y : nat :=
  Nat.square (x + y) + y.

(* Proof that diagonalize and undiagonalize are correct *)
Lemma diagonalize_surjective x y :
  diagonalize (undiagonalize x y) = (x, y).
  unfold diagonalize, undiagonalize.
  assert (Nat.sqrt (Nat.square (x + y) + y) = x + y).
  apply Nat.sqrt_unique; split.
  unfold Nat.square; apply le_plus_l.
  unfold Nat.square. unfold lt.
  unfold mult; fold mult.
  assert (forall n m, S (n + m) = n + S m); [ intros; apply plus_Snm_nSm | ].
  repeat (rewrite H).
  repeat (first [ rewrite Nat.mul_add_distr_r | rewrite Nat.mul_add_distr_l ]).
  repeat (rewrite Nat.mul_succ_r).
  rewrite (plus_comm _ (S y)).
  rewrite (plus_comm x (S y)).
  rewrite <- (plus_assoc (S y)).
  apply plus_le_compat_l.
  rewrite (plus_comm x); apply le_plus_trans.
  repeat (rewrite <- plus_assoc).
  apply plus_le_compat_l. apply plus_le_compat_l.
  rewrite (plus_comm x); apply le_plus_trans.
  apply plus_le_compat_l.
  apply le_plus_trans.
  reflexivity.
  rewrite H.
  rewrite minus_plus.
  rewrite plus_comm; rewrite minus_plus.
  reflexivity.
Qed.

End Diagonalization.

(* Keep diagonalize opaque, because all that matters is the above lemma *)
Opaque diagonalize.


Section FixT.
Context `{Monad}.

(* approximation relation (FIXME: document this) *)
(* FIXME HERE: this doesn't work; see approx_under2, below, for a newer way... *)
Definition approx_under {A} : relation (M (option A)) :=
  fun m1 m2 =>
    exists (m': M (option A)),
      m2 == bindM m1 (fun sum =>
                        match sum with
                          | None => m'
                          | Some x => returnM (Some x)
                        end).

Instance approx_under_Reflexive {A} : Reflexive (approx_under (A:=A)).
intro m; exists (returnM None).
transitivity (bindM m returnM); [ symmetry; apply monad_bind_return | ].
apply monad_proper_bind; [ reflexivity | ].
intros x y xy_eq; rewrite xy_eq; destruct y; reflexivity.
Qed.

Instance approx_under_Transitive {A} : Transitive (approx_under (A:=A)).
intros m1 m2 m3 approx12 approx23.
destruct approx12 as [ m1' e_12 ].
destruct approx23 as [ m2' e_23 ].
exists (bindM m1' (fun sum => match sum with
                                | None => m2'
                                | Some x => returnM (Some x)
                              end)).
rewrite e_23; rewrite e_12.
rewrite <- monad_assoc.
apply bind_fun_eqM.
intro x; destruct x.
rewrite monad_return_bind; reflexivity.
apply bind_fun_eqM.
intro x; destruct x; reflexivity.
Qed.

(* Helper definition: bind on just the option part of FixT *)
(* FIXME HERE: need something like this, but generalized to nested trees of options... *)
Definition bindM_opt {A B} (m:M (option A)) (f:A -> M (option B)) : M (option (option B)) :=
  bindM m (fun o => match o with
                      | Some x =>
                        bindM (f x)
                              (fun o' => match o' with
                                           | Some y => returnM (Some (Some y))
                                           | None => returnM (Some None)
                                         end)
                      | None => returnM None
                    end).

(* FIXME HERE: this does not work (transitivity fails) *)
(* approximation relation (FIXME: document this) *)
(*
Definition approx_under2 {A} : relation (M (option A)) :=
  fun m1 m2 =>
    exists (T:Type) (mT: M T) (fT: T -> M (option A)),
      m2 == bindM mT fT
      /\
      m1 == bindM mT (fun _ => returnM None).
*)
(*
Inductive approx_under2 {A} (m1 m2 : M (option A)) : Prop :=
  MkApproxUnder2 (T:Type) (mT: M T) (fT: T -> M (option A)) :
    m2 == bindM mT fT ->
    m1 == bindM mT (fun _ => returnM None) ->
    approx_under2 m1 m2.

Instance approx_under2_Transitive {A} : Transitive (approx_under2 (A:=A)).
  intros m1 m2 m3 ap12 ap23.
  destruct ap12; destruct ap23.
  eapply (MkApproxUnder2
            _ _ ((T * M T0)%type)
            (bindM mT (fun t => returnM (t, mT0)))
            (fun t_mt0 =>
               bindM (fT (fst t_mt0))
                     (fun opt_A =>
                        match opt_A with
                          | 
bindM (snd t_mt0) fT0))).

  exists ((T * M T0)%type).
*)


(* In order for this to work, we need to know that the underlying bind is
monotonic w.r.t. approx_under *)
Lemma bindM_proper_approx_under {A B} :
  Proper (approx_under (A:=A) ==>
            ((@eq A) ==> (approx_under (A:=B))) ==>
            approx_under (A:=B)) bindM_opt.
  intros m1 m2 approx_m f1 f2 approx_f.
  transitivity (bindM_opt m2 f1).
  destruct approx_m as [m' e_m].
  unfold bindM_opt, approx_under.
  exists (bindM_opt m' f1).
  rewrite e_m.
  repeat (rewrite <- monad_assoc).
  apply bind_fun_eqM; intro x; destruct x.

  replace m2 with (bindM m1
          (fun sum : option A =>
           match sum with
           | Some x => returnM (Some x)
           | None => m'
           end)).
rewrite e_m.

m1 m2 (f: A -> M (option B)) :
  approx_under1 m1 m2 -> approx_under1 (bindM_opt m1 f) (bindM_opt m2 f).
  intro appr; destruct appr as [ m' ]; destruct H0.
  exists (bindM m' (fun sum =>
                      match sum with
                        | inl None => returnM (inl _ None)
                        | inl (Some x) =>
                          bindM (f x) (fun b => returnM (inl _ b))
                        | inr m' =>
                          returnM (inr _ (bindM_opt m' f))
                      end)).
  unfold bindM_opt; rewrite H0; rewrite H1.
  repeat (rewrite <- monad_assoc).
  split.
  apply bind_fun_eqM; intro sum; destruct sum; rewrite monad_return_bind.
  destruct o.
  rewrite <- monad_assoc.
  rewrite bind_fun_eqM.
  rewrite monad_bind_return; reflexivity.
  intro optB; repeat (rewrite monad_return_bind); reflexivity.
  rewrite monad_return_bind; reflexivity.
  rewrite monad_return_bind; reflexivity.
  apply bind_fun_eqM; intro sum; destruct sum.
  rewrite monad_return_bind; destruct o.
  rewrite <- monad_assoc.
  rewrite bind_fun_eqM; [ rewrite monad_bind_return; reflexivity | ].
  intro optB; destruct optB; rewrite monad_return_bind; reflexivity.
  rewrite monad_return_bind; reflexivity.
  rewrite monad_return_bind; reflexivity.
Qed.


(* FIXME: document this *)
Definition FixT (X:Type) :=
  {f:nat -> M (option X) |
   forall n1 n2, n1 < n2 -> approx_under (f n1) (f n2)}.


End FixT.


(* FIXME HERE NOW: old stuff below... *)

Section FixT.
Context `{Monad}.

(* One step of the approximation order for underlying computations: computation
m1 approximates m2 iff there is some way to split m2 into "now" and "later"
parts -- returning an option A is "now" and returning an M (option A) is "later"
-- such that m1 only does the "now" parts. *)
Definition approx_under1 {A} : relation (M (option A)) :=
  fun m1 m2 =>
    exists (m: M (option A + M (option A))),
      m1 == bindM m (fun sum =>
                       match sum with
                         | inl x => returnM x
                         | inr m' => returnM None
                       end) /\
      m2 == bindM m (fun sum =>
                       match sum with
                         | inl x => returnM x
                         | inr m' => m'
                       end).

(* approx_under is then the reflexive-transitive closure of approx_under1 *)
Definition approx_under {A} : relation (M (option A)) :=
  clos_refl_trans _ (approx_under1 (A:=A)).

Global Instance approx_under_Reflexive {A} : Reflexive (approx_under (A:=A)).
apply clos_rt_is_preorder.
Qed.

Global Instance approx_under_Transitive {A} : Transitive (approx_under (A:=A)).
apply clos_rt_is_preorder.
Qed.

(* A fixed-point computation is a countable directed set of underlying
computations, meaning that any two computations in the set have a supremum
(w.r.t. approx_under) also in the set *)
Definition FixT (X:Type) :=
  {f:nat -> M (option X) |
   forall n1 n2, exists n',
     approx_under (f n1) (f n') /\ approx_under (f n2) (f n')}.

(* Helper definition: bind on just the option part of FixT *)
Definition bindM_opt {A B} (m:M (option A)) (f:A -> M (option B)) : M (option B) :=
  bindM m (fun o => match o with
                      | Some x => f x
                      | None => returnM None
                    end).

(* In order for this to work, we need to know that the underlying bind is
monotonic w.r.t. approx_under *)
Lemma bindM_proper_approx_under1 {A B} m1 m2 (f: A -> M (option B)) :
  approx_under1 m1 m2 -> approx_under1 (bindM_opt m1 f) (bindM_opt m2 f).
  intro appr; destruct appr as [ m' ]; destruct H0.
  exists (bindM m' (fun sum =>
                      match sum with
                        | inl None => returnM (inl _ None)
                        | inl (Some x) =>
                          bindM (f x) (fun b => returnM (inl _ b))
                        | inr m' =>
                          returnM (inr _ (bindM_opt m' f))
                      end)).
  unfold bindM_opt; rewrite H0; rewrite H1.
  repeat (rewrite <- monad_assoc).
  split.
  apply bind_fun_eqM; intro sum; destruct sum; rewrite monad_return_bind.
  destruct o.
  rewrite <- monad_assoc.
  rewrite bind_fun_eqM.
  rewrite monad_bind_return; reflexivity.
  intro optB; repeat (rewrite monad_return_bind); reflexivity.
  rewrite monad_return_bind; reflexivity.
  rewrite monad_return_bind; reflexivity.
  apply bind_fun_eqM; intro sum; destruct sum.
  rewrite monad_return_bind; destruct o.
  rewrite <- monad_assoc.
  rewrite bind_fun_eqM; [ rewrite monad_bind_return; reflexivity | ].
  intro optB; destruct optB; rewrite monad_return_bind; reflexivity.
  rewrite monad_return_bind; reflexivity.
  rewrite monad_return_bind; reflexivity.
Qed.

(* Return for FixT: build the set of computations that return x in the
underlying monad; i.e., return (Some x) for all nat inputs *)
Program Instance FixT_MonadRet : MonadRet FixT :=
  fun {X} x _ => returnM (Some x).
Next Obligation.
  exists 0; split; reflexivity.
Qed.

(* Bind for FixT: build the set that includes bindM (m n1) (fun x => f x n2) for
all n1 and n2, by diagonalize, above *)
Program Instance FixT_MonadBind : MonadBind FixT :=
  fun {A B} m f =>
    fun n =>
      bindM_opt
        (m (fst (diagonalize n)))
           (fun x => f x (snd (diagonalize n))).
Next Obligation.
destruct (proj2_sig m n1 n2) as [n_m H_n_m];
  destruct H_n_m as [approx_m1 approx_m2].

(* FIXME HERE NOW: the above doesn't work, because there might not be one single
n' that works for all input values of f in the bind... *)

Class MonadBind (M:Type -> Type) : Type :=
  bindM : forall {A B:Type}, M A -> (A -> M B) -> M B.

Class MonadEquiv (M:Type -> Type) : Type :=
  eqM : forall {A:Type}, M A -> M A -> Prop.


(* FIXME HERE NOW: finish FixT and its operations! *)

End FixT.



(***
 *** A Non-Termination Monad Transformer via Non-Determinism + Errors
 ***)

Section FixT2.

(* We model non-termination with the more general construction of a
non-determinism transformer + option transformer, where each computation has a
countably infinite non-deterministic choice, and can also return no value. The
choice is used to represent different "amounts" of computation, and returning no
value is used to represent non-termination. *)
Definition FixT2 (X:Type) := nat -> M (option X).

(* For return, we build the set of computations that always return x *)
Instance FixT2_returnM : MonadRet FixT2 :=
  fun {A} x => fun _ => returnM (Some x).

(* For bind, we diagonalize over all possible computations for m and f *)
Instance FixT2_bindM : MonadBind FixT2 :=
  fun {A B} m f =>
    fun n => bindM (m (fst (diagonalize n)))
                   (fun opt_x =>
                      match opt_x with
                        | Some x => f x (snd (diagonalize n))
                        | None => returnM None
                      end).

(* Approximation order: each computation in one set, other than the trivial None
computation, also occurs in the other. Excluding the trivial computation allows
our sets to be "empty". *)
Instance FixT2_approxM : MonadApprox FixT2 :=
  fun {A} m1 m2 =>
    forall n, m1 n == returnM None \/ exists n', m1 n == m2 n'.

(* Equivlence: two computations approximate each other *)
Instance FixT2_eqM : MonadEquiv FixT2 :=
  fun {A} => inter_sym approxM.

Definition FixT2_bottomM {A} : FixT2 A :=
  fun _ => returnM None.

(* Building a fixed-point: consider all possible numbers of iterations of f to
the bottom function, and all possible elements of the resulting set *)
Instance FixT2_fixM : MonadFixM FixT2 :=
  fun {A B} f x n =>
    iterate_f
      (fst (diagonalize n)) f (fun _ => FixT2_bottomM)
      x (snd (diagonalize n)).


(* FIXME HERE NOW *)

End FixT2.



(* FIXME HERE: yet another idea for FixT, using the resumption transformer *)
Section FixT3.
Context `{Monad}.

Inductive Ord : Type :=
| Ord0 : Ord
| OrdS (o:Ord) : Ord
| OrdLimit (f:nat -> Ord) : Ord
.

Inductive Resumption (F: Ord -> Type) A : Ord -> Type :=
| Res_Done ord (a:A) : Resumption F A ord
| Res_NonTerm : Resumption F A Ord0
| Res_Step ords (m:M {n:nat & F (ords n)}) : Resumption F A (OrdLimit ords).

End FixT3.


(*** FIXME: old stuff below! ***)

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

Instance FixM_leqM : MonadEquiv FixM :=
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





(* The MonadFix instances for FixM *)

Definition FixM_Bottom {A} : FixM A :=
  exist (fun P => forall x y, P x /\ P y -> x = y)
        (fun x => False)
        (fun x y (H: False /\ False) => match proj1 H with end).

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

(* Whether the first non-None value of a FixM2 computation is x *)
Inductive IsValueBelow {A} (m:FixM2 A) (x:A) : nat -> Prop :=
| IsVB_Base n (e: m n = Some x) :
    (forall n', n' < n -> m n' = None) ->
    IsValueBelow m x n
| IsVB_Cons n : IsValueBelow m x n -> IsValueBelow m x (S n)
.

(* The proposition that a FixM2 computation has value x for some n *)
Definition IsValue {A} (m:FixM2 A) (x:A) : Prop :=
  exists n, IsValueBelow m x n.

(* The proposition that there are no values of m at or below n *)
Definition NoValueBelow {A} (m:FixM2 A) n : Prop :=
  forall n', n' <= n -> m n' = None.

(* IsValueBelow and NoValueBelow are mutually contradictor *)
Lemma IsValueBelow_NoValueBelow_false {A} (m:FixM2 A) n x :
  IsValueBelow m x n -> NoValueBelow m n -> False.
  unfold NoValueBelow; intro isvb; induction isvb; intro novb.
  rewrite novb in e; [ discriminate | apply le_n ].
  apply IHisvb. intros. apply novb.
  transitivity n; [ assumption | apply le_S; apply le_n ].
Qed.

(* IsValueBelow is a functor from <= *)
Lemma IsValueBelow_leq {A} (m:FixM2 A) x n n' :
  n <= n' -> IsValueBelow m x n -> IsValueBelow m x n'.
  intro leq; induction leq; intro H.
  assumption.
  apply IsVB_Cons; apply IHleq; assumption.
Qed.

Lemma IsValueBelow_inversion {A} (m:FixM2 A) x n :
  IsValueBelow m x n ->
  exists n', n' <= n /\ m n' = Some x /\ (forall n'', n'' < n' -> m n'' = None).
  intro isvb; induction isvb.
  exists n; split; [ apply le_n | split; [ assumption | ] ].
  intros n' l; apply H; assumption.
  destruct IHisvb as [ n' H ]; destruct H; destruct H0.
  exists n'; split; [ apply le_S; assumption | split; [ assumption | ]].
  intros; apply H1; assumption.
Qed.

(* A computation can only have one value below n *)
Lemma IsValueBelow_functional {A} (m:FixM2 A) n x1 x2 :
  IsValueBelow m x1 n -> IsValueBelow m x2 n -> x1 = x2.
  intro isvb1; induction isvb1; intro isvb2; inversion isvb2.
  assert (Some x1 = Some x2) as e_some;
    [ rewrite <- e; rewrite <- e0; reflexivity
    | injection e_some; intros; assumption ].
  destruct (IsValueBelow_inversion _ _ _ H0) as [ n' H2 ];
    destruct H2; destruct H3.
  rewrite H in H3; [ discriminate | ].
  apply (le_lt_trans _ n0); [ assumption | rewrite <- H1; apply le_n ].
  destruct (IsValueBelow_inversion _ _ _ isvb1) as [ n' H2 ];
    destruct H2; destruct H2.
  rewrite H in H2; [ discriminate | ].
  apply le_n_S; assumption.
  apply IHisvb1; assumption.
Qed.

(* IsValueBelow is decidable *)
Program Fixpoint IsValueBelow_dec {A} m n :
  {x:A | IsValueBelow m x n} + {NoValueBelow m n} :=
  match n with
    | 0 =>
      match m 0 with
        | Some x => inleft x
        | None => inright _
      end
    | S n' =>
      match IsValueBelow_dec m n' with
        | inleft x => inleft x
        | inright _ =>
          match m (S n') with
            | Some x => inleft x
            | None => inright _
          end
      end
  end.
Next Obligation.
apply IsVB_Base.
symmetry; assumption.
intros n' H; inversion H.
Qed.
Next Obligation.
intros n l; inversion l; symmetry; assumption.
Qed.
Next Obligation.
apply IsVB_Cons; assumption.
Defined.
Next Obligation.
apply IsVB_Base; [ symmetry; assumption | ].
intros n l; apply (n0 n).
apply le_S_n; assumption.
Defined.
Next Obligation.
intros n l; inversion l.
symmetry; assumption.
apply (n0 n); assumption.
Defined.

Lemma IsValueBelow_smaller {A} (m:FixM2 A) n n' x :
  n' <= n -> IsValueBelow m x n ->
  IsValueBelow m x n' \/ NoValueBelow m n'.
  intro l; induction l; intros.
  left; assumption.
  destruct (IsValueBelow_dec m m0). destruct s.
  assert (x0 = x).
  apply (IsValueBelow_functional m (S m0)); [ | assumption ].
  apply (IsValueBelow_leq _ _ m0); [ repeat constructor | assumption ].
  rewrite H0 in i; apply IHl; assumption.
  right. intros n'' l'; apply n; transitivity n'; assumption.
Qed.

(* Get the first value of m at or below n *)
Definition first_value_below {A} (m:FixM2 A) n : option A :=
  match IsValueBelow_dec m n with
    | inleft (exist _ x _) => Some x
    | inright _ => None
  end.

Lemma first_value_below_Some {A} (m:FixM2 A) n x :
  IsValueBelow m x n <-> first_value_below m n = Some x.
  split.
  intro isvb; unfold first_value_below; destruct (IsValueBelow_dec m n).
  destruct s as [ y H ]; unfold proj1_sig.
  f_equal; apply (IsValueBelow_functional _ _ _ _ H isvb).
  elimtype False;
    apply (IsValueBelow_NoValueBelow_false _ _ _ isvb n0).
  unfold first_value_below; destruct (IsValueBelow_dec m n).
  destruct s as [ y H ]; unfold proj1_sig; intro e;
    injection e; intro e2; rewrite <- e2; assumption.
  intro; discriminate.
Qed.

Lemma first_value_below_None {A} (m:FixM2 A) n :
  NoValueBelow m n <-> first_value_below m n = None.
  split.
  intro novb; unfold first_value_below; destruct (IsValueBelow_dec m n).
  destruct s as [ x H ]; elimtype False;
    apply (IsValueBelow_NoValueBelow_false _ _ _ H novb).
  reflexivity.
  unfold first_value_below; destruct (IsValueBelow_dec m n).
  destruct s as [ x H ]; intro; discriminate.
  intros; assumption.
Qed.

(* An alternate definition of first_value_below *)
Fixpoint first_value_below_alt {A} (m:FixM2 A) n : option A :=
  match n with
    | 0 => m 0
    | S n' =>
      match first_value_below_alt m n' with
        | Some x => Some x
        | None => m (S n')
      end
  end.

Lemma first_value_below_alt_correct {A} (m:FixM2 A) n :
  first_value_below m n = first_value_below_alt m n.
  induction n.
  unfold first_value_below, first_value_below_alt.
  destruct (IsValueBelow_dec m 0).
  destruct s. inversion i. symmetry; assumption.
  symmetry; apply n; apply le_n.
  unfold first_value_below_alt; fold (@first_value_below_alt A).
  rewrite <- IHn.
  destruct (IsValueBelow_dec m (S n)).
  destruct s.
  rewrite (proj1 (first_value_below_Some _ _ _) i).
  inversion i.
  rewrite (proj1 (first_value_below_None m n)).
  symmetry; assumption.
  intros n' l; apply H; apply le_n_S; assumption.
  rewrite (proj1 (first_value_below_Some _ _ _) H0).
  reflexivity.
  rewrite (proj1 (first_value_below_None _ _) n0).
  rewrite (proj1 (first_value_below_None m n)).
  symmetry; apply n0; reflexivity.
  intros n' l; apply n0; apply le_S; assumption.
Qed.


(* The return for FixM2: just return x, ignoring n *)
Instance FixM2_returnM : MonadRet FixM2 :=
  fun {A} x => fun n => Some x.

(* For bind, we must be sure we always use the value of m for the least n that
it accepts, even if (f x) takes a much greater value of n, and vice-versa *)
Instance FixM2_bindM : MonadBind FixM2 :=
  fun {A B} m f =>
    fun n =>
      match first_value_below m n with
        | None => None
        | Some x => first_value_below (f x) n
      end.

Instance FixM2_leqM : MonadEquiv FixM2 :=
  fun {A} m1 m2 => forall x, IsValue m1 x -> IsValue m2 x.

Lemma first_value_below_bindM {A B} m f n :
  first_value_below (@FixM2_bindM A B m f) n =
  (match first_value_below m n with
     | Some x => first_value_below (f x) n
     | None => None
   end).
  (* unfold first_value_below, FixM2_bindM. *)
  destruct (IsValueBelow_dec m n).
  destruct s.
  rewrite (proj1 (first_value_below_Some _ _ _) i).
  destruct (IsValueBelow_dec (f x) n).
  destruct s.
  rewrite (proj1 (first_value_below_Some _ _ _) i0).
  unfold FixM2_bindM.
  apply first_value_below_Some.
  destruct (IsValueBelow_inversion _ _ _ i) as [ n1 ];
    destruct H; destruct H0.
  destruct (IsValueBelow_inversion _ _ _ i0) as [ n2 ];
    destruct H2; destruct H3.
  apply (IsValueBelow_leq _ _ (max n1 n2)); [ apply Nat.max_case; assumption | ].
  apply IsVB_Base.
  rewrite (proj1 (first_value_below_Some m _ x)).
  apply first_value_below_Some.
  apply (IsValueBelow_leq _ _ n2); [ apply Nat.le_max_r | ].
  apply IsVB_Base; assumption.
  apply (IsValueBelow_leq _ _ n1); [ apply Nat.le_max_l | ].
  apply IsVB_Base; assumption.
  intros.
  destruct (Nat.max_dec n1 n2); rewrite e in H5.
  rewrite (proj1 (first_value_below_None _ _)); [ reflexivity | ].
  intros n'' l; apply H1. apply (le_lt_trans _ _ _ l H5).
  destruct (IsValueBelow_dec m n').
  destruct s.
  rewrite (proj1 (first_value_below_Some _ _ _) i1).
  apply first_value_below_None.
  rewrite (IsValueBelow_functional m n x1 x); [ | | assumption ].
  intros n'' l; apply H4. apply (le_lt_trans _ _ _ l H5).
  apply (IsValueBelow_leq _ _ n'); [ | assumption ].
  apply le_S_n. apply le_S. transitivity n2; assumption.
  rewrite (proj1 (first_value_below_None m n') n0); reflexivity.
  unfold FixM2_bindM.
  rewrite (proj1 (first_value_below_None _ _) n0).
  apply first_value_below_None.
  intros n' l.
  destruct (IsValueBelow_smaller _ _ _ _ l i).
  rewrite (proj1 (first_value_below_Some _ _ _) H).
  apply first_value_below_None.
  intros n'' l'; apply n0; transitivity n'; assumption.
  rewrite (proj1 (first_value_below_None _ _) H); reflexivity.
  rewrite (proj1 (first_value_below_None _ _) n0).
  unfold FixM2_bindM.
  apply first_value_below_None.
  intros n' l.
  rewrite (proj1 (first_value_below_None m n')); [ reflexivity | ].
  intros n'' l''; apply n0; transitivity n'; assumption.
Qed.


(* Helper for proving FixM2_eqM *)
Lemma FixM2_eqM_helper A (m1 m2: FixM2 A) :
  (forall n, first_value_below m1 n = first_value_below m2 n) -> m1 == m2.
  unfold eqM, leqM, FixM2_leqM, IsValue; intro e; split;
    intros; destruct H as [ n H ]; exists n.
  rewrite first_value_below_Some; rewrite <- e;
    apply first_value_below_Some; assumption.
  rewrite first_value_below_Some; rewrite e;
    apply first_value_below_Some; assumption.
Qed.


(* The Monad instance for FixM2 *)
Instance FixM2_Monad : Monad FixM2.
  constructor;
    unfold returnM, FixM2_returnM, bindM; intros;
  try (apply FixM2_eqM_helper; intros).

  rewrite first_value_below_bindM.
  rewrite (proj1 (first_value_below_Some (fun _ : nat => Some x) n x));
    [ reflexivity | ].
  apply (IsValueBelow_leq _ _ 0); [ apply le_0_n | ].
  apply IsVB_Base; [ reflexivity | ].
  intros n' l; inversion l.

  rewrite first_value_below_bindM.
  destruct (first_value_below m n); [ | reflexivity ].
  apply first_value_below_Some.
  apply (IsValueBelow_leq _ _ 0); [ apply le_0_n | ].
  apply IsVB_Base; [ reflexivity | ].
  intros n' l; inversion l.

  repeat (rewrite first_value_below_bindM).
  destruct (first_value_below m n); [ | reflexivity ].
  rewrite first_value_below_bindM.
  reflexivity.

  constructor.
  intros m x vis; assumption.
  intros m1 m2 m3 H1 H2 x vis. apply H2; apply H1; assumption.
  intros x y e z vis. rewrite <- e; assumption.

  intros m1 m2 leqm f1 f2 leqf y vis.
  unfold IsValue.
  destruct vis as [ n ].
  assert (first_value_below (FixM2_bindM A B m1 f1) n = Some y).
  apply first_value_below_Some; assumption.
  rewrite first_value_below_bindM in H0.
  case_eq (first_value_below m1 n);
    intros; rewrite H1 in H0; [ | discriminate ].
  rewrite <- first_value_below_Some in H1.
  destruct (leqm _ (ex_intro _ n H1)) as [ nm ].
  rewrite <- first_value_below_Some in H0.
  destruct (leqf a a eq_refl y (ex_intro _ n H0)) as [ nf ].
  exists (max nm nf).
  rewrite first_value_below_Some.
  rewrite first_value_below_bindM.
  rewrite (proj1 (first_value_below_Some m2 _ a)).
  apply first_value_below_Some.
  apply (IsValueBelow_leq _ _ nf); [ apply Nat.le_max_r | assumption ].
  apply (IsValueBelow_leq _ _ nm); [ apply Nat.le_max_l | assumption ].
Qed.


(*** The MonadFix instance for FixM2 ***)

(* The least element of FixM2 w.r.t. leqM *)
Definition FixM2_Bottom {A} : FixM2 A :=
  fun n => None.

(* Bottom is in fact least *)
Lemma FixM2_Bottom_least {A} (m:FixM2 A) :
  leqM FixM2_Bottom m.
  intros x isv; destruct isv. rewrite first_value_below_Some in H.
  rewrite (proj1 (first_value_below_None _ _)) in H; [ discriminate | ].
  intros n l. reflexivity.
Qed.

(* For fixM, we must use the value of the fixed-point of f for the least n, even
if it takes some n' <> n steps of iteration of f to reach that fixed-point. *)
Instance FixM2_fixM : MonadFixM FixM2 :=
  fun {A B} f =>
    fun a n => first_value_below (iterate_f n f (fun _ => FixM2_Bottom) a) n.

Instance FixM2_MonadFix : MonadFix FixM2.
  constructor.
  auto with typeclass_instances.
  intros.
  unfold fixM; unfold FixM2_fixM.
  apply FixM2_eqM_helper; intros.
