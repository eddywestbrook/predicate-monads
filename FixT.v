
(* Some attempts to build a fixed-point monad transformer *)

Load Monad.
Load CPO.

(***
 *** A Non-Termination Monad Transformer via Non-Determinism + Errors
 ***)

Section FixT.

Context `{Monad}.

Definition diagonalize n : nat * nat :=
  (Nat.sqrt n - (n - (Nat.square (Nat.sqrt n))),
   (n - (Nat.square (Nat.sqrt n)))).

Definition undiagonalize x y : nat :=
  Nat.square (x + y) + y.

Lemma diagonalize_surjective x y :
  diagonalize (undiagonalize x y) = (x, y).
  unfold diagonalize, undiagonalize.
  assert (Nat.sqrt (Nat.square (x + y) + y) = x + y).
  apply Nat.sqrt_unique; split.
  unfold Nat.square; apply le_plus_l.
  unfold Nat.square. unfold lt.
  unfold mult; fold mult.
  assert (forall n m, S (n + m) = n + S m); [ intros; apply plus_Snm_nSm | ].
  repeat (rewrite H0).
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
  rewrite H0.
  rewrite minus_plus.
  rewrite plus_comm; rewrite minus_plus.
  reflexivity.
Qed.


(* We model non-termination with the more general construction of a
non-determinism transformer + option transformer, where each computation has a
countably infinite non-deterministic choice, and can also return no value. The
choice is used to represent different "amounts" of computation, and returning no
value is used to represent non-termination. *)
Definition FixT (X:Type) := nat -> M (option X).

(* For return, we build the set of computations that always return x *)
Instance FixT_returnM : MonadRet FixT :=
  fun {A} x => fun _ => returnM (Some x).

(* For bind, we diagonalize over all possible computations for m and f *)
Instance FixT_bindM : MonadBind FixT :=
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
Instance FixT_approxM : MonadApprox FixT :=
  fun {A} m1 m2 =>
    forall n, m1 n == returnM None \/ exists n', m1 n == m2 n'.

(* Equivlence: two computations approximate each other *)
Instance FixT_eqM : MonadEquiv FixT :=
  fun {A} => inter_sym approxM.

Definition FixT_bottomM {A} : FixT A :=
  fun _ => returnM None.

(* Building a fixed-point: consider all possible numbers of iterations of f to
the bottom function, and all possible elements of the resulting set *)
Instance FixT_fixM : MonadFixM FixT :=
  fun {A B} f x n =>
    iterate_f
      (fst (diagonalize n)) f (fun _ => FixT_bottomM)
      x (snd (diagonalize n)).


(* FIXME HERE NOW *)

End FixT.


(* FIXME HERE: another idea for FixT *)
Section FixT2.
Context `{Monad}.

(* One step of the approximation order for underlying computations: computation
m1 approximates m2 iff m1 is the result of replacing some monadic function in m2
with the bottom function (which represents a function that never terminates) *)
Definition approx_under1 {A} : relation (M (option A)) :=
  fun m1 m2 =>
    exists B C (mf : (B -> M (option C)) -> M (option A)) f,
      m1 == mf (fun _ => returnM None) /\ m2 == mf f.

Definition approx_under {A} : relation (M (option A)) :=
  clos_refl_trans _ (approx_under1 (A:=A)).

(* NOTE: the following doesn't work, because we may need uncountably many Ms *)
(*
Definition approx_under' {A} : relation (M (option A)) :=
  fun m1 m2 =>
    exists (Ts: nat -> Type) (C: (forall n, M (option (Ts n))) -> M (option A))
           (Ms: forall n, M (option (Ts n))),
      m1 == C (fun n => returnM None) /\ m2 == C Ms.
*)

(* A fixed-point computation is a chain of underlying computations that get more
and more precise *)
Definition FixT2 (X:Type) :=
  {f:nat -> M (option X) | forall n, approx_under (f n) (f (S n))}.


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
