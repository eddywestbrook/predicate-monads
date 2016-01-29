
Require Import Coq.Program.Tactics.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Arith.Arith_base.

Load CPO.


(***
 *** The monad typeclass (unbundled approach)
 ***)

Class MonadRet (M:Type -> Type) : Type :=
  returnM : forall {A:Type}, A -> M A.

Class MonadBind (M:Type -> Type) : Type :=
  bindM : forall {A B:Type}, M A -> (A -> M B) -> M B.

Class MonadOrder (M:Type -> Type) : Type :=
  approxM : forall {A} {_:DomainOrder A}, DomainOrder (M A).

Instance MonadOrder_DomainOrder `{MonadOrder} `{DomainOrder} : DomainOrder (M A) :=
  approxM.

Class Monad M {MonadRet:MonadRet M} {MonadBind:MonadBind M}
      {MonadOrder:MonadOrder M} : Prop :=
  {
    monad_domain :> forall `{Domain}, @Domain (M A) approxM;
    monad_return_bind :
      forall {A B} `{_:Domain A} `{_:Domain B} x (f:A -> M B),
        bindM (returnM x) f == f x;
    monad_bind_return :
      forall {A} `{_:Domain A} (m:M A), bindM m returnM == m;
    monad_assoc :
      forall {A B C} `{_:Domain A} `{_:Domain B} `{_:Domain C}
             (m:M A) (f: A -> M B) (g: B -> M C),
        bindM m (fun x => bindM (f x) g) == bindM (bindM m f) g;
    monad_proper_return :> forall `{Domain}, Proper (approx ==> approx) returnM;
    monad_proper_bind :>
      forall {A B} `{_:Domain A} `{_:Domain B},
        Proper (approx (A:=M A) ==> (approx (A:=A) ==> approx (A:=M B)) ==> approx (A:=M B)) bindM
  }.


(***
 *** Stuff needed for rewriting computations w.r.t. approx and approxEq
 ***)

Instance proper_approx_approxM `{Monad} `{Domain} :
  Proper (approxEq (A:=M A) ==> approxEq (A:=M A) ==> iff) (approx (A:=M A)).
  intros x1 y1 eq1 x2 y2 eq2; destruct eq1; destruct eq2; split; intro.
  transitivity x1; [ assumption | ]; transitivity x2; assumption.
  transitivity y1; [ assumption | ]; transitivity y2; assumption.
Qed.

Instance monad_proper_return_approxEq `{Monad} `{Domain} :
  Proper (approxEq ==> approxEq) returnM.
  intros x y e; destruct e; split; apply monad_proper_return; assumption.
Qed.

(* Approximate equality for functions *)
Definition approxEqFun {A} {DomainOrderA:DomainOrder A}
           {B} {DomainOrderB:DomainOrder B} (f1 f2 : A -> B) :=
  forall x y (leq:approx x y),
    approx (f1 x) (f2 y) /\ approx (f2 x) (f1 y).

Instance monad_proper_bind_eqM `{Monad} `{Domain} {B} `{Domain B} :
  Proper (approxEq (A:=M A) ==> approxEqFun ==> approxEq (A:=M B)) bindM.
  intros m1 m2 eqm f1 f2 eqf. destruct eqm.
  split;
    (apply monad_proper_bind; [ assumption | ]; intros x1 x2 e;
     destruct (eqf x1 x2 e); assumption).
Qed.


(***
 *** The Identity Monad
 ***)

Definition Identity (X:Type) := X.
Instance IdMonad_returnM : MonadRet Identity := fun A x => x.
Instance IdMonad_bindM : MonadBind Identity := fun A B m f => f m.
Instance IdMonad_approxM : MonadOrder Identity :=
  fun {A} {ord:DomainOrder A} => ord.
Instance IdMonad : Monad Identity.
  constructor; intros; try reflexivity.
  split; auto with typeclass_instances.
  intros x y leq; assumption.
  intros m1 m2 leqm f1 f2 leqf.
  apply leqf. assumption.
Qed.


(***
 *** The State Monad
 ***)

Section StateT.

Context `{Monad} {S} `{SDomain:Domain S}.

(* StateT itself *)
Definition StateT (S:Type) (M: Type -> Type) (X:Type) := S -> M (prod S X).

Instance StateT_returnM {S} : MonadRet (StateT S M) :=
  fun A x => fun s => returnM (s, x).
Instance StateT_bindM {S} : MonadBind (StateT S M) :=
  fun A B m f =>
    fun s => bindM (m s) (fun (sx:S * A) => let (s',x) := sx in f x s').
Instance StateT_approxM : MonadOrder (StateT S M) :=
  fun {A ord} m1 m2 => forall s, approx (m1 s) (m2 s).

(* Extensionality law for == on StateT *)
Lemma StateT_eqM_ext `{Domain} (m1 m2: StateT S M A) :
  (forall s, m1 s == m2 s) -> m1 == m2.
  unfold approxM, StateT_approxM; intro e; split; intros s;
    destruct (e s); assumption.
Qed.

(* The Monad instance for StateT *)
Instance StateT_Monad : Monad (StateT S M).
  constructor;
    unfold returnM, StateT_returnM, bindM, StateT_bindM;
    intros; try (apply StateT_eqM_ext); intros.
  split; split; intro; intros; intro; intros.
  reflexivity.
  transitivity (y s); [ apply H1 | apply H2 ].
  rewrite monad_return_bind; reflexivity.
  transitivity (bindM (m s) returnM); [ | apply monad_bind_return ].
  apply monad_proper_bind_eqM; [ reflexivity | ].
  intros sx sy e; destruct sx; destruct sy; split; rewrite e; reflexivity.
  rewrite <- monad_assoc.

(* FIXME HERE NOW: Cannot prove associativity, because we do not know that f
respects either of its input domains! *)

  apply monad_proper_bind_eqM; [ reflexivity | ].
  intros sx sy e; destruct sx; destruct sy; split.

 rewrite e; destruct sy; reflexivity.
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

Instance StateT_getM {S} `{MonadRet} : MonadGet S (StateT S M) :=
  fun s => returnM (s, s).
Instance StateT_putM {S} `{MonadRet} : MonadPut S (StateT S M) :=
  fun s_new s => returnM (s_new, tt).

Instance StateT_MonadState S `{Monad} : MonadState S (StateT S M).
  constructor; intros; try apply StateT_Monad;
    unfold returnM, StateT_returnM, bindM, StateT_bindM,
           getM, StateT_getM, putM, StateT_putM; intros;
    try (apply StateT_eqM_ext; intros;
         repeat (rewrite monad_return_bind); reflexivity).
  assumption.
  intros s1 s2 e s; rewrite e; reflexivity.
Qed.


(***
 *** The Least Fixed-Point / Non-Termination Monad Transformer
 ***)

Section FixT.

Context `{Monad}.

(* A FixT M computation is a chain of M computations where each M computation in
the chain might do more work than the previous one, if the previous one has not
yet terminated, where non-termination is represented by returning None. *)
Definition FixT (X:Type) :=
  {m:nat -> M (option X) |
   forall n,
     exists m', eqM (m (S n))
                    (bindM (m n)
                           (fun opt =>
                              match opt with
                                | Some x => returnM (Some x)
                                | None => m'
                              end))}.

(* For return, we build the chain of computations that always return x *)
Program Instance FixT_returnM : MonadRet FixT :=
  fun {A} x => fun _ => returnM (Some x).
Obligation 1.
exists (returnM None).
rewrite monad_return_bind.
reflexivity.
Qed.

(* For bind, each element of the chain binds the corresponding elements of the
chains of m and f *)
Program Instance FixT_bindM : MonadBind FixT :=
  fun {A B} m f =>
    fun n => bindM (m n)
                   (fun opt_x =>
                      match opt_x with
                        | Some x => f x n
                        | None => returnM None
                      end).
Obligation 1.
destruct (proj2_sig m n) as [ m' H0 ].
(* FIXME HERE: the m' we need could depend on x, the return value for m! *)

rewrite H0.


Definition FixT_bottomM `{MonadRet} {A} : FixT M A :=
  fun _ => returnM None.

(* Iterate m until either it returns a Some value or n runs out *)
Fixpoint normalize_below {M} {MonadRet:MonadRet M}
         {MonadBind:MonadBind M} {A} (m: FixT M A) n : M (option A) :=
  match n with
    | 0 => m 0
    | S n' => bindM (normalize_below m n')
                    (fun opt_x =>
                       match opt_x with
                         | Some x => returnM (Some x)
                         | None => m (S n')
                       end)
  end.

(* FIXME HERE: This is not right! it should say something about the traces!
Also, the formulation of the case where m1 is "less terminating" than m2 seems
incorrect... *)

(* The order on fixed-point computations: either m1 and m2 are equivalent, or m1
returns a None (so m1 is equivalent to (m2 >> return None)) *)
Instance FixT_leqM {M} {_:MonadRet M} {_:MonadBind M} {_:MonadOrder M} :
  MonadOrder (FixT M) :=
  fun {A} m1 m2 =>
    exists n,
      leqM (normalize_below m1 n) (normalize_below m2 n)
      \/
      leqM (normalize_below m1 n)
           (bindM (normalize_below m2 n) (fun _ => returnM None)).


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
        Proper (((@eq A) ==> (leqM (A:=B))) ==> @eq A ==> leqM (A:=B)) f ->
        fixM (A:=A) (B:=B) f x == f (fixM f) x
  }.


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

Instance FixM2_leqM : MonadOrder FixM2 :=
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
