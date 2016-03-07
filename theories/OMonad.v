Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import PredMonad.OrderedTerms.



Module ONotations.
  Notation "x '-o>' y" := (otype_fun x y) (right associativity, at level 99).
  Notation "x ~~ y" := (@oequiv _ x y) (no associativity, at level 70).
  Notation "x <~ y" := (@ole _ x y) (no associativity, at level 70).
  Notation "x @ y" := (otype_apply x y) (left associativity, at level 11, y at level 0).
  Notation "x $ y" := (otype_apply x y) (left associativity, at level 11, y at level 200, only parsing).

  Ltac make_cons T n :=
    let rec go n :=
        lazymatch n with
        | 0 => uconstr:(@cons T _ _)
        | S ?Z =>
          let p := go Z in
          uconstr:(@cons T _ p)
        end
    in
    let z := go n in
    refine z.

  Delimit Scope ctx_scope with ctx.

  Notation "x @ y" := (@App_ctx _ _ _ x%ctx y%ctx) (left associativity, at level 11, y at level 0) : ctx_scope.
  Notation "x $ y" := (@App_ctx _ _ _ x%ctx y%ctx) (left associativity, at level 11, y at level 200, only parsing) : ctx_scope.
  Notation "\ t => y" := (@Abs_ctx _ t _ y%ctx) (left associativity, at level 200) : ctx_scope.
  Notation "! x" := (@Lift_ctx _ _ x%ctx) (no associativity, at level 0) : ctx_scope.
  Notation "# n" := (@Var_ctx _ n%nat ltac:(make_cons otype n) eq_refl) (at level 0) : ctx_scope.
  Arguments ToCtx {_} _%ctx.
  Arguments Abs_ctx {_ _ _} _%ctx.
  Arguments App_ctx {_ _ _} (_ _)%ctx.
End ONotations.

Import ONotations.


Typeclasses Opaque oequiv ole.

(**
 ** The Definition of an ordered monad
 **)
Class OMonad (M : otype -> otype) : Type :=
{ returnM : forall {A : otype}, A -o> (M A)
; bindM : forall {A B : otype}, M A -o> (A -o> M B) -o> M B
; monad_return_bind : forall (A B : otype) (x : A) (f : A -o> M B),
    bindM @ (returnM @ x) @ f ~~ f @ x
; monad_bind_return : forall A (m : M A),
    bindM @ m @ returnM ~~ m
; monad_assoc : forall {A B C : otype} m (f : A -o> M B) (g : B -o> M C),
    bindM @ (bindM @ m @ f) @ g ~~
    bindM @ m $ ToCtx (\ A => !bindM @ (!f @ #0) @ !g)
}.

(**
 ** Pair Functions
 **)
Definition otype_pair {A B : otype} : A -o> B -o> otype_prod A B.
  refine (ToCtx (\ _ => \ _ => _)).
  red. simpl. exists (fun ba_ => (fst (snd ba_), fst ba_)).
  abstract (do 2 red; split; simpl; apply H).
Defined.

Definition pair_fst {A B : otype} : otype_prod A B -o> A.
  exists fst.
  abstract (do 2 red; simpl; intros; apply H).
Defined.

Definition pair_snd {A B : otype} : otype_prod A B -o> B.
  exists snd.
  abstract (do 2 red; simpl; intros; apply H).
Defined.

Definition pair_elim {A B C : otype} : otype_prod A B -o> (A -o> B -o> C) -o> C :=
  ToCtx (\ _ => \ _ => #0 @ (!pair_fst @ #1) @ (!pair_snd @ #1)).

(** * Pair Reduction **)
Lemma pair_elim_red {A B C : otype} (f : A -> B -> C)  pf' pf x :
  pair_elim @ x @ (@otype_abs _ _ (fun x => @otype_abs _ _ (f x) (pf' x)) pf)
  ~~ f (pair_fst @ x) (pair_snd @ x).
Proof. destruct x; reflexivity. Defined.
Lemma pair_elim_pair_red {A B C : otype} (f : A -o> B -o> C) x y :
  pair_elim @ (otype_pair @ x @ y) @ f ~~ f @ x @ y.
Proof. reflexivity. Defined.
Lemma pair_fst_pair_red {A B} x y :
  @pair_fst A B @ (x,y) ~~ x.
Proof. reflexivity. Defined.
Lemma pair_snd_pair_red {A B} x y :
  @pair_snd A B @ (x,y) ~~ y.
Proof. reflexivity. Defined.
Lemma otype_pair_red {A B} x y :
  (@otype_pair A B @ x @ y) ~~ (x,y).
Proof. reflexivity. Defined.
Lemma otype_pair_eta_contract {A B} (x : otype_prod A B) :
  otype_pair @ (pair_fst @ x) @ (pair_snd @ x) ~~ x.
Proof. destruct x; reflexivity. Defined.
Lemma pair_eta_contract {A B} (x : otype_prod A B) :
  ((pair_fst @ x), (pair_snd @ x)) ~~ x.
Proof. destruct x; reflexivity. Defined.
Lemma pair_elim_arr {A B C : otype} x (f : A -o> B -o> C)
  : pair_elim @ x @ f ~~ f @ (pair_fst @ x) @ (pair_snd @ x).
Proof. destruct x; reflexivity. Defined.

Global Instance Proper_pair {A B : otype}
: Proper (oequiv ==> oequiv ==> oequiv) (@pair A B).
Proof. do 3 red. intros.
       do 2 constructor; first [ apply H | apply H0 ].
Qed.


Hint Rewrite @pair_elim_pair_red @otype_pair_eta_contract @pair_eta_contract
  : reduce_pair.
Hint Rewrite @pair_elim_arr @otype_pair_red
     @pair_fst_pair_red @pair_snd_pair_red
  : reduce_pair.



(** Tuple Reduction **)
Lemma tuple_hd_red {A : otype} {As : list otype} x xs
: @tuple_hd A As @ (otype_pair @ x @ xs) ~~ x.
Proof. reflexivity. Defined.
Lemma tuple_tl_red {A : otype} {As : list otype} x xs
: @tuple_tl A As @ (otype_pair @ x @ xs) ~~ xs.
Proof. reflexivity. Defined.

Lemma tuple_tl_pair {A : otype} {Bs : list otype} (x : A) (y : otype_tuple Bs)
: OrderedTerms.tuple_tl @ (x,y) ~~ y.
Proof. reflexivity. Defined.
Lemma tuple_hd_pair {A : otype} {Bs : list otype} (x : A) (y : otype_tuple Bs)
: OrderedTerms.tuple_hd @ (x,y) ~~ x.
Proof. reflexivity. Defined.



(**
 ** Generic Reduction
 **
 ** NOTE: Most things here follow immediately from reflexivity. However, we do
 ** not want to compute them because we only want to reduce in these instances.
 ** If we do unconstrained reduction, then we will expose proofs and everything
 ** will slow down.
 **)
Lemma otype_apply_ToCtx {B} (f : InCtx nil B)
: ToCtx f ~~ f @ tt.
Proof. reflexivity. Defined.
Lemma otype_apply_Abs_ctx A B G (f : InCtx (A :: G) B) (x : A) gs
: Abs_ctx f @ gs @ x ~~ f @ (x, gs).
Proof. reflexivity. Defined.
Lemma otype_apply_App_ctx {A B G} (f : InCtx G (A -o> B)) x gs
: otype_apply (App_ctx f x) gs ~~ otype_apply (f @ gs) (x @ gs).
Proof. reflexivity. Defined.
Lemma otype_apply_Lift_ctx {A : otype} {G : list otype} (f : A) gs
: otype_apply (Lift_ctx (ls:=G) f) gs ~~ f.
Proof. reflexivity. Defined.
Lemma otype_apply_Var_ctx_O {A : otype} {G : list otype} (x : A)
      (xs : otype_tuple G)
: otype_apply (Var_ctx (a:=A) (ls:=A::G) 0 (@eq_refl _ (List.nth_error (A::G) 0))) (x, xs) ~~ x.
Proof. reflexivity. Qed.
Lemma otype_apply_Var_ctx_O' {A : otype} {G : list otype} (x : A)
      (xs : otype_tuple G)
: otype_apply (Var_ctx (a:=A) (ls:=A::G) 0 (@eq_refl _ (Some A))) (x, xs) ~~ x.
Proof. reflexivity. Qed.
Lemma otype_apply_Var_ctx_S {A B : otype} {G : list otype} n pf (x : A)
      (xs : otype_tuple G)
  : otype_apply (Var_ctx (a:=B) (ls:=A::G) (S n) pf) (x, xs) ~~
                otype_apply (Var_ctx n pf) xs.
Proof. simpl. unfold otype_compose.
       generalize (Var_ctx n pf). intros.
       destruct t.
       simpl. reflexivity.
Qed.
Lemma otype_abs_otype_apply : forall {A B : otype} f pf x,
    (@otype_abs A B f pf @ x) ~~ f x.
Proof. reflexivity. Qed.
Lemma ToCtx_oequiv {B} (f : InCtx nil B)
: ToCtx f ~~ f @ tt.
Proof. reflexivity. Qed.
Lemma ToCtx_eq {B} (f : InCtx nil B)
: ToCtx f = f @ tt.
Proof. reflexivity. Qed.
Lemma otype_compose_red {A B C : otype} (f : A -o> B) (g : C -o> A) (x : C) :
  otype_compose g f @ x ~~ f $ g $ x.
Proof. reflexivity. Defined.

Hint Rewrite otype_apply_Abs_ctx @ToCtx_eq
     @otype_apply_Abs_ctx @otype_apply_App_ctx
     @otype_apply_Lift_ctx @otype_apply_Var_ctx_S
     @otype_apply_Var_ctx_O @otype_apply_Var_ctx_O'
     @ToCtx_oequiv
  : reduce.
Hint Rewrite @otype_abs_otype_apply : reduce.
Hint Rewrite @otype_compose_red : reduce.


(** * Tactics for Ordered Terms **)
Ltac oext := repeat (eapply otype_ext_eq; intros).

Ltac of_equal := first [ eapply Proper_otype_apply_oequiv
                       | eapply Proper_otype_apply_ole ] ; try reflexivity.

Ltac oreduce :=
  rewrite_strat topdown (repeat (choice (hints reduce) (hints reduce_pair))).


(***
 *** The Identity Monad
 ***)
Definition Identity (X:otype) := X.
Instance OMonad_Identity : OMonad Identity :=
{ returnM := fun A => ToCtx (\ A => #0)
; bindM  := fun A B => ToCtx (\ Identity A => \ (A -o> Identity B) => #0 @ #1)
}.
Proof.
{ reflexivity. }
{ reflexivity. }
{ reflexivity. }
Qed.



(***
 *** The State Monad
 ***)
Section with_state.
  Context {s : otype}.

  Definition State (x : otype) := s -o> otype_prod x s.
  Instance OMonad_State : OMonad State :=
  { returnM := fun A => ToCtx (\ A => \ s => !otype_pair @ #1 @ #0)
  ; bindM   := fun A B => ToCtx (\ State A => \ (A -o> State B) => \ s =>
                                 !pair_elim @ (#2 @ #0) @ #1)
  }.
  Proof.
  all: unfold State; simpl List.nth_error.
  { intros; oext.
    oreduce.
    reflexivity. }
  { intros; oext.
    oreduce.
    reflexivity. }
  { intros; oext.
    oreduce.
    reflexivity. }
  Defined.
End with_state.

Hint Rewrite @monad_return_bind @monad_bind_return @monad_assoc : reduce_monad.

Section StateT.
  Variable s : otype.
  Variable m : otype -> otype.
  Variable Mm : OMonad m.

  Ltac oreduce_m :=
    rewrite_strat topdown (repeat (choice (hints reduce)
                                          (choice (hints reduce_pair)
                                                  (hints reduce_monad)))).

  Definition StateT (x : otype) : otype := s -o> m (otype_prod x s).
  Instance OMonad_StateT : OMonad StateT :=
  { returnM := fun A => ToCtx (\ A => \ s => !returnM $ !otype_pair @ #1 @ #0)
  ; bindM   := fun A B => ToCtx (\ StateT A => \ (A -o> StateT B) => \ s =>
                                 !bindM @ (#2 @ #0) @ \ (otype_prod A s) =>
                                 !pair_elim @ #0 @ \ A => \ s =>
                                   #4 @ #1 @ #0)
  }.
  Proof.
  all: simpl List.nth_error; unfold StateT.
  { intros; oext. oreduce_m. reflexivity. }
  { intros; oext. oreduce_m.
    etransitivity; [ | eapply monad_bind_return ].
    of_equal.
    oext. oreduce_m.
    reflexivity. }
  { intros; oext. oreduce_m.
    of_equal. oext.
    oreduce_m.
    of_equal. oext.
    oreduce_m.
    reflexivity. }
  Time Defined.
End StateT.
