Require Import Coq.Setoids.Setoid.
Require Import PredMonad.OrderedTerms.

(***
 *** The monad typeclass
 ***)

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


Instance Reflexive_ole {T} : Reflexive (@ole T).
Proof. red. intros. red. destruct T. eapply Refl_le. Qed.
Instance Transitive_ole {T} : Transitive (@ole T).
Proof. red. intros. red. destruct T. eapply Trans_le; eauto. Qed.

Instance Reflexive_oequiv {T} : Reflexive (@oequiv T).
Proof. red. intros. red. destruct T. split; eapply Refl_le. Qed.
Instance Transitive_oequiv {T} : Transitive (@oequiv T).
Proof. red. intros. red. destruct T. destruct H; destruct H0; split; etransitivity; eauto. Qed.


Instance Proper_oequiv_iff {A : otype} : Morphisms.Proper (oequiv ==> oequiv ==> iff) (@oequiv A).
Proof. Admitted.
Instance Proper_oequiv_flip_impl {A : otype} : Morphisms.Proper (oequiv ==> oequiv ==> Basics.flip Basics.impl) (@oequiv A).
Proof. Admitted.
Instance Proper_oequiv_impl {A : otype} : Morphisms.Proper (oequiv ==> oequiv ==> Basics.impl) (@oequiv A).
Proof. Admitted.
Instance Proper_otype_apply {A B} : Morphisms.Proper (oequiv ==> oequiv ==> oequiv) (@otype_apply A B).
Proof. Admitted.

Typeclasses Opaque oequiv ole.


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

(** Pair Functions
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

Lemma otype_ext_eq : forall {A B : otype} (f g : A -o> B),
    (forall x, f @ x ~~ g @ x) ->
    f ~~ g.
Proof.
  intros.
  destruct f; destruct g; simpl in *.
  split.
  { red. simpl. red. intros.
    etransitivity.
    eapply Proper_function. eassumption.
    eapply H. }
  { red. simpl. red. intros.
    etransitivity.
    eapply Proper_function0. eassumption.
    eapply H. }
Qed.

Opaque otype_apply.

(** Tuple Reduction **)
Lemma tuple_hd {A : otype} {As : list otype} x xs
: @tuple_hd A As @ (otype_pair @ x @ xs) ~~ x.
Proof. reflexivity. Defined.
Lemma tuple_tl {A : otype} {As : list otype} x xs
  : @tuple_tl A As @ (otype_pair @ x @ xs) ~~ xs.
Proof. reflexivity. Defined.

Lemma tuple_tl_pair {A : otype} {Bs : list otype} (x : A) (y : otype_tuple Bs)
  : OrderedTerms.tuple_tl @ (x,y) ~~ y.
Proof. reflexivity. Defined.
Lemma tuple_hd_pair {A : otype} {Bs : list otype} (x : A) (y : otype_tuple Bs)
  : OrderedTerms.tuple_hd @ (x,y) ~~ x.
Proof. reflexivity. Defined.

(** Generic Reduction **)
Lemma otype_apply_ToCtx {B} (f : InCtx nil B)
: ToCtx f ~~ f @ tt.
Proof. reflexivity. Defined.
Lemma otype_apply_Abs_ctx {A B G} (f : InCtx (A :: G) B) (x : A) gs
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
: otype_apply (Var_ctx (a:=A) (ls:=A::G) 0 eq_refl) (x, xs) ~~ x.
Proof. reflexivity. Qed.
(** NOTE: Most things here are immediate from reflexivity, however, we don't
 ** want to compute them because we only want to reduce in these instances.
 ** If we do unconstrained reduction, then we will expose proofs and everything
 ** will slow down.
 **)

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


Instance Proper_App_ctx G A B
  : Morphisms.Proper (oequiv ==> oequiv ==> oequiv) (@App_ctx G A B).
Proof. Admitted.

Instance Proper_Abs_ctx G B A : Morphisms.Proper (oequiv ==> oequiv) (@Abs_ctx G A B).
Proof. Admitted.

Lemma ToCtx_eq {B} (f : InCtx nil B)
  : ToCtx f = f @ tt.
Proof. reflexivity. Qed.

Instance Symmetric_oequiv {A} : Symmetric (@oequiv A).
Proof. red. unfold oequiv. tauto. Qed.

Hint Rewrite @otype_apply_Abs_ctx @ToCtx_eq
     @otype_apply_Abs_ctx @otype_apply_App_ctx
     @otype_apply_Lift_ctx @otype_apply_Var_ctx_S @otype_apply_Var_ctx_O
  : reduce.
Hint Rewrite @otype_abs_otype_apply : reduce.

Lemma pair_elim_red {A B C : otype} (f : A -> B -> C)  pf' pf x :
  pair_elim @ x @ (@otype_abs _ _ (fun x => @otype_abs _ _ (f x) (pf' x)) pf)
  ~~ f (pair_fst @ x) (pair_snd @ x).
Proof. Admitted.
Lemma pair_elim_pair_red {A B C : otype} (f : A -o> B -o> C) x y :
  pair_elim @ (otype_pair @ x @ y) @ f ~~ f @ x @ y.
Proof. Admitted.
Lemma otype_compose_red {A B C : otype} (f : A -o> B) (g : C -o> A) (x : C) :
  otype_compose g f @ x ~~ f $ g $ x.
Proof. Admitted.

Lemma otype_pair_eta_contract {A B} (x : otype_prod A B) :
  otype_pair @ (pair_fst @ x) @ (pair_snd @ x) ~~ x.
Proof. Admitted.
Lemma pair_elim_arr {A B C : otype} x (f : A -o> B -o> C)
  : pair_elim @ x @ f ~~ f @ (pair_fst @ x) @ (pair_snd @ x).
Proof. Admitted.

Hint Rewrite @pair_elim_pair_red @otype_pair_eta_contract : reduce_pair.
Hint Rewrite @pair_elim_arr : reduce_pair.

(** TODO: move this outward **)
Arguments otype_abs {_ _} _ {_} : clear implicits.

Existing Instance Reflexive_oequiv.

Existing Instance Transitive_oequiv.


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
  { intros. eapply otype_ext_eq; intros.
    autorewrite with reduce reduce_pair.
    reflexivity. }
  { intros.
    repeat (eapply otype_ext_eq; intros).
    rewrite_strat (bottomup (hints reduce)).
    rewrite_strat (topdown @otype_apply_Abs_ctx).
    autorewrite with reduce reduce_pair.
    reflexivity. }
  { intros.
    repeat (eapply otype_ext_eq; intros).
    autorewrite with reduce reduce_pair.
    reflexivity. }
  Qed.
End with_state.

Hint Rewrite @monad_return_bind @monad_bind_return
     @monad_assoc : reduce_monad.

Lemma otype_pair_fst_pair : forall {A B : otype} (x : A) (y : B),
    (pair_fst $ otype_pair @ x @ y) ~~ x.
Proof. reflexivity. Qed.
Lemma otype_pair_snd_pair : forall {A B : otype} (x : A) (y : B),
    (pair_snd $ otype_pair @ x @ y) ~~ y.
Proof. reflexivity. Qed.
Hint Rewrite @otype_pair_fst_pair @otype_pair_snd_pair : reduce_pair.


Section StateT.
  Variable s : otype.
  Variable m : otype -> otype.
  Variable Mm : OMonad m.

  (** This is hack to get around a bug in rewriting *)
  Ltac force_rewrite :=
    match goal with
    | |- context [ @otype_apply ?Ta ?Tb (@otype_apply (otype_tuple ?G) (otype_fun ?Ta ?Tb) (@Abs_ctx ?G _ _ ?A) ?B) ?C ] =>
      generalize (@otype_apply_Abs_ctx Ta Tb G A C B) ;
      match goal with
      | |- (?X ~~ _) -> _ => generalize X
      end;
      let x := fresh in
      intro x ;
      let H := fresh in
      let rw := repeat simple eapply Proper_otype_apply;
                first [ eapply H | reflexivity ] in
      intro H; (etransitivity;
                [ rw
                | first [ clear H ; clear x
                        | etransitivity ; [ | symmetry; rw ] ] ])
    end.

  Instance Proper_Lift_ctx A G
  : Morphisms.Proper (oequiv ==> oequiv) (@Lift_ctx A G).
  Proof.
    do 2 red. simpl. unfold Lift_ctx. intros.
    eapply otype_ext_eq.
    intros.
    autorewrite with reduce. assumption.
  Qed.

  Fixpoint otype_tuple_concat {A B} {struct A}
  : otype_tuple A -o> otype_tuple B -o> otype_tuple (A ++ B) :=
    match A as A
          return otype_tuple A -o> otype_tuple B -o> otype_tuple (A ++ B)
    with
    | nil => ToCtx (\ _ => \ _ => #0)
    | List.cons a b => ToCtx (\ (otype_tuple (a :: b)) => \ otype_tuple B =>
      !otype_pair @ (!OrderedTerms.tuple_hd @ #1)
       @ (!otype_tuple_concat @ (!OrderedTerms.tuple_tl @ #1) @ #0))%ctx
    end.

  Definition Shifts_ctx {A B G} (f : InCtx (A ++ G) B) (g : otype_tuple G)
  : InCtx A B.
  red. simpl. econstructor.
  Unshelve.
  Focus 2. intro. eapply f.
  eapply otype_tuple_concat; eassumption.
  red. red. intros. red. eapply f.
  eapply otype_tuple_concat; eauto. eapply Reflexive_ole.
  Defined.

(*
  Definition Shift_ctx {A B G} (f : InCtx (A :: G) B) (g : otype_tuple G)
    : InCtx (A :: nil) B := Shifts_ctx 
    simpl in *. eexists (fun x_ => f.(function) (pair (pair_fst @ x_) g)).
    simpl. red. red. intros.
    eapply Proper_function. red. simpl. split.
    apply H. reflexivity.
  Defined.
*)

  Lemma otype_apply_Abs_ctx_shift {A B G} (f : InCtx (A :: G) B) gs
  : otype_apply (Abs_ctx f) gs ~~ Abs_ctx (Shifts_ctx (A:=A::nil) f gs) @ tt.
  Proof.
    apply otype_ext_eq. intros.
    reflexivity.
  Qed.
  Lemma Shift_ctx_App_ctx {A B : otype} {Z G : list otype}
        (f : InCtx (Z ++ G) (A -o> B)) x g
  : Shifts_ctx (App_ctx f x) g ~~ App_ctx (Shifts_ctx f g) (Shifts_ctx x g).
  Proof.
    eapply otype_ext_eq; intros.
    reflexivity.
  Qed.
(*
  Lemma Shift_ctx_Var_ctx_0 {A : otype} {G : list otype}
        (pf : Some A = Some A) g
    : Shift_ctx (A:=A) (G:=G) (Var_ctx (ls:=A::G) 0 pf) g ~~
                (Var_ctx (ls:=A::nil) 0 pf).
  Proof. Admitted.
  Lemma Shift_ctx_Var_ctx_S {A B : otype} {G : list otype}
        n (pf : List.nth_error G n = Some A) g
    : Shift_ctx (A:=B) (G:=G) (Var_ctx (ls:=B::G) (S n) pf) g ~~
                Lift_ctx ((Var_ctx n pf) @ g).
  Proof. Admitted.
  Lemma Shift_ctx_Lift_ctx {A B : otype} {G : list otype} (x : B) y
    : Shift_ctx (A:=A) (G:=G) (Lift_ctx x) y ~~ Lift_ctx x.
  Proof. Admitted.
*)

  Require Import Coq.Lists.List.
(*
  Lemma Shifts_ctx_Abs_ctx (A B C : otype) (G : list otype) (f : InCtx (C :: A :: G) B) (x : otype_tuple G)
  : Shift_ctx (Abs_ctx f) x ~~ Abs_ctx (Shifts_ctx (A:=C::A::nil) (B:=B) (G:=G) f x).
  Proof. Admitted.
*)
  Lemma Shifts_ctx_Abs_ctx (A : list otype) (B C : otype) (G : list otype) (f : InCtx (C :: A ++ G) B) (x : otype_tuple G)
  : Shifts_ctx (A:=A) (Abs_ctx f) x ~~
               Abs_ctx (Shifts_ctx (A:=C::A) (B:=B) (G:=G) f x).
  Proof.
    repeat (eapply otype_ext_eq; intros).
    reflexivity.
  Qed.
  Lemma Shifts_ctx_App_ctx {A B : otype} {Z G : list otype}
        (f : InCtx (Z ++ G) (A -o> B)) x g
  : Shifts_ctx (App_ctx f x) g ~~ App_ctx (Shifts_ctx f g) (Shifts_ctx x g).
  Proof.
    repeat (eapply otype_ext_eq; intros).
    reflexivity.
  Qed.
  Definition n_minus_0_is_n n : n - 0 = n :=
    match n as n return n - 0 = n with
    | 0 => eq_refl
    | S n => eq_refl
    end.

  Fixpoint nth_error_pick_side {A} (xs ys : list otype) (n : nat)
  : nth_error (xs ++ ys) n = Some A ->
    {nth_error xs n = Some A} + {nth_error ys (n - length xs) = Some A} :=
    match xs as xs
          return nth_error (xs ++ ys) n = Some A ->
                 {nth_error xs n = Some A} + {nth_error ys (n - length xs) = Some A}
    with
    | nil => fun pf => right match eq_sym (n_minus_0_is_n n) with
                             | eq_refl => pf
                             end
    | x :: xs => match n as n
                       return nth_error (x :: xs ++ ys) n = Some A ->
                              {nth_error (x :: xs) n = Some A} + {nth_error ys (n - S (length xs)) = Some A}
                 with
                 | 0 => fun pf => left pf
                 | S n => @nth_error_pick_side A xs ys n
                 end
    end.

  Lemma Shifts_ctx_Var_ctx {A : otype} {Bs G : list otype}
        n (pf : List.nth_error (Bs++G) n = Some A) g
  : Shifts_ctx (A:=Bs) (G:=G) (Var_ctx (ls:=Bs++G) n pf) g ~~
               match nth_error_pick_side Bs G n pf with
               | left pf => @Var_ctx _ _ _ pf
               | right pf => @Lift_ctx Bs A ((Var_ctx (n - List.length Bs) pf) @ g)
               end.
  Proof.
    repeat (eapply otype_ext_eq; intros).
    generalize dependent n.
    induction Bs; simpl; intros.
    { unfold Shifts_ctx. simpl.
      Transparent otype_apply.
      unfold otype_apply. simpl.
      generalize (eq_sym (n_minus_0_is_n n)); intros.
      generalize dependent (n-0).
      intros; subst. reflexivity. }
    { destruct n.
      { simpl in *; clear.
        admit. }
      { admit. } }
  Admitted.

  Hint Rewrite @otype_apply_Abs_ctx_shift @Shift_ctx_App_ctx
       @Shifts_ctx_Abs_ctx
       @Shifts_ctx_App_ctx
       @Shifts_ctx_Var_ctx
    : reduce_shift.


  Lemma Shifts_ctx_Lift_ctx {B : otype} {A G : list otype} (x : B) y
    : Shifts_ctx (A:=A) (G:=G) (Lift_ctx x) y ~~ Lift_ctx x.
  Proof. Admitted.
  Instance Proper_pair {A B : otype} : Morphisms.Proper (oequiv ==> oequiv ==> oequiv) (@pair A B).
  Proof. red. red. red. intros.
         do 2 constructor; first [ apply H | apply H0 ].
  Qed.

  Lemma otype_apply_Var_ctx_O'
    : forall (A : otype) (G : list otype) (x : A) (xs : otype_tuple G),
      @oequiv A
              (@otype_apply (otype_tuple (@cons otype A G)) A
                            (@Var_ctx A O (@cons otype A G)
                                      (@eq_refl (option otype) (@Some _ A)))
                            (@pair A (otype_tuple G) x xs)) x.
  Proof. Admitted.

  Definition StateT (x : otype) : otype := s -o> m (otype_prod x s).
  Instance OMonad_StateT : OMonad StateT :=
  { returnM := fun A => ToCtx (\ A => \ s => !returnM $ !otype_pair @ #1 @ #0)
  ; bindM   := fun A B => ToCtx (\ StateT A => \ (A -o> StateT B) => \ s =>
                                 !bindM @ (#2 @ #0) @ \ (otype_prod A s) =>
                                 !pair_elim @ #0 @ \ A => \ s =>
                                   #4 @ #1 @ #0)
  }.
  Proof.
  { intros.
    repeat (eapply otype_ext_eq; intros).
    repeat rewrite ToCtx_eq.
    unfold StateT.
    autorewrite with reduce reduce_pair reduce_monad.
    reflexivity. }
  { intros.
    repeat (eapply otype_ext_eq; intros).
    unfold StateT.
    autorewrite with reduce reduce_pair reduce_monad.
    etransitivity; [ | eapply monad_bind_return ].
    eapply Proper_otype_apply; [ reflexivity | ].
    repeat (eapply otype_ext_eq; intros).
    autorewrite with reduce reduce_pair.
    reflexivity. }
  { intros.
    repeat (eapply otype_ext_eq; intros).
    rewrite ToCtx_eq.
    rewrite_strat repeat progress (outermost @otype_apply_Abs_ctx).
    progress rewrite_strat repeat progress (outermost (hints reduce)).
    Ltac fwd :=
      repeat first [ rewrite otype_apply_Abs_ctx
                   | rewrite otype_apply_App_ctx
                   | rewrite otype_apply_Lift_ctx
                   | (progress repeat rewrite otype_apply_Var_ctx_S)
                   | rewrite otype_apply_Var_ctx_O ].
    fwd.
    rewrite monad_assoc.
    eapply Proper_otype_apply.
    eapply Proper_otype_apply. reflexivity.
    Ltac ext := repeat (eapply otype_ext_eq; intros).
    reflexivity.
    rewrite ToCtx_eq.
    ext.
    fwd.
    do 2 rewrite pair_elim_arr.
    fwd.
    eapply Proper_otype_apply. reflexivity.
    ext.
    fwd.
    reflexivity. }
  Defined.
End StateT.