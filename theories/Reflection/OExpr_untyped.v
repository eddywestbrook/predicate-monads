Require Export PredMonad.Reflection.OrderedType.
Require Export PredMonad.Reflection.OrderedContext.
Require Import Coq.Logic.ProofIrrelevance.

Import EqNotations.
Import ListNotations.
Import ProofIrrelevanceTheory.

(***
 *** Ordered Expressions
 ***)

(* Ordered expressions to represent proper functions *)
Inductive OExpr : Type :=
| OVar (vctx:Ctx) (n:nat)
| OEmbed (ectx:Ctx) {A} {RA:OTRelation A} (a:A)
| OApp (B:Type) {RB:OTRelation B} (e1 e2 : OExpr)
| OLam (e: OExpr)
.

(* Get the canonical context of an ordered expression *)
Fixpoint OExpr_ctx e : Ctx :=
  match e with
  | OVar ctx _ => ctx
  | @OEmbed ctx _ _ _ => ctx
  | OApp _ _ arg => OExpr_ctx arg
  | OLam f => ctxTail (OExpr_ctx f)
  end.
Arguments OExpr_ctx !e.

(* Get the canonical type and relation of an ordered expression *)
Fixpoint OExpr_TpRel e : TpRel :=
  match e with
  | OVar ctx n => mkTpRel (ctxNth n ctx)
  | @OEmbed _ A _ _ => mkTpRel A
  | OApp B _ _ => mkTpRel B
  | OLam f =>
    mkTpRel ((ctxHead (OExpr_ctx f)) -o> (projT1 (OExpr_TpRel f)))
  end.
Arguments OExpr_TpRel !e.

Definition OExpr_type e := projT1 (OExpr_TpRel e).
Arguments OExpr_type e /.

Instance OTRelation_OExpr_type e : OTRelation (OExpr_type e) := _.
Arguments OTRelation_OExpr_type e /.


(***
 *** Typing for Ordered Expressions
 ***)

(* Proof that an ordered expression is well-typed *)
Fixpoint HasType ctx T {RT:OTRelation T} (e:OExpr) : Prop :=
  match e with
  | OVar ctx' v =>
    ValidCtx ctx /\ (ctx = ctx' /\ (ctxNth v ctx') =t= T)
  | @OEmbed ctx' A _ a =>
    (ValidCtx ctx /\ OType A) /\
    (ctx = ctx' /\ A =t= T)
  | OApp B f arg =>
    (B =t= T /\ OType B) /\
    (HasType ctx (OExpr_type arg -o> T) f /\
     HasType ctx (OExpr_type arg) arg)
  | OLam f =>
    (ctx = ctxTail (OExpr_ctx f) /\
     (ctxHead (OExpr_ctx f) -o> OExpr_type f) =t= T) /\
    (HasType (CtxCons (ctxHead (OExpr_ctx f)) (ctxTail (OExpr_ctx f)))
            (OExpr_type f) f /\
     (OExpr_ctx f <> CtxNil /\ ValidCtx (OExpr_ctx f)))
  end.
Arguments HasType ctx T {RT} !e.

(* Typeclass version of HasType *)
Class HasTypeC ctx T {RT:OTRelation T} e : Prop := hasType : HasType ctx T e.

(* Expressions can only be typed in their one context *)
Lemma HasType_ctx_eq ctx T {RT:OTRelation T} e :
  HasType ctx T e -> ctx = OExpr_ctx e.
Proof.
  revert ctx T RT; induction e.
  - intros ctx' T RT [valid [ctx_eq tp_eq]]. assumption.
  - intros ctx' T RT [[valid otype] [ctx_eq tp_eq]]. assumption.
  - intros ctx' T RT [[tp_eq otype] [ht1 ht2]]. apply (IHe2 _ _ _ ht2).
  - intros ctx' T RT [[ctx_eq tp_eq] [ctx_neq_nil ht_e]]. assumption.
Qed.

(* Expressions can only have their one type *)
Lemma HasType_TpRel_eq ctx T {RT:OTRelation T} e :
  HasType ctx T e -> mkTpRel T = OExpr_TpRel e.
Proof.
  revert ctx T RT; induction e.
  - intros ctx' T RT [ valid [ ctx_eq tp_eq ]]. symmetry; assumption.
  - intros ctx' T RT [[valid otype] [ctx_eq tp_eq]]. symmetry; assumption.
  - intros ctx' T RT [[tp_eq otype] [ht1 ht2]]. symmetry; assumption.
  - intros ctx' T RT [[ctx_eq tp_eq] [ctx_neq_nil ht_e]]. symmetry; assumption.
Qed.

Lemma HasType_tp_eq ctx T {RT:OTRelation T} e :
  HasType ctx T e -> T =t= OExpr_type e.
Proof.
  intro ht. unfold OExpr_type. unfold OTRelation_OExpr_type.
  rewrite <- (HasType_TpRel_eq _ _ _ ht). simpl. reflexivity.
Qed.

Instance ValidCtx_OExpr_ctx ctx T {RT:OTRelation T} e (ht:HasTypeC ctx T e) :
  ValidCtx (OExpr_ctx e).
Proof.
  revert ctx T RT ht; induction e.
  - intros ctx' T RT [ valid [ ctx_eq _ ]]. rewrite <- ctx_eq; assumption.
  - intros ctx' T RT [[valid _] [ctx_eq _]]. rewrite <- ctx_eq; assumption.
  - intros ctx' T RT [[tp_eq otype] [ht1 ht2]]. apply (IHe2 _ _ _ ht2).
  - intros ctx' T RT [[ctx_eq tp_eq] [ctx_neq_nil ht_e]]. typeclasses eauto.
Qed.

Instance ValidCtx_HasTypeC ctx T RT e (ht:@HasTypeC ctx T RT e) :
  ValidCtx ctx.
Proof.
  rewrite (HasType_ctx_eq _ _ _ ht). typeclasses eauto.
Qed.

(* Any well-typed expression has a valid type *)
Instance OType_OExpr_type ctx T RT e (ht:@HasTypeC ctx T RT e) :
  OType (OExpr_type e).
Proof.
  revert ctx T RT ht; induction e; intros.
  - destruct ht as [valid [ctx_eq _]]; rewrite <- ctx_eq; typeclasses eauto.
  - destruct ht as [[valid otype] _]. assumption.
  - destruct ht as [[ctx_eq otype] _]. assumption.
  - destruct ht as [[ctx_eq tp_eq] [ctx_neq_nil ht_e]]. typeclasses eauto.
Qed.

Instance OType_semTp_HasTypeC ctx T RT e (ht:@HasTypeC ctx T RT e) :
  OType T.
Proof.
  dependent rewrite (HasType_tp_eq _ _ _ ht). typeclasses eauto.
Qed.


(***
 *** The Semantics of Ordered Expressions
 ***)

(* We need versions of proj1 and proj2 that actually compute *)
Definition proj1c {P Q:Prop} (pf:P /\ Q) : P :=
  match pf with conj pf1 _ => pf1 end.
Arguments proj1c {P Q} !pf.

Definition proj2c {P Q:Prop} (pf:P /\ Q) : Q :=
  match pf with conj _ pf2 => pf2 end.
Arguments proj2c {P Q} !pf.

(* The ordered type associated with a TpRel + context *)
Definition Semantics ctx T {RT:OTRelation T} : Type := CtxElem ctx -o> T.
Arguments Semantics ctx T {RT} /.

(* Helper function to coerce a Semantics type *)
Definition coerceSemantics {ctx1 ctx2 T1 T2}
           {RT1:OTRelation T1} {RT2:OTRelation T2}
           (pf:ctx2 = ctx1 /\ T1 =t= T2) (sem:Semantics ctx1 T1) :
  Semantics ctx2 T2 :=
  compose_pfun (eq_ctx_pfun (proj1c pf))
               (compose_pfun sem (eq_pfun (proj2c pf))).
Arguments coerceSemantics {_ _ _ _ _ _} pf sem /.

(* The semantics of a well-typed expression *)
Program Fixpoint exprSemantics ctx T {RT:OTRelation T} e :
  HasTypeC ctx T e -> Semantics ctx T :=
  match e return HasType ctx T e -> Semantics ctx T with
  | OVar ctx' v =>
    fun ht =>
      coerceSemantics (proj2c ht) (nth_pfun ctx' v)
  | OEmbed ctx a =>
    fun ht =>
      coerceSemantics (proj2c ht)
                      (const_pfun (H0:=proj2c (proj1c ht)) a)
  | OApp B f arg =>
    fun ht =>
      pfun_apply
        (exprSemantics ctx (OExpr_type arg -o> T) f
                       (proj1c (proj2c ht)))
        (exprSemantics ctx (OExpr_type arg) arg
                       (proj2c (proj2c ht)))
  | OLam f =>
    fun ht =>
      coerceSemantics
        (proj1c ht)
        (pfun_curry
           (H:= _ )
           (exprSemantics (CtxCons _ _) (OExpr_type f)
                          f
                          (proj1c (proj2c ht))))
  end.
Next Obligation.
  apply OType_CtxElem. apply ValidCtx_ctxTail. assumption.
Defined.
Arguments exprSemantics ctx T {RT} !e.


(***
 *** Relating Ordered Expressions
 ***)

(* Proposition that two expressions have the same set of types *)
Definition equiTyped e1 e2 : Prop :=
  forall ctx T {RT}, @HasType ctx T RT e1 <-> @HasType ctx T RT e2.

Instance Equivalence_equiTyped : Equivalence equiTyped.
Proof.
  split.
  - intros x ctx T RT; reflexivity.
  - intros x y equi ctx T RT; symmetry; apply equi.
  - intros e1 e2 e3 equi12 equi23 ctx T RT.
    transitivity (HasType ctx T e2); [ apply equi12 | apply equi23 ].
Qed.

(* Equi-typed expressions have the same contexts *)
Lemma equiTyped_eq_ctx e1 e2 (equi:equiTyped e1 e2)
      ctx T {RT} (ht:@HasType ctx T RT e1) :
  OExpr_ctx e1 = OExpr_ctx e2.
  rewrite <- (HasType_ctx_eq _ _ _ ht).
  apply (HasType_ctx_eq _ _ _ (proj1 (equi ctx T RT) ht)).
Qed.

(* Equi-typed expressions have the same canonical types *)
Lemma equiTyped_eq_TpRel e1 e2 (equi:equiTyped e1 e2)
      ctx T {RT} (ht:@HasType ctx T RT e1) :
  OExpr_TpRel e1 = OExpr_TpRel e2.
  rewrite <- (HasType_TpRel_eq _ _ _ ht).
  apply (HasType_TpRel_eq _ _ _ (proj1 (equi ctx T RT) ht)).
Qed.

(* Equi-typed expressions have the same canonical types *)
Lemma equiTyped_eq_tp e1 e2 (equi:equiTyped e1 e2)
      ctx T {RT} (ht:@HasType ctx T RT e1) :
  OExpr_type e1 =t= OExpr_type e2.
Proof.
  simpl. rewrite (equiTyped_eq_TpRel _ _ equi _ _ ht). reflexivity.
Qed.

Record oexpr_R (e1 e2:OExpr) : Prop :=
  { oexpr_R_ht : equiTyped e1 e2;
    oexpr_R_R :
      forall ctx T RT ht1 ht2,
        @exprSemantics ctx T RT e1 ht1 <o= @exprSemantics ctx T RT e2 ht2 }.

(* The equivalence relation on ordered expressions *)
Definition oexpr_eq : relation OExpr :=
  fun e1 e2 => oexpr_R e1 e2 /\ oexpr_R e2 e1.

(* oexpr_R is reflexive *)
Instance Reflexive_oexpr_R : Reflexive oexpr_R.
Proof.
  intro e; split; try reflexivity.
  intros. rewrite (proof_irrelevance _ ht1 ht2). reflexivity.
Qed.

(* oexpr_R is transitive *)
Instance Transitive_oexpr_R : Transitive oexpr_R.
Proof.
  intros e1 e2 e3 [ ht12 r12 ] [ ht23 r23 ]. split.
  { intros; rewrite ht12; apply ht23. }
  { intros.
    transitivity (exprSemantics ctx T e2 (proj1 (ht12 _ _ _) ht1));
      [ apply r12 | apply r23 ]. }
Qed.

(* oexpr_R is thus a PreOrder *)
Instance PreOrder_oexpr_R : PreOrder oexpr_R :=
  Build_PreOrder _ _ _.

(* oexpr_eq is thus an Equivalence *)
Instance Equivalence_oexpr_eq : Equivalence oexpr_eq.
Proof.
  constructor; intro; intros.
  { split; reflexivity. }
  { destruct H; split; assumption. }
  { destruct H; destruct H0; split; transitivity y; assumption. }
Qed.


(***
 *** Rewriting Relative to oexpr_R and oexpr_eq
 ***)

Instance Proper_OEmbed_R ctx A {RA:OTRelation A} :
  Proper (ot_R ==> oexpr_R) (@OEmbed ctx A _).
Proof.
  intros a1 a2 Ra; split.
  { intro; intros; reflexivity. }
  { intros ctx' T RT [[valid1 otype1] [eq_ctx eq_tp]] ht2.
    rewrite (proof_irrelevance
               _ ht2 (conj (conj valid1 otype1) (conj eq_ctx eq_tp))).
    rewrite eq_ctx in ht2. simpl.
    rewrite Ra. reflexivity. }
Qed.

Instance Proper_OEmbed_eq ctx A {RA:OTRelation A} :
  Proper (ot_equiv ==> oexpr_eq) (@OEmbed ctx A _).
Proof.
  intros a1 a2 eqA; destruct eqA; split; apply Proper_OEmbed_R; assumption.
Qed.

Instance Proper_equiTyped_OApp (B:Type) {RB:OTRelation B} :
  Proper (equiTyped ==> equiTyped ==> equiTyped) (OApp B).
Proof.
  intros f1 f2 equi_f arg1 arg2 equi_arg ctx T RT.
  split; intros [ [semTp_eq otype_b] [ht_f' ht_arg'] ]; split; split;
    try assumption; simpl.
  { apply equi_f.
    rewrite (equiTyped_eq_TpRel
               arg2 arg1 (symmetry equi_arg) _ _
               (proj1 (equi_arg _ _ _) ht_arg')); assumption. }
  { apply equi_arg.
    rewrite (equiTyped_eq_TpRel
               arg2 arg1 (symmetry equi_arg) _ _
               (proj1 (equi_arg _ _ _) ht_arg')); assumption. }
  { apply equi_f.
    rewrite (equiTyped_eq_TpRel
               arg1 arg2 equi_arg _ _
               (proj2 (equi_arg _ _ _) ht_arg')); assumption. }
  { apply equi_arg.
      rewrite (equiTyped_eq_TpRel
                 arg1 arg2 equi_arg _ _
                 (proj2 (equi_arg _ _ _) ht_arg')); assumption. }
Qed.

Instance Proper_oexpr_R_OApp (B:Type) {RB:OTRelation B} :
  Proper (oexpr_R ==> oexpr_R ==> oexpr_R) (OApp B).
Proof.
  intros f1 f2 [ equi_f rf ] arg1 arg2 [ equi_arg r_arg ]; split; intros.
  { rewrite equi_f. rewrite equi_arg. reflexivity. }
  { destruct ht1 as [ [eq_tp otype_b] [ht_f1 ht_arg1]].
    destruct ht2 as [ [eq_tp' otype_b'] [ht_f2 ht_arg2]].
    assert (OExpr_TpRel arg1 = OExpr_TpRel arg2) as eq_arg_tp;
      [ apply (equiTyped_eq_TpRel _ _ equi_arg _ _ ht_arg1) | ].
    revert ht_f1 ht_arg1; simpl; rewrite eq_arg_tp; intros. f_equiv.
    - apply (rf ctx (_ -o> _)).
    - apply r_arg. }
Qed.

Instance Proper_equiTyped_OLam : Proper (equiTyped ==> equiTyped) OLam.
Proof.
  intros e1 e2 equi_e ctx tpRel; split;
    intros [[eq_ctx eq_tp] [ht_e [neq_nil valid]]];
    split; split; try split; simpl;
      first [ rewrite <- (equiTyped_eq_ctx e1 e2 equi_e _ _ ht_e)
            | rewrite <- (equiTyped_eq_ctx e2 e1 (symmetry equi_e) _ _ ht_e) ];
      first [ rewrite <- (equiTyped_eq_TpRel e1 e2 equi_e _ _ ht_e)
            | rewrite <- (equiTyped_eq_TpRel e2 e1 (symmetry equi_e) _ _ ht_e)
            | idtac ];
      try apply equi_e;
      try assumption.
Qed.

Instance Proper_oexpr_R_OLam : Proper (oexpr_R ==> oexpr_R) OLam.
Proof.
  intros e1 e2 [ equi_e re ]; split.
  { rewrite equi_e; reflexivity. }
  { intros ctx T RT [[eq_ctx1 eq_tp1] [ht_e1 [neq_nil1 valid1]]]
           [[eq_ctx2 eq_tp2] [ht_e2 [neq_nil2 valid2]]]; simpl.
    revert eq_ctx2 eq_tp2 neq_nil2 valid2 ht_e2; simpl.
    rewrite <- (equiTyped_eq_ctx e1 e2 equi_e _ _ ht_e1).
    rewrite <- (equiTyped_eq_TpRel e1 e2 equi_e _ _ ht_e1).
    intros. rewrite (proof_irrelevance _ eq_tp2 eq_tp1).
    rewrite (proof_irrelevance _ eq_ctx2 eq_ctx1).
    repeat f_equiv.
    - rewrite eq_ctx1. reflexivity.
    - apply (re _ _ _ ht_e1 ht_e2).
    - dependent rewrite <- eq_tp1. reflexivity. }
Qed.


(***
 *** Weakening for Ordered Expressions
 ***)

(* Weakening / lifting of ordered expressions *)
Fixpoint weakenOExpr w W {RW:OTRelation W} (e:OExpr) : OExpr :=
  match e with
  | OVar ctx v => OVar (ctxInsert w W ctx) (weakenIndex w v)
  | OEmbed ctx a => OEmbed (ctxInsert w W ctx) a
  | OApp B f arg =>
    OApp B (weakenOExpr w W f) (weakenOExpr w W arg)
  | OLam f => OLam (weakenOExpr (S w) W f)
  end.
Arguments weakenOExpr w W {RW} !e.

(* Weakening an expression weakens its context *)
Lemma weaken_OExpr_ctx w W {RW} e :
  OExpr_ctx (@weakenOExpr w W RW e) = ctxInsert w W (OExpr_ctx e).
Proof.
  revert w; induction e; intros; simpl; try reflexivity.
  { apply IHe2. }
  { rewrite IHe. rewrite ctxInsert_ctxTail. reflexivity. }
Qed.

(* Weakening an expression does not change its type *)
Lemma weaken_OExpr_TpRel_eq w W {RW} e :
  OExpr_TpRel (@weakenOExpr w W RW e) = OExpr_TpRel e.
Proof.
  revert w; induction e; intros; simpl.
  { apply weaken_ctxNth. }
  { reflexivity. }
  { reflexivity. }
  { rewrite weaken_OExpr_ctx. rewrite IHe.
    dependent rewrite (ctxHead_ctxInsert_S w _ (OExpr_ctx e)). reflexivity. }
Qed.

(* Weakening preserves typing *)
Lemma weaken_HasType w W `{OType W} ctx T {RT} e :
  @HasType ctx T RT e ->
  HasType (ctxInsert w W ctx) T (weakenOExpr w W e).
  revert w ctx T RT; induction e; simpl; intros w ctx T RT.
  { intros [ valid [ ctx_eq htv ]]; split; [ | split ].
    - typeclasses eauto.
    - simpl; rewrite ctx_eq; reflexivity.
    - rewrite weaken_ctxNth; assumption. }
  { intros [ [valid otype] [eq_ctx eq_tp]]; split; split; try assumption.
    - typeclasses eauto.
    - dependent rewrite <- eq_tp. rewrite eq_ctx. reflexivity. }
  { intros [[ eq_tp otype ] [ ht1 ht2 ]]; split; split.
    - dependent rewrite eq_tp; reflexivity.
    - assumption.
    - simpl. rewrite weaken_OExpr_TpRel_eq.
      apply IHe1. assumption.
    - simpl. rewrite weaken_OExpr_TpRel_eq. apply IHe2; assumption. }
  { intros [ [eq_ctx eq_tp] [ hte [ctx_neq_nil valid]]];
      repeat (lazymatch goal with | |- _ /\ _ => split | _ => idtac end).
    - rewrite eq_ctx. rewrite weaken_OExpr_ctx. rewrite ctxInsert_ctxTail.
      reflexivity.
    - rewrite weaken_OExpr_ctx.
      dependent rewrite (ctxHead_ctxInsert_S w W (OExpr_ctx e)).
      rewrite weaken_OExpr_TpRel_eq. assumption.
    - rewrite weaken_OExpr_ctx.
      rewrite <- ctxInsert_ctxTail.
      dependent rewrite (ctxHead_ctxInsert_S w W (OExpr_ctx e)).
      apply (IHe (S w) (CtxCons _ _)).
      rewrite weaken_OExpr_TpRel_eq. assumption.
    - rewrite weaken_OExpr_ctx.
      destruct (OExpr_ctx e);
        [ intro; apply ctx_neq_nil; reflexivity | discriminate ].
    - rewrite weaken_OExpr_ctx. typeclasses eauto. }
Qed.

(* Weakening is equivalent to pre-composing with weaken_pfun *)
Lemma weakeaning w W `{OType W} ctx T {RT} e ht ht_w :
  @exprSemantics _ T RT (weakenOExpr w W e) ht_w =o=
  compose_pfun (weaken_pfun w W ctx) (exprSemantics ctx T e ht).
  revert w ctx T RT ht ht_w; induction e; intros w ctx T RT; simpl.
  { intros [valid [eq_ctx eq_tp]]; simpl.
    rewrite eq_ctx. assert (ctxNth n vctx =t= T) as eq_tp'; try assumption.
    revert eq_tp; dependent rewrite <- eq_tp'.
    intros eq_tp [ valid_w [eq_ctx_w eq_tp_w]].
    rewrite (UIP_refl _ _ eq_tp). rewrite (UIP_refl _ _ eq_ctx_w). simpl.
    rewrite eq_ctx in valid.
    repeat rewrite id_compose_pfun. rewrite compose_id_pfun.
    rewrite weaken_nth_pfun; try assumption. f_equiv. f_equiv.
    apply UIP. }
  { intros [[valid otype] [eq_ctx eq_tp]]; simpl. rewrite eq_ctx.
    assert (A =t= T) as eq_tp'; try assumption.
    revert eq_tp; dependent rewrite <- eq_tp'; intro eq_tp.
    intros [[valid_w otype_w] [eq_ctx_w eq_tp_w]]; simpl.
    rewrite (UIP_refl _ _ eq_tp). rewrite (UIP_refl _ _ eq_ctx_w).
    rewrite (UIP_refl _ _ eq_tp_w). simpl. rewrite eq_ctx in valid.
    repeat rewrite id_compose_pfun.
    rewrite compose_compose_pfun.
    rewrite compose_f_const_pfun; try typeclasses eauto.
    rewrite (proof_irrelevance _ otype otype_w).
    reflexivity. }
  { rewrite (weaken_OExpr_TpRel_eq w W e2).
    intros [[eq_tp otype] [ht1 ht2]]; simpl.
    assert (B =t= T) as eq_tp'; try assumption.
    revert eq_tp; dependent rewrite eq_tp'; intro eq_tp.
    intros [[eq_tp_w otype_w] [ht1_w ht2_w]]; simpl.
    rewrite (IHe1 _ _ _ _ ht1). rewrite (IHe2 _ _ _ _ ht2).
    rewrite compose_pfun_apply; try typeclasses eauto. reflexivity. }
  { intros [[eq_ctx eq_tp] [ht [neq_nil valid]]]; simpl.
    assert {THead:Type & {RTHead:OTRelation THead &
                                 OExpr_ctx e = CtxCons THead ctx}}
      as [THead [RTHead eq_ctx']];
      [ exists (ctxHead (OExpr_ctx e)); eexists;
        rewrite eq_ctx; apply ctx_eq_head_tail; assumption | ].
    revert eq_ctx eq_tp ht neq_nil valid; rewrite eq_ctx'; simpl;
      intros eq_ctx eq_tp ht neq_nil [otype_head valid].
    assert ((THead -o> projT1 (OExpr_TpRel e)) =t= T) as eq_tp';
      try assumption; revert eq_tp; dependent rewrite <- eq_tp'.
    intros eq_tp [[eq_ctx_w eq_tp_w] [ht_w [neq_nil_w valid_w]]]; simpl.
    revert eq_ctx_w eq_tp_w ht_w neq_nil_w valid_w.
    rewrite (weaken_OExpr_ctx (S w) W); rewrite eq_ctx'; simpl.
    rewrite (weaken_OExpr_TpRel_eq (S w) W e). intros.
    destruct valid_w as [otype_w valid_w].
    rewrite (UIP_refl _ _ eq_tp). rewrite (UIP_refl _ _ eq_ctx).
    rewrite (UIP_refl _ _ eq_tp_w). rewrite (UIP_refl _ _ eq_ctx_w). simpl.
    repeat rewrite id_compose_pfun. repeat rewrite compose_id_pfun.
    rewrite compose_pfun_curry; try typeclasses eauto.
    f_equiv. apply (IHe (S w) (CtxCons THead _)).
    Unshelve. typeclasses eauto. }
Qed.


(***
 *** Substitution for Ordered Expressions
 ***)

(* Substitution for ordered expression variables *)
Fixpoint substOVar n (s:OExpr) vctx v : OExpr :=
  match n with
  | 0 =>
    match v with
    | 0 => s
    | S v' => OVar (ctxTail vctx) v'
    end
  | S n' =>
    match v with
    | 0 => OVar (ctxDelete (S n') vctx) 0
    | S v' =>
      weakenOExpr 0 (ctxHead vctx) (substOVar n' s (ctxTail vctx) v')
    end
  end.
Arguments substOVar !n s vctx !v.

(* Substitution for ordered expressions *)
Fixpoint substOExpr n (s:OExpr) (e:OExpr) : OExpr :=
  match e with
  | OVar vctx v => substOVar n s vctx v
  | OEmbed ctx a => OEmbed (ctxDelete n ctx) a
  | OApp B f arg => OApp B (substOExpr n s f) (substOExpr n s arg)
  | OLam body => OLam (substOExpr (S n) s body)
  end.


FIXME HERE NOW: need an equivalence on contexts, basically saying that
ctxNth is the same for all indices (so, e.g., CtxNil equiv cons of all units)

Lemma HasType_substOVar n s vctx v {valid:ValidCtx vctx} :
  HasType (ctxSuffix n vctx) (ctxNth n vctx) s ->
  HasType (ctxDelete n vctx) (ctxNth v vctx) (substOVar n s vctx v).
Proof.
  revert n vctx valid v; induction n; intros; destruct v.
  - destruct vctx; assumption.
  - destruct vctx; simpl; split; try split; try reflexivity.
    destruct valid; assumption.
  - destruct vctx; simpl; split; try split; try reflexivity.
    + destruct valid; assumption.
    + apply ValidCtx_ctxDelete; destruct valid; assumption.
  - destruct vctx; simpl.

Lemma substOExpr_HasType n s e ctx A {RA:OTRelation A} :
  HasType (ctxSuffix n ctx) (ctxNth n ctx) s -> HasType ctx A e ->
  HasType (ctxDelete n ctx) A (substOExpr n s e).
Admitted.

Lemma var_substitution n s vctx v
      (ht: HasTypeC (ctxDelete n vctx) (ctxNth v vctx) (substOVar n s vctx v))
      (ht_s: HasTypeC (ctxSuffix n vctx) (ctxNth n vctx) s) :
  exprSemantics (ctxDelete n vctx) _ (substOVar n s vctx v) ht =o=
  subst_var_pfun vctx n v (exprSemantics _ _ s ht_s).
Admitted.

Lemma substitution n s e ctx A {RA:OTRelation A}
      (ht: HasTypeC ctx A e)
      (ht_s: HasTypeC (ctxSuffix n ctx) (ctxNth n ctx) s)
      (ht_subst: HasTypeC (ctxDelete n ctx) A (substOExpr n s e)) :
  exprSemantics (ctxDelete n ctx) A (substOExpr n s e) ht_subst =o=
  compose_pfun (subst_pfun ctx n (exprSemantics _ _ s ht_s))
               (exprSemantics ctx A e ht).
Admitted.

Theorem OExpr_beta B {RB:OTRelation B} e1 e2 :
  oexpr_eq (OApp B (OLam e1) e2) (substOExpr 0 e2 e1).
Admitted.

FIXME HERE NOW: prove correctness of substitution!


FIXME HERE NOW: build quoting tactic
