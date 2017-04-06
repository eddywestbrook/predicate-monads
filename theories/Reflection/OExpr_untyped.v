Require Export PredMonad.Reflection.OrderedType.
Require Import Coq.Logic.ProofIrrelevance.

Import EqNotations.
Import ListNotations.
Import ProofIrrelevanceTheory.

(***
 *** Types + Relations
 ***)

(* A type plus a relation, bundled into a nice inductive type *)
Inductive TpRel : Type := | mkTpRel A {RA:OTRelation A}.

(* Accessor for the type of a TpRel *)
Definition tpRelType (tpRel:TpRel) : Type :=
  let (A,_) := tpRel in A.

(* Accessor for the OTRelation instance of a TpRel *)
Instance tpRelRel tpRel : OTRelation (tpRelType tpRel) :=
  match tpRel return OTRelation (tpRelType tpRel) with
  | @mkTpRel A RA => RA
  end.

(* A pfun that converts from an otype to an equal one *)
Definition eq_pfun {tprel1 tprel2:TpRel} (e:tprel1=tprel2) :
  tpRelType tprel1 -o> tpRelType tprel2 :=
  match e in _ = tprel2 with
  | eq_refl => id_pfun
  end.
Arguments eq_pfun {_ _} !e.

(* Composing two eq_pfuns composes the equality proofs *)
Lemma compose_eq_pfun {tprel1 tprel2 tprel3}
      (e1:tprel1=tprel2) (e2:tprel2=tprel3) (e3:tprel1=tprel3)
      {otype1:OType (tpRelType tprel1)} :
  compose_pfun (eq_pfun e1) (eq_pfun e2) =o= eq_pfun e3.
Proof.
  revert e2; destruct e1; intros.
  assert (OType (tpRelType tprel3)); [ rewrite <- e2; assumption | ].
  rewrite id_compose_pfun. rewrite (proof_irrelevance _ e2 e3).
  reflexivity.
Qed.

(* An eq_pfun on two equal types simplifies to the identity *)
Lemma eq_pfun_refl {tprel} (e:tprel=tprel) : eq_pfun e = id_pfun.
Proof.
  rewrite (UIP_refl _ _ e). reflexivity.
Qed.

Definition eqTpRelFst {tpRel1 tpRel2 A} {RA:OTRelation A} (e:tpRel1=tpRel2) :
  mkTpRel (tpRelType tpRel1 * A) = mkTpRel (tpRelType tpRel2 * A) :=
  rew [fun tprel =>
         mkTpRel (tpRelType tpRel1 * A) =
         mkTpRel (tpRelType tprel * A)]
      e in eq_refl.

(* commute eq_pfun inside a pfun_curry *)
Lemma commute_eq_curry_pfun {tpRel1 tpRel2 B C}
      {otype1:OType (tpRelType tpRel1)} {otype2:OType (tpRelType tpRel2)}
      `{OTRelation B} `{OTRelation C} (e:tpRel1=tpRel2)
      (f : (tpRelType tpRel2 * B) -o> C) :
  compose_pfun (eq_pfun e) (pfun_curry f) =o=
  pfun_curry (compose_pfun (eq_pfun (eqTpRelFst e)) f).
Proof.
  revert e f; destruct e; intros. simpl.
  split; intros x1 x2 Rx y1 y2 Ry; simpl; apply pfun_Proper; split; assumption.
Qed.

(* commute eq_pfun inside a pfun_apply *)
Lemma commute_eq_apply_pfun {tpRel1 tpRel2 B C}
      `{OTRelation B} `{OTRelation C} (e:tpRel1=tpRel2)
      (f: tpRelType tpRel2 -o> B -o> C) g :
  compose_pfun (eq_pfun e) (pfun_apply f g) =o=
  pfun_apply (compose_pfun (eq_pfun e) f) (compose_pfun (eq_pfun e) g).
Proof.
  revert e f g; destruct e; intros. simpl.
  split; intros x1 x2 Rx; simpl;
    assert (f @o@ x1 <o= f @o@ x2) as Rfx;
    try (apply pfun_Proper; assumption);
    apply Rfx; apply pfun_Proper; assumption.
Qed.

Lemma eq_pfun_adjoint_l {tprel1 tprel2 A} {RA:OTRelation A}
      (e:tprel1=tprel2) (e':tprel2=tprel1) f g :
  compose_pfun (eq_pfun e) f =o= g <-> f =o= compose_pfun (eq_pfun e') g.
Proof.
  revert e' f g; destruct e; intros. rewrite (UIP_refl _ _ e'). simpl.
  split; intros [Rfg Rgf]; split; intros x y Rxy; simpl;
    first [ apply Rfg | apply Rgf ]; assumption.
Qed.

Lemma eq_pfun_adjoint_r {tprel1 tprel2 A} {RA:OTRelation A}
      (e:tprel1=tprel2) (e':tprel2=tprel1) f g :
  compose_pfun f (eq_pfun e) =o= g <-> f =o= compose_pfun g (eq_pfun e').
Proof.
  revert e' f g; destruct e; intros. rewrite (UIP_refl _ _ e'). simpl.
  split; intros [Rfg Rgf]; split; intros x y Rxy; simpl;
    first [ apply Rfg | apply Rgf ]; assumption.
Qed.


(***
 *** Ordered Type Contexts
 ***)

(* A context here is just a list of types *)
Inductive Ctx : Type :=
| CtxNil
| CtxCons A `{OTRelation A} (ctx:Ctx)
.

(* An element of a context is a nested tuple of elements of its types *)
Fixpoint CtxElem (ctx:Ctx) : Type :=
  match ctx with
  | CtxNil => unit
  | CtxCons A ctx' => CtxElem ctx' * A
  end.

(* OTRelation instance for any CtxElem type *)
Instance OTRelation_CtxElem ctx : OTRelation (CtxElem ctx).
Proof.
  induction ctx.
  - apply OTunit_R.
  - apply OTpair_R; assumption.
Defined.

(* A context is valid iff each ordered type in it is valid *)
Fixpoint ValidCtxF ctx : Prop :=
  match ctx with
  | CtxNil => True
  | CtxCons A ctx' =>
    OType A /\ ValidCtxF ctx'
  end.

(* Typeclass version of ValidCtxF *)
Class ValidCtx ctx : Prop := validCtx : ValidCtxF ctx.

(* Instances for building ValidCtx proofs *)
Instance ValidCtx_Nil : ValidCtx CtxNil := I.
Instance ValidCtx_Cons A `{OType A} ctx (vc:ValidCtx ctx) :
  ValidCtx (CtxCons A ctx) := conj _ vc.

(* OType instance of CtxElem of a valid context *)
Instance OType_CtxElem ctx (valid:ValidCtx ctx) : OType (CtxElem ctx).
Proof.
  induction ctx; [ | destruct valid ]; typeclasses eauto.
Qed.

(* Convert an equality on context to one on CtxElems *)
Definition eqCtxElem {ctx1 ctx2} (e:ctx1=ctx2) :
  mkTpRel (CtxElem ctx1) = mkTpRel (CtxElem ctx2) :=
  match e in _ = ctx2 with
  | eq_refl => eq_refl
  end.

(* Helper pfun that converts between equal contexts *)
Definition eq_ctx_pfun {ctx1 ctx2} e : CtxElem ctx1 -o> CtxElem ctx2 :=
  eq_pfun (eqCtxElem e).
Arguments eq_ctx_pfun {_ _ } e /.

(* Get the head type of a context, defaulting to unit *)
Definition ctxHead ctx : Type :=
  match ctx with
  | CtxNil => unit
  | CtxCons A _ => A
  end.

Instance OTRelation_ctxHead ctx : OTRelation (ctxHead ctx) :=
  match ctx with
  | CtxNil => _
  | CtxCons _ _ => _
  end.

Instance OType_ctxHead ctx `{valid:ValidCtx ctx} : OType (ctxHead ctx).
Proof.
  destruct ctx.
  - typeclasses eauto.
  - exact (proj1 valid).
Qed.

(* Get the tail of a context, defaulting to the empty context *)
Definition ctxTail ctx :=
  match ctx with
  | CtxNil => CtxNil
  | CtxCons _ ctx' => ctx'
  end.

Instance ValidCtx_ctxTail ctx `{valid:ValidCtx ctx} : ValidCtx (ctxTail ctx).
Proof.
  destruct ctx.
  - typeclasses eauto.
  - exact (proj2 valid).
Qed.

(* Non-nil contexts equal cons of their heads and tails *)
Lemma ctx_eq_head_tail ctx :
  ctx <> CtxNil -> ctx = CtxCons (ctxHead ctx) (ctxTail ctx).
  destruct ctx; intro e.
  elimtype False; apply e; reflexivity.
  reflexivity.
Qed.

(* Look up the nth type in a Ctx, returning the unit type as a default *)
Fixpoint ctxNth n ctx {struct ctx} : Type :=
  match ctx with
  | CtxNil => unit
  | CtxCons A ctx' =>
    match n with
    | 0 => A
    | S n' => ctxNth n' ctx'
    end
  end.
Arguments ctxNth !n !ctx.

(* The OTRelation for the nth type in a context *)
Instance OTRelation_ctxNth n ctx : OTRelation (ctxNth n ctx).
Proof.
  revert n; induction ctx; intros; simpl; try typeclasses eauto.
  destruct n; simpl; typeclasses eauto.
Defined.
Arguments OTRelation_ctxNth !n !ctx.

(* For valid contexts, the nth element is a valid OType *)
Instance OType_ctxNth n ctx `{valid:ValidCtx ctx} : OType (ctxNth n ctx).
Proof.
  revert n valid; induction ctx; intros; simpl; try typeclasses eauto.
  destruct valid. destruct n; try assumption. apply IHctx; apply H1.
Qed.

(* The ctxNth of nil is always unit *)
Lemma ctxNth_nil n : mkTpRel (ctxNth n CtxNil) = mkTpRel unit.
Proof.
  induction n; reflexivity.
Qed.

(* Pfun to extract the nth element of a context *)
Fixpoint nth_pfun ctx n : CtxElem ctx -o> ctxNth n ctx :=
  match ctx return CtxElem ctx -o> ctxNth n ctx with
  | CtxNil => const_pfun tt
  | CtxCons A ctx' =>
    match n return CtxElem (CtxCons A ctx') -o> ctxNth n (CtxCons A ctx') with
    | 0 => snd_pfun
    | S n' => compose_pfun fst_pfun (nth_pfun ctx' n')
    end
  end.
Arguments nth_pfun !ctx !n.

(* Appending contexts *)
(* FIXME: is this needed? *)
Fixpoint appendCtx ctx1 ctx2 : Ctx :=
  match ctx1 with
  | CtxNil => ctx2
  | CtxCons A ctx1' =>
    CtxCons A (appendCtx ctx1' ctx2)
  end.

(* Context length *)
(* FIXME: is this needed? *)
Fixpoint ctxLen ctx :=
  match ctx with
  | CtxNil => 0
  | CtxCons A ctx' => S (ctxLen ctx')
  end.


(***
 *** Context Insertion, aka Weakening
 ***)

(* Weaken a context by inserting a type at point w *)
Fixpoint ctxInsert w A {RA:OTRelation A} ctx : Ctx :=
  match w with
  | 0 => CtxCons A ctx
  | S w' =>
    match ctx with
    | CtxNil => CtxCons unit (ctxInsert w' A CtxNil)
    | CtxCons B ctx' => CtxCons B (ctxInsert w' A ctx')
    end
  end.
Arguments ctxInsert !w A {RA} !ctx.

(* Weakening preserves validity *)
Instance ValidCtx_insert w A `{OType A} ctx {valid:ValidCtx ctx} :
  ValidCtx (ctxInsert w A ctx).
Proof.
  revert ctx valid; induction w; intros; destruct ctx; try typeclasses eauto.
  destruct valid. split; [ | apply IHw ]; assumption.
Qed.

(* Map from a weaker to a strong context, by dropping the new element *)
Fixpoint insert_pfun w A {RA:OTRelation A} ctx :
  CtxElem (ctxInsert w A ctx) -o> CtxElem ctx :=
  match w return CtxElem (ctxInsert w A ctx) -o> CtxElem ctx with
  | 0 => fst_pfun (H:=OTRelation_CtxElem _)
  | S w' =>
    match ctx return CtxElem (ctxInsert (S w') A ctx) -o> CtxElem ctx with
    | CtxNil => const_pfun tt
    | CtxCons B ctx' =>
      pair_pfun (compose_pfun fst_pfun (insert_pfun w' A ctx')) snd_pfun
    end
  end.
Arguments insert_pfun !w A {RA} !ctx.

(* Weaken an index in a context, to make ctxNth commute with ctxInsert *)
Fixpoint weakenIndex w (n:nat) {struct w} : nat :=
  match w with
  | 0 => S n
  | S w' =>
    match n with
    | 0 => 0
    | S n' => S (weakenIndex w' n')
    end
  end.
Arguments weakenIndex !w !n.

(* Weakening commutes with ctxNth *)
Lemma weaken_ctxNth w A {RA:OTRelation A} ctx n :
  mkTpRel (ctxNth (weakenIndex w n) (ctxInsert w A ctx)) = mkTpRel (ctxNth n ctx).
Proof.
  revert ctx n; induction w; intros; destruct ctx; simpl.
  - reflexivity.
  - reflexivity.
  - destruct n; simpl; try reflexivity. rewrite <- (ctxNth_nil n). apply IHw.
  - destruct n; simpl; try reflexivity. apply IHw.
Qed.

(* FIXME: put this somewhere more appropriate *)
Lemma unit_eq_tt (x:unit) : x =o= tt.
Proof.
  destruct x; reflexivity.
Qed.

(* FIXME: put this somewhere more appropriate *)
Definition pfun_unit_eq {A} {RA:OTRelation A} (f g: A -o> unit) : f =o= g.
  (* FIXME: why doesn't unit_eq_tt work without an arg on both sides? *)
  split; intros x y Rxy; repeat rewrite (unit_eq_tt (_ @o@ _));
    reflexivity.
Qed.

(* Insertion followed by nth is just the extended nth *)
Lemma insert_nth_pfun w A `{OType A} ctx {valid:ValidCtx ctx} n :
  compose_pfun (insert_pfun w A ctx) (nth_pfun ctx n)
  =o= compose_pfun (nth_pfun (ctxInsert w A ctx) (weakenIndex w n))
                   (eq_pfun (weaken_ctxNth w A ctx n)).
Proof.
  revert ctx valid n; induction w; intros; destruct ctx; destruct n; simpl;
    try apply pfun_unit_eq; destruct valid.
  - rewrite eq_pfun_refl. rewrite compose_id_pfun. reflexivity.
  - rewrite eq_pfun_refl. rewrite compose_id_pfun. reflexivity.
  - rewrite eq_pfun_refl. rewrite compose_pair_snd.
    rewrite compose_id_pfun. reflexivity.
  - rewrite compose_compose_pfun. rewrite compose_pair_fst.
    rewrite <- compose_compose_pfun. rewrite IHw; try assumption.
    rewrite compose_compose_pfun. f_equiv. f_equiv. apply proof_irrelevance.
Qed.


(***
 *** Context Deletion, aka Substitution
 ***)

(* Delete the nth element of a context *)
Fixpoint ctxDelete n ctx {struct ctx} : Ctx :=
  match ctx with
  | CtxNil => CtxNil
  | CtxCons A ctx' =>
    match n with
    | 0 => ctx'
    | S n' => CtxCons A (ctxDelete n' ctx')
    end
  end.
Arguments ctxDelete !n !ctx.

(* FIXME: explain this... *)
Fixpoint delete_pfun ctx n :
  CtxElem (ctxDelete n ctx) * ctxNth n ctx -o> CtxElem ctx :=
  match ctx return
        CtxElem (ctxDelete n ctx) * ctxNth n ctx -o> CtxElem ctx with
  | CtxNil => fst_pfun
  | CtxCons A ctx' =>
    match n return
          CtxElem (ctxDelete n (CtxCons _ _)) * ctxNth n (CtxCons _ _) -o>
          CtxElem (CtxCons A ctx') with
    | 0 => id_pfun
    | S n' =>
      pair_pfun
        (compose_pfun
           (pair_pfun (compose_pfun fst_pfun fst_pfun) snd_pfun)
           (delete_pfun ctx' n'))
        (compose_pfun fst_pfun snd_pfun)
    end
  end.
Arguments delete_pfun !ctx !n.


(***
 *** Ordered Expressions
 ***)

(* Ordered expressions to represent proper functions *)
Inductive OExpr : Type :=
| OVar (ctx:Ctx) (n:nat)
| OEmbed (ctx:Ctx) {A} {RA:OTRelation A} (a:A)
| OApp (B:Type) {RB:OTRelation B} (e1 e2 : OExpr)
| OLam (e: OExpr)
.

Fixpoint OExpr_ctx e : Ctx :=
  match e with
  | OVar ctx _ => ctx
  | @OEmbed ctx _ _ _ => ctx
  | OApp _ _ arg => OExpr_ctx arg
  | OLam f => ctxTail (OExpr_ctx f)
  end.
Arguments OExpr_ctx !e.

Fixpoint OExpr_TpRel e : TpRel :=
  match e with
  | OVar ctx n => mkTpRel (ctxNth n ctx)
  | @OEmbed _ A _ _ => mkTpRel A
  | OApp B _ _ => mkTpRel B
  | OLam f =>
    mkTpRel (ctxHead (OExpr_ctx f) -o> tpRelType (OExpr_TpRel f))
  end.
Arguments OExpr_TpRel !e.

Definition OExpr_type e := tpRelType (OExpr_TpRel e).
Arguments OExpr_type e /.

Instance OTRelation_OExpr_type e : OTRelation (OExpr_type e) := _.
Arguments OTRelation_OExpr_type e /.


(***
 *** Typing for Ordered Expressions
 ***)

(* Proof that an ordered expression is well-typed *)
Fixpoint HasType ctx tpRel (e:OExpr) : Prop :=
  match e with
  | OVar ctx' v =>
    ValidCtx ctx /\ (ctx = ctx' /\ mkTpRel (ctxNth v ctx') = tpRel)
  | @OEmbed ctx' A _ a =>
    (ValidCtx ctx /\ OType A) /\
    (ctx = ctx' /\ mkTpRel A = tpRel)
  | OApp B f arg =>
    (mkTpRel B = tpRel /\ OType B) /\
    (HasType ctx (mkTpRel (OExpr_type arg -o> tpRelType tpRel)) f /\
     HasType ctx (OExpr_TpRel arg) arg)
  | OLam f =>
    (ctx = ctxTail (OExpr_ctx f) /\
     mkTpRel (ctxHead (OExpr_ctx f) -o> OExpr_type f) = tpRel) /\
    (HasType (CtxCons (ctxHead (OExpr_ctx f)) (ctxTail (OExpr_ctx f)))
            (mkTpRel (OExpr_type f)) f /\
     (OExpr_ctx f <> CtxNil /\ ValidCtx (OExpr_ctx f)))
  end.
Arguments HasType ctx tpRel !e.

(* Typeclass version of HasType *)
Class HasTypeC ctx tpRel e : Prop := hasType : HasType ctx tpRel e.

(* Expressions can only be typed in their one context *)
Lemma HasType_ctx_eq ctx tpRel e : HasType ctx tpRel e -> ctx = OExpr_ctx e.
  revert ctx tpRel; induction e.
  - intros ctx' tpRel [valid [ctx_eq tp_eq]]. assumption.
  - intros ctx' tpRel [[valid otype] [ctx_eq tp_eq]]. assumption.
  - intros ctx' tpRel [[tp_eq otype] [ht1 ht2]]. apply (IHe2 _ _ ht2).
  - intros ctx' tpRel [[ctx_eq tp_eq] [ctx_neq_nil ht_e]]. assumption.
Qed.

(* Expressions can only have their one type and one context *)
Lemma HasType_tp_eq ctx tpRel e :
  HasType ctx tpRel e -> tpRel = OExpr_TpRel e.
  revert ctx tpRel; induction e.
  - intros ctx' tpRel [ valid [ ctx_eq tp_eq ]]. symmetry; assumption.
  - intros ctx' tpRel [[valid otype] [ctx_eq tp_eq]]. symmetry; assumption.
  - intros ctx' tpRel [[tp_eq otype] [ht1 ht2]]. symmetry; assumption.
  - intros ctx' tpRel [[ctx_eq tp_eq] [ctx_neq_nil ht_e]]. symmetry; assumption.
Qed.

Instance ValidCtx_OExpr_ctx ctx tpRel e (ht:HasTypeC ctx tpRel e) :
  ValidCtx (OExpr_ctx e).
Proof.
  revert ctx tpRel ht; induction e.
  - intros ctx' tpRel [ valid [ ctx_eq _ ]]. rewrite <- ctx_eq; assumption.
  - intros ctx' tpRel [[valid _] [ctx_eq _]]. rewrite <- ctx_eq; assumption.
  - intros ctx' tpRel [[tp_eq otype] [ht1 ht2]]. apply (IHe2 _ _ ht2).
  - intros ctx' tpRel [[ctx_eq tp_eq] [ctx_neq_nil ht_e]]. typeclasses eauto.
Qed.

Instance ValidCtx_HasTypeC ctx tpRel e (ht:HasTypeC ctx tpRel e) :
  ValidCtx ctx.
Proof.
  rewrite (HasType_ctx_eq _ _ _ ht). typeclasses eauto.
Qed.

(* Any well-typed expression has a valid type *)
Instance OType_OExpr_type ctx tpRel e (ht:HasTypeC ctx tpRel e) :
  OType (OExpr_type e).
Proof.
  revert ctx tpRel ht; induction e; intros.
  - destruct ht as [valid [ctx_eq _]]; rewrite <- ctx_eq; typeclasses eauto.
  - destruct ht as [[valid otype] _]. assumption.
  - destruct ht as [[ctx_eq otype] _]. assumption.
  - destruct ht as [[ctx_eq tp_eq] [ctx_neq_nil ht_e]]. typeclasses eauto.
Qed.

Instance OType_semTp_HasTypeC ctx tpRel e (ht:HasTypeC ctx tpRel e) :
  OType (tpRelType tpRel).
Proof.
  rewrite (HasType_tp_eq _ _ _ ht). typeclasses eauto.
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
Definition Semantics ctx tpRel : Type :=
  CtxElem ctx -o> tpRelType tpRel.
Arguments Semantics ctx tpRel /.

(* Helper function to coerce a Semantics type *)
Definition coerceSemantics {ctx1 ctx2 tpRel1 tpRel2}
           (pf:ctx2 = ctx1 /\ tpRel1 = tpRel2) (sem:Semantics ctx1 tpRel1) :
  Semantics ctx2 tpRel2 :=
  compose_pfun (eq_ctx_pfun (proj1c pf))
               (compose_pfun sem (eq_pfun (proj2c pf))).
Arguments coerceSemantics {_ _ _ _} pf sem/.

(* The semantics of a well-typed expression *)
Program Fixpoint exprSemantics ctx tpRel e :
  HasTypeC ctx tpRel e -> Semantics ctx tpRel :=
  match e return HasType ctx tpRel e -> Semantics ctx tpRel with
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
        (exprSemantics ctx (mkTpRel (OExpr_type arg -o> tpRelType tpRel)) f
                       (proj1c (proj2c ht)))
        (exprSemantics ctx (OExpr_TpRel arg) arg
                       (proj2c (proj2c ht)))
  | OLam f =>
    fun ht =>
      coerceSemantics
        (proj1c ht)
        (pfun_curry
           (H:= _ )
           (exprSemantics (CtxCons _ _) (mkTpRel (OExpr_type f))
                          f
                          (proj1c (proj2c ht))))
  end.
Next Obligation.
  apply OType_CtxElem. apply ValidCtx_ctxTail. assumption.
Defined.
Arguments exprSemantics ctx tpRel !e.


(***
 *** Relating Ordered Expressions
 ***)

(* Proposition that two expressions have the same set of types *)
Definition equiTyped e1 e2 : Prop :=
  forall ctx tpRel, HasType ctx tpRel e1 <-> HasType ctx tpRel e2.

Instance Equivalence_equiTyped : Equivalence equiTyped.
Proof.
  split.
  - intros x ctx tpRel; reflexivity.
  - intros x y equi ctx tpRel; symmetry; apply equi.
  - intros e1 e2 e3 equi12 equi23 ctx tpRel.
    transitivity (HasType ctx tpRel e2); [ apply equi12 | apply equi23 ].
Qed.

(* Equi-typed expressions have the same contexts *)
Lemma equiTyped_eq_ctx e1 e2 (equi:equiTyped e1 e2)
      ctx tpRel (ht:HasType ctx tpRel e1) :
  OExpr_ctx e1 = OExpr_ctx e2.
  rewrite <- (HasType_ctx_eq _ _ _ ht).
  apply (HasType_ctx_eq _ _ _ (proj1 (equi ctx tpRel) ht)).
Qed.

(* Equi-typed expressions have the same canonical types *)
Lemma equiTyped_eq_TpRel e1 e2 (equi:equiTyped e1 e2)
      ctx tpRel (ht:HasType ctx tpRel e1) :
  OExpr_TpRel e1 = OExpr_TpRel e2.
  rewrite <- (HasType_tp_eq _ _ _ ht).
  apply (HasType_tp_eq _ _ _ (proj1 (equi ctx tpRel) ht)).
Qed.

Record oexpr_R (e1 e2:OExpr) : Prop :=
  { oexpr_R_ht : equiTyped e1 e2;
    oexpr_R_R :
      forall ctx tpRel ht1 ht2,
        exprSemantics ctx tpRel e1 ht1 <o= exprSemantics ctx tpRel e2 ht2 }.

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
    transitivity (exprSemantics ctx tpRel e2 (proj1 (ht12 _ _) ht1));
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
  { intros ctx' tpRel [[valid1 otype1] [eq_ctx eq_tp]] ht2.
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
  intros f1 f2 equi_f arg1 arg2 equi_arg ctx tpRel.
  split; intros [ [semTp_eq otype_b] [ht_f' ht_arg'] ]; split; split;
    try assumption; simpl.
  { apply equi_f.
    rewrite (equiTyped_eq_TpRel
               arg2 arg1 (symmetry equi_arg) _ _
               (proj1 (equi_arg _ _) ht_arg')); assumption. }
  { apply equi_arg.
    rewrite (equiTyped_eq_TpRel
               arg2 arg1 (symmetry equi_arg) _ _
               (proj1 (equi_arg _ _) ht_arg')); assumption. }
  { apply equi_f.
    rewrite (equiTyped_eq_TpRel
               arg1 arg2 equi_arg _ _
               (proj2 (equi_arg _ _) ht_arg')); assumption. }
  { apply equi_arg.
      rewrite (equiTyped_eq_TpRel
                 arg1 arg2 equi_arg _ _
                 (proj2 (equi_arg _ _) ht_arg')); assumption. }
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
    - apply (rf ctx (mkTpRel (_ -o> _))).
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
  { intros ctx tpRel [[eq_ctx1 eq_tp1] [ht_e1 [neq_nil1 valid1]]]
           [[eq_ctx2 eq_tp2] [ht_e2 [neq_nil2 valid2]]]; simpl.
    revert eq_ctx2 eq_tp2 neq_nil2 valid2 ht_e2; simpl.
    rewrite <- (equiTyped_eq_ctx e1 e2 equi_e _ _ ht_e1).
    rewrite <- (equiTyped_eq_TpRel e1 e2 equi_e _ _ ht_e1).
    intros. rewrite (proof_irrelevance _ eq_tp2 eq_tp1).
    rewrite (proof_irrelevance _ eq_ctx2 eq_ctx1).
    repeat f_equiv.
    - rewrite eq_ctx1. reflexivity.
    - apply (re _ _ ht_e1 ht_e2).
    - rewrite <- eq_tp1. reflexivity. }
Qed.


(***
 *** Weakening for Ordered Expressions
 ***)

(* Weakening / lifting of ordered expressions *)
Fixpoint weakenOExpr n A {RA:OTRelation A} (e:OExpr) : OExpr :=
  match e with
  | OVar ctx v => OVar (ctxInsert n A ctx) (weakenIndex n v)
  | OEmbed ctx a => OEmbed (ctxInsert n A ctx) a
  | OApp B f arg =>
    OApp B (weakenOExpr n A f) (weakenOExpr n A arg)
  | OLam f => OLam (weakenOExpr (S n) A f)
  end.
Arguments weakenOExpr n A {RA} !e.

FIXME HERE NOW: keep updating things to use TpRel instead of SemType;
maybe get rid of TpRel as well, and use existT pairs?


(* Weakening a semantic type *)
Definition weakenSemType n A {RA:OTRelation A} semTp : SemType :=
  {| semCtx := ctxInsert n A (semCtx semTp);
     semType := semType semTp; sem_OTRelation := _ |}.
Arguments weakenSemType n A {RA} semTp /.

(* A context is valid iff its weakening with a valid OType is *)
Lemma ValidCtx_ctxInsert_iff n A `{OType A} ctx :
  ValidCtx ctx <-> ValidCtx (ctxInsert n A ctx).
Proof.
  split; revert ctx; induction n; intros ctx valid; destruct ctx; simpl.
  - typeclasses eauto.
  - typeclasses eauto.
  - typeclasses eauto.
  - destruct (ValidCtxInd_inversion _ _ valid);
      constructor; [ | apply IHn ]; assumption.
  - typeclasses eauto.
  - destruct (ValidCtxInd_inversion _ _ valid); assumption.
  - apply ValidCtx_Nil.
  - simpl in valid. destruct (ValidCtxInd_inversion _ _ valid).
    constructor; [ | apply IHn ]; assumption.
Qed.

(* Instance version of the left-to-right of the above *)
Instance ValidCtx_ctxInsert n A `{OType A} ctx `{ValidCtx ctx} :
  ValidCtx (ctxInsert n A ctx).
Proof.
  apply ValidCtx_ctxInsert_iff; assumption.
Qed.

(* Weakening commutes with ctxNth *)
(*
Lemma weaken_ctxNth n A {RA:OTRelation A} ctx v :
  ctxNth (weakenIndex n v) (ctxInsert n A ctx) = ctxNth v ctx.
  revert ctx v; induction n; intros; [ | destruct ctx; destruct v ];
    simpl; try reflexivity; apply IHn.
Qed.
*)

(* ctxNth is the same after weakening as before *)
Lemma weaken_ctxNth n A {RA:OTRelation A} ctx v :
  mkTpRel (ctxNth (weakenIndex n v) (ctxInsert n A ctx))
  = mkTpRel (ctxNth v ctx).
  revert ctx v; induction n; intros; [ | destruct ctx; destruct v ];
    try reflexivity; simpl.
  - apply IHn.
  - apply IHn.
Qed.

(* ctxInsert commutes with ctxTail by incrementing the weakening position *)
Lemma ctxInsert_ctxTail n A {RA:OTRelation A} ctx :
  ctxInsert n A (ctxTail ctx) = ctxTail (ctxInsert (S n) A ctx).
Proof.
  revert ctx; induction n; intros; destruct ctx; reflexivity.
Qed.

(* The head of a weakened context at non-zero position is just the head of the
original context *)
Lemma ctxHead_ctxInsert_S n A {RA:OTRelation A} ctx :
  existT OTRelation (ctxHead (ctxInsert (S n) A ctx)) _ =
  existT OTRelation (ctxHead ctx) _.
Proof.
  destruct ctx; reflexivity.
Qed.

(* The type of a weakened expression is just the weakening of its type *)
Lemma weaken_OExpr_type n A {RA:OTRelation A} e :
  OExpr_SemType (weakenOExpr n A e) = weakenSemType n A (OExpr_SemType e).
  revert n; induction e; simpl; intros.
  { apply split_eqSemType; [ reflexivity | apply weaken_ctxNth ]. }
  { reflexivity. }
  { rewrite (eqSemCtx (IHe2 _)). reflexivity. }
  { rewrite (IHe _). rewrite ctxInsert_ctxTail.
    unfold weakenSemType; simpl.
    generalize (semCtx (OExpr_SemType e)); intro.
    dependent rewrite (ctxHead_ctxInsert_S n A c).
    reflexivity. }
Qed.

Lemma weaken_HasTypeVar n A {RA:OTRelation A} ctx tpRel v :
  HasTypeVar ctx tpRel v ->
  HasTypeVar (ctxInsert n A ctx) tpRel (weakenIndex n v).
Proof.
  revert ctx tpRel v; induction n; intros; destruct ctx; destruct v;
    try assumption; simpl.
  - apply IHn. assumption.
  - apply IHn. assumption.
Qed.

Lemma weaken_HasType n A `{OType A} semTp e :
  HasType semTp e -> HasType (weakenSemType n A semTp) (weakenOExpr n A e).
  revert n semTp; induction e; intros n0 semTp.
  { intros [ valid [ ctx_eq htv ]]; split; [ | split ].
    - typeclasses eauto.
    - simpl; rewrite ctx_eq; reflexivity.
    - apply weaken_HasTypeVar; assumption. }
  { intros [ valid [ otype eq_semTp ]]; split; [ | split ].
    - typeclasses eauto.
    - assumption.
    - rewrite <- eq_semTp. reflexivity. }
  { intros [[ eq_semTp otype ] [ ht1 ht2 ]]; split; split.
    - rewrite eq_semTp; reflexivity.
    - assumption.
    - simpl. rewrite weaken_OExpr_type.
      change
        (HasType (weakenSemType n0 A
                                {| semCtx := semCtx semTp;
                                   semType := semType (OExpr_SemType e2) -o>
                                              semType semTp;
                                   sem_OTRelation := _ |}) (weakenOExpr n0 A e1)).
      apply IHe1; assumption.
    - simpl. rewrite weaken_OExpr_type. unfold weakenSemType; simpl.
      change (HasType (weakenSemType n0 A
                                     {| semCtx := semCtx semTp;
                                        semType := semType (OExpr_SemType e2);
                                        sem_OTRelation := _ |})
                      (weakenOExpr n0 A e2)).
      apply IHe2; assumption. }
  { intros [ eq_semTp [ ctx_neq_nil hte ]]; split; [ | split ].
    - simpl. rewrite weaken_OExpr_type.
      unfold weakenSemType; simpl.
      rewrite <- ctxInsert_ctxTail.
      dependent rewrite (ctxHead_ctxInsert_S n0 A (semCtx (OExpr_SemType e))).
      rewrite <- eq_semTp; simpl. reflexivity.
    - simpl. rewrite weaken_OExpr_type. unfold weakenSemType; simpl.
      case_eq (semCtx (OExpr_SemType e)); intros;
        [ elimtype False; apply ctx_neq_nil; assumption | ].
      discriminate.
    - rewrite weaken_OExpr_type. apply IHe. assumption. }
Qed.


(* Weakening a semantic value *)
Definition weakenSemantics n A {RA:OTRelation A} semTp (sem:Semantics semTp) :
  Semantics (weakenSemType n A semTp) :=
  compose_pfun (pfun_weakening n A (semCtx semTp)) sem.
Arguments weakenSemantics n A {RA} semTp sem /.

Lemma var_weakening n A `{OType A} ctx `{ValidCtx ctx}
      tpRel {otype:OType (tpRelType tpRel)}
      v htv htv_w :
  compose_pfun (pfun_weakening n A ctx) (varSemantics ctx tpRel v htv)
  =o=
  varSemantics (ctxInsert n A ctx) tpRel (weakenIndex n v) htv_w.
Proof.
  revert n v htv htv_w; induction ctx; intros; [ | destruct n; destruct v ].
  - revert htv htv_w; destruct htv; intros; apply pfun_unit_eq.
  - revert htv htv_w; destruct htv; simpl in * |- *; intros.
    rewrite (UIP_refl _ _ htv_w).
    destruct (ValidCtxInd_inversion _ _ H0).
    reflexivity.
  - simpl in * |- *. rewrite (proof_irrelevance _ htv htv_w).
    destruct (ValidCtxInd_inversion _ _ H0). reflexivity.
  - simpl in * |- *. rewrite (proof_irrelevance _ htv_w htv).
    destruct (ValidCtxInd_inversion _ _ H0).
    rewrite compose_compose_pfun. rewrite compose_pair_snd. reflexivity.
  - simpl in * |- *. destruct (ValidCtxInd_inversion _ _ H0).
    rewrite compose_compose_pfun. rewrite compose_pair_fst.
    rewrite <- compose_compose_pfun. rewrite IHctx; [ | assumption ].
    reflexivity.
Qed.

Lemma weakeaning n A `{OType A} semTp e ht ht_w :
  exprSemantics _ (weakenOExpr n A e) ht_w =o=
  weakenSemantics n A _ (exprSemantics semTp e ht).
  revert n ht ht_w; induction e.
  { intros n0 htv htv_w. simpl. symmetry. rewrite <- var_weakening.
    - reflexivity.
    - assumption.
    - destruct htv as [ valid [ eq_ctx htv ]]. rewrite eq_ctx. assumption.
    - destruct htv as [ valid [ eq_ctx htv ]]. simpl. unfold semTpRel in htv.
      rewrite eq_ctx in htv.
      apply (HasTypeVar_OType _ _ _ htv). }
  { intros n [ valid [ otype eq_semTp ]]; rewrite <- eq_semTp.
    intros [ valid_w [ otype_w eq_semTp_w ]]; simpl in * |- *.
    rewrite (UIP_refl _ _ eq_semTp_w). unfold coerceSemantics; simpl.
    repeat rewrite id_compose_pfun.
    repeat rewrite compose_const_pfun_f. symmetry.
    apply compose_f_const_pfun. typeclasses eauto. }
  { intros n [[eq_semTp otype] [ht1 ht2]]. revert ht1 ht2. simpl.
    rewrite eq_semTp; simpl.

FIXME HERE NOW: maybe get rid of SemTypes, and use TpRels instead?


 [[eq_semTp_w otype_w] [ht1_w ht2_w]];
      simpl in * |- *.
    assert (ValidCtx (semCtx semTp));
      [ apply (ValidCtx_semTp_HasTypeC _ _ ht1) | ].
    assert (OType (semType semTp));  [ rewrite eq_semTp; assumption | ].
    rewrite compose_pfun_apply.
    rewrite eq_semTp.
    refine (Proper_pfun_apply_equiv _ _ _ _ _ _ _ _ _).

    rewrite eq_semTp in IHe1; simpl in IHe1.
    rewrite <- IHe1.


(***
 *** Substitution for Ordered Expressions
 ***)


(* Substitution for ordered expression variables *)
(* FIXME HERE: write this!
Fixpoint substOVar n w_ctx (s:OExpr) v : OExpr :=
  match n with
  | 0 =>
    match v with
    | 0 => weakenOExpr 0 w_ctx s
    | S v' => OVar v'
    end
  | S n' =>
    match v with
    | 0 => OVar lifting
    | S v' =>
      substOVar n' (S lifting) s v
    end
  end.
*)

(* Substitution for ordered expressions *)
(*
Fixpoint substOExpr n (s:OExpr) (e:OExpr) : OExpr :=
  match e with
  | OVar v => substOVar n CtxNil s v
  | OEmbed a => OEmbed a
  | OApp A B f arg => OApp A B (substOExpr n s f) (substOExpr n s arg)
  | OLam A B body => OLam A B (substOExpr (S n) s body)
  end.
 *)



FIXME HERE NOW:
- prove beta rewrite rule(s)
- build quoting tactic
