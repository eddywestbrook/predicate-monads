Require Export PredMonad.Reflection.OrderedType.
Require Import Coq.Logic.ProofIrrelevance.

Import EqNotations.
Import ListNotations.
Import ProofIrrelevanceTheory.

(***
 *** Pairs of Types + Relations
 ***)

(* Shorthand for type + relation *)
Notation "'TpRel'" := (sigT OTRelation).

(* Shorthand for building type + relation pairs *)
Notation "'mkTpRel' A" := (existT OTRelation A _)
                            (left associativity, at level 20).

(* Shorthand for equalities on types + relations *)
Notation "A =t= B" := (existT OTRelation A%type _ = existT OTRelation B%type _)
                        (no associativity, at level 70).

(* OTRelation instance for the first projection of a type + relation pair *)
Instance OTRelation_projT1 (tprel:TpRel) : OTRelation (projT1 tprel) :=
  projT2 tprel.

(* A pfun that converts from an otype to an equal one *)
Definition eq_pfun A B {RA:OTRelation A} {RB:OTRelation B} (e:A =t= B) :
  A -o> B :=
  match e in _ = existT _ B _ with
  | eq_refl => id_pfun
  end.
Arguments eq_pfun {_ _ _ _} !e.

(* Composing two eq_pfuns composes the equality proofs *)
Lemma compose_eq_pfun {A B C}
      {RA:OTRelation A} {RB:OTRelation B} {RC:OTRelation C}
      (e1:A =t= B) (e2:B =t= C) (e3:A =t= C) :
  compose_pfun (eq_pfun e1) (eq_pfun e2) =o= eq_pfun e3.
Proof.
  assert (A =t= B) as e1'; [ assumption | ].
  assert (B =t= C) as e2'; [ assumption | ].
  revert e1 e2 e3; dependent rewrite e1'; dependent rewrite e2'; intros.
  repeat (rewrite (UIP_refl _ _ _); simpl).
  split; intros c1 c2 Rc; apply Rc.
Qed.

(* An eq_pfun on two equal types simplifies to the identity *)
Lemma eq_pfun_refl {A} {RA:OTRelation A} (e:A =t= A) : eq_pfun e = id_pfun.
Proof.
  rewrite (UIP_refl _ _ e). reflexivity.
Qed.

Lemma eqTpTupleR {A B C} {RA:OTRelation A} {RB:OTRelation B} {RC:OTRelation C} :
  A =t= B -> A*C =t= B*C.
Proof.
  intro e; dependent rewrite e; reflexivity.
Defined.

(* commute eq_pfun before a pfun_curry inside it *)
Lemma commute_eq_curry_pfun {A1 A2 B C}
      `{OType A1} `{OType A2} `{OTRelation B} `{OTRelation C}
      (e:A1 =t= A2) (f : (A2 * B) -o> C) :
  compose_pfun (eq_pfun e) (pfun_curry f) =o=
  pfun_curry (compose_pfun (eq_pfun (eqTpTupleR e)) f).
Proof.
  assert (A1 =t= A2) as e'; try assumption.
  revert H e f; dependent rewrite e'; intros.
  rewrite (UIP_refl _ _ e). simpl.
  split; intros x1 x2 Rx y1 y2 Ry; simpl; apply pfun_Proper; split; assumption.
Qed.

(* commute eq_pfun inside a pfun_apply *)
Lemma commute_eq_apply_pfun {A1 A2 B C}
      `{OTRelation A1} `{OTRelation A2} `{OTRelation B} `{OTRelation C}
      (e:A1 =t= A2) (f: A2 -o> B -o> C) g :
  compose_pfun (eq_pfun e) (pfun_apply f g) =o=
  pfun_apply (compose_pfun (eq_pfun e) f) (compose_pfun (eq_pfun e) g).
Proof.
  assert (A1 =t= A2) as e'; try assumption.
  revert e f g; dependent rewrite e'; intros. rewrite (UIP_refl _ _ _). simpl.
  split; intros x1 x2 Rx; simpl;
    assert (f @o@ x1 <o= f @o@ x2) as Rfx;
    try (apply pfun_Proper; assumption);
    apply Rfx; apply pfun_Proper; assumption.
Qed.

Lemma eq_pfun_adjoint_l {A1 A2 B}
      `{OTRelation A1} `{OTRelation A2} `{OTRelation B}
      (e12:A1 =t= A2) (e21:A2 =t= A1) f g :
  compose_pfun (eq_pfun e12) f =o= g <-> f =o= compose_pfun (eq_pfun e21) g.
Proof.
  assert (A1 =t= A2) as e'; try assumption.
  revert f g e12 e21; dependent rewrite <- e'; intros.
  rewrite (UIP_refl _ _ e12); rewrite (UIP_refl _ _ e21); simpl.
  split; intros [Rfg Rgf]; split; intros x y Rxy; simpl;
    first [ apply Rfg | apply Rgf ]; assumption.
Qed.

Lemma eq_pfun_adjoint_r {A1 A2 B}
      `{OTRelation A1} `{OTRelation A2} `{OTRelation B}
      (e12:A1 =t= A2) (e21:A2 =t= A1) f g :
  compose_pfun f (eq_pfun e12) =o= g <-> f =o= compose_pfun g (eq_pfun e21).
Proof.
  assert (A1 =t= A2) as e'; try assumption.
  revert f g e12 e21; dependent rewrite <- e'; intros.
  rewrite (UIP_refl _ _ e12); rewrite (UIP_refl _ _ e21); simpl.
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
  (CtxElem ctx1) =t= (CtxElem ctx2) :=
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
Lemma ctxNth_nil n : ctxNth n CtxNil =t= unit.
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
Fixpoint ctxInsert w W {RW:OTRelation W} ctx : Ctx :=
  match w with
  | 0 => CtxCons W ctx
  | S w' =>
    match ctx with
    | CtxNil => CtxCons unit (ctxInsert w' W CtxNil)
    | CtxCons B ctx' => CtxCons B (ctxInsert w' W ctx')
    end
  end.
Arguments ctxInsert !w W {RW} !ctx.

(* A context is valid iff its weakening with a valid OType is *)
Lemma ValidCtx_ctxInsert_iff n W `{OType W} ctx :
  ValidCtx ctx <-> ValidCtx (ctxInsert n W ctx).
Proof.
  split; revert ctx; induction n; intro ctx; destruct ctx; simpl; intro valid;
    repeat (lazymatch goal with | |- _ /\ _ => split | _ => idtac end);
    repeat (lazymatch goal with | H:_ /\ _ |- _ => destruct H | _ => idtac end);
    try typeclasses eauto; apply I.
Qed.

(* Weakening preserves validity *)
Instance ValidCtx_insert w W `{OType W} ctx {valid:ValidCtx ctx} :
  ValidCtx (ctxInsert w W ctx).
Proof.
  apply ValidCtx_ctxInsert_iff; assumption.
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
  ctxHead (ctxInsert (S n) A ctx) =t= ctxHead ctx.
Proof.
  destruct ctx; reflexivity.
Qed.

(* Map from a weaker to a stronger context, by dropping the new element *)
Fixpoint weaken_pfun w W {RW:OTRelation W} ctx :
  CtxElem (ctxInsert w W ctx) -o> CtxElem ctx :=
  match w return CtxElem (ctxInsert w W ctx) -o> CtxElem ctx with
  | 0 => fst_pfun (H:=OTRelation_CtxElem _)
  | S w' =>
    match ctx return CtxElem (ctxInsert (S w') W ctx) -o> CtxElem ctx with
    | CtxNil => const_pfun tt
    | CtxCons B ctx' =>
      pair_pfun (compose_pfun fst_pfun (weaken_pfun w' W ctx')) snd_pfun
    end
  end.
Arguments weaken_pfun !w W {RW} !ctx.

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
Lemma weaken_ctxNth w W {RW:OTRelation W} ctx n :
  ctxNth (weakenIndex w n) (ctxInsert w W ctx) =t= ctxNth n ctx.
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
Definition pfun_unit_eq_tt {A} {RA:OTRelation A} (f g: A -o> unit) : f =o= g.
  (* FIXME: why doesn't unit_eq_tt work without an arg on both sides? *)
  split; intros x y Rxy; repeat rewrite (unit_eq_tt (_ @o@ _));
    reflexivity.
Qed.

(* Weakening followed by nth is just the extended nth *)
Lemma weaken_nth_pfun w W `{OType W} ctx {valid:ValidCtx ctx} n :
  compose_pfun (weaken_pfun w W ctx) (nth_pfun ctx n)
  =o= compose_pfun (nth_pfun (ctxInsert w W ctx) (weakenIndex w n))
                   (eq_pfun (weaken_ctxNth w W ctx n)).
Proof.
  revert ctx valid n; induction w; intros; destruct ctx; destruct n; simpl;
    try apply pfun_unit_eq_tt; destruct valid.
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

Instance ValidCtx_ctxDelete n ctx {valid:ValidCtx ctx} :
  ValidCtx (ctxDelete n ctx).
Proof.
  revert n valid; induction ctx; intros n valid;
    [ | destruct n; destruct valid ]; simpl.
  - apply I.
  - assumption.
  - split; [ | apply IHctx ]; assumption.
Qed.

(* The the n+1-th suffix of a context *)
Fixpoint ctxSuffix n ctx {struct ctx} : Ctx :=
  match ctx with
  | CtxNil => CtxNil
  | CtxCons A ctx' =>
    match n with
    | 0 => ctx'
    | S n' => ctxSuffix n' ctx'
    end
  end.

Instance ValidCtx_ctxSuffix n ctx {valid:ValidCtx ctx} :
  ValidCtx (ctxSuffix n ctx).
Proof.
  revert n valid; induction ctx; intros n valid;
    [ | destruct n; destruct valid ]; simpl.
  - apply I.
  - assumption.
  - apply IHctx; assumption.
Qed.

Fixpoint subst_pfun ctx n :
  (CtxElem (ctxSuffix n ctx) -o> ctxNth n ctx) ->
  CtxElem (ctxDelete n ctx) -o> CtxElem ctx :=
  match ctx return
        (CtxElem (ctxSuffix n ctx) -o> ctxNth n ctx) ->
        CtxElem (ctxDelete n ctx) -o> CtxElem ctx with
  | CtxNil => fun s => const_pfun tt
  | CtxCons A ctx' =>
    match n return
        (CtxElem (ctxSuffix n (CtxCons A ctx')) -o> ctxNth n (CtxCons A ctx')) ->
        CtxElem (ctxDelete n (CtxCons A ctx')) -o> CtxElem (CtxCons A ctx')
    with
    | 0 => fun s => pair_pfun id_pfun s
    | S n' =>
      fun s =>
        pair_pfun (compose_pfun fst_pfun (subst_pfun ctx' n' s)) snd_pfun
    end
  end.

(* Helper shortcut for the repeated types in subst_var_pfun *)
Definition subst_var_tp ctx n v :=
  (CtxElem (ctxSuffix n ctx) -o> ctxNth n ctx) ->
  CtxElem (ctxDelete n ctx) -o> ctxNth v ctx.

(* Substitute into a variable v, which may or may not equal n *)
Fixpoint subst_var_pfun ctx n v {struct ctx} :
  (CtxElem (ctxSuffix n ctx) -o> ctxNth n ctx) ->
  CtxElem (ctxDelete n ctx) -o> ctxNth v ctx :=
  match ctx return subst_var_tp ctx n v with
  | CtxNil => fun s => const_pfun tt
  | CtxCons A ctx' =>
    match n return subst_var_tp (CtxCons A ctx') n v with
    | 0 =>
      match v return subst_var_tp (CtxCons A ctx') 0 v with
      | 0 => fun s => s
      | S v' => fun _ => nth_pfun ctx' v'
      end
    | S n' =>
      match v return subst_var_tp (CtxCons A ctx') (S n') v with
      | 0 => fun _ => snd_pfun
      | S v' =>
        fun s => compose_pfun fst_pfun (subst_var_pfun ctx' n' v' s)
      end
    end
  end.

Lemma subst_nth_pfun ctx n v s {valid:ValidCtx ctx} :
  compose_pfun (subst_pfun ctx n s) (nth_pfun ctx v) =o=
  subst_var_pfun ctx n v s.
Proof.
  revert n v s valid; induction ctx; intros;
    [ | destruct n; destruct v; destruct valid ]; simpl.
  - rewrite compose_const_pfun_f. reflexivity.
  - apply compose_pair_snd.
  - rewrite compose_compose_pfun. rewrite compose_pair_fst.
    rewrite id_compose_pfun. reflexivity.
  - apply compose_pair_snd.
  - rewrite compose_compose_pfun. rewrite compose_pair_fst.
    rewrite <- compose_compose_pfun. f_equiv. apply IHctx. assumption.
Qed.


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
    | 0 => OVar (ctxDelete n' (ctxTail vctx)) 0
    | S v' =>
      weakenOExpr 0 (ctxHead vctx) (substOVar n' s (ctxTail vctx) v')
    end
  end.

(* Substitution for ordered expressions *)
Fixpoint substOExpr n (s:OExpr) (e:OExpr) : OExpr :=
  match e with
  | OVar vctx v => substOVar n s vctx v
  | OEmbed ctx a => OEmbed (ctxDelete n ctx) a
  | OApp B f arg => OApp B (substOExpr n s f) (substOExpr n s arg)
  | OLam body => OLam (substOExpr (S n) s body)
  end.


FIXME HERE NOW: prove correctness of substitution!


FIXME HERE NOW: build quoting tactic
