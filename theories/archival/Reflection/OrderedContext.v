Require Export PredMonad.Reflection.OrderedType.
Require Export Coq.Logic.ProofIrrelevance.

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
Defined.

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
Defined.

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
Defined.

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

(* FIXME: move these somewhere sensible! *)
Ltac destruct_ands :=
  repeat (lazymatch goal with | H:_ /\ _ |- _ => destruct H | _ => idtac end).
Ltac split_ands :=
  repeat (lazymatch goal with | |- _ /\ _ => split | _ => idtac end).

(* A context is valid iff its weakening with a valid OType is *)
Lemma ValidCtx_ctxInsert_iff n W `{OTRelation W} ctx :
  (OType W /\ ValidCtx ctx) <-> ValidCtx (ctxInsert n W ctx).
Proof.
  split; revert ctx; induction n; intro ctx; destruct ctx; simpl; intro valid;
    destruct_ands; split_ands;
    try typeclasses eauto; try apply I.
  - apply IHn; split; auto.
  - apply IHn; split; assumption.
  - apply (proj1 (IHn CtxNil H1)).
  - apply (proj1 (IHn _ H2)).
  - apply (proj2 (IHn _ H2)).
Qed.

(* Weakening preserves validity *)
Instance ValidCtx_ctxInsert w W `{OType W} ctx {valid:ValidCtx ctx} :
  ValidCtx (ctxInsert w W ctx).
Proof.
  apply ValidCtx_ctxInsert_iff; split; assumption.
Defined.

Lemma OType_ctxInsert n W `{OTRelation W} ctx `{ValidCtx (ctxInsert n W ctx)} :
  OType W.
Proof.
  exact (proj1 ((proj2 (ValidCtx_ctxInsert_iff n W ctx)) H0)).
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
Defined.

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

(* ctxSuffix preserves ValidCtx *)
Instance ValidCtx_ctxSuffix n ctx {valid:ValidCtx ctx} :
  ValidCtx (ctxSuffix n ctx).
Proof.
  revert n valid; induction ctx; intros n valid;
    [ | destruct n; destruct valid ]; simpl.
  - apply I.
  - assumption.
  - apply IHctx; assumption.
Defined.

(* Substitute into a context by providing a pfun for the nth value *)
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

(* Proper-ness of subst_pfun *)
Instance Proper_subst_pfun ctx n : Proper (ot_R ==> ot_R) (subst_pfun ctx n).
Proof.
  revert n; induction ctx; intros; [ | destruct n ]; simpl; intros s1 s2 Rs.
  - reflexivity.
  - intros c1 c2 Rc; simpl. split; [ | apply Rs ]; assumption.
  - intros c1 c2 Rc; simpl.
    split; destruct Rc; [ apply IHctx | ]; assumption.
Qed.

(* Proper-ness of subst_pfun w.r.t equivalence *)
Instance Proper_subst_pfun_equiv ctx n :
  Proper (ot_equiv ==> ot_equiv) (subst_pfun ctx n).
Proof.
  intros s1 s2 Rs; destruct Rs; split; apply Proper_subst_pfun; assumption.
Qed.

(* FIXME HERE: delete subst_var_pfun? *)

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
