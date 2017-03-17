Require Export PredMonad.Reflection.OrderedType.
Require Import Coq.Logic.ProofIrrelevance.

Import EqNotations.
Import ListNotations.
Import ProofIrrelevanceTheory.


(***
 *** Ordered Type Contexts
 ***)

(* A context here is just a list of types *)
Inductive Ctx : Type :=
| CtxNil
| CtxCons A `{OTRelation A} (ctx:Ctx)
.

(* Inductive type stating that every type in a Ctx is a valid OType *)
Inductive ValidCtxInd : Ctx -> Prop :=
| ValidCtxNil : ValidCtxInd CtxNil
| ValidCtxCons A `{OType A} ctx : ValidCtxInd ctx -> ValidCtxInd (CtxCons A ctx)
.

(* Inversion for ValidCtxInd *)
Lemma ValidCtxInd_inversion A `{OTRelation A} ctx
      (valid:ValidCtxInd (CtxCons A ctx)) : OType A /\ ValidCtxInd ctx.
  inversion valid.
  dependent rewrite <- H1.
  split; assumption.
Qed.

(* Typeclass version of ValidCtxInd *)
Class ValidCtx ctx : Prop :=
  validCtx : ValidCtxInd ctx.

(* Instances for building ValidCtx proofs *)
Instance ValidCtx_Nil : ValidCtx CtxNil := ValidCtxNil.
Instance ValidCtx_Cons A `{OType A} ctx (vc:ValidCtx ctx) :
  ValidCtx (CtxCons A ctx) := ValidCtxCons A ctx vc.

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

(* OType instance of CtxElem of a valid context *)
Instance OType_CtxElem ctx (valid:ValidCtx ctx) : OType (CtxElem ctx).
Proof.
  induction valid; typeclasses eauto.
Qed.

(* Look up the nth type in a Ctx, returning the unit type as a default *)
Fixpoint nthCtx n ctx {struct ctx} : Type :=
  match ctx with
  | CtxNil => unit
  | CtxCons A ctx' =>
    match n with
    | 0 => A
    | S n' => nthCtx n' ctx'
    end
  end.

(* The OTRelation for the nth type in a context *)
Instance OTRelation_nthCtx n ctx : OTRelation (nthCtx n ctx).
Proof.
  revert n; induction ctx; intros; simpl; try typeclasses eauto.
  destruct n; simpl; typeclasses eauto.
Defined.

(* For valid contexts, the nth element is a valid OType *)
Instance OType_nthCtx n ctx `{valid:ValidCtx ctx} : OType (nthCtx n ctx).
Proof.
  revert n valid; induction ctx; intros; simpl; try typeclasses eauto.
  destruct (ValidCtxInd_inversion _ _ valid).
  destruct n; try assumption. apply IHctx; apply H1.
Qed.

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
  - exact (proj1 (ValidCtxInd_inversion _ ctx valid)).
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
  - exact (proj2 (ValidCtxInd_inversion _ ctx valid)).
Qed.

(* Non-nil contexts equal cons of their heads and tails *)
Lemma ctx_eq_head_tail ctx :
  ctx <> CtxNil -> ctx = CtxCons (ctxHead ctx) (ctxTail ctx).
  destruct ctx; intro e.
  elimtype False; apply e; reflexivity.
  reflexivity.
Qed.

(* Appending contexts *)
Fixpoint appendCtx ctx1 ctx2 : Ctx :=
  match ctx1 with
  | CtxNil => ctx2
  | CtxCons A ctx1' =>
    CtxCons A (appendCtx ctx1' ctx2)
  end.

(* Context length *)
Fixpoint ctxLen ctx :=
  match ctx with
  | CtxNil => 0
  | CtxCons A ctx' => S (ctxLen ctx')
  end.


(***
 *** Semantic Types
 ***)

(* A "semantics type", which is a context plus an ordered type *)
Record SemType : Type :=
  { semCtx : Ctx;
    semType : Type;
    sem_OTRelation :> OTRelation semType }.

(* For some reason, Coq doesn't build sem_OTRelation as an instance... *)
Instance OTRelation_SemType semTp : OTRelation (semType semTp) :=
  sem_OTRelation semTp.

(* Typeclass capturing that a SemType is valid: semType is an OType *)
Class ValidSemType semTp : Prop := otypeSemType :> OType (semType semTp).

(* Convert a SemType to an actual type (FIXME: should this be a coercion?) *)
Definition oSemantics (semTp:SemType) : Type :=
  CtxElem (semCtx semTp) -o> semType semTp.

(* Cast a semantic value to an equal semantic type *)
Definition castSemantics {semTp1 semTp2} (e:semTp1=semTp2)
           (sem:oSemantics semTp1) : oSemantics semTp2 :=
  rew e in sem.

(* castSemantics is Proper *)
Instance Proper_castSemantics semTp1 semTp2 (e:semTp1=semTp2) :
  Proper (ot_R ==> ot_R) (castSemantics e).
Proof.
  generalize e. rewrite e. intros e2 sem1 sem2 Rsem.
  rewrite (UIP_refl _ _ e2). apply Rsem.
Qed.

Lemma double_cast {A} {x y z:A} {F:A -> Type} (e1:x=y) (e2:y=z) (e3:x=z) obj :
  rew [F] e2 in (rew [F] e1 in obj) = rew [F] e3 in obj.
  revert e2 e3 obj. generalize e1. rewrite e1. intros. rewrite (UIP_refl _ _ e0).
  simpl. rewrite (UIP _ _ _ e2 e3). reflexivity.
Qed.

(* A cast of a cast is a cast *)
Definition double_castSemantics semTp1 semTp2 semTp3 (e1:semTp1=semTp2)
           (e2:semTp2=semTp3) e3 sem :
  castSemantics e2 (castSemantics e1 sem) = castSemantics e3 sem :=
  double_cast _ _ _ _.


FIXME HERE NOW: we need to prove that castSemantics commutes with exprSemantics
for the OApp and OLam constructors, which is going to be gross...


(* castSemantics commutes with pfun_apply *)
Lemma castSemantics_pfun_apply_commute semTp1 semTp2 (e:semTp1=semTp2)
      (fsem: oSemantics {| semCtx := semCtx semTp1 |})


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

(* We can always look up the correct context and ordered type of an OExpr *)
Fixpoint OExpr_SemType (e:OExpr) : SemType :=
  match e with
  | OVar ctx n => Build_SemType ctx (nthCtx n ctx) _
  | @OEmbed ctx A _ _ => Build_SemType ctx A _
  | OApp B _ arg => Build_SemType (semCtx (OExpr_SemType arg)) B _
  | OLam f =>
    Build_SemType (ctxTail (semCtx (OExpr_SemType f)))
                  (ctxHead (semCtx (OExpr_SemType f)) -o> semType (OExpr_SemType f))
                  _
  end.

Definition OExpr_ctx e := semCtx (OExpr_SemType e).
Definition OExpr_type e := semType (OExpr_SemType e).
Instance OTRelation_OExpr_type e : OTRelation (OExpr_type e) := _.


(***
 *** Substitution and Weakening for Ordered Expressions
 ***)

(* Weakening / lifting of ordered expression variables: insert w_ctx into the
context of a variable at point n *)
Fixpoint weakenOVar n w_ctx (v:nat) {struct n} : nat :=
  match n with
  | 0 => v + ctxLen w_ctx
  | S n' =>
    match v with
    | 0 => 0
    | S v' => weakenOVar n' w_ctx v'
    end
  end.

(* Weakening a context by inserting another at point n *)
Fixpoint weakenCtx n w_ctx ctx : Ctx :=
  match n with
  | 0 => appendCtx w_ctx ctx
  | S n' =>
    match ctx with
    | CtxNil => CtxCons unit (weakenCtx n' w_ctx CtxNil)
    | CtxCons A ctx' => CtxCons A (weakenCtx n' w_ctx ctx')
    end
  end.

(* Weakening / lifting of ordered expressions *)
Fixpoint weakenOExpr n w_ctx (e:OExpr) : OExpr :=
  match e with
  | OVar ctx v => OVar (weakenCtx n w_ctx ctx) (weakenOVar n w_ctx v)
  | OEmbed ctx a => OEmbed (weakenCtx n w_ctx ctx) a
  | OApp B f arg =>
    OApp B (weakenOExpr n w_ctx f) (weakenOExpr n w_ctx arg)
  | OLam f => OLam (weakenOExpr (S n) w_ctx f)
  end.

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


(***
 *** The Semantics of Ordered Expressions
 ***)

Definition oexprSemantics e := oSemantics (OExpr_SemType e).


(* Since expressions contain their types and contexts, the only requirement for
typing ordered expressions is that different parts of the expression have types
that agree with each other, and that the contexts are always valid *)
Fixpoint WellTypedP (e:OExpr) : Prop :=
  match e with
  | OVar ctx n => ValidCtx ctx
  | @OEmbed ctx A _ a => ValidCtx ctx /\ OType A
  | OApp B f arg =>
    (OExpr_SemType f =
     {| semCtx := OExpr_ctx arg; semType := OExpr_type arg -o> B;
        sem_OTRelation := _ |} /\ OType B)
    /\ (WellTypedP f /\ WellTypedP arg)
  | OLam f =>
    OExpr_SemType f =
    {| semCtx := CtxCons (ctxHead (OExpr_ctx f)) (ctxTail (OExpr_ctx f));
       semType := OExpr_type f; sem_OTRelation := _ |}
    /\ WellTypedP f
  end.

(* Type class for well-typedness *)
Class WellTyped e : Prop := wellTyped : WellTypedP e.

(* Any WellTyped expression has a ValidCtx *)
Instance ValidCtx_OExpr_ctx e (wt:WellTyped e) : ValidCtx (OExpr_ctx e).
Proof.
  revert wt; induction e; simpl; intro wt.
  - assumption.
  - exact (proj1 wt).
  - apply IHe2. apply (proj2 (proj2 wt)).
  - apply ValidCtx_ctxTail. apply IHe. apply (proj2 wt).
Qed.

(* Any WellTyped expression has a valid type *)
Instance OType_OExpr_type e (wt:WellTyped e) : OType (OExpr_type e).
Proof.
  revert wt; induction e; simpl; intro wt.
  - typeclasses eauto.
  - destruct wt; assumption.
  - destruct wt as [wt1 wt2]; destruct wt1; assumption.
  - unfold OExpr_type. simpl. destruct wt. typeclasses eauto.
Qed.

(* The semantics of a variable *)
Fixpoint varSemantics ctx v {struct ctx} :
  oSemantics (Build_SemType ctx (nthCtx v ctx) _) :=
  match ctx return oSemantics (Build_SemType ctx (nthCtx v ctx) _) with
  | CtxNil => const_pfun tt
  | CtxCons A ctx' =>
    match v return
          oSemantics (Build_SemType (CtxCons A ctx') (nthCtx v (CtxCons A ctx')) _)
    with
    | 0 => snd_pfun
    | S v' => compose_pfun fst_pfun (varSemantics ctx' v')
    end
  end.


(* The semantics of a well-typed expression *)
Program Fixpoint exprSemantics e :
  forall `{WellTyped e}, oexprSemantics e :=
  match e return WellTyped e -> oexprSemantics e with
  | OVar ctx v =>
    fun wt => varSemantics ctx v
  | OEmbed ctx a =>
    fun wt => const_pfun (H0:=proj2 wt) a
  | OApp B f arg =>
    fun wt =>
      pfun_apply
        (castSemantics (proj1 (proj1 wt)) (@exprSemantics f (proj1 (proj2 wt))))
        (@exprSemantics arg (proj2 (proj2 wt)))
  | OLam f =>
    fun wt =>
      pfun_curry
        (H:= _ )
        (castSemantics (proj1 wt) (@exprSemantics f (proj2 wt)))
  end.
Next Obligation.
  eauto with typeclass_instances.
Defined.

Instance OTRelation_expr_oSemantics e : OTRelation (oexprSemantics e) := _.
Instance OType_expr_oSemantics e (wt:WellTyped e) :
  OType (oexprSemantics e) := _.

(* castSemantics commutes with the semantics of applications *)
Lemma castSemantics_commute_OApp B B' {RB:OTRelation B} {RB':OTRelation B} e1 e2


(***
 *** Relating Ordered Expressions
 ***)

Record oexpr_R (e1 e2:OExpr) : Prop :=
  { oexpr_R_wt : WellTyped e1 <-> WellTyped e2;
    oexpr_R_eq_tp : OExpr_SemType e1 = OExpr_SemType e2;
    oexpr_R_sem :
      forall wt1 wt2,
        castSemantics oexpr_R_eq_tp (@exprSemantics e1 wt1) <o=
        @exprSemantics e2 wt2 }.

(* The equivalence relation on ordered expressions *)
Definition oexpr_eq : relation OExpr :=
  fun e1 e2 => oexpr_R e1 e2 /\ oexpr_R e2 e1.

(* oexpr_R is reflexive *)
Instance Reflexive_oexpr_R : Reflexive oexpr_R.
Proof.
  intro e; split.
  - reflexivity.
  - intros; apply mk_otRdep. rewrite (proof_irrelevance _ wt1 wt2). reflexivity.
Qed.

(* oexpr_R is transitive *)
Instance Transitive_oexpr_R : Transitive oexpr_R.
Proof.
  intros e1 e2 e3 [ wt12 r12 ]. destruct 
  split.
  { transitivity (WellTyped e2); assumption. }
  { intros wt1 wt3. rewrite <- r23. rewrite <- r12.
    rewrite (double_castSemantics _ _ _ _ _ (eq_trans eq12 eq23)).
    reflexivity. }
  Unshelve.
  apply wt23. assumption.
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
  intros a1 a2 Ra. split; [ | exists eq_refl ].
  { reflexivity. }
  { unfold castSemantics; simpl; intros. rewrite (proof_irrelevance _ wt1 wt2).
    destruct wt1. rewrite Ra. reflexivity. }
Qed.

Instance Proper_OEmbed_eq ctx A {RA:OTRelation A} :
  Proper (ot_equiv ==> oexpr_eq) (@OEmbed ctx A _).
Proof.
  intros a1 a2 eqA; destruct eqA; split; apply Proper_OEmbed_R; assumption.
Qed.

Instance Proper_OApp_R (B:Type) {RB:OTRelation B} :
  Proper (oexpr_R ==> oexpr_R ==> oexpr_R) (OApp B).
Proof.
  intros f1 f2 [ wt_f [ eqf rf ] ] arg1 arg2 [ wt_a [ eqa ra ] ].
  split; [ | eexists ]. Unshelve.
  { simpl. rewrite eqf. unfold OExpr_ctx, OExpr_type, OTRelation_OExpr_type.
    rewrite wt_f. rewrite wt_a. rewrite eqa. reflexivity. }
  { simpl; intros.

 intro wt1; generalize wt1. 

 intros.
