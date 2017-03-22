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
 *** Ordered Expressions
 ***)

(* Ordered expressions to represent proper functions. These are formulated in
this way to ensure that each expression has a unique type and context. *)
Inductive OExpr : Type :=
| OVar (ctx:Ctx) (n:nat)
| OEmbed (ctx:Ctx) {A} {RA:OTRelation A} (a:A)
| OApp (B:Type) {RB:OTRelation B} (e1 e2 : OExpr)
| OLam (e: OExpr)
.

(* A "semantics type", which is a context plus an ordered type *)
Record SemType : Type :=
  { semCtx : Ctx;
    semType : Type;
    sem_OTRelation :> OTRelation semType }.

(* For some reason, Coq doesn't build sem_OTRelation as an instance... *)
Instance OTRelation_SemType semTp : OTRelation (semType semTp) :=
  sem_OTRelation semTp.

(* Look up the ordered context and type of an OExpr *)
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
 *** Typing for Ordered Expressions
 ***)

Inductive HasType ctx : forall A {RA:OTRelation A}, OExpr -> Prop :=
| HT_OVar n : HasType ctx (nthCtx n ctx) (OVar ctx n)
| HT_OEmbed A {RA:OTRelation A} (a:A) : HasType ctx A (OEmbed ctx a)
| HT_OApp A B {RA:OTRelation A} {RB:OTRelation B} f arg :
    HasType ctx (A -o> B) f -> HasType ctx A arg -> HasType ctx B (OApp B f arg)
| HT_OLam A B {RA:OTRelation A} {RB:OTRelation B} f :
    HasType (CtxCons A ctx) B f -> HasType ctx (A -o> B) (OLam f)
.

Lemma HasType_unique_SemType ctx A {RA:OTRelation A} e :
  HasType ctx A e ->
  OExpr_SemType e = {| semCtx := ctx; semType := A; sem_OTRelation := RA |}.
  revert ctx A RA; induction e; intros.
  { inversion H. reflexivity. }
  { assert (OEmbed ctx a = OEmbed ctx a); [ reflexivity | ].
    revert H H0. generalize (OEmbed ctx a) at 0 1 2. intros.
    destruct H; simplify_eq H0; intros.
    rewrite H. dependent rewrite -> H2. reflexivity. }
  { assert (OApp B e1 e2 = OApp B e1 e2); [ reflexivity | ].
    revert H H0. generalize (OApp B e1 e2) at 0 1 2. intros.
    destruct H; simplify_eq H0; intros.
    dependent rewrite -> H3. simpl. rewrite H5 in H1.
    rewrite (IHe2 _ _ _ H1). reflexivity. }
  { assert (OLam e = OLam e); [ reflexivity | ].
    revert H H0. generalize (OLam e) at 0 1 2. intros.
    destruct H; simplify_eq H0; intros. simpl.
    rewrite H1 in H. rewrite (IHe _ _ _ H). reflexivity. }
Qed.


Lemma HasType_unique_ctx ctx A {RA:OTRelation A} e :
  HasType ctx A e -> ctx = OExpr_ctx e.
  intro ht. unfold OExpr_ctx. rewrite (HasType_unique_SemType _ _ _ ht).
  reflexivity.
Qed.

Lemma HasType_unique_type ctx A {RA:OTRelation A} e :
  HasType ctx A e -> A = OExpr_type e.
  intro ht. unfold OExpr_type. rewrite (HasType_unique_SemType _ _ _ ht).
  reflexivity.
Qed.

FIXME HERE NOW:
- project out HasType proofs for subterms of OApp and OLam
  (might need the above proof!)
- Also: OExpr_SemType could be OExpr_ctx followed by OExpr_type, since the
  latter can be written in terms of the former
