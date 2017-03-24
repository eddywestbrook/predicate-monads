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

(* Eta rule for SemType *)
Lemma eta_SemType semTp :
  semTp = {| semCtx := semCtx semTp; semType := semType semTp;
             sem_OTRelation := _ |}.
  destruct semTp; reflexivity.
Qed.

(* Typeclass capturing that a SemType is valid: semType is an OType *)
(* FIXME: is this needed? *)
(*
Class ValidSemType semTp : Prop := otypeSemType :> OType (semType semTp).
*)

(* Convert a SemType to an actual type (FIXME: should this be a coercion?) *)
Definition Semantics (semTp:SemType) : Type :=
  CtxElem (semCtx semTp) -o> semType semTp.

(* Cast a semantic value to an equal semantic type *)
Definition castSemantics {semTp1 semTp2} (e:semTp1=semTp2)
           (sem:Semantics semTp1) : Semantics semTp2 :=
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


(* castSemantics commutes with pfun_apply *)
(*
Lemma castSemantics_pfun_apply_commute semTp1 semTp2 (e:semTp1=semTp2)
      (fsem: Semantics {| semCtx := semCtx semTp1 |})
*)


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

Arguments OExpr_ctx e /.
Arguments OExpr_type e /.
Arguments OTRelation_OExpr_type e /.


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
 *** Typing for Ordered Expressions
 ***)

(* Proof that an ordered expression is well-typed *)
Fixpoint HasType semTp (e:OExpr) : Prop :=
  match e with
  | OVar ctx n =>
    ValidCtx ctx /\
    {| semCtx := ctx; semType := nthCtx n ctx; sem_OTRelation := _ |} = semTp
  | @OEmbed ctx A _ a =>
    ValidCtx ctx /\
    OType A /\
    {| semCtx := ctx; semType := A; sem_OTRelation := _ |} = semTp
  | OApp B f arg =>
    (semTp = {| semCtx := semCtx semTp; semType := B; sem_OTRelation := _ |} /\
     OType B) /\
    (HasType {| semCtx := semCtx semTp;
                semType := OExpr_type arg -o> semType semTp;
                sem_OTRelation := _ |} f /\
     HasType {| semCtx := semCtx semTp; semType := OExpr_type arg;
                sem_OTRelation := _ |} arg)
  | OLam f =>
    {| semCtx := ctxTail (OExpr_ctx f);
       semType := ctxHead (OExpr_ctx f) -o> OExpr_type f;
       sem_OTRelation := _ |} = semTp /\
    OExpr_ctx f <> CtxNil /\ HasType (OExpr_SemType f) f
  end.

(* Typeclass version of HasType *)
Class HasTypeC semTp e : Prop := hasType : HasType semTp e.

(* Expressions can only have their one type *)
Lemma HasType_OExpr_SemType semTp e :
  HasType semTp e -> semTp = OExpr_SemType e.
  revert semTp; induction e; intros semTp ht; destruct ht.
  - rewrite <- H0; reflexivity.
  - destruct H0; rewrite <- H1; reflexivity.
  - destruct H; destruct H0; simpl. rewrite H. rewrite <- (IHe2 _ H2).
    reflexivity.
  - rewrite <- H; simpl. reflexivity.
Qed.

Instance ValidCtx_OExpr_ctx semTp e (ht:HasTypeC semTp e) :
  ValidCtx (OExpr_ctx e).
Proof.
  revert semTp ht; induction e; intros; destruct ht.
  - assumption.
  - assumption.
  - destruct H0. apply (IHe2 _ H1).
  - destruct H0. apply ValidCtx_ctxTail. apply (IHe _ H1).
Qed.

Instance ValidCtx_semTp_HasTypeC semTp e (ht:HasTypeC semTp e) :
  ValidCtx (semCtx semTp).
Proof.
  rewrite (HasType_OExpr_SemType _ _ ht). typeclasses eauto.
Qed.

(* Any well-typed expression has a valid type *)
Instance OType_OExpr_type semTp e (ht:HasTypeC semTp e) : OType (OExpr_type e).
Proof.
  revert semTp ht; induction e; intros; destruct ht.
  - typeclasses eauto.
  - destruct H0; assumption.
  - destruct H; assumption.
  - destruct H0.
    assert (OType (OExpr_type e)); [ apply (IHe _ H1) | typeclasses eauto ].
Qed.

Instance OType_semTp_HasTypeC semTp e (ht:HasTypeC semTp e) :
  OType (semType semTp).
Proof.
  rewrite (HasType_OExpr_SemType _ _ ht). typeclasses eauto.
Qed.


(***
 *** The Semantics of Ordered Expressions
 ***)

(* The semantics of a variable *)
Fixpoint varSemantics ctx v {struct ctx} :
  Semantics (Build_SemType ctx (nthCtx v ctx) _) :=
  match ctx return Semantics (Build_SemType ctx (nthCtx v ctx) _) with
  | CtxNil => const_pfun tt
  | CtxCons A ctx' =>
    match v return
          Semantics (Build_SemType (CtxCons A ctx') (nthCtx v (CtxCons A ctx')) _)
    with
    | 0 => snd_pfun
    | S v' => compose_pfun fst_pfun (varSemantics ctx' v')
    end
  end.


(* We need versions of proj1 and proj2 that actually compute *)
Definition proj1c {P Q:Prop} (pf:P /\ Q) : P :=
  match pf with conj pf1 _ => pf1 end.
Arguments proj1c {P Q} !pf.

Definition proj2c {P Q:Prop} (pf:P /\ Q) : Q :=
  match pf with conj _ pf2 => pf2 end.
Arguments proj2c {P Q} !pf.


(* The semantics of a well-typed expression *)
Program Fixpoint exprSemantics semTp e :
  HasTypeC semTp e -> Semantics semTp :=
  match e return HasType semTp e -> Semantics semTp with
  | OVar ctx v =>
    fun ht =>
      castSemantics (proj2c ht) (varSemantics ctx v)
  | OEmbed ctx a =>
    fun ht =>
      castSemantics (proj2c (proj2c ht))
                    (const_pfun (H0:=proj1c (proj2c ht)) a)
  | OApp B f arg =>
    fun ht =>
      pfun_apply
        (exprSemantics
           {| semCtx := semCtx semTp;
              semType := OExpr_type arg -o> semType semTp;
              sem_OTRelation := _ |}
           f
           (rew _ in proj1c (proj2c ht)))
        (exprSemantics
           {| semCtx := semCtx semTp; semType := OExpr_type arg;
              sem_OTRelation := _ |}
           arg
           (rew _ in proj2c (proj2c ht)))
  | OLam f =>
    fun ht =>
      castSemantics
        (proj1c ht)
        (pfun_curry
           (H:= _ )
           (exprSemantics
              {| semCtx := CtxCons _ _; semType := OExpr_type f;
                 sem_OTRelation := _ |}
              f
              _))
  end.
Next Obligation.
  fold (HasTypeC (OExpr_SemType f) f) in H1; typeclasses eauto.
Defined.
Next Obligation.
  rewrite <- (ctx_eq_head_tail _ H0).
  rewrite <- (eta_SemType _). assumption.
Defined.


(***
 *** Relating Ordered Expressions
 ***)

(* Proposition that two expressions have the same set of types *)
Definition equiTyped e1 e2 : Prop :=
  forall semTp, HasType semTp e1 <-> HasType semTp e2.

Instance Equivalence_equiTyped : Equivalence equiTyped.
Proof.
  split.
  - intros x semTp; reflexivity.
  - intros x y equi semTp; symmetry; apply equi.
  - intros e1 e2 e3 equi12 equi23 semTp.
    transitivity (HasType semTp e2); [ apply equi12 | apply equi23 ].
Qed.

(* Equi-typed expressions have the same canonical types *)
Lemma equiTyped_eq_SemTypes e1 e2 (equi:equiTyped e1 e2)
      semTp (ht:HasType semTp e1) :
  OExpr_SemType e1 = OExpr_SemType e2.
  rewrite <- (HasType_OExpr_SemType _ _ ht).
  apply (HasType_OExpr_SemType _ _ (proj1 (equi semTp) ht)).
Qed.

Record oexpr_R (e1 e2:OExpr) : Prop :=
  { oexpr_R_ht : equiTyped e1 e2;
    oexpr_R_R :
      forall semTp ht1 ht2,
        exprSemantics semTp e1 ht1 <o= exprSemantics _ e2 ht2 }.

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
    transitivity (exprSemantics semTp e2 (proj1 (ht12 _) ht1));
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
  intros a1 a2 Ra; split; intros.
  { intro semTp; reflexivity. }
  { simpl. rewrite Ra. rewrite (proof_irrelevance _ ht1 ht2). reflexivity. }
Qed.

Instance Proper_OEmbed_eq ctx A {RA:OTRelation A} :
  Proper (ot_equiv ==> oexpr_eq) (@OEmbed ctx A _).
Proof.
  intros a1 a2 eqA; destruct eqA; split; apply Proper_OEmbed_R; assumption.
Qed.

Instance Proper_OApp_R (B:Type) {RB:OTRelation B} :
  Proper (oexpr_R ==> oexpr_R ==> oexpr_R) (OApp B).
Proof.
  intros f1 f2 [ ht_f rf ] arg1 arg2 [ ht_arg r_arg ]; split; intros.
  { intro semTp; split;
      intros [ [semTp_eq otype_b] [ht_f' ht_arg'] ]; split; split;
      try assumption; simpl.
    - apply ht_f.
      rewrite (equiTyped_eq_SemTypes
                 arg2 arg1 (symmetry ht_arg) _
                 (proj1 (ht_arg _) ht_arg')); assumption.
    - apply ht_arg.
      rewrite (equiTyped_eq_SemTypes
                 arg2 arg1 (symmetry ht_arg) _
                 (proj1 (ht_arg _) ht_arg')); assumption.
    - apply ht_f.
      rewrite (equiTyped_eq_SemTypes
                 arg1 arg2 ht_arg _
                 (proj2 (ht_arg _) ht_arg')); assumption.
    - apply ht_arg.
      rewrite (equiTyped_eq_SemTypes
                 arg1 arg2 ht_arg _
                 (proj2 (ht_arg _) ht_arg')); assumption. }
  { destruct ht1 as [ [eq_semTp otype_b] [ht_f1 ht_arg1]].
    assert (OExpr_SemType arg1 = OExpr_SemType arg2) as eq_arg_tp;
      [ apply (equiTyped_eq_SemTypes _ _ ht_arg _ ht_arg1) | ].
    revert ht_f1 ht_arg1; simpl; rewrite eq_arg_tp; intros.
    apply Proper_pfun_apply.
    - apply (rf {| semCtx := _; semType := _; sem_OTRelation := _ |}).
    - apply (r_arg {| semCtx := _; semType := _; sem_OTRelation := _ |}). }
Qed.
