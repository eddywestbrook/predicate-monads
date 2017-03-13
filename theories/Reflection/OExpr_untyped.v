Require Export PredMonad.Reflection.OrderedType.
Require Import Coq.Logic.ProofIrrelevance.

Import EqNotations.
Import ListNotations.


(***
 *** Ordered Expressions
 ***)

(* Ordered expressions to represent proper functions *)
Inductive OExpr : Type :=
| OVar (n:nat)
| OEmbed {A} {RA:OTRelation A} (a:A)
| OApp (A B:Type) {RA:OTRelation A} {RB:OTRelation B} (e1 e2 : OExpr)
| OLam (A B:Type) {RA:OTRelation A} {RB:OTRelation B} (e: OExpr)
.

(* Weakening / lifting of ordered expression variables *)
Fixpoint weakenOVar n k (v:nat) {struct n} : nat :=
  match n with
  | 0 => v + k
  | S n' =>
    match v with
    | 0 => 0
    | S v' => weakenOVar n' k v'
    end
  end.

(* Weakening / lifting of ordered expressions *)
Fixpoint weakenOExpr n k (e:OExpr) : OExpr :=
  match e with
  | OVar v => OVar (weakenOVar n k v)
  | OEmbed a => OEmbed a
  | OApp A B f arg => OApp A B (weakenOExpr n k f) (weakenOExpr n k arg)
  | OLam A B f => OLam A B (weakenOExpr (S n) k f)
  end.

(* Substitution for ordered expression variables *)
Fixpoint substOVar n lifting (s:OExpr) v : OExpr :=
  match n with
  | 0 =>
    match v with
    | 0 => weakenOExpr 0 lifting s
    | S v' => OVar v'
    end
  | S n' =>
    match v with
    | 0 => OVar lifting
    | S v' =>
      substOVar n' (S lifting) s v
    end
  end.

(* Substitution for ordered expressions *)
Fixpoint substOExpr n (s:OExpr) (e:OExpr) : OExpr :=
  match e with
  | OVar v => substOVar n 0 s v
  | OEmbed a => OEmbed a
  | OApp A B f arg => OApp A B (substOExpr n s f) (substOExpr n s arg)
  | OLam A B body => OLam A B (substOExpr (S n) s body)
  end.


(***
 *** Typing for Ordered Expressions
 ***)

(* Proof that one ordered type equals another *)
Definition eqOType A {RA:OTRelation A} B {RB:OTRelation B} : Prop :=
  existT OTRelation A RA = existT OTRelation B RB.



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

(* Inductive type stating that every type in a Ctx is a valid OType *)
Inductive ValidCtxInd : Ctx -> Prop :=
| ValidCtxNil : ValidCtxInd CtxNil
| ValidCtxCons A `{OType A} ctx : ValidCtxInd ctx -> ValidCtxInd (CtxCons A ctx)
.

(* Typeclass version of ValidCtxInd *)
Class ValidCtx ctx : Prop :=
  validCtx : ValidCtxInd ctx.

(* Instances for building ValidCtx proofs *)
Instance ValidCtx_Nil : ValidCtx CtxNil := ValidCtxNil.
Instance ValidCtx_Cons A `{OType A} ctx (vc:ValidCtx ctx) :
  ValidCtx (CtxCons A ctx) := ValidCtxCons A ctx vc.

(* OType instance of CtxElem of a valid context *)
Instance OType_CtxElem ctx (valid:ValidCtx ctx) : OType (CtxElem ctx).
Proof.
  induction valid; typeclasses eauto.
Qed.

(* Proofs that a type is the nth element of a context *)
Fixpoint HasTypeVar (v:nat) (ctx:Ctx) (B:Type) {RB:OTRelation B} : Prop :=
  match v with
  | 0 =>
    match ctx with
    | CtxNil => False
    | @CtxCons A RA _ => eqOType A B
    end
  | S v' =>
    match ctx with
    | CtxNil => False
    | CtxCons _ ctx' => HasTypeVar v' ctx' B
    end
  end.

(* Typing proofs for ordered expressions *)
Fixpoint HasType (e:OExpr) (ctx:Ctx) (B:Type) {RB:OTRelation B} : Prop :=
  match e with
  | OVar v => HasTypeVar v ctx B
  | @OEmbed A RA a => eqOType A B /\ OType A
  | OApp A B' f arg =>
    eqOType B' B /\ (HasType f ctx (A -o> B') /\ HasType arg ctx A)
  | OLam A B' body =>
    eqOType (A -o> B') B /\ (ValidCtx ctx /\ HasType body (CtxCons A ctx) B')
  end.

(* Lemma: each HasTypeVar proof is unique *)
(*
Lemma HasTypeVar_unique v ctx B {RB:OTRelation B} (ht1 ht2: HasTypeVar v ctx B)
  : ht1 = ht2.
  revert ctx ht1 ht2; induction v; destruct ctx; simpl; intros;
    try apply proof_irrelevance; try apply IHv; try destruct ht1.
Qed.
*)

(* Lemma: each HasType proof is unique *)
(*
Lemma HasType_unique ctx B {RB:OTRelation B} e (ht1 ht2: HasType e ctx B)
  : ht1 = ht2.
  revert ctx B RB ht1 ht2; induction e; simpl; intros.
  { apply HasTypeVar_unique. }
  { apply proof_irrelevance. }
  { destruct ht1; destruct ht2; f_equal; apply proof_irrelevance. }
      repeat f_equal; first [ apply UIP | apply IHe1 | apply IHe2 ]. }
  { destruct ht1; destruct ht2. f_equal; [ apply UIP | apply IHe ]. }
Qed.
 *)


(***
 *** The Semantics of Ordered Expressions
 ***)

(* The semantics of a well-typed variable *)
Program Fixpoint varSemantics v ctx B {RB:OTRelation B} :
  HasTypeVar v ctx B -> CtxElem ctx -o> B :=
  match v return HasTypeVar v ctx B -> CtxElem ctx -o> B with
  | 0 =>
    match ctx return HasTypeVar 0 ctx B -> CtxElem ctx -o> B with
    | CtxNil => fun ht => match ht with end
    | @CtxCons A RA ctx' =>
      fun ht =>
        rew [fun p =>
               @Pfun (CtxElem ctx' * A) (projT1 p) (OTpair_R _ A _ RA) (projT2 p)]
            ht in (snd_pfun (B:=projT1 (existT OTRelation A RA)))
    end
  | S v' =>
    match ctx return HasTypeVar (S v') ctx B ->
                     @Pfun (CtxElem ctx) B (OTRelation_CtxElem ctx) _ with
    | CtxNil => fun ht => match ht with end
    | CtxCons A ctx' =>
      fun ht =>
        compose_pfun fst_pfun (varSemantics v' ctx' B ht)
    end
  end.

(* Helper to cast a proper function using an equality on ordered types *)
Definition castSemantics {ctx A B} `{OTRelation A} `{OTRelation B}
           (e:eqOType A B) (sem: CtxElem ctx -o> A) : CtxElem ctx -o> B :=
  rew [fun p => @Pfun (CtxElem ctx) (projT1 p) _ (projT2 p)] e in
    (sem : CtxElem ctx -o> (projT1 (existT OTRelation A _))).

(* The semantics of a well-typed expression *)
Fixpoint exprSemantics e ctx B {RB:OTRelation B} :
  HasType e ctx B -> CtxElem ctx -o> B :=
  match e return HasType e ctx B -> CtxElem ctx -o> B with
  | OVar v => varSemantics v ctx B
  | OEmbed a =>
    fun ht => castSemantics (proj1 ht) (const_pfun (H0:=proj2 ht) a)
  | OApp A B' f arg =>
    fun ht =>
      castSemantics
        (proj1 ht)
        (pfun_apply
           (exprSemantics f ctx (A -o> B') (proj1 (proj2 ht)))
           (exprSemantics arg ctx A (proj2 (proj2 ht))))
  | OLam A B' body =>
    fun ht =>
      castSemantics
        (proj1 ht)
        (pfun_curry (H:=OType_CtxElem ctx (proj1 (proj2 ht)))
                   (exprSemantics body (CtxCons A ctx) B' (proj2 (proj2 ht)))
         : CtxElem ctx -o> (projT1 (existT OTRelation (A -o> B') _)))
  end.


(***
 *** Relating Ordered Expressions
 ***)

(* The preorder on ordered expressions *)
Definition oexpr_R ctx B `{OTRelation B} : relation OExpr :=
  fun e1 e2 =>
    (HasType e1 ctx B <-> HasType e2 ctx B) /\
    (forall ht1 ht2 `{ValidCtx ctx},
        ot_R (exprSemantics e1 ctx B ht1) (exprSemantics e2 ctx B ht2)).

(* The equivalence relation on ordered expressions *)
Definition oexpr_eq ctx B `{OTRelation B} : relation OExpr :=
  fun e1 e2 => oexpr_R ctx B e1 e2 /\ oexpr_R ctx B e2 e1.

(* oexpr_R is reflexive *)
Instance Reflexive_oexpr_R ctx B `{OType B} : Reflexive (oexpr_R ctx B).
Proof.
  intro e; split; intros.
  - reflexivity.
  - rewrite (proof_irrelevance _ ht1 ht2); apply pfun_Proper; assumption.
Qed.

(* oexpr_R is transitive *)
Instance Transitive_oexpr_R ctx B `{OType B} : Transitive (oexpr_R ctx B).
Proof.
  intros e1 e2 e3 r12 r23; destruct r12; destruct r23; split.
  { transitivity (HasType e2 ctx B); [ apply H0 | apply H2 ]. }
  { intros ht1 ht3 valid.
    assert (HasType e2 ctx B) as ht2; [ apply H0; assumption | ].
    transitivity (exprSemantics e2 ctx B ht2).
    - apply H1; assumption.
    - apply H3; assumption. }
Qed.

(* oexpr_R is thus a PreOrder *)
Instance PreOrder_oexpr_R ctx B `{OType B} : PreOrder (oexpr_R ctx B) :=
  Build_PreOrder _ _ _.

(* oexpr_eq is thus an Equivalence *)
Instance Equivalence_oexpr_eq ctx B `{OType B} : Equivalence (oexpr_eq ctx B).
Proof.
  constructor; intro; intros.
  { split; reflexivity. }
  { destruct H0; split; assumption. }
  { destruct H0; destruct H1; split; transitivity y; assumption. }
Qed.

