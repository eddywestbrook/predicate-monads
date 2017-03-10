Require Export PredMonad.Reflection.OrderedType.
Require Import Coq.Logic.Eqdep. (* We need Streicher's K / UIP *)

Import EqNotations.
Import ListNotations.


(***
 *** Ordered Expressions
 ***)

(* Untyped expressions to represent proper functions *)
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

(* A context here is just a list of types *)
Inductive Ctx : Type :=
| CtxNil
| CtxCons A `{OTRelation A} (ctx:Ctx)
.

(* An element of a context is a nested tuple of elements of its types *)
Fixpoint CtxElem (ctx:Ctx) : Type :=
  match ctx with
  | CtxNil => unit
  | CtxCons A ctx' => A * CtxElem ctx'
  end.

(* OTRelation instance for any CtxElem type *)
Instance OTRelation_CtxElem ctx : OTRelation (CtxElem ctx).
Proof.
  induction ctx.
  - apply OTunit_R.
  - apply OTpair_R; assumption.
Defined.

(* Proofs that a type is the nth element of a context *)
Fixpoint HasTypeVar (v:nat) (ctx:Ctx) (B:Type) {RB:OTRelation B} : Prop :=
  match v with
  | 0 =>
    match ctx with
    | CtxNil => False
    | @CtxCons A RA _ =>
      existT OTRelation A RA = existT OTRelation B RB
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
  | @OEmbed A RA a =>
      existT OTRelation A RA = existT OTRelation B RB
  | OApp A B' f arg =>
    existT OTRelation (A -o> B') _ = existT OTRelation B _
    /\ (HasType f ctx (A -o> B') /\ HasType arg ctx A)
  | OLam A B' body =>
    existT OTRelation (A -o> B') _ = existT OTRelation B _
    /\ HasType body (CtxCons A ctx) B'
  end.

(* Lemma: each HasTypeVar proof is unique *)
Lemma HasTypeVar_unique v ctx B {RB:OTRelation B} (ht1 ht2: HasTypeVar v ctx B)
  : ht1 = ht2.
  revert ctx ht1 ht2; induction v; destruct ctx; simpl; intros;
    try apply UIP; try apply IHv; try destruct ht1.
Qed.

(* Lemma: each HasType proof is unique *)
Lemma HasType_unique ctx B {RB:OTRelation B} e (ht1 ht2: HasType e ctx B)
  : ht1 = ht2.
  revert ctx B RB ht1 ht2; induction e; simpl; intros.
  { apply HasTypeVar_unique. }
  { apply UIP. }
  { destruct ht1 as [ ht11 ht1 ]; destruct ht1;
      destruct ht2 as [ ht21 ht2 ]; destruct ht2;
        repeat f_equal; first [ apply UIP | apply IHe1 | apply IHe2 ]. }
  { destruct ht1; destruct ht2. f_equal; [ apply UIP | apply IHe ]. }
Qed.

(* The semantics of a well-typed variable *)
Program Fixpoint varSemantics v ctx B {RB:OTRelation B} :
  HasTypeVar v ctx B -> CtxElem ctx -o> B :=
  match v return HasTypeVar v ctx B -> CtxElem ctx -o> B with
  | 0 =>
    match ctx return HasTypeVar 0 ctx B -> CtxElem ctx -o> B with
    | CtxNil => fun ht => match ht with end
    | @CtxCons A RA ctx' =>
      fun (ht: existT OTRelation A RA = existT OTRelation B RB) =>
        rew [fun p =>
               @Pfun (A * CtxElem ctx') (projT1 p) (OTpair_R A _ RA _) (projT2 p)]
            ht in (fst_pfun (A:=projT1 (existT OTRelation A RA)) (H:=RA))
    end
  | S v' =>
    match ctx return HasTypeVar (S v') ctx B ->
                     @Pfun (CtxElem ctx) B (OTRelation_CtxElem ctx) _ with
    | CtxNil => fun ht => match ht with end
    | CtxCons A ctx' =>
      fun ht =>
        compose_pfun snd_pfun (varSemantics v' ctx' B ht)
    end
  end.

(* The semantics of a well-typed expression *)
Fixpoint exprSemantics e ctx B {RB:OTRelation B} :
  HasType e ctx B -> CtxElem ctx -> B :=
  match e return HasType e ctx B -> CtxElem ctx -o> B with
  | OVar v => varSemantics v ctx B
  | OEmbed a => fun ht _ => rew ht in a
  | OApp A B' f arg =>
    fun ht celem =>
      rew (proj1 ht) in
        pfun_app (exprSemantics f ctx (A -o> B') (proj1 (proj2 ht)) celem)
                 (exprSemantics arg ctx A (proj2 (proj2 ht)) celem)
  | OLam A B' body =>
    fun ht celem =>
      rew (proj1 ht) in
        exprSemantics body (A::ctx) B' (proj2 ht) celem
  end.