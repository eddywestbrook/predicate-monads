Require Export PredMonad.Reflection.OrderedType.
Require Export PredMonad.Reflection.OrderedContext.
Require Import Coq.Logic.ProofIrrelevance.

Import EqNotations.
Import ListNotations.
Import ProofIrrelevanceTheory.


(***
 *** Ordered Expressions
 ***)

Inductive OVar A {RA:OTRelation A} : Ctx  -> Type :=
| OVar_0 {ctx:Ctx} : OVar A (CtxCons A ctx)
| OVar_S {ctx:Ctx} {B} {RB:OTRelation B} :
    OVar A ctx -> OVar A (CtxCons B ctx)
.

Arguments OVar_0 {A RA ctx}.
Arguments OVar_S {A RA ctx B RB} v.

(* Expressions to represent proper functions *)
Inductive OExpr (ctx:Ctx) : forall A {RA:OTRelation A}, Type :=
| Var {A} {RA:OTRelation A} {valid:ValidCtx ctx} (v:OVar A ctx) : OExpr ctx A
| Embed {A} {RA:OTRelation A} {OA:OType A} {valid:ValidCtx ctx} (a:A) : OExpr ctx A
| App {A B:Type} {RA:OTRelation A} {OA:OType A} {RB:OTRelation B} {OB:OType B}
      (e1 : OExpr ctx (A -o> B)) (e2 : OExpr ctx A) : OExpr ctx B
| Lam {A B:Type} {RA:OTRelation A} {OA:OType A} {RB:OTRelation B} {OB:OType B}
      {valid:ValidCtx ctx}
      (e: OExpr (CtxCons A ctx) B) : OExpr ctx (A -o> B)
.

Arguments Var {ctx} {A RA valid} v.
Arguments Embed {ctx} {A RA OA valid} a.
Arguments App {ctx} {A B RA OA RB OB} e1 e2.
Arguments Lam {ctx} {A B RA OA RB OB valid} e.


(* The type of any OExpr is always an OType *)
Instance OType_OExpr_type ctx A {RA} (e:@OExpr ctx A RA) : OType A.
Proof.
  induction e; try assumption.
  - induction v; destruct valid; [ | apply IHv]; assumption.
  - typeclasses eauto.
Qed.

(* The context of any OExpr is always valid *)
Instance ValidCtx_OExpr_ctx ctx A {RA} (e:@OExpr ctx A RA) : ValidCtx ctx.
Proof.
  induction e; assumption.
Qed.


(***
 *** Semantics of Ordered Expressions
 ***)

(* The semantics of a variable *)
Fixpoint varSemantics {A} {RA:OTRelation A} {ctx} (v:OVar A ctx) :
  CtxElem ctx -o> A :=
  match v in OVar _ ctx return CtxElem ctx -o> A with
  | OVar_0 => snd_pfun (A:=CtxElem _)
  | OVar_S v' => compose_pfun fst_pfun (varSemantics v')
  end.
Arguments varSemantics {A RA ctx} !v.

(* The semantics of an ordered expression *)
Fixpoint exprSemantics {ctx A} {RA:OTRelation A} (e:OExpr ctx A) :
  CtxElem ctx -o> A :=
  match e in OExpr _ A return CtxElem ctx -o> A with
  | Var v => varSemantics v
  | Embed a => const_pfun a
  | App e1 e2 =>
    pfun_apply (exprSemantics e1) (exprSemantics e2)
  | Lam e => pfun_curry (exprSemantics e)
  end.
Arguments exprSemantics {ctx A RA} !e.


(***
 *** Relating Ordered Expressions
 ***)

(* Two expressions are related iff their semantics are *)
Definition oexpr_R {ctx A} {RA:OTRelation A} : relation (OExpr ctx A) :=
  fun e1 e2 => exprSemantics e1 <o= exprSemantics e2.
Arguments oexpr_R {ctx A RA} e1 e2 /.

(* oexpr_R is a PreOrder *)
Instance PreOrder_oexpr_R ctx A {RA} : PreOrder (@oexpr_R ctx A RA).
Proof.
  split; intro; intros;
  assert (ValidCtx ctx) as valid; try eauto with typeclass_instances;
    assert (OType A) as OA; try eauto with typeclass_instances;
      unfold oexpr_R.
  - reflexivity.
  - transitivity (exprSemantics y); assumption.
Qed.

(* Two expressions are equivalent iff their semantics are *)
Definition oexpr_eq {ctx A} {RA:OTRelation A} : relation (OExpr ctx A) :=
  fun e1 e2 => exprSemantics e1 =o= exprSemantics e2.
Arguments oexpr_eq {ctx A RA} e1 e2 /.

(* oexpr_eq is an Equivalence *)
Instance Equivalence_oexpr_eq ctx A {RA} : Equivalence (@oexpr_eq ctx A RA).
Proof.
  constructor; intro; intros;
    assert (ValidCtx ctx) as valid; try eauto with typeclass_instances;
      assert (OType A) as OA; try eauto with typeclass_instances;
        unfold oexpr_eq.
  { split; reflexivity. }
  { symmetry; assumption. }
  { transitivity (exprSemantics y); assumption. }
Qed.

(* The Embed constructor is Proper w.r.t. ot_R and oexpr_R *)
Instance Proper_Embed ctx A {RA OA valid} :
  Proper (ot_R ==> oexpr_R) (@Embed ctx A RA OA valid).
Proof.
  intros a1 a2 Ra. simpl. rewrite Ra. reflexivity.
Qed.

(* The Embed constructor is Proper w.r.t. ot_equiv and oexpr_eq *)
Instance Proper_Embed_eq ctx A {RA OA valid} :
  Proper (ot_equiv ==> oexpr_eq) (@Embed ctx A RA OA valid).
Proof.
  intros a1 a2 Ra. simpl. rewrite Ra. reflexivity.
Qed.

(* The App constructor is Proper *)
Instance Proper_App ctx {A B RA OA RB OB} :
  Proper (oexpr_R ==> oexpr_R ==> oexpr_R) (@App ctx A B RA OA RB OB).
Proof.
  intros f1 f2 Rf a1 a2 Ra. simpl in * |- *.
  apply Proper_pfun_apply; assumption.
Qed.

(* The App constructor is Proper for equivalence *)
Instance Proper_App_eq ctx {A B RA OA RB OB} :
  Proper (oexpr_eq ==> oexpr_eq ==> oexpr_eq) (@App ctx A B RA OA RB OB).
Proof.
  intros f1 f2 Rf a1 a2 Ra. simpl in * |- *.
  apply Proper_pfun_apply_equiv; assumption.
Qed.

(* The Lam constructor is Proper *)
Instance Proper_Lam ctx {A B RA OA RB OB valid} :
  Proper (oexpr_R ==> oexpr_R) (@Lam ctx A B RA OA RB OB valid).
Proof.
  intros e1 e2 Re. simpl in * |- *.
  apply Proper_pfun_curry; assumption.
Qed.

(* The Lam constructor is Proper for equivalence *)
Instance Proper_Lam_eq ctx {A B RA OA RB OB valid} :
  Proper (oexpr_eq ==> oexpr_eq) (@Lam ctx A B RA OA RB OB valid).
Proof.
  intros e1 e2 Re. simpl in * |- *.
  apply Proper_pfun_curry_equiv; assumption.
Qed.


(***
 *** Substitution for Ordered Expressions
 ***)

(* Weakening / lifting of ordered expression variables *)
Fixpoint weakenOVar w W {RW:OTRelation W} :
  forall {ctx A} {RA:OTRelation A}, OVar A ctx -> OVar A (ctxInsert w W ctx) :=
  match w return
        forall ctx A {RA:OTRelation A}, OVar A ctx -> OVar A (ctxInsert w W ctx)
  with
  | 0 =>
    fun _ _ {_} v => OVar_S v
  | S w' =>
    fun ctx A {RA} v =>
      match v in OVar _ ctx return OVar A (ctxInsert (S w') W ctx) with
      | OVar_0 => OVar_0
      | OVar_S v' => OVar_S (weakenOVar w' W v')
      end
  end.

(* Weakening / lifting of ordered expressions *)
Fixpoint weakenOExpr w W {RW:OTRelation W} {OW:OType W} {ctx} {A} {RA:OTRelation A}
         (e:OExpr ctx A) : OExpr (ctxInsert w W ctx) A :=
  match e in OExpr _ A return OExpr (ctxInsert w W ctx) A with
  | Var v => Var (weakenOVar w W v)
  | Embed a => Embed a
  | App e1 e2 => App (weakenOExpr w W e1) (weakenOExpr w W e2)
  | Lam e => Lam (weakenOExpr (S w) W e)
  end.

(* Substitution for ordered expression variables *)
Fixpoint substOVar n {ctx} {A} {RA:OTRelation A} :
  OVar A ctx ->
  forall {valid:ValidCtx ctx}, OExpr (ctxSuffix n ctx) (ctxNth n ctx) ->
  OExpr (ctxDelete n ctx) A :=
  match n return
        OVar A ctx ->
        ValidCtx ctx -> OExpr (ctxSuffix n ctx) (ctxNth n ctx) ->
        OExpr (ctxDelete n ctx) A
  with
  | 0 =>
    fun v =>
      match v in OVar _ ctx return
            ValidCtx ctx ->
            OExpr (ctxSuffix 0 ctx) (ctxNth 0 ctx) -> OExpr (ctxDelete 0 ctx) A
      with
      | OVar_0 => fun _ s => s
      | OVar_S v' => fun valid _ => Var (valid:=proj2 valid) v'
    end
  | S n' =>
    fun v =>
      match v in OVar _ ctx return
            ValidCtx ctx ->
            OExpr (ctxSuffix (S n') ctx) (ctxNth (S n') ctx) ->
            OExpr (ctxDelete (S n') ctx) A
      with
      | OVar_0 =>
        fun valid _ =>
          Var (valid:=ValidCtx_ctxDelete (S n') (CtxCons _ _)) OVar_0
      | @OVar_S _ _ ctx' B RB v' =>
        fun valid s =>
          weakenOExpr 0 B (OW:=proj1 valid) (A:=A)
                      (substOVar n' v' (valid:=proj2 valid) s)
      end
  end.

(* Substitution for ordered expressions *)
Fixpoint substOExpr n {ctx} {A} {RA:OTRelation A} (e:OExpr ctx A) :
  OExpr (ctxSuffix n ctx) (ctxNth n ctx) -> OExpr (ctxDelete n ctx) A :=
  match e with
  | Var v => fun s => substOVar n v s
  | Embed a => fun _ => Embed a
  | App e1 e2 => fun s => App (substOExpr n e1 s) (substOExpr n e2 s)
  | Lam e => fun s => Lam (substOExpr (S n) e s)
  end.


FIXME HERE NOW:
- prove that weakening and substitution are correct
- quoting tactic!
