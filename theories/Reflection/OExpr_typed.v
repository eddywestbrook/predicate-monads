Require Export PredMonad.Reflection.OrderedType.
Require Export PredMonad.Reflection.OrderedContext.
Require Import Coq.Logic.ProofIrrelevance.

Import EqNotations.
Import ListNotations.
Import ProofIrrelevanceTheory.


(***
 *** Ordered Expressions
 ***)

Inductive OVar A {RA:OTRelation A} : Ctx -> Type :=
| OVar_0 {ctx:Ctx} : OVar A (CtxCons A ctx)
| OVar_S {ctx:Ctx} {B} {RB:OTRelation B} :
    OVar A ctx -> OVar A (CtxCons B ctx)
.

Arguments OVar_0 {A RA ctx}.
Arguments OVar_S {A RA ctx B RB} v.

(* Expressions to represent proper functions *)
Inductive OExpr (ctx:Ctx) : forall A {RA:OTRelation A}, Type :=
| Var {A} {RA:OTRelation A} (v:OVar A ctx) : OExpr ctx A
| Embed {A} {RA:OTRelation A} (a:A) : OExpr ctx A
| App {A B:Type} {RA:OTRelation A} {RB:OTRelation B}
      (e1 : OExpr ctx (A -o> B)) (e2 : OExpr ctx A) : OExpr ctx B
| Lam {A B:Type} {RA:OTRelation A} {RB:OTRelation B}
      (e: OExpr (CtxCons A ctx) B) : OExpr ctx (A -o> B)
.

Arguments Var {ctx} {A RA} v.
Arguments Embed {ctx} {A RA} a.
Arguments App {ctx} {A B RA RB} e1 e2.
Arguments Lam {ctx} {A B RA RB} e.

(* An OExpr is valid iff all the types it contains are valid *)
Fixpoint ValidOExprProp {ctx A RA} (e:@OExpr ctx A RA) : Prop :=
  match e with
  | @Var _ A RA v =>
    OType A
  | @Embed _ A RA a =>
    OType A
  | @App _ A B RA RB e1 e2 =>
    (OType A /\ OType B) /\ (ValidOExprProp e1 /\ ValidOExprProp e2)
  | @Lam _ A B RA RB e =>
    OType A /\ ValidOExprProp e
  end.

(* Typeclass version of ValidOExprProp *)
Class ValidOExpr {ctx A RA} (e:@OExpr ctx A RA) : Prop :=
  validOExpr : ValidOExprProp e.

(* Type type of a ValidOExpr is an OType *)
Lemma OType_ValidOExpr {ctx A RA e} (valid:@ValidOExpr ctx A RA e) : OType A.
Proof.
  revert valid; induction e; simpl; intros; try assumption.
  - exact (proj2 (proj1 valid)).
  - destruct valid; apply OTarrow; [ | apply IHe ]; assumption.
Qed.

(* Only use OType_ValidOExpr if the ValidOExpr can be discharged trivially *)
Hint Immediate OType_ValidOExpr : typeclass_instances.

Instance ValidOExpr_Var ctx A RA (OA:OType A) v : ValidOExpr (@Var ctx A RA v).
Proof.
  assumption.
Qed.

Instance ValidOExpr_Embed ctx A RA (OA:OType A) a :
  ValidOExpr (@Embed ctx A RA a).
Proof.
  assumption.
Qed.

Instance ValidOExpr_App ctx A RA B RB (OB:OType B) e1 e2 :
  ValidOExpr e1 -> ValidOExpr e2 -> ValidOExpr (@App ctx A B RA RB e1 e2).
Proof.
  intros; split; split; eauto with typeclass_instances.
Qed.

Instance ValidOExpr_Lam ctx A RA (OA:OType A) B RB e :
  ValidOExpr e -> ValidOExpr (@Lam ctx A B RA RB e).
Proof.
  intros; split; eauto with typeclass_instances.
Qed.


(***
 *** Semantics of Ordered Expressions
 ***)

(* We need versions of proj1 and proj2 that actually compute *)
Definition proj1c {P Q:Prop} (pf:P /\ Q) : P :=
  match pf with conj pf1 _ => pf1 end.
Arguments proj1c {P Q} !pf.
Definition proj2c {P Q:Prop} (pf:P /\ Q) : Q :=
  match pf with conj _ pf2 => pf2 end.
Arguments proj2c {P Q} !pf.


(* The semantics of a variable *)
Fixpoint varSemantics {A} {RA:OTRelation A} {ctx} (v:OVar A ctx) :
  CtxElem ctx -o> A :=
  match v in OVar _ ctx return CtxElem ctx -o> A with
  | OVar_0 => snd_pfun (A:=CtxElem _)
  | OVar_S v' => compose_pfun fst_pfun (varSemantics v')
  end.
Arguments varSemantics {A RA ctx} !v.

(* The semantics of an ordered expression *)
Fixpoint exprSemantics {ctx A RA} {validC:ValidCtx ctx}
        (e:@OExpr ctx A RA) :
  forall {validE:ValidOExpr e}, CtxElem ctx -o> A :=
  match e in OExpr _ A return ValidOExpr e -> CtxElem ctx -o> A with
  | Var v => fun _ => varSemantics v
  | @Embed _ A _ a => fun (_:OType A) => const_pfun a
  | App e1 e2 =>
    fun validE =>
      pfun_apply (exprSemantics e1 (validE:=proj1c (proj2c validE)))
                 (exprSemantics e2 (validE:=proj2c (proj2c validE)))
  | Lam e =>
    fun validE =>
      pfun_curry
        (exprSemantics (ctx:=CtxCons _ _) (validC:=conj (proj1c validE) validC)
                       e (validE:=proj2c validE))
  end.
Arguments exprSemantics {ctx A RA validC} !e {validE}.

(* Lemma: the validC and validE arguments to exprSemantics are irrelevant *)
Lemma exprSemantics_irrel {ctx A RA} e validC1 validC2 validE1 validE2 :
  @exprSemantics ctx A RA validC1 e validE1
  =o= @exprSemantics ctx A RA validC2 e validE2.
Proof.
  revert validC1 validC2 validE1 validE2; induction e; intros;
    try reflexivity; simpl.
  - split; repeat intro; simpl; reflexivity.
  - f_equiv; [ apply IHe1 | apply IHe2 ].
  - f_equiv. apply IHe.
Qed.

(* FIXME: we could remove some uses of proof irrelevance below by proving that
exprSemantics does not care about its validE argument... *)


(***
 *** Relating Ordered Expressions
 ***)

(* Captures that validity of e1 implies validity of e2 *)
Definition implValid {ctx A RA} (e1 e2:@OExpr ctx A RA) : Prop :=
  ValidOExpr e1 -> ValidOExpr e2.

Instance PreOrder_implValid {ctx A RA} : PreOrder (@implValid ctx A RA).
Proof.
  split; unfold implValid.
  - intro e; intros; assumption.
  - intros e1 e2 e3 equi12 equi23 v.
    apply equi23; apply equi12; assumption.
Qed.

(* Two expressions are equi-valid iff one being valid implies the other is *)
Definition equiValid {ctx A RA} (e1 e2:@OExpr ctx A RA) : Prop :=
  ValidOExpr e1 <-> ValidOExpr e2.

Instance Equivalence_equiValid {ctx A RA} : Equivalence (@equiValid ctx A RA).
Proof.
  split; unfold equiValid.
  - intros e; reflexivity.
  - intros e1 e2 equi; symmetry; apply equi.
  - intros e1 e2 e3 equi12 equi23.
    etransitivity; [ apply equi12 | apply equi23 ].
Qed.

(* Two expressions are related iff their semantics are *)
Definition oexpr_R {ctx A RA} (e1 e2:@OExpr ctx A RA) : Prop :=
  equiValid e1 e2 /\
  forall `{ValidCtx ctx} {v1:ValidOExpr e1} {v2:ValidOExpr e2},
    exprSemantics e1 <o= exprSemantics e2.
Arguments oexpr_R {ctx A RA} e1 e2 : simpl never.

(* oexpr_R is a PreOrder *)
Instance PreOrder_oexpr_R ctx A {RA} : PreOrder (@oexpr_R ctx A RA).
Proof.
  unfold oexpr_R; split; split; intros.
  - reflexivity.
  - assert (OType A); [ typeclasses eauto | ].
    erewrite exprSemantics_irrel; reflexivity.
  - destruct H; destruct H0; transitivity y; assumption.
  - destruct H; destruct H0.
    assert (ValidOExpr y); [ apply H; assumption | ].
    transitivity (exprSemantics y); [ apply H2 | apply H3 ].
Qed.

(* Two expressions are equivalent iff their semantics are *)
Definition oexpr_eq {ctx A RA} (e1 e2:@OExpr ctx A RA) : Prop :=
  equiValid e1 e2 /\
  forall `{ValidCtx ctx} {v1:ValidOExpr e1} {v2:ValidOExpr e2},
    exprSemantics e1 =o= exprSemantics e2.
Arguments oexpr_eq {ctx A RA} e1 e2 : simpl never.

(* oexpr_eq is an Equivalence *)
Instance Equivalence_oexpr_eq ctx A {RA} : Equivalence (@oexpr_eq ctx A RA).
Proof.
  unfold oexpr_eq; split; split; intros.
  - reflexivity.
  - erewrite exprSemantics_irrel; reflexivity.
  - destruct H; symmetry; assumption.
  - destruct H; symmetry. apply H1.
  - destruct H; destruct H0; transitivity y; assumption.
  - destruct H; destruct H0.
    assert (ValidOExpr y); [ apply H; assumption | ].
    transitivity (exprSemantics y); [ apply H2 | apply H3 ].
Qed.

Notation "x <e= y" :=
  (oexpr_R x y) (no associativity, at level 70).
Notation "x =e= y" :=
  (oexpr_eq x y) (no associativity, at level 70).

(* oexpr_eq is the symmetric closure of oexpr_R *)
Lemma oexpr_R_oexpr_eq ctx A {RA} (e1 e2: @OExpr ctx A RA) :
  (e1 <e= e2 /\ e2 <e= e1) <-> e1 =e= e2.
Proof.
  split; intros; [ split | split; split ]; intros;
    destruct_ands; destruct H; try assumption.
  - destruct H1. split; [ apply H2 | apply H3 ].
  - destruct (H1 H0 v1 v2); assumption.
  - symmetry; assumption.
  - destruct (H1 H0 v2 v1); assumption.
Qed.

(* Tactic to destruct an e1 =e= e2 into an e1 <e= e2 and e2 <e= e1 *)
Ltac destruct_oexpr_eq H :=
  destruct (proj2 (oexpr_R_oexpr_eq _ _ _ _) H).


(* The Embed constructor is Proper w.r.t. ot_R and oexpr_R *)
Instance Proper_Embed ctx A RA :
  Proper (ot_R ==> oexpr_R) (@Embed ctx A RA).
Proof.
  intros a1 a2 Ra; split.
  - unfold equiValid; simpl; reflexivity.
  - intros; simpl.
    rewrite (proof_irrelevance _ v1 v2).
    apply Proper_const_pfun. assumption.
Qed.

(* The Embed constructor is Proper w.r.t. ot_equiv and oexpr_eq *)
Instance Proper_Embed_eq ctx A RA :
  Proper (ot_equiv ==> oexpr_eq) (@Embed ctx A RA).
Proof.
  intros a1 a2 Ra; split.
  - unfold equiValid; simpl; reflexivity.
  - intros; simpl.
    rewrite (proof_irrelevance _ v1 v2).
    apply Proper_const_pfun_equiv. assumption.
Qed.

(* The App constructor is Proper *)
Instance Proper_App ctx A B RA RB :
  Proper (oexpr_R ==> oexpr_R ==> oexpr_R) (@App ctx A B RA RB).
Proof.
  intros f1 f2 Rf a1 a2 Ra. destruct Rf; destruct Ra. split.
  - unfold equiValid in * |- *; simpl. rewrite H. rewrite H1. reflexivity.
  - simpl; intros. apply Proper_pfun_apply; [ apply H0 | apply H2 ].
Qed.

(* The App constructor is Proper for equivalence *)
Instance Proper_App_eq ctx {A B RA RB} :
  Proper (oexpr_eq ==> oexpr_eq ==> oexpr_eq) (@App ctx A B RA RB).
Proof.
  intros f1 f2 Rf a1 a2 Ra. destruct Rf; destruct Ra. split.
  - unfold equiValid in * |- *; simpl. rewrite H. rewrite H1. reflexivity.
  - simpl; intros. apply Proper_pfun_apply_equiv; [ apply H0 | apply H2 ].
Qed.

(* The Lam constructor is Proper *)
Instance Proper_Lam ctx {A B RA RB} :
  Proper (oexpr_R ==> oexpr_R) (@Lam ctx A B RA RB).
Proof.
  intros e1 e2 Re. destruct Re. split.
  - unfold equiValid in * |- *; simpl. rewrite H. reflexivity.
  - simpl; intros. apply Proper_pfun_curry.
    destruct v1. destruct v2. unfold proj1c. unfold proj2c.
    erewrite exprSemantics_irrel; apply H0.
    Unshelve. assumption.
Qed.

(* The Lam constructor is Proper for equivalence *)
Instance Proper_Lam_eq ctx {A B RA RB} :
  Proper (oexpr_eq ==> oexpr_eq) (@Lam ctx A B RA RB).
Proof.
  intros e1 e2 Re. destruct Re. split.
  - unfold equiValid in * |- *; simpl. rewrite H. reflexivity.
  - simpl; intros. apply Proper_pfun_curry_equiv.
    destruct v1. destruct v2. unfold proj1c. unfold proj2c.
    erewrite exprSemantics_irrel; apply H0.
    Unshelve. assumption.
Qed.


(***
 *** Weakening for Ordered Expressions
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

(* Correctness of weakenOVar: it is equivalent to weaken_pfun *)
Lemma weakenOVar_correct w W {RW} {OW:OType W} {ctx A RA}
      {OA:OType A} {valid:ValidCtx ctx} v :
  varSemantics (@weakenOVar w W RW ctx A RA v) =o=
  compose_pfun (weaken_pfun w W ctx) (varSemantics v).
Proof.
  revert ctx valid v; induction w; intros; [ | destruct v; destruct valid ]; simpl.
  - reflexivity.
  - rewrite compose_pair_snd. reflexivity.
  - rewrite compose_compose_pfun. rewrite compose_pair_fst.
    rewrite <- compose_compose_pfun. f_equiv. apply IHw. assumption.
Qed.

(* Weakening / lifting of ordered expressions *)
Fixpoint weakenOExpr w W {RW:OTRelation W} {ctx} {A} {RA:OTRelation A}
         (e:OExpr ctx A) : OExpr (ctxInsert w W ctx) A :=
  match e in OExpr _ A return OExpr (ctxInsert w W ctx) A with
  | Var v => Var (weakenOVar w W v)
  | Embed a => Embed a
  | App e1 e2 => App (weakenOExpr w W e1) (weakenOExpr w W e2)
  | Lam e => Lam (weakenOExpr (S w) W e)
  end.

(* A weakening is valid iff the original expr is *)
Lemma weakenOExpr_equiValid w W {RW:OTRelation W} {ctx} {A} {RA:OTRelation A}
      (e:OExpr ctx A) :
  ValidOExpr e <-> ValidOExpr (weakenOExpr w W e).
Proof.
  revert w; induction e; intros; simpl; try reflexivity.
  - rewrite IHe1. rewrite IHe2. reflexivity.
  - rewrite <- (IHe (S w)). reflexivity.
Qed.

(* Weakening preserves validity of OExprs *)
Instance ValidOExpr_weakenOExpr w W {RW:OTRelation W}
         {ctx A RA} (e:@OExpr ctx A RA) {validE:ValidOExpr e} :
  ValidOExpr (@weakenOExpr w W RW ctx A RA e).
Proof.
  apply weakenOExpr_equiValid. assumption.
Qed.

(* Commonly-used special case of ValidOExpr_weakenOExpr *)
Instance ValidOExpr_weakenOExpr0 W {RW:OTRelation W}
         {ctx A RA} (e:@OExpr ctx A RA) {validE:ValidOExpr e} :
  ValidOExpr (ctx:=CtxCons W ctx) (@weakenOExpr 0 W RW ctx A RA e).
Proof.
  apply (ValidOExpr_weakenOExpr 0 W (ctx:=ctx)). assumption.
Qed.

(* Correctness of weakenOExpr: it is equivalent to weaken_pfun *)
Lemma weakenOExpr_correct w W {RW} {ctx A RA} (e:OExpr ctx A)
      {validC:ValidCtx ctx} {validE:ValidOExpr e}
      {validC':ValidCtx (ctxInsert w W ctx)}
      {validE':ValidOExpr (weakenOExpr w W e)} :
  exprSemantics (@weakenOExpr w W RW ctx A RA e) =o=
  compose_pfun (weaken_pfun w W ctx) (exprSemantics e).
  assert (OType W); [ apply (OType_ctxInsert w W ctx); assumption | ].
  revert w validC' validE'; induction e; intros; simpl.
  - apply weakenOVar_correct; assumption.
  - rewrite compose_f_const_pfun; try typeclasses eauto.
    split; repeat intro; rewrite H0; reflexivity.
  - destruct validE as [ [OA OB] [validE1 validE2]].
    rewrite compose_pfun_apply; try typeclasses eauto.
    f_equiv.
    + erewrite exprSemantics_irrel. apply IHe1.
    + erewrite exprSemantics_irrel. apply IHe2.
  - destruct validE as [OA validE].
    rewrite compose_pfun_curry; try typeclasses eauto. f_equiv.
    erewrite exprSemantics_irrel. apply (IHe _ _ (S w)).
    Unshelve.
    + assumption.
    + destruct validE'; destruct_ands; assumption.
    + assumption.
    + destruct validE'; destruct_ands; assumption.
    + typeclasses eauto.
    + split; assumption.
    + destruct validE'; destruct_ands; assumption.
Qed.

(* Proper-ness of weakenOExpr *)
Instance Proper_weakenOExpr w W {RW} {ctx A RA} :
  Proper (oexpr_R ==> oexpr_R) (@weakenOExpr w W RW ctx A RA).
Proof.
  intros e1 e2 Re. destruct Re; split; intros.
  - unfold equiValid. repeat rewrite <- weakenOExpr_equiValid. apply H.
  - destruct ((proj2 (ValidCtx_ctxInsert_iff w W ctx)) H1).
    assert (ValidOExpr e1); [ rewrite weakenOExpr_equiValid; apply v1 | ].
    assert (ValidOExpr e2); [ rewrite weakenOExpr_equiValid; apply v2 | ].
    rewrite weakenOExpr_correct. rewrite weakenOExpr_correct.
    rewrite H0. reflexivity.
    Unshelve.
    + assumption.
    + assumption.
    + assumption.
Qed.


(* Proper-ness of weakenOExpr *)
Instance Proper_weakenOExpr_equiv w W {RW} {ctx A RA} :
  Proper (oexpr_eq ==> oexpr_eq) (@weakenOExpr w W RW ctx A RA).
Proof.
  intros e1 e2 Re. destruct_oexpr_eq Re.
  apply oexpr_R_oexpr_eq; split; apply Proper_weakenOExpr; assumption.
Qed.


(***
 *** Substitution for Ordered Variables
 ***)

(* Substitution for ordered expression variables *)
Fixpoint substOVar n {ctx} {A} {RA:OTRelation A} :
  OVar A ctx -> OExpr (ctxSuffix n ctx) (ctxNth n ctx) ->
  OExpr (ctxDelete n ctx) A :=
  match n return
        OVar A ctx -> OExpr (ctxSuffix n ctx) (ctxNth n ctx) ->
        OExpr (ctxDelete n ctx) A
  with
  | 0 =>
    fun v =>
      match v in OVar _ ctx return
            OExpr (ctxSuffix 0 ctx) (ctxNth 0 ctx) -> OExpr (ctxDelete 0 ctx) A
      with
      | OVar_0 => fun s => s
      | OVar_S v' => fun _ => Var v'
    end
  | S n' =>
    fun v =>
      match v in OVar _ ctx return
            OExpr (ctxSuffix (S n') ctx) (ctxNth (S n') ctx) ->
            OExpr (ctxDelete (S n') ctx) A
      with
      | OVar_0 =>
        fun _ => Var OVar_0
      | @OVar_S _ _ ctx' B RB v' =>
        fun s =>
          weakenOExpr 0 B (A:=A) (substOVar n' v' s)
      end
  end.
Arguments substOVar !n {ctx A RA} !v s.

(* Correctness of substOVar: it is equivalent to subst_pfun *)
Lemma substOVar_correct n {ctx A RA} (v:OVar A ctx) s
      {validC: ValidCtx ctx} {validC': ValidCtx (ctxDelete n ctx)}
      {validE: ValidOExpr s} {validE': ValidOExpr (substOVar n v s)} :
  exprSemantics (@substOVar n ctx A RA v s) =o=
  compose_pfun (subst_pfun ctx n (exprSemantics s)) (varSemantics v).
Proof.
  revert n s validC validC' validE validE'; induction v; simpl; intros;
    destruct n; destruct_ands.
  - rewrite compose_pair_snd. apply exprSemantics_irrel.
  - rewrite compose_pair_snd. reflexivity.
  - assert (OType A) as OA; [ eauto with typeclass_instances | ].
    rewrite compose_compose_pfun. rewrite compose_pair_fst.
    rewrite id_compose_pfun. reflexivity.
  - assert (OType A) as OA; [ eauto with typeclass_instances | ].
    simpl. rewrite (weakenOExpr_correct 0). unfold weaken_pfun.
    rewrite compose_compose_pfun. rewrite compose_pair_fst.
    rewrite <- compose_compose_pfun. f_equiv. apply IHv.
    Unshelve.
    + destruct validC'. assumption.
    + simpl in validE'.
      apply (proj2 (weakenOExpr_equiValid _ _ _) validE').
Qed.

Lemma equiValid_substOVar_equiValid n {ctx A RA} (v:@OVar A RA ctx) s1 s2 :
  equiValid s1 s2 -> equiValid (substOVar n v s1) (substOVar n v s2).
  unfold equiValid.
  revert ctx v s1 s2; induction n; destruct v; intros; simpl; try reflexivity.
  + assumption.
  + repeat rewrite <- (weakenOExpr_equiValid 0 B _).
    apply (IHn ctx v s1 s2 H).
Qed.

(* If s and the type of v are valid then so is substOVar n v s *)
Instance ValidOExpr_substOVar n ctx A RA (v:@OVar A RA ctx) {OA:OType A}
         (s: OExpr _ (ctxNth n ctx)) {validS: ValidOExpr s} :
  ValidOExpr (substOVar n v s).
Proof.
  revert ctx v s validS; induction n; destruct v; intros; simpl;
    eauto with typeclass_instances.
Qed.

(* substOVar is Proper in its s argument *)
Instance Proper_substOVar n {ctx A RA} v :
  Proper (oexpr_R ==> oexpr_R) (@substOVar n ctx A RA v).
Proof.
  intros s1 s2; simpl; intro Rs. destruct Rs. split; intros.
  - apply equiValid_substOVar_equiValid. assumption.
  - revert ctx v s1 s2 H H0 H1 v1 v2; induction n; destruct v; intros;
      try reflexivity.
    + apply H0.
    + simpl. eapply (proj2 (Proper_weakenOExpr 0 B _ _ _)). Unshelve.
      split; [ apply equiValid_substOVar_equiValid; assumption | ].
      intros. apply IHn; [ assumption | ].
      intros. apply H0.
Qed.

(* substOVar is Proper w.r.t. equivalence in its s argument *)
Instance Proper_substOVar_equiv n {ctx A RA} v :
  Proper (oexpr_eq ==> oexpr_eq) (@substOVar n ctx A RA v).
Proof.
  intros s1 s2 Rs; destruct_oexpr_eq Rs; split.
  - destruct Rs; apply equiValid_substOVar_equiValid; assumption.
  - intros. split; apply Proper_substOVar; assumption.
Qed.


(***
 *** Substitution for Ordered Expressions
 ***)

(* Substitution for ordered expressions *)
Fixpoint substOExpr n {ctx} {A} {RA:OTRelation A} (e:OExpr ctx A) :
  OExpr (ctxSuffix n ctx) (ctxNth n ctx) -> OExpr (ctxDelete n ctx) A :=
  match e with
  | Var v => fun s => substOVar n v s
  | Embed a => fun _ => Embed a
  | App e1 e2 => fun s => App (substOExpr n e1 s) (substOExpr n e2 s)
  | Lam e => fun s => Lam (substOExpr (S n) e s)
  end.
Arguments substOExpr n {ctx A RA} !e.

(* Correctness of substOExpr: it is equivalent to subst_pfun *)
Lemma substOExpr_correct n {ctx A RA} (e:OExpr ctx A) s
      {validC: ValidCtx ctx} {validC': ValidCtx (ctxDelete n ctx)}
      {validE: ValidOExpr e} {validS: ValidOExpr s}
      {validE': ValidOExpr (substOExpr n e s)} :
  exprSemantics (@substOExpr n ctx A RA e s) =o=
  compose_pfun (subst_pfun ctx n (exprSemantics s)) (exprSemantics e).
Proof.
  revert n s validC validC' validE validS validE'; induction e; simpl;
    intros; destruct_ands.
  - apply substOVar_correct.
  - symmetry. rewrite compose_f_const_pfun.
    (* FIXME: prove const_pfun is proof irrelevant somewhere else! *)
    + split; intro; intros; simpl; reflexivity.
    + eauto with typeclass_instances.
  - rewrite compose_pfun_apply; eauto with typeclass_instances.
    rewrite IHe1. rewrite IHe2. reflexivity.
  - rewrite compose_pfun_curry; eauto with typeclass_instances.
    rewrite (IHe (S n)). simpl.
    repeat f_equiv. Unshelve. eauto with typeclass_instances.
Qed.

(* If both e and s are valid, then so is substOExpr e s *)
Instance ValidOExpr_substOExpr n {ctx A RA}
         (e:@OExpr ctx A RA) (s:OExpr _ (ctxNth n ctx))
         (validE:ValidOExpr e) (validS:ValidOExpr s) :
  ValidOExpr (substOExpr n e s).
Proof.
  revert n s validE validS; induction e; intros; simpl; split_ands;
    eauto with typeclass_instances.
  - destruct validE; destruct_ands; assumption.
  - apply IHe1; destruct validE; destruct_ands; assumption.
  - apply IHe2; destruct validE; destruct_ands; assumption.
  - destruct validE; destruct_ands; assumption.
  - apply (IHe (S n)); destruct validE; destruct_ands; assumption.
Qed.

(* If substOExpr e s is valid then e is, but s need not be valid if e does not
contain a free variable that s gets substituted for *)
Lemma substOExpr_ValidOExpr n {ctx A RA} (e:@OExpr ctx A RA) s
      (validE:ValidOExpr (substOExpr n e s)) : ValidOExpr e.
  revert n s validE; induction e; intros; simpl; split_ands;
    eauto with typeclass_instances.
  - destruct validE; destruct_ands.
    refine (OType_ValidOExpr (IHe2 n s _)).
  - apply (IHe1 n s). destruct validE; destruct_ands. assumption.
  - apply (IHe2 n s). destruct validE; destruct_ands. assumption.
  - destruct validE; destruct_ands. assumption.
  - destruct validE; destruct_ands. apply (IHe _ _ H0).
Qed.


(* FIXME: cannot prove this because the equiValid condition only holds when we
already know that the s arguments are valid *)
(*
Instance Proper_substOExpr n {ctx A RA} :
  Proper (oexpr_R ==> oexpr_R ==> oexpr_R) (@substOExpr n ctx A RA).
Proof.
  intros e1 e2 Re s1 s2 Rs. destruct Re. destruct Rs.
 *)

(* The Beta rule for ordered expressions *)
Lemma OExpr_Beta ctx A `{OTRelation A} B `{OTRelation B}
      (e1: OExpr (CtxCons A ctx) B) (e2: OExpr ctx A)
      {validE: ValidOExpr e2} :
  App (Lam e1) e2 =e= substOExpr 0 e1 e2.
Proof.
  split.
  - unfold equiValid. simpl.
    split; intro; split_ands; destruct_ands; eauto with typeclass_instances.
    + apply (@ValidOExpr_substOExpr 0 (@CtxCons A _ ctx)); assumption.
    + apply (substOExpr_ValidOExpr _ _ _ H1).
  - intros. simpl.
    rewrite pfun_apply_pfun_curry; eauto with typeclass_instances.
    rewrite (substOExpr_correct 0 (ctx:=CtxCons A ctx)). simpl.
    f_equiv. reflexivity.
Qed.


(***
 *** Other OExpr Rewrite Rules
 ***)

Lemma OExpr_fst_pair ctx A `{OType A} B `{OType B}
      (e1: OExpr ctx A) (e2: OExpr ctx B) {validE: ValidOExpr e2} :
  App (Embed (ofst (A:=A) (B:=B))) (App (App (Embed opair) e1) e2) =e= e1.
Proof.
  split.
  - split; simpl; intros; destruct_ands; split_ands; typeclasses eauto.
  - split; intros a1 a2 Ra; simpl; f_equiv;
      try apply exprSemantics_irrel; assumption.
Qed.

Lemma OExpr_snd_pair ctx A `{OType A} B `{OType B}
      (e1: OExpr ctx A) (e2: OExpr ctx B) {validE: ValidOExpr e1} :
  App (Embed (osnd (A:=A) (B:=B))) (App (App (Embed opair) e1) e2) =e= e2.
Proof.
  split.
  - split; simpl; intros; destruct_ands; split_ands; typeclasses eauto.
  - split; intros a1 a2 Ra; simpl; f_equiv;
      try apply exprSemantics_irrel; assumption.
Qed.

Lemma OExpr_pair_eta ctx A `{OType A} B `{OType B} (e: OExpr ctx (A*B)) :
  (App (App (Embed opair) (App (Embed ofst) e)) (App (Embed osnd) e))
  =e= e.
Proof.
  split.
  - split; simpl; intros; destruct_ands; split_ands; typeclasses eauto.
  - split; intros c1 c2 Rc; split; simpl; rewrite Rc; f_equiv; f_equiv;
      apply exprSemantics_irrel.
Qed.

Hint Rewrite OExpr_fst_pair OExpr_snd_pair OExpr_pair_eta : osimpl.
Opaque ofst osnd opair.


(***
 *** Quoting Tactic for Ordered Expressions
 ***)

(* Specially-marked versions of fst and snd just used for quoting OExprs *)
Definition celem_head {ctx A RA} (celem: CtxElem (@CtxCons A RA ctx)) : A :=
  let (_,head) := celem in head.
Definition celem_rest {ctx A RA} (celem: CtxElem (@CtxCons A RA ctx)) :
  CtxElem ctx :=
  let (rest,_) := celem in rest.

(* Typeclass for incrementally quoting functions into OExpr variables, by
peeling off the celem_rest projections one at a time and adding them as OVar_S
constructors to the input variable to build the output variable *)
Class QuotesToVar {ctx1 ctx2 A} {RA:OTRelation A}
      (f: CtxElem ctx1 -> CtxElem ctx2) (vin: OVar A ctx2)
      (vout: OVar A ctx1) : Prop :=
  quotesToVar :
    forall c, varSemantics vin @o@ (f c) = varSemantics vout @o@ c.

Instance QuotesToVar_Base {ctx A} {RA:OTRelation A} v :
  QuotesToVar (ctx1:=ctx) (fun c => c) v v.
Proof.
  intro; reflexivity.
Qed.

Instance QuotesToVar_Step {ctx1 ctx2 A B} {RA:OTRelation A} {RB:OTRelation B}
         (f: CtxElem ctx1 -> CtxElem (CtxCons B ctx2)) vin vout
         (q: QuotesToVar f (OVar_S vin) vout) :
  QuotesToVar (fun c => celem_rest (f c)) vin vout.
Proof.
  intro. apply q.
Qed.

(* Class for quoting functions to OExprs *)
Class QuotesTo {ctx A} {RA:OTRelation A}
      (f: CtxElem ctx -> A) (e: OExpr ctx A) : Prop :=
  {
    quotesToValid : ValidOExpr e;
    quotesTo : forall vc ve c,
        f c =o= exprSemantics (validC:=vc) e (validE:=ve) @o@ c
  }.

(* Logically the same as QuotesTo, but we never build lambdas in this one, i.e.,
this only builds "atomic" OExprs *)
Class QuotesToAtomic {ctx A} {RA:OTRelation A}
      (f: CtxElem ctx -> A) (e: OExpr ctx A) : Prop :=
  quotesToAtomic : QuotesTo f e.

(* Quote any term of functional type to a lambda *)
Instance QuotesTo_Lam {ctx A B} `{OType A} `{OTRelation B}
      (f: CtxElem ctx -> A -o> B) e
      (q: QuotesTo (fun c => f (celem_rest c) @o@ (celem_head c)) e) :
  QuotesTo f (Lam e) | 2.
Proof.
  split.
  - apply ValidOExpr_Lam; try assumption. apply quotesToValid.
  - assert (OType B);
      [ apply (OType_ValidOExpr (quotesToValid (QuotesTo:=q))) | ].
    intros; split; intro; intros; simpl;
      rewrite <- H2; rewrite <- (quotesTo (QuotesTo:=q)); reflexivity.
Qed.

(* Special case: quote ofuns as lambdas, destructuring the ofun *)
Instance QuotesTo_Lam_ofun {ctx A B} `{OType A} `{OTRelation B}
         (f: CtxElem ctx -> A -> B) prp e
         (q: QuotesTo (fun c => f (celem_rest c) (celem_head c)) e) :
  QuotesTo (fun c => ofun (f c) (prp:=prp c)) (Lam e) | 1.
Proof.
  apply QuotesTo_Lam. assumption.
Qed.


(* Quote any non-function term as an atomic OExpr *)
Instance QuotesTo_Atomic {ctx A} {RA:OTRelation A} (f: CtxElem ctx -> A) e
         (q: QuotesToAtomic f e) :
  QuotesTo f e | 3 := q.

(*
Ltac solve_QuotesTo :=
  first [ apply QuotesTo_Lam_ofun | apply QuotesTo_Lam | apply QuotesTo_Atomic ].

Hint Extern 1 (QuotesTo _ _) => solve_QuotesTo : typeclass_instances.
 *)

(* Quote any use of celem_head as a var *)
Instance QuotesTo_Var {ctx1 ctx2 A} `{OType A} {valid:ValidCtx ctx1}
         (f: CtxElem ctx1 -> CtxElem (CtxCons A ctx2)) v
         (q: QuotesToVar f OVar_0 v) :
  QuotesToAtomic (fun c => celem_head (f c)) (Var v) | 1.
Proof.
  split; try assumption.
  intros; rewrite <- (quotesToVar (QuotesToVar:=q)). simpl.
  destruct (f c). reflexivity.
Qed.

(* Special case for an eta-reduced celem_head application *)
Instance QuotesTo_Var0 {ctx A} `{OType A} {valid:ValidCtx ctx} :
  QuotesToAtomic (@celem_head ctx A _) (Var OVar_0) | 1.
Proof.
  split; try typeclasses eauto.
  intros. reflexivity.
Qed.

(* Quote applications as OExpr applications, where the function must still be
atomic but the argument need not  be *)
Instance QuotesTo_App {ctx A B} `{OTRelation A} `{OType B}
         (f1: CtxElem ctx -> A -o> B) (f2: CtxElem ctx -> A) e1 e2
         (q1: QuotesToAtomic f1 e1) (q2: QuotesTo f2 e2) :
  QuotesToAtomic (fun c => (f1 c) @o@ (f2 c)) (App e1 e2) | 1.
Proof.
  split.
  - simpl; split_ands; [ | assumption | apply q1 | apply q2 ].
    apply (OType_ValidOExpr (e:=e2)). apply q2.
  - intros. simpl. f_equiv.
    + apply (quotesTo (QuotesTo:=q1)).
    + apply (quotesTo (QuotesTo:=q2)).
Qed.

(* Quote ofuns in atomic position as lambdas *)
Instance QuotesToAtomic_ofun {ctx A B} `{OType A} `{OTRelation B}
         (f: CtxElem ctx -> A -> B) prp e
         (q: QuotesTo (fun c => f (celem_rest c) (celem_head c)) e) :
  QuotesToAtomic (fun c => ofun (f c) (prp:=prp c)) (Lam e) | 1.
Proof.
  apply QuotesTo_Lam. assumption.
Qed.

(* Quote objects that are independent of the context as embedded objects, but at
low priority *)
Instance QuotesTo_Embed {ctx A} `{OType A} {valid:ValidCtx ctx} (a:A) :
  QuotesToAtomic (ctx:=ctx) (fun _ => a) (Embed a) | 2.
Proof.
  split; [ assumption | ].
  intros. reflexivity.
Qed.

(* Quote pairs as applications of opair *)
Instance QuotesTo_pair {ctx A B} `{OType A} `{OType B}
         (a: CtxElem ctx -> A) (b: CtxElem ctx -> B) e1 e2
         (q1: QuotesTo a e1) (q2: QuotesTo b e2) :
  QuotesToAtomic (fun c => (a c, b c)) (App (App (Embed opair) e1) e2) | 1.
Proof.
  destruct q1. destruct q2.
  split; [ simpl; split_ands; typeclasses eauto | ].
  intros. simpl. rewrite <- quotesTo0. rewrite <- quotesTo1. reflexivity.
Qed.

(* Quote applications of fst as applications of ofst *)
Instance QuotesTo_fst {ctx A B} `{OType A} `{OType B}
         (f: CtxElem ctx -> A * B) e (q: QuotesTo f e) :
  QuotesToAtomic (fun c => fst (f c)) (App (Embed ofst) e) | 1.
Proof.
  destruct q.
  split; [ simpl; split_ands; typeclasses eauto | ].
  intros. simpl. rewrite <- quotesTo0. reflexivity.
Qed.

(* Quote applications of fst as applications of ofst *)
Instance QuotesTo_snd {ctx A B} `{OType A} `{OType B}
         (f: CtxElem ctx -> A * B) e (q: QuotesTo f e) :
  QuotesToAtomic (fun c => snd (f c)) (App (Embed osnd) e) | 1.
Proof.
  destruct q.
  split; [ simpl; split_ands; typeclasses eauto | ].
  intros. simpl. rewrite <- quotesTo0. reflexivity.
Qed.


(*
Instance QuotesTo_Lam1 {ctx A B} `{OType A} `{OType B} `{ValidCtx ctx}
         (f: CtxElem ctx -> A -> B) prp e
         (q: QuotesTo (fun c => f (celem_rest c) (celem_head c)) e) :
  QuotesTo (fun c => {| pfun_app := f c; pfun_Proper := prp c |}) (Lam e) | 1.
Proof.
  intros c; split; intros a1 a2 Ra; simpl.
  - rewrite <- (q (c, a2)). rewrite Ra. reflexivity.
  - rewrite <- (q (c, a1)). rewrite <- Ra. reflexivity.
Qed.

Instance QuotesTo_Lam2 {ctx A B} `{OType A} `{OType B} `{ValidCtx ctx}
         (f: CtxElem ctx -> A -> B) prp e
         (q: QuotesTo (fun c => f (celem_rest c) (celem_head c)) e) :
  QuotesTo (fun c => ofun (f c) (prp:=prp c)) (Lam e)| 1.
Proof.
  unfold ofun. apply QuotesTo_Lam1. assumption.
Qed.
*)


Lemma oquote_R {A} {RA:OTRelation A} {f1 f2 : A} {e1 e2: OExpr CtxNil A}
      {q1: QuotesTo (fun _ => f1) e1} {q2: QuotesTo (fun _ => f2) e2} :
  e1 <e= e2 -> f1 <o= f2.
Proof.
  intro R12.
  assert (ValidOExpr e1); [ apply q1 | ].
  assert (ValidOExpr e2); [ apply q2 | ].
  transitivity (exprSemantics e1 @o@ tt);
    [ | transitivity (exprSemantics e2 @o@ tt) ].
  - apply (quotesTo (QuotesTo:=q1)).
  - apply R12. reflexivity.
  - apply (quotesTo (QuotesTo:=q2)).
Qed.

Lemma oquote_eq {A} {RA:OTRelation A} {f1 f2 : A} {e1 e2: OExpr CtxNil A}
      {q1: QuotesTo (fun _ => f1) e1} {q2: QuotesTo (fun _ => f2) e2} :
  e1 =e= e2 -> f1 =o= f2.
Proof.
  intros eq12. rewrite <- oexpr_R_oexpr_eq in eq12. destruct eq12.
  split; apply oquote_R; assumption.
Qed.

(* Translate a problem about proper functions into one about OExprs, by
"quoting" both sides *)
Ltac oquote :=
  lazymatch goal with
  | |- ?e1 =o= ?e2 =>
    apply oquote_eq
  | |- ?e1 <o= ?e2 =>
    apply oquote_R
  end.

Ltac oexpr_simpl :=
  rewrite_strat (bottomup (choice (OExpr_Beta ; eval simpl) (hints osimpl))).

(* Translate a problem about proper functions into one about OExprs by calling
oquote, simplify both sides using the osimpl rewrite database, and then try to
use reflexivity, going back to proper functions if that does not work *)
Ltac osimpl :=
  simpl; oquote; try oexpr_simpl; try reflexivity; try typeclasses eauto; simpl.


(***
 *** Unquoting
 ***)

(* Class for unquoting OVars to functions *)
Class UnQuotesToVar {ctx A} {RA:OTRelation A}
      (v: OVar A ctx) (f: CtxElem ctx -> A) : Prop :=
  { unQuotesToVarProper : Proper (ot_R ==> ot_R) f;
    unQuotesToVar : forall c, f c = varSemantics v @o@ c }.

Instance UnQuotesToVar_Base A RA ctx :
  UnQuotesToVar (@OVar_0 A RA ctx) snd.
Proof.
  split.
  - typeclasses eauto.
  - intros; reflexivity.
Qed.

Instance UnQuotesToVar_Step A RA ctx B RB (v:OVar A ctx) f
         (q: UnQuotesToVar v f) :
  UnQuotesToVar (@OVar_S A RA ctx B RB v) (fun c => f (fst c)).
Proof.
  split.
  - intros c1 c2 Rc. apply (unQuotesToVarProper (UnQuotesToVar:=q)).
    f_equiv. assumption.
  - intros; apply q.
Qed.


(* Class for unquoting OExprs to functions *)
Class UnQuotesTo {ctx A} {RA:OTRelation A}
      (e: OExpr ctx A) (f: CtxElem ctx -> A) : Prop :=
  {
    unQuotesToValidC : ValidCtx ctx;
    unQuotesToValidE : ValidOExpr e;
    unQuotesTo : forall vc ve c,
        f c =o= exprSemantics (validC:=vc) e (validE:=ve) @o@ c
  }.

Instance UnQuotesTo_Var ctx `{ValidCtx ctx} A `{OType A} (v:OVar A ctx) f
         (q: UnQuotesToVar v f) :
  UnQuotesTo (Var v) f | 1.
Proof.
  split; [ assumption | apply H0 | ].
  intros. rewrite (unQuotesToVar (UnQuotesToVar:=q) c). reflexivity.
Qed.

Instance UnQuotesTo_Embed ctx `{ValidCtx ctx} A `{OType A} (a:A) :
  UnQuotesTo (@Embed ctx A _ a) (fun _ => a) | 1.
Proof.
  split; try assumption.
  intros. reflexivity.
Qed.

Instance UnQuotesTo_App {ctx A B} `{OTRelation A} `{OType B}
         e1 e2 (f1: CtxElem ctx -> A -o> B) (f2: CtxElem ctx -> A)
         (q1: UnQuotesTo e1 f1) (q2: UnQuotesTo e2 f2) :
  UnQuotesTo (App e1 e2) (fun c => (f1 c) @o@ (f2 c)) | 1.
Proof.
  split.
  - apply q1.
  - simpl; split_ands; [ | assumption | apply q1 | apply q2 ].
    apply (OType_ValidOExpr (e:=e2)). apply q2.
  - intros. simpl. f_equiv.
    + apply (unQuotesTo (UnQuotesTo:=q1)).
    + apply (unQuotesTo (UnQuotesTo:=q2)).
Qed.

Lemma Proper_unQuotesTo {ctx A B} `{OTRelation A} `{OTRelation B}
      {e: OExpr (CtxCons A ctx) B} {f} (q: UnQuotesTo e f) c :
  Proper (ot_R ==> ot_R) (fun a => f (c, a)).
Proof.
  intros a1 a2 Ra.
  assert (ValidOExpr e); [ apply q | ].
  destruct (unQuotesToValidC (UnQuotesTo:=q)).
  etransitivity; [ apply (unQuotesTo (UnQuotesTo:=q)) | ].
  etransitivity; [ | apply (unQuotesTo (UnQuotesTo:=q)) ].
  f_equiv. split; [ reflexivity | assumption ].
Qed.

Instance UnQuotesTo_Lam {ctx A B} `{OTRelation A} `{OTRelation B}
      (e: OExpr (CtxCons A ctx) B) f (q: UnQuotesTo e f) :
  UnQuotesTo (Lam e) (fun c =>
                        ofun (fun a => f (c, a))
                             (prp:=Proper_unQuotesTo q c)) | 1.
Proof.
  destruct (unQuotesToValidC (UnQuotesTo:=q)).
  split.
  - assumption.
  - apply ValidOExpr_Lam; apply q.
  - assert (OType B);
      [ apply (OType_ValidOExpr (unQuotesToValidE (UnQuotesTo:=q))) | ].
    intros; split; intros a1 a2 Ra; simpl.
    + etransitivity.
      -- apply (Proper_unQuotesTo q); apply Ra.
      -- apply (unQuotesTo (UnQuotesTo:=q)).
    + etransitivity.
      -- apply (unQuotesTo (UnQuotesTo:=q)).
      -- apply (Proper_unQuotesTo q); apply Ra.
Qed.


Instance UnQuotesTo_weakenOExpr {ctx A} {RA:OTRelation A} w W `{OType W}
         (e: OExpr ctx A) f (q: UnQuotesTo e f) :
  UnQuotesTo (weakenOExpr w W e) (fun c => f (weaken_pfun w W _ @o@ c)) | 1.
Proof.
  split.
  - apply ValidCtx_ctxInsert; [ assumption | apply q ].
  - apply ValidOExpr_weakenOExpr. apply q.
  - intros. rewrite weakenOExpr_correct. simpl.
    rewrite (unQuotesTo (UnQuotesTo:=q)). reflexivity.
    Unshelve.
    apply q. apply q.
Qed.

(* This instance is meant to only apply to Coq-level variables of OExpr type *)
Instance UnQuotesTo_MetaVar {ctx A} {RA:OTRelation A} `{ValidCtx ctx}
         (e:OExpr ctx A) {validE:ValidOExpr e} :
  UnQuotesTo e (fun c => exprSemantics e @o@ c) | 2.
Proof.
  split; try assumption.
  intros. f_equiv. apply exprSemantics_irrel.
Qed.

Lemma unquote_R {ctx A} {RA:OTRelation A} {e1 e2: OExpr ctx A}
      {f1 f2 : CtxElem ctx -> A} {q1: UnQuotesTo e1 f1} {q2: UnQuotesTo e2 f2} :
  (forall c, f1 c <o= f2 c) -> e1 <e= e2.
Proof.
  intro R12.
  split; [ split; intros; try apply q1; apply q2 | ].
  intros. intros c1 c2 Rc. rewrite Rc.
  transitivity (f1 c2); [ apply (unQuotesTo (UnQuotesTo:=q1)) | ].
  transitivity (f2 c2); [ | apply (unQuotesTo (UnQuotesTo:=q2)) ].
  apply R12.
Qed.

Lemma unquote_eq {ctx A} {RA:OTRelation A} {e1 e2: OExpr ctx A}
      {f1 f2 : CtxElem ctx -> A} {q1: UnQuotesTo e1 f1} {q2: UnQuotesTo e2 f2} :
  (forall c, f1 c =o= f2 c) -> e1 =e= e2.
Proof.
  intro R12. apply oexpr_R_oexpr_eq.
  split; apply unquote_R; apply R12.
Qed.


(***
 *** Old Version of Quoting Tactic, using Ltac Directly
 ***)

(*
Tactic Notation "unify'" open_constr(t) open_constr(u) :=
  assert(t = u); [refine eq_refl|].
*)

(*
Lemma ltac_oquote_R {A RA} (e1 e2 : @OExpr CtxNil A RA) :
  e1 <e= e2 -> (exprSemantics e1) @o@ tt <o= (exprSemantics e2) @o@ tt.
Proof.
  intro R12. apply R12. reflexivity.
Qed.

Lemma ltac_oquote_eq {A RA} (e1 e2 : @OExpr CtxNil A RA) :
  e1 =e= e2 -> (exprSemantics e1) @o@ tt =o= (exprSemantics e2) @o@ tt.
Proof.
  intro equiv.
  destruct equiv; split; apply ltac_oquote_R; assumption.
Qed.

(* Quote an expression that we think corresponds to a variable *)
Ltac ltac_quote_ovar f :=
  lazymatch f with
  | (fun (celem:_) => @celem_head ?ctx ?A ?RA _) =>
    uconstr:(@OVar_0 A RA ctx)
  | (fun (celem:?ctype) => @celem_rest ?ctx ?B ?RB ?f') =>
    let qv := ltac_quote_ovar (fun (celem:ctype) => f') in
    uconstr:(@OVar_S _ _ B RB ctx qv)
  end.

(* Quote an expression-in-context, returning an OExpr that corresponds to it *)
Ltac ltac_quote_oexpr f :=
  lazymatch f with
  | (fun (celem:?ctype) => ?e1 @o@ ?e2) =>
    let q1 := ltac_quote_oexpr (fun (celem:ctype) => e1) in
    let q2 := ltac_quote_oexpr (fun (celem:ctype) => e2) in
    uconstr:(App q1 q2)
  | (fun (celem:CtxElem ?ctx) => ofun (fun (x:?A) =>?g)) =>
    let e_rec :=
        (eval simpl in
            (fun (celem':CtxElem (CtxCons A ctx)) =>
               (fun (celem:CtxElem ctx) (x:A) => g)
                 (celem_rest ctx A celem') (celem_head ctx A celem')))
    in
    let q := ltac_quote_oexpr e_rec in
    uconstr:(Lam q)
  | (fun (celem:?ctype) => celem_head _ _ _) =>
    let qv := ltac_quote_ovar f in
    uconstr:(Var qv)
  | (fun (celem:?ctype) => celem_rest _ _ _) =>
    let qv := ltac_quote_ovar f in
    uconstr:(Var qv)
  | (fun (celem:?ctype) => ?body) =>
    (* For constants, just make a fresh evar, and let the unification of the
    change tactic used later fill it in *)
    uconstr:(Embed _)
    (*
    lazymatch type of (fun (celem:ctype) => body) with
    | _ -> ?A =>
      let ename := fresh "e" in
      let res1 := evar (ename:_) in
      let e := constr:(?ename) in
      let res := unify' (fun celem => body) (fun _ => e) in
      uconstr:(Embed (ctx:=CtxNil) e)
    end
     *)
  end.

(* Quote an expression at the top level by quoting it in the empty context *)
Ltac ltac_quote_oexpr_top e :=
  ltac_quote_oexpr (fun (celem:CtxElem CtxNil) => e).

(* Translate a problem about proper functions into one about OExprs, by
"quoting" both sides *)
Ltac ltac_oquote :=
  lazymatch goal with
  | |- ?e1 =o= ?e2 =>
    let q1 := ltac_quote_oexpr_top e1 in
    let q2 := ltac_quote_oexpr_top e2 in
    (* idtac q1 "=e=" q2; *)
    apply (ltac_oquote_eq q1 q2)
  | |- ?e1 <o= ?e2 =>
    let q1 := ltac_quote_oexpr_top e1 in
    let q2 := ltac_quote_oexpr_top e2 in
    apply (ltac_oquote_R q1 q2)
  end.

(* Translate a problem about proper functions into one about OExprs by calling
oquote, simplify both sides using the osimpl rewrite database, and then try to
use reflexivity, going back to proper functions if that does not work *)
Ltac ltac_osimpl := ltac_oquote; try oexpr_simpl; try reflexivity; simpl.
*)


(***
 *** Testing the Quote Mechanism
 ***)

Module OQuoteTest.

(* A simple test case for constant terms *)
Lemma simple_quote_test A `{OType A} a : a =o= a.
  osimpl.
Qed.

(* A simple test case with all 4 OExpr constructs, that does beta-reduction *)
Lemma beta_test A `{OType A} a : (ofun (A:=A) (fun x => x)) @o@ a =o= a.
  osimpl.
Qed.

(* A test case with the first projection of a product *)
Lemma product_proj1_test A `{OType A} B `{OType B} (a:A) (b:B) :
  ofst @o@ (a ,o, b) =o= a.
  osimpl.
Qed.

(* A test case with with beta-reduction and projections + eta for products *)
Lemma beta_product_test A `{OType A} B `{OType B} (p:A*B) :
  ofun (fun p => (osnd @o@ p ,o, ofst @o@ p)) @o@ (osnd @o@ p ,o, ofst @o@ p)
  =o= p.
  (* osimpl *)
  (* NOTE: we write this out to see how long each step takes... *)
  oquote. oexpr_simpl. reflexivity. typeclasses eauto.
Qed.

Lemma double_lambda_test A `{OType A} :
  (ofun (fun (f : A -o> A) => ofun (fun x => f @o@ x))) @o@ (ofun (fun y => y))
  =o= ofun (fun x => x).
  osimpl.
Qed.

(* A test case with with beta-reduction and projections for products *)
Lemma beta_product_test2 A `{OType A} B `{OType B} :
  ofun (fun a =>
          ofun (fun b =>
                  ofun (fun p => (osnd @o@ p ,o, ofst @o@ p)) @o@ (b ,o, a)))
  =o= opair.
  (* osimpl *)
  (* NOTE: we write this out to see how long each step takes... *)
  oquote. oexpr_simpl.
  reflexivity. typeclasses eauto. typeclasses eauto.
Qed.

End OQuoteTest.
