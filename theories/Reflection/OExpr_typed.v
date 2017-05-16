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
Instance OType_ValidOExpr {ctx A RA e} (valid:@ValidOExpr ctx A RA e) : OType A.
Proof.
  revert valid; induction e; simpl; intros; try assumption.
  - exact (proj2 (proj1 valid)).
  - destruct valid; apply OTarrow; [ | apply IHe ]; assumption.
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

(* FIXME: we could remove some uses of proof irrelevance below by proving that
exprSemantics does not care about its validE argument... *)


(***
 *** Relating Ordered Expressions
 ***)

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
    rewrite (proof_irrelevance _ v1 v2). reflexivity.
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
  - rewrite (proof_irrelevance _ v1 v2); reflexivity.
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
    rewrite (proof_irrelevance _ o o0).
    apply H0.
Qed.



FIXME HERE NOW: keep going!


(* The Lam constructor is Proper for equivalence *)
Instance Proper_Lam_eq ctx {A B RA OA RB OB valid} :
  Proper (oexpr_eq ==> oexpr_eq) (@Lam ctx A B RA OA RB OB valid).
Proof.
  intros e1 e2 Re. simpl in * |- *.
  apply Proper_pfun_curry_equiv; assumption.
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
Fixpoint weakenOExpr w W {RW:OTRelation W} {OW:OType W} {ctx} {A} {RA:OTRelation A}
         (e:OExpr ctx A) : OExpr (ctxInsert w W ctx) A :=
  match e in OExpr _ A return OExpr (ctxInsert w W ctx) A with
  | Var v => Var (weakenOVar w W v)
  | Embed a => Embed a
  | App e1 e2 => App (weakenOExpr w W e1) (weakenOExpr w W e2)
  | Lam e => Lam (weakenOExpr (S w) W e)
  end.

(* Correctness of weakenOExpr: it is equivalent to weaken_pfun *)
Lemma weakenOExpr_correct w W {RW} {OW:OType W} {ctx A RA} e :
  exprSemantics (@weakenOExpr w W RW OW ctx A RA e) =o=
  compose_pfun (weaken_pfun w W ctx) (exprSemantics e).
Proof.
  revert w; induction e; intros; simpl.
  - apply weakenOVar_correct; try assumption.
    apply (OType_OExpr_type _ _ (Var v)).
  - rewrite compose_f_const_pfun; [ reflexivity | typeclasses eauto ].
  - assert (ValidCtx ctx) as valid; [ apply (ValidCtx_OExpr_ctx _ _ e1) | ].
    rewrite compose_pfun_apply; try typeclasses eauto.
    f_equiv; [ apply IHe1 | apply IHe2 ].
  - rewrite compose_pfun_curry; try assumption. Unshelve.
    f_equiv. apply (IHe (S w)).
    typeclasses eauto.
Qed.

(* Proper-ness of weakenOExpr *)
Instance Proper_weakenOExpr w W {RW} {OW:OType W} {ctx A RA} :
  Proper (oexpr_R ==> oexpr_R) (@weakenOExpr w W RW OW ctx A RA).
Proof.
  intros e1 e2 Re. unfold oexpr_R.
  assert (ValidCtx ctx) as valid; [ apply (ValidCtx_OExpr_ctx _ _ e1) | ].
  assert (OType A) as OA; [ eauto with typeclass_instances | ].
  repeat rewrite weakenOExpr_correct. f_equiv. assumption.
Qed.

(* Proper-ness of weakenOExpr *)
Instance Proper_weakenOExpr_equiv w W {RW} {OW:OType W} {ctx A RA} :
  Proper (oexpr_eq ==> oexpr_eq) (@weakenOExpr w W RW OW ctx A RA).
Proof.
  intros e1 e2 Re. destruct Re; split; apply Proper_weakenOExpr; assumption.
Qed.


(***
 *** Substitution for Ordered Expressions
 ***)

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
Arguments substOVar !n {ctx A RA} !v {valid} s.

(* Correctness of substOVar: it is equivalent to subst_pfun *)
Lemma substOVar_correct n {ctx A RA} v {valid} s :
  exprSemantics (@substOVar n ctx A RA v valid s) =o=
  compose_pfun (subst_pfun ctx n (exprSemantics s)) (varSemantics v).
Proof.
  revert n valid s; induction v; intros; destruct n; destruct valid; simpl.
  - rewrite compose_pair_snd. reflexivity.
  - rewrite compose_pair_snd. reflexivity.
  - assert (OType A) as OA; [ eauto with typeclass_instances | ].
    rewrite compose_compose_pfun. rewrite compose_pair_fst.
    rewrite id_compose_pfun. reflexivity.
  - assert (OType A) as OA; [ eauto with typeclass_instances | ].
    rewrite (weakenOExpr_correct 0). unfold weaken_pfun.
    rewrite compose_compose_pfun. rewrite compose_pair_fst.
    rewrite <- compose_compose_pfun. f_equiv. apply IHv.
Qed.

(* substOVar is Proper in its s argument *)
Instance Proper_substOVar n {ctx A RA} v {valid} :
  Proper (oexpr_R ==> oexpr_R) (@substOVar n ctx A RA v valid).
Proof.
  intros s1 s2; simpl; intro Rs.
  assert (OType A) as OA; [ eauto with typeclass_instances | ].
  repeat rewrite substOVar_correct. rewrite Rs. reflexivity.
Qed.

(* substOVar is Proper w.r.t. equivalence in its s argument *)
Instance Proper_substOVar_equiv n {ctx A RA} v {valid} :
  Proper (oexpr_eq ==> oexpr_eq) (@substOVar n ctx A RA v valid).
Proof.
  intros s1 s2 Rs; destruct Rs; split; apply Proper_substOVar; assumption.
Qed.


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
Lemma substOExpr_correct n {ctx A RA} e s :
  exprSemantics (@substOExpr n ctx A RA e s) =o=
  compose_pfun (subst_pfun ctx n (exprSemantics s)) (exprSemantics e).
Proof.
  revert n s; induction e; intros; simpl.
  - apply substOVar_correct.
  - symmetry. apply compose_f_const_pfun. eauto with typeclass_instances.
  - assert (ValidCtx ctx) as valid; [ apply (ValidCtx_OExpr_ctx _ _ e1) | ].
    rewrite compose_pfun_apply; eauto with typeclass_instances.
    rewrite IHe1. rewrite IHe2. reflexivity.
  - rewrite compose_pfun_curry; eauto with typeclass_instances.
    rewrite (IHe (S n)). reflexivity.
Qed.


(* The Beta rule for ordered expressions *)
Lemma OExpr_Beta ctx `{ValidCtx ctx} A `{OType A} B `{OType B}
      (e1: OExpr (CtxCons A ctx) B) (e2: OExpr ctx A) :
  App (Lam e1) e2 =e= substOExpr 0 e1 e2.
Proof.
  simpl. rewrite pfun_apply_pfun_curry; eauto with typeclass_instances.
  rewrite (substOExpr_correct 0 (ctx:=CtxCons A ctx)). reflexivity.
Qed.


(***
 *** Other OExpr Rewrite Rules
 ***)

Lemma OExpr_fst_pair ctx `{ValidCtx ctx} A `{OType A} B `{OType B}
      (e1: OExpr ctx A) (e2: OExpr ctx B) :
  App (Embed (ofst (A:=A) (B:=B))) (App (App (Embed opair) e1) e2) =e= e1.
Proof.
  split; intros c1 c2 Rc; simpl; apply pfun_Proper; assumption.
Qed.

Lemma OExpr_snd_pair ctx `{ValidCtx ctx} A `{OType A} B `{OType B}
      (e1: OExpr ctx A) (e2: OExpr ctx B) :
  App (Embed (osnd (A:=A) (B:=B))) (App (App (Embed opair) e1) e2) =e= e2.
Proof.
  split; intros c1 c2 Rc; simpl; apply pfun_Proper; assumption.
Qed.

Lemma OExpr_pair_eta ctx `{ValidCtx ctx} A `{OType A} B `{OType B}
      (e: OExpr ctx (A*B)) :
  (App (App (Embed opair) (App (Embed ofst) e)) (App (Embed osnd) e))
  =e= e.
Proof.
  split; intros c1 c2 Rc; split; simpl; rewrite Rc; reflexivity.
Qed.

Hint Rewrite OExpr_fst_pair OExpr_snd_pair OExpr_pair_eta : osimpl.
Opaque ofst osnd opair.


(***
 *** Quoting Tactic for Ordered Expressions
 ***)

(* Specially-marked versions of fst and snd just used for quoting OExprs *)
Definition celem_head ctx A {RA} (celem: CtxElem (@CtxCons A RA ctx)) : A :=
  let (_,head) := celem in head.
Definition celem_rest ctx A {RA} (celem: CtxElem (@CtxCons A RA ctx)) :
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
  QuotesToVar (fun c => celem_rest _ _ (f c)) vin vout.
Proof.
  intro. apply q.
Qed.

(* Class for quoting functions to OExprs *)
Class QuotesTo {ctx A} {RA:OTRelation A}
      (f: CtxElem ctx -> A) (e: OExpr ctx A) : Prop :=
  quotesTo : forall c, f c =o= exprSemantics e @o@ c.

(* Logically the same as QuotesTo, but we never build lambdas in this one, i.e.,
this only builds "atomic" OExprs *)
Class QuotesToAtomic {ctx A} {RA:OTRelation A}
      (f: CtxElem ctx -> A) (e: OExpr ctx A) : Prop :=
  quotesToAtomic : forall c, f c =o= exprSemantics e @o@ c.

(* Quote any term of functional type to a lambda *)
Instance QuotesTo_Lam {ctx A B} `{OType A} `{OType B} `{ValidCtx ctx}
      (f: CtxElem ctx -> A -o> B) e
      (q: QuotesTo (fun c => f (celem_rest _ _ c) @o@ (celem_head _ _ c)) e) :
  QuotesTo f (Lam e) | 2.
Proof.
  intros c; split; intros a1 a2 Ra; simpl.
  - rewrite <- (q (c, a2)). rewrite Ra. reflexivity.
  - rewrite <- (q (c, a1)). rewrite <- Ra. reflexivity.
Qed.

(* Special case: quote ofuns as lambdas, destructuring the ofun *)
Instance QuotesTo_Lam_ofun {ctx A B} `{OType A} `{OType B} `{ValidCtx ctx}
         (f: CtxElem ctx -> A -> B) prp e
         (q: QuotesTo (fun c => f (celem_rest _ _ c) (celem_head _ _ c)) e) :
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
Instance QuotesTo_Var {ctx1 ctx2 A} {RA:OTRelation A} {valid:ValidCtx ctx1}
         (f: CtxElem ctx1 -> CtxElem (CtxCons A ctx2)) v
         (q: QuotesToVar f OVar_0 v) :
  QuotesToAtomic (fun c => celem_head ctx2 A (f c)) (Var v) | 1.
Proof.
  assert (OType A) as OA; [ apply (OType_OVar_type _ _ v) | ].
  intro. simpl. rewrite <- (q c). reflexivity.
Qed.

(* Special case for an eta-reduced celem_head application *)
Instance QuotesTo_Var0 {ctx A} `{OType A} {valid:ValidCtx ctx} :
  QuotesToAtomic (celem_head ctx A) (Var OVar_0) | 1.
Proof.
  intro. reflexivity.
Qed.

(* Quote applications as OExpr applications, where the function must still be
atomic but the argument need not  be *)
Instance QuotesTo_App {ctx A B} `{OType A} `{OType B}
         (f1: CtxElem ctx -> A -o> B) (f2: CtxElem ctx -> A) e1 e2
         (q1: QuotesToAtomic f1 e1) (q2: QuotesTo f2 e2) :
  QuotesToAtomic (fun c => (f1 c) @o@ (f2 c)) (App e1 e2) | 1.
Proof.
  intro c. simpl. rewrite <- (q1 c). rewrite <- (q2 c). reflexivity.
Qed.

(* Quote ofuns in atomic position as lambdas *)
Instance QuotesTo_ofun {ctx A B} `{OType A} `{OType B} `{ValidCtx ctx}
         (f: CtxElem ctx -> A -> B) prp e
         (q: QuotesTo (fun c => f (celem_rest _ _ c) (celem_head _ _ c)) e) :
  QuotesToAtomic (fun c => ofun (f c) (prp:=prp c)) (Lam e) | 1.
Proof.
  apply QuotesTo_Lam. assumption.
Qed.

(* Quote objects that are independent of the context as embedded objects, but at
low priority *)
Instance QuotesTo_Embed {ctx A} `{OType A} {valid:ValidCtx ctx} (a:A) :
  QuotesToAtomic (fun _ => a) (Embed a) | 2.
Proof.
  intro. reflexivity.
Qed.

(* Quote pairs as applications of opair *)
Instance QuotesTo_pair {ctx A B} `{OType A} `{OType B} `{ValidCtx ctx}
         (a: CtxElem ctx -> A) (b: CtxElem ctx -> B) e1 e2
         (q1: QuotesTo a e1) (q2: QuotesTo b e2) :
  QuotesToAtomic (fun c => (a c, b c)) (App (App (Embed opair) e1) e2) | 1.
Proof.
  intro c. simpl. rewrite <- (q1 c). rewrite <- (q2 c). reflexivity.
Qed.

(* Quote applications of fst as applications of ofst *)
Instance QuotesTo_fst {ctx A B} `{OType A} `{OType B} `{ValidCtx ctx}
         (f: CtxElem ctx -> A * B) e (q: QuotesTo f e) :
  QuotesToAtomic (fun c => fst (f c)) (App (Embed ofst) e) | 1.
Proof.
  intro c. simpl. rewrite <- (q c). reflexivity.
Qed.

(* Quote applications of fst as applications of ofst *)
Instance QuotesTo_snd {ctx A B} `{OType A} `{OType B} `{ValidCtx ctx}
         (f: CtxElem ctx -> A * B) e (q: QuotesTo f e) :
  QuotesToAtomic (fun c => snd (f c)) (App (Embed osnd) e) | 1.
Proof.
  intro c. simpl. rewrite <- (q c). reflexivity.
Qed.


(*
Instance QuotesTo_Lam1 {ctx A B} `{OType A} `{OType B} `{ValidCtx ctx}
         (f: CtxElem ctx -> A -> B) prp e
         (q: QuotesTo (fun c => f (celem_rest _ _ c) (celem_head _ _ c)) e) :
  QuotesTo (fun c => {| pfun_app := f c; pfun_Proper := prp c |}) (Lam e) | 1.
Proof.
  intros c; split; intros a1 a2 Ra; simpl.
  - rewrite <- (q (c, a2)). rewrite Ra. reflexivity.
  - rewrite <- (q (c, a1)). rewrite <- Ra. reflexivity.
Qed.

Instance QuotesTo_Lam2 {ctx A B} `{OType A} `{OType B} `{ValidCtx ctx}
         (f: CtxElem ctx -> A -> B) prp e
         (q: QuotesTo (fun c => f (celem_rest _ _ c) (celem_head _ _ c)) e) :
  QuotesTo (fun c => ofun (f c) (prp:=prp c)) (Lam e)| 1.
Proof.
  unfold ofun. apply QuotesTo_Lam1. assumption.
Qed.
*)


Lemma oquote_R {A} {RA:OTRelation A} {f1 f2 : A} {e1 e2: OExpr CtxNil A}
      {q1: QuotesTo (fun _ => f1) e1} {q2: QuotesTo (fun _ => f2) e2} :
  e1 <e= e2 -> f1 <o= f2.
Proof.
  intro R12. assert (OType A) as OT; [ eauto with typeclass_instances | ].
  rewrite (q1 tt). rewrite (q2 tt). apply R12. reflexivity.
Defined.

Lemma oquote_eq {A} {RA:OTRelation A} {f1 f2 : A} {e1 e2: OExpr CtxNil A}
      {q1: QuotesTo (fun _ => f1) e1} {q2: QuotesTo (fun _ => f2) e2} :
  e1 =e= e2 -> f1 =o= f2.
Proof.
  intros eq12; destruct eq12; split; apply oquote_R; assumption.
Defined.

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
Ltac osimpl := simpl; oquote; try oexpr_simpl; try reflexivity; simpl.

Lemma product_proj1_test A `{OType A} B `{OType B} (a:A) (b:B) :
  ofst @o@ (a ,o, b) =o= a.
  osimpl.
Qed.


(***
 *** Old Version of Quoting Tactic, using Ltac Directly
 ***)

(*
Tactic Notation "unify'" open_constr(t) open_constr(u) :=
  assert(t = u); [refine eq_refl|].
*)

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
  simpl. osimpl.
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
  simpl. oquote. oexpr_simpl. reflexivity.
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
  simpl. oquote. oexpr_simpl. reflexivity.
Qed.

End OQuoteTest.
