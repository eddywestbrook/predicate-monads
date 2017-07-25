Require Export PredMonad.TypeReflection.OrderedType.
Require Export PredMonad.TypeReflection.OTypeExpr.


(***
 *** Helper Tactics
 ***)

(* FIXME: move these somewhere sensible! *)
Ltac destruct_ands :=
  repeat (lazymatch goal with | H:_ /\ _ |- _ => destruct H | _ => idtac end).
Ltac split_ands :=
  repeat (lazymatch goal with | |- _ /\ _ => split | _ => idtac end).


(***
 *** Ordered Expressions
 ***)

Inductive OVar A : Ctx -> Type :=
| OVar_0 {ctx:Ctx} : OVar A (CtxCons A ctx)
| OVar_S {ctx:Ctx} {B} : OVar A ctx -> OVar A (CtxCons B ctx)
.

Arguments OVar_0 {A ctx}.
Arguments OVar_S {A ctx B} v.

(* Expressions to represent proper functions *)
Inductive OExpr (ctx:Ctx) : OTypeExpr -> Type :=
| Var {A} (v:OVar A ctx) : OExpr ctx A
| Embed {A:OTypeExpr} (a:A) : OExpr ctx A
| App {A B} (e1 : OExpr ctx (OTpArrow A B)) (e2 : OExpr ctx A) : OExpr ctx B
| Lam {A B} (e: OExpr (CtxCons A ctx) B) : OExpr ctx (OTpArrow A B)
.

Arguments Var {ctx A} v.
Arguments Embed {ctx A} a.
Arguments App {ctx A B} e1 e2.
Arguments Lam {ctx A B} e.


(***
 *** Semantics of Ordered Expressions
 ***)

(* The semantics of a variable *)
Fixpoint varSemantics {A ctx} (v:OVar A ctx) :
  CtxElem ctx -o> A :=
  match v in OVar _ ctx return CtxElem ctx -o> A with
  | OVar_0 => ctx_head_pfun
  | OVar_S v' => compose_pfun ctx_tail_pfun (varSemantics v')
  end.
Arguments varSemantics {A ctx} !v.

(* The semantics of an ordered expression *)
Fixpoint exprSemantics {ctx A} (e:OExpr ctx A) : CtxElem ctx -o> A :=
  match e in OExpr _ A return CtxElem ctx -o> A with
  | Var v => varSemantics v
  | Embed a => const_pfun a
  | App e1 e2 => pfun_apply (exprSemantics e1) (exprSemantics e2)
  | Lam e => pfun_curry (exprSemantics e)
  end.
Arguments exprSemantics {ctx A} !e.


(***
 *** Relating Ordered Expressions
 ***)

(* Two expressions are related iff their semantics are *)
Definition oexpr_R {ctx A} (e1 e2:OExpr ctx A) : Prop :=
  exprSemantics e1 <o= exprSemantics e2.
Arguments oexpr_R {ctx A} e1 e2 : simpl never.

(* oexpr_R is a PreOrder *)
Instance PreOrder_oexpr_R ctx A : PreOrder (@oexpr_R ctx A).
Proof.
  unfold oexpr_R; split; intro; intros.
  - reflexivity.
  - etransitivity; [ apply H | apply H0 ].
Qed.

(* Two expressions are equivalenct iff their semantics are *)
Definition oexpr_eq {ctx A} (e1 e2:OExpr ctx A) : Prop :=
  exprSemantics e1 =o= exprSemantics e2.
Arguments oexpr_eq {ctx A} e1 e2 : simpl never.

(* oexpr_eq is a Equivalence *)
Instance Equivalence_oexpr_eq ctx A : Equivalence (@oexpr_eq ctx A).
Proof.
  unfold oexpr_eq; split; intro; intros.
  - reflexivity.
  - symmetry; assumption.
  - etransitivity; [ apply H | apply H0 ].
Qed.

Notation "x <e= y" :=
  (oexpr_R x y) (no associativity, at level 70).
Notation "x =e= y" :=
  (oexpr_eq x y) (no associativity, at level 70).


(* The Embed constructor is Proper w.r.t. ot_R and oexpr_R *)
Instance Proper_Embed ctx A :
  Proper (ot_R ==> oexpr_R) (@Embed ctx A).
Proof.
  intros a1 a2 Ra; unfold oexpr_R; simpl.
  apply Proper_const_pfun. assumption.
Qed.

(* The Embed constructor is Proper w.r.t. ot_equiv and oexpr_eq *)
Instance Proper_Embed_equiv ctx A :
  Proper (ot_equiv ==> oexpr_eq) (@Embed ctx A).
Proof.
  intros a1 a2 Ra. destruct Ra; split; apply Proper_Embed; assumption.
Qed.

(* The App constructor is Proper *)
Instance Proper_App ctx A B :
  Proper (oexpr_R ==> oexpr_R ==> oexpr_R) (@App ctx A B).
Proof.
  intros f1 f2 Rf a1 a2 Ra. unfold oexpr_R; simpl.
  apply Proper_pfun_apply; assumption.
Qed.

(* The App constructor is Proper for equivalence *)
Instance Proper_App_equiv ctx A B :
  Proper (oexpr_eq ==> oexpr_eq ==> oexpr_eq) (@App ctx A B).
Proof.
  intros f1 f2 Rf a1 a2 Ra. unfold oexpr_eq; simpl.
  apply Proper_pfun_apply_equiv; assumption.
Qed.

(* The Lam constructor is Proper *)
Instance Proper_Lam ctx {A B} :
  Proper (oexpr_R ==> oexpr_R) (@Lam ctx A B).
Proof.
  intros e1 e2 Re. unfold oexpr_R; simpl.
  apply Proper_pfun_curry. assumption.
Qed.

(* The Lam constructor is Proper for equivalence *)
Instance Proper_Lam_equiv ctx {A B} :
  Proper (oexpr_eq ==> oexpr_eq) (@Lam ctx A B).
Proof.
  intros e1 e2 Re. unfold oexpr_eq; simpl.
  apply Proper_pfun_curry_equiv. assumption.
Qed.


(***
 *** Weakening for Ordered Expressions
 ***)

(* Weakening / lifting of ordered expression variables *)
Fixpoint weakenOVar w tpW :
  forall {ctx A}, OVar A ctx -> OVar A (ctxInsert w tpW ctx) :=
  match w return forall ctx A, OVar A ctx -> OVar A (ctxInsert w tpW ctx) with
  | 0 => fun _ _ v => OVar_S v
  | S w' =>
    fun ctx A v =>
      match v in OVar _ ctx return OVar A (ctxInsert (S w') tpW ctx) with
      | OVar_0 => OVar_0
      | OVar_S v' => OVar_S (weakenOVar w' tpW v')
      end
  end.

(* Correctness of weakenOVar: it is equivalent to weaken_pfun *)
Lemma weakenOVar_correct w tpW {ctx A} (v:OVar A ctx) :
  varSemantics (weakenOVar w tpW v) =o=
  compose_pfun (weaken_pfun w tpW ctx) (varSemantics v).
Proof.
  revert ctx v; induction w; intros; [ | destruct v ]; simpl.
  - reflexivity.
  - rewrite compose_pair_snd. reflexivity.
  - rewrite compose_compose_pfun. rewrite compose_pair_fst.
    rewrite <- compose_compose_pfun. f_equiv. apply IHw.
Qed.

(* Weakening / lifting of ordered expressions *)
Fixpoint weakenOExpr w tpW {ctx A} (e:OExpr ctx A)
  : OExpr (ctxInsert w tpW ctx) A :=
  match e in OExpr _ A return OExpr (ctxInsert w tpW ctx) A with
  | Var v => Var (weakenOVar w tpW v)
  | Embed a => Embed a
  | App e1 e2 => App (weakenOExpr w tpW e1) (weakenOExpr w tpW e2)
  | Lam e => Lam (weakenOExpr (S w) tpW e)
  end.

(* Correctness of weakenOExpr: it is equivalent to weaken_pfun *)
Lemma weakenOExpr_correct w tpW {ctx A} (e:OExpr ctx A) :
  exprSemantics (weakenOExpr w tpW e) =o=
  compose_pfun (weaken_pfun w tpW ctx) (exprSemantics e).
  revert w; induction e; intros; simpl.
  - apply weakenOVar_correct.
  - rewrite compose_f_const_pfun; try typeclasses eauto. reflexivity.
  - rewrite compose_pfun_apply; try typeclasses eauto.
    rewrite IHe1. rewrite IHe2. reflexivity.
  - rewrite compose_pfun_curry; try typeclasses eauto.
    f_equiv. apply (IHe (S w)).
    Unshelve. typeclasses eauto.
Qed.

(* Proper-ness of weakenOExpr *)
Instance Proper_weakenOExpr w tpW {ctx A} :
  Proper (oexpr_R ==> oexpr_R) (@weakenOExpr w tpW ctx A).
Proof.
  intros e1 e2 Re. unfold oexpr_R.
  etransitivity; [ apply weakenOExpr_correct | ].
  etransitivity; [ | apply weakenOExpr_correct ].
  f_equiv. assumption.
Qed.

(* Proper-ness of weakenOExpr *)
Instance Proper_weakenOExpr_equiv w tpW {ctx A} :
  Proper (oexpr_eq ==> oexpr_eq) (@weakenOExpr w tpW ctx A).
Proof.
  intros e1 e2 Re. unfold oexpr_eq.
  etransitivity; [ apply weakenOExpr_correct | ].
  etransitivity; [ | symmetry; apply weakenOExpr_correct ].
  f_equiv. assumption.
Qed.


(***
 *** Substitution for Ordered Variables
 ***)

(* Substitution for ordered expression variables *)
Fixpoint substOVar n {ctx A} :
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
      | OVar_0 => fun _ => Var OVar_0
      | @OVar_S _ ctx' B v' =>
        fun s => weakenOExpr 0 B (substOVar n' v' s)
      end
  end.
Arguments substOVar !n {ctx A} !v s.

(* Correctness of substOVar: it is equivalent to subst_pfun *)
Lemma substOVar_correct n {ctx A} (v:OVar A ctx) s :
  exprSemantics (substOVar n v s) =o=
  compose_pfun (subst_pfun ctx n (exprSemantics s)) (varSemantics v).
Proof.
  revert n s; induction v; intros; destruct n; simpl.
  - symmetry; apply compose_pair_snd.
  - symmetry; apply compose_pair_snd.
  - rewrite compose_compose_pfun. rewrite compose_pair_fst.
    rewrite id_compose_pfun. reflexivity.
  - etransitivity; [ apply (weakenOExpr_correct 0) | ].
    rewrite compose_compose_pfun. rewrite compose_pair_fst.
    rewrite <- compose_compose_pfun. f_equiv. apply IHv.
Qed.

(* substOVar is Proper in its s argument *)
Instance Proper_substOVar n {ctx A} v :
  Proper (oexpr_R ==> oexpr_R) (@substOVar n ctx A v).
Proof.
  revert ctx v; induction n; intros; destruct v; intros e1 e2 Re; simpl.
  - assumption.
  - reflexivity.
  - reflexivity.
  - apply (Proper_weakenOExpr 0). apply IHn. assumption.
Qed.

(* substOVar is Proper in its s argument *)
Instance Proper_substOVar_equiv n {ctx A} v :
  Proper (oexpr_eq ==> oexpr_eq) (@substOVar n ctx A v).
Proof.
  intros e1 e2 Re; destruct Re; split; apply Proper_substOVar; assumption.
Qed.


(***
 *** Substitution for Ordered Expressions
 ***)

(* Substitution for ordered expressions *)
Fixpoint substOExpr n {ctx A} (e:OExpr ctx A) :
  OExpr (ctxSuffix n ctx) (ctxNth n ctx) -> OExpr (ctxDelete n ctx) A :=
  match e with
  | Var v => fun s => substOVar n v s
  | Embed a => fun _ => Embed a
  | App e1 e2 => fun s => App (substOExpr n e1 s) (substOExpr n e2 s)
  | Lam e => fun s => Lam (substOExpr (S n) e s)
  end.
Arguments substOExpr n {ctx A} !e.

(* Correctness of substOExpr: it is equivalent to subst_pfun *)
Lemma substOExpr_correct n {ctx A} (e:OExpr ctx A) s :
  exprSemantics (substOExpr n e s) =o=
  compose_pfun (subst_pfun ctx n (exprSemantics s)) (exprSemantics e).
Proof.
  revert n s; induction e; intros; simpl.
  - apply substOVar_correct.
  - symmetry. apply compose_f_const_pfun. typeclasses eauto.
  - etransitivity; [ | symmetry; apply compose_pfun_apply ];
      try typeclasses eauto.
    apply Proper_pfun_apply_equiv; [ apply IHe1 | apply IHe2 ].
  - etransitivity; [ | symmetry; apply compose_pfun_curry ];
      try typeclasses eauto.
    f_equiv.
    apply (IHe (S n)).
Qed.


(* The Beta rule for ordered expressions *)
Lemma OExpr_Beta ctx A B (e1: OExpr (CtxCons A ctx) B) (e2: OExpr ctx A) :
  App (Lam e1) e2 =e= substOExpr 0 e1 e2.
Proof.
  unfold oexpr_eq; simpl.
  rewrite (substOExpr_correct 0 e1 e2).
  rewrite pfun_apply_pfun_curry; try typeclasses eauto.
  f_equiv.
Qed.


FIXME HERE NOW: continue porting OExpr_typed.v!
