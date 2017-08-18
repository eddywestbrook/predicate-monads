Require Export PredMonad.TypeReflection.OrderedType.
Require Export PredMonad.TypeReflection.OTypeExpr.

Import EqNotations.


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

Inductive OVar {A RA} (tpA:@OTypeExpr A RA) : Ctx -> Type :=
| OVar_0 {ctx} : OVar tpA (@CtxCons A RA tpA ctx)
| OVar_S {B RB tpB ctx} : OVar tpA ctx -> OVar tpA (@CtxCons B RB tpB ctx)
.

Arguments OVar_0 {A RA tpA ctx}.
Arguments OVar_S {A RA tpA B RB tpB ctx} v.

(* Expressions to represent proper functions *)
Inductive OExpr ctx : forall {A RA}, @OTypeExpr A RA -> Type :=
| Var {A RA tp} (v:OVar tp ctx) : @OExpr ctx A RA tp
| Embed {A RA tp} (a:A) : @OExpr ctx A RA tp
| App {A RA} {tpA:@OTypeExpr A RA} {B RB} {tpB:@OTypeExpr B RB}
      (e1 : OExpr ctx (OTpArrow tpA tpB)) (e2 : OExpr ctx tpA) :
    OExpr ctx tpB
| Lam {A RA} {tpA:@OTypeExpr A RA} {B RB} {tpB:@OTypeExpr B RB}
      (e: OExpr (CtxCons tpA ctx) tpB) :
    OExpr ctx (OTpArrow tpA tpB)
.

Arguments Var {ctx A RA tp} v.
Arguments Embed {ctx A RA tp} a.
Arguments App {ctx A RA tpA B RB tpB} e1 e2.
Arguments Lam {ctx A RA tpA B RB tpB} e.


(***
 *** Semantics of Ordered Expressions
 ***)

(* The semantics of a variable *)
Fixpoint varSemantics {A RA tp ctx} (v:@OVar A RA tp ctx) :
  CtxElem ctx -o> A :=
  match v in OVar _ ctx return CtxElem ctx -o> A with
  | OVar_0 => ctx_head_pfun
  | OVar_S v' => compose_pfun ctx_tail_pfun (varSemantics v')
  end.
Arguments varSemantics {A RA tp ctx} !v.

(* The semantics of an ordered expression *)
Fixpoint exprSemantics {ctx A RA tp} (e:@OExpr ctx A RA tp) : CtxElem ctx -o> A :=
  match e in @OExpr _ A RA tp return CtxElem ctx -o> A with
  | Var v => varSemantics v
  | Embed a => const_pfun a
  | App e1 e2 => pfun_apply (exprSemantics e1) (exprSemantics e2)
  | Lam e => pfun_curry (exprSemantics e)
  end.
Arguments exprSemantics {ctx A RA tp} !e.


(***
 *** Relating Ordered Expressions
 ***)

(* Two expressions are related iff their semantics are *)
Definition oexpr_R {ctx A RA tp} (e1 e2:@OExpr ctx A RA tp) : Prop :=
  exprSemantics e1 <o= exprSemantics e2.
Arguments oexpr_R {ctx A RA tp} e1 e2 : simpl never.

(* oexpr_R is a PreOrder *)
Instance PreOrder_oexpr_R ctx A RA tp : PreOrder (@oexpr_R ctx A RA tp).
Proof.
  unfold oexpr_R; split; intro; intros.
  - reflexivity.
  - etransitivity; [ apply H | apply H0 ].
Qed.

(* Two expressions are equivalenct iff their semantics are *)
Definition oexpr_eq {ctx A RA tp} (e1 e2:@OExpr ctx A RA tp) : Prop :=
  exprSemantics e1 =o= exprSemantics e2.
Arguments oexpr_eq {ctx A RA tp} e1 e2 : simpl never.

(* oexpr_eq is a Equivalence *)
Instance Equivalence_oexpr_eq ctx A RA tp : Equivalence (@oexpr_eq ctx A RA tp).
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
Instance Proper_Embed ctx A RA tp :
  Proper (ot_R ==> oexpr_R) (@Embed ctx A RA tp).
Proof.
  intros a1 a2 Ra; unfold oexpr_R; simpl.
  apply Proper_const_pfun. assumption.
Qed.

(* The Embed constructor is Proper w.r.t. ot_equiv and oexpr_eq *)
Instance Proper_Embed_equiv ctx A RA tp :
  Proper (ot_equiv ==> oexpr_eq) (@Embed ctx A RA tp).
Proof.
  intros a1 a2 Ra. destruct Ra; split; apply Proper_Embed; assumption.
Qed.

(* The App constructor is Proper *)
Instance Proper_App ctx A RA tpA B RB tpB :
  Proper (oexpr_R ==> oexpr_R ==> oexpr_R) (@App ctx A RA tpA B RB tpB).
Proof.
  intros f1 f2 Rf a1 a2 Ra. unfold oexpr_R; simpl.
  apply Proper_pfun_apply; assumption.
Qed.

(* The App constructor is Proper for equivalence *)
Instance Proper_App_equiv ctx A RA tpA B RB tpB :
  Proper (oexpr_eq ==> oexpr_eq ==> oexpr_eq) (@App ctx A RA tpA B RB tpB).
Proof.
  intros f1 f2 Rf a1 a2 Ra. unfold oexpr_eq; simpl.
  apply Proper_pfun_apply_equiv; assumption.
Qed.

(* The Lam constructor is Proper *)
Instance Proper_Lam ctx A RA tpA B RB tpB :
  Proper (oexpr_R ==> oexpr_R) (@Lam ctx A RA tpA B RB tpB).
Proof.
  intros e1 e2 Re. unfold oexpr_R; simpl.
  apply Proper_pfun_curry. assumption.
Qed.

(* The Lam constructor is Proper for equivalence *)
Instance Proper_Lam_equiv ctx A RA tpA B RB tpB :
  Proper (oexpr_eq ==> oexpr_eq) (@Lam ctx A RA tpA B RB tpB).
Proof.
  intros e1 e2 Re. unfold oexpr_eq; simpl.
  apply Proper_pfun_curry_equiv. assumption.
Qed.


(***
 *** Weakening for Ordered Expressions
 ***)

(* Weakening / lifting of ordered expression variables *)
Fixpoint weakenOVar w {W RW} (tpW:@OTypeExpr W RW) :
  forall {ctx A RA tpA}, @OVar A RA tpA ctx -> OVar tpA (ctxInsert w tpW ctx) :=
  match w return forall ctx A RA tpA,
      OVar tpA ctx -> OVar tpA (ctxInsert w tpW ctx) with
  | 0 => fun _ _ _ _ v => OVar_S v
  | S w' =>
    fun ctx A RA tpA v =>
      match v in OVar _ ctx return OVar tpA (ctxInsert (S w') tpW ctx) with
      | OVar_0 => OVar_0
      | OVar_S v' => OVar_S (weakenOVar w' tpW v')
      end
  end.
Arguments weakenOVar w {W RW} tpW {ctx A RA tpA} v : simpl nomatch.

(* Correctness of weakenOVar: it is equivalent to weaken_pfun *)
Lemma weakenOVar_correct w {W RW} tpW {ctx A RA tpA} (v:@OVar A RA tpA ctx) :
  varSemantics (@weakenOVar w W RW tpW ctx A RA tpA v) =o=
  compose_pfun (weaken_pfun w tpW ctx) (varSemantics v).
Proof.
  revert ctx v; induction w; intros; [ | destruct v ]; simpl.
  - reflexivity.
  - rewrite compose_pair_snd. reflexivity.
  - rewrite compose_compose_pfun. rewrite compose_pair_fst.
    rewrite <- compose_compose_pfun. f_equiv. apply IHw.
Qed.

(* Weakening / lifting of ordered expressions *)
Fixpoint weakenOExpr w {W RW} (tpW:@OTypeExpr W RW) {ctx A RA tpA}
         (e:@OExpr ctx A RA tpA) : OExpr (ctxInsert w tpW ctx) tpA :=
  match e in OExpr _ A return OExpr (ctxInsert w tpW ctx) A with
  | Var v => Var (weakenOVar w tpW v)
  | Embed a => Embed a
  | App e1 e2 => App (weakenOExpr w tpW e1) (weakenOExpr w tpW e2)
  | Lam e => Lam (weakenOExpr (S w) tpW e)
  end.

(* Correctness of weakenOExpr: it is equivalent to weaken_pfun *)
Lemma weakenOExpr_correct w {W RW} tpW {ctx A RA tpA} (e:@OExpr ctx A RA tpA) :
  exprSemantics (@weakenOExpr w W RW tpW ctx A RA tpA e) =o=
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
Instance Proper_weakenOExpr w W RW tpW ctx A RA tpA :
  Proper (oexpr_R ==> oexpr_R) (@weakenOExpr w W RW tpW ctx A RA tpA).
Proof.
  intros e1 e2 Re. unfold oexpr_R.
  etransitivity; [ apply weakenOExpr_correct | ].
  etransitivity; [ | apply weakenOExpr_correct ].
  f_equiv. assumption.
Qed.

(* Proper-ness of weakenOExpr *)
Instance Proper_weakenOExpr_equiv w W RW tpW ctx A RA tpA :
  Proper (oexpr_eq ==> oexpr_eq) (@weakenOExpr w W RW tpW ctx A RA tpA).
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
Fixpoint substOVar n {ctx A RA tp} :
  @OVar A RA tp ctx -> OExpr (ctxSuffix n ctx) (ctxNthExpr n ctx) ->
  OExpr (ctxDelete n ctx) tp :=
  match n return
        OVar tp ctx -> OExpr (ctxSuffix n ctx) (ctxNthExpr n ctx) ->
        OExpr (ctxDelete n ctx) tp
  with
  | 0 =>
    fun v =>
      match v in OVar _ ctx return
            OExpr (ctxSuffix 0 ctx) (ctxNthExpr 0 ctx) ->
            OExpr (ctxDelete 0 ctx) tp
      with
      | OVar_0 => fun s => s
      | OVar_S v' => fun _ => Var v'
    end
  | S n' =>
    fun v =>
      match v in OVar _ ctx return
            OExpr (ctxSuffix (S n') ctx) (ctxNthExpr (S n') ctx) ->
            OExpr (ctxDelete (S n') ctx) tp
      with
      | OVar_0 => fun _ => Var OVar_0
      | @OVar_S _ _ _ B RB tpB ctx' v' =>
        fun s => weakenOExpr 0 tpB (substOVar n' v' s)
      end
  end.
Arguments substOVar !n {ctx A RA tp} !v s.

(* Correctness of substOVar: it is equivalent to subst_pfun *)
Lemma substOVar_correct n {ctx A RA tp} (v:@OVar A RA tp ctx) s :
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
Instance Proper_substOVar n {ctx A RA tp} v :
  Proper (oexpr_R ==> oexpr_R) (@substOVar n ctx A RA tp v).
Proof.
  revert ctx v; induction n; intros; destruct v; intros e1 e2 Re; simpl.
  - assumption.
  - reflexivity.
  - reflexivity.
  - apply (Proper_weakenOExpr 0). apply IHn. assumption.
Qed.

(* substOVar is Proper in its s argument *)
Instance Proper_substOVar_equiv n {ctx A RA tp} v :
  Proper (oexpr_eq ==> oexpr_eq) (@substOVar n ctx A RA tp v).
Proof.
  intros e1 e2 Re; destruct Re; split; apply Proper_substOVar; assumption.
Qed.


(***
 *** Substitution for Ordered Expressions
 ***)

(* Substitution for ordered expressions *)
Fixpoint substOExpr n {ctx A RA tp} (e:@OExpr ctx A RA tp) :
  OExpr (ctxSuffix n ctx) (ctxNthExpr n ctx) -> OExpr (ctxDelete n ctx) tp :=
  match e with
  | Var v => fun s => substOVar n v s
  | Embed a => fun _ => Embed a
  | App e1 e2 => fun s => App (substOExpr n e1 s) (substOExpr n e2 s)
  | Lam e => fun s => Lam (substOExpr (S n) e s)
  end.
Arguments substOExpr n {ctx A RA tp} !e.

(* Correctness of substOExpr: it is equivalent to subst_pfun *)
Lemma substOExpr_correct n {ctx A RA tp} (e:@OExpr ctx A RA tp) s :
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


(***
 *** OExpr Rewrite Rules
 ***)

(* The Beta rule for ordered expressions *)
Lemma OExpr_Beta ctx A RA tpA B RB tpB
      (e1: @OExpr (@CtxCons A RA tpA ctx) B RB tpB) (e2: @OExpr ctx A RA tpA) :
  App (Lam e1) e2 =e= substOExpr 0 e1 e2.
Proof.
  unfold oexpr_eq; simpl.
  rewrite (substOExpr_correct 0 e1 e2).
  rewrite pfun_apply_pfun_curry; try typeclasses eauto.
  f_equiv.
Qed.

(*
(* The OExpr for the fst function *)
Definition OFst {ctx A RA B} {RB:OTRelation B} {tp} : @OExpr ctx (A*B -o> A) _ tp :=
  Embed (tp:=tp) (@ofst A B RA RB).

(* The OExpr for the snd function *)
Definition OSnd {ctx A B} : OExpr ctx (OTpArrow (OTpPair A B) B) :=
  Embed (A:=OTpArrow (OTpPair A B) B) osnd.

(* The OExpr for the pair function *)
Definition OPair {ctx A B} : OExpr ctx (OTpArrow A (OTpArrow B (OTpPair A B))) :=
  Embed (A:=OTpArrow A (OTpArrow B (OTpPair A B))) opair.

(* Mark the above OExpr constructs as opaque *)
Typeclasses Opaque OFst OSnd OPair.
*)

Lemma OExpr_fst_pair ctx A RA tpA B RB tpB
      (e1: @OExpr ctx A RA tpA) (e2: @OExpr ctx B RB tpB) :
  App (Embed ofst) (App (App (Embed opair) e1) e2) =e= e1.
Proof.
  split; intros a1 a2 Ra; simpl; f_equiv; assumption.
Qed.

Lemma OExpr_snd_pair ctx A RA tpA B RB tpB
      (e1: @OExpr ctx A RA tpA) (e2: @OExpr ctx B RB tpB) :
  App (Embed osnd) (App (App (Embed opair) e1) e2) =e= e2.
Proof.
  split; intros a1 a2 Ra; simpl; f_equiv; assumption.
Qed.

Lemma OExpr_pair_eta ctx A RA (tpA:@OTypeExpr A RA) B RB (tpB:@OTypeExpr B RB)
      (e: OExpr ctx (OTpPair tpA tpB)) :
  (App (App (Embed opair) (App (Embed ofst) e)) (App (Embed osnd) e)) =e= e.
Proof.
  split; intros a1 a2 Ra; split; simpl; f_equiv; f_equiv; assumption.
Qed.

Hint Rewrite OExpr_fst_pair OExpr_snd_pair OExpr_pair_eta : osimpl.


(***
 *** Quoting Tactic for Ordered Expressions
 ***)

(* Specially-marked versions of fst and snd just used for quoting OExprs *)
Definition celem_head {ctx A RA tpA}
           (celem: CtxElem (@CtxCons A RA tpA ctx)) : A :=
  let (_,head) := celem in head.
Definition celem_rest {ctx A RA tpA}
           (celem: CtxElem (@CtxCons A RA tpA ctx)) : CtxElem ctx :=
  let (rest,_) := celem in rest.

(* Typeclass for incrementally quoting functions into OExpr variables, by
peeling off the celem_rest projections one at a time and adding them as OVar_S
constructors to the input variable to build the output variable *)
Class QuotesToVar {ctx1 ctx2 A RA} {tpA:@OTypeExprInd A RA}
      (f: CtxElem ctx1 -> CtxElem ctx2)
      (vin: OVar tpA ctx2) (vout: OVar tpA ctx1) : Prop :=
  quotesToVar :
    forall c, varSemantics vin @o@ (f c) = varSemantics vout @o@ c.

Instance QuotesToVar_Base {ctx A RA} {tpA:@OTypeExprInd A RA}
         (v:@OVar A RA tpA ctx) : QuotesToVar (fun c => c) v v.
Proof.
  intro; reflexivity.
Qed.

Instance QuotesToVar_Step {ctx1 ctx2 A RA} {tpA:@OTypeExprInd A RA}
         {B RB} {tpB:@OTypeExprInd B RB}
         (f: CtxElem ctx1 -> CtxElem (@CtxCons B RB tpB ctx2)) vin vout
         (q: @QuotesToVar _ _ A RA tpA f (OVar_S vin) vout) :
  QuotesToVar (fun c => celem_rest (f c)) vin vout.
Proof.
  intro. apply q.
Qed.


(* Class for quoting functions to OExprs *)
Class QuotesTo {ctx A RA} {tpA:@OTypeExprInd A RA} (f: CtxElem ctx -> A)
      (e: @OExpr ctx A RA tpA) : Prop :=
  quotesTo : forall c, f c =o= exprSemantics e @o@ c.

(* Logically the same as QuotesTo, but we never build lambdas in this one, i.e.,
this only builds "atomic" OExprs *)
Class QuotesToAtomic {ctx A RA} {tpA:@OTypeExprInd A RA}
      (f: CtxElem ctx -> A) (e: @OExpr ctx A RA tpA) :=
  quotesToAtomic : QuotesTo f e.

(* Quote any term of functional type to a lambda *)
Instance QuotesTo_Lam {ctx A RA} {tpA:@OTypeExprInd A RA}
         {B RB} {tpB:@OTypeExprInd B RB} (f: CtxElem ctx -> A -o> B)
         (e: OExpr (CtxCons tpA ctx) tpB)
         (q: QuotesTo (fun c => f (celem_rest c) @o@ (celem_head c)) e) :
  QuotesTo f (Lam e) | 2.
Proof.
  intros; split; intro; intros; simpl; rewrite H;
    rewrite <- (q (c,a2)); reflexivity.
Qed.

(* Special case: quote ofuns as lambdas, destructuring the ofun *)
Instance QuotesTo_Lam_ofun {ctx A RA} {tpA:@OTypeExprInd A RA}
         {B RB} {tpB:@OTypeExprInd B RB} (f: CtxElem ctx -> A -> B) prp
         (e: OExpr (CtxCons tpA ctx) tpB)
         (q: QuotesTo (fun c => f (celem_rest c) (celem_head c)) e) :
  QuotesTo (fun c => ofun (f c) (prp:=prp c)) (Lam e) | 1.
Proof.
  apply QuotesTo_Lam. assumption.
Qed.


(* Quote any non-function term as an atomic OExpr *)
Instance QuotesTo_Atomic {ctx A RA} {tpA:@OTypeExprInd A RA}
         (f: CtxElem ctx -> A) e (q: QuotesToAtomic f e) :
  QuotesTo (tpA:=tpA) f e | 3 := q.

(* Quote any use of celem_head as a var *)
Instance QuotesTo_Var {ctx1 ctx2 A RA} {tpA:@OTypeExprInd A RA}
         (f: CtxElem ctx1 -> CtxElem (CtxCons tpA ctx2)) v
         (q: QuotesToVar f OVar_0 v) :
  QuotesToAtomic (fun c => celem_head (f c)) (Var v) | 1.
Proof.
  intro. rewrite <- (quotesToVar (QuotesToVar:=q)). destruct (f c).
  reflexivity.
Qed.

(* Special case for an eta-reduced celem_head application *)
Instance QuotesTo_Var0 {ctx A RA} {tpA:@OTypeExprInd A RA} :
  QuotesToAtomic (@celem_head ctx A RA tpA) (Var OVar_0) | 1.
Proof.
  intro; reflexivity.
Qed.

(* Quote applications as OExpr applications, where the function must still be
atomic but the argument need not be *)
Instance QuotesTo_App {ctx A RA} {tpA:@OTypeExprInd A RA} {B RB}
         {tpB:@OTypeExprInd B RB}
         (f1: CtxElem ctx -> A -o> B) (f2: CtxElem ctx -> A)
         (e1: OExpr ctx (OTpArrow tpA tpB)) (e2: OExpr ctx tpA)
         (q1: QuotesToAtomic f1 e1) (q2: QuotesTo f2 e2) :
  QuotesToAtomic (fun c => (f1 c) @o@ (f2 c)) (App e1 e2) | 1.
Proof.
  intro. simpl. f_equiv.
  - apply (quotesTo (QuotesTo:=q1)).
  - apply (quotesTo (QuotesTo:=q2)).
Qed.

(* Quote ofuns in atomic position as lambdas *)
Instance QuotesToAtomic_ofun {ctx A RA} {tpA:@OTypeExprInd A RA} {B RB}
         {tpB:@OTypeExprInd B RB} (f: CtxElem ctx -> A -> B) prp
         (e: OExpr (CtxCons tpA ctx) tpB)
         (q: QuotesTo (fun c => f (celem_rest c) (celem_head c)) e) :
  QuotesToAtomic (fun c => ofun (f c) (prp:=prp c)) (Lam e) | 1.
Proof.
  apply QuotesTo_Lam. assumption.
Qed.

(* Quote objects that are independent of the context as embedded objects, but at
low priority *)
Instance QuotesTo_Embed {ctx A RA} {tpA:@OTypeExprInd A RA} (a:A) :
  QuotesToAtomic (fun _ => a) (@Embed ctx A RA tpA a) | 2.
Proof.
  intro. reflexivity.
Qed.

(* Quote pairs as applications of opair *)
Instance QuotesTo_pair {ctx A RA} {tpA:@OTypeExprInd A RA} {B RB}
         {tpB:@OTypeExprInd B RB} (a: CtxElem ctx -> A) (b: CtxElem ctx -> B)
         (e1: OExpr ctx tpA) (e2: OExpr ctx tpB)
         (q1: QuotesTo a e1) (q2: QuotesTo b e2) :
  QuotesToAtomic (tpA:=OTpPair tpA tpB) (fun c => (a c, b c))
                 (App (App (Embed opair) e1) e2) | 1.
Proof.
  intro. simpl. rewrite (q1 c). rewrite (q2 c). reflexivity.
Qed.

(* Quote applications of fst as applications of ofst *)
Instance QuotesTo_fst {ctx A RA} {tpA:@OTypeExprInd A RA} {B RB}
         {tpB:@OTypeExprInd B RB} (f: CtxElem ctx -> A * B)
         (e: OExpr ctx (OTpPair tpA tpB)) (q: QuotesTo f e) :
  QuotesToAtomic (tpA:=tpA) (fun c => fst (f c)) (App (Embed ofst) e) | 1.
Proof.
  intro. simpl. rewrite (q c). reflexivity.
Qed.

(* Quote applications of snd as applications of osnd *)
Instance QuotesTo_snd {ctx A RA} {tpA:@OTypeExprInd A RA} {B RB}
         {tpB:@OTypeExprInd B RB} (f: CtxElem ctx -> A * B)
         (e: OExpr ctx (OTpPair tpA tpB)) (q: QuotesTo f e) :
  QuotesToAtomic (tpA:=tpB) (fun c => snd (f c)) (App (Embed osnd) e) | 1.
Proof.
  intro. simpl. rewrite (q c). reflexivity.
Qed.


(* Use QuotesTo to prove a relation *)
Lemma oquote_R {A RA} {tpA:@OTypeExprInd A RA} {f1 f2 : A}
      {e1 e2: OExpr CtxNil tpA}
      {q1: QuotesTo (fun _ => f1) e1} {q2: QuotesTo (fun _ => f2) e2} :
  e1 <e= e2 -> f1 <o= f2.
Proof.
  intro R12.
  etransitivity; [ apply (q1 tt) | ].
  etransitivity; [ | apply (q2 tt) ].
  apply R12. reflexivity.
Qed.

(* Use QuotesTo to prove an equivalence *)
Lemma oquote_eq {A RA} {tpA:@OTypeExpr A RA} {f1 f2 : A}
      {e1 e2: OExpr CtxNil tpA}
      {q1: QuotesTo (tpA:=tpA) (fun _ => f1) e1} {q2: QuotesTo (fun _ => f2) e2} :
  e1 =e= e2 -> f1 =o= f2.
Proof.
  intro R12.
  etransitivity; [ apply (q1 tt) | ].
  etransitivity; [ | symmetry; apply (q2 tt) ].
  f_equiv. apply R12.
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
 *** Testing the Quote Mechanism
 ***)

Module OQuoteTest.

(* Set Printing All. *)
(* Hint Extern 4 (QuotesTo ) : typeclass_instances. *)

(*
Goal (forall A (RA:OTRelation A) (a:A),
         exists (tpA:OTypeExprInd A) (e:OExpr CtxNil tpA),
           QuotesTo (fun _ => a) e).
  intros. eexists. eexists.
  typeclasses eauto.
  simple apply @QuotesTo_Atomic.
 *)
(* Hint Extern 1 (OTypeExprInd _) => prove_OTypeExpr : typeclass_instances. *)
(* Typeclasses Opaque OTypeExprInd.
Print HintDb typeclass_instances. *)

Instance Equivalence_oexpr_eq' ctx A RA (tp:@OTypeExprInd A RA)
  : Equivalence (@oexpr_eq ctx A RA tp) := Equivalence_oexpr_eq _ _ _ _.

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
  oquote.

  FIXME HERE NOW: quoting for ofuns is not working!

  oexpr_simpl. reflexivity. typeclasses eauto.
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



FIXME HERE NOW: continue porting OExpr_typed.v!
