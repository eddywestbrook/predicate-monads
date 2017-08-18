Require Export PredMonad.Reflection2.OrderedType.
Require Export PredMonad.Reflection2.OrderedContext.


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

Inductive OVar A {RA} : Ctx -> Type :=
| OVar_0 {ctx} : OVar A (@CtxCons A RA ctx)
| OVar_S {B RB ctx} : OVar A ctx -> OVar A (@CtxCons B RB ctx)
.

Arguments OVar_0 {A RA ctx}.
Arguments OVar_S {A RA B RB ctx} v.

(* Expressions to represent proper functions *)
Inductive OExpr ctx : forall A {RA:OType A}, Type :=
| Var {A RA} (v:OVar A ctx) : @OExpr ctx A RA
| Embed {A RA} (a:A) : @OExpr ctx A RA
| App {A RA B RB} (e1 : OExpr ctx (A -o> B)) (e2 : @OExpr ctx A RA) :
    @OExpr ctx B RB
| Lam {A RA B RB} (e: @OExpr (@CtxCons A RA ctx) B RB) :
    OExpr ctx (A -o> B)
.

Arguments Var {ctx A RA} v.
Arguments Embed {ctx A RA} a.
Arguments App {ctx A RA B RB} e1 e2.
Arguments Lam {ctx A RA B RB} e.


(***
 *** Helpers for Building OExprs
 ***)

Notation "e1 @e@ e2" :=
  (App e1 e2) (left associativity, at level 20).

(* Apply a context extension to an OVar *)
Fixpoint extendVar {ctx1 ctx2} {ext:ContextExtends ctx1 ctx2} :
  forall {A} {RA:OType A}, OVar A ctx1 -> OVar A ctx2 :=
  match ext in ContextExtendsInd _ ctx2 return
        forall A (RA:OType A), OVar A ctx1 -> OVar A ctx2
  with
  | CtxExtNil _ => fun _ _ v => v
  | CtxExtCons _ _ _ ext' =>
    fun _ _ v => OVar_S (extendVar (ext:=ext') v)
  end.

Definition mkLam {ctx A RA B RB}
           (body: (forall ctx2,
                      ContextExtends (CtxCons A ctx) ctx2 -> @OExpr ctx2 A RA) ->
                  OExpr (CtxCons A ctx) B) :
  OExpr ctx (A -o> B) :=
  @Lam ctx A RA B RB (body (fun _ ext => Var (extendVar (ext:=ext) OVar_0))).

Notation "'efun' x => e" :=
  (mkLam (fun (x : forall {ctx2 ext}, OExpr _ _) => e))
    (right associativity, at level 99).


(***
 *** Semantics of Ordered Expressions
 ***)

(* The semantics of a variable *)
Fixpoint varSemantics {A RA ctx} (v:@OVar A RA ctx) :
  CtxElem ctx -o> A :=
  match v in OVar _ ctx return CtxElem ctx -o> A with
  | OVar_0 => ctx_head_pfun
  | OVar_S v' => compose_pfun ctx_tail_pfun (varSemantics v')
  end.
Arguments varSemantics {A RA ctx} !v.

(* The semantics of an ordered expression *)
Fixpoint exprSemantics {ctx A RA} (e:@OExpr ctx A RA) : CtxElem ctx -o> A :=
  match e in @OExpr _ A RA return CtxElem ctx -o> A with
  | Var v => varSemantics v
  | Embed a => const_pfun a
  | App e1 e2 => pfun_apply (exprSemantics e1) (exprSemantics e2)
  | Lam e => pfun_curry (exprSemantics e)
  end.
Arguments exprSemantics {ctx A RA} !e.


(***
 *** Relating Ordered Expressions
 ***)

(* Two expressions are related iff their semantics are *)
Definition oexpr_R {ctx A RA} (e1 e2:@OExpr ctx A RA) : Prop :=
  exprSemantics e1 <o= exprSemantics e2.
Arguments oexpr_R {ctx A RA} e1 e2 : simpl never.

(* oexpr_R is a PreOrder *)
Instance PreOrder_oexpr_R ctx A RA : PreOrder (@oexpr_R ctx A RA).
Proof.
  unfold oexpr_R; split; intro; intros.
  - reflexivity.
  - etransitivity; [ apply H | apply H0 ].
Qed.

(* Two expressions are equivalenct iff their semantics are *)
Definition oexpr_eq {ctx A RA} (e1 e2:@OExpr ctx A RA) : Prop :=
  exprSemantics e1 =o= exprSemantics e2.
Arguments oexpr_eq {ctx A RA} e1 e2 : simpl never.

(* oexpr_eq is a Equivalence *)
Instance Equivalence_oexpr_eq ctx A RA : Equivalence (@oexpr_eq ctx A RA).
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
Instance Proper_Embed ctx A RA :
  Proper (ot_R ==> oexpr_R) (@Embed ctx A RA).
Proof.
  intros a1 a2 Ra; unfold oexpr_R; simpl.
  apply Proper_const_pfun. assumption.
Qed.

(* The Embed constructor is Proper w.r.t. ot_equiv and oexpr_eq *)
Instance Proper_Embed_equiv ctx A RA :
  Proper (ot_equiv ==> oexpr_eq) (@Embed ctx A RA).
Proof.
  intros a1 a2 Ra. destruct Ra; split; apply Proper_Embed; assumption.
Qed.

(* The App constructor is Proper *)
Instance Proper_App ctx A RA B RB :
  Proper (oexpr_R ==> oexpr_R ==> oexpr_R) (@App ctx A RA B RB).
Proof.
  intros f1 f2 Rf a1 a2 Ra. unfold oexpr_R; simpl.
  apply Proper_pfun_apply; assumption.
Qed.

(* The App constructor is Proper for equivalence *)
Instance Proper_App_equiv ctx A RA B RB :
  Proper (oexpr_eq ==> oexpr_eq ==> oexpr_eq) (@App ctx A RA B RB).
Proof.
  intros f1 f2 Rf a1 a2 Ra. unfold oexpr_eq; simpl.
  apply Proper_pfun_apply_equiv; assumption.
Qed.

(* The Lam constructor is Proper *)
Instance Proper_Lam ctx A RA B RB :
  Proper (oexpr_R ==> oexpr_R) (@Lam ctx A RA B RB).
Proof.
  intros e1 e2 Re. unfold oexpr_R; simpl.
  apply Proper_pfun_curry. assumption.
Qed.

(* The Lam constructor is Proper for equivalence *)
Instance Proper_Lam_equiv ctx A RA B RB :
  Proper (oexpr_eq ==> oexpr_eq) (@Lam ctx A RA B RB).
Proof.
  intros e1 e2 Re. unfold oexpr_eq; simpl.
  apply Proper_pfun_curry_equiv. assumption.
Qed.


(***
 *** Weakening for Ordered Expressions
 ***)

(* Weakening / lifting of ordered expression variables *)
Fixpoint weakenOVar w W {RW} :
  forall {ctx A RA}, @OVar A RA ctx -> OVar A (@ctxInsert w W RW ctx) :=
  match w return forall ctx A RA,
      OVar A ctx -> OVar A (ctxInsert w W ctx) with
  | 0 => fun _ _ _ v => OVar_S v
  | S w' =>
    fun ctx A RA v =>
      match v in OVar _ ctx return OVar A (ctxInsert (S w') W ctx) with
      | OVar_0 => OVar_0
      | OVar_S v' => OVar_S (weakenOVar w' W v')
      end
  end.
Arguments weakenOVar w W {RW ctx A RA} v : simpl nomatch.

(* Correctness of weakenOVar: it is equivalent to weaken_pfun *)
Lemma weakenOVar_correct w W {RW ctx A RA} (v:@OVar A RA ctx) :
  varSemantics (@weakenOVar w W RW ctx A RA v) =o=
  compose_pfun (weaken_pfun w W ctx) (varSemantics v).
Proof.
  revert ctx v; induction w; intros; [ | destruct v ]; simpl.
  - reflexivity.
  - rewrite compose_pair_snd. reflexivity.
  - rewrite compose_compose_pfun. rewrite compose_pair_fst.
    rewrite <- compose_compose_pfun. f_equiv. apply IHw.
Qed.

(* Weakening / lifting of ordered expressions *)
Fixpoint weakenOExpr w W {RW:OType W} {ctx A RA}
         (e:@OExpr ctx A RA) : OExpr (ctxInsert w W ctx) A :=
  match e in OExpr _ A return OExpr (ctxInsert w W ctx) A with
  | Var v => Var (weakenOVar w W v)
  | Embed a => Embed a
  | App e1 e2 => App (weakenOExpr w W e1) (weakenOExpr w W e2)
  | Lam e => Lam (weakenOExpr (S w) W e)
  end.

(* Correctness of weakenOExpr: it is equivalent to weaken_pfun *)
Lemma weakenOExpr_correct w W {RW ctx A RA} (e:@OExpr ctx A RA) :
  exprSemantics (@weakenOExpr w W RW ctx A RA e) =o=
  compose_pfun (weaken_pfun w W ctx) (exprSemantics e).
  revert w; induction e; intros; simpl.
  - apply weakenOVar_correct.
  - rewrite compose_f_const_pfun; try typeclasses eauto. reflexivity.
  - rewrite compose_pfun_apply; try typeclasses eauto.
    rewrite IHe1. rewrite IHe2. reflexivity.
  - rewrite compose_pfun_curry; try typeclasses eauto.
    f_equiv. apply (IHe (S w)).
Qed.

(* Proper-ness of weakenOExpr *)
Instance Proper_weakenOExpr w W RW ctx A RA :
  Proper (oexpr_R ==> oexpr_R) (@weakenOExpr w W RW ctx A RA).
Proof.
  intros e1 e2 Re. unfold oexpr_R.
  etransitivity; [ apply weakenOExpr_correct | ].
  etransitivity; [ | apply weakenOExpr_correct ].
  f_equiv. assumption.
Qed.

(* Proper-ness of weakenOExpr *)
Instance Proper_weakenOExpr_equiv w W RW ctx A RA :
  Proper (oexpr_eq ==> oexpr_eq) (@weakenOExpr w W RW ctx A RA).
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
Fixpoint substOVar n {ctx A RA} :
  @OVar A RA ctx -> @OExpr (ctxSuffix n ctx) (ctxNth ctx n) (ctxNthOType ctx n) ->
  OExpr (ctxDelete n ctx) A :=
  match n return
        OVar A ctx -> OExpr (ctxSuffix n ctx) (ctxNth ctx n) ->
        OExpr (ctxDelete n ctx) A
  with
  | 0 =>
    fun v =>
      match v in OVar _ ctx return
            OExpr (ctxSuffix 0 ctx) (ctxNth ctx 0) ->
            OExpr (ctxDelete 0 ctx) A
      with
      | OVar_0 => fun s => s
      | OVar_S v' => fun _ => Var v'
    end
  | S n' =>
    fun v =>
      match v in OVar _ ctx return
            OExpr (ctxSuffix (S n') ctx) (ctxNth ctx (S n')) ->
            OExpr (ctxDelete (S n') ctx) A
      with
      | OVar_0 => fun _ => Var OVar_0
      | @OVar_S _ _ B RB ctx' v' =>
        fun (s: @OExpr _ _ (ctxNthOType _ _)) =>
          weakenOExpr 0 B (substOVar n' (ctx:=ctx') v' s)
      end
  end.
Arguments substOVar !n {ctx A RA} !v s.

(* Correctness of substOVar: it is equivalent to subst_pfun *)
Lemma substOVar_correct n {ctx A RA} (v:@OVar A RA ctx) s :
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
Instance Proper_substOVar n {ctx A RA} v :
  Proper (oexpr_R ==> oexpr_R) (@substOVar n ctx A RA v).
Proof.
  revert ctx v; induction n; intros; destruct v; intros e1 e2 Re; simpl.
  - assumption.
  - reflexivity.
  - reflexivity.
  - apply (Proper_weakenOExpr 0). apply IHn. assumption.
Qed.

(* substOVar is Proper in its s argument *)
Instance Proper_substOVar_equiv n {ctx A RA} v :
  Proper (oexpr_eq ==> oexpr_eq) (@substOVar n ctx A RA v).
Proof.
  intros e1 e2 Re; destruct Re; split; apply Proper_substOVar; assumption.
Qed.


(***
 *** Substitution for Ordered Expressions
 ***)

(* Substitution for ordered expressions *)
Fixpoint substOExpr n {ctx A RA} (e:@OExpr ctx A RA) :
  OExpr (ctxSuffix n ctx) (ctxNth ctx n) -> OExpr (ctxDelete n ctx) A :=
  match e with
  | Var v => fun s => substOVar n v s
  | Embed a => fun _ => Embed a
  | App e1 e2 => fun s => App (substOExpr n e1 s) (substOExpr n e2 s)
  | Lam e => fun s => Lam (substOExpr (S n) e s)
  end.
Arguments substOExpr n {ctx A RA} !e.

(* Correctness of substOExpr: it is equivalent to subst_pfun *)
Lemma substOExpr_correct n {ctx A RA} (e:@OExpr ctx A RA) s :
  exprSemantics (substOExpr n e s) =o=
  compose_pfun (subst_pfun ctx n (exprSemantics s)) (exprSemantics e).
Proof.
  revert n s; induction e; intros; simpl.
  - apply substOVar_correct.
  - symmetry. apply compose_f_const_pfun.
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
Lemma OExpr_Beta ctx A RA B RB
      (e1: @OExpr (@CtxCons A RA ctx) B RB) (e2: @OExpr ctx A RA) :
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

Lemma OExpr_fst_pair ctx A RA B RB
      (e1: @OExpr ctx A RA) (e2: @OExpr ctx B RB) :
  App (Embed ofst) (App (App (Embed opair) e1) e2) =e= e1.
Proof.
  split; intros a1 a2 Ra; simpl; f_equiv; assumption.
Qed.

Lemma OExpr_snd_pair ctx A RA B RB
      (e1: @OExpr ctx A RA) (e2: @OExpr ctx B RB) :
  App (Embed osnd) (App (App (Embed opair) e1) e2) =e= e2.
Proof.
  split; intros a1 a2 Ra; simpl; f_equiv; assumption.
Qed.

Lemma OExpr_pair_eta ctx A (RA:OType A) B (RB:OType B) (e: OExpr ctx (A * B)) :
  (App (App (Embed opair) (App (Embed ofst) e)) (App (Embed osnd) e)) =e= e.
Proof.
  split; intros a1 a2 Ra; split; simpl; f_equiv; f_equiv; assumption.
Qed.

Hint Rewrite OExpr_fst_pair OExpr_snd_pair OExpr_pair_eta : osimpl.


(***
 *** Quoting Tactic for Ordered Expressions
 ***)

(* Specially-marked versions of fst and snd just used for quoting OExprs *)
Definition celem_head {ctx A RA}
           (celem: CtxElem (@CtxCons A RA ctx)) : A :=
  let (_,head) := celem in head.
Definition celem_rest {ctx A RA}
           (celem: CtxElem (@CtxCons A RA ctx)) : CtxElem ctx :=
  let (rest,_) := celem in rest.

Arguments celem_head {_ _ _} _ : simpl never.
Arguments celem_rest {_ _ _} _ : simpl never.

(* Typeclass for incrementally quoting functions into OExpr variables, by
peeling off the celem_rest projections one at a time and adding them as OVar_S
constructors to the input variable to build the output variable *)
Class QuotesToVar {ctx1 ctx2 A} {RA:OType A}
      (f: CtxElem ctx1 -> CtxElem ctx2)
      (vin: OVar A ctx2) (vout: OVar A ctx1) : Prop :=
  quotesToVar :
    forall c, varSemantics vin @o@ (f c) = varSemantics vout @o@ c.

Instance QuotesToVar_Base {ctx A RA}
         (v:@OVar A RA ctx) : QuotesToVar (fun c => c) v v.
Proof.
  intro; reflexivity.
Qed.

Instance QuotesToVar_Step {ctx1 ctx2 A} {RA:OType A} {B} {RB:OType B}
         (f: CtxElem ctx1 -> CtxElem (@CtxCons B RB ctx2)) vin vout
         (q: @QuotesToVar _ _ A RA f (OVar_S vin) vout) :
  QuotesToVar (fun c => celem_rest (f c)) vin vout.
Proof.
  intro. apply q.
Qed.


(* Class for quoting functions to OExprs *)
Class QuotesTo {ctx A RA} (f: CtxElem ctx -> A) (e: @OExpr ctx A RA) : Prop :=
  quotesTo : forall c, f c =o= exprSemantics e @o@ c.

(* Logically the same as QuotesTo, but we never build lambdas in this one, i.e.,
this only builds "atomic" OExprs *)
Class QuotesToAtomic {ctx A RA} (f: CtxElem ctx -> A) (e: @OExpr ctx A RA) :=
  quotesToAtomic : QuotesTo f e.

(* Quote any term of functional type to a lambda *)
Instance QuotesTo_Lam {ctx A RA B RB} (f: CtxElem ctx -> A -o> B)
         (e: @OExpr (@CtxCons A RA ctx) B RB)
         (q: QuotesTo (fun c => f (celem_rest c) @o@ (celem_head c)) e) :
  QuotesTo f (Lam e) | 2.
Proof.
  intros; split; intro; intros; simpl; rewrite H;
    rewrite <- (q (c,a2)); reflexivity.
Qed.

(* Special case: quote ofuns as lambdas, destructuring the ofun *)
Instance QuotesTo_Lam_ofun {ctx A RA B RB} (f: CtxElem ctx -> A -> B) prp
         (e: @OExpr (@CtxCons A RA ctx) B RB)
         (q: QuotesTo (fun c => f (celem_rest c) (celem_head c)) e) :
  QuotesTo (fun c => mk_ofun (f c) (prp:=prp c)) (Lam e) | 1.
Proof.
  apply QuotesTo_Lam. assumption.
Qed.


(* Quote any non-function term as an atomic OExpr *)
Instance QuotesTo_Atomic {ctx A} {RA:OType A} (f: CtxElem ctx -> A)
         e (q: QuotesToAtomic f e) :
  QuotesTo f e | 3 := q.

(* Quote any use of celem_head as a var *)
Instance QuotesTo_Var {ctx1 ctx2 A} {RA:OType A}
         (f: CtxElem ctx1 -> CtxElem (CtxCons A ctx2)) v
         (q: QuotesToVar f OVar_0 v) :
  QuotesToAtomic (fun c => celem_head (f c)) (Var v) | 1.
Proof.
  intro. rewrite <- q. destruct (f c).
  reflexivity.
Qed.

(* Special case for an eta-reduced celem_head application *)
Instance QuotesTo_Var0 {ctx A} {RA:OType A} :
  QuotesToAtomic (@celem_head ctx A RA) (Var OVar_0) | 1.
Proof.
  intro; reflexivity.
Qed.

(* Quote applications as OExpr applications, where the function must still be
atomic but the argument need not be *)
Instance QuotesTo_App {ctx A} {RA:OType A} {B} {RB:OType B}
         (f1: CtxElem ctx -> A -o> B) (f2: CtxElem ctx -> A)
         (e1: OExpr ctx (A -o> B)) (e2: OExpr ctx A)
         (q1: QuotesToAtomic f1 e1) (q2: QuotesTo f2 e2) :
  QuotesToAtomic (fun c => (f1 c) @o@ (f2 c)) (App e1 e2) | 1.
Proof.
  intro. simpl. f_equiv.
  - apply q1.
  - apply q2.
Qed.

(* Quote ofuns in atomic position as lambdas *)
Instance QuotesToAtomic_ofun {ctx A} {RA:OType A} {B} {RB:OType B}
         (f: CtxElem ctx -> A -> B) prp
         (e: OExpr (CtxCons A ctx) B)
         (q: QuotesTo (fun c => f (celem_rest c) (celem_head c)) e) :
  QuotesToAtomic (fun c => mk_ofun (f c) (prp:=(fun z => prp z c))) (Lam e) | 1.
Proof.
  apply QuotesTo_Lam. assumption.
Qed.

(* Quote objects that are independent of the context as embedded objects, but at
low priority *)
Instance QuotesTo_Embed {ctx A} {RA:OType A} (a:A) :
  QuotesToAtomic (fun _ => a) (@Embed ctx A RA a) | 2.
Proof.
  intro. reflexivity.
Qed.

(* Quote pairs as applications of opair *)
Instance QuotesTo_pair {ctx A} {RA:OType A} {B} {RB:OType B}
         (a: CtxElem ctx -> A) (b: CtxElem ctx -> B)
         (e1: OExpr ctx A) (e2: OExpr ctx B)
         (q1: QuotesTo a e1) (q2: QuotesTo b e2) :
  QuotesToAtomic (fun c => (a c, b c)) (App (App (Embed opair) e1) e2) | 1.
Proof.
  intro. simpl. rewrite (q1 c). rewrite (q2 c). reflexivity.
Qed.

(* Quote applications of fst as applications of ofst *)
(*
Instance QuotesTo_fst {ctx A} {RA:OType A} {B} {RB:OType B}
         (f: CtxElem ctx -> A * B) (e: OExpr ctx (A*B)) (q: QuotesTo f e) :
  QuotesToAtomic (fun c => fst (f c)) (App (Embed ofst) e) | 1.
Proof.
  intro. simpl. rewrite (q c). reflexivity.
Qed.

(* Quote applications of snd as applications of osnd *)
Instance QuotesTo_snd {ctx A} {RA:OType A} {B} {RB:OType B}
         (f: CtxElem ctx -> A * B) (e: OExpr ctx (A*B)) (q: QuotesTo f e) :
  QuotesToAtomic (fun c => snd (f c)) (App (Embed osnd) e) | 1.
Proof.
  intro. simpl. rewrite (q c). reflexivity.
Qed.
*)

(* Use QuotesTo to prove a relation *)
Lemma oquote_R {A} {RA:OType A} {f1 f2 : A} {e1 e2: OExpr CtxNil A}
      {q1: QuotesTo (fun _ => f1) e1} {q2: QuotesTo (fun _ => f2) e2} :
  e1 <e= e2 -> f1 <o= f2.
Proof.
  intro R12.
  etransitivity; [ apply (q1 tt) | ].
  etransitivity; [ | apply (q2 tt) ].
  apply R12. reflexivity.
Qed.

(* Use QuotesTo to prove an equivalence *)
Lemma oquote_eq {A} {RA:OType A} {f1 f2 : A} {e1 e2: OExpr CtxNil A}
      {q1: QuotesTo (fun _ => f1) e1} {q2: QuotesTo (fun _ => f2) e2} :
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
  repeat (repeat rewrite OExpr_Beta ; simpl;
          try ((rewrite_strat (bottomup (hints osimpl ; eval simpl))))).

(* This one is not as fast for some reason... *)
(*
Ltac oexpr_simpl :=
  rewrite_strat (bottomup (choice (OExpr_Beta ; eval simpl) (hints osimpl))).
 *)

(* Translate a problem about proper functions into one about OExprs by calling
oquote, simplify both sides using the osimpl rewrite database, and then try to
use reflexivity, going back to proper functions if that does not work *)
Ltac osimpl :=
  oquote; try oexpr_simpl; try reflexivity; try typeclasses eauto; simpl.


(***
 *** Unquoting
 ***)

(* Class for unquoting OVars to functions *)
Class UnQuotesToVar {ctx A} {RA:OType A}
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

Instance UnQuotesToVar_Step A RA ctx B (RB:OType B) (v:OVar A ctx) f
         (q: UnQuotesToVar v f) :
  UnQuotesToVar (@OVar_S A RA B RB ctx v) (fun c => f (fst c)).
Proof.
  split.
  - intros c1 c2 Rc. apply (unQuotesToVarProper (UnQuotesToVar:=q)).
    f_equiv. assumption.
  - intros; apply q.
Qed.


(* Class for unquoting OExprs to functions *)
Class UnQuotesTo {ctx A RA} (e: @OExpr ctx A RA) (f: CtxElem ctx -> A) : Prop :=
  unQuotesTo : forall c, f c =o= exprSemantics e @o@ c.

Instance UnQuotesTo_Var ctx A {RA:OType A} (v:OVar A ctx) f
         (q: UnQuotesToVar v f) :
  UnQuotesTo (Var v) f | 1.
Proof.
  intro. rewrite (unQuotesToVar (UnQuotesToVar:=q)). reflexivity.
Qed.

Instance UnQuotesTo_Embed ctx A {RA:OType A} (a:A) :
  UnQuotesTo (@Embed ctx A RA a) (fun _ => a) | 1.
Proof.
  intro; reflexivity.
Qed.

Instance UnQuotesTo_App {ctx A} {RA:OType A} {B} {RB:OType B}
         e1 e2 (f1: CtxElem ctx -> A -o> B) (f2: CtxElem ctx -> A)
         (q1: UnQuotesTo e1 f1) (q2: UnQuotesTo e2 f2) :
  UnQuotesTo (App e1 e2) (fun c => (f1 c) @o@ (f2 c)) | 1.
Proof.
  intro. simpl. f_equiv.
  - apply (unQuotesTo (UnQuotesTo:=q1)).
  - apply (unQuotesTo (UnQuotesTo:=q2)).
Qed.

Lemma Proper_unQuotesTo {ctx A} {RA:OType A} {B} {RB:OType B}
      {e: OExpr (CtxCons A ctx) B} {f} (q: UnQuotesTo e f) c :
  Proper (ot_R ==> ot_R) (fun a => f (c, a)).
Proof.
  intros a1 a2 Ra.
  etransitivity; [ apply (unQuotesTo (UnQuotesTo:=q)) | ].
  etransitivity; [ | apply (unQuotesTo (UnQuotesTo:=q)) ].
  f_equiv. split; [ reflexivity | assumption ].
Qed.

Instance UnQuotesTo_Lam {ctx A} {RA:OType A} {B} {RB:OType B}
      (e: OExpr (CtxCons A ctx) B) f (q: UnQuotesTo e f) :
  UnQuotesTo (Lam e) (fun c =>
                        mk_ofun (fun a => f (c, a))
                                (prp:=Proper_unQuotesTo q c)) | 1.
Proof.
  intro; split; intros a1 a2 Ra; simpl.
  - etransitivity.
    + apply (Proper_unQuotesTo q); apply Ra.
    + apply (unQuotesTo (UnQuotesTo:=q)).
  - etransitivity.
    + apply (unQuotesTo (UnQuotesTo:=q)).
    + apply (Proper_unQuotesTo q); apply Ra.
Qed.


(* The above instance generally will not fire, because the implicit ctx argument
to UnQuotesTo is of the form (ctxInsert w W ctx), but this will generally be
already simplified away in the goal, making it hard for Coq to match. The
following instructs Coq how to do the match by supplying the w argument. *)
Instance UnQuotesTo_weakenOExpr {ctx A} {RA:OType A} w W {OW:OType W}
         (e: OExpr ctx A) f (q: UnQuotesTo e f) :
  UnQuotesTo (weakenOExpr w W e) (fun c => f (weaken_pfun w W _ @o@ c)) | 1.
Proof.
  intro. rewrite weakenOExpr_correct. simpl.
  rewrite (unQuotesTo (UnQuotesTo:=q)). reflexivity.
Qed.

(* The above instance will generally not fire because the ctxInsert implicit
argument to UnQuotesTo will already be simplified, and so Coq will not be able
to match it; this, we make an explicit extern tactic to do the matching *)
Hint Extern 1 (@UnQuotesTo _ _ _ (weakenOExpr _ _ _) _) =>
(lazymatch goal with
 | |- UnQuotesTo (weakenOExpr ?w ?W _) _ =>
   apply (UnQuotesTo_weakenOExpr w W)
 end) : typeclass_instances.


(* This instance is meant to only apply to Coq-level variables of OExpr type *)
Instance UnQuotesTo_MetaVar {ctx A} {RA:OType A} (e:OExpr ctx A) :
  UnQuotesTo e (fun c => exprSemantics e @o@ c) | 2.
Proof.
  intro. f_equiv.
Qed.

Lemma unquote_R {ctx A} {RA:OType A} {e1 e2: OExpr ctx A}
      {f1 f2 : CtxElem ctx -> A} {q1: UnQuotesTo e1 f1} {q2: UnQuotesTo e2 f2} :
  (forall c, f1 c <o= f2 c) -> e1 <e= e2.
Proof.
  intro R12.
  intros c1 c2 Rc. rewrite Rc.
  transitivity (f1 c2); [ apply (unQuotesTo (UnQuotesTo:=q1)) | ].
  transitivity (f2 c2); [ | apply (unQuotesTo (UnQuotesTo:=q2)) ].
  apply R12.
Qed.

Lemma unquote_eq {ctx A} {RA:OType A} {e1 e2: OExpr ctx A}
      {f1 f2 : CtxElem ctx -> A} {q1: UnQuotesTo e1 f1} {q2: UnQuotesTo e2 f2} :
  (forall c, f1 c =o= f2 c) -> e1 =e= e2.
Proof.
  intro R12.
  split; [ apply (unquote_R (q1:=q1) (q2:=q2))
         | apply (unquote_R (q1:=q2) (q2:=q1)) ];
  intro c; destruct (R12 c); assumption.
Qed.


(***
 *** Testing the Quote Mechanism
 ***)

Module OQuoteTest.

(* A simple test case for constant terms *)
Lemma simple_quote_test A `{OType A} a : a =o= a.
  osimpl.
Qed.

(* A simple test case with all 4 OExpr constructs, that does beta-reduction *)
Lemma beta_test A `{OType A} a : (ofun (x:A) => x) @o@ a =o= a.
  osimpl.
Qed.

(* A test case with the first projection of a product *)
Lemma product_proj1_test A `{OType A} B `{OType B} (a:A) (b:B) :
  ofst @o@ (a ,o, b) =o= a.
  osimpl.
Qed.

(* A test case with with beta-reduction and projections + eta for products *)
Lemma beta_product_test A `{OType A} B `{OType B} (p:A*B) :
  (ofun p => (osnd @o@ p ,o, ofst @o@ p)) @o@ (osnd @o@ p ,o, ofst @o@ p)
  =o= p.
  osimpl.
Qed.

Lemma double_lambda_test A `{OType A} :
  (ofun (f : A -o> A) => ofun x => f @o@ x) @o@ (ofun y => y)
  =o= ofun x => x.
  osimpl.
Qed.

(* A test case with with beta-reduction and projections for products *)
Lemma beta_product_test2 A `{OType A} B `{OType B} :
  (ofun a => ofun b => (ofun p => (osnd @o@ p ,o, ofst @o@ p)) @o@ (b ,o, a))
  =o= opair.
  (* osimpl *)
  (* NOTE: we write this out to see how long each step takes... *)
  oquote. oexpr_simpl. reflexivity.
Qed.

End OQuoteTest.
