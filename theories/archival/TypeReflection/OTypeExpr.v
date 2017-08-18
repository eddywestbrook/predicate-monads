Require Export PredMonad.TypeReflection.OrderedType.


(***
 *** Ordered Type Expressions
 ***)

Inductive OTypeExprInd : forall A {RA:OTRelation A}, Type :=
| OTpUnit : OTypeExprInd unit
| OTpEmbed A `{OType A} : OTypeExprInd A
| OTpPair {A} {RA:OTRelation A} {B} {RB:OTRelation B}
          (tp1: OTypeExprInd A) (tp2: OTypeExprInd B) : OTypeExprInd (A * B)
| OTpSum {A} {RA:OTRelation A} {B} {RB:OTRelation B}
         (tp1: OTypeExprInd A) (tp2: OTypeExprInd B) : OTypeExprInd (A + B)
| OTpArrow {A} {RA:OTRelation A} {B} {RB:OTRelation B}
           (tp1: OTypeExprInd A) (tp2: OTypeExprInd B) : OTypeExprInd (A -o> B)
| OTpApply {arity} F `{OTypeF1 arity F} As (tps:OTypeExprInds As) :
    OTypeExprInd (OTFunctorApply arity F As)
with
OTypeExprInds : OTArgs -> Type :=
| OTpNil : OTypeExprInds ArgsNil
| OTpCons {A} {RA:OTRelation A} {As} (tp: OTypeExprInd A) (tps:OTypeExprInds As) :
    OTypeExprInds (ArgsCons A As)
.

(* Define the mutual recursion / induction schemes for OTypeExprInd *)
Scheme OTypeExpr_OTypeExprs_rec := Induction for OTypeExprInd Sort Type
  with OTypeExprs_OTypeExpr_rec := Induction for OTypeExprInds Sort Type.

(* Apply a predicate to all OTypeExprs in an OTypeExprs list *)
Fixpoint forall_OTypeExprInds (P: forall A RA, @OTypeExprInd A RA -> Type)
         args (tps:OTypeExprInds args) : Type :=
  match tps with
  | OTpNil => True
  | OTpCons tp tps => P _ _ tp * forall_OTypeExprInds P _ tps
  end.

(* Mutual induction scheme for OTypeExprInd *)
Definition OTypeExprInd_rect' P f1 f2 f3 f4 f5 f6 :=
  OTypeExpr_OTypeExprs_rec P (forall_OTypeExprInds P)
                           f1 f2 f3 f4 f5 f6 I
                           (fun _ _ _ _ x _ xs => (x,xs)).

(* Typeclass version of OTypeExprInd *)
Class OTypeExpr A {RA:OTRelation A} : Type :=
  otypeExpr : @OTypeExprInd A RA.

(* Instances for building OTypeExprs *)
(*
Instance OTypeExpr_unit : OTypeExpr unit := OTpUnit.
Instance OTypeExpr_pair A RA (tpA:@OTypeExpr A RA) B RB (tpB:@OTypeExpr B RB) :
  OTypeExpr (A*B) | 1 := OTpPair tpA tpB.
Instance OTypeExpr_sum A RA (tpA:@OTypeExpr A RA) B RB (tpB:@OTypeExpr B RB) :
  OTypeExpr (A+B) | 1 := OTpSum tpA tpB.
Instance OTypeExpr_arrow A RA (tpA:@OTypeExpr A RA) B RB (tpB:@OTypeExpr B RB) :
  OTypeExpr (A -o> B) | 1 := OTpArrow tpA tpB.
Instance OTypeExpr_embed A `{OType A} : OTypeExpr A | 2 := OTpEmbed A.
 *)

Ltac prove_OTypeExpr :=
  match goal with
  | |- OTypeExprInd _ => assumption
  | |- @OTypeExprInd ?A ?RA => change (@OTypeExpr A RA); try prove_OTypeExpr
  | |- OTypeExpr _ => assumption
  | |- OTypeExpr unit => apply OTpUnit
  | |- OTypeExpr (_ * _) => apply OTpPair; try prove_OTypeExpr
  | |- OTypeExpr (_ + _) => apply OTpSum; try prove_OTypeExpr
  | |- OTypeExpr (_ -o> _) => apply OTpArrow; try prove_OTypeExpr
  | |- OTypeExpr (?F _ _) =>
    refine (OTpApply F (OTpCons _ OTpNil)); try prove_OTypeExpr
  | |- OTypeExpr _ => apply OTpEmbed; try prove_OTypeExpr
  end.

Hint Extern 1 (OTypeExpr _) => prove_OTypeExpr : typeclass_instances.
Hint Extern 1 (OTypeExprInd _) => prove_OTypeExpr : typeclass_instances.

(* Any type + relation with an OTypeExpr representation is valid *)
Lemma OType_OTypeExpr A (RA:OTRelation A) (tp:OTypeExpr A) : OType A.
Proof.
  apply
    (OTypeExpr_OTypeExprs_rec (fun A RA _ => @OType A RA)
                              (fun As _ => OTArgsValid As));
    try typeclasses eauto.
Qed.

(* Only apply OType_OTypeExpr when there are OTypeExprs in the context *)
Hint Immediate OType_OTypeExpr : typeclass_instances.


(***
 *** Ordered Type Contexts
 ***)

(* A context here is just a list of type expressions *)
Inductive Ctx : Type :=
| CtxNil
| CtxCons {A RA} (tp:@OTypeExpr A RA) (ctx:Ctx)
.

(* An element of a context is a nested tuple of elements of its types *)
Fixpoint CtxElem (ctx:Ctx) : Type :=
  match ctx with
  | CtxNil => unit
  | @CtxCons A _ tp ctx' => CtxElem ctx' * A
  end.

(* OTRelation instance for any CtxElem type *)
Instance OTRelation_CtxElem ctx : OTRelation (CtxElem ctx).
Proof.
  induction ctx; typeclasses eauto.
Defined.

Instance OType_CtxElem ctx : OType (CtxElem ctx).
Proof.
  induction ctx; simpl; [ typeclasses eauto | ].
  apply OTpair; [ typeclasses eauto | ]. apply OType_OTypeExpr. assumption.
Qed.

(* Map from an element of a context to an element of its head. This is just
fst_pfun, but writing it this way helps the Coq unifier. *)
Definition ctx_head_pfun {ctx A RA} {tp:@OTypeExpr A RA} :
  CtxElem (CtxCons tp ctx) -o> A :=
  snd_pfun.

(* Map from an element of a context to an element of its tail. This is just
fst_pfun, but writing it this way helps the Coq unifier. *)
Definition ctx_tail_pfun {ctx A RA} {tp:@OTypeExpr A RA} :
  CtxElem (CtxCons tp ctx) -o> CtxElem ctx :=
  fst_pfun.

(* Look up the nth type in a Ctx, returning the unit type as a default *)
Fixpoint ctxNth n ctx {struct ctx} : Type :=
  match ctx with
  | CtxNil => unit
  | @CtxCons A _ _ ctx' =>
    match n with
    | 0 => A
    | S n' => ctxNth n' ctx'
    end
  end.
Arguments ctxNth !n !ctx.

Instance OTRelation_ctxNth n ctx : OTRelation (ctxNth n ctx).
Proof.
  revert n; induction ctx; [ | destruct n ]; intros; typeclasses eauto.
Defined.

(* Look up the nth OTypeExpr in a Ctx *)
Fixpoint ctxNthExpr n ctx {struct ctx} : OTypeExpr (ctxNth n ctx) :=
  match ctx with
  | CtxNil => OTpUnit
  | CtxCons tp ctx' =>
    match n with
    | 0 => tp
    | S n' => ctxNthExpr n' ctx'
    end
  end.
Arguments ctxNthExpr !n !ctx.

(* Pfun to extract the nth element of a context *)
Fixpoint nth_pfun ctx n : CtxElem ctx -o> ctxNth n ctx :=
  match ctx return CtxElem ctx -o> ctxNth n ctx with
  | CtxNil => const_pfun tt
  | CtxCons tp ctx' =>
    match n return CtxElem (CtxCons tp ctx') -o> ctxNth n (CtxCons tp ctx') with
    | 0 => ctx_head_pfun
    | S n' =>
      compose_pfun ctx_tail_pfun (nth_pfun ctx' n')
    end
  end.
Arguments nth_pfun ctx n : simpl nomatch.

(* Weaken a context by inserting a type at point w *)
Fixpoint ctxInsert w {W RW} (tpW:@OTypeExpr W RW) ctx {struct w} : Ctx :=
  match w with
  | 0 => CtxCons tpW ctx
  | S w' =>
    match ctx with
    | CtxNil => CtxCons OTpUnit (ctxInsert w' tpW CtxNil)
    | CtxCons tp ctx' => CtxCons tp (ctxInsert w' tpW ctx')
    end
  end.
Arguments ctxInsert w {W RW} tpW ctx : simpl nomatch.

(* Map from a weaker to a stronger context, by dropping the new element *)
Fixpoint weaken_pfun w {W RW} tpW ctx :
  CtxElem (@ctxInsert w W RW tpW ctx) -o> CtxElem ctx :=
  match w return CtxElem (ctxInsert w tpW ctx) -o> CtxElem ctx with
  | 0 => ctx_tail_pfun
  | S w' =>
    match ctx return CtxElem (ctxInsert (S w') tpW ctx) -o> CtxElem ctx with
    | CtxNil => const_pfun tt
    | CtxCons tpB ctx' =>
      pair_pfun (compose_pfun ctx_tail_pfun (weaken_pfun w' tpW ctx'))
                ctx_head_pfun
    end
  end.
Arguments weaken_pfun !w {W RW} tpW !ctx.

(* Delete the nth element of a context *)
Fixpoint ctxDelete n ctx {struct ctx} : Ctx :=
  match ctx with
  | CtxNil => CtxNil
  | CtxCons tp ctx' =>
    match n with
    | 0 => ctx'
    | S n' => CtxCons tp (ctxDelete n' ctx')
    end
  end.
Arguments ctxDelete n ctx : simpl nomatch.

(* The the n+1-th suffix of a context *)
Fixpoint ctxSuffix n ctx {struct ctx} : Ctx :=
  match ctx with
  | CtxNil => CtxNil
  | CtxCons tp ctx' =>
    match n with
    | 0 => ctx'
    | S n' => ctxSuffix n' ctx'
    end
  end.
Arguments ctxSuffix n ctx : simpl nomatch.

(* Substitute into a context by providing a pfun for the nth value *)
Fixpoint subst_pfun ctx n :
  (CtxElem (ctxSuffix n ctx) -o> ctxNth n ctx) ->
  CtxElem (ctxDelete n ctx) -o> CtxElem ctx :=
  match ctx return
        (CtxElem (ctxSuffix n ctx) -o> ctxNth n ctx) ->
        CtxElem (ctxDelete n ctx) -o> CtxElem ctx with
  | CtxNil => fun s => const_pfun tt
  | CtxCons A ctx' =>
    match n return
        (CtxElem (ctxSuffix n (CtxCons A ctx')) -o> ctxNth n (CtxCons A ctx')) ->
        CtxElem (ctxDelete n (CtxCons A ctx')) -o> CtxElem (CtxCons A ctx')
    with
    | 0 => fun s => pair_pfun id_pfun s
    | S n' =>
      fun s =>
        pair_pfun (compose_pfun fst_pfun (subst_pfun ctx' n' s)) snd_pfun
    end
  end.
Arguments subst_pfun ctx n : simpl nomatch.

(* Proper-ness of subst_pfun *)
Instance Proper_subst_pfun ctx n : Proper (ot_R ==> ot_R) (subst_pfun ctx n).
Proof.
  revert n; induction ctx; intros; [ | destruct n ]; simpl; intros s1 s2 Rs.
  - reflexivity.
  - intros c1 c2 Rc; simpl. split; [ | apply Rs ]; assumption.
  - intros c1 c2 Rc; simpl.
    split; destruct Rc; [ apply IHctx | ]; assumption.
Qed.

(* Proper-ness of subst_pfun w.r.t equivalence *)
Instance Proper_subst_pfun_equiv ctx n :
  Proper (ot_equiv ==> ot_equiv) (subst_pfun ctx n).
Proof.
  intros s1 s2 Rs; destruct Rs; split; apply Proper_subst_pfun; assumption.
Qed.
