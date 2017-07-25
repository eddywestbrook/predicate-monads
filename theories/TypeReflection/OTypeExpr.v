Require Export PredMonad.TypeReflection.OrderedType.


(***
 *** Ordered Type Expressions
 ***)

Inductive OTypeExpr : Type :=

(* The unit type *)
| OTpUnit

(* Embedding an ordered type *)
| OTpEmbed A `{OType A}

(* Products, sums, and functions *)
| OTpPair (tp1 tp2:OTypeExpr)
| OTpSum (tp1 tp2:OTypeExpr)
| OTpArrow (tp1 tp2:OTypeExpr)

(* Application of an embedded functor *)
| OTpApply (TF: forall A `{OType A}, Type) `{OTypeF TF} (tp:OTypeExpr)
.

(* The semantics of an OTypeExpr *)
Record OTypeSem :=
  {
    otypeSem :> Type;
    otypeSemRelation :> OTRelation otypeSem;
    otypeSemValid :> OType otypeSem
  }.
Arguments otypeSem !o.

Instance OTRelation_OTypeSem sem : OTRelation (otypeSem sem) :=
  otypeSemRelation _.
Instance OType_OTypeSem sem : OType (otypeSem sem) :=
  otypeSemValid _.

(* Interpret an OTypeExpr as a type plus relation *)
Fixpoint otype (tp:OTypeExpr) : OTypeSem :=
  match tp with
  | OTpUnit => Build_OTypeSem unit _ _
  | OTpEmbed A => Build_OTypeSem A _ _
  | OTpPair tp1 tp2 =>
    Build_OTypeSem (prod (otype tp1) (otype tp2)) _ _
  | OTpSum tp1 tp2 =>
    Build_OTypeSem (sum (otype tp1) (otype tp2)) _ _
  | OTpArrow tp1 tp2 =>
    Build_OTypeSem
      (@Pfun (otypeSem (otype tp1)) (otypeSem (otype tp2)) _ _) _ _
  | OTpApply TF tp =>
    Build_OTypeSem
      (TF (otypeSem (otype tp)) _ _)
      _ _
  end.
Arguments otype !tp.

Coercion otype : OTypeExpr >-> OTypeSem.


(***
 *** Ordered Type Contexts
 ***)

(* A context here is just a list of type expressions *)
Inductive Ctx : Type :=
| CtxNil
| CtxCons (tp:OTypeExpr) (ctx:Ctx)
.

(* An element of a context is a nested tuple of elements of its types *)
Fixpoint CtxElem (ctx:Ctx) : Type :=
  match ctx with
  | CtxNil => unit
  | CtxCons tp ctx' => CtxElem ctx' * tp
  end.

(* OTRelation instance for any CtxElem type *)
Instance OTRelation_CtxElem ctx : OTRelation (CtxElem ctx).
Proof.
  induction ctx; typeclasses eauto.
Defined.

Instance OType_CtxElem ctx : OType (CtxElem ctx).
Proof.
  induction ctx; typeclasses eauto.
Qed.

(* Map from an element of a context to an element of its head. This is just
fst_pfun, but writing it this way helps the Coq unifier. *)
Definition ctx_head_pfun {tp ctx} : CtxElem (CtxCons tp ctx) -o> tp :=
  snd_pfun.

(* Map from an element of a context to an element of its tail. This is just
fst_pfun, but writing it this way helps the Coq unifier. *)
Definition ctx_tail_pfun {tp ctx} : CtxElem (CtxCons tp ctx) -o> CtxElem ctx :=
  fst_pfun.

(* Look up the nth type in a Ctx, returning the unit type as a default *)
Fixpoint ctxNth n ctx {struct ctx} : OTypeExpr :=
  match ctx with
  | CtxNil => OTpUnit
  | CtxCons A ctx' =>
    match n with
    | 0 => A
    | S n' => ctxNth n' ctx'
    end
  end.
Arguments ctxNth !n !ctx.

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
Arguments nth_pfun !ctx !n.

(* Weaken a context by inserting a type at point w *)
Fixpoint ctxInsert w tpW ctx {struct w} : Ctx :=
  match w with
  | 0 => CtxCons tpW ctx
  | S w' =>
    match ctx with
    | CtxNil => CtxCons OTpUnit (ctxInsert w' tpW CtxNil)
    | CtxCons tp ctx' => CtxCons tp (ctxInsert w' tpW ctx')
    end
  end.
Arguments ctxInsert w tpW ctx : simpl nomatch.

(* Map from a weaker to a stronger context, by dropping the new element *)
Fixpoint weaken_pfun w tpW ctx :
  CtxElem (ctxInsert w tpW ctx) -o> CtxElem ctx :=
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
Arguments weaken_pfun !w tpW !ctx.

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
Arguments ctxDelete !n !ctx.

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


(***
 *** Quoting Mechanism for Types
 ***)

Class QuotesToType (A:Type) `{OType A} tp : Prop :=
  quotesToType : otype tp = Build_OTypeSem A _ _.

(* Quote the unit type to OTpUnit *)
Instance QuotesToType_unit : QuotesToType unit OTpUnit | 1 := eq_refl.

(* Quote anything that doesn't match another rule using OTpEmbed *)
Instance QuotesToType_embed A `{OType A} : QuotesToType A (OTpEmbed A) | 3 :=
  eq_refl.

(* Quote products, sums, and arrows accordingly *)
Instance QuotesToType_pair A1 A2 `(OType A1) `(OType A2)
         tp1 tp2 (q1:QuotesToType A1 tp1) (q2:QuotesToType A2 tp2) :
  QuotesToType (A1 * A2) (OTpPair tp1 tp2) | 1.
Proof.
  unfold QuotesToType in * |- *. simpl. rewrite q1. rewrite q2. reflexivity.
Qed.

Instance QuotesToType_sum A1 A2 `(OType A1) `(OType A2)
         tp1 tp2 (q1:QuotesToType A1 tp1) (q2:QuotesToType A2 tp2) :
  QuotesToType (A1 + A2) (OTpSum tp1 tp2) | 1.
Proof.
  unfold QuotesToType in * |- *. simpl. rewrite q1. rewrite q2. reflexivity.
Qed.

Instance QuotesToType_arrow A1 A2 `(OType A1) `(OType A2)
         tp1 tp2 (q1:QuotesToType A1 tp1) (q2:QuotesToType A2 tp2) :
  QuotesToType (A1 -o> A2) (OTpArrow tp1 tp2) | 1.
Proof.
  unfold QuotesToType in * |- *. simpl. rewrite q1. rewrite q2. reflexivity.
Qed.

Instance QuotesToType_apply (TF: forall A `{OType A}, Type) `{OTypeF TF}
         A `(OType A) tp (q:QuotesToType A tp) :
  QuotesToType (TF A) (OTpApply TF tp) | 1.
Proof.
  unfold QuotesToType in * |- *. simpl. rewrite q. reflexivity.
Qed.


(*
Definition quote_type_test A `{OType A} {tp:OTypeExpr} `{QuotesToType A tp} :=
  tp.

Eval compute in (fun A `(OType A) => quote_type_test (A -o> A * unit)).

Eval compute in (fun TF `(OTypeF TF) A `(OType A) =>
                   quote_type_test (TF (A + unit)%type _ _ -o> A * unit)).
 *)
