Require Export PredMonad.Reflection2.OrderedType.


(***
 *** Ordered Type Contexts
 ***)

(* A context here is just a list of type expressions *)
Inductive Ctx : Type :=
| CtxNil
| CtxCons A {RA:OType A} (ctx:Ctx)
.

(* An element of a context is a nested tuple of elements of its types *)
Fixpoint CtxElem (ctx:Ctx) : Type :=
  match ctx with
  | CtxNil => unit
  | @CtxCons A _ ctx' => CtxElem ctx' * A
  end.

(* OTRelation instance for any CtxElem type *)
Instance OType_CtxElem ctx : OType (CtxElem ctx).
Proof.
  induction ctx; typeclasses eauto.
Defined.

(* Map from an element of a context to an element of its head. This is just
fst_pfun, but writing it this way helps the Coq unifier. *)
Definition ctx_head_pfun {ctx A RA} :
  CtxElem (@CtxCons A RA ctx) -o> A :=
  snd_pfun.

(* Map from an element of a context to an element of its tail. This is just
fst_pfun, but writing it this way helps the Coq unifier. *)
Definition ctx_tail_pfun {ctx A RA} :
  CtxElem (@CtxCons A RA ctx) -o> CtxElem ctx :=
  fst_pfun.

(* Look up the nth type in a Ctx, returning the unit type as a default *)
Fixpoint ctxNth ctx n {struct ctx} : Type :=
  match ctx with
  | CtxNil => unit
  | @CtxCons A _ ctx' =>
    match n with
    | 0 => A
    | S n' => ctxNth ctx' n'
    end
  end.
Arguments ctxNth !ctx !n.

(* Look up the nth OType in a Ctx *)
Fixpoint ctxNthOType ctx {struct ctx} : forall n, OType (ctxNth ctx n) :=
  match ctx return forall n, OType (ctxNth ctx n) with
  | CtxNil => fun _ => OTunit
  | @CtxCons A RA ctx' =>
    fun n =>
      match n return OType (ctxNth (@CtxCons A RA ctx') n) with
      | 0 => RA
      | S n' => ctxNthOType ctx' n'
      end
  end.
Arguments ctxNthOType !ctx !n.

Hint Resolve ctxNthOType : typeclass_instances.

(* Pfun to extract the nth element of a context *)
Fixpoint nth_pfun ctx n : CtxElem ctx -o> ctxNth ctx n :=
  match ctx return CtxElem ctx -o> ctxNth ctx n with
  | CtxNil => const_pfun tt
  | CtxCons tp ctx' =>
    match n return CtxElem (CtxCons tp ctx') -o> ctxNth (CtxCons tp ctx') n with
    | 0 => ctx_head_pfun
    | S n' =>
      compose_pfun ctx_tail_pfun (nth_pfun ctx' n')
    end
  end.
Arguments nth_pfun ctx n : simpl nomatch.

(* Weaken a context by inserting a type at point w *)
Fixpoint ctxInsert w W {RW:OType W} ctx {struct w} : Ctx :=
  match w with
  | 0 => CtxCons W ctx
  | S w' =>
    match ctx with
    | CtxNil => CtxCons unit (ctxInsert w' W CtxNil)
    | CtxCons A ctx' => CtxCons A (ctxInsert w' W ctx')
    end
  end.
Arguments ctxInsert w W {RW} ctx : simpl nomatch.

(* Map from a weaker to a stronger context, by dropping the new element *)
Fixpoint weaken_pfun w W {RW} ctx :
  CtxElem (@ctxInsert w W RW ctx) -o> CtxElem ctx :=
  match w return CtxElem (ctxInsert w W ctx) -o> CtxElem ctx with
  | 0 => ctx_tail_pfun
  | S w' =>
    match ctx return CtxElem (ctxInsert (S w') W ctx) -o> CtxElem ctx with
    | CtxNil => const_pfun tt
    | CtxCons tpB ctx' =>
      pair_pfun (compose_pfun ctx_tail_pfun (weaken_pfun w' W ctx'))
                ctx_head_pfun
    end
  end.
Arguments weaken_pfun !w W {RW} !ctx.

(* Delete the nth element of a context *)
Fixpoint ctxDelete n ctx {struct ctx} : Ctx :=
  match ctx with
  | CtxNil => CtxNil
  | CtxCons A ctx' =>
    match n with
    | 0 => ctx'
    | S n' => CtxCons A (ctxDelete n' ctx')
    end
  end.
Arguments ctxDelete n ctx : simpl nomatch.

(* The the n+1-th suffix of a context *)
Fixpoint ctxSuffix n ctx {struct ctx} : Ctx :=
  match ctx with
  | CtxNil => CtxNil
  | CtxCons A ctx' =>
    match n with
    | 0 => ctx'
    | S n' => ctxSuffix n' ctx'
    end
  end.
Arguments ctxSuffix n ctx : simpl nomatch.

(* Substitute into a context by providing a pfun for the nth value *)
Fixpoint subst_pfun ctx n :
  (CtxElem (ctxSuffix n ctx) -o> ctxNth ctx n) ->
  CtxElem (ctxDelete n ctx) -o> CtxElem ctx :=
  match ctx return
        (CtxElem (ctxSuffix n ctx) -o> ctxNth ctx n) ->
        CtxElem (ctxDelete n ctx) -o> CtxElem ctx with
  | CtxNil => fun s => const_pfun tt
  | CtxCons A ctx' =>
    match n return
        (CtxElem (ctxSuffix n (CtxCons A ctx')) -o> ctxNth (CtxCons A ctx') n) ->
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


(***
 *** Appending Ordered Type Contexts
 ***)

(* Inductive proof that ctx2 is an extension of ctx1 *)
Inductive ContextExtendsInd ctx1 : Ctx -> Type :=
| CtxExtNil : ContextExtendsInd ctx1 ctx1
| CtxExtCons A {RA:OType A} ctx2 (ext: ContextExtendsInd ctx1 ctx2) :
    ContextExtendsInd ctx1 (CtxCons A ctx2)
.

(* Typeclass version of the above *)
Class ContextExtends ctx1 ctx2 : Type :=
  contextExtends : ContextExtendsInd ctx1 ctx2.

Instance ContextExtends_base ctx : ContextExtends ctx ctx := CtxExtNil ctx.

Instance ContextExtends_cons ctx1 ctx2 A (RA:OType A)
         (ext: ContextExtends ctx1 ctx2) :
  ContextExtends ctx1 (CtxCons A ctx2) :=
  CtxExtCons ctx1 A ctx2 ext.
