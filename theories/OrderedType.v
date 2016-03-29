Require Export Coq.Program.Tactics.
Require Export Coq.Setoids.Setoid.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Arith.Arith_base.
Require Export Coq.Relations.Relations.
Require Export Coq.Lists.List.

Import EqNotations.
Import ListNotations.


(***
 *** Semi-Transitive Relations
 ***)

(* Semi-Transitivity is to PERs as pre-orders are to equivalence relations *)
Class SemiTransitive {A} (R:relation A) : Prop :=
  {
    semitransitivity :
      forall x y z, R x x -> R y y -> R z z -> R x y -> R y z -> R x z
  }.

(* Restrict a semi-transitive relation to the "valid" elements, i.e., those that
are related to themselves *)
Definition validR {A} (R:relation A) : relation A :=
   fun x y => R x x /\ R y y /\ R x y.

(* FIXME: validR R is transitive when R is semi-transitive *)


(***
 *** Ordered Types = Types with a Semi-PreOrder
 ***)

Record OrderedType : Type :=
  {
    ot_Type :> Type;
    ot_R :> relation ot_Type;
    ot_PreOrder :> SemiTransitive ot_R
  }.


(***
 *** Commonly-Used Ordered Types
 ***)

(* The ordered type of propositions *)
Program Definition OTProp : OrderedType :=
  {|
    ot_Type := Prop;
    ot_R := iff;
  |}.
Next Obligation.
  constructor.
  { intros. transitivity y; assumption. }
Qed.

(* The ordered type of natural numbers *)
Program Definition OTnat : OrderedType :=
  {|
    ot_Type := nat;
    ot_R := le;
  |}.
Next Obligation.
  constructor.
  { intros. transitivity y; assumption. }
Qed.

(* NOTE: the following definition requires everything above to be polymorphic *)
(* NOTE: The definition we choose for OTType is actually deep: instead of
requiring ot_Type A = ot_Type B, we could just require a coercion function from
ot_Type A to ot_Type B, which would yield something more like HoTT... though
maybe it wouldn't work unless we assumed the HoTT axiom? As it is, we might need
UIP to hold if we want to use the definition given here... *)
(*
Program Definition OTType : OrderedType :=
  {|
    ot_Type := OrderedType;
    ot_R := (fun A B =>
               exists (e:ot_Type A = ot_Type B),
                 forall (x y:A),
                   ot_R A x y ->
                   ot_R B (rew [fun A => A] e in x)
                        (rew [fun A => A] e in y));
  |}.
*)

(* The non-dependent function ordered type *)
Program Definition OTArrow
            (A:OrderedType) (B: OrderedType) : OrderedType :=
  {|
    ot_Type := ot_Type A -> ot_Type B;
    ot_R := fun f g =>
              forall x y, validR (ot_R A) x y -> ot_R B (f x) (g y);
  |}.
Next Obligation.
  constructor. intros f g h; intros. destruct H4; destruct H5.
  apply (semitransitivity (SemiTransitive:=B) _ (g y)).
  { apply H; repeat split; assumption. }
  { apply H0; repeat split; assumption. }
  { apply H1; repeat split; assumption. }
  { apply H2; repeat split; assumption. }
  { apply H3; repeat split; assumption. }
Qed.


(* The non-dependent product ordered type *)
Program Definition OTProd
            (A:OrderedType) (B: OrderedType) : OrderedType :=
  {|
    ot_Type := ot_Type A * ot_Type B;
    ot_R := fun p1 p2 =>
              ot_R A (fst p1) (fst p2) /\ ot_R B (snd p1) (snd p2)
  |}.
Next Obligation.
  constructor. intros p1 p2 p3; intros.
  destruct H; destruct H0; destruct H1; destruct H2; destruct H3.
  split.
  { apply (semitransitivity (SemiTransitive:=A) _ (fst p2)); assumption. }
  { apply (semitransitivity (SemiTransitive:=B) _ (snd p2)); assumption. }
Qed.


(* The non-dependent sum ordered type *)
Program Definition OTSum
            (A:OrderedType) (B: OrderedType) : OrderedType :=
  {|
    ot_Type := ot_Type A + ot_Type B;
    ot_R := fun sum1 sum2 =>
              match sum1, sum2 with
                | inl x, inl y => ot_R A x y
                | inl x, inr y => False
                | inr x, inl y => False
                | inr x, inr y => ot_R B x y
              end
  |}.
Next Obligation.
  constructor.
  intros sum1 sum2 sum3; destruct sum1; destruct sum2; destruct sum3; intros.
  { apply (semitransitivity (SemiTransitive:=A) _ o0); assumption. }
  { assumption. }
  { elimtype False; assumption. }
  { elimtype False; assumption. }
  { assumption. }
  { elimtype False; assumption. }
  { assumption. }
  { apply (semitransitivity (SemiTransitive:=B) _ o0); assumption. }
Qed.

(* FIXME: also need notations *)

(* FIXME: could also do a forall type, but need the second type argument, B, to
itself be proper, i.e., to be an element of OTArrow A OType. Would also need a
dependent version of OTContext, below. *)



(***
 *** Types-in-Context
 ***)

(* An ordered type context is a list of ordered types *)
Definition OTContext := list OrderedType.

(* An element of an ordered type context is an element of each ordered type *)
Fixpoint ctx_elem (ctx:OTContext) : Type :=
  match ctx with
  | [] => unit
  | A::ctx' => (ot_Type A) * (ctx_elem ctx')
  end.

(* The ordering on ordered type context elements is the pointwise orderings of
all the ordered types in the context *)
Fixpoint ctx_elem_lt (ctx:OTContext) : relation (ctx_elem ctx) :=
  match ctx with
  | [] => fun _ _ => True
  | A::ctx' => fun e1 e2 =>
                 validR (ot_R A) (fst e1) (fst e2) /\
                 ctx_elem_lt ctx' (snd e1) (snd e2)
  end.

(* Consing two ordered objects to two ordered context elements yields two
ordered context elements *)
Lemma ctx_elem_lt_cons ctx A celem1 celem2 a1 a2
      (pf_ctx: validR (ctx_elem_lt ctx) celem1 celem2)
      (pf_A : validR (ot_R A) a1 a2) :
  validR (ctx_elem_lt (A::ctx)) (a1,celem1) (a2,celem2).
  unfold ctx_elem_lt; fold ctx_elem_lt.
  destruct pf_ctx as [ pf_ctx1 pf_ctx2 ]; destruct pf_ctx2 as [ pf_ctx2 pf_ctx3 ].
  destruct pf_A as [ pf_A1 pf_A2 ]; destruct pf_A2 as [ pf_A2 pf_A3 ].
  repeat split; assumption.
Qed.

(* The ordered type of context elements *)
Program Definition OTCtxElem (ctx:OTContext) : OrderedType :=
  {|
    ot_Type := ctx_elem ctx;
    ot_R := ctx_elem_lt ctx;
  |}.
Next Obligation.
  induction ctx; constructor.
  { intros; assumption. }
  { repeat (intro foo; destruct foo). split.
    - destruct H; destruct H3; destruct H5; destruct H11;
        destruct H7; destruct H13.
      repeat split; try assumption.
      apply (@semitransitivity _ _ (ot_PreOrder a) _ (fst (o0, c0)));
        try assumption.
    - apply (semitransitivity _ (snd (o0, c0))); assumption.
  }
Qed.

(* The ordered type of objects-in-context *)
Definition OTInCtx (ctx:OTContext) (A:OrderedType) : OrderedType :=
  OTArrow (OTCtxElem ctx) A.


(***
 *** Context Extensions
 ***)

(* Captures that one context extends another. Note that we put this in Type
instead of Prop so we can induct on it. *)
Inductive ContextExtends : OTContext -> OTContext -> Type :=
| ContextExtends_nil : ContextExtends [] []
| ContextExtends_cons_both {ctx1 ctx2} A :
    ContextExtends ctx1 ctx2 -> ContextExtends (A::ctx1) (A::ctx2)
| ContextExtends_cons_right {ctx1 ctx2} A :
    ContextExtends ctx1 ctx2 -> ContextExtends ctx1 (A::ctx2)
.

(* Context extension is reflexive *)
Definition ContextExtends_reflexive ctx : ContextExtends ctx ctx.
  induction ctx; constructor; assumption.
Defined.

(* Context extension as a type class *)
Class OTCtxExtends ctx1 ctx2 : Type :=
  context_extends : ContextExtends ctx1 ctx2.

Arguments context_extends {_ _ _}.

(* The rules for context extension, as type class instances *)
Instance OTCtxExtends_base ctx : OTCtxExtends ctx ctx :=
  ContextExtends_reflexive _.

Instance OTCtxExtends_cons_both ctx1 ctx2
         {ext:OTCtxExtends ctx1 ctx2} {B} : OTCtxExtends (B::ctx1) (B::ctx2) :=
  ContextExtends_cons_both _ context_extends.

Instance OTCtxExtends_cons_right ctx1 ctx2
         {ext:OTCtxExtends ctx1 ctx2} {B} : OTCtxExtends ctx1 (B::ctx2) :=
  ContextExtends_cons_right _ context_extends.


(* "Forget" elements of an extended context to get an un-extended context *)
Fixpoint context_forget {ctx1 ctx2} (ext: ContextExtends ctx1 ctx2) :
  ctx_elem ctx2 -> ctx_elem ctx1 :=
  match ext in ContextExtends ctx1 ctx2
        return ctx_elem ctx2 -> ctx_elem ctx1 with
    | ContextExtends_nil => fun celem => celem
    | ContextExtends_cons_both A ext' =>
      fun celem =>
        let (a,celem') := celem in
        (a, context_forget ext' celem')
    | ContextExtends_cons_right A ext' =>
      fun celem =>
        let (a,celem') := celem in
        context_forget ext' celem'
  end.

(* Forgetting preserves context element ordering *)
Lemma context_forget_preserves {ctx1 ctx2} ext celem2_1 celem2_2 :
  ctx_elem_lt ctx2 celem2_1 celem2_2 ->
  ctx_elem_lt ctx1 (context_forget ext celem2_1) (context_forget ext celem2_2).
  revert celem2_1 celem2_2; induction ext; intros.
  { unfold context_forget; assumption. }
  { unfold context_forget; fold (context_forget ext).
    destruct celem2_1; destruct celem2_2. destruct H; destruct H; destruct H1.
    repeat constructor; unfold fst in * |- *; try assumption.
    apply IHext; assumption. }
  { unfold context_forget; fold (context_forget ext).
    destruct celem2_1; destruct celem2_2. destruct H; destruct H; destruct H1.
    apply IHext; assumption. }
Qed.

(* Forgetting thus preserves valid context element ordering *)
Lemma context_forget_preserves_validR {ctx1 ctx2} ext celem2_1 celem2_2 :
  validR (ctx_elem_lt ctx2) celem2_1 celem2_2 ->
  validR (ctx_elem_lt ctx1)
         (context_forget ext celem2_1) (context_forget ext celem2_2).
  intro pf; destruct pf as [ pf1 pf2 ]; destruct pf2 as [ pf2 pf3 ].
  repeat constructor; apply context_forget_preserves; assumption.
Qed.


(***
 *** Pairs of Related Elements
 ***)

(* Pairs of terms-in-context that are valid and related to each other *)
Inductive OTPairInCtx ctx A : Type :=
  mkOTPairInCtx (x1: ctx_elem ctx -> ot_Type A)
                (x2: ctx_elem ctx -> ot_Type A)
                (pf: validR (ot_R (OTInCtx ctx A)) x1 x2) :
    OTPairInCtx ctx A.

(* Weakening the context of an OTPairInCtx *)
Program Definition weaken_context {ctx1 ctx2} (ext: ContextExtends ctx1 ctx2)
           {A} (p: OTPairInCtx ctx1 A) : OTPairInCtx ctx2 A :=
  match p with
    | mkOTPairInCtx _ _ x1 x2 pf =>
      mkOTPairInCtx _ _ (fun celem1 => x1 (context_forget ext celem1))
                    (fun celem1 => x2 (context_forget ext celem1))
                    _
  end.
Next Obligation.
  destruct pf as [ pf1 pf2 ]; destruct pf2 as [ pf2 pf3 ].
  repeat constructor;
    intros; [ apply pf1 | apply pf2 | apply pf3 ];
    apply context_forget_preserves_validR; assumption.
Qed.

(* Build a term-in-context for the top-most variable in the context *)
Program Definition top_var_in_context ctx A : OTPairInCtx (A::ctx) A :=
  mkOTPairInCtx (A::ctx) A
           (fun ctx_elem =>
              let (celem_A,_) := ctx_elem in celem_A)
           (fun ctx_elem =>
              let (celem_A,_) := ctx_elem in celem_A)
           _.
Next Obligation.
  repeat split;
    intros x y; destruct x; destruct y; unfold fst; unfold snd;
      intros; repeat (destruct H); repeat (destruct H0);
        destruct H2; destruct H3; destruct H5; destruct H3; destruct H9;
          assumption.
Qed.

(* OTPairInCtx is a functor w.r.t. proper functions *)
Program Definition map_OTPairInCtx {ctx A B}
        (f: ot_Type A -> ot_Type B)
        (proper: Proper (validR (ot_R A) ==> validR (ot_R B)) f)
        (x: OTPairInCtx ctx A) : OTPairInCtx ctx B :=
  let (x1,x2,pf_x) := x in
  mkOTPairInCtx _ _ (fun celem => f (x1 celem)) (fun celem => f (x2 celem)) _.
Next Obligation.
  destruct pf_x as [ pfx_1 pfx_2 ]; destruct pfx_2 as [ pfx_2 pfx_3 ].
  repeat split; intros celem1 celem2 H; apply proper; repeat split;
  first [ apply pfx_1 | apply pfx_2 | apply pfx_3 ];
  try assumption; destruct H; destruct H0; repeat split; assumption.
Qed.

(* OTPairInCtx is also a bi-functor w.r.t. proper functions *)
Program Definition map2_OTPairInCtx {ctx A B C}
        (f: ot_Type A -> ot_Type B -> ot_Type C)
        (proper: Proper (validR (ot_R A) ==> validR (ot_R B) ==> validR (ot_R C)) f)
        (x: OTPairInCtx ctx A) (y: OTPairInCtx ctx B) : OTPairInCtx ctx C :=
  let (x1,x2,pf_x) := x in
  let (y1,y2,pf_y) := y in
  mkOTPairInCtx _ _ (fun celem => f (x1 celem) (y1 celem))
                (fun celem => f (x2 celem) (y2 celem)) _.
Next Obligation.
  destruct pf_x as [ pfx_1 pfx_2 ]; destruct pfx_2 as [ pfx_2 pfx_3 ].
  destruct pf_y as [ pfy_1 pfy_2 ]; destruct pfy_2 as [ pfy_2 pfy_3 ].
  repeat split; intros celem1 celem2 H; apply proper; repeat split;
  first [ apply pfx_1 | apply pfy_1 | apply pfx_2 | apply pfy_2 |
          apply pfx_3 | apply pfy_3 ];
  try assumption; destruct H; destruct H0; repeat split; assumption.
Qed.

(* OTPairInCtx is also a tri-functor w.r.t. proper functions *)
Program Definition map3_OTPairInCtx {ctx A B C D}
        (f: ot_Type A -> ot_Type B -> ot_Type C -> ot_Type D)
        (proper: Proper (validR (ot_R A) ==> validR (ot_R B) ==>
                                validR (ot_R C) ==> validR (ot_R D)) f)
        (x: OTPairInCtx ctx A) (y: OTPairInCtx ctx B) (z: OTPairInCtx ctx C)
: OTPairInCtx ctx D :=
  let (x1,x2,pf_x) := x in
  let (y1,y2,pf_y) := y in
  let (z1,z2,pf_z) := z in
  mkOTPairInCtx _ _ (fun celem => f (x1 celem) (y1 celem) (z1 celem))
                (fun celem => f (x2 celem) (y2 celem) (z2 celem)) _.
Next Obligation.
  destruct pf_x as [ pfx_1 pfx_2 ]; destruct pfx_2 as [ pfx_2 pfx_3 ].
  destruct pf_y as [ pfy_1 pfy_2 ]; destruct pfy_2 as [ pfy_2 pfy_3 ].
  destruct pf_z as [ pfz_1 pfz_2 ]; destruct pfz_2 as [ pfz_2 pfz_3 ].
  repeat split; intros celem1 celem2 H; apply proper; repeat split;
  first [ apply pfx_1 | apply pfy_1 | apply pfz_1 |
          apply pfx_2 | apply pfy_2 | apply pfz_2 |
          apply pfx_3 | apply pfy_3 | apply pfz_3 ];
  try assumption; destruct H; destruct H0; repeat split; assumption.
Qed.


(***
 *** Top-Level Proper Terms
 ***)

(* A "proper term" is an OTPairInCtx in the empty context *)
Definition ProperTerm (A:OrderedType) := OTPairInCtx [] A.

(* We can coerce a ProperTerm A to an element of ot_Type A by just taking the
first projection of the pair in the ProperTerm *)
Definition coerce_proper_term {A} (p: ProperTerm A) : ot_Type A :=
  match p with
  | mkOTPairInCtx _ _ x1 x2 pf => x1 tt
  end.

Coercion coerce_proper_term : ProperTerm >-> ot_Type.

(* Any ProperTerm is always Proper *)
Instance ProperTerm_Proper {A} (p:ProperTerm A) : Proper (ot_R A) p.
destruct p; unfold coerce_proper_term. destruct pf; apply H.
repeat split.
Qed.


(***
 *** Builders for Proper Terms using OTPairInCtx
 ***)

(* Helper to build a ProperTerm for a function *)
Program Definition proper_fun {ctx} {A} {B}
        (f: (forall {ctx'} `{ext: OTCtxExtends (A::ctx) ctx'},
               OTPairInCtx ctx' A) ->
            OTPairInCtx (A::ctx) B) :
  OTPairInCtx ctx (OTArrow A B) :=
  let (y1,y2,pf_y) :=
      f (fun {ctx'} {ext} => weaken_context ext (top_var_in_context ctx A))
  in
  mkOTPairInCtx _ _ (fun ctx_elem x => y1 (x,ctx_elem))
           (fun ctx_elem x => y2 (x,ctx_elem)) _.
Next Obligation.
  destruct pf_y as [ pf1 pf2 ]; destruct pf2 as [ pf2 pf3 ].
  repeat split; intros; [ apply pf1 | apply pf2 | apply pf3 ];
  apply ctx_elem_lt_cons; assumption.
Qed.

(* Helper to implicitly add the arguments for a ProperTerm variable *)
Definition proper_var {ctx} {A}
           (var: (forall ctx' (ext: OTCtxExtends (A::ctx) ctx'),
                    OTPairInCtx ctx' A))
           {ctx'} {ext: OTCtxExtends (A::ctx) ctx'} :
  OTPairInCtx ctx' A :=
  var ctx' ext.


(* Helper to build a ProperTerm for an application *)
Program Definition proper_apply {ctx} {A} {B}
        (f: OTPairInCtx ctx (OTArrow A B))
        (x: OTPairInCtx ctx A) : OTPairInCtx ctx B :=
  map2_OTPairInCtx (A:=OTArrow A B) (fun g y => g y) _ f x.
Next Obligation.
  intros f1 f2 pf_f;
  destruct pf_f as [ pf_f1 pf_f2 ]; destruct pf_f2 as [ pf_f2 pf_f3 ];
  intros x1 x2 pf_x;
  destruct pf_x as [ pf_x1 pf_x2 ]; destruct pf_x2 as [ pf_x2 pf_x3 ];
  repeat split;
  first [ apply pf_f1 | apply pf_f2 | apply pf_f3 ];
  repeat split; assumption.
Qed.

(* Helper to build a ProperTerm for a pair *)
Program Definition proper_pair {ctx} {A} {B}
           (x: OTPairInCtx ctx A) (y: OTPairInCtx ctx B) :
  OTPairInCtx ctx (OTProd A B) :=
  map2_OTPairInCtx (C:=OTProd A B) (fun x y => (x,y)) _ x y.
Next Obligation.
repeat (intro; intros); destruct H; destruct H1; destruct H0; destruct H3.
unfold fst, snd; repeat split; assumption.
Qed.

(* Helper to build a ProperTerm for a first projection *)
Program Definition proper_proj1 {ctx} {A} {B}
           (x: OTPairInCtx ctx (OTProd A B)) : OTPairInCtx ctx A :=
  map_OTPairInCtx (A:=OTProd A B) (fun p => fst p) _ x.
Next Obligation.
  intros p1 p2; destruct p1; destruct p2; unfold fst;
  intro pf_p; destruct pf_p.
  destruct H; repeat destruct H0; destruct H2.
  repeat split; assumption.
Qed.

(* Helper to build a ProperTerm for a second projection *)
Program Definition proper_proj2 {ctx} {A} {B}
           (x: OTPairInCtx ctx (OTProd A B)) : OTPairInCtx ctx B :=
  map_OTPairInCtx (A:=OTProd A B) (fun p => snd p) _ x.
Next Obligation.
  intros p1 p2; destruct p1; destruct p2; unfold snd;
  intro pf_p; destruct pf_p.
  destruct H; repeat destruct H0; destruct H2.
  repeat split; assumption.
Qed.

(* Helper to build a ProperTerm for the inl constructor *)
Program Definition proper_inl {ctx} {A} {B}
           (x: OTPairInCtx ctx A) : OTPairInCtx ctx (OTSum A B) :=
  map_OTPairInCtx (B:=OTSum A B) (fun y => inl y) _ x.
Next Obligation.
  intros x1 x2 pf_x; assumption.
Qed.

(* Helper to build a ProperTerm for the inr constructor *)
Program Definition proper_inr {ctx} {A} {B}
           (x: OTPairInCtx ctx B) : OTPairInCtx ctx (OTSum A B) :=
  map_OTPairInCtx (B:=OTSum A B) (fun y => inr y) _ x.
Next Obligation.
  intros x1 x2 pf_x; assumption.
Qed.

(* Helper to build a ProperTerm for sum elimination *)
Program Definition proper_sum_elim {ctx} {A} {B} {C}
           (x: OTPairInCtx ctx (OTSum A B))
           (f1: OTPairInCtx ctx (OTArrow A C))
           (f2: OTPairInCtx ctx (OTArrow B C))
: OTPairInCtx ctx C :=
  map3_OTPairInCtx (A:=OTSum A B) (B:=OTArrow A C) (C:=OTArrow B C)
                   (fun y g1 g2 => match y with
                                     | inl y1 => g1 y1
                                     | inr y2 => g2 y2
                                   end) _ x f1 f2.
Next Obligation.
  intros sum1 sum2; destruct sum1; destruct sum2;
  intros H g1 g2 pf_g h1 h2 pf_h; destruct H; destruct H0;
  destruct pf_g as [ pf_g1 pf_g2 ]; destruct pf_g2 as [ pf_g2 pf_g3 ];
  destruct pf_h as [ pf_h1 pf_h2 ]; destruct pf_h2 as [ pf_h2 pf_h3 ];
  repeat split;
  first [ apply pf_g1 | apply pf_g2 | apply pf_g3
          | apply pf_h1 | apply pf_h2 | apply pf_h3
          | elimtype False; assumption ];
  repeat split; assumption.
Qed.


(***
 *** Notations
 ***)

Module ProperTermNotations.

  Notation "A '-o>' B" :=
    (OTArrow A B) (right associativity, at level 99).
  Notation "A '*o*' B" :=
    (OTProd A B) (left associativity, at level 40).
  Notation "A '+o+' B" :=
    (OTSum A B) (left associativity, at level 50).

  Delimit Scope pterm_scope with pterm.

  Bind Scope pterm_scope with ProperTerm.

  Notation "'pfun' ( x ::: T ) ==> y" :=
    (proper_fun (A:=T) (fun x => y%pterm))
      (at level 100, right associativity, x at level 99) : pterm_scope.

  Notation "'pvar' x" := (proper_var x) (no associativity, at level 75) : pterm_scope.

  Notation "x @ y" :=
    (proper_apply x y) (right associativity, at level 20) : pterm_scope.

  Notation "( x ,o, y )" :=
    (proper_pair x%pterm y%pterm)
      (no associativity, at level 0) : pterm_scope.
  Notation "'ofst' x" :=
    (proper_proj1 x%pterm) (right associativity, at level 80) : pterm_scope.
  Notation "'osnd' x" :=
    (proper_proj2 x%pterm) (right associativity, at level 80) : pterm_scope.

  Notation "'pinl' ( B ) x" :=
    (proper_inl (B:=B) x) (right associativity, at level 80) : pterm_scope.
  Notation "'pinr' ( A ) x" :=
    (proper_inl (A:=A) x) (right associativity, at level 80) : pterm_scope.
  Notation "'pmatch_sum' x 'with' | 'inl' y1 => z1 | 'inr' y2 => z2 'end'" :=
    (proper_sum_elim x (proper_fun (fun y1 => z1))
                     (proper_fun (fun y2 => z2)))
      (no associativity, at level 0, x at level 100).

  (* NOTE: this notation needs to be in a Program Instance *)
  Notation "'pmap1' ( f ::: A --> B ) x" :=
    (map_OTPairInCtx (A:=A) (B:=B) f _ x)
      (right associativity, at level 80) : pterm_scope.

End ProperTermNotations.


(***
 *** Examples
 ***)

Module ProperTermExamples.

Import ProperTermNotations.

(* Example: the identity on Prop *)
Definition proper_id_Prop_fun : ProperTerm (OTProp -o> OTProp) :=
  pfun ( x ::: OTProp ) ==> pvar x.

(* You can see that it yields the identity function *)
Eval compute in (coerce_proper_term proper_id_Prop_fun : Prop -> Prop).

(* The proof of Proper-ness is automatic by typeclass instances *)
Goal (Proper (OTProp -o> OTProp) proper_id_Prop_fun).
auto with typeclass_instances.
Qed.

(* Example 2: the first projection function on 2 Props *)
Definition proper_proj1_Prop_fun : ProperTerm (OTProp -o> OTProp -o> OTProp) :=
  pfun ( P1 ::: OTProp ) ==>
    pfun ( P2 ::: OTProp ) ==>
      pvar P1.

(* Example 3: apply each of a pair of functions to an argument *)
Definition proper_example3 {A B C} :
  ProperTerm ((A -o> B) *o* (A -o> C) -o> A -o> (B *o* C)) :=
  pfun ( p ::: (A -o> B) *o* (A -o> C)) ==>
    pfun ( x ::: A ) ==>
      (((ofst (pvar p)) @ pvar x) ,o, ((osnd (pvar p)) @ pvar x)).

(* Example 4: match a sum of two A's and return an A *)
Definition proper_example4 {A} :
  ProperTerm (A +o+ A -o> A) :=
  pfun ( sum ::: A +o+ A) ==>
    pmatch_sum (pvar sum) with
      | inl x => pvar x
      | inr y => pvar y
    end.

End ProperTermExamples.
