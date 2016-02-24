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

(* An element of an ordered type has to be proper *)
(*
Definition OTElem (A:OrderedType) : Type :=
  {x:ot_Type A | ot_R A x x}.
 *)

(*
Inductive OTElem (A:OrderedType) : Type :=
| mkOTElem (x:ot_Type A) (pf:ot_R A x x).
*)

(* OTElem is how we view an OrderedType as a type *)
(* Coercion OTElem : OrderedType >-> Sortclass. *)


(***
 *** Commonly-Used Ordered Types
 ***)

Program Definition OTProp : OrderedType :=
  {|
    ot_Type := Prop;
    ot_R := iff;
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

(*
constructor.
{ intro f; intros. apply (proj2_sig f). assumption. }
{ intros f g h; intros.
  apply (PreOrder_Transitive (PreOrder:=B) _ (proj1_sig g y)).
  + apply H; assumption.
  + apply H0; apply (PreOrder_Reflexive (PreOrder:=A) y). }
Qed.
*)

(* FIXME: do product and sum types *)
(* FIXME: also need notations *)

(* FIXME: could also do a forall type, but need the second type argument, B, to
itself be proper, i.e., to be an element of OTArrow A OType. Would also need a
dependent version of OTContext, below. *)



(***
 *** Types-in-Context
 ***)

Definition OTContext := list OrderedType.

Fixpoint ctx_elem (ctx:OTContext) : Type :=
  match ctx with
  | [] => unit
  | A::ctx' => (ot_Type A) * (ctx_elem ctx')
  end.

Fixpoint ctx_elem_lt (ctx:OTContext) : relation (ctx_elem ctx) :=
  match ctx with
  | [] => fun _ _ => True
  | A::ctx' => fun e1 e2 =>
                 validR (ot_R A) (fst e1) (fst e2) /\
                 ctx_elem_lt ctx' (snd e1) (snd e2)
  end.

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

Definition OTInCtx (ctx:OTContext) (A:OrderedType) : OrderedType :=
  OTArrow (OTCtxElem ctx) A.


(***
 *** Pairs of Related Elements
 ***)

(* Pairs of terms-in-context that are valid and related to each other *)
Inductive OTPair ctx A : Type :=
  mkOTPair (x1: ctx_elem ctx -> ot_Type A)
           (x2: ctx_elem ctx -> ot_Type A)
           (pf: validR (ot_R (OTInCtx ctx A)) x1 x2) :
    OTPair ctx A.

(* OTPairs in the empty context can be coerced to OTElems *)
Definition ot_pair_to_elem {A} (p: OTPair [] A) : ot_Type A :=
  match p with
  | mkOTPair _ _ x1 x2 pf => x1 tt
  end.

(* FIXME: does not satisfy the uniform inheritance condition... *)
Coercion ot_pair_to_elem : OTPair >-> ot_Type.

(* Any OTPair is always Proper *)
Instance ot_pair_proper {A} (p:OTPair [] A) :
  Proper (ot_R A) (ot_pair_to_elem p).
destruct p; unfold ot_pair_to_elem. destruct pf; apply H.
repeat split.
Qed.

(* Weakening for OTContexts: captures that ctx2 is an extension of ctx1 by
saying that any object in ctx1 can be translated to ctx2 *)
Class OTCtxExtends ctx1 ctx2 : Type :=
  weaken_context :
    forall {A}, (ctx_elem ctx1 -> ot_Type A) ->
                ctx_elem ctx2 -> ot_Type A.

(* The rules for context extension, as type class instances *)
Instance OTCtxExtends_base ctx : OTCtxExtends ctx ctx :=
  fun {A} elem => elem.

Instance OTCtxExtends_cons_both ctx1 ctx2
         {ext:OTCtxExtends ctx1 ctx2} {B}
  : OTCtxExtends (B::ctx1) (B::ctx2) :=
  fun {A} elem ctx_elem =>
    let (celem1, ctx_elem') := ctx_elem in
    (ext _ (fun ctx_elem'' => elem (celem1, ctx_elem''))) ctx_elem'.

Instance OTCtxExtends_cons_right ctx1 ctx2
         {ext:OTCtxExtends ctx1 ctx2} {B}
  : OTCtxExtends ctx1 (B::ctx2) :=
  fun {A} elem ctx_elem =>
    let (_, ctx_elem') := ctx_elem in
    (ext _ elem) ctx_elem'.


(***
 *** Builders for Proper Terms using OTPair
 ***)

Program Definition proper_var ctx A : OTPair (A::ctx) A :=
  mkOTPair (A::ctx) A
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

Program Definition proper_fun {ctx} {A} {B}
        (f: (forall {ctx'} `{ext: OTCtxExtends (A::ctx) ctx'}, OTPair ctx' A) ->
            OTPair (A::ctx) B) :
  OTPair ctx (OTArrow A B) :=
  let (y1,y2,pf_y) :=
      f (fun {ctx'} {ext} =>
           let (x1,x2,pf_x) := proper_var ctx A in
           mkOTPair _ _ (weaken_context x1)
                    (weaken_context x2)
                    _)
  in
  mkOTPair _ _ (fun ctx_elem x => y1 (x,ctx_elem))
           (fun ctx_elem x => y2 (x,ctx_elem)) _.
Next Obligation.
  repeat split; intros.
  { admit. }
  { admit. }
  { admit. }
Admitted.
Next Obligation.
Admitted.


(***
 *** Examples
 ***)

(* Example: the identity on Prop *)
Definition proper_id_Prop_fun : Prop -> Prop :=
  ot_pair_to_elem (proper_fun (A:=OTProp) (fun x => x _ _)).

(* You can see tat it is the identity, and we get an (almost) automatic Proper
proof for it... *)
Eval compute in proper_id_Prop_fun.
Goal (Proper (OTArrow OTProp OTProp) proper_id_Prop_fun).
unfold proper_id_Prop_fun; auto with typeclass_instances.
Qed.

(* Example 2: the first projection function on 2 Props *)
Definition proper_proj1_Prop_fun : Prop -> Prop -> Prop :=
  ot_pair_to_elem
    (proper_fun (A:=OTProp)
                (fun x =>
                   (proper_fun (A:=OTProp) (fun y => x _ _)))).

Eval compute in proper_proj1_Prop_fun.
Goal (Proper (OTArrow OTProp (OTArrow OTProp OTProp)) proper_proj1_Prop_fun).
unfold proper_proj1_Prop_fun; auto with typeclass_instances.
Qed.
