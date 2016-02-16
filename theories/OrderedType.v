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
    ot_Type : Type;
    ot_R :> relation ot_Type;
    ot_PreOrder :> SemiTransitive ot_R
  }.

(* An element of an ordered type has to be proper *)
Definition OTElem (A:OrderedType) : Type :=
  {x:ot_Type A | ot_R A x x}.

(*
Inductive OTElem (A:OrderedType) : Type :=
| mkOTElem (x:ot_Type A) (pf:ot_R A x x).
*)

(* OTElem is how we view an OrderedType as a type *)
Coercion OTElem : OrderedType >-> Sortclass.


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
 *** Terms-in-Context
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
                 validR (ot_R A) (fst e1) (fst e1) /\
                 ctx_elem_lt ctx' (snd e1) (snd e2)
  end.

Program Definition OTCtxElem (ctx:OTContext) : OrderedType :=
  {|
    ot_Type := ctx_elem ctx;
    ot_R := ctx_elem_lt ctx;
  |}.
Next Obligation.
induction ctx; constructor.
{ intro ce. apply I. }
{ intro; intros; apply I. }
{ intro ce; split.
  + apply (PreOrder_Reflexive (PreOrder:=a) (fst ce)).
  + apply (PreOrder_Reflexive (PreOrder:=IHctx) (snd ce)). }
{ intros ce1 ce2 ce3; intros. destruct H; destruct H0. split.
  + apply (PreOrder_Transitive (PreOrder:=a) _ (fst ce2)); assumption.
  + apply (PreOrder_Transitive (PreOrder:=IHctx) _ (snd ce2)); assumption. }
Qed.

Definition ctx_nil : ctx_elem [] := tt.

Definition ctx_cons {A:OrderedType} {ctx}
            (x y:A) (r:ot_R A x y) (c:ctx_elem ctx) : ctx_elem (A::ctx) :=
  existT _ x (existT2 _ _ y r c).



Definition OTInCtx (ctx:OTContext) (A:OrderedType) : OrderedType :=
  {|
    ot_Type := 
  |}.
