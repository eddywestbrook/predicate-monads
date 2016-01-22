
Require Export Coq.Program.Tactics.
Require Export Coq.Setoids.Setoid.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Arith.Arith_base.
Require Export Coq.Relations.Relations.

(***
 *** Distinguished Preorders
 ***)

(* A distinguished preorder is a preorder marked as "the" preorder for a type *)
Polymorphic Class OrderOp@{c} (A : Type@{c}) : Type :=
  order : A -> A -> Prop.

(* Distinguished preorders must be preorders *)
Polymorphic Class Order@{c} (A : Type@{c}) `{OrdOp:OrderOp@{c} A} : Prop :=
  { equals_preorder :> PreOrder order }.

Notation "x '<~' y" := (order x y) (at level 80, no associativity).

(* The distinguished equality for a type is defined by the equivalence relations
of the distinguished preorder for that type *)
Polymorphic Definition equals@{c} {A: Type@{c}} `{OrderOp A} : relation A :=
  fun x y => order x y /\ order y x.

Polymorphic Instance equals_Equivalence (A: Type) `{Order A} : Equivalence equals.
repeat constructor.
reflexivity.
reflexivity.
destruct H0; assumption.
destruct H0; assumption.
destruct H0; destruct H1; transitivity y; assumption.
destruct H0; destruct H1; transitivity y; assumption.
Qed.

Notation "x '==' y" := (equals x y) (at level 80, no associativity).


(***
 *** Order Instances
 ***)

(* Provable equality can be used as an instance of Order, but we only give the
definitions here, and do not declare them as instances, in case it is not *the*
distinguished preorder of a given type. *)
Polymorphic Definition Eq_OrderOp (A:Type) : OrderOp A := eq.
Polymorphic Definition Eq_Order (A:Type) : Order A (OrdOp:=Eq_OrderOp A).
  repeat constructor; unfold order, Eq_OrderOp; auto with typeclass_instances.
Qed.

(* The preorder on the unit type is the only thing it could be *)
Polymorphic Instance Unit_OrderOp : OrderOp unit :=
  fun p1 p2 => True.

(* The unit preorder is a valid preorder *)
Polymorphic Instance Unit_Order : Order unit.
  repeat constructor.
Qed.


(* Equality on pairs = equality on the two components *)
Polymorphic Instance Pair_OrderOp (A B: Type)
            {OrdOp_A:OrderOp A} `{OrdOp_B:OrderOp B} : OrderOp (A*B) :=
  fun p1 p2 => order (fst p1) (fst p2) /\ order (snd p1) (snd p2).

(* Pair equality is a valid equality *)
Polymorphic Instance Pair_Order (A B: Type)
            `{Ord_A:Order A} `{Ord_B:Order B} : Order (A*B).
  repeat constructor.
  reflexivity.
  reflexivity.
  destruct H; destruct H0; transitivity (fst y); assumption.
  destruct H; destruct H0; transitivity (snd y); assumption.
Qed.


(***
 *** Logical Relations
 ***)

(* A logical relation is a relation between two types that respects the
distinguished preorders of those two types; i.e., it is a morphism in the
category of preorders. *)
Polymorphic Class LogRelOp@{c} (A B : Type@{c}) : Type :=
  relLR : A -> B -> Prop.

(* The propositional part of a logical relation *)
Polymorphic Class LogRel@{c} (A B : Type@{c})
            `{OrdA:Order A} `{OrdB:Order B} `{LR:LogRelOp A B} : Prop :=
  { logrel_proper :> Proper (order ==> order ==> iff) (relLR (A:=A) (B:=B)) }.

(* Notation "x '~~' y" := (relLR x y) (at level 80, no associativity). *)


(* equals respects itself *)
(* FIXME: this is probably not needed...? *)
(*
Polymorphic Instance equals_proper `{LogRel} :
  Proper (equals ==> equals ==> iff) equals.
intros x1 x2 ex y1 y2 ey. rewrite ex.
 split; intro exy.
rewrite <- ex; rewrite exy; rewrite ey; reflexivity.
rewrite ex; rewrite exy; rewrite <- ey; reflexivity.
Qed.
*)


(***
 *** Logical Relations
 ***)

(*

(* The identity logical relation, between a type and itself, is just the type's
distinguished equality *)
Polymorphic Instance LogRelOp_Id (A: Type) `{EqualsOp A} : LogRelOp A A :=
  equals.

Polymorphic Instance LogRel_Id (A: Type) `{Equals A} : LogRel A A.
constructor; intros x1 x2 ex y1 y2 ey.
rewrite ex; rewrite ey; reflexivity.
Qed.

(* The logical relation for pairs: relate the components pointwise *)
Polymorphic Instance LogRelOp_Pair (A1 A2 B1 B2: Type)
            `{LogRelOp A1 B1} `{LogRelOp A2 B2} : LogRelOp (A1*A2) (B1*B2) :=
  fun p1 p2 => fst p1 ~~ fst p2 /\ snd p1 ~~ snd p2.

Polymorphic Instance LogRel_Pair (A1 A2 B1 B2: Type)
            `{LogRel A1 B1} `{LogRel A2 B2} : LogRel (A1*A2) (B1*B2).
constructor; intros p1 p1' e1 p2 p2' e2.
destruct e1 as [e1_1 e1_2]; destruct e2 as [e2_1 e2_2].
destruct p1; destruct p1'; destruct p2; destruct p2'.
split; intro e; destruct e as [e_1 e_2]; split;
unfold fst in * |- *; unfold snd in * |- *.
rewrite <- e1_1; rewrite <- e2_1; assumption.
rewrite <- e1_2; rewrite <- e2_2; assumption.
rewrite e1_1; rewrite e2_1; assumption.
rewrite e1_2; rewrite e2_2; assumption.
Qed.

*)