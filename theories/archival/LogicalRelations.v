Require Export Coq.Program.Tactics.
Require Export Coq.Setoids.Setoid.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Arith.Arith_base.
Require Export Coq.Relations.Relations.


(***
 *** Distinguished Equalities
 ***)

(* A distinguished equality for a given type is an equivalence marked as "the"
equality for that type *)
 Class EqualsOp (A : Type) : Type :=
  equals : A -> A -> Prop.

(* Distinguished equalities must be equivalences *)
 Class Equals (A : Type) `{EqOp:EqualsOp A} : Prop :=
  { equals_equivalence :> Equivalence equals }.

Global Instance Reflexive_equals `{Equals} : Reflexive equals.
Proof.
  apply equals_equivalence.
Qed.


Global Instance Symmetric_equals `{Equals} : Symmetric equals.
Proof.
  apply equals_equivalence.
Qed.

Global Instance Tansitive_equals `{Equals} : Transitive equals.
Proof.
  apply equals_equivalence.
Qed.

Notation "x '==' y" := (equals x y) (at level 80, no associativity).

(***
 *** Equality Instances
 ***)

(* Provable equality can be used as an instance of Equals, but we only give the
definitions here, and do not declare them as instances, in case it is not *the*
distinguished equality of a given type. *)
 Definition Eq_EqualsOp (A:Type) : EqualsOp A := eq.
 Definition Eq_Equals (A:Type) : Equals A (EqOp:=Eq_EqualsOp A).
  repeat constructor; unfold equals, Eq_EqualsOp; auto with typeclass_instances.
Qed.

(* The equality on the unit type is the only thing it could be *)
 Instance Unit_EqualsOp : EqualsOp unit :=
  fun p1 p2 => True.

(* The unit equality is a valid equality *)
 Instance Unit_Equals : Equals unit.
  repeat constructor.
Qed.


(* Equality on pairs = equality on the two components *)
 Instance Pair_EqualsOp (A B: Type)
            {EqOp_A:EqualsOp A} `{EqOp_B:EqualsOp B} : EqualsOp (A*B) :=
  fun p1 p2 => equals (fst p1) (fst p2) /\ equals (snd p1) (snd p2).

(* Pair equality is a valid equality *)
 Instance Pair_Equals (A B: Type)
            `{Eq_A:Equals A} `{Eq_B:Equals B} : Equals (A*B).
  repeat constructor.
  reflexivity.
  reflexivity.
  symmetry; destruct H; assumption.
  symmetry; destruct H; assumption.
  destruct H; destruct H0; transitivity (fst y); assumption.
  destruct H; destruct H0; transitivity (snd y); assumption.
Qed.


(* Equality on sums = equality on the two components *)
 Instance Sum_EqualsOp (A B: Type)
            {EqOp_A:EqualsOp A} `{EqOp_B:EqualsOp B} : EqualsOp (A+B) :=
  fun p1 p2 =>
    match p1, p2 with
      | inl x1, inl x2 => x1 == x2
      | inr y1, inr y2 => y1 == y2
      | _, _ => False
    end.

(* Pair equality is a valid equality *)
 Instance Sum_Equals (A B: Type)
            `{Eq_A:Equals A} `{Eq_B:Equals B} : Equals (A+B).
  repeat constructor; unfold equals, Sum_EqualsOp; intro; intros.
  destruct x; reflexivity.
  destruct x; destruct y; try symmetry; assumption.
  destruct x; destruct y; destruct z; try assumption.
  transitivity a0; assumption.
  elimtype False; assumption.
  elimtype False; assumption.
  transitivity b0; assumption.
Qed.


(***
 *** Distinguished Preorders
 ***)

(* A distinguished preorder is a preorder marked as "the" preorder for a type *)
 Class OrderOp@{c} (A : Type@{c}) : Type :=
  order : A -> A -> Prop.

(* Distinguished preorders must be preorders *)
 Class Order (A : Type) `{OrdOp:OrderOp A} : Prop :=
  { equals_preorder :> PreOrder order }.

Notation "x '<~' y" := (order x y) (at level 80, no associativity).


(***
 *** Relating Distinguished Preorders and Equalities
 ***)

(* If we have a distinguished preorder on a type, we want its distinguished
equality to be the one that is induced by that preorder. Note: we give this a
low priority, however, to favor other equality constructions. *)
 Instance Order_EqualsOp `{OrderOp} : EqualsOp A | 5 :=
  fun x y => order x y /\ order y x.
 Instance Order_Equals `{Order} : Equals A | 5.
repeat constructor.
reflexivity.
reflexivity.
destruct H0; assumption.
destruct H0; assumption.
destruct H0; destruct H1; transitivity y; assumption.
destruct H0; destruct H1; transitivity y; assumption.
Qed.

(* Similarly, an equality can be used as a preorder, but we don't generally want
this to be *the* preorder of a type *)
 Definition OrderOp_of_EqualsOp `{EqualsOp} : OrderOp A := equals.
 Definition Order_of_Equals `{Equals} : @Order A (OrderOp_of_EqualsOp).
repeat constructor; auto with typeclass_instances.
Qed.


(***
 *** Order Instances
 ***)

(* Provable equality can be used as an instance of Order, but we only give the
definitions here, and do not declare them as instances, in case it is not *the*
distinguished preorder of a given type. *)
 Definition Eq_OrderOp (A:Type) : OrderOp A := eq.
 Definition Eq_Order (A:Type) : Order A (OrdOp:=Eq_OrderOp A).
  repeat constructor; unfold order, Eq_OrderOp; auto with typeclass_instances.
Qed.

(* The preorder on the unit type is the only thing it could be *)
 Instance Unit_OrderOp : OrderOp unit :=
  fun p1 p2 => True.

(* The unit preorder is a valid preorder *)
 Instance Unit_Order : Order unit.
  repeat constructor.
Qed.


(* The ordering on pairs = ordering on the two components *)
 Instance Pair_OrderOp (A B: Type)
            {OrdOp_A:OrderOp A} `{OrdOp_B:OrderOp B} : OrderOp (A*B) :=
  fun p1 p2 => order (fst p1) (fst p2) /\ order (snd p1) (snd p2).

(* Pair equality is a valid equality *)
 Instance Pair_Order (A B: Type)
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
 Class LogRelOp@{c} (A B : Type@{c}) : Type :=
  relLR : A -> B -> Prop.

(* The propositional part of a logical relation *)
 Class LogRel@{c} (A B : Type@{c})
            `{OrdA:Order A} `{OrdB:Order B} `{LR:LogRelOp A B} : Prop :=
  { logrel_proper :> Proper (order ==> order ==> iff) (relLR (A:=A) (B:=B)) }.

(* Notation "x '~~' y" := (relLR x y) (at level 80, no associativity). *)


(* equals respects itself *)
(* FIXME: this is probably not needed...? *)
(*
 Instance equals_proper `{LogRel} :
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
 Instance LogRelOp_Id (A: Type) `{EqualsOp A} : LogRelOp A A :=
  equals.

 Instance LogRel_Id (A: Type) `{Equals A} : LogRel A A.
constructor; intros x1 x2 ex y1 y2 ey.
rewrite ex; rewrite ey; reflexivity.
Qed.

(* The logical relation for pairs: relate the components pointwise *)
 Instance LogRelOp_Pair (A1 A2 B1 B2: Type)
            `{LogRelOp A1 B1} `{LogRelOp A2 B2} : LogRelOp (A1*A2) (B1*B2) :=
  fun p1 p2 => fst p1 ~~ fst p2 /\ snd p1 ~~ snd p2.

~ Instance LogRel_Pair (A1 A2 B1 B2: Type)
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
