
Require Export Coq.Program.Tactics.
Require Export Coq.Setoids.Setoid.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Arith.Arith_base.
Require Export Coq.Relations.Relations.

(***
 *** Distinguished Equalities
 ***)

(* A distinguished equality is an equality relation marked as "the" equality
relation for a given type *)
Polymorphic Class EqualsOp@{c} (A : Type@{c}) : Type :=
  equals : A -> A -> Prop.

(* Distinguished equalities must be equivalences *)
Polymorphic Class Equals@{c} (A : Type@{c}) `{EqOp:EqualsOp@{c} A} : Prop :=
  { equals_equivalence :> Equivalence equals }.

Notation "x '==' y" := (equals x y) (at level 80, no associativity).


(***
 *** Equality Instances
 ***)

(* Provable equality can be used as an instance of Equals, but we only give the
definitions here, and do not declare them as instances, in case it is not *the*
distinguished equality of a given type. *)
Polymorphic Definition Eq_EqualsOp (A:Type) : EqualsOp A := eq.
Polymorphic Definition Eq_Equals (A:Type) : Equals A (EqOp:=Eq_EqualsOp A).
  repeat constructor; unfold equals, Eq_EqualsOp; auto with typeclass_instances.
Qed.

(* Equality on pairs = equality on the two components *)
Polymorphic Instance Pair_EqualsOp (A B: Type)
            {EqOp_A:EqualsOp A} `{EqOp_B:EqualsOp B} : EqualsOp (A*B) :=
  fun p1 p2 => equals (fst p1) (fst p2) /\ equals (snd p1) (snd p2).

(* Pair equality is a valid equality *)
Polymorphic Instance Pair_Equals (A B: Type)
            `{Eq_A:Equals A} `{Eq_B:Equals B} : Equals (A*B).
  repeat constructor.
  reflexivity.
  reflexivity.
  destruct H; symmetry; assumption.
  destruct H; symmetry; assumption.
  destruct H; destruct H0; transitivity (fst y); assumption.
  destruct H; destruct H0; transitivity (snd y); assumption.
Qed.


(***
 *** Logical Relations
 ***)

(* A logical relation is a relation between two types that respects the
distinguished equalities of those two types; i.e., it is a morphism in the
category of equality relations. *)
Polymorphic Class LogRelOp@{c} (A B : Type@{c}) : Type :=
  relLR : A -> B -> Prop.

(* The propositional part of a logical relation *)
Polymorphic Class LogRel@{c} (A B : Type@{c})
            `{EqA:Equals A} `{EqB:Equals B} `{LR:LogRelOp A B} : Prop :=
  { logrel_proper :> Proper (equals ==> equals ==> iff) (relLR (A:=A) (B:=B)) }.

Notation "x '~~' y" := (relLR x y) (at level 80, no associativity).


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

