(***
 *** Semi Pre-Orders
 ***)

Require Export Coq.Program.Tactics.
Require Export Coq.Setoids.Setoid.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Arith.Arith_base.
Require Export Coq.Relations.Relations.
Require Export Coq.Classes.RelationClasses.


Section SemiPreOrder.

Context {A:Type}.

(* Semi-reflexivity: reflexivity on the field of the relation *)
Class SemiReflexive (R : relation A) :=
    semi_reflexivity : forall (x y : A), (R x y \/ R y x) -> R x x.

(* A Semi-PreOrder is a pre-order just on the field of the relation *)
Class SemiPreOrder (R : relation A) : Prop :=
  {
    SemiPreOrder_SemiReflexive :> SemiReflexive R | 2 ;
    SemiPreOrder_Transitive :> Transitive R | 2
  }.

(* A PreOrder is always a Semi-PreOrder *)
Global Instance PreOrder_SemiPreOrder {R} `{@PreOrder A R} : SemiPreOrder R.
destruct H; constructor; [ | assumption ].
intros x y H1; reflexivity.
Qed.

(* A PER is always a Semi-PreOrder *)
Global Instance PER_SemiPreOrder {R} `{@PER A R} : SemiPreOrder R.
destruct H; constructor; [ | assumption ].
intros x y H1; destruct H1; transitivity y;
  try assumption; symmetry; assumption.
Qed.

(* Symmetric intersection: the intersection of a relation and its converse *)
Definition inter_sym (R:relation A) : relation A :=
  fun x y => R x y /\ R y x.

(* The symmetric intersection of any relation is symmetric *)
Global Instance inter_sym_Symmetric {R} : Symmetric (inter_sym R).
intros x y H; destruct H; split; assumption.
Qed.

(* The symmetric intersection of any semi-preorder is a PER *)
Global Instance inter_sym_PER `{SemiPreOrder} : PER (inter_sym R).
Proof.
  constructor.
  + auto with typeclass_instances.
  + intros x y z Rxy Ryz; destruct Rxy; destruct Ryz; split; transitivity y; assumption.
Qed.

End SemiPreOrder.


(***
 *** So-Called Logical Relations
 ***)

(* A "logical relation" is just a distinguished semi-preorder on a type *)
Class LR_Op (A:Type) : Type := lr_leq : relation A.

(* To be valid, a logical relation must actually be a semi-preorder *)
Class LR A `{R:LR_Op A} : Prop :=
  { lr_SemiPreOrder :> @SemiPreOrder A lr_leq }.

Notation "x '<~' y" := (lr_leq x y) (at level 80, no associativity).

(* Helper notation for using the PER associated with a logical relation *)
Definition lr_eq `{LR_Op} : relation A := inter_sym lr_leq.

Notation "x '~~' y" := (lr_eq x y) (at level 80, no associativity).

Instance le_eq_SemiPreOrder `{LR} : SemiPreOrder lr_eq.
Proof. apply PER_SemiPreOrder. Qed.


(***
 *** Pre-Defined Logical Relations
 ***)

(* The LR for pairs is just the pointwise relation on the components *)
Instance LR_Op_pair {A B} `{LR_Op A} `{LR_Op B} : LR_Op (A * B) :=
  fun p1 p2 =>
    lr_leq (fst p1) (fst p2) /\ lr_leq (snd p1) (snd p2).

Instance LR_pair {A B} `{LR A} `{LR B} : LR (A * B).
Proof.
  constructor; constructor.
  intros p1 p2 R12; split; destruct R12; destruct H1;
    first [ apply (semi_reflexivity _ (fst p2)) | apply (semi_reflexivity _ (snd p2)) ];
    first [ left; assumption | right; assumption ].
  intros p1 p2 p3 R12 R23; destruct R12; destruct R23; split;
    [ transitivity (fst p2) | transitivity (snd p2) ]; assumption.
Qed.


(* The LR for functions is the pointwise relation on all the outputs, restricted
so to only relate proper functions *)
Instance LR_Op_fun {A B} `{LR_Op A} `{LR_Op B} : LR_Op (A -> B) :=
  fun f g =>
    forall x y, x <~ y -> f x <~ f y /\ g x <~ g y /\ f x <~ g y.

Instance LR_fun {A B} `{LR A} `{LR B} : LR (A -> B).
Proof.
  constructor; constructor.
  { intros f g Rfg x y Rxy; destruct Rfg as [ Rfg | Rfg ];
      destruct (Rfg x y) as [ Rfg1 Rfg2 ]; try assumption;
        destruct Rfg2 as [ Rfg2 Rfg3 ]; repeat split; assumption. }
  { intros f g h Rfg Rgh x y Rxy; repeat split.
    + destruct (Rfg x y); assumption.
    + destruct (Rgh x y) as [ Rgh1 Rgh2 ]; try assumption; destruct Rgh2; assumption.
    + transitivity (g x).
      - apply Rfg; apply (semi_reflexivity _ y); left; assumption.
      - apply Rgh; assumption. 
  }
Qed.
