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

(* Symmetric closure *)
Definition clos_sym (R:relation A) : relation A :=
  fun x y => R x y \/ R y x.

(* The symmetric closure of any relation is symmetric *)
Global Instance sym_clos_Symmetric {R} : Symmetric (clos_sym R).
intros x y H; destruct H; [ right | left ]; assumption.
Qed.

(* Symmetric-Transitive closure *)
Inductive clos_sym_trans (R:relation A) (x:A) : A -> Prop :=
| st_step (y:A) : R x y -> clos_sym_trans R x y
| st_rstep (y:A) : R y x -> clos_sym_trans R x y
| st_trans (y z:A) : clos_sym_trans R x y -> clos_sym_trans R y z -> clos_sym_trans R x z.

(* The symmetric-transitive closure of a SemiPreOrder is a PER *)
Global Instance SemiPreOrder_sym_clos {R} `{@SemiPreOrder R} : PER (clos_sym_trans R).
destruct H; constructor.
+ intros x y Rxy. induction Rxy.
  - apply st_rstep; assumption.
  - apply st_step; assumption.
  - apply (st_trans _ _ y); assumption.
+ intros x y z Rxy Ryz. apply (st_trans _ _ y); assumption.
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
Definition lr_eq `{LR_Op} : relation A := clos_sym_trans lr_leq.

Notation "x '~~' y" := (lr_eq x y) (at level 80, no associativity).

Instance le_eq_SemiPreOrder `{LR} : SemiPreOrder lr_eq.
Proof. apply PER_SemiPreOrder. Qed.


(***
 *** Pre-Defined Logical Relations
 ***)

(* The logical relation for pairs is just the pointwise relation *)
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
