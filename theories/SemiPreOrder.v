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
  {
    semi_reflexivity_l : forall (x y : A), R x y -> R x x;
    semi_reflexivity_r : forall (x y : A), R x y -> R y y
  }.

Theorem semi_reflexivity `{SemiReflexive} (x y : A) : R x y \/ R y x -> R x x.
  intro hypR; destruct hypR.
  + apply (semi_reflexivity_l _ y); assumption.
  + apply (semi_reflexivity_r y); assumption.
Qed.

(* A Semi-PreOrder is a pre-order just on the field of the relation *)
Class SemiPreOrder (R : relation A) : Prop :=
  {
    SemiPreOrder_SemiReflexive :> SemiReflexive R | 2 ;
    SemiPreOrder_Transitive :> Transitive R | 2
  }.

(* A PreOrder is always a Semi-PreOrder *)
Global Instance PreOrder_SemiPreOrder {R} `{@PreOrder A R} : SemiPreOrder R.
destruct H; constructor; [ | assumption ].
constructor; intros x y H1; reflexivity.
Qed.

(* A PER is always a Semi-PreOrder *)
Global Instance PER_SemiPreOrder {R} `{@PER A R} : SemiPreOrder R.
destruct H; constructor; [ | assumption ].
constructor; intros x y H1; [ transitivity y | transitivity x ];
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
  + intros x y z Rxy Ryz; destruct Rxy; destruct Ryz;
      split; transitivity y; assumption.
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
 *** Automation for proving terms are related by a logical relation
 ***)

Create HintDb LR.

(* Tactic to apply semi-reflexivity to goals x <~ x if there is an assumption
with the form x <~ y or y <~ x *)
Ltac apply_semi_reflexivity :=
  lazymatch goal with
  | H : ?x <~ ?y |- ?x <~ ?x => apply (semi_reflexivity_l _ _ H)
  | H : ?y <~ ?x |- ?x <~ ?x => apply (semi_reflexivity_r _ _ H)
  end.

Hint Extern 1 (?x <~ ?x) => apply_semi_reflexivity : LR.

(* Tactic to apply transitivity to goals x <~ z if there is an assumption with
the form x <~ y or y <~ z *)
Ltac apply_transitivity :=
  lazymatch goal with
  | H : ?x <~ ?y |- ?x <~ ?z => apply (transitivity H); try assumption
  | H : ?y <~ ?z |- ?x <~ ?z => apply (transitivity (y:=?y)); try assumption
  end.

Hint Extern 1 (?x <~ ?z) => apply_transitivity : LR.

(* Hint to prove proper-ness of functions *)
Ltac prove_proper_fun :=
  let x := fresh "x" in
  let y := fresh "y" in
  let H := fresh "H" in
  intros x y H.

Hint Extern 1 (Proper (?R1 ==> ?R2) ?f) => prove_proper_fun : LR.

Hint Extern 1 (?x ~~ ?y) => split : LR.


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
  constructor; intros p1 p2 R12; split; destruct R12; auto with LR.
  intros p1 p2 p3 R12 R23; destruct R12; destruct R23; split; auto with LR.
Qed.

(* The LR for functions is the pointwise relation on all the outputs, restricted
so to only relate proper functions *)
Instance LR_Op_fun {A B} `{LR_Op A} `{LR_Op B} : LR_Op (A -> B) :=
  fun f g =>
    forall x y, x <~ y -> f x <~ f y /\ g x <~ g y /\ f x <~ g y.

Instance LR_fun {A B} `{LR A} `{LR B} : LR (A -> B).
Proof.
  constructor; constructor.
  { constructor; intros f g Rfg x y Rxy;
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

(* Tactic for eliminating a relation on functions *)
Ltac elim_lr_fun :=
  lazymatch goal with
  | H : ?f <~ ?g |- ?f ?x <~ ?g ?y => apply H; try assumption
  end.

Hint Extern 1 (?f ?x <~ ?g ?y) => elim_lr_fun : LR.
