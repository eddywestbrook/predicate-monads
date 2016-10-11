(***
 *** Semi Pre-Orders
 ***)

Require Export Coq.Program.Basics.
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
 *** Some tactics and Proper instances for logical relations
 ***)

(* Tactic to apply semi-reflexivity to goals x <~ x if there is an assumption
with the form x <~ y or y <~ x *)
Ltac assumption_semi_refl :=
  match goal with
  | H : ?x <~ ?y |- ?x <~ ?x => apply (semi_reflexivity_l _ _ H)
  | H : ?y <~ ?x |- ?x <~ ?x => apply (semi_reflexivity_r _ _ H)
  | H : ?x ~~ ?y |- ?x <~ ?x => destruct H; assumption_semi_refl
  | H : ?y ~~ ?x |- ?x <~ ?x => destruct H; assumption_semi_refl
  | H : ?x ~~ ?y |- ?x ~~ ?x => apply (semi_reflexivity_l _ _ H)
  | H : ?y ~~ ?x |- ?x ~~ ?x => apply (semi_reflexivity_r _ _ H)
  (*
  | |- ?f ?z <~ ?f ?z =>
    apply semi_reflexivity_apply_Proper_leq; semi_reflexivity
  | |- ?f ?z ~~ ?f ?z =>
    apply semi_reflexivity_apply_Proper_eq; semi_reflexivity
  | |- ?R ?f ?f =>
    change (Proper R f); eauto with typeclass_instances
   *)
  end.


(* Tactic to apply transitivity to goals x <~ z if there is an assumption with
the form x <~ y or y <~ z *)
Ltac apply_transitivity :=
  lazymatch goal with
  | H : ?x <~ ?y |- ?x <~ ?z => apply (transitivity H); try assumption
  | H : ?y <~ ?z |- ?x <~ ?z => apply (transitivity (y:=?y)); try assumption
  end.


(* Rewrite using an lr_leq or lr_eq assumption *)
Ltac rewrite_assumption :=
  match goal with
  | H : ?x <~ ?y |- ?u <~ ?v => rewrite <- H
  | H : ?x ~~ ?y |- ?u ~~ ?v => rewrite H
  end.


(* FIXME HERE: not sure if these Proper instances are needed... *)

Instance lr_leq_Proper `{LR} : Proper (flip lr_leq ==> lr_leq ==> impl) lr_leq.
Proof.
  intros x1 y1 R1 x2 y2 R2 R12. rewrite <- R1. rewrite <- R2. assumption.
Qed.

Instance lr_leq_Proper_flip `{LR} : Proper (lr_leq ==> flip lr_leq ==> flip impl) lr_leq.
Proof.
  intros x1 y1 R1 x2 y2 R2 R12. rewrite R1. rewrite R2. assumption.
Qed.

Instance lr_leq_Proper_proj1 `{LR} x : Proper (lr_leq ==> impl) (lr_leq x).
Proof.
  intros y1 y2 Ry. rewrite Ry. reflexivity.
Qed.

Instance lr_leq_Proper_proj1_flip `{LR} x :
  Proper (lr_leq --> flip impl) (lr_leq x).
Proof.
  intros y1 y2 Ry. rewrite Ry. reflexivity.
Qed.

Instance lr_eq_Proper `{LR} : Proper (lr_eq ==> lr_eq ==> iff) lr_eq.
Proof.
  intros x1 y1 R1 x2 y2 R2; split; intro Rx.
  + rewrite <- R1. rewrite <- R2. assumption.
  + rewrite R1. rewrite R2. assumption.
Qed.


(* FIXME HERE: not sure if these subrelations are used... *)

(* lr_eq is a sub-relation of lr_leq *)
Instance subrelation_lr_eq_lr_leq `{LR} : subrelation lr_eq lr_leq.
Proof.
  intros x y Rxy; destruct Rxy; assumption.
Qed.

(* lr_eq is a sub-relation of the inverse of lr_leq *)
Instance subrelation_lr_eq_flip_lr_leq `{LR} : subrelation lr_eq (flip lr_leq).
Proof.
  intros x y Rxy; destruct Rxy; assumption.
Qed.


(* FIXME HERE: not sure if these Proper lemmas are used... *)

(* Any function that is Proper w.r.t. (lr_leq ==> lr_leq) also Proper
w.r.t. (lr_eq ==> lr_eq) *)
Instance Proper_lr_leq_lr_eq_unary {A B} `{LR A} `{LR B} (f:A -> B)
         `{P:Proper _ (lr_leq ==> lr_leq) f} : Proper (lr_eq ==> lr_eq) f.
Proof.
  intros x y Rxy; destruct Rxy; split; apply P; assumption.
Qed.

(* Similar to the above, but for binary functions *)
Instance Proper_lr_leq_lr_eq_binary {A B C} `{LR A} `{LR B} `{LR C}
         (f:A -> B -> C)
         `{P:Proper _ (lr_leq ==> lr_leq ==> lr_leq) f} :
  Proper (lr_eq ==> lr_eq ==> lr_eq) f.
Proof.
  intros x1 y1 Rxy1 x2 y2 Rxy2; destruct Rxy1; destruct Rxy2;
    split; apply P; assumption.
Qed.

(* Similar to the above, but for trinary functions *)
Instance Proper_lr_leq_lr_eq_trinary {A B C D} `{LR A} `{LR B} `{LR C} `{LR D}
         (f:A -> B -> C -> D)
         `{P:Proper _ (lr_leq ==> lr_leq ==> lr_leq ==> lr_leq) f} :
  Proper (lr_eq ==> lr_eq ==> lr_eq ==> lr_eq) f.
Proof.
  intros x1 y1 Rxy1 x2 y2 Rxy2 x3 y3 Rxy3;
    destruct Rxy1; destruct Rxy2; destruct Rxy3;
    split; apply P; assumption.
Qed.


(***
 *** Logical Relation for Common Types
 ***)

(* The LR for functions is the pointwise relation on all the outputs, restricted
so to only relate proper functions *)
Record LRFun {A B} `{LR_Op A} `{LR_Op B} (f g : A -> B) : Prop :=
  {
    LRFun_Proper_l : Proper (lr_leq ==> lr_leq) f;
    LRFun_Proper_r : Proper (lr_leq ==> lr_leq) g;
    apply_lr_leq : forall x y, x <~ y -> f x <~ g y
  }.

(* Make LRFun itself an instance of LR_Op *)
Instance LR_Op_fun {A B} `{LR_Op A} `{LR_Op B} : LR_Op (A -> B) := LRFun.

(* LR instance for functions *)
Instance LR_fun {A B} `{LR A} `{LR B} : LR (A -> B).
Proof.
  constructor; constructor.
  { constructor; intros f g Rfg; destruct Rfg as [ Pf Pg Rfg ]; constructor;
      intros x y Rxy; first [ apply Pf | apply Pg | apply Rfg ]; assumption. }
  { intros f g h Rfg Rgh; destruct Rfg as [ Pf Pg Rfg ];
      destruct Rgh as [ Pg' Ph Rgh ]; constructor; intros x y Rxy.
    - apply Pf; assumption.
    - apply Ph; assumption.
    - transitivity (g x).
      + apply Rfg; assumption_semi_refl.
      + apply Rgh; assumption. }
Qed.

(* Elimination principle for proving ~~ from functions *)
Lemma apply_lr_eq {A B} `{LR_Op A} `{LR_Op B} (f g : A -> B) :
  f ~~ g -> forall x y, x ~~ y -> f x ~~ g y.
  intros Rfg x y Rxy; destruct Rfg as [ Rfg1 Rfg2 ]; destruct Rxy; split;
    [ apply Rfg1 | apply Rfg2 ]; assumption.
Qed.


(* The LR for pairs is just the pointwise relation on the components *)
Record LRPair {A B} `{LR_Op A} `{LR_Op B} (p1 p2 : A * B) : Prop :=
  { LRPair_fst : fst p1 <~ fst p2;
    LRPair_snd : snd p1 <~ snd p2
  }.

(* Make LRPair itself an instance of LR_Op *)
Instance LR_Op_pair {A B} `{LR_Op A} `{LR_Op B} : LR_Op (A * B) := LRPair.

(* Prove the LR instance for LRPair *)
Instance LR_pair {A B} `{LR A} `{LR B} : LR (A * B).
Proof.
  constructor; constructor.
  { constructor; intros p1 p2 R12; destruct R12; split; assumption_semi_refl. }
  { intros p1 p2 p3 R12 R23; destruct R12; destruct R23; split;
      [ transitivity (fst p2) | transitivity (snd p2) ]; assumption. }
Qed.

(* fst is a Proper morphism *)
Instance Proper_LRPair_fst {A B} `{LR_Op A} `{LR_Op B} :
  Proper lr_leq (fst : (A*B) -> A).
Proof.
  split; intros p1 p2 Rp; destruct Rp; assumption.
Qed.

(* snd is a Proper morphism *)
Instance Proper_LRPair_snd {A B} `{LR_Op A} `{LR_Op B} :
  Proper lr_leq (snd : (A*B) -> B).
Proof.
  split; intros p1 p2 Rp; destruct Rp; assumption.
Qed.

(* pair is a Proper morphism *)
Instance Proper_LRPair_pair {A B} `{LR A} `{LR B} :
  Proper lr_leq (pair : A -> B -> A*B).
Proof.
  split; intros x1 y1 Rxy1; split; intros x2 y2 Rxy2; split; unfold fst, snd;
    try assumption; try assumption_semi_refl.
Qed.


(* The LR for the unit type is the obvious one *)
Definition LRUnit : relation unit := fun _ _ => True.
Instance LR_Op_unit : LR_Op unit := LRUnit.

Instance LR_unit : LR unit.
Proof.
  repeat constructor.
Qed.


(***
 *** Automation
 ***)

(* Tactic to prove things like (f x y) <~ (f' x' y') and (f x y) ~~ (f' x' y')
 by reducing them to f <~ f', x <~ x', and y <~ y' (or similar with ~~ in place
 of <~).  This is similar to (and the code is adapted from) the f_equiv tactic
 in Coq.Classes.Morphisms, except that we do not use rewriting or reflexivity
 because lr_leq and lr_eq are not necessarily reflexive. *)
Ltac prove_lr :=
  match goal with
  | |- (?f _) <~ (?g _) => apply apply_lr_leq; [ change (f <~ g) | ]; prove_lr
  | |- (?f _) ~~ (?g _) => apply apply_lr_eq; prove_lr
  | |- ?f <~ ?g =>
    first [ change (Proper lr_leq f); solve [ eauto with typeclass_instances ]
          | change (f <~ f); assumption_semi_refl
          | assumption
          | idtac ]
  | |- ?f ~~ ?g =>
    first [ change (Proper lr_eq f); solve [ eauto with typeclass_instances ]
          | split; change (Proper lr_leq f);
            solve [ eauto with typeclass_instances ]
          | change (f ~~ f); assumption_semi_refl
          | assumption
          | idtac ]
 end.


(* To prove a function is Proper w.r.t. lr_leq, we only need to prove it is
Proper w.r.t. (lr_leq ==> lr_leq). Note that we do *not* make this an Instance,
since this is only for use in the lr_prove_proper tactic, below. *)
Lemma fun_Proper_lr_leq {A B} `{LR A} `{LR B} (f: A -> B) :
  Proper (lr_leq ==> lr_leq) f -> Proper lr_leq f.
  intro Rf; constructor; assumption.
Qed.

(* Helper lemma for the lr_prove_proper tactic *)
Lemma fun_Proper_lr_leq_adjoint {A B C} `{LR A} `{LR B} `{LR C} (f: A -> B -> C) :
  Proper (lr_leq ==> lr_leq) (fun p => let (x,y) := p : A*B in f x y) ->
  Proper (lr_leq ==> lr_leq) f.
  intros Pf x1 y1 Rxy1; constructor; intros x2 y2 Rxy2;
    (lazymatch goal with
     | |- f ?x1 ?x2 <~ f ?y1 ?y2 => apply (Pf (x1,x2) (y1,y2))
     end); split; prove_lr.
Qed.

(* Helper lemma for the lr_prove_proper tactic *)
Lemma fun_Proper_arrow_pair_commute {A B C D} `{LR A} `{LR B} `{LR C} RD
      (f: A * (B * C) -> D) :
  Proper (lr_leq ==> RD) (fun (p:(A * B) * C) =>
                            match p with ((x,y),z) => f (x,(y,z)) end) ->
  Proper (lr_leq ==> RD) f.
  intros Pf p1 p2 Rp; destruct p1 as [ x1 p1 ]; destruct p1 as [ y1 z1 ];
    destruct p2 as [ x2 p2 ]; destruct p2 as [ y2 z2 ];
      destruct Rp as [ Rx Rp ]; destruct Rp.
  apply (Pf (x1, y1, z1) (x2, y2, z2)).
  repeat split; unfold fst, snd in * |- *; assumption.
Qed.

(* Helper lemma for the lr_prove_proper tactic *)
Lemma fun_Proper_arrow_adjoint {A B C} `{LR A} `{LR B} RC (f: A * B -> C) :
  Proper (lr_leq ==> (lr_leq ==> RC)) (fun x y => f (x,y)) ->
  Proper (lr_leq ==> RC) f.
  intros Pf p1 p2 Rp; destruct p1; destruct p2; destruct Rp; apply Pf;
    unfold fst, snd in * |- *; assumption.
Qed.

(* Tactic to prove Proper lr_leq f from Proper (lr_leq ==> ... ==> lr_leq) f *)
Ltac prove_lr_proper :=
  repeat (first [ solve [ eauto with typeclass_instances ]
                | progress (apply fun_Proper_lr_leq)
                | apply fun_Proper_lr_leq_adjoint
                | apply fun_Proper_arrow_pair_commute
                | apply fun_Proper_arrow_adjoint
                | repeat (intro; intros); prove_lr ]).
