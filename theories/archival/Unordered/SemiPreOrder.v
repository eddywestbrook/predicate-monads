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
  | |- Proper lr_leq _ => unfold Proper; assumption_semi_refl
  | |- Proper lr_eq _ => unfold Proper; assumption_semi_refl
  | H : ?x <~ ?y |- ?x <~ ?x => apply (semi_reflexivity_l _ _ H)
  | H : ?y <~ ?x |- ?x <~ ?x => apply (semi_reflexivity_r _ _ H)
  | H : Proper lr_leq ?x |- ?x <~ ?x => apply H
  | H : ?x ~~ ?y |- ?x <~ ?x => destruct H; assumption_semi_refl
  | H : ?y ~~ ?x |- ?x <~ ?x => destruct H; assumption_semi_refl
  | H : ?x ~~ ?y |- ?x ~~ ?x => apply (semi_reflexivity_l _ _ H)
  | H : ?y ~~ ?x |- ?x ~~ ?x => apply (semi_reflexivity_r _ _ H)
  | H : Proper lr_leq ?x |- ?x ~~ ?x => split; apply H
  | H : Proper lr_eq ?x |- ?x ~~ ?x => apply H
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
 *** The Logical Relation for Functions
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

(* LRFun itself is Proper w.r.t. subrelations in the second argument *)
Instance LRFun_Proper_subrelation {A B} `{LR_Op A} :
  Proper (subrelation ==> subrelation) (@LR_Op_fun A B _).
Proof.
  intros R1 R2 subR f g Rfg; destruct Rfg as [Pf Pg Rfg].
  split; intros x y Rxy; apply subR;
    first [ apply Pf | apply Pg | apply Rfg ]; assumption.
Qed.


(* Elimination principle for proving ~~ from functions *)
Lemma apply_lr_eq {A B} `{LR_Op A} `{LR_Op B} (f g : A -> B) :
  f ~~ g -> forall x y, x ~~ y -> f x ~~ g y.
  intros Rfg x y Rxy; destruct Rfg as [ Rfg1 Rfg2 ]; destruct Rxy; split;
    [ apply Rfg1 | apply Rfg2 ]; assumption.
Qed.


(***
 *** The Logical Relation for Pairs
 ***)

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

(* LRPair itself is Proper w.r.t. subrelations *)
Instance LRPair_Proper_subrelation {A B} :
  Proper (subrelation ==> subrelation ==> subrelation) (@LR_Op_pair A B).
Proof.
  intros R1 R2 subR S1 S2 subS p1 p2 Rp; destruct Rp.
  split; first [ apply subR | apply subS ]; assumption.
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

(* Eta rule for pairs *)
Lemma LRPair_eta {A B} `{LR A} `{LR B} (p : A*B) : p <~ p -> (fst p, snd p) ~~ p.
  intro Rp; destruct p; split; assumption.
Qed.
Hint Rewrite @LRPair_eta : LR.


(***
 *** Automation (which uses the LRs for functions and pairs)
 ***)

(* Helper tactic for prove_lr: proves f <~ g by the Build_LRFun constructor *)
Ltac build_lr_fun :=
  let x := fresh "x" in
  let y := fresh "y" in
  let Rxy := fresh "Rxy" in
  apply Build_LRFun; intros x y Rxy.

(* Tactic to prove things like (f x y) <~ (f' x' y') and (f x y) ~~ (f' x' y')
 by reducing them to f <~ f', x <~ x', and y <~ y' (or similar with ~~ in place
 of <~).  This is similar to (and the code is adapted from) the f_equiv tactic
 in Coq.Classes.Morphisms, except that we do not use rewriting or reflexivity
 because lr_leq and lr_eq are not necessarily reflexive. *)
Ltac prove_lr :=
  (* autorewrite with LR; *)
  repeat (simpl; rewrite_strat (topdown (hints LR)));
  match goal with
  | |- (?f _) <~ (?g _) => apply apply_lr_leq; [ change (f <~ g) | ]; prove_lr
  | |- (?f _) ~~ (?g _) => apply apply_lr_eq; prove_lr
  | |- (fun _ => _) <~ _ => build_lr_fun; prove_lr
  | |- _ <~ (fun _ => _) => build_lr_fun; prove_lr
  | |- (fun _ => _) ~~ _ => split; build_lr_fun; prove_lr
  | |- _ ~~ (fun _ => _) => split; build_lr_fun; prove_lr
  | |- ?f <~ ?g =>
    first [ change (Proper lr_leq f);
            solve [ assumption | auto with typeclass_instances ]
          | change (f <~ f); assumption_semi_refl
          | assumption ]
  | |- ?f ~~ ?g =>
    first [ change (Proper lr_eq f);
            solve [ assumption | auto with typeclass_instances ]
          | split; change (Proper lr_leq f);
            solve [ auto with typeclass_instances ]
          | change (f ~~ f); assumption_semi_refl
          | assumption ]
  | |- Proper lr_leq _ => unfold Proper; prove_lr
  | |- _ => first [ assumption | auto with typeclass_instances ]
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
  lazymatch goal with
  | |- Proper lr_leq ?f =>
    first [ solve [ auto with typeclass_instances ]
          | progress (apply fun_Proper_lr_leq); prove_lr_proper
          | unfold Proper; prove_lr ]
  | |- Proper (lr_leq ==> _) ?f =>
    first [ apply fun_Proper_lr_leq_adjoint; prove_lr_proper
          | apply fun_Proper_arrow_pair_commute; prove_lr_proper
          | apply fun_Proper_arrow_adjoint; prove_lr_proper
          | repeat (intro; intros); prove_lr ]
  | |- _ => idtac
  end.


(***
 *** The Discrete Logical Relation
 ***)

(* The discrete LR for a type A, making every element of A related to itself and
nothing else; this is the same as Liebniz equality *)
Definition LRDiscrete {A} : relation A := eq.

(* LRDiscrete is a valid LR. Note that we do not make this an Instance, since we
do not want Coq using this unless we tell it to. *)
Lemma LR_LRDiscrete {A} : @LR A LRDiscrete.
  repeat constructor.
  intros x y z Rxy Ryz; transitivity y; assumption.
Qed.

(* In the discrete LR, everything is related to itself. Again, we do not make
this an Instance, so that Coq doesn't use it unless we tell it to. *)
Lemma Proper_LRDiscrete_any {A} (a:A) : Proper (lr_leq (LR_Op:= LRDiscrete)) a.
  reflexivity.
Qed.

(* The LR for the unit type is the discrete one *)
Instance LR_Op_unit : LR_Op unit := LRDiscrete.
Instance LR_unit : LR unit := LR_LRDiscrete.
Instance Proper_LR_unit_tt : Proper lr_leq tt := Proper_LRDiscrete_any tt.

(* The LR for bool is also the discrete one *)
Instance LR_Op_bool : LR_Op bool := LRDiscrete.
Instance LR_bool : LR bool := LR_LRDiscrete.
Instance Proper_LR_bool_any b : Proper lr_leq b := Proper_LRDiscrete_any b.

(* We want prove_lr, below, to always replace pattern-matches, including if,
with applications of an elimination combinator that we prove once and for all is
Proper. This is the version of that for bool. *)
Definition elimBool {A} (b:bool) (x y:A) := if b then x else y.

Instance Proper_elimBool `{LR} : Proper lr_leq elimBool.
Proof.
 unfold elimBool; prove_lr_proper. rewrite H0; destruct y; assumption.
Qed.

Lemma rewrite_if_elimBool `{LR} (b:bool) x y :
  Proper lr_leq x -> Proper lr_leq y ->
  (if b then x else y) ~~ elimBool b x y.
  intros Px Py; destruct b; unfold elimBool; assumption_semi_refl.
Qed.

Hint Rewrite @rewrite_if_elimBool : LR.


(***
 *** The Logical Relation for Prop
 ***)

(* P1 <~ P2 is defined as P1 -> P2 *)
Instance LR_Op_Prop : LR_Op Prop := impl.

Instance LR_Prop : LR Prop.
Proof.
  constructor; apply @PreOrder_SemiPreOrder; constructor;
    auto with typeclass_instances.
Qed.
