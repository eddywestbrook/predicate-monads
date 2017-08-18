Require Export Coq.Program.Tactics.
Require Export Coq.Setoids.Setoid.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Arith.Arith_base.
Require Export Coq.Relations.Relations.
Require Export Coq.Lists.List.

Import EqNotations.
Import ListNotations.


(***
 *** Semi-PreOrders
 ***)

(* Semi-reflexivity: reflexivity on the field of the relation *)
Class SemiReflexive {A} (R : relation A) :=
  {
    semi_reflexivity_l : forall (x y : A), R x y -> R x x;
    semi_reflexivity_r : forall (x y : A), R x y -> R y y
  }.

(* A Semi-PreOrder is a pre-order just on the field of the relation *)
Class SemiPreOrder {A} (R : relation A) : Prop :=
  {
    SemiPreOrder_SemiReflexive :> SemiReflexive R | 2 ;
    SemiPreOrder_Transitive :> Transitive R | 2
  }.

(* A PreOrder is always a Semi-PreOrder. We don't make this an Instance because
we don't want Coq always doing these searches for us. *)
Lemma SemiPreOrder_PreOrder A R (H:@PreOrder A R) : SemiPreOrder R.
destruct H; constructor; [ | assumption ].
constructor; intros x y Rxy; reflexivity.
Qed.

(* Tactic to apply semi-reflexivity to goals x <o= x if there is an assumption
with the form x <o= y or y <o= x *)
Ltac assumption_semi_refl :=
  match goal with
  | H : ?R ?x ?y |- ?R ?x ?x => apply (semi_reflexivity_l _ _ H)
  | H : ?R ?x ?y |- ?R ?y ?y => apply (semi_reflexivity_r _ _ H)
  end.


(***
 *** Canonical Relations for Types
 ***)

(* Set the universe levels in OTRelation and OType (was getting some "universe
undefined" errors...) *)
Definition Type0 := Type.

(* An "ordered type relation" is "the" relation for a give type *)
Class OTRelation (A:Type0) : Type := ot_R : relation A.

(* A valid ordered type is a SemiPreOrder *)
Class OType (A:Type0) {RA:OTRelation A} : Prop :=
  {
    SemiPreOrder_OType :> SemiPreOrder RA
  }.

Arguments OTRelation A%type.
Arguments OType A%type {RA}.

Instance SemiReflexive_OType A `{OType A} : SemiReflexive ot_R.
Proof. apply SemiPreOrder_OType. Qed.

Instance Transitive_OType A `{OType A} : Transitive ot_R.
Proof. apply SemiPreOrder_OType. Qed.

(* The equivalence relation for an OrderedType *)
Definition ot_equiv {A} `{OTRelation A} : relation A :=
  fun x y => ot_R x y /\ ot_R y x.

Lemma ot_equiv_PER A `{OType A} : PER _ ot_equiv.
Proof.
  constructor; intro; intros.
  { destruct H0; split; assumption. }
  { destruct H0; destruct H1; split; transitivity y; assumption. }
Qed.

Notation "x <o= y" :=
  (ot_R x y) (no associativity, at level 70).
Notation "x =o= y" :=
  (ot_equiv x y) (no associativity, at level 70).


(***
 *** Definining Some OTypes
 ***)

(* The only ordered type over unit is the discrete one *)
Instance OTunit_R : OTRelation unit := eq.

Instance OTunit : OType unit := Build_OType _ _ (SemiPreOrder_PreOrder _ _ _).

(* The pointwise relation on pairs *)
Instance OTpair_R A B (RA:OTRelation A) (RB:OTRelation B) : OTRelation (A*B) :=
  fun p1 p2 => ot_R (fst p1) (fst p2) /\ ot_R (snd p1) (snd p2).

Instance OTpair A B `(OType A) `(OType B) : OType (A*B).
Proof.
  constructor; split.
  - split; intros x y Rxy; destruct Rxy as [ Rx Ry ]; split;
      assumption_semi_refl.
  - intros p1 p2 p3 R12 R23.
    destruct R12 as [ R12l R12r ]; destruct R23 as [ R23l R23r ].
    split; [ transitivity (fst p2) | transitivity (snd p2) ]; assumption.
Qed.

(* The pointwise relation on functions *)
Instance OTarrow_R A B (RA:OTRelation A) (RB:OTRelation B) : OTRelation (A -> B) :=
  fun f1 f2 =>
    forall a1 a2,
      RA a1 a2 ->
      ot_R (f1 a1) (f2 a2) /\ ot_R (f1 a1) (f1 a2) /\ ot_R (f2 a1) (f2 a2).

Instance OTarrow A B `(OType A) `(OType B) : OType (A -> B).
Proof.
  constructor; split.
  - split; intros f1 f2 Rf a1 a2 Ra; repeat split;
      apply (Rf a1 a2 Ra).
  - intros f1 f2 f3 R12 R23 a1 a2 Ra; repeat split.
    + transitivity (f2 a2); [ apply R12 | try apply R23 ];
        try assumption; assumption_semi_refl.
    + apply R12; assumption.
    + apply R23; assumption.
Qed.

Inductive OExpr : forall A {RA:OTRelation A} (a1 a2:A), Type :=
| Embed {A} {RA:OTRelation A} {a1 a2:A} (Ra:RA a1 a2) :
    @OExpr A RA a1 a2
| App {A B} {RA:OTRelation A} {RB:OTRelation B} {f1 f2 a1 a2}
       (e1: OExpr (A -> B) f1 f2) (e2: OExpr A a1 a2) :
    OExpr B (f1 a1) (f2 a2)
| Lam {A B} {RA:OTRelation A} {RB:OTRelation B} {f1 f2}
      (e: forall (a1 a2:A), RA a1 a2 -> OExpr B (f1 a1) (f2 a2)) :
    OExpr (A -> B) f1 f2
.


FIXME HERE NOW: this is not going to work, because we need to know that
the e in the Lam constructor has all three types:
OExpr B (f1 a1) (f1 a2), OExpr B (f1 a1) (f2 a2), and OExpr B (f2 a1) (f2 a2)!


Definition mkLam {A B} {RA:OTRelation A} {RB:OTRelation B} {f1 f2}
           (f: forall {a1 a2}, OExpr A a1 a2 -> OExpr B (f1 a1) (f2 a2)) :
  OExpr (A -> B) f1 f2 :=
  Lam (fun a1 a2 Ra => f (Embed Ra)).

Definition OConst A {RA:OTRelation A} {a} : Prop :=
  Proper RA a.

Definition ott : @OConst unit _ tt := eq_refl.

Definition opair {A} {RA:OTRelation A} {B} {RB:OTRelation B} :
  @OConst _ _ (pair (A:=A) (B:=B)).
Proof.
  repeat intro; split; assumption.
Qed.

Definition ofst A {RA:OTRelation A} B {RB:OTRelation B} :
  @OConst _ _ (fst (A:=A) (B:=B)).
Proof.
  intros p1 p2 Rp; destruct Rp; assumption.
Qed.


Check (fun A {RA:OTRelation A} => mkLam (fun (_:A) _ x => x)).
Check (mkLam (A:=unit) (fun _ _ x => Embed ott)).
Check (mkLam (A:=unit -> unit) (fun _ _ f => App f (Embed ott))).
Check (mkLam (fun _ _ f =>
                App f (App (App (Embed opair) (Embed ott)) (Embed ott)))).
