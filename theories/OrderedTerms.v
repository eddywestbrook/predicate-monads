Require Import Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.

Set Implicit Arguments.
Set Strict Implicit.

Class Order (T : Type) : Type :=
{ le : T -> T -> Prop
; Refl_le :> Reflexive le
; Trans_le :> Transitive le }.
Arguments le {_ _} _ _.
Arguments Refl_le {_ _} _.
Arguments Trans_le {_ _} _ _ _ _ _.

Record otype : Type :=
{ T :> Type
; order :> Order T }.
(* 'equality' is defined as 'a <= b /\ b <= a' *)

Existing Instance order.

Definition ole {T : otype} (a b : T) : Prop :=
  le a b.

Global Instance Reflexive_ole {T} : Reflexive (@ole T).
Proof. red. intros. red. destruct T0. eapply Refl_le. Qed.
Global Instance Transitive_ole {T} : Transitive (@ole T).
Proof. red. intros. red. destruct T0. eapply Trans_le; eauto. Qed.

Instance Proper_ole_impl {A : otype}
: Morphisms.Proper (ole --> ole ==> Basics.impl) (@ole A).
Proof.
  do 4 red. intros.
  etransitivity. eapply H. etransitivity; eauto.
Qed.

Definition oequiv {T : otype} (a b : T) : Prop :=
  ole a b /\ ole b a.

Global Instance Reflexive_oequiv {T} : Reflexive (@oequiv T).
Proof. red. intros. red. destruct T0. split; eapply Refl_le. Qed.
Global Instance Symmetric_oequiv {A} : Symmetric (@oequiv A).
Proof. red. unfold oequiv. tauto. Qed.
Global Instance Transitive_oequiv {T} : Transitive (@oequiv T).
Proof. do 2 red. intros.
       destruct T0. destruct H; destruct H0; split; etransitivity; eauto.
Qed.

Instance Proper_oequiv_iff {A : otype}
: Morphisms.Proper (oequiv ==> oequiv ==> iff) (@oequiv A).
Proof.
  red. red. red. intros.
  split; intros.
  etransitivity. symmetry; eauto. etransitivity; eauto.
  etransitivity. eauto. etransitivity; eauto. symmetry; eauto.
Qed.

Instance Proper_ole_oequiv_iff {A : otype}
: Morphisms.Proper (oequiv ==> oequiv ==> iff) (@ole A).
Proof.
  red. red. red. intros.
  split; intros.
  etransitivity. eapply H. etransitivity; eauto. eapply H0.
  etransitivity. eapply H. etransitivity; eauto. eapply H0.
Qed.

(* The discrete ordering *)
Definition otype_eq (T : Type) : otype :=
{| T := T
 ; order := {| le := @eq T |}
 |}.

(** * Ordered Products **)
Definition Order_prod (A B : Type) `{OA : Order A} `{OB : Order B}
: Order (A * B).
refine
{| le := fun a b => @le _ OA (fst a) (fst b) /\ @le _ OB(snd a) (snd b) |}.
{ split; apply Refl_le. }
{ red. destruct 1; destruct 1; split; eapply Trans_le; eassumption. }
Defined.

Canonical Structure otype_prod (a b : otype) : otype :=
{| T := a.(T) * b.(T)
; order := @Order_prod a.(T) b.(T) a.(order) b.(order) |}.

(** * Ordered Unit **)
Definition Order_unit : Order unit.
refine
  {| le := fun _ _ => True |}.
compute; auto.
compute; auto.
Defined.

Canonical Structure otype_unit : otype :=
{| T := unit ; order := @Order_unit |}.

(** * Ordered Functions **)
Record PFun (A B : otype) : Type :=
{ function : A -> B
; Proper_function : Proper (ole ==> ole) function }.

Local Definition Order_fun (A B : otype)
: Order (PFun A B).
refine
{| le := fun a b => (ole ==> ole)%signature (function a) (function b) |}.
{ red. red. intros. destruct x. simpl. apply Proper_function0. assumption. }
{ red. red. intros.
  eapply Trans_le.
  eapply H. eassumption.
  eapply H0. eapply Refl_le. }
Defined.

Definition otype_fun (a b : otype) : otype :=
{| T := PFun a b
; order := @Order_fun a b |}.

Definition otype_apply {a b : otype} (f : otype_fun a b) (x : a) : b :=
  f.(function) x.

Global Instance Proper_otype_apply_ole {a b : otype}
: Proper (ole ==> ole ==> ole) (@otype_apply a b).
Proof.
  red. red. red. intros.
  red in H. unfold le in H. unfold order in H. simpl in H.
  eapply H. assumption.
Defined.

Global Instance Proper_otype_apply_oequiv {A B}
: Morphisms.Proper (oequiv ==> oequiv ==> oequiv) (@otype_apply A B).
Proof.
  do 3 red. intros.
  unfold otype_apply.
  destruct H.
  split.
  eapply H; eapply H0.
  eapply H1; eapply H0.
Qed.

Lemma otype_ext_eq : forall {A B : otype} (f g : otype_fun A  B),
    (forall x, oequiv (otype_apply f x) (otype_apply g x)) ->
    oequiv f g.
Proof.
  intros.
  destruct f; destruct g; simpl in *.
  split.
  { red. simpl. red. intros.
    etransitivity.
    eapply Proper_function0. eassumption.
    eapply H. }
  { red. simpl. red. intros.
    etransitivity.
    eapply Proper_function1. eassumption.
    eapply H. }
Qed.

Definition otype_abs {a b : otype} (f : a -> b) (pf : Proper (@le _ a.(order) ==> @le _ b.(order)) f) : otype_fun a b.
  exists f. assumption.
Defined.
Arguments otype_abs {_ _} _ {_} : clear implicits.

(** * A Shallow Encoding using Eddy's 'ProperInCtx' phrasing **)
(**************************************************************)
Require Import Coq.Lists.List.
Fixpoint otype_tuple (ls : list otype) : otype :=
  match ls with
  | nil => otype_unit
  | l :: ls => otype_prod l (otype_tuple ls)
  end.

Definition InCtx (ls : list otype) (t : otype) : otype :=
  otype_fun (otype_tuple ls) t.

Definition App_ctx {ls a b} (f : InCtx ls (otype_fun a b)) (x : InCtx ls a)
: InCtx ls b.
eapply otype_abs.
instantiate (1 := fun ctx =>
                    otype_apply (otype_apply f ctx)
                                (otype_apply x ctx)).
red. red. intros.
repeat simple eapply Proper_otype_apply_ole; try eassumption; reflexivity.
Defined.

Definition Lift_ctx {ls} {a : otype} (x : a) : InCtx ls a.
eapply otype_abs.
instantiate (1 := fun _ => x). red. red. intros. eapply Refl_le.
Defined.

Definition ToCtx {a} (x : InCtx nil a) : a := x.(function) tt.

Definition Abs_ctx {ls a b} (x : InCtx (a :: ls) b) : InCtx ls (otype_fun a b).
eapply otype_abs.
instantiate (1:=fun ctx => otype_abs _).
Unshelve.
Focus 2.
intro. eapply x. constructor. apply X. apply ctx.
Focus 2.
abstract (simpl; do 2 red; intros; destruct x; simpl; eapply Proper_function0; constructor;
          [ eassumption | eapply Refl_le ]).
abstract (do 2 red; unfold le; simpl; do 2 red; intros; simpl; destruct x; apply Proper_function0; constructor; auto).
Defined.


Definition tuple_hd {x xs} : otype_fun (otype_tuple (x :: xs)) x.
exists (@fst _ _).
abstract (do 2 red; fold otype_tuple; intros; red in H; unfold le in H; simpl in H; tauto).
Defined.

Definition tuple_tl {x xs} : otype_fun (otype_tuple (x :: xs)) (otype_tuple xs).
exists (@snd _ _).
abstract (do 2 red; fold otype_tuple; intros; red in H; unfold le in H; simpl in H; tauto).
Defined.

Definition otype_compose {a b c} : otype_fun a b -> otype_fun b c -> otype_fun a c.
intros.
red. simpl.
exists (fun x => function X0 (function X x)).
abstract (do 2 red; intros; eapply (Proper_function X0); eapply (Proper_function X); eassumption).
Defined.

Fixpoint Var_ctx {a} (n : nat) {ls} {struct n}
: nth_error ls n = Some a -> InCtx ls a :=
  match ls as ls , n as n
        return nth_error ls n = Some a -> InCtx ls a
  with
  | l :: _ , 0 => fun pf : Some l = Some a =>
                    match pf in _ = X return match X with
                                             | Some y => _
                                             | _ => unit
                                             end
                    with
                    | eq_refl => tuple_hd
                    end
  | _ :: ls , S n => fun pf : nth_error ls n = Some a =>
    otype_compose tuple_tl(@Var_ctx _ _ _ pf)
  | nil , 0
  | nil , S _ => fun x : None = Some a => match x with eq_refl => tt end
  end.

(** * Instances **)
Global Instance Proper_App_ctx G A B
: Morphisms.Proper (oequiv ==> oequiv ==> oequiv) (@App_ctx G A B).
Proof.
  red. red. red. simpl. intros.
  unfold App_ctx. simpl. split; red; simpl; red; intros.
  { eapply H; eauto.
    eapply H0; eauto. }
  { eapply H; eauto.
    eapply H0; eauto. }
Qed.

Global Instance Proper_Abs_ctx G B A
: Morphisms.Proper (oequiv ==> oequiv) (@Abs_ctx G A B).
Proof.
  unfold Abs_ctx. red. red. simpl. intros.
  simpl. apply otype_ext_eq; intros.
  simpl. unfold otype_abs. split; red; simpl; red; intros; eapply H; eauto.
  constructor; simpl; eauto. reflexivity.
  constructor; simpl; eauto. reflexivity.
Qed.

Global Instance Proper_Lift_ctx A G
: Morphisms.Proper (oequiv ==> oequiv) (@Lift_ctx A G).
Proof.
  do 2 red. simpl. unfold Lift_ctx. intros.
  eapply otype_ext_eq.
  intros. assumption.
Qed.
