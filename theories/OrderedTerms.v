Require Import Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.

Set Implicit Arguments.
Set Strict Implicit.

Record Order (T : Type) : Type :=
{ le : T -> T -> Prop
; Refl_le :> Reflexive le
; Trans_le :> Transitive le }.
Arguments le {_ _} _ _.
Arguments Refl_le {_ _} _.
Arguments Trans_le {_ _} _ _ _ _ _.

Record otype : Type :=
{ T :> Type ; order :> Order T }.
(* 'equality' is defined as 'a <= b /\ b <= a' *)

(* The discrete ordering *)
Definition otype_eq (T : Type) : otype.
exists T.
exists eq.
eauto. eauto with typeclass_instances.
Defined.


Definition Order_pair (A B : Type) `{OA : Order A} `{OB : Order B} : Order (A * B).
refine
{| le := fun a b => @le _ OA (fst a) (fst b) /\ @le _ OB(snd a) (snd b) |}.
{ split; apply Refl_le. }
{ red. destruct 1; destruct 1; split; eapply Trans_le; eassumption. }
Defined.

Canonical Structure otype_pair (a b : otype) : otype := (* canonical structure *)
{| T := a.(T) * b.(T) ; order := @Order_pair a.(T) b.(T) a.(order) b.(order) |}.

Definition Order_fun (A B : Type) `{OA : Order A} `{OB : Order B}
: Order { f : A -> B & Proper (@le _ OA ==> @le _ OB) f }.
refine
{| le := fun a b => (@le _ OA ==> @le _ OB)%signature (projT1 a) (projT1 b) |}.
{ red. red. intros. destruct x. simpl. apply p. assumption. }
{ red. red. intros.
  eapply Trans_le.
  eapply H. eassumption.
  eapply H0. eapply Refl_le. }
Defined.

Definition otype_fun (a b : otype) : otype :=
{| T := { f : a.(T) -> b.(T) & Proper (le ==> le) f }
; order := @Order_fun _ _ a.(order) b.(order) |}.

Definition Order_unit : Order unit.
refine
  {| le := fun _ _ => True |}.
compute; auto.
compute; auto.
Defined.

Canonical Structure otype_unit : otype :=
{| T := unit ; order := @Order_unit |}.


Definition otype_apply {a b : otype} (f : otype_fun a b) (x : a) : b :=
  (projT1 f) x.

Lemma Proper_otype_apply {a b : otype}
  : Proper (@le _ (otype_fun a b).(order) ==> @le _ a.(order) ==> @le _ b.(order)) (@otype_apply a b).
  red. red. red. intros.
  eapply H. assumption.
Defined.

Definition otype_abs {a b : otype} (f : a -> b) (pf : Proper (@le _ a.(order) ==> @le _ b.(order)) f) : otype_fun a b.
  exists f. assumption.
Defined.


(** * A Shallow Encoding using Eddy's 'ProperInCtx' phrasing **)
(**************************************************************)
Require Import Coq.Lists.List.
Fixpoint otype_tuple (ls : list otype) : otype :=
  match ls with
  | nil => otype_unit
  | l :: ls => otype_pair l (otype_tuple ls)
  end.

Definition InCtx (ls : list otype) (t : otype) : Type :=
  otype_fun (otype_tuple ls) t.

Definition App_ctx {ls a b} (f : InCtx ls (otype_fun a b)) (x : InCtx ls a)
: InCtx ls b.
eapply otype_abs.
instantiate (1 := fun ctx =>
                    otype_apply (otype_apply f ctx)
                                (otype_apply x ctx)).
red. red. intros.
repeat simple eapply Proper_otype_apply; try eassumption; eapply Refl_le.
Defined.

Definition Lift_ctx {ls} {a : otype} (x : a) : InCtx ls a.
eapply otype_abs.
instantiate (1 := fun _ => x). red. red. intros. eapply Refl_le.
Defined.

Definition ToCtx {a} (x : InCtx nil a) : a.
apply x. compute. tauto.
Defined.

Definition Abs_ctx {ls a b} (x : InCtx (a :: ls) b) : InCtx ls (otype_fun a b).
eapply otype_abs.
instantiate (1:=fun ctx => otype_abs _).
Unshelve.
Focus 2.
intro. eapply x. constructor. apply X. apply ctx.
Focus 2.
simpl. red. red. intros. destruct x; simpl. eapply p. constructor.
simpl. eassumption. eapply Refl_le.
red. red. intros.
red. red. red. red. red. intros.
simpl. destruct x. apply p. constructor; auto.
Defined.

Definition tuple_hd {x xs} : otype_fun (otype_tuple (x :: xs)) x.
exists (@fst _ _).
red. red. simpl. tauto.
Defined.

Definition tuple_tl {x xs} : otype_fun (otype_tuple (x :: xs)) (otype_tuple xs).
exists (@snd _ _).
red. red. simpl. tauto.
Defined.

Definition otype_compose {a b c} : otype_fun a b -> otype_fun b c -> otype_fun a c.
intros.
red. simpl.
exists (fun x => projT1 X0 (projT1 X x)).
red. red. intros.
eapply (projT2 X0).
eapply (projT2 X).
eassumption.
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

(** * A Deeply Embedded Langauge **)
(**********************************)
Require Import ExtLib.Data.Member.
Section fo.
  Inductive oexpr (g : list otype) : otype -> Type :=
  | Const : forall ot : otype, ot.(T) -> oexpr g ot
  | Var : forall T, member T g -> oexpr g T
  | App : forall a b : otype, oexpr g (otype_fun a b) -> oexpr g a -> oexpr g b
  | Abs : forall a b : otype, oexpr (a :: g) b -> oexpr g (otype_fun a b).
End fo.
Arguments oexpr _ _ : clear implicits.

Fixpoint member_to_nat {T : Type} ls (l : T) (m : member l ls)
: { n : nat & nth_error ls n = Some l } :=
  match m in member _ ls
        return { n : nat & nth_error ls n = Some l }
  with
  | MZ _ _ => @existT _ _ 0 eq_refl
  | MN _ m => match @member_to_nat T _ _ m with
              | existT _ n pf => @existT _ _ (S n) pf
              end
  end.

Fixpoint oexprD {ls} {ot} (e : oexpr ls ot) : InCtx ls ot :=
  match e in oexpr _ ot return InCtx ls ot with
  | Const _ t c => Lift_ctx c
  | Var v => let '(existT _ n pf) := member_to_nat v in Var_ctx n pf
  | @App _ d c f x => 
    App_ctx (oexprD f) (oexprD x)
  | Abs body => Abs_ctx (oexprD body)
  end.

Definition OExprD {ot} (e : oexpr nil ot) : ot :=
  ToCtx (oexprD e).

Arguments Abs {_} _ {_} _ : clear implicits.
Arguments Var {_ _} _ : clear implicits.
Arguments Const {_ _} _ : clear implicits.
Arguments MZ {_ _ _}.
Arguments MN {_ _ _ _} _ : clear implicits.

(* A very simple example *)
Eval compute in OExprD (Abs (otype_eq nat) (Var MZ)).

Definition otype_abs_eq {T} {a : otype} (F : T -> a) : otype_fun (otype_eq T) a.
red. red. exists F. red. red. intros. compute in H. subst. eapply Refl_le.
Defined.

Definition inj {a:otype} (x : a) : a := x.
Canonical Structure otype_nat := otype_eq nat.

(* Embedding functions is going to be horrible *)
Definition Plus : otype_fun (otype_eq nat) (otype_fun (otype_eq nat) (otype_eq nat)) :=
  otype_abs_eq (fun x : nat => otype_abs_eq (fun y : nat => inj (x + y))).

Eval compute in OExprD (Abs otype_nat (Abs otype_nat (App (App (Const Plus) (Var MZ)) (Var (MN MZ))))).
