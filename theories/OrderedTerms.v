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
Definition oequiv {T : otype} (a b : T) : Prop :=
  ole a b /\ ole b a.

(* The discrete ordering *)
Definition otype_eq (T : Type) : otype.
exists T.
exists eq.
eauto. eauto with typeclass_instances.
Defined.


Definition Order_prod (A B : Type) `{OA : Order A} `{OB : Order B}
: Order (A * B).
refine
{| le := fun a b => @le _ OA (fst a) (fst b) /\ @le _ OB(snd a) (snd b) |}.
{ split; apply Refl_le. }
{ red. destruct 1; destruct 1; split; eapply Trans_le; eassumption. }
Defined.

Canonical Structure otype_prod (a b : otype) : otype := (* canonical structure *)
{| T := a.(T) * b.(T)
; order := @Order_prod a.(T) b.(T) a.(order) b.(order) |}.

Record PFun (A B : otype) : Type :=
{ function : A -> B
; Proper_function : Proper (ole ==> ole) function }.

Definition Order_fun (A B : otype)
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

Definition Order_unit : Order unit.
refine
  {| le := fun _ _ => True |}.
compute; auto.
compute; auto.
Defined.

Canonical Structure otype_unit : otype :=
{| T := unit ; order := @Order_unit |}.


Definition otype_apply {a b : otype} (f : otype_fun a b) (x : a) : b :=
  f.(function) x.

Lemma Proper_otype_apply {a b : otype}
: Proper (ole ==> ole ==> ole) (@otype_apply a b).
  red. red. red. intros.
  red in H. unfold le in H. unfold order in H. simpl in H.
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
repeat simple eapply Proper_otype_apply; try eassumption; eapply Refl_le.
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

(** * A Deeply Embedded Language **)
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

Require Import ExtLib.Data.HList.

Fixpoint arrs (ls : list otype) (d : otype) : otype :=
  match ls with
  | nil => d
  | l :: ls => otype_fun l (arrs ls d)
  end.
Fixpoint apps {vs ls : list otype} {d : otype} (f : oexpr vs (arrs ls d)) (xs : hlist (oexpr vs) ls)
: oexpr vs d.
refine (
  match xs in hlist _ ls
        return oexpr vs (arrs ls d) -> oexpr vs d
  with
  | Hnil => fun f => f
  | @Hcons _ _ l ls x xs => fun f => @apps vs ls _ (@App _ _ _ f x) xs
  end f).
Defined.

(*
Section tele.
  Context {T : Type}.
  Variable F : list T -> T -> Type.

  Inductive tele : list T -> Type :=
  | Tend : tele nil
  | Tcons : forall t ts, F ts t -> tele ts -> tele (t :: ts).
End tele.

Section rem.
  Context {T} {F : list T -> T -> Type}.
  Fixpoint tele_rem  {ts} (t : tele (fun ts t => option (F ts t)) ts) : list T :=
    match t with
    | Tend _ => nil
    | @Tcons _ _ t _ None ts => t :: tele_rem ts
    | @Tcons _ _ _ _ (Some _) ts => tele_rem ts
    end.
End rem.
*)

Section Subst.
  Context {T : Type}.
  Variable F : list T -> T -> Type.
  Inductive Subst : list T -> list T -> Type :=
  | Snil : Subst nil nil
  | Sterm : forall ts ts' t, F ts' t -> Subst ts ts' -> Subst (t :: ts) ts'
  | Sskip : forall ts ts' t, Subst ts ts' -> Subst (t :: ts) (t :: ts').
End Subst.

(* NOTE: You can not implement this when you have a shallow encoding of types
Fixpoint oexpr_red {ls' ls ds} {ot}
         (g : Subst oexpr ls ls')
         (e : oexpr ls (arrs ds ot))
         (xs : hlist (oexpr ls') ds)
: oexpr ls' ot.
refine (
  match e in oexpr _ ot'
        return ot' = arrs ds ot -> oexpr ls' ot
  with
  | Const _ t c => fun pf =>
                     _
  | Var v => _
  | @App _ d c f x => fun pf =>
    @oexpr_red _ _ (d :: ds) ot g
               match pf in _ = X return oexpr _ (otype_fun _ X) with
               | eq_refl => f
               end (Hcons (@oexpr_red _ _ nil d g x Hnil) xs)
  | @Abs _ d c body =>
    match xs in hlist _ ds
          return otype_fun d c = arrs ds ot -> oexpr ls' ot
    with
    | Hnil => fun pf : otype_fun d c = ot =>
      match pf with
      | eq_refl => @Abs _ d c (@oexpr_red _ _ nil _ (@Sskip _ _ _ _ _ g)
                                          body
                                          Hnil)
      end
    | Hcons x xs => _
    end
  end eq_refl).
Focus 3. simpl.
refine
  (fun pf => @oexpr_red ls' (_ :: ls) _ _ (Sterm _ x g) _ xs).
*)

Definition OExprD {ot} (e : oexpr nil ot) : ot :=
  ToCtx (oexprD e).

Arguments Abs {_} _ {_} _ : clear implicits.
Arguments Var {_ _} _ : clear implicits.
Arguments Const {_ _} _ : clear implicits.
Arguments MZ {_ _ _}.
Arguments MN {_ _ _ _} _ : clear implicits.

(* A very simple example *)
Eval compute in OExprD (Abs (otype_eq nat) (Var MZ)).

Definition otype_abs_eq {T} {a : otype} (F : T -> a)
: otype_fun (otype_eq T) a.
red. exists F. red. red. intros. compute in H. simpl in H. subst. eapply Refl_le.
Defined.

Definition inj {a:otype} (x : a) : a := x.
Canonical Structure otype_nat := otype_eq nat.

(* Embedding functions is going to be horrible *)
Definition Plus : otype_fun (otype_eq nat) (otype_fun (otype_eq nat) (otype_eq nat)) :=
  otype_abs_eq (fun x : nat => otype_abs_eq (fun y : nat => inj (x + y))).

Eval compute in OExprD (Abs otype_nat (Abs otype_nat (App (App (Const Plus) (Var MZ)) (Var (MN MZ))))).
