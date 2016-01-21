
Require Import Coq.Program.Tactics.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Arith.Arith_base.
Require Import Coq.Relations.Relations.


(***
 *** Logical Relations
 ***)

(* A logical relation is just an equivalence with a fancy name, so that we can
distinguish them as "the" relations for their respective types *)
Polymorphic Class LogRel_Rel@{c} (A : Type@{c}) : Type :=
  equalsLR : A -> A -> Prop.

(* The propositional part of a logical relation *)
Polymorphic Class LogRel@{c} (A : Type@{c}) {LR:LogRel_Rel A} : Prop :=
  { logrel_equivalence :> Equivalence equalsLR }.

Notation "x '==' y" := (equalsLR x y) (at level 80, no associativity).

(* equalsLR respects itself *)
(* FIXME: this is probably not needed...? *)
(*
Polymorphic Instance equalsLR_proper `{LogRel} :
  Proper (equalsLR ==> equalsLR ==> iff) equalsLR.
intros x1 x2 ex y1 y2 ey. rewrite ex.
 split; intro exy.
rewrite <- ex; rewrite exy; rewrite ey; reflexivity.
rewrite ex; rewrite exy; rewrite <- ey; reflexivity.
Qed.
*)


(* Some standard logical relations *)

Polymorphic Instance Pair_LogRel_Rel (A B: Type)
            {LRA:LogRel_Rel A} {LRB:LogRel_Rel B} : LogRel_Rel (A*B) :=
  fun p1 p2 =>
    equalsLR (fst p1) (fst p2) /\ equalsLR (snd p1) (snd p2).

Polymorphic Instance Pair_LogRel (A B: Type)
            `{LRA:LogRel A} `{LRB:LogRel B} : LogRel (A*B).
  repeat constructor.
  reflexivity.
  reflexivity.
  destruct H; symmetry; assumption.
  destruct H; symmetry; assumption.
  destruct H; destruct H0; transitivity (fst y); assumption.
  destruct H; destruct H0; transitivity (snd y); assumption.
Qed.


(***
 *** The monad typeclass
 ***)

Polymorphic Class MonadOps@{d c} (M : Type@{d} -> Type@{c}) : Type :=
  { returnM : forall {A : Type@{d}}, A -> M A;
    bindM : forall {A B : Type@{d}}, M A -> (A -> M B) -> M B;
    equalsM :> forall {A : Type@{d}} {LR:LogRel_Rel A}, LogRel_Rel (M A) }.

Polymorphic Class Monad@{d c} (M : Type@{d} -> Type@{c})
            {MonadOps:MonadOps@{d c} M} : Prop :=
  {
    monad_return_bind :
      forall (A B:Type@{d}) `{LogRel B} x (f:A -> M B),
        bindM (returnM x) f == f x;
    monad_bind_return :
      forall (A:Type@{d}) (m:M A) `{LogRel A},
        bindM m returnM == m;
    monad_assoc :
      forall (A B C:Type@{d}) `{LogRel C} m (f:A -> M B) (g:B -> M C),
        bindM (bindM m f) g == bindM m (fun x => bindM (f x) g);
    monad_equalsM :>
      forall (A:Type@{d}) `{LogRel A},
        LogRel _ (LR:=equalsM);
    monad_proper_return :>
      forall (A:Type@{d}) `{LogRel A},
        Proper (equalsLR ==> equalsM) returnM;
    monad_proper_bind :>
      forall (A B:Type@{d}) `{LogRel A} `{LogRel B},
        Proper (equalsM ==> (equalsLR ==> equalsM) ==> equalsM)
               (bindM (A:=A) (B:=B))
  }.


(***
 *** Helper theorems about monads
 ***)

(* FIXME: Equivalence and friends are not polymorphic... *)
Instance equalsM_Equivalence `{Monad} `{LogRel} : Equivalence (equalsM (A:=A)).
  apply monad_equalsM; assumption.
Qed.

(* FIXME: why is this not automatic in the proof of bind_fun_equalsM?!? *)
Instance equalsM_Reflexive `{Monad} `{LogRel} : Reflexive (equalsM (A:=A)).
  auto with typeclass_instances.
Qed.

Instance equalsM_Symmetric `{Monad} `{LogRel} : Symmetric (equalsM (A:=A)).
  auto with typeclass_instances.
Qed.

Instance equalsM_Transitive `{Monad} `{LogRel} : Transitive (equalsM (A:=A)).
  auto with typeclass_instances.
Qed.

Polymorphic Instance equalsM_equalsLR_iff_Proper `{Monad} `{LogRel} :
  Proper (equalsLR ==> equalsLR ==> iff) equalsM.
intros m11 m12 e1 m21 m22 e2; split; intros.
transitivity m11; [ symmetry; assumption | transitivity m21; assumption ].
transitivity m12; [ assumption |
                    transitivity m22; try assumption; symmetry; assumption ].
Qed.

Polymorphic Instance equalsM_equalsLR_impl_Proper `{Monad} `{LogRel} :
  Proper (equalsLR ==> equalsLR ==> Basics.flip Basics.impl) equalsM.
intros m11 m12 e1 m21 m22 e2 e12.
transitivity m12; [ assumption |
                    transitivity m22; try assumption; symmetry; assumption ].
Qed.

Lemma bind_fun_equalsM `{Monad}
            {A B:Type} `{LogRel (A:=A)} `{LogRel (A:=B)}
            m (f1 f2:A -> M B) :
  Proper (equalsLR ==> equalsM) f1 -> Proper (equalsLR ==> equalsM) f2 ->
  (forall x, f1 x == f2 x) -> bindM m f1 == bindM m f2.
intros proper1 proper2 e; apply (monad_proper_bind A B); [ reflexivity | ].
intros x y e'.
transitivity (f1 y).
apply proper1; assumption.
apply e.
Qed.


(***
 *** The Identity Monad
 ***)

Definition Identity (X:Type) := X.
Instance IdMonad_MonadOps : MonadOps Identity :=
  { returnM := fun A x => x;
    bindM := fun A B m f => f m;
    equalsM := fun A LR => LR }.

Instance IdMonad : Monad Identity.
  constructor; intros; try reflexivity.
  split; auto with typeclass_instances.
  intros x y exy; assumption.
  intros m1 m2 eqm f1 f2 eqf; apply eqf; assumption.
Qed.
