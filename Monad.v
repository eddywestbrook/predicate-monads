
Add LoadPath "." as PredMonad.
Require Export PredMonad.LogicalRelations.


(***
 *** The monad typeclass
 ***)

Polymorphic Class MonadOps@{d c} (M : Type@{d} -> Type@{c}) : Type :=
  { returnM : forall {A : Type@{d}}, A -> M A;
    bindM : forall {A B : Type@{d}}, M A -> (A -> M B) -> M B;
    orderM :> forall {A : Type@{d}} {OrdOp:OrderOp A}, OrderOp (M A) }.

Polymorphic Class Monad@{d c} (M : Type@{d} -> Type@{c})
            {MonadOps:MonadOps@{d c} M} : Prop :=
  {
    monad_return_bind :
      forall (A B:Type@{d}) `{Order A} `{Order B} x (f:A -> M B),
        bindM (returnM x) f == f x;
    monad_bind_return :
      forall (A:Type@{d}) `{Order A} (m:M A),
        bindM m returnM == m;
    monad_assoc :
      forall (A B C:Type@{d}) `{Order A} `{Order B} `{Order C}
             m (f:A -> M B) (g:B -> M C),
        bindM (bindM m f) g == bindM m (fun x => bindM (f x) g);
    monad_orderM :>
      forall {A:Type@{d}} `{Order A},
        Order _ (OrdOp:=orderM);
    monad_proper_return :>
      forall (A:Type@{d}) `{Order A},
        Proper (order ==> orderM) returnM;
    monad_proper_bind :>
      forall (A B:Type@{d}) `{Order A} `{Order B},
        Proper (orderM ==> (order ==> orderM) ==> orderM)
               (bindM (A:=A) (B:=B))
  }.


(***
 *** Helper theorems about monads
 ***)

(* If we have a monad and an Order for A, we have an Order for M A. *)
Instance orderM_OrderOp `{MonadOps} `{OrderOp} : OrderOp (M A) :=
  orderM.
Instance orderM_Order `{Monad} `{Order} : Order (M A) :=
  monad_orderM.

Instance orderM_PreOrder `{Monad} `{Order} : PreOrder (orderM (A:=A)).
apply monad_orderM.
Qed.

Instance orderM_Reflexive `{Monad} `{Order} : Reflexive (orderM (A:=A)).
auto with typeclass_instances.
Qed.

(*
(* FIXME: Equivalence and friends are not polymorphic... *)
Instance equalsM_Equivalence `{Monad} `{Equals} : Equivalence (equalsM (A:=A)).
  apply monad_equalsM; assumption.
Qed.

(* FIXME: why is this not automatic in the proof of bind_fun_equalsM?!? *)
Instance equalsM_Reflexive `{Monad} `{Equals} : Reflexive (equalsM (A:=A)).
  auto with typeclass_instances.
Qed.

Instance equalsM_Symmetric `{Monad} `{Equals} : Symmetric (equalsM (A:=A)).
  auto with typeclass_instances.
Qed.

Instance equalsM_Transitive `{Monad} `{Equals} : Transitive (equalsM (A:=A)).
  auto with typeclass_instances.
Qed.

Add Parametric Relation `{Monad} `{Equals} : (M A) equalsM
    reflexivity proved by equalsM_Reflexive
    symmetry proved by equalsM_Symmetric
    transitivity proved by equalsM_Transitive
as equalsM_Equivalence2.
*)

(*
Polymorphic Instance equalsM_equals_iff_Proper `{Monad} `{Equals} :
  Proper (equals ==> equals ==> iff) equalsM.
intros m11 m12 e1 m21 m22 e2; split; intros.
transitivity m11; [ symmetry; assumption | transitivity m21; assumption ].
transitivity m12; [ assumption |
                    transitivity m22; try assumption; symmetry; assumption ].
Qed.

Polymorphic Instance equalsM_equals_impl_Proper `{Monad} `{Equals} :
  Proper (equals ==> equals ==> Basics.flip Basics.impl) equalsM.
intros m11 m12 e1 m21 m22 e2 e12.
transitivity m12; [ assumption |
                    transitivity m22; try assumption; symmetry; assumption ].
Qed.
*)

Lemma bind_fun_equalsM `{Monad} {A B:Type}
      `{Order A} `{Order B} m (f1 f2:A -> M B) :
  (forall x, f1 x == f2 x) -> bindM m f1 == bindM m f2.
  intros e; split; apply (monad_proper_bind A B (H:=Eq_Order A) m m).
  (* FIXME: why does the reflexivity tactic not work? *)
  apply (orderM_Reflexive (H0:=Eq_Order A)).
  intros x y exy. rewrite exy. apply e.
  apply (orderM_Reflexive (H0:=Eq_Order A)).
  intros x y exy. rewrite exy. apply e.
Qed.


(***
 *** The Identity Monad
 ***)

Definition Identity (X:Type) := X.
Instance IdMonad_MonadOps : MonadOps Identity :=
  { returnM := fun A x => x;
    bindM := fun A B m f => f m;
    orderM := fun A ord => ord }.

Instance IdMonad : Monad Identity.
  constructor; intros; try reflexivity.
  split; auto with typeclass_instances.
  intros x y exy; assumption.
  intros m1 m2 eqm f1 f2 eqf; apply eqf; assumption.
Qed.
