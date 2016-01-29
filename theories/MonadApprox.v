Require Import PredMonad.Monad.
(***
 *** Non-Termination Effects
 ***)

Section Divergence.
Variable M : Type -> Type.
(* approxM m1 m2 means m1 "approximates" m2, i.e., m2 is "at least as
terminating as" m1 *)
Class MonadApprox : Type :=
{ approxM : forall {A}, relation (M A)
; fixM : forall {A B}, ((A -> M B) -> (A -> M B)) -> A -> M B }.

Notation "m1 '<<<' m2" := (approxM m1 m2) (at level 80, no associativity).

Class MonadFix `{Monad M} `{MonadApprox}
: Prop :=
  {
    monad_fix_monad :> Monad M ;
    monad_fix_approx_preorder :> forall A, PreOrder (approxM (A:=A));
    monad_fix_approx_antisymmetry :
      forall A (m1 m2:M A) `{Equals A}, approxM m1 m2 -> approxM m2 m1 -> m1 == m2;
    monad_fix_approx_bind :>
      forall A B `{Equals A} `{Equals B},
        Proper
          (approxM (A:=A) ==> (@eq A ==> approxM (A:=B)) ==> approxM (A:=B))
          bindM ;
    monad_fix_approx_proper :>
      forall A `{Equals A}, Proper (equals (A:=M A) ==> equals (A:=M A) ==> iff) approxM;
    monad_fix_fix_proper :>
      forall A B `{Equals A} `{Equals B},
        Proper (((@eq A ==> equals (A:=M B)) ==> @eq A ==> equals (A:=M B))
                  ==> @eq A ==> equals (A:=M B)) fixM;
    monad_fix_fixm :
      forall A B f x `{Equals A} `{Equals B},
        Proper (((@eq A) ==> (approxM (A:=B))) ==> @eq A ==> approxM (A:=B)) f ->
        fixM (A:=A) (B:=B) f x == f (fixM f) x
  }.

Add Parametric Relation `{MonadFix} A : (M A) (approxM (A:=A))
  reflexivity proved by PreOrder_Reflexive
  transitivity proved by PreOrder_Transitive
as approxM_morphism.

End Divergence.