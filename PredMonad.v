
Require Import Coq.Program.Basics.

Load Monad.


(***
 *** The Predicate Monad Typeclass
 ***)

Section PredMonad.

Context (M: Type -> Type) (PM : Type -> Type).

(* The satisfiability order on monadic predicates, where leqM P1 P2 means that
anything satisfying P1 satisfies P2; we will require this to be a complete
lattice (meets and joins over arbitrary sets) below *)
Class PredMonadOrder : Type :=
  leqP : forall {A}, relation (PM A).

(* The satisfaction relation between computations and monadic predicates *)
Class PredMonadSatisfaction : Type :=
  satisfiesP : forall {A}, M A -> PM A -> Prop.

(* Notation for satisfaction *)
Infix "|=" := satisfiesP (at level 80).

(* The quantifiers, which correspond to lattice meet and join, respectively *)
Class PredMonadForall : Type :=
  forallP : forall {A B}, (A -> PM B) -> PM B.
Class PredMonadExists : Type :=
  existsP : forall {A B}, (A -> PM B) -> PM B.

(* Implication, which will form a Heyting Algebra, below *)
Class PredMonadImplication : Type :=
  impliesP : forall {A}, PM A -> PM A -> PM A.

Context
  (PredMonadRet:MonadRet PM) (PredMonadBind:MonadBind PM)
  (PredMonadEquiv:MonadEquiv PM)
  (MonadRet:MonadRet M) (MonadBind:MonadBind M) (MonadEquiv:MonadEquiv M)
  (PredMonadOrder:PredMonadOrder) (PredMonadSatisfaction:PredMonadSatisfaction)
  (PredMonadForall:PredMonadForall)
  (PredMonadExists:PredMonadExists) (PredMonadImplication:PredMonadImplication).

(* Defined logical operators, which correspond to binary meet and join *)
Definition andP {A} (P1 P2: PM A) : PM A :=
  forallP (fun (b:bool) => if b then P1 else P2).
Definition orP {A} (P1 P2: PM A) : PM A :=
  existsP (fun (b:bool) => if b then P1 else P2).

(* True and false, which correspond to top and bottom, respectively *)
Definition trueP {A} : PM A := existsP id.
Definition falseP {A} : PM A := forallP id.

(* Negation, which (as in normal Coq) is implication of false *)
Definition notP {A} (P: PM A) : PM A := impliesP P falseP.

(* Lifting a proposition = the join over all proofs of it *)
Definition liftProp {A} (P: Prop) : PM A :=
  existsP (fun (pf:P) => trueP).

(* The predicate monad typeclass itself *)
Class PredMonad : Prop :=
  {
    (* Both M and PM must be monads *)
    predmonad_monad_M : Monad M;
    predmonad_monad_PM : Monad PM;

    (* The satisfiability order is a partial order w.r.t. eqM *)
    predmonad_leqP_preorder : forall {A}, PreOrder (leqP (A:=A));
    predmonad_leqP_antisymmetric :
      forall {A}, Antisymmetric (eqM (A:=A)) leqP;
    predmonad_leqP_proper :
      forall {A}, Proper (eqM (A:=A) ==> eqM (A:=A) ==> impl) leqP;

    (* Satisfaction is monotone with respect to the satisfiability order *)
    predmonad_satisfiesP_monotone :
      forall {A}, Proper (@eq (M A) ==> leqP ==> impl) satisfiesP;

    (* Forall and exists are complete meet and join operators, respectively *)
    predmonad_forallP_lower_bound :
      forall {A B} (f: A -> PM B) a, leqP (forallP f) (f a);
    predmonad_forallP_greatest_lower_bound :
      forall {A B} (f: A -> PM B) P,
        (forall a, leqP P (f a)) -> leqP P (forallP f);
    predmonad_existsP_upper_bound :
      forall {A B} (f: A -> PM B) a, leqP (f a) (existsP f);
    predmonad_existsP_least_upper_bound :
      forall {A B} (f: A -> PM B) P,
        (forall a, leqP (f a) P) ->  leqP (existsP f) P;

    (* The fact that true always holds and false never does is equivalent to the
    existence, for each m, of predicates that m does and does not satisfy,
    respectively. We state the latter property as an axiom, and the former
    properties follow from them. *)
    predmonad_separation :
      forall {A} (m:M A), exists P1 P2, m |= P1 /\ ~(m |= P2);

    (* Implication makes a predicate monad into a complete Heyting algebra,
    which means there is a Galois connection between implication and the andP
    operation.  Note that this is weaker than making PM a Boolean algebra,
    which would be inherently non-constructive. *)
    predmonad_heyting_algegbra :
      forall {A} (P1 P2 P3: PM A),
        leqP (andP P1 P2) P3 <-> leqP P1 (impliesP P2 P3);

    (* Return in the predicate monad precisely characterizes return in M *)
    predmonad_return_return :
      forall {A} (x:A) m, m |= returnM x <-> m == returnM x

    (* FIXME: characterize bind!! *)

    (* FIXME: need to commute return and bind with logical operators! *)
  }.


End PredMonad.
