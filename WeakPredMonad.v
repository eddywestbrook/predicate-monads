
Load PredMonad.


(* The satisfiability order on monadic predicates, where leqM P1 P2 means that
anything satisfying P1 satisfies P2; we will require this to be a complete
lattice (meets and joins over arbitrary sets) below *)
Class PredMonadOrder (PM: Type -> Type) : Type :=
  leqP : forall {A}, relation (PM A).


(***
 *** Weak Predicate Monad Axioms (as a Typeclass)
 ***)

(* A weak predicate monad, where impliesP, forallP, and existsP are not quite
equivalent to their corresponding logical connectives; I think this becomes
equivalent to the standard PredMonad class if we require the topology to be
preregular (R1), meaning that every pair of non-equal monadic computations
satisfy, respectively, a pair of monadic predicates that are disjoint. *)

Class WeakPredMonad
      {M: Type -> Type} {PM : Type -> Type}
      {PredMonadRet:MonadRet PM} {PredMonadBind:MonadBind PM}
      {PredMonadEquiv:MonadEquiv PM}
      {MonadRet:MonadRet M} {MonadBind:MonadBind M} {MonadEquiv:MonadEquiv M}
      {PredMonadOrder:@PredMonadOrder PM}
      {PredMonadSatisfaction:@PredMonadSatisfaction M PM}
      {PredMonadForall:@PredMonadForall PM}
      {PredMonadExists:@PredMonadExists PM}
      {PredMonadImplication:@PredMonadImplication PM}
  : Prop :=
  {
    (* Both M and PM must be monads *)
    weakpredmonad_monad_M :> Monad M;
    weakpredmonad_monad_PM :> Monad PM;

    (* The satisfiability order is a partial order w.r.t. eqM *)
    weakpredmonad_leqP_preorder :> forall {A}, PreOrder (leqP (A:=A));
    weakpredmonad_leqP_antisymmetric :>
      forall {A}, Antisymmetric (eqM (A:=A)) leqP;
    weakpredmonad_leqP_proper :>
      forall {A}, Proper (eqM (A:=A) ==> eqM (A:=A) ==> impl) leqP;

    (* Satisfaction is monotone with respect to the satisfiability order *)
    weakpredmonad_satisfiesP_monotone :>
      forall {A}, Proper (eqM (A:=A) ==> leqP ==> impl) satisfiesP;

    (* Forall and exists are complete meet and join operators, respectively *)
    weakpredmonad_forallP_lower_bound :
      forall {A B} (f: A -> PM B) a, leqP (forallP f) (f a);
    weakpredmonad_forallP_greatest_lower_bound :
      forall {A B} (f: A -> PM B) P,
        (forall a, leqP P (f a)) -> leqP P (forallP f);
    weakpredmonad_existsP_upper_bound :
      forall {A B} (f: A -> PM B) a, leqP (f a) (existsP f);
    weakpredmonad_existsP_least_upper_bound :
      forall {A B} (f: A -> PM B) P,
        (forall a, leqP (f a) P) ->  leqP (existsP f) P;

    (* The fact that true always holds and false never does is equivalent to the
    existence, for each m, of predicates that m does and does not satisfy,
    respectively. We state the latter property as an axiom, and the former
    properties follow from them. *)
    weakpredmonad_separation :
      forall {A} (m:M A), exists P1 P2, m |= P1 /\ ~(m |= P2);

    (* Implication makes a predicate monad into a complete Heyting algebra,
    which means there is a Galois connection between implication and the andP
    operation.  Note that this is weaker than making PM a Boolean algebra,
    which would be inherently non-constructive. *)
    weakpredmonad_heyting_algegbra :
      forall {A} (P1 P2 P3: PM A),
        leqP (andP P1 P2) P3 <-> leqP P1 (impliesP P2 P3);

    (* Return in the predicate monad precisely characterizes return in M *)
    weakpredmonad_return_return :
      forall {A} (x:A) m, m |= returnM x <-> m == returnM x;

    weakpredmonad_bind_bind :
      forall {A B} (m:M B) (P: PM A) (Q: A -> PM B),
        m |= bindM P Q <->
        (exists (phi:A -> Prop) (m': M {x:A | phi x}) (f : A -> M B),
           (bindM m' (fun x => returnM (proj1_sig x))) |= P /\
           (forall x, phi x -> f x |= Q x) /\
           eqM m (bindM m' (fun x => f (proj1_sig x))))

    (* FIXME: need to commute return and bind with logical operators! *)
  }.


(***
 *** Theorems about predicate monads
 ***)

Section WeakPredMonad_thms.

Context `{WeakPredMonad}.

Theorem existsP_exists_weak {A B} m (P: A -> PM B) :
  (exists x, m |= P x) -> m |= existsP P.
  intro H0; destruct H0.
  apply (weakpredmonad_satisfiesP_monotone m m (reflexivity m) (P x));
    [ apply weakpredmonad_existsP_upper_bound | assumption ].
Qed.

Theorem forallP_forall_weak {A B} m (P: A -> PM B) :
  m |= forallP P -> forall x, m |= P x.
  intros.
  apply (weakpredmonad_satisfiesP_monotone m m (reflexivity m) (forallP P));
    [ apply weakpredmonad_forallP_lower_bound | assumption ].
Qed.

Theorem andP_and_weak {A} m (P1 P2: PM A) :
  m |= andP P1 P2 -> m |= P1 /\ m |= P2.
  intros; split.
  apply (weakpredmonad_satisfiesP_monotone m m (reflexivity m) (andP P1 P2));
    [ | assumption ].
  apply (weakpredmonad_forallP_lower_bound
           (fun (b:bool) => if b then P1 else P2) true); assumption.
  apply (weakpredmonad_satisfiesP_monotone m m (reflexivity m) (andP P1 P2));
    [ | assumption ].
  apply (weakpredmonad_forallP_lower_bound
           (fun (b:bool) => if b then P1 else P2) false); assumption.
Qed.


(* FIXME HERE *)
(*
Theorem impliesP_implies {A} m (P1 P2: PM A) :
  m |= impliesP P1 P2 -> m |= P1 -> m |= P2.
  intros.
*)

End WeakPredMonad_thms.
