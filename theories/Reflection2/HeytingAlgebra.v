(***
 *** Monads with Logical Structure, Including Implication
 ***)

Require Export PredMonad.Reflection2.Monad.

Class CompleteHeytingOps M `{OTypeF1 M} : Type :=
  { forallP: forall {A B} `{OType A} `{OType B}, (A -o> M B _) -o> M B _;
    existsP: forall {A B} `{OType A} `{OType B}, (A -o> M B _) -o> M B _;
    impliesP: forall {A} `{OType A}, Flip (M A _) -o> M A _ -o> M A _;
  }.

Definition andP `{CompleteHeytingOps} `{OType} : M A _ -o> M A _ -o> M A _ :=
  ofun (fun P1 =>
          ofun (fun P2 =>
                  forallP @o@ (ofun (fun b:bool =>
                                       oif @o@ b @o@ P1 @o@ P2)))).

Class CompleteHeyting M `{CompleteHeytingOps M} : Prop :=
  {
    (* M must be a monad *)
    (* monadset_monad_M :> Monad M; *)

    (* forallP is a complete meet operator. The laws for it being a lower bound
    and the greatest lower bound actually correspond to forall-elimination and
    forall-introduction rules, respectively. *)
    monadset_forallP_elim :
      forall {A B} `{OType A} `{OType B} (f: A -o> M B _) a,
        forallP @o@ f <o= f @o@ a;
    monadset_forallP_intro :
      forall {A B} `{OType A} `{OType B} (f: A -o> M B _) P,
        (forall a, P <o= f @o@ a) -> P <o= forallP @o@ f;

    (* existsP is a complete join operator. The laws for it being an upper bound
    and the least upper bound actually correspond to exists-introduction and
    exists-elimination rules, respectively. *)
    monadset_existsP_intro :
      forall {A B} `{OType A} `{OType B} (f: A -o> M B _) a,
        f @o@ a <o= existsP @o@ f;
    monadset_existsP_elim :
      forall {A B} `{OType A} `{OType B} (f: A -o> M B _) P,
        (forall a, f @o@ a <o= P) -> existsP @o@ f <o= P;

    (* impliesP is a right adjoint to andP, the laws for which correspond to
    implication introduction and generalization of implication elimination
    (where taking P1 = (impliesP P2 P3) yields the standard elimination rule) *)
    (* FIXME HERE: figure out how to write this!! *)
    monadset_impliesP_intro :
      forall {A} `{OType A} P1 P2 P3,
        andP @o@ P1 @o@ (unflip P2) <o= P3 -> P1 <o= impliesP @o@ P2 @o@ P3;
    monadset_impliesP_elim :
      forall {A} `{OType A} P1 P2 P3,
        P1 <o= impliesP @o@ (flip P2) @o@ P3 -> andP @o@ P1 @o@ P2 <o= P3;

    (* FIXME: need laws about how the combinators interact *)
  }.


(***
 *** The Equiv Type (FIXME HERE NOW: move this to OrderedType.v!)
 ***)

(* FIXME HERE NOW: move these to OrderedType *)
Instance ProperPair_flip A `{OType A} (x y:A) (prp:ProperPair A x y) :
  ProperPair (Flip A) (flip y) (flip x) := prp.

Instance ProperPair_unflip A `{OType A} x y (prp:ProperPair (Flip A) x y) :
  ProperPair A (unflip y) (unflip x) := prp.

(* FIXME HERE NOW: move all this to OrderedType.v! *)
Inductive Equiv A : Type := equiv (a:A).
Arguments equiv {A} a.

(* Project out the element of an Equiv *)
Definition unequiv {A} (f:Equiv A) : A := let (x) := f in x.

Instance OTEquiv A (R:OType A) : OType (Equiv A) :=
  {| ot_R := fun x y => unequiv x =o= unequiv y |}.
Proof.
  constructor; intro; intros.
  - reflexivity.
  - etransitivity; eassumption.
Defined.

Instance ProperPair_unequiv A `{OType A} x y (prp:ProperPair (Equiv A) x y) :
  ProperPair A (unequiv x) (unequiv y).
Proof.
  destruct prp; assumption.
Qed.

(* Project out the element of an Equiv and then flip it *)
Definition flip_unequiv {A} (f:Equiv A) : Flip A := flip (unequiv f).

Instance ProperPair_flip_unequiv A `{OType A} x y (prp:ProperPair (Equiv A) x y) :
  ProperPair (Flip A) (flip_unequiv x) (flip_unequiv y).
Proof.
  destruct prp; assumption.
Qed.

(* Map an Equiv to its flip *)
Program Definition flip_equiv `{OType} : Equiv A -o> Flip (Equiv A) :=
  ofun (fun x => flip x) (prp:=_).
Next Obligation.
  unfold OFunProper, ProperPair; intros. simpl.
  symmetry; assumption.
Defined.

(* FIXME HERE NOW: move this to OrderedType! *)
Definition flip_app_equiv {A B} `{OType A} `{OType B} :
  Flip (Equiv A -o> B) -o> Equiv A -o> Flip B :=
  ofun (fun f =>
          ofun (fun a =>
                  flip (unflip f @o@ unflip (flip_equiv @o@ a)))).




(***
 *** The Sets, which are almost a monad...
 ***)

(* Sets that are closed under the equivalence relation of A *)
Definition SetM A `{OType A} := Equiv A -o> Prop.

Instance OTypeF1_SetM : OTypeF1 SetM := fun _ _ => _.

Instance CompleteHeytingOps_SetM : CompleteHeytingOps SetM :=
  {|
    forallP :=
      fun A B _ _ =>
        ofun (fun P =>
                ofun (fun b =>
                        oforall @o@ ofun (fun a =>
                                            P @o@ a @o@ b)));
    existsP :=
      fun A B _ _ =>
        ofun (fun P =>
                ofun (fun b =>
                        oexists @o@ ofun (fun a =>
                                            P @o@ a @o@ b)));
    impliesP :=
      fun A _ =>
        ofun (fun S1 =>
                ofun (fun S2 =>
                        ofun (fun x => oimpl @o@ (flip_app_equiv @o@ S1 @o@ x)
                                             @o@ (S2 @o@ x))))
  |}.

Instance CompleteHeyting_SetM : CompleteHeyting SetM.
Proof.
  constructor; simpl; intros; intro.
  - assert (a1 =o= a2); [ split; simpl; [ | symmetry ]; apply H | ].
    rewrite <- H3; apply H0.
  - intro. apply (H _ _ _ H0 H3).
  - assert (a1 =o= a2); [ split; simpl; [ | symmetry ]; apply H | ].
    exists a. rewrite <- H3. assumption.
  - destruct H3. apply (H _ _ _ H0 H3).
  - intro. apply (H _ _ H0).
    intro b; destruct b; try assumption.
    assert (a1 =o= a2); [ split; simpl; [ | symmetry ]; apply H0 | ].
    rewrite H4; assumption.
  - apply (H _ _ H0); [ apply (H2 true) | ].
    assert (a1 =o= a2); [ split; simpl; [ | symmetry ]; apply H0 | ].
    rewrite <- H3. apply (H2 false).
Qed.


(* NOTE: the above definition of SetM does not form a monad! The key problem is
return, because it needs to be Proper, i.e., it needs to be:

>> returnM x := { y | y <o= x }

If we define bind the normal way for sets, like this:

>> bindM S f := union { f x | x in S }

then we end up with

>> bindM S returnM =o= downward_closure S =o= { y | exists x in S. y <o= x }

which violates the return-bind monad law:

>> bindM S returnM =o= S *)
