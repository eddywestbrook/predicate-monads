Require Export PredMonad.Reflection2.Monad.

(***
 *** The Predicate Monad Class
 ***)

(* FIXME HERE NOW: move these to OrderedType *)
Instance ProperPair_flip A `{OType A} (x y:A) (prp:ProperPair A x y) :
  ProperPair (Flip A) (flip y) (flip x) := prp.

Instance ProperPair_unflip A `{OType A} x y (prp:ProperPair (Flip A) x y) :
  ProperPair A (unflip y) (unflip x) := prp.

(* FIXME HERE NOW: move this to OrderedType! *)
Definition flip_app {A B} `{OType A} `{OType B} :
  Flip (A -o> B) -o> Flip A -o> Flip B :=
  ofun (fun f => ofun (fun a => flip (unflip f @o@ unflip a)) (prp:=_)) (prp:=_).

Program Definition flip_abs {A B} `{OType A} `{OType B} :
  (Flip A -o> Flip B) -o> Flip (A -o> B) :=
  ofun (fun f => flip (ofun (fun x => unflip (f @o@ flip x)))).

Definition double_flip {A} `{OType A} : A -o> Flip (Flip A) :=
  ofun (fun x => flip (flip x)).

(* FIXME: the universe constraints on M and PM could be different...? *)
Class PredMonadOps M PM `{MonadOps M} `{MonadOps PM} :=
  { forallP: forall {A B} `{OType A} `{OType B}, (A -o> PM B _) -o> PM B _;
    existsP: forall {A B} `{OType A} `{OType B}, (A -o> PM B _) -o> PM B _;
    impliesP: forall {A} `{OType A}, Flip (PM (Flip A) _) -o> PM A _ -o> PM A _;
    liftP: forall {A} `{OType A}, M A _ -o> PM A _;
    invertP: forall {A} `{OType A}, PM A _ -o> Flip (PM (Flip A) _)
  }.

Definition andP `{PredMonadOps} `{OType} : PM A _ -o> PM A _ -o> PM A _ :=
  ofun (fun P1 =>
          ofun (fun P2 =>
                  forallP @o@ (ofun (fun b:bool =>
                                       oif @o@ b @o@ P1 @o@ P2)))).


Definition uninvertP `{PredMonadOps} `{OType} : Flip (PM (Flip A) _) -o> PM A _ :=
  ofun (fun m =>
          bindM @o@ unflip (invertP @o@ unflip m)
                @o@ ofun (fun x => returnM @o@ unflip (unflip x))).


Class PredMonad `{PredMonadOps} : Prop :=
  {
    (* Both M and PM must be monads *)
    predmonad_monad_M :> Monad M;
    predmonad_monad_PM :> Monad PM;

    (* forallP is a complete meet operator. The laws for it being a lower bound
    and the greatest lower bound actually correspond to forall-elimination and
    forall-introduction rules, respectively. *)
    predmonad_forallP_elim :
      forall {A B} `{OType A} `{OType B} (f: A -o> PM B _) a,
        forallP @o@ f <o= f @o@ a;
    predmonad_forallP_intro :
      forall {A B} `{OType A} `{OType B} (f: A -o> PM B _) P,
        (forall a, P <o= f @o@ a) -> P <o= forallP @o@ f;

    (* existsP is a complete join operator. The laws for it being an upper bound
    and the least upper bound actually correspond to exists-introduction and
    exists-elimination rules, respectively. *)
    predmonad_existsP_intro :
      forall {A B} `{OType A} `{OType B} (f: A -o> PM B _) a,
        f @o@ a <o= existsP @o@ f;
    predmonad_existsP_elim :
      forall {A B} `{OType A} `{OType B} (f: A -o> PM B _) P,
        (forall a, f @o@ a <o= P) -> existsP @o@ f <o= P;

    (* impliesP is a right adjoint to andP, the laws for which correspond to
    implication introduction and generalization of implication elimination
    (where taking P1 = (impliesP P2 P3) yields the standard elimination rule) *)
    (* FIXME HERE: figure out how to write this!! *)
    predmonad_impliesP_intro :
      forall {A} `{OType A} P1 P2 P3,
        andP @o@ P1 @o@ (uninvertP @o@ P2) <o= P3 -> P1 <o= impliesP @o@ P2 @o@ P3;
    predmonad_impliesP_elim :
      forall {A} `{OType A} P1 P2 P3,
        P1 <o= impliesP @o@ (invertP @o@ P2) @o@ P3 -> andP @o@ P1 @o@ P2 <o= P3;

    (* laws about liftP *)
    predmonad_liftP_return :
      forall {A} `{OType A} (a:A),
        liftP @o@ (returnM @o@ a) =o= returnM @o@ a;
    predmonad_liftP_bind :
      forall {A B} `{OType A} `{OType B} m (f:A -o> M B _),
        liftP @o@ (bindM @o@ m @o@ f)
        =o= bindM @o@ (liftP @o@ m) @o@ (ofun (fun x => liftP @o@ (f @o@ x)));

    (* invertP and uninvertP form a bijection *)
    (*
    predmonad_invertP_double :
      forall {A} `{OType A} (m:PM A _),
        invertP @o@ unflip (invertP @o@ m) =o=
        flip (bindM @o@ m @o@ ofun (fun x =>
                                      returnM @o@ (double_flip @o@ x)));

    (* invertP commutes with the other operators *)
    predmonad_invertP_return :
      forall {A} `{OType A} (a:A),
        invertP @o@ (returnM @o@ a) =o=
        flip (returnM @o@ (flip a));
    predmonad_invertP_bind :
      forall {A B} `{OType A} `{OType B} (m:PM A _) f,
        invertP @o@ (bindM @o@ m @o@ f) =o=
        flip (bindM @o@ (unflip (invertP @o@ m))
                    @o@ (ofun (fun x => unflip (invertP @o@ (f @o@ unflip x)))));
    predmonad_invertP_forallP :
      forall {A B} `{OType A} `{OType B} P,
        invertP @o@ (forallP @o@ P) =o=
        flip (forallP @o@ ofun (fun x => unflip (invertP @o@ (P @o@ unflip x))))
     *)

    (* FIXME: need laws about how the combinators interact *)

  }.


(***
 *** Defined Predicate Monad Operators
 ***)

(* We define m |= P as holding iff (liftP m) entails P *)
Definition satisfiesP `{PredMonadOps} `{OType} (m:M A _) (P:PM A _) :=
  liftP @o@ m <o= P.

(* Notation for satisfaction *)
Infix "|=" := satisfiesP (at level 80).

(* Disjunction is definable in terms of the existential *)
Definition orP `{PredMonadOps} `{OType} : PM A _ -o> PM A _ -o> PM A _ :=
  ofun (fun P1 =>
          ofun (fun P2 =>
                  existsP @o@ (ofun (fun b:bool => oif @o@ b @o@ P1 @o@ P2)))).

(* True and false, which correspond to top and bottom, respectively *)
Definition trueP `{PredMonadOps} `{OType} : PM A _ :=
  existsP @o@ (ofun (fun pm => pm)).
Definition falseP `{PredMonadOps} `{OType} : PM A _ :=
  forallP @o@ (ofun (fun pm => pm)).

(* Negation, which (as in normal Coq) is implication of false *)
Definition notP `{PredMonadOps} `{OType} : Flip (PM (Flip A) _) -o> PM A _ :=
  ofun (fun P => impliesP @o@ P @o@ falseP).

(* An assertion inside a predicate monad *)
Definition assertP `{PredMonadOps} (P:Prop) : PM unit _ :=
  existsP @o@ (ofun (fun pf:P => trueP)).


(***
 *** The Set monad as a predicate monad for the Identity monad
 ***)


FIXME HERE NOW: cannot write invertSet constructively! It requires negation!

(* An existential with both a positive and a negative component *)
Program Definition oexists2 `{OType} : (A -o> Prop) -o>
                                       (Flip A -o> Prop) -o> Prop :=
  ofun (fun P1 =>
          ofun (fun P2 =>
                  exists2 x, P1 @o@ x & P2 @o@ flip x) (prp:=_)) (prp:=_).
Next Obligation.
  intro pf; destruct pf as [z pf1 pf2].
  exists z; try assumption. apply (H0 _ _ (reflexivity _)). assumption.
Defined.
Next Obligation.
  intro pf. destruct pf as [z pf1 pf2].
  exists z; [ apply (H0 _ _ (reflexivity _)) |
              apply (H1 _ _ (reflexivity _)) ]; assumption.
Defined.

(* The type of downward-closed sets over a carrier type A *)
Definition SetM A `{OType A} : Type := Flip A -o> Prop.

(* SetM is an ordered type functor *)
Instance OTypeF_SetM : OTypeF1 SetM := fun _ ot => _.

Instance MonadOps_SetM : MonadOps SetM :=
  {| returnM :=
       fun A _ =>
         ofun (fun (x:A) => ofun (fun (y:Flip A) => oR @o@ y @o@ x));
     bindM :=
       fun A B _ _ =>
         ofun (fun m =>
                 ofun (fun f =>
                         ofun (fun (y:Flip B) =>
                                 oexists2 @o@ (ofun (fun x => f @o@ x @o@ y))
                                          @o@ m)))
  |}.

Instance Monad_SetM : Monad SetM.
Proof.
  constructor; intros.
  - split; intros a1 a2 Ra pf.
    + destruct pf as [ z pf1 pf2].
      rewrite <- Ra. rewrite <- pf2. assumption.
    + simpl. exists x; try reflexivity. rewrite <- Ra. assumption.
  - simpl; split; intros a1 a2 Ra pf.
    + destruct pf as [ z pf1 pf2].
      refine (pfun_Proper m _ _ _ _); [ | eassumption ].
      etransitivity; try eassumption. apply pf1.
    + exists (unflip a1); try assumption.
      destruct a1. simpl. assumption.
  - split; intros c1 c2 Rc pf.
    + destruct pf as [b pfB pf]. destruct pf as [a pfA pf].
      exists a; try assumption.
      exists b; try assumption.
      simpl. rewrite <- Rc. assumption.
    + destruct pf as [a pf pfA]. destruct pf as [b pfB pf].
      exists b; [ simpl; rewrite <- Rc; assumption | ].
      exists a; assumption.
Qed.


Definition impliesSet `{OType} : Flip (SetM (Flip A)) -o> SetM A -o> SetM A :=
  ofun (fun S1 =>
          ofun (fun S2 =>
                  ofun (fun (x:Flip A) =>
                          oimpl @o@ flip (unflip S1 @o@ flip x)
                                @o@ (S2 @o@ x)))).

Program Definition invertSet `{OType} : SetM A -o> Flip (SetM (Flip A)) :=
  ofun (fun S =>
          flip (ofun (fun x =>))).


Instance PredMonadOps_SetM : PredMonadOps Identity SetM :=
  {| forallP :=
       fun A B _ _ =>
         ofun (fun P =>
                 ofun (fun (b:Flip B) =>
                         oforall @o@ ofun (fun a => P @o@ a @o@ b)));
     existsP :=
       fun A B _ _ =>
         ofun (fun P =>
                 ofun (fun b =>
                         oexists @o@ ofun (fun a => P @o@ a @o@ b)));
     impliesP :=
       fun A _ =>
         ofun (fun S1 =>
          ofun (fun S2 =>
                  ofun (fun (x:Flip A) =>
                          oimpl @o@ (flip_app @o@ S1 @o@ flip (flip x))
                                @o@ (S2 @o@ x))));
     liftP := fun A _ => returnM;
     invertP :=
       fun A _ => ofun (fun S =>)
  |}.



FIXME HERE NOW: old stuff

(* The type of downward-closed sets over a carrier type A *)
Definition SetM A `{OType A} : Type := Flip A -o> Prop.

Instance OTypeF1_SetM : OTypeF1 SetM := fun _ _ => _.

Instance MonadOps_SetM : MonadOps SetM :=
    {| returnM :=
         fun A _ =>
           ofun (fun (x:A) => (ofun (fun (y:Flip A) => oR @o@ y @o@ x)));
     bindM :=
       fun A B _ _ =>
         ofun (fun m =>
                 ofun (fun f =>
                         ofun (fun (y:Flip B) =>
                                 oexists2 @o@ (ofun (fun x => f @o@ x @o@ y))
                                          @o@ m)))
  |}.

Instance Monad_SetM : Monad SetM.
Proof.
  constructor; intros.
  - split; intros a1 a2 Ra pf.
    + destruct pf as [ z pf1 pf2].
      rewrite <- Ra. rewrite <- pf2. assumption.
    + simpl. exists x; try reflexivity. rewrite <- Ra. assumption.
  - simpl; split; intros a1 a2 Ra pf.
    + destruct pf as [ z pf1 pf2].
      refine (pfun_Proper m _ _ _ _); [ | eassumption ].
      etransitivity; try eassumption. apply pf1.
    + exists (unflip a1); try assumption.
      destruct a1. simpl. assumption.
  - split; intros c1 c2 Rc pf.
    + destruct pf as [b pfB pf]. destruct pf as [a pfA pf].
      exists a; try assumption.
      exists b; try assumption.
      simpl. rewrite <- Rc. assumption.
    + destruct pf as [a pf pfA]. destruct pf as [b pfB pf].
      exists b; [ simpl; rewrite <- Rc; assumption | ].
      exists a; assumption.
Qed.


Definition completeSet `{OType} : SetM A := ofun (fun _ => True).

Definition intersectSet {A B} `{OType A} `{OType B} : (A -o> SetM B) -o> SetM B :=
  ofun (fun P =>
          ofun (fun y =>
                  oforall @o@ ofun (fun x => P @o@ x @o@ y))).

Definition unionSet {A B} `{OType A} `{OType B} : (A -o> SetM B) -o> SetM B :=
  ofun (fun P =>
          ofun (fun y =>
                  oexists @o@ ofun (fun x => P @o@ x @o@ y))).


Definition IdentityP A `{OType A} : Type := Flip (SetM A) * SetM A.

Instance OTypeF_IdentityP : OTypeF1 IdentityP := fun _ _ => _.

Hint Mode ProperPair + + + - : typeclass_instances.

Definition flipBindM {A B} `{OType A} `{OType B} : Flip (SetM A) -o>
                                                   Flip (A -o> SetM B) -o>
                                                   Flip (SetM B) :=
  ofun (fun m =>
          ofun (fun f =>
                  flip (bindM @o@ unflip m @o@ unflip f))).

Instance MonadOps_IdentityP : MonadOps IdentityP :=
  {| returnM :=
       fun A _ =>
         ofun (fun (x:A) => (flip completeSet ,o, returnM @o@ x));
     bindM :=
       fun A B _ _ =>
         ofun (fun m =>
                 ofun (fun f =>
                         (flip
                            (bindM @o@ unflip (ofst @o@ m) @o@
                                   ofun (fun x => unflip (ofst @o@ (f @o@ x))))
                          ,o,
                          (bindM @o@ (osnd @o@ m) @o@
                                 ofun (fun x => (osnd @o@ (f @o@ x)))))))
  |}.










FIXME HERE NOW: we would need a proper forall type for the following to work

Record IdentityP `{OType} : Type :=
  { idpL : Flip (A -o> Prop);
    idpR : (A -o> Prop);
    idpPf : oR @o@ idpL @o@ idpR }.

Instance OTypeF_IdentityP : OTypeF1 (@IdentityP) :=
  fun A _ =>
    {| ot_R := fun P1 P2 => idpL P1 <o= idpL P2 /\ idpR P1 <o= idpR P2 |}.
Proof.
  constructor.
  - intro x; split; reflexivity.
  - intros x y z [RxyL RxyR] [RyzL RyzR]; split; etransitivity; eassumption.
Defined.

Definition mkIdP `{OType} : Flip (A -o> Prop) -o> (A -o> Prop) -o> 

Instance MonadOps_SetM : MonadOps SetM :=
  {| returnM :=
       fun A _ =>
         ofun (fun (x:A) => ofun (fun (y:Flip A) => oR @o@ y @o@ x));
     bindM :=
       fun A B _ _ =>
         ofun (fun m =>
                 ofun (fun f =>
                         ofun (fun (y:Flip B) =>
                                 oexists2 @o@ (ofun (fun x => f @o@ x @o@ y))
                                          @o@ m)))
  |}.






FIXME HERE NOW: old stuff

(* The type of downward-closed sets over a carrier type A *)
Definition SetM A `{OType A} : Type := Flip A -o> Prop.

(* SetM is an ordered type functor *)
Instance OTypeF_SetM : OTypeF1 SetM := fun _ ot => _.

(* An existential with both a positive and a negative component *)
Program Definition oexists2 `{OType} : (A -o> Prop) -o>
                                       (Flip A -o> Prop) -o> Prop :=
  ofun (fun P1 =>
          ofun (fun P2 =>
                  exists2 x, P1 @o@ x & P2 @o@ flip x) (prp:=_)) (prp:=_).
Next Obligation.
  intro pf; destruct pf as [z pf1 pf2].
  exists z; try assumption. apply (H0 _ _ (reflexivity _)). assumption.
Defined.
Next Obligation.
  intro pf. destruct pf as [z pf1 pf2].
  exists z; [ apply (H0 _ _ (reflexivity _)) |
              apply (H1 _ _ (reflexivity _)) ]; assumption.
Defined.


Instance MonadOps_SetM : MonadOps SetM :=
  {| returnM :=
       fun A _ =>
         ofun (fun (x:A) => ofun (fun (y:Flip A) => oR @o@ y @o@ x));
     bindM :=
       fun A B _ _ =>
         ofun (fun m =>
                 ofun (fun f =>
                         ofun (fun (y:Flip B) =>
                                 oexists2 @o@ (ofun (fun x => f @o@ x @o@ y))
                                          @o@ m)))
  |}.

Instance Monad_SetM : Monad SetM.
Proof.
  constructor; intros.
  - split; intros a1 a2 Ra pf.
    + destruct pf as [ z pf1 pf2].
      rewrite <- Ra. rewrite <- pf2. assumption.
    + simpl. exists x; try reflexivity. rewrite <- Ra. assumption.
  - simpl; split; intros a1 a2 Ra pf.
    + destruct pf as [ z pf1 pf2].
      refine (pfun_Proper m _ _ _ _); [ | eassumption ].
      etransitivity; try eassumption. apply pf1.
    + exists (unflip a1); try assumption.
      destruct a1. simpl. assumption.
  - split; intros c1 c2 Rc pf.
    + destruct pf as [b pfB pf]. destruct pf as [a pfA pf].
      exists a; try assumption.
      exists b; try assumption.
      simpl. rewrite <- Rc. assumption.
    + destruct pf as [a pf pfA]. destruct pf as [b pfB pf].
      exists b; [ simpl; rewrite <- Rc; assumption | ].
      exists a; assumption.
Qed.

Program Definition flip_abs {A B} `{OType A} `{OType B} :
  (Flip A -o> Flip B) -o> Flip (A -o> B) :=
  ofun (fun f => flip (ofun (fun x => unflip (f @o@ flip x)))).


Instance PredMonadOps_SetM : PredMonadOps Identity SetM :=
  {| forallP :=
       fun A B _ _ =>
         ofun (fun P =>
                 ofun (fun (b:Flip B) =>
                         oforall @o@ ofun (fun a => P @o@ a @o@ b)));
     existsP :=
       fun A B _ _ =>
         ofun (fun P =>
                 ofun (fun b =>
                         oexists @o@ ofun (fun a => P @o@ a @o@ b)));
     impliesP :=
       fun A _ =>
         ofun (fun (P1:Flip (Flip A -o> Prop)) =>
                 ofun (fun P2 =>
                         ofun (fun a =>
                                 oimpl @o@ (flip_app @o@ P1 @o@ flip a)
                                       @o@ (P2 @o@ a))));
     liftP :=
       fun A _ => returnM;

  |}.

     invertP :=
       fun A _ =>
         ofun (fun (P: Flip A -o> Prop) =>
                 flip_abs @o@ (ofun (fun (a:Flip (Flip (Flip A))) => flip (P @o@ unflip (unflip a))) (prp:=_)))
              (prp:=_)
              |}.
Proof.
  - intros a1 a2 Ra pf. refine (pfun_Proper P _ _ _ _); try eassumption.
    simpl in Ra.
    apply Ra.

  - intros a1 a2 Ra pf12 pf1. simpl in pf12. simpl in pf1.

 unfold ProperPair in Ra.
    simpl in pf1.
    rewrite <- Ra. apply pf12. 

apply pf12.

intro.

: forall {A} `{OType A}, Flip (PM A _) -o> PM A _ -o> PM A _;
    liftP: forall {A} `{OType A}, M A _ -o> PM A _
  }.



FIXME HERE NOW: old stuff

Inductive Equiv A : Type := equiv (a:A).
Arguments equiv {A} a.

Definition unequiv {A} (f:Equiv A) : A := let (x) := f in x.

Definition flip_unequiv {A} (f:Equiv A) : Flip A := flip (unequiv f).

Instance OTEquiv A (R:OType A) : OType (Equiv A) :=
  {| ot_R := fun x y => unequiv y =o= unequiv x |}.
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

Instance ProperPair_unequiv_flip A `{OType A} x y (prp:ProperPair (Equiv A) x y) :
  ProperPair (Flip A) (flip_unequiv x) (flip_unequiv y).
Proof.
  destruct prp; assumption.
Qed.

(* The double existential combinator as an ordered function *)
Program Definition oexists2 `{OType} : (A -o> Prop) -o> (A -o> Prop) -o> Prop :=
  ofun (fun P =>
          ofun (fun Q => exists2 x, P @o@ x & Q @o@ x) (prp:=_)) (prp:=_).
Next Obligation.
  intro pf; destruct pf as [z pf1 pf2].
  exists z; try assumption. apply (H0 _ _ (reflexivity _) pf2).
Defined.
Next Obligation.
  intro pf; destruct pf as [z pf1 pf2].
  exists z; [ apply (H0 _ _ (reflexivity _) pf1)
            | apply (H1 _ _ (reflexivity _) pf2) ].
Defined.


Inductive SetM A `{OType A} : Type :=
  mkSetM (P:Equiv A -o> Prop).

Arguments mkSetM {A _} P.

Definition inSetM `{OType} (S:SetM A) (a:A) : Prop :=
  let (P) := S in P @o@ equiv a.

(* The ordering on sets is a covering property, where the bigger set contains a
bigger element for each element of the smaller one *)
Instance OType_SetM `{OType} : OType (SetM A) :=
  {| ot_R := fun (S1 S2:SetM A) =>
               forall a1, inSetM S1 a1 ->
                          exists2 a2, a1 <o= a2 & inSetM S2 a2 |}.
Proof.
  constructor; intro; intros.
  - exists a1; [ reflexivity | assumption ].
  - destruct (H0 a1 H2) as [a2]. destruct (H1 a2 H4) as [a3].
    exists a3; try assumption. etransitivity; eassumption.
Defined.

Instance OTypeF_SetM : OTypeF1 SetM := fun _ _ => _.

(* Set comprehension as a proper function *)
Program Definition setCompr `{OType} : (Equiv A -o> Prop) -o> SetM A :=
  ofun mkSetM (prp:=_).
Next Obligation.
  exists a1; try reflexivity.
  apply (H0 _ _ (reflexivity _) H1).
Defined.

(* Whether an object is "covered" by something larger than it in a set *)
Program Definition setCovers `{OType} : SetM A -o> Flip A -o> Prop :=
  ofun (fun S =>
          ofun (fun x => exists2 y, unflip x <o= y & inSetM S y) (prp:=_)) (prp:=_).
Next Obligation.
  intro. destruct H1. exists x0; try assumption. etransitivity; eassumption.
Defined.
Next Obligation.
  intro. destruct H2. destruct (H0 _ H3).
  exists x1; try assumption.
  etransitivity; try eassumption. etransitivity; eassumption.
Defined.

Program Definition setSingleton `{OType} : A -o> SetM A :=
  ofun (fun x => mkSetM (ofun (fun y => unequiv y =o= x) (prp:=_))) (prp:=_).
Next Obligation.
  intro. etransitivity; eassumption.
Defined.
Next Obligation.
  exists y; try reflexivity. rewrite H1. assumption.
Defined.


Instance MonadOps_SetM : MonadOps SetM :=
  {| returnM := fun A _ => setSingleton;
     bindM :=
       fun A B _ _ =>
         ofun (fun S =>
                 ofun (fun f =>
                         setCompr
                           @o@
                           (ofun (fun y =>
                                    oexists2
                                      @o@ (ofun (fun x =>
                                                   setCovers @o@ S
                                                             @o@ flip_unequiv x))
                                      @o@ (ofun (fun x =>
                                                   setCovers @o@ (f @o@ unequiv x)
                                                             @o@ flip_unequiv y
                           ))))))
  |}.

Instance Monad_SetM : Monad SetM.
Proof.
  constructor; intros.
  - split; intros b inb.
    + destruct inb. destruct H0 as [b1].
      destruct 


FIXME HERE NOW: old stuff below


(* The set monad over a carrier type A *)
Definition SetM A `{OType A} : Type := Equiv A -o> Prop.

Instance OTypeF1_SetM : OTypeF1 SetM := fun _ _ => _.

(* Form the set containing all elements below x in the A ordering *)
Definition downward_closure `{OType} : A -o> SetM A :=
  ofun (fun (x:A) => ofun (fun (y:Equiv A) => oR @o@ flip_unequiv y @o@ x)).

(* Ordered type relations are themselves ordered propositional functions *)
Program Definition oeq `{OType} : Equiv A -o> Equiv A -o> Prop :=
  ofun (fun x =>
          ofun (fun y => ot_equiv (unequiv x) (unequiv y)) (prp:=_)) (prp:=_).
Next Obligation.
  intro. symmetry in H0. etransitivity; eassumption.
Defined.
Next Obligation.
  intro. symmetry in H1. etransitivity; try eassumption.
  etransitivity; eassumption.
Defined.

(* The double existential combinator as an ordered function *)
Program Definition oexists2 `{OType} : (A -o> Prop) -o> (A -o> Prop) -o> Prop :=
  ofun (fun P =>
          ofun (fun Q => exists2 x, P @o@ x & Q @o@ x) (prp:=_)) (prp:=_).
Next Obligation.
  intro pf; destruct pf as [z pf1 pf2].
  exists z; try assumption. apply (H0 _ _ (reflexivity _) pf2).
Defined.
Next Obligation.
  intro pf; destruct pf as [z pf1 pf2].
  exists z; [ apply (H0 _ _ (reflexivity _) pf1)
            | apply (H1 _ _ (reflexivity _) pf2) ].
Defined.


Definition bind_SetM {A B} `{OType A} `{OType B} : SetM A -o> (A -o> SetM B) -o>
                                                   SetM B :=
  ofun (fun S =>
          ofun (fun f =>
                  ofun (fun y =>
                          oexists2 @o@ S @o@
                                   (ofun (fun x => f @o@ unequiv x @o@ y))))).

Instance MonadOps_SetM : MonadOps SetM :=
  {| returnM := fun A _ => downward_closure;
     bindM :=
       fun A B _ _ => bind_SetM
  |}.

Instance Monad_SetM : Monad SetM.
Proof.
  constructor; intros; split.
  - intros b1 b2 Rb inb. destruct inb as [a].
    simpl in H; rewrite <- H. rewrite <- Rb. apply H0.
  - intros b1 b2 Rb inb. simpl. exists (equiv x); try reflexivity.
    rewrite <- Rb. assumption.
  - intros a1 a2 Ra inm. destruct inm as [x]. simpl in H0.





FIXME HERE NOW: old stuff below

Inductive SetM A `{OType A} : Type :=
  mkSetM (P:A -> Prop).

Arguments mkSetM {A _} P.

Definition inSetM `{OType} (S:SetM A) : A -> Prop :=
  let (P) := S in P.

(* The ordering on sets is a covering property, where the bigger set contains a
bigger element for each element of the smaller one *)
Instance OType_SetM `{OType} : OType (SetM A) :=
  {| ot_R := fun (S1 S2:SetM A) =>
               forall a1, inSetM S1 a1 ->
                          exists2 a2, a1 <o= a2 & inSetM S2 a2 |}.
Proof.
  constructor; intro; intros.
  - exists a1; [ reflexivity | assumption ].
  - destruct (H0 a1 H2) as [a2]. destruct (H1 a2 H4) as [a3].
    exists a3; try assumption. etransitivity; eassumption.
Defined.

Instance OTypeF_SetM : OTypeF1 SetM := fun _ _ => _.

(* Form the set containing all elements  *)
Program Definition downward_closure `{OType} : A -o> SetM A :=
  ofun (fun x => mkSetM (fun y => x = y)) (prp:=_).
Next Obligation.
  exists y; [ assumption | reflexivity ].
Defined.

(*
Program Definition singleton_SetM `{OType} : A -o> SetM A :=
  ofun (fun x => mkSetM (fun y => x = y)) (prp:=_).
Next Obligation.
  exists y; [ assumption | reflexivity ].
Defined.
*)

(*
Program Definition map_SetM {A B} `{OType A} `{OType B} :
  (A -o> B) -o> SetM A -o> SetM B :=
  ofun (fun f =>
          ofun (fun S =>
                  mkSetM (fun y => exists2 x:A, inSetM S x & y = f @o@ x)) (prp:=_))
       (prp:=_).
Next Obligation.
  destruct (H1 _ H3).
  exists (f @o@ x0); [ apply pfun_Proper; assumption | ].
  exists x0; [ assumption | reflexivity ].
Defined.
Next Obligation.
*)

Instance MonadOps_SetM : MonadOps SetM :=
  {| returnM :=
       fun A _ => singleton_SetM;
     bindM :=
       fun A B _ _ =>
         ofun (fun m =>
                 ofun (fun f =>
                         mkSetM (fun y =>
                                   exists2 x:A, inSetM m x & inSetM (f @o@ x) y))
              (prp:=_)) (prp:=_)
  |}.
Proof.
  - intros f1 f2 Rf b1 inb1. destruct inb1 as [a ina f1ab].
    destruct (Rf a a (reflexivity a) b1 f1ab) as [b2 Rb inb2].
    exists b2; try assumption. simpl.
    exists a; assumption.
  - intros S1 S2 RS f1 f2 Rf b1 inb1. simpl in * |- *.
    destruct inb1 as [a1 ina1 inf1ab].
    destruct (RS _ ina1) as [a2 Ra ina2].
    destruct (Rf _ _ Ra _ inf1ab) as [b2 Rb inb2].
    exists b2; try assumption.
    exists a2; try assumption.
Defined.    

Instance Monad_SetM : Monad SetM.
Proof.
  constructor; intros; split; simpl; intros.
  - destruct H. rewrite H. exists a1; [ reflexivity | assumption ].
  - exists a1; try reflexivity. exists x; try reflexivity. assumption.
  - destruct H. rewrite <- H0. exists x; [ reflexivity | assumption ].
  - exists a1; try reflexivity. exists a1; try reflexivity. assumption.
  - destruct H as [b]. destruct H as [a].
    exists a1; try reflexivity. exists a; try assumption.
    exists b; assumption.
  - destruct H as [a]. destruct H0 as [b]. exists a1; try reflexivity.
    exists b; try assumption. exists a; assumption.
Qed.


Instance PredMonadOps_SetM : PredMonadOps Identity SetM :=
  {| forallP :=
       fun A B _ _ =>
         ofun (fun P => mkSetM (fun y => forall x, inSetM (P @o@ x) y))
              (prp:=_);
     existsP :=
       fun A B _ _ =>
         ofun (fun P => mkSetM (fun y => exists x, inSetM (P @o@ x) y))
              (prp:=_);
     impliesP :=
       fun A _ =>
         ofun (fun P1 =>
                 ofun (fun P2 =>
                         mkSetM (fun a => inSetM (unflip P1) a -> inSetM P2 a))
                      (prp:=_))
              (prp:=_);
     liftP :=
       fun A _ => singleton_SetM;
  |}.
Proof.
  - simpl; intros P1 P2 RP b1 inb1.



FIXME HERE NOW: old stuff below!


(* The type of downward-closed sets over a carrier type A *)
Definition SetM A `{OType A} : Type := Flip A -o> Prop.

(* SetM is an ordered type functor *)
Instance OTypeF_SetM : OTypeF1 SetM := fun _ ot => _.

(* An existential with both a positive and a negative component *)
Program Definition oexists2 `{OType} : (A -o> Prop) -o>
                                       (Flip A -o> Prop) -o> Prop :=
  ofun (fun P1 =>
          ofun (fun P2 =>
                  exists2 x, P1 @o@ x & P2 @o@ flip x) (prp:=_)) (prp:=_).
Next Obligation.
  intro pf; destruct pf as [z pf1 pf2].
  exists z; try assumption. apply (H0 _ _ (reflexivity _)). assumption.
Defined.
Next Obligation.
  intro pf. destruct pf as [z pf1 pf2].
  exists z; [ apply (H0 _ _ (reflexivity _)) |
              apply (H1 _ _ (reflexivity _)) ]; assumption.
Defined.


Instance MonadOps_SetM : MonadOps SetM :=
  {| returnM :=
       fun A _ =>
         ofun (fun (x:A) => ofun (fun (y:Flip A) => oR @o@ y @o@ x));
     bindM :=
       fun A B _ _ =>
         ofun (fun m =>
                 ofun (fun f =>
                         ofun (fun (y:Flip B) =>
                                 oexists2 @o@ (ofun (fun x => f @o@ x @o@ y))
                                          @o@ m)))
  |}.

Instance Monad_SetM : Monad SetM.
Proof.
  constructor; intros.
  - split; intros a1 a2 Ra pf.
    + destruct pf as [ z pf1 pf2].
      rewrite <- Ra. rewrite <- pf2. assumption.
    + simpl. exists x; try reflexivity. rewrite <- Ra. assumption.
  - simpl; split; intros a1 a2 Ra pf.
    + destruct pf as [ z pf1 pf2].
      refine (pfun_Proper m _ _ _ _); [ | eassumption ].
      etransitivity; try eassumption. apply pf1.
    + exists (unflip a1); try assumption.
      destruct a1. simpl. assumption.
  - split; intros c1 c2 Rc pf.
    + destruct pf as [b pfB pf]. destruct pf as [a pfA pf].
      exists a; try assumption.
      exists b; try assumption.
      simpl. rewrite <- Rc. assumption.
    + destruct pf as [a pf pfA]. destruct pf as [b pfB pf].
      exists b; [ simpl; rewrite <- Rc; assumption | ].
      exists a; assumption.
Qed.

Program Definition flip_abs {A B} `{OType A} `{OType B} :
  (Flip A -o> Flip B) -o> Flip (A -o> B) :=
  ofun (fun f => flip (ofun (fun x => unflip (f @o@ flip x)))).


Instance PredMonadOps_SetM : PredMonadOps Identity SetM :=
  {| forallP :=
       fun A B _ _ =>
         ofun (fun P =>
                 ofun (fun (b:Flip B) =>
                         oforall @o@ ofun (fun a => P @o@ a @o@ b)));
     existsP :=
       fun A B _ _ =>
         ofun (fun P =>
                 ofun (fun b =>
                         oexists @o@ ofun (fun a => P @o@ a @o@ b)));
     impliesP :=
       fun A _ =>
         ofun (fun P1 =>
                 ofun (fun P2 =>
                         ofun (fun a =>
                                 oimpl @o@ (flip (unflip P1 @o@ a))
                                       @o@ (P2 @o@ a))));
     liftP :=
       fun A _ => returnM;

  |}.

     invertP :=
       fun A _ =>
         ofun (fun (P: Flip A -o> Prop) =>
                 flip_abs @o@ (ofun (fun (a:Flip (Flip (Flip A))) => flip (P @o@ unflip (unflip a))) (prp:=_)))
              (prp:=_)
              |}.
Proof.
  - intros a1 a2 Ra pf. refine (pfun_Proper P _ _ _ _); try eassumption.
    simpl in Ra.
    apply Ra.

  - intros a1 a2 Ra pf12 pf1. simpl in pf12. simpl in pf1.

 unfold ProperPair in Ra.
    simpl in pf1.
    rewrite <- Ra. apply pf12. 

apply pf12.

intro.

: forall {A} `{OType A}, Flip (PM A _) -o> PM A _ -o> PM A _;
    liftP: forall {A} `{OType A}, M A _ -o> PM A _
  }.
