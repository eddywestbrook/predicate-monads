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

Definition double_flip {A} `{OType A} : A -o> Flip (Flip A) :=
  ofun (fun x => flip (flip x)).

(* FIXME: the universe constraints on M and PM could be different...? *)
Class PredMonadOps M PM `{MonadOps M} `{MonadOps PM} :=
  { forallP: forall {A B} `{OType A} `{OType B}, (A -o> PM B _) -o> PM B _;
    existsP: forall {A B} `{OType A} `{OType B}, (A -o> PM B _) -o> PM B _;
    impliesP: forall {A} `{OType A}, Flip (PM A _) -o> PM A _ -o> PM A _;
    liftP: forall {A} `{OType A}, M A _ -o> PM A _
  }.

Definition andP `{PredMonadOps} `{OType} : PM A _ -o> PM A _ -o> PM A _ :=
  ofun (fun P1 =>
          ofun (fun P2 =>
                  forallP @o@ (ofun (fun b:bool =>
                                       oif @o@ b @o@ P1 @o@ P2)))).

(*
Definition uninvertP `{PredMonadOps} `{OType} : Flip (PM (Flip A) _) -o> PM A _ :=
  ofun (fun m =>
          bindM @o@ unflip (invertP @o@ unflip m)
                @o@ ofun (fun x => returnM @o@ unflip (unflip x))).
*)

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
        andP @o@ P1 @o@ (unflip P2) <o= P3 -> P1 <o= impliesP @o@ P2 @o@ P3;
    predmonad_impliesP_elim :
      forall {A} `{OType A} P1 P2 P3,
        P1 <o= impliesP @o@ (flip P2) @o@ P3 -> andP @o@ P1 @o@ P2 <o= P3;

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
Definition notP `{PredMonadOps} `{OType} : Flip (PM A _) -o> PM A _ :=
  ofun (fun P => impliesP @o@ P @o@ falseP).

(* An assertion inside a predicate monad *)
Definition assertP `{PredMonadOps} (P:Prop) : PM unit _ :=
  existsP @o@ (ofun (fun pf:P => trueP)).


(***
 *** The Set monad as a predicate monad for the Identity monad
 ***)

(* The type of downward-closed sets over a carrier type A *)
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

Program Definition singleton_SetM `{OType} : A -o> SetM A :=
  ofun (fun x => mkSetM (fun y => x = y)) (prp:=_).
Next Obligation.
  exists y; [ assumption | reflexivity ].
Defined.

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
