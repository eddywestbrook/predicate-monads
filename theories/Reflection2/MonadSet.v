(***
 *** Monads with Set-like structure
 ***)

Require Export PredMonad.Reflection2.Monad.

Class MonadSetOps M `{OTypeF1 M} : Type :=
  { forallM: forall {A B} `{OType A} `{OType B}, (A -o> M B _) -o> M B _;
    existsM: forall {A B} `{OType A} `{OType B}, (A -o> M B _) -o> M B _;
  }.

Class MonadSet M {OM:OTypeF1 M} `{@MonadOps M OM} `{@MonadSetOps M OM} : Prop :=
  {
    (* M must be a monad *)
    monadset_monad_M :> Monad M;

    (* forallM is a complete meet operator. The laws for it being a lower bound
    and the greatest lower bound actually correspond to forall-elimination and
    forall-introduction rules, respectively. *)
    monadset_forallM_elim :
      forall {A B} `{OType A} `{OType B} (f: A -o> M B _) a,
        forallM @o@ f <o= f @o@ a;
    monadset_forallM_intro :
      forall {A B} `{OType A} `{OType B} (f: A -o> M B _) P,
        (forall a, P <o= f @o@ a) -> P <o= forallM @o@ f;

    (* existsM is a complete join operator. The laws for it being an upper bound
    and the least upper bound actually correspond to exists-introduction and
    exists-elimination rules, respectively. *)
    monadset_existsM_intro :
      forall {A B} `{OType A} `{OType B} (f: A -o> M B _) a,
        f @o@ a <o= existsM @o@ f;
    monadset_existsM_elim :
      forall {A B} `{OType A} `{OType B} (f: A -o> M B _) P,
        (forall a, f @o@ a <o= P) -> existsM @o@ f <o= P;

    (* FIXME: need laws about how the combinators interact *)
  }.


(***
 *** Defined Set Operations
 ***)

Definition andP `{MonadSetOps} `{OType} : M A _ -o> M A _ -o> M A _ :=
  ofun (fun P1 =>
          ofun (fun P2 =>
                  forallM @o@ (ofun (fun b:bool =>
                                       oif @o@ b @o@ P1 @o@ P2)))).



(***
 *** The Monad of Downward-Closed Sets
 ***)

(* The type of downward-closed sets *)
Definition DownSetM A `{OType A} := Flip A -o> Prop.

Instance OTypeF1_DownSetM : OTypeF1 DownSetM := fun _ _ => _.

(* An existential with both a positive and a negative component *)
Program Definition oexists2' `{OType} : (A -o> Prop) -o>
                                            (Flip A -o> Prop) -o> Prop :=
  ofun (fun P1 =>
          ofun (fun P2 =>
                  exists2 x, P1 @o@ x & P2 @o@ flip x) (prp:=_)) (prp:=_).
Next Obligation.
  unfold OFunProper, ProperPair; simpl; intros. intro pf.
  destruct pf as [z pf1 pf2].
  exists z; try assumption. apply (H0 _ _ (reflexivity _)). assumption.
Defined.
Next Obligation.
  unfold OFunProper, ProperPair; simpl; intros. intro pf.
  destruct pf as [z pf1 pf2].
  exists z; [ apply (H0 _ _ (reflexivity _)) |
              apply (H1 _ _ (reflexivity _)) ]; assumption.
Defined.

(* The Monad operations for downward-closed sets *)
Instance MonadOps_DownSetM : MonadOps DownSetM :=
  {| returnM :=
       fun A _ =>
         ofun (fun (x:A) => ofun (fun (y:Flip A) => oR @o@ y @o@ x));
     bindM :=
       fun A B _ _ =>
         ofun (fun m =>
                 ofun (fun f =>
                         ofun (fun (y:Flip B) =>
                                 oexists2' @o@ (ofun (fun x => f @o@ x @o@ y))
                                               @o@ m)))
  |}.

Instance Monad_DownSetM : Monad DownSetM.
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


Instance MonadSetOps_DownSetM : MonadSetOps DownSetM :=
  {|
    forallM :=
      fun A B _ _ =>
        ofun (fun P =>
                ofun (fun b =>
                        oforall @o@ ofun (fun a =>
                                            P @o@ a @o@ b)));
    existsM :=
      fun A B _ _ =>
        ofun (fun P =>
                ofun (fun b =>
                        oexists @o@ ofun (fun a =>
                                            P @o@ a @o@ b)));
  |}.

Instance MonadSet_DownSetM : MonadSet DownSetM.
Proof.
  constructor; intros.
  - typeclasses eauto.
  - intros b1 b2 Rb pf. rewrite <- Rb. apply pf.
  - intros b1 b2 Rb pf a. apply (H a b1 b2 Rb); assumption.
  - intros b1 b2 Rb pf. rewrite <- Rb. exists a; assumption.
  - intros b1 b2 Rb [a pf]. apply (H a b1 b2 Rb); assumption.
Qed.
