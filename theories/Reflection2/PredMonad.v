Require Export PredMonad.Reflection2.Monad.

(***
 *** The Predicate Monad Class
 ***)

Class PredMonadOps M PM `{FindOTypeF1 M} `{FindOTypeF1 PM} : Type :=
  { forallP: forall {A B} `{OType A} `{OType B}, (A -o> PM B _) -o> PM B _;
    existsP: forall {A B} `{OType A} `{OType B}, (A -o> PM B _) -o> PM B _;
    liftP: forall {A} `{OType A}, M A _ -o> PM A _;
  }.

Class PredMonad M PM {OM} {FOM: FindOTypeF1 M OM} {OPM} {FOPM: FindOTypeF1 PM OPM}
      `{@MonadOps M OM FOM} `{@MonadOps PM OPM FOPM}
      `{@PredMonadOps M PM OM FOM OPM FOPM} : Prop :=
  {
    (* M and PM must be monads *)
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

    (* Laws about liftP *)
    predmonad_liftP_return :
      forall {A} `{OType A} (a:A),
        liftP @o@ (returnM @o@ a) =o= returnM @o@ a;
    predmonad_liftP_bind :
      forall {A B} `{OType A} `{OType B} m f prp,
        liftP @o@ (bindM @o@ m @o@ f)
        =o= bindM @o@ (liftP @o@ m) @o@
                  (mk_pfun (fun x => liftP @o@ (f @o@ x)) (prp:=prp));

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
  pfun P1 => pfun P2 =>
  existsP @o@ (pfun (b:bool) => oif @o@ b @o@ P1 @o@ P2).

(* True and false, which correspond to top and bottom, respectively *)
Definition trueP `{PredMonadOps} `{OType} : PM A _ :=
  existsP @o@ (pfun pm => pm).
Definition falseP `{PredMonadOps} `{OType} : PM A _ :=
  forallP @o@ (pfun pm => pm).

(* An assertion inside a predicate monad *)
Program Definition assertP `{PredMonad} : Prop -o> PM unit _ :=
  mk_pfun (fun (P:Prop) => existsP @o@ (pfun (pf:P) => trueP)) (prp:=_).
Next Obligation.
  intros P1 P2 RP. apply predmonad_existsP_elim; intro pf1.
  assert P2 as pf2; [ apply RP; assumption | ].
  etransitivity; [ | apply (predmonad_existsP_intro _ pf2) ].
  reflexivity.
Defined.

(* An assumption made for the duration of a predicate monad *)
Program Definition assumingP `{PredMonad} `{OType} :
  Flip Prop -o> PM A _ -o> PM A _ :=
  mk_pfun
    (fun (P:Flip Prop) =>
       mk_pfun (fun (Q:PM A _) =>
                  forallP @o@ (pfun (pf:unflip P) => Q)) (prp:=_))
       (prp:=_).
Next Obligation.
  intros Q1 Q2 RQ.
  apply predmonad_forallP_intro; intro pf. simpl.
  etransitivity; [ apply (predmonad_forallP_elim _ pf) | eassumption ].
Defined.
Next Obligation.
  intros P1 P2 RP Q1 Q2 RQ.
  apply predmonad_forallP_intro; intro pf2.
  assert (unflip P1) as pf1; [ apply RP; assumption | ].
  etransitivity; [ apply (predmonad_forallP_elim _ pf1) | eassumption ].
Defined.


(***
 *** The Downward-Closed Set Predicate Monad
 ***)

(* The type of downward-closed sets *)
Definition DownSetM A `{OType A} := Flip A -o> Prop.

(*
Instance OTypeF1_DownSetM : OTypeF1 DownSetM := fun _ _ => _.
*)

Instance FindOTypeF1_DownSetM : FindOTypeF1 DownSetM (fun _ _ => _) := I.

(* An existential with both a positive and a negative component *)
Program Definition oexists2' `{OType} : (A -o> Prop) -o>
                                        (Flip A -o> Prop) -o> Prop :=
  mk_pfun
    (fun P1 =>
       mk_pfun
         (fun P2 =>
            exists2 x, P1 @o@ x & P2 @o@ flip x) (prp:=_)) (prp:=_).
Next Obligation.
  unfold PFunProper, ProperPair; simpl; intros. intro pf.
  destruct pf as [z pf1 pf2].
  exists z; try assumption. apply (H0 _ _ (reflexivity _)). assumption.
Defined.
Next Obligation.
  unfold PFunProper, ProperPair; simpl; intros. intro pf.
  destruct pf as [z pf1 pf2].
  exists z; [ apply (H0 _ _ (reflexivity _)) |
              apply (H1 _ _ (reflexivity _)) ]; assumption.
Defined.

(* The Monad operations for downward-closed sets *)
Instance MonadOps_DownSetM : MonadOps DownSetM :=
  {| returnM :=
       fun A _ =>
         pfun (x:A) => pfun (y:Flip A) => oR @o@ y @o@ x;
     bindM :=
       fun A B _ _ =>
         (pfun m => pfun f => pfun (y:Flip B) =>
          oexists2' @o@ (pfun x => f @o@ x @o@ y) @o@ m)
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


Instance PredMonadOps_DownSetM : PredMonadOps Identity DownSetM :=
  {|
    forallP :=
      fun A B _ _ =>
        pfun P => pfun b => oforall @o@ (pfun a => P @o@ a @o@ b);
    existsP :=
      fun A B _ _ =>
        pfun P => pfun b => oexists @o@ (pfun a => P @o@ a @o@ b);
    liftP :=
      fun A _ => returnM
  |}.

Instance PredMonad_DownSetM : PredMonad Identity DownSetM.
Proof.
  constructor; intros; try typeclasses eauto.
  - intros b1 b2 Rb pf. rewrite <- Rb. apply pf.
  - intros b1 b2 Rb pf a. apply (H a b1 b2 Rb); assumption.
  - intros b1 b2 Rb pf. rewrite <- Rb. exists a; assumption.
  - intros b1 b2 Rb [a pf]. apply (H a b1 b2 Rb); assumption.
  - reflexivity.
  - split; intros b1 b2 Rb pf.
    + simpl. exists m; [ | reflexivity ].
      etransitivity; [ apply Rb | apply pf ].
    + destruct pf. simpl in * |- *. etransitivity; try eassumption.
      etransitivity; try eassumption.
      apply pfun_Proper; assumption.
Qed.
