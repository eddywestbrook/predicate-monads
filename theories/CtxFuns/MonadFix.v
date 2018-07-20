Require Export PredMonad.CtxFuns.Monad.

(***
 *** Monads with Fixed-points
 ***)

Class MonadFixOps M `{OTypeF M} : Type :=
  { fixM : forall {A B} `{OType A} `{OType B},
      ((A -o> M B _) -o> (A -o> M B _)) -o> (A -o> M B _); }.

Definition ofix {ctx} `{MonadFixOps} {A B} `{OType A} `{OType B} :
  OExpr ctx (((A -o> M B _) -o> (A -o> M B _)) -o> (A -o> M B _)) :=
  const_ofun fixM.


Class MonadFix M `{OF:OTypeF M} `{@MonadOps M OF} `{@MonadFixOps M OF} : Prop :=
  { Monad_MonadFix :> Monad M;
    FixedPoint_ofix :
      forall {ctx A B} `{OType A} `{OType B}
             (f: OExpr ctx ((A -o> M B _) -o> (A -o> M B _))),
        ofix @o@ f =o= f @o@ (ofix @o@ f)
  }.


(***
 *** The Fixed-point Monad = Downwards-closed sets
 ***)

(* The type of downward-closed sets *)
Definition FixM A `{OType A} := Flip A -o> Prop.

Instance OTypeF_FixM : OTypeF FixM := fun _ _ => _.

(* The Monad operations for downward-closed sets *)
Instance MonadOps_FixM : MonadOps FixM :=
  {| returnM :=
       fun A _ =>
         oexpr (ofun (x:A) => ofun (y:Flip A) => oappr @o@ ovar y @o@ ovar x);
     bindM :=
       fun A B _ _ =>
         oexpr (ofun m => ofun f => ofun (y:Flip B) =>
                oexists2 @o@ (ofun x => ovar f @o@ ovar x @o@ ovar y) @o@ ovar m)
  |}.

Lemma flipLeftAdj {A} `{OType A} (x: A) (y: Flip A) :
  flip x <o= y <-> unflip y <o= x.
Proof.
  destruct y; simpl; reflexivity.
Qed.

Lemma flipRightAdj {A} `{OType A} (x: Flip A) (y: A) :
  x <o= flip y <-> y <o= unflip x.
Proof.
  destruct x; simpl; reflexivity.
Qed.

Lemma flipAdjEq {A} `{OType A} (x: A) (y: Flip A) :
  flip x =o= y <-> x =o= unflip y.
Proof.
  destruct y; simpl. split; intro e; destruct e; split; assumption.
Qed.

Instance Monad_FixM : Monad FixM.
Proof.
  constructor; intros; apply funOExt; intro celem; apply funOExt.
  { intro y; simpl; split.
    - intros [ z pf1 pf2 ]. rewrite <- pf2. assumption.
    - intro H. exists (ofun_app x celem); [ assumption | reflexivity ]. }
  { intro x; simpl; split.
    - intros [ z pf1 pf2 ]. rewrite <- flipLeftAdj in pf1.
      rewrite <- pf1. assumption.
    - intro. exists (unflip x); [ reflexivity | ]. destruct x; assumption. }
  { intro c; simpl; split.
    - intros [ b pf_bc [ a pf_ab pf_a ] ].
      exists a; [ exists b | ]; assumption.
    - intros [ a [ b pf_bc pf_ab ] pf_a ].
      exists b; [ | exists a ]; assumption. }
Qed.

(* FIXME: this should essentially be the OFun version of

   fun (f: (A -> DownSet B) -> (A -> DownSet B)) (a:A) (b:Flip B) =>
     forall (g: Equiv (A -> DownSet B)), f g <o= g -> g a b

   which is the greatest fixed-point, by the Knaster-Tarski theorem, but this
   requires a way to write OExprs in "flipped context" *)
Instance MonadFixOps_FixM : MonadFixOps FixM.
Admitted.

Instance MonadFix_FixM : MonadFix FixM.
Admitted.
