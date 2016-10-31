Require Import Coq.Setoids.Setoid.
Require Export PredMonad.OrderedType.

Import ProperTermNotations.


(***
 *** The Monad Typeclass
 ***)

Class MonadOps (M : OrderedType -> OrderedType) : Type :=
  { returnM : forall {A : OrderedType}, ProperTerm (A -o> M A);
    bindM : forall {A B : OrderedType}, ProperTerm (M A -o> (A -o> M B) -o> M B) }.

Class Monad M {MonadOps:MonadOps M} : Prop :=
  {
    monad_return_bind :
      forall A B x (f: ProperTerm (A -o> M B)),
        bindM @ (returnM @ x) @ f =o= f @ x;
    monad_bind_return :
      forall A (m:M A),
        bindM @ m @ returnM =o= m;
    monad_assoc :
      forall A B C m (f:A -o> M B) (g:B -o> M C),
        bindM @ (bindM @ m @ f) @ g
        =o= bindM @ m @ (pfun (x ::: _) ==> !bindM @ (!f @ pvar x) @ !g)
  }.


(***
 *** The Identity Monad
 ***)

Definition Identity (A: OrderedType) : OrderedType := A.
Instance MonadOps_Identity : MonadOps Identity :=
  { returnM := fun A => (pfun (x ::: A) ==> pvar x)%pterm;
    bindM := fun A B =>
               (pfun (m:::A) ==> pfun (f:::A -o> B) ==>
                     pvar f @ pvar m)%pterm }.

Instance Monad_Identity : Monad Identity.
  constructor; intros.
  destruct x as [x1 x2 pf_x]; destruct f as [f1 f2 pf_f]; compute.
  destruct pf_f as [ pf_f1 pf_f2 pf_f3 ].
  destruct pf_x as [ pf_x1 pf_x2 pf_x3 ].
  split.
  apply pf_f1; repeat constructor; apply pf_x1; repeat constructor.
  apply pf_f1; repeat constructor; apply pf_x1; repeat constructor.
  destruct m as [m1 m2 pf_m].
  destruct pf_m as [ pf_m1 pf_m2 pf_m3 ].
  compute; split; apply pf_m1; repeat constructor.
  destruct m as [m1 m2 pf_m];
    destruct pf_m as [ pf_m1 pf_m2 pf_m3 ].
  destruct f as [f1 f2 pf_f];
    destruct pf_f as [ pf_f1 pf_f2 pf_f3 ].
  destruct g as [g1 g2 pf_g];
    destruct pf_g as [ pf_g1 pf_g2 pf_g3 ].
  compute; split; apply pf_g1; repeat constructor;
    apply pf_f1; repeat constructor; apply pf_m1; repeat constructor.
Qed.


(***
 *** The Set Monad
 ***)

(* The downward-closed sets, as an OrderedType *)
Definition SetM (A: OrderedType) : OrderedType := ~o~ A -o> OTProp.

(* Mapping the elements of a downward-closed set; this is the functor map
operation for SetM *)
Program Definition SetM_map {ctx} {A} {B}
        (f: OTPairInCtx ctx (A -o> B))
        (s: OTPairInCtx ctx (SetM A)) : OTPairInCtx ctx (SetM B) :=
  pfun (y ::: ~o~ B) ==>
       map3_OTPairInCtx
         (ctx:= ~o~ B::ctx)
         (A:= A -o> B) (B:=SetM A) (C:=~o~ B) (D:=OTProp)
         (fun f s y =>
            exists x, ot_R A x x /\ s x /\ ot_R B y (f x))
         _ (!f) (!s) (pvar y).
Next Obligation.
  unfold Basics.impl.
  intros f1 f2 pf_f s1 s2 pf_s y1 y2 pf_y.
  destruct pf_f as [ pf_f1 pf_f2 pf_f3 ].
  destruct pf_s as [ pf_s1 pf_s2 pf_s3 ].
  destruct pf_y as [ pf_y1 pf_y2 pf_y3 ].
  split; intro; try assumption.
  repeat (destruct H); destruct H0.
  exists x; repeat split.
  assumption.
  apply (pf_s3 x); try assumption.
  split; assumption.
  apply (semitransitivity (SemiTransitive:=B) _ y1); try assumption.
  apply pf_f2; split; assumption.
  apply (semitransitivity (SemiTransitive:=B) _ (f1 x)); try assumption.
  apply pf_f1; split; assumption.
  apply pf_f2; split; assumption.
  apply pf_f3; split; assumption.
Qed.

(* Take the union of a set of sets; this is the join operation for SetM *)
Program Definition SetM_union {ctx} {A}
        (s: OTPairInCtx ctx (SetM (SetM A))) : OTPairInCtx ctx (SetM A) :=
  pfun (x ::: ~o~ A) ==>
       map2_OTPairInCtx (A:=SetM (SetM A)) (B:=~o~ A) (C:=OTProp)
       (fun s x => exists s', ot_R (SetM A) s' s' /\ s s' /\ s' x) _ (!s) (pvar x).
Next Obligation.
  intros s1 s2 pf_s x1 x2 pf_x.
  destruct pf_s as [ pf_s1 pf_s2 pf_s3 ].
  destruct pf_x as [ pf_x1 pf_x2 pf_x3 ].
  split; intro; try assumption.
  destruct H as [ s' H ]; destruct H; destruct H0.
  exists s'; repeat split.
  apply H.
  unfold Basics.impl in pf_s3; apply (pf_s3 s'); try assumption.
  split; apply H; assumption.
  unfold Basics.impl in H; apply (H x1).
  split; assumption.
  assumption.
Qed.

Instance MonadOps_SetM : MonadOps SetM :=
  { returnM := fun A => (pfun (x ::: A) ==>
                         pfun (y ::: ~o~ A) ==>
                         proper_leq (pvar y) (pvar x))%pterm;
    bindM := fun A B =>
               (pfun (m:::SetM A) ==> pfun (f::: A -o> SetM B) ==>
                  SetM_union (SetM_map (pvar f) (pvar m)))%pterm }.

(*
Instance Monad_SetM : Monad SetM.
*)
