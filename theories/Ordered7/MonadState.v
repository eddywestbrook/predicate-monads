Require Export PredMonad.Ordered7.Monad.


(***
 *** Monads with State Effects
 ***)

(* State effects = get and put *)
Class MonadStateOps M `{MOps:MonadOps M} (St:OType) : Type :=
  {
    getM : M St ;
    putM : St -o> M OTunit
  }.

Class MonadState M `{MSOps:MonadStateOps M} : Prop :=
  {
    monad_state_monad :> Monad M;

    monad_state_get :
      forall A (m : M A),
        bindM @o@ getM @o@ (ofun (fun _ => m)) =o= m ;

    monad_state_get_put :
      forall A (f : St -o> OTunit -o> M A),
        bindM @o@ getM @o@
              (ofun (fun s => bindM @o@ (putM @o@ s) @o@ (f @o@ s)))
        =o= bindM @o@ getM @o@
                  (ofun (fun s => f @o@ s @o@ tt)) ;

    monad_state_put_get :
      forall A s (f : OTunit -o> St -o> M A),
        bindM @o@ (putM @o@ s) @o@
              (ofun (fun u => bindM @o@ getM @o@ (f @o@ u)))
        =o= bindM @o@ (putM @o@ s) @o@
                  (ofun (fun u => f @o@ u @o@ s)) ;

    monad_state_put_put :
      forall A s1 s2 (f : OTunit -o> OTunit -o> M A),
        bindM @o@ (putM @o@ s1) @o@
              (ofun (fun u => bindM @o@ (putM @o@ s2) @o@ (f @o@ u)))
        =o= bindM @o@ (putM @o@ s2) @o@ (f @o@ tt)
  }.


(***
 *** The State Monad Transformer
 ***)

Definition StateT St M A := St -o> M (St *o* A).

Instance StateT_MonadOps St M (MOps:MonadOps M) : MonadOps (StateT St M) :=
  {returnM :=
     fun A => ofun (fun x => ofun (fun s => returnM @o@ (s ,o, x)));
   bindM :=
     fun A B =>
       ofun (fun (m: _ -o> _) =>
               ofun (fun (f:A -o> StateT St M B) =>
                       ofun (fun s =>
                               do s_x <- (m @o@ s);
                                 f @o@ (osnd @o@ s_x) @o@ (ofst @o@ s_x))))
  }.

Ltac simpl_OT1 :=
  lazymatch goal with
  | |- context ctx [ofun ?f @o@ ?arg] =>
    let new_goal := context ctx [f arg] in
    change new_goal
  end.

Ltac simpl_OT := repeat (simpl_OT1 ; cbv beta).

(*
Lemma ofun_apply A B f prp x : @ot_Lambda A B f prp @o@ x = f x.
  reflexivity.
Qed.
Ltac simpl_OT := repeat rewrite ofun_apply.
*)

(* The Monad instance for StateT *)
Instance StateT_Monad St M `{Monad M} : Monad (StateT St M).
Proof.
  constructor; intros; unfold StateT, returnM, bindM, StateT_MonadOps.
  { simpl_OT; split; apply ot_arrow_ext; intros; simpl_OT; rewrite_OT; simpl_OT;
      try assumption; rewrite H0; reflexivity. }
  { simpl_OT; split; apply ot_arrow_ext; intros; simpl_OT; rewrite H0;
      transitivity (bindM @o@ (m @o@ y) @o@ returnM);
      try (rewrite monad_bind_return; reflexivity);
      apply Proper_ot_R_pfun_app_partial; apply ot_arrow_ext; intros; simpl_OT;
        apply Proper_ot_R_pfun_app_partial; destruct H1; split; assumption. }
  { split.
    - apply ot_arrow_ext; intros. simpl_OT. rewrite monad_assoc.
      rewrite H0. apply Proper_ot_R_pfun_app_partial.
      apply ot_arrow_ext. intros. simpl_OT.
      destruct H1; rewrite H1; rewrite H2; reflexivity.
    - apply ot_arrow_ext; intros. simpl_OT. rewrite monad_assoc.
      rewrite H0. apply Proper_ot_R_pfun_app_partial.
      apply ot_arrow_ext. intros. simpl_OT.
      destruct H1; rewrite H1; rewrite H2; reflexivity.
  }
Qed.


(* FIXME HERE: move to OrderedType.v *)
Definition ott : OTunit := tt.

Instance StateT_MonadStateOps St M (MOps:MonadOps M) :
  MonadStateOps (StateT St M) St :=
  {
    getM := ofun (fun s => returnM @o@ (s ,o, s));
    putM := ofun (fun s => ofun (fun _ => returnM @o@ (s ,o, ott)));
  }.

Instance StateT_MonadState St M `(Monad M) : MonadState (StateT St M).
Proof.
  constructor; intros; unfold StateT, returnM, bindM, getM, putM,
                       StateT_MonadOps, StateT_MonadStateOps.
  { fold (StateT St M); typeclasses eauto. }
  { simpl_OT; split; apply ot_arrow_ext; intros; simpl_OT;
      rewrite monad_return_bind; simpl_OT; rewrite H0; reflexivity. }
  { simpl_OT. split.
    - apply ot_arrow_ext. intros. simpl_OT.
      rewrite monad_return_bind. rewrite monad_return_bind.
      

simpl_OT1. simpl_OT1. simpl_OT1. simpl_OT1. split; apply ot_arrow_ext; intros; simpl;
      repeat rewrite monad_return_bind;
      simpl; rewrite monad_return_bind; simpl; rewrite H0; reflexivity.
Qed.

End StateT.
