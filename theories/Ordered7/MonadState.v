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



Ltac simpl_OT_term t :=
  lazymatch t with
  | ?f @o@ ?arg =>
    let f_ret := simpl_OT_term f in
    let arg_ret := simpl_OT_term arg in
    lazymatch f_ret with
    | ot_Lambda ?f_body =>
      let x := eval simpl in (f_body arg) in
      simpl_OT_term x
    | _ => constr:(pfun_app f_ret arg_ret)
    end
(*
  | ot_Lambda (fun x => ?f) =>
    let f_ret := constr:(fun x => ltac:(simpl_OT_term f)) in
    constr:(ot_Lambda f_ret)
*)
  | ?t => t
  end.

Ltac simpl_OT :=
  lazymatch goal with
  | |- ?t1 <o= ?t2 =>
    let t1' := simpl_OT_term t1 in
    let t2' := simpl_OT_term t2 in
    change (t1' <o= t2')
  | |- ?t1 =o= ?t2 =>
    let t1' := simpl_OT_term t1 in
    let t2' := simpl_OT_term t2 in
    change (t1' =o= t2')
  end.

(*
Ltac simpl_OT1 :=
  match goal with
  | |- context ctx [ofun ?f @o@ ?arg] =>
    let new_goal := context ctx [f arg] in
    change new_goal
  end.

Ltac simpl_OT := repeat (simpl_OT1 ; cbv beta).
 *)

(*
Lemma ofun_apply A B f prp x : @ot_Lambda A B f prp @o@ x = f x.
  reflexivity.
Qed.
Ltac simpl_OT := repeat rewrite ofun_apply.
*)



Ltac prove_OT :=
  simpl; try (rewrite_OT; simpl);
  lazymatch goal with
  | |- ot_equiv (_ -o> _) _ _ =>
    split; apply ot_arrow_ext; intro; intro; intro; prove_OT
  | |- ot_R (_ -o> _) _ _ =>
    apply ot_arrow_ext; intro; intro; intro; prove_OT
  | |- _ =>
    match goal with
    | H : (?x <o= ?y) |- _ => rewrite H; prove_OT
    | H : (?x =o= ?y) |- _ => rewrite H; prove_OT
    | |- _ => try reflexivity
    end
  end.

(* Don't unfold ot_Lambda when simplifying  *)
(* Arguments ot_Lambda A B f prp : simpl never. *)

Arguments ot_R {o} x y : simpl never.
Arguments opair {A B} : simpl never.
Arguments ofst {A B} : simpl never.
Arguments osnd {A B} : simpl never.
Arguments ot_Type o : simpl never.

Lemma ot_pair_eta_pfun (A B:OType) (x : A *o* B) :
  (ofst @o@ x ,o, osnd @o@ x) =o= x.
  split; split; reflexivity.
Qed.

Hint Rewrite ot_pair_eta_pfun : OT.

(* The Monad instance for StateT *)
Instance StateT_Monad St M `{Monad M} : Monad (StateT St M).
Proof.
  constructor; intros; unfold StateT, returnM, bindM, StateT_MonadOps.
  { prove_OT; try typeclasses eauto. }
  { assert (ofun (fun (s_x : St *o* A) =>
                    returnM @o@ (ofst @o@ s_x ,o, osnd @o@ s_x) : M (St *o* A))
            =o= ofun (fun s_x => returnM @o@ s_x)) as pair_eq;
    [ prove_OT; admit | ].
    simpl in pair_eq.
    prove_OT.

FIXME HERE NOW

    lazymatch goal with
    | |- (bindM @o@ _ @o@ ?f) <o= _ =>
      setoid_replace f with (ofun (fun (s_x : St *o* A) => returnM @o@ s_x))
    end.

    rewrite pair_eq.

      
      change (returnM @o@ (ofst @o@ x ,o, osnd @o@ x) <o= returnM @o@ y).
      rewrite ot_pair_eta_pfun.
      prove_OT.

      prove_OT.
      [ prove_OT

 | ].
    simpl in pair_eq.
    prove_OT.
    rewrite pair_eq.
    prove_OT.
    rewrite pair_eq.
    simpl; split; apply ot_arrow_ext; intro; intro; intro; simpl.
    prove_OT.


    transitivity (do s_x <- m @o@ x; returnM @o@ s_x).


simpl. try rewrite_OT. split; apply ot_arrow_ext; intros.
    simpl; try rewrite_OT; simpl.
  simpl.
  simpl_OT.
  repeat simpl (pfun_app (ot_Lambda _) _). simpl (pfun_app (ot_Lambda _) _).

  simpl_OT. simpl_OT.
  { simpl; split; apply ot_arrow_ext; intros; simpl; rewrite monad_return_bind; simpl;
      rewrite H0; reflexivity. }
  { simpl; split; apply ot_arrow_ext; intros; simpl; rewrite H0;
      transitivity (bindM @o@ (m @o@ y) @o@ returnM);
      try (rewrite monad_bind_return; reflexivity);
      apply Proper_ot_R_pfun_app_partial; apply ot_arrow_ext; intros; simpl;
        apply Proper_ot_R_pfun_app_partial; destruct H1; split; assumption. }
  { simpl_OT.

 rewrite monad_return_bind.

    apply ot_arrow_ext; intros.
  lazymatch goal with
  | |- ?t1 =o= ?t2 =>
    let t1' := eval simpl in t1 in
    change (t1' =o= t2)
  end.


simpl_OT.
simpl_OT; split; apply ot_arrow_ext; intros; simpl_OT; rewrite_OT; simpl_OT;
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
