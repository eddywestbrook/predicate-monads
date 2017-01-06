Require Export PredMonad.Ordered8.Monad.


(***
 *** Monads with State Effects
 ***)

(* State effects = get and put *)
Class MonadStateOps M `{MonadOps M} St `{OType St} : Type :=
  {
    getM : M St _ _ ;
    putM : St -o> M unit _ _
  }.

Class MonadState M `{MonadStateOps M} : Prop :=
  {
    monad_state_monad :> Monad M;

    monad_state_get :
      forall A `{OType A} (m : M A _ _),
        bindM @o@ getM @o@ (ofun (fun _ => m)) =o= m ;

    monad_state_get_put :
      forall A `{OType A} (f : St -o> unit -o> M A _ _),
        bindM @o@ getM @o@
              (ofun (fun s => bindM @o@ (putM @o@ s) @o@ (f @o@ s)))
        =o= bindM @o@ getM @o@
                  (ofun (fun s => f @o@ s @o@ tt)) ;

    monad_state_put_get :
      forall A `{OType A} s (f : unit -o> St -o> M A _ _),
        bindM @o@ (putM @o@ s) @o@
              (ofun (fun u => bindM @o@ getM @o@ (f @o@ u)))
        =o= bindM @o@ (putM @o@ s) @o@
                  (ofun (fun u => f @o@ u @o@ s)) ;

    monad_state_put_put :
      forall A `{OType A} s1 s2 (f : unit -o> unit -o> M A _ _),
        bindM @o@ (putM @o@ s1) @o@
              (ofun (fun u => bindM @o@ (putM @o@ s2) @o@ (f @o@ u)))
        =o= bindM @o@ (putM @o@ s2) @o@ (f @o@ tt)
  }.


(***
 *** The State Monad Transformer
 ***)

Definition StateT St `{OType St} M `{OTypeF M} A `{OType A} :=
  St -o> M (St * A)%type _ _.

Instance OTRelationF_StateT St `{OType St} M `{OTypeF M} :
  OTRelationF (StateT St M) :=
  fun _ _ _ => _.

Instance OTypeF_StateT St `{OType St} M `{OTypeF M} :
  OTypeF (StateT St M) :=
  fun _ _ _ => _.

Instance StateT_MonadOps St `{OType St} M `{MonadOps M} : MonadOps (StateT St M) :=
  {returnM :=
     fun A _ _ => ofun (fun x => ofun (fun s => returnM @o@ (s , x)));
   bindM :=
     fun A B _ _ _ _ =>
       ofun (fun m =>
               ofun (fun f =>
                       ofun (fun s =>
                               do s_x <- (m @o@ s);
                                 f @o@ (snd s_x) @o@ (fst s_x))))
  }.


Ltac simpl_OT_term t :=
  lazymatch t with
  | ?f @o@ ?arg =>
    let f_ret := simpl_OT_term f in
    let arg_ret := simpl_OT_term arg in
    lazymatch f_ret with
    | ofun ?f_body =>
      let x := eval simpl in (f_body arg) in
      simpl_OT_term x
    | _ => constr:(pfun_app f_ret arg_ret)
    end
(*
  | ofun (fun x => ?f) =>
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
  | |- _ => idtac
  end.

Ltac prove_OT :=
  simpl_OT; repeat (rewrite_OT; simpl_OT);
  lazymatch goal with
  | |- @ot_equiv (_ -o> _) _ _ _ =>
    split; apply ot_arrow_ext; intro; intro; intro; prove_OT
  | |- @ot_R (_ -o> _) _ _ _ =>
    apply ot_arrow_ext; intro; intro; intro; prove_OT
  | |- _ =>
    match goal with
    | H : (?x <o= ?y) |- _ => rewrite H; prove_OT
    | H : (?x =o= ?y) |- _ => rewrite H; prove_OT
    | |- _ => try reflexivity
    end
  end.

Instance Proper_pair A B `{OType A} `{OType B} :
  Proper (ot_R ==> ot_R ==> ot_R) (pair : A -> B -> A*B).
Proof.
  repeat intro; split; assumption.
Qed.


(*
Instance ot_equiv_pointwise_Pfun A B `{OType A} `{OType B} :
  Proper (pointwise_relation A ot_R ==> ot_R) ofun.
*)

(* The Monad instance for StateT *)
Instance StateT_Monad St `{OType St} M `{Monad M} : Monad (StateT St M).
Proof.
  constructor; intros; unfold StateT, returnM, bindM, StateT_MonadOps.
  { prove_OT; typeclasses eauto. }
  { prove_OT; transitivity (bindM @o@ (m @o@ y) @o@ returnM).
    - apply Proper_ot_R_pfun_app_partial; try typeclasses eauto.
      prove_OT; typeclasses eauto.
    - prove_OT; typeclasses eauto.
    - prove_OT; typeclasses eauto.
    - apply Proper_ot_R_pfun_app_partial; try typeclasses eauto.
      prove_OT; typeclasses eauto. }
  { admit.
    (* FIXME HERE: why is the following SOOOOOO slow?! *)
    (*
    cbn. apply conj.
    - apply ot_arrow_ext. intros. cbn.
      rewrite monad_assoc. cbn. rewrite H7. reflexivity.
     *) }
Admitted.

Instance StateT_MonadStateOps St `{OType St} M `{MonadOps M} :
  MonadStateOps (StateT St M) St :=
  {
    getM := ofun (fun s => returnM @o@ (s , s));
    putM := ofun (fun s => ofun (fun _ => returnM @o@ (s , tt)));
  }.

Instance StateT_MonadState St `{OType St} M `{Monad M} : MonadState (StateT St M).
Proof.
  constructor; intros; unfold StateT, returnM, bindM, getM, putM,
                       StateT_MonadOps, StateT_MonadStateOps.
  { typeclasses eauto. }
  { prove_OT; typeclasses eauto. }
  { prove_OT.

FIXME HERE NOW: why is proving anything here so slow?!


simpl; split; apply ot_arrow_ext; intros.
    rewrite monad_return_bind.
    - simpl.

simpl_OT; split; apply ot_arrow_ext; intros; simpl_OT;
      rewrite monad_return_bind; simpl_OT; rewrite H0; reflexivity. }
  { simpl_OT. split.
    - apply ot_arrow_ext. intros. simpl_OT.
      rewrite monad_return_bind. rewrite monad_return_bind.
      

simpl_OT1. simpl_OT1. simpl_OT1. simpl_OT1. split; apply ot_arrow_ext; intros; simpl;
      repeat rewrite monad_return_bind;
      simpl; rewrite monad_return_bind; simpl; rewrite H0; reflexivity.
Qed.

End StateT.
