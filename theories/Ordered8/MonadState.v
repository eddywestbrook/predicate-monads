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

FIXME HERE NOW: the problem is that the proof arguments keep getting too big!

Inductive OpaqueOFunArg A B `{OTRelation A} `{OTRelation B} (f : A -> B) : Prop :=
| MkOFunArg {prp:forall x y, ProperPair A x y -> ProperPair B (f x) (f y)}.
Definition GetOFunArg {A B} `{OTRelation A} `{OTRelation B} {f : A -> B}
           (arg:OpaqueOFunArg A B f) :
  forall x y, ProperPair A x y -> ProperPair B (f x) (f y) :=
  let (prp) := arg in prp.

Definition mk_ofun {A B} `{OTRelation A} `{OTRelation B} (f: A -> B)
           (arg:OpaqueOFunArg A B f)
  : A -o> B :=
  ofun f (prp:=GetOFunArg arg).

Ltac mk_ofun_tac := program_simpl; apply MkOFunArg; typeclasses eauto.


Program Definition monad_state_get_type M `{MonadStateOps M} : Prop :=
  forall A `{OType A} (m : M A _ _),
    bindM @o@ getM @o@ (mk_ofun (fun _ => m) _) =o= m.
Solve Obligations with mk_ofun_tac.

Program Definition monad_state_get_put_type M `{MonadStateOps M} : Prop :=
  forall A `{OType A} (f : St -o> unit -o> M A _ _),
    bindM @o@ getM @o@
          (mk_ofun (fun s => bindM @o@ (putM @o@ s) @o@ (f @o@ s)) _)
    =o= bindM @o@ getM @o@
              (mk_ofun (fun s => f @o@ s @o@ tt) _).
Solve Obligations with mk_ofun_tac.


Program Class MonadState M `{MonadStateOps M} : Prop :=
  {
    monad_state_monad :> Monad M;

    monad_state_get : monad_state_get_type M;
    monad_state_get_put : monad_state_get_put_type M;

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

Program Instance StateT_MonadOps St `{OType St} M `{MonadOps M} : MonadOps (StateT St M) :=
  {returnM :=
     fun A _ _ => mk_ofun (fun x => mk_ofun (fun s => returnM @o@ (s , x)) _) _;
   bindM :=
     fun A B _ _ _ _ =>
       mk_ofun
         (fun m =>
            mk_ofun (fun f =>
                       mk_ofun (fun s =>
                                  do s_x <- (m @o@ s);
                                    f @o@ (snd s_x) @o@ (fst s_x)) _) _) _
  }.
Solve Obligations with mk_ofun_tac.


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
  simpl; repeat (rewrite_OT; simpl_OT);
  match goal with
  | H : (?x <o= ?y) |- _ => rewrite H; prove_OT
  | H : (?x =o= ?y) |- _ => rewrite H; prove_OT
  | |- @ot_equiv _ _ _ _ =>
    split; apply ot_arrow_ext; intro; intro; intro; prove_OT
  | |- @ot_R _ _ _ _ =>
    apply ot_arrow_ext; intro; intro; intro; prove_OT
  | |- _ => try reflexivity
  end.

Instance Proper_pair A B `{OType A} `{OType B} :
  Proper (ot_R ==> ot_R ==> ot_R) (pair : A -> B -> A*B).
Proof.
  repeat intro; split; assumption.
Qed.

Arguments bindM : simpl never.
Arguments StateT : simpl never.

(*
Instance ot_equiv_pointwise_Pfun A B `{OType A} `{OType B} :
  Proper (pointwise_relation A ot_R ==> ot_R) ofun.
*)

(* The Monad instance for StateT *)
Instance StateT_Monad St `{OType St} M `{Monad M} : Monad (StateT St M).
Proof.
  constructor; intros.
  { prove_OT; typeclasses eauto. }
  { prove_OT; transitivity (bindM @o@ (m @o@ y) @o@ returnM).
    - apply Proper_ot_R_pfun_app_partial; try typeclasses eauto.
      prove_OT; typeclasses eauto.
    - prove_OT; typeclasses eauto.
    - prove_OT; typeclasses eauto.
    - apply Proper_ot_R_pfun_app_partial; try typeclasses eauto.
      prove_OT; typeclasses eauto. }
  { split; intro; intros; setoid_rewrite H7.
    Set Printing All.
    simpl (bindM @o@ _); unfold mk_ofun.
    rewrite monad_assoc.

    simpl.
    (* simpl bindM. repeat (simpl (ofun _ @o@ _)). *)
    refine (proj1 (monad_assoc _ _ _ (m @o@ a2) (ofun (fun s_x => f @o@ snd s_x @o@ fst s_x)) _)).
    exact (proj1 (monad_assoc ))

    - refine (proj1 (monad_assoc _ _ _ _ _ _)).
    rewrite monad_assoc.
rewrite_OT.

 apply ot_arrow_ext; intros.
    intro.
    apply ot_arrow_ext.


split.

simpl. split.

prove_OT.
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
