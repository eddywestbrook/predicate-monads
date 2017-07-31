Require Export PredMonad.Reflection2.Monad.


(***
 *** Monads with State Effects
 ***)

(* State effects = get and put *)
Class MonadStateOps M `{MonadOps M} St `{OType St} : Type :=
  {
    getM : M St _ ;
    putM : St -o> M unit _
  }.

Class MonadState M `{MonadStateOps M} : Prop :=
  {
    monad_state_monad :> Monad M;

    monad_state_get :
      forall A `{OType A} (m : M A _) prp,
        bindM @o@ getM @o@ (ofun (fun _ => m) (prp:=prp)) =o= m;

    monad_state_get_put :
      forall A `{OType A} (f : St -o> unit -o> M A _) prp1 prp2,
        bindM @o@ getM @o@
              (ofun (fun s => bindM @o@ (putM @o@ s) @o@ (f @o@ s)) (prp:=prp1))
        =o= bindM @o@ getM @o@
                  (ofun (fun s => f @o@ s @o@ tt) (prp:=prp2));

    monad_state_put_get :
      forall A `{OType A} s (f : unit -o> St -o> M A _) prp1 prp2,
        bindM @o@ (putM @o@ s) @o@
              (ofun (fun u => bindM @o@ getM @o@ (f @o@ u)) (prp:=prp1))
        =o= bindM @o@ (putM @o@ s) @o@
                  (ofun (fun u => f @o@ u @o@ s) (prp:=prp2)) ;

    monad_state_put_put :
      forall A `{OType A} s1 s2 (f : unit -o> unit -o> M A _) prp,
        bindM @o@ (putM @o@ s1) @o@
              (ofun (fun u => bindM @o@ (putM @o@ s2) @o@ (f @o@ u)) (prp:=prp))
        =o= bindM @o@ (putM @o@ s2) @o@ (f @o@ tt)
  }.


(***
 *** The State Monad Laws for OExprs
 ***)

(*
FIXME HERE NOW: cannot match weakenOExpr on the LHS; instead, we need a
Strengthens typeclass for lifting m out of its context

FIXME HERE NOW: also need a rule for unquoting 

Lemma monad_state_get_OExpr
      {ctx} `{ValidCtx ctx} `{MonadState} {A} `{OType A}
      m {validM: @ValidOExpr ctx (M A _ _) _ m} :
  App (App (Embed bindM) (Embed getM)) (Lam (weakenOExpr 0 _ m)) =e= m.
Proof.
  apply unquote_eq. intro. simpl. apply monad_state_get.
Qed.

Lemma monad_state_get_put_OExpr
      {ctx} `{ValidCtx ctx} `{MonadState} {A} `{OType A}
      f {validF: @ValidOExpr _ (St -o> unit -o> M A _ _) _ f} :
  App (App (Embed bindM) (Embed getM))
      (Lam (App (App (Embed bindM) (App (Embed putM) (Var OVar_0)))
                (Lam (App (App f )))))
*)


(***
 *** The State Monad Transformer
 ***)

Definition StateT St `{OType St} M `{OTypeF1 M} A `{OType A} :=
  St -o> M (St * A)%type _.

Instance OTypeF1_StateT St `{OType St} M `{OTypeF1 M} :
  OTypeF1 (StateT St M) :=
  fun _ _ => _.

Instance StateT_MonadOps St `{OType St} M `{MonadOps M} : MonadOps (StateT St M) :=
  {returnM :=
     fun A _ => ofun (fun x => ofun (fun s => returnM @o@ (s ,o, x)));
   bindM :=
     fun A B _ _ =>
       ofun
         (fun m =>
            ofun (fun f =>
                    ofun (fun s =>
                            do s_x <- (m @o@ s);
                              f @o@ (osnd @o@ s_x) @o@ (ofst @o@ s_x))))
  }.


(* The Monad instance for StateT *)
Instance StateT_Monad St `{OType St} M `{Monad M} : Monad (StateT St M).
Proof.
  constructor; intros.
  - osimpl.
  - osimpl.
  - osimpl.
Qed.
