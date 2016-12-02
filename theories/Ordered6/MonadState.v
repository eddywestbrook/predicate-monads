Require Export PredMonad.Ordered6.Monad.

Import OTNotations.


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
        bindM @o@ getM @o@ (mkOTerm _ (fun _ => m)) =o= m ;

    monad_state_get_put :
      forall A (f : St -o> OTunit -o> M A),
        bindM @o@ getM @o@
              (mkOTerm (St -o> M A)
                       (fun s => bindM @o@ (putM @o@ s) @o@ (f @o@ s)))
        =o= bindM @o@ getM @o@
                  (mkOTerm (St -o> M A) (fun s => f @o@ s @o@ tt)) ;

    monad_state_put_get :
      forall A s (f : OTunit -o> St -o> M A),
        bindM @o@ (putM @o@ s) @o@
              (mkOTerm (OTunit -o> M A) (fun u => bindM @o@ getM @o@ (f @o@ u)))
        =o= bindM @o@ (putM @o@ s) @o@
                  (mkOTerm (OTunit -o> M A) (fun u => f @o@ u @o@ s)) ;

    monad_state_put_put :
      forall A s1 s2 (f : OTunit -o> OTunit -o> M A),
        bindM @o@ (putM @o@ s1) @o@
              (mkOTerm (OTunit -o> M A)
                       (fun u => bindM @o@ (putM @o@ s2) @o@ (f @o@ u)))
        =o= bindM @o@ (putM @o@ s2) @o@ (f @o@ tt)
  }.


(***
 *** The State Monad Transformer
 ***)

Definition StateT St M A := St -o> M (St *o* A).

Set Printing All. Typeclasses eauto := debug.
Instance StateT_MonadOps St M (MOps:MonadOps M) : MonadOps (StateT St M) :=
  {returnM :=
     fun A => mkOTerm (A -o> St -o> M (St *o* A))
                      (fun x s => returnM @o@ (s ,o, x));

   bindM :=
     fun A B =>
       mkOTerm _ (fun (m:StateT St M A) (f:A -o> StateT St M B) s =>
                    do s_x <- (m @o@ s);
                      f @o@ (osnd @o@ s_x) @o@ (ofst @o@ s_x))
  }.

(* The Monad instance for StateT *)
Global Instance StateT_Monad : Monad (StateT).
Proof.
  constructor; intros; unfold StateT, returnM, bindM, lrM, StateT_MonadOps.
  - auto with typeclass_instances.
  - prove_lr_proper.
  - prove_lr_proper.
  - intros R1 R2 subR; apply LRFun_Proper_subrelation; apply monad_proper_lrM;
      apply LRPair_Proper_subrelation; try assumption; reflexivity.
  - prove_lr.
  - transitivity (fun s => do s_x <- m s; returnM s_x).
    + split; build_lr_fun; apply monad_proper_bind; prove_lr.
    + prove_lr; autorewrite with LR; prove_lr.
  - prove_lr.
Qed.

Global Instance StateT_MonadStateOps : MonadStateOps S StateT :=
  { getM := fun s => returnM (s, s)
  ; putM := fun s _ => returnM (s, tt)
  }.

Global Instance StateT_MonadState : MonadState S StateT.
Proof.
  constructor; intros;
    unfold StateT, returnM, bindM, lrM, getM, putM,
    StateT_MonadOps, StateT_MonadStateOps.
  - auto with typeclass_instances.
  - prove_lr_proper.
  - prove_lr_proper.
  - prove_lr.
  - prove_lr.
  - prove_lr.
  - prove_lr.
Qed.

End StateT.
