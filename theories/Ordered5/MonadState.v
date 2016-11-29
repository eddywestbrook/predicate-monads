Require Export PredMonad.Ordered5.Monad.

Import OTNotations.


(***
 *** Monads with State Effects
 ***)

(* State effects = get and put *)
Class MonadStateOps `(MOps:MonadOps) {TSt} (St:OType TSt) : Type :=
  {
    getM : M @t@ St ;
    putM : St -o> M @t@ OTunit
  }.

Class MonadState `(MSOps:MonadStateOps) : Prop :=
  {
    monad_state_monad :> Monad MOps;
    monad_state_ValidOType :> ValidOType St;

    monad_state_get :
      forall `(ValidOType) (m : M @t@ A),
        bindM @o@ getM @o@ (mkOTerm _ (fun _ => m)) =o= m ;

    monad_state_get_put :
      forall `(ValidOType) (f : St -o> OTunit -o> M @t@ A),
        bindM @o@ getM @o@
              (mkOTerm (St -o> M @t@ A)
                       (fun s => bindM @o@ (putM @o@ s) @o@ (f @o@ s)))
        =o= bindM @o@ getM @o@
                  (mkOTerm (St -o> M @t@ A) (fun s => f @o@ s @o@ tt)) ;

    monad_state_put_get :
      forall `(ValidOType) s (f : OTunit -o> St -o> M @t@ A),
        bindM @o@ (putM @o@ s) @o@
              (mkOTerm (OTunit -o> M @t@ A) (fun u => bindM @o@ getM @o@ (f @o@ u)))
        =o= bindM @o@ (putM @o@ s) @o@
                  (mkOTerm (OTunit -o> M @t@ A) (fun u => f @o@ u @o@ s)) ;

    monad_state_put_put :
      forall `(ValidOType) s1 s2 (f : OTunit -o> OTunit -o> M @t@ A),
        bindM @o@ (putM @o@ s1) @o@
              (mkOTerm (OTunit -o> M @t@ A)
                       (fun u => bindM @o@ (putM @o@ s2) @o@ (f @o@ u)))
        =o= bindM @o@ (putM @o@ s2) @o@ (f @o@ tt)
  }.


(***
 *** The State Monad Transformer
 ***)

Instance StateT `(St:OType) `(MOps:MonadOps) :
  OTypeF (fun `(A:OType) => Pfun St (M @t@ (St *o* A))) :=
  fun `(A:OType) => St -o> M @t@ (St *o* A).

Set Printing All. Typeclasses eauto := debug.
Instance StateT_MonadOps `(St:OType) (_:ValidOType St)
         `(MOps:MonadOps) (_:Monad MOps)
  : MonadOps (StateT St MOps) :=
  {returnM :=
     fun `(ValidOType) =>
       mkOTerm (A -o> St -o> M @t@ (St *o* A))
               (fun x s => returnM @o@ (s, x)); }.
   bindM :=
     fun A B m f =>
       fun s => do s_x <- m s; f (snd s_x) (fst s_x);
   lrM := fun {A} _ => LR_Op_fun }.

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
