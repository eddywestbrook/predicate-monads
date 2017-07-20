Require Export PredMonad.Reflection.Monad.


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
        bindM @o@ getM @o@ (ofun (fun _ => m)) =o= m;

    monad_state_get_put :
      forall A `{OType A} (f : St -o> unit -o> M A _ _),
        bindM @o@ getM @o@
              (ofun (fun s => bindM @o@ (putM @o@ s) @o@ (f @o@ s)))
        =o= bindM @o@ getM @o@
                  (ofun (fun s => f @o@ s @o@ tt));

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
     fun A _ _ => ofun (fun x => ofun (fun s => returnM @o@ (s ,o, x)));
   bindM :=
     fun A B _ _ _ _ =>
       ofun
         (fun m =>
            ofun (fun f =>
                    ofun (fun s =>
                            do s_x <- (m @o@ s);
                              f @o@ (osnd @o@ s_x) @o@ (ofst @o@ s_x))))
  }.

Typeclasses Opaque celem_head celem_rest.

(* The Monad instance for StateT *)
Instance StateT_Monad St `{OType St} M `{Monad M} : Monad (StateT St M).
Proof.
  constructor; intros.
  - unfold bindM, returnM, StateT_MonadOps, StateT.
    simpl. oquote. oexpr_simpl. simpl. try reflexivity. assumption.
  - unfold bindM, returnM, StateT_MonadOps, StateT.
    simpl. oquote. oexpr_simpl. try reflexivity. assumption.
  - unfold bindM, returnM, StateT_MonadOps, StateT.
    simpl.
    oquote. oexpr_simpl. unfold weakenOExpr, weakenOVar.
    repeat first [ reflexivity | apply Proper_Lam_eq
                   | apply Proper_App_eq | simpl; reflexivity ].
    simpl.

reflexivity.
apply (Proper_Lam_eq _ _).

    simpl. reflexivity.
Set Printing All. idtac. simpl.
    reflexivity.
    apply Proper_Lam_eq. apply Proper_App_eq; try reflexivity.

reflexivity.

try reflexivity. assumption.
