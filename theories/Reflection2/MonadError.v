Require Export PredMonad.Reflection2.Monad.


(***
 *** Monads with Errors
 ***)

(* Error effects = throw and catch *)
Class MonadErrorOps M `{OTypeF1 M} Err `{OType Err} : Type :=
  {
    throwM : forall `{OType}, Err -o> M A _ ;
    catchM : forall `{OType}, M A _ -o> (Err -o> M A _) -o> M A _
  }.

Class MonadError M {FOM: OTypeF1 M} St {OSt: OType St}
      `{@MonadOps M FOM} `{@MonadErrorOps M FOM St OSt} : Prop :=
  {
    monad_error_monad :> Monad M;

    monad_error_throw_bind :
      forall A B `{OType A} `{OType B} err (f : A -o> M B _),
        bindM @o@ (throwM @o@ err) @o@ f =o= throwM @o@ err;

    monad_error_return_catch :
      forall A `{OType A} a f,
        catchM @o@ (returnM @o@ a) @o@ f =o= returnM @o@ a;

    monad_error_throw_catch :
      forall A `{OType A} err f,
        catchM @o@ (throwM @o@ err) @o@ f =o= f @o@ err;
  }.


(***
 *** The Error Monad Laws for OExprs
 ***)

(* FIXME HERE *)

(***
 *** The Error Monad Transformer
 ***)

Definition ErrorT Err `{OType Err} M `{OTypeF1 M} A `{OType A} :=
  M (Err + A)%type _.

Instance OTypeF1_ErrorT Err `{OType Err} M `{OTypeF1 M} :
  OTypeF1 (ErrorT Err M) :=
  fun _ _ => OType_OTypeF1 M _ _ _.

(*
Instance FindOTypeF1_ErrorT Err `{OType Err} M `{FindOTypeF1 M} :
  FindOTypeF1 (ErrorT Err M) (fun _ _ => _) := I.
*)

Instance MonadOps_ErrorT Err `{OType Err} M `{MonadOps M}
  : MonadOps (ErrorT Err M) :=
  {returnM :=
     fun A _ => ofun x => returnM @o@ (oinr @o@ x);
   bindM :=
     fun A B _ _ =>
       (ofun m => ofun f =>
        (bindM
           @o@ m
           @o@ (osum_elim
                  @o@ (ofun err => returnM @o@ (oinl @o@ err))
                  @o@ f)))
  }.

(*
Definition ErrorT_OTypeF1_simpl Err `{OType Err} M `{OTypeF1 M} A `{OType A} :
  OType_OTypeF1 (ErrorT Err M) (OTypeF1_ErrorT Err M) A _ =
  OType_OTypeF1 M _ _ _ := eq_refl.

Hint Rewrite ErrorT_OTypeF1_simpl : osimpl.
*)

Lemma OExpr_lambda_sum ctx A B C `{OType A} `{OType B} `{OType C}
      (e:OExpr (CtxCons (A+B) ctx) C) :
  Lam e =e=
  App (App (Embed osum_elim)
           (Lam (substOExpr 0 (weakenOExpr 1 A e)
                            (Embed oinl @e@ (Var OVar_0)))))
      (Lam (substOExpr 0 (weakenOExpr 1 B e)
                       (Embed oinr @e@ (Var OVar_0)))).
Proof.
  admit.
Admitted.

(* Hint Rewrite OExpr_lambda_sum : osimpl. *)

(* The Monad instance for ErrorT *)
Instance Monad_ErrorT Err `{OType Err} M `{Monad M} : Monad (ErrorT Err M).
Proof.
  (* FIXME: the automation gets screwed up here because (ErrorT Err M A) is the
  same as M (Err + A), and so the unification sometimes tries to match a bindM
  for M as a bindM for ErrorT... *)
  constructor; intros.
  - osimpl.
  - osimpl.
  - osimpl.

    FIXME HERE NOW

    oexpr_simpl.
    rewrite (monad_assoc_OExpr (M:=M)); simpl.
    f_equiv; f_equiv.
    repeat (rewrite OExpr_Beta; simpl).

    FIXME HERE NOW
Qed.
