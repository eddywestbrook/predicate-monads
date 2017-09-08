Require Export PredMonad.Reflection2.OrderedType.
Require Export PredMonad.Reflection2.OrderedContext.
Require Export PredMonad.Reflection2.OExpr.


(***
 *** The monad typeclass
 ***)

Class MonadOps M `{FindOTypeF1 M} : Type :=
  { returnM : forall {A} `{OType A}, A -o> M A _;
    bindM : forall {A B} `{OType A} `{OType B},
        M A _ -o> (A -o> M B _) -o> M B _ }.

Class Monad M `{MonadOps M} : Prop :=
  {
    monad_return_bind :
      forall A B `{OType A} `{OType B} (f: A -o> M B _) x,
        bindM @o@ (returnM @o@ x) @o@ f =o= f @o@ x;

    monad_bind_return :
      forall A `{OType A} m prp,
        bindM @o@ m @o@ (mk_ofun (fun x => returnM @o@ x) (prp:=prp)) =o= m;

    monad_assoc :
      forall A B C `{OType A} `{OType B} `{OType C}
             m (f: A -o> M B _) (g: B -o> M C _) prp,
        bindM @o@ (bindM @o@ m @o@ f) @o@ g
        =o=
        bindM @o@ m @o@ (mk_ofun (fun x => bindM @o@ (f @o@ x) @o@ g) (prp:=prp));
  }.

(* Helpful bind notation *)
Notation "'do' x <- m1 ; m2" :=
  (bindM @o@ m1 @o@ (mk_ofun (fun x => m2))) (at level 60, right associativity).

Notation "'edo' x <- m1 ; m2" :=
  (Embed bindM @e@ m1 @e@ (mkLam (fun x => m2)))
    (at level 60, right associativity).


(***
 *** The Monad Laws for OExprs
 ***)

(* Return-bind law for OExprs *)
Lemma monad_return_bind_OExpr
      `{Monad} {ctx A B} `{OType A} `{OType B}
      (f: OExpr ctx (A -o> M B _)) (x: OExpr ctx A) :
  App (App (Embed bindM) (App (Embed returnM) x)) f
  =e= (App f x).
Proof.
  apply unquote_eq. intro. apply monad_return_bind.
Qed.

(* Bind-return law for OExprs *)
Lemma monad_bind_return_OExpr
      `{Monad} {ctx A} `{OType A} (m: OExpr ctx (M A _)) :
  App (App (Embed bindM) m) (Lam (App (Embed returnM) (Var OVar_0))) =e= m.
Proof.
  apply unquote_eq. intro. apply monad_bind_return.
Qed.


(* Associativity law for OExprs *)
Lemma monad_assoc_OExpr
      `{Monad} {ctx A B C} {RA:OType A} {RB:OType B} {RC:OType C}
      (m:OExpr ctx (M A _))
      (f: OExpr ctx (A -o> M B _)) (g: OExpr ctx (B -o> M C _)) :
  App (App (Embed bindM) (App (App (Embed bindM) m) f)) g =e=
  App (App (Embed bindM) m)
      (Lam (App (App (Embed bindM)
                     (App (weakenOExpr 0 A f) (Var OVar_0)))
                (weakenOExpr 0 A g))).
Proof.
  apply unquote_eq. intro. simpl. apply monad_assoc.
Qed.

(* Add the monad laws to the OT rewrite set *)
Hint Rewrite @monad_return_bind_OExpr @monad_bind_return_OExpr
     @monad_assoc_OExpr : osimpl.


(***
 *** The Identity Monad
 ***)

Definition Identity A `{OType A} := A.

(*
Instance OTypeF_Identity : OTypeF1 Identity :=
  fun _ ot => ot.
 *)

Instance FindOTypeF_Identity : FindOTypeF1 Identity (fun _ ot => ot) := I.

Instance IdMonad_MonadOps : MonadOps Identity :=
  { returnM := fun A _ => ofun x => x;
    bindM := fun A B _ _ =>
               ofun m => ofun (f : A -o> B ) => f @o@ m }.

Instance IdMonad : Monad Identity.
Proof.
  econstructor; intros; simpl; reflexivity.
Qed.
