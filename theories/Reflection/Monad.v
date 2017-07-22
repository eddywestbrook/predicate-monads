Require Export PredMonad.Reflection.OrderedType.
Require Export PredMonad.Reflection.OrderedContext.
Require Export PredMonad.Reflection.OExpr_typed.


(***
 *** The monad typeclass
 ***)

Class MonadOps M `{OTypeF M} : Type :=
  { returnM : forall {A} `{OType A}, A -o> M A _ _;
    bindM : forall {A B} `{OType A} `{OType B},
        M A _ _ -o> (A -o> M B _ _) -o> M B _ _ }.

Class Monad M `{MonadOps M} : Prop :=
  {
    monad_return_bind :
      forall A B `{OType A} `{OType B} (f: A -o> M B _ _) x,
        bindM @o@ (returnM @o@ x) @o@ f =o= f @o@ x;

    monad_bind_return :
      forall A `{OType A} m prp,
        bindM @o@ m @o@ (ofun (fun x => returnM @o@ x) (prp:=prp)) =o= m;

    monad_assoc :
      forall A B C `{OType A} `{OType B} `{OType C}
             m (f: A -o> M B _ _) (g: B -o> M C _ _) prp,
        bindM @o@ (bindM @o@ m @o@ f) @o@ g
        =o=
        bindM @o@ m @o@ (ofun (fun x => bindM @o@ (f @o@ x) @o@ g) (prp:=prp));
  }.

(* Helpful bind notation *)
Notation "'do' x <- m1 ; m2" :=
  (bindM @o@ m1 @o@ (ofun (fun x => m2))) (at level 60, right associativity).

(* Return-bind law for OExprs *)
Lemma monad_return_bind_OExpr
      {ctx} `{ValidCtx ctx} `{Monad} {A B} `{OType A} `{OType B}
      (f: OExpr ctx (A -o> M B _ _)) (x: OExpr ctx A)
      {validF: ValidOExpr f} {validX: ValidOExpr x} :
  App (App (Embed bindM) (App (Embed returnM) x)) f
  =e= (App f x).
Proof.
  apply unquote_eq. intro. apply monad_return_bind.
Qed.

(* Bind-return law for OExprs *)
Lemma monad_bind_return_OExpr
      {ctx} `{ValidCtx ctx} `{Monad} {A} `{OType A} (m: OExpr ctx (M A _ _))
      {validM: ValidOExpr m} :
  App (App (Embed bindM) m) (Lam (App (Embed returnM) (Var OVar_0))) =e= m.
Proof.
  apply unquote_eq. intro. apply monad_bind_return.
Qed.


(* Associativity law for OExprs *)
Typeclasses eauto := debug.
Lemma monad_assoc_OExpr
      {ctx} `{ValidCtx ctx} `{Monad} {A B C} `{OType A} `{OType B} `{OType C}
      m (f: OExpr ctx (A -o> M B _ _)) (g: OExpr ctx (B -o> M C _ _))
      {validM: ValidOExpr m} {validF: ValidOExpr f} {validG: ValidOExpr g} :
  App (App (Embed bindM) (App (App (Embed bindM) m) f)) g =e=
  App (App (Embed bindM) m)
      (Lam (App (App (Embed bindM)
                     (App (weakenOExpr 0 A f) (Var OVar_0)))
                (weakenOExpr 0 A g))).
Proof.
  split.
  - split; simpl; intro; destruct_ands; split_ands; try typeclasses eauto.
    + rewrite (weakenOExpr_equiValid 0). apply H14.
    + rewrite (weakenOExpr_equiValid 0). apply H11.
  - intros; split; intros c1 c2 Rc; simpl.
    + etransitivity; [ apply monad_assoc | ]. f_equiv.
      -- f_equiv; f_equiv; [ apply exprSemantics_irrel | assumption ].
      -- intros a1 a2 Ra. simpl.
         repeat f_equiv; try assumption; rewrite (weakenOExpr_correct 0); simpl;
           f_equiv; assumption.
    + etransitivity; [ | apply monad_assoc ]. f_equiv.
      -- f_equiv; f_equiv; [ apply exprSemantics_irrel | assumption ].
      -- intros a1 a2 Ra. simpl.
         repeat f_equiv; try assumption; rewrite (weakenOExpr_correct 0); simpl;
           f_equiv; assumption.
Qed.

(* Add the monad laws to the OT rewrite set *)
Hint Rewrite @monad_return_bind_OExpr @monad_bind_return_OExpr
     @monad_assoc_OExpr : osimpl.


(***
 *** The Identity Monad
 ***)

Definition Identity A `{OType A} := A.

Instance OTRelationF_Identity : OTRelationF Identity :=
  fun _ R _ => R.

Instance OTypeF_Identity : OTypeF Identity :=
  fun _ _ ot => ot.

Instance IdMonad_MonadOps : MonadOps Identity :=
  { returnM := fun A _ _ => ofun (fun x => x);
    bindM := fun A B _ _ _ _ =>
               ofun (fun m => ofun (fun (f:A -o> B) => f @o@ m)) }.

Instance IdMonad : Monad Identity.
Proof.
  econstructor; intros; simpl; reflexivity.
Qed.
