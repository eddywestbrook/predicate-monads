Require Export PredMonad.CtxFuns.OrderedType.
Require Export PredMonad.CtxFuns.OExpr.


(***
 *** The monad typeclass
 ***)

Class MonadOps M `{OTypeF M} : Type :=
  { returnM : forall {A} `{OType A}, A -o> M A _;
    bindM : forall {A B} `{OType A} `{OType B},
        M A _ -o> (A -o> M B _) -o> M B _ }.

Definition oreturn {ctx} `{MonadOps} {A} `{OType A} : OExpr ctx (A -o> M A _) :=
  const_ofun returnM.
Definition obind {ctx} `{MonadOps} {A B} `{OType A} `{OType B} :
  OExpr ctx (M A _ -o> (A -o> M B _) -o> M B _) :=
  const_ofun bindM.
Notation "'do' x <- m1 ; m2" :=
  (obind @o@ m1 @o@ mkLam (fun x => m2)) (at level 60, right associativity).


Class Monad M `{MonadOps M} : Prop :=
  {
    monad_return_bind :
      forall {ctx A B} `{OType A} `{OType B} (f: OExpr ctx (A -o> M B _)) x,
        obind @o@ (oreturn @o@ x) @o@ f =o= f @o@ x;

    monad_bind_return :
      forall {ctx A} `{OType A} (m: OExpr ctx (M A _)),
        obind @o@ m @o@ oreturn =o= m;

    monad_assoc :
      forall {ctx A B C} `{OType A} `{OType B} `{OType C}
             m (f: OExpr ctx (A -o> M B _)) (g: OExpr ctx (B -o> M C _)),
        obind @o@ (obind @o@ m @o@ f) @o@ g
        =o=
        obind @o@ m @o@ (ofun x => obind @o@ (ovar f @o@ ovar x) @o@ ovar g);
  }.


(***
 *** The Identity Monad
 ***)

Definition Identity A `{OType A} := A.

Instance OTypeF_Identity : OTypeF Identity :=
  fun _ ot => ot.

Definition oexpr {A} `{OType A} (e: OExpr CNil A) : A := ofun_app e tt.

Instance IdMonad_MonadOps : MonadOps Identity :=
  { returnM := fun A _ => oexpr (ofun x => x);
    bindM := fun A B _ _ =>
               oexpr (ofun m => ofun (f : A -o> B ) => ovar f @o@ ovar m) }.

Instance IdMonad : Monad Identity.
Proof.
  constructor; intros; apply funOExt; intros; simpl; reflexivity.
Qed.
