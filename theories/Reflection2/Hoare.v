Require Export PredMonad.Reflection2.PredMonadState.


(***
 *** Hoare Logic using Predicate Monads
 ***)

Definition HoareF `{PredMonadState} `{OType} {ctx} :
  OExpr ctx ((St -o> Flip Prop) -o> (St -o> A -o> St -o> Prop)
                                    -o> PM A _ -o> PM A _) :=
  (efun pre =>
   efun post =>
   efun pm =>
   edo s_pre <- Embed getM;
     Embed assumingP
       @e@ (pre _ _ @e@ s_pre _ _)
       @e@ (edo x <- pm _ _;
              edo s_post <- Embed getM;
              edo unused
                  <- Embed assertP @e@ (post _ _ @e@ s_pre _ _
                                             @e@ x _ _ @e@ s_post _ _);
              Embed returnM @e@ x _ _)).

(*
FIXME: is this true?

Lemma HoareF_fixpoint_self `{PredMonadState} `{OType} {ctx}
      pre post (pm : OExpr ctx (PM A _)) :
  HoareF @e@ pre @e@ post @e@ (HoareF @e@ pre @e@ post @e@ pm)
  =e= HoareF @e@ pre @e@ post @e@ pm.
*)

Definition HoareExpr `{PredMonadState} `{OType} {ctx} :
  OExpr ctx ((St -o> Flip Prop) -o> (St -o> A -o> St -o> Prop) -o> PM A _) :=
  (efun pre =>
   efun post =>
   edo s_pre <- Embed getM ;
     (Embed assumingP)
       @e@ (pre _ _ @e@ s_pre _ _)
       @e@ (edo x <- Embed trueP;
              edo s_post <- Embed getM;
              edo unused
                  <- Embed assertP @e@ (post _ _ @e@ s_pre _ _
                                             @e@ x _ _ @e@ s_post _ _);
              Embed returnM @e@ x _ _)).
