Require Export PredMonad.CtxFuns.OrderedType.

(***
 *** The Category of OFuns
 ***)

(* Extensionality for functions w.r.t. oeq (the one for oleq is definitionally
true already) *)
Lemma funOExt A B `{OType A} `{OType B} (f g : A -o> B) :
  f =o= g <-> (forall x, ofun_app f x =o= ofun_app g x).
Proof.
  split.
  { intros Rfg x. rewrite Rfg. reflexivity. }
  { intro all_fg; split; intros a1 a2 Ra; rewrite Ra; apply all_fg. }
Qed.


(* The identity ofun *)
Definition id_ofun {A} `{OType A} : A -o> A :=
  {| ofun_app := fun x => x; ofun_Proper := fun x1 x2 Rx => Rx |}.

(* The identity ofun *)
Program Definition compose_ofun {A B C}
        `{OType A} `{OType B} `{OType C}
        (f:A -o> B) (g:B -o> C) : A -o> C :=
  {| ofun_app := fun x => ofun_app g (ofun_app f x);
     ofun_Proper := _ |}.
Next Obligation.
  intros x1 x2 Rx. apply ofun_Proper. apply ofun_Proper. assumption.
Qed.

Instance Proper_compose_ofun A B C
         `{OType A} `{OType B} `{OType C} :
  Proper (oleq ==> oleq ==> oleq) (@compose_ofun A B C _ _ _).
  intros f1 f2 Rf g1 g2 Rg a1 a2 Ra.
  apply Rg. apply Rf. assumption.
Qed.

(* Category theory laws for OFuns *)
Lemma id_compose_ofun A B `{OType A} `{OType B} (f: A -o> B) :
  (compose_ofun id_ofun f) =o= f.
  apply funOExt; intro a. simpl. reflexivity.
Qed.

Lemma compose_id_ofun A B `{OType A} `{OType B} (f: A -o> B) :
  (compose_ofun f id_ofun) =o= f.
  apply funOExt; intro a. simpl. reflexivity.
Qed.

Lemma compose_compose_ofun A B C D
      `{OType A} `{OType B} `{OType C} `{OType D}
      (f: A -o> B) (g: B -o> C) (h: C -o> D) :
  (compose_ofun f (compose_ofun g h)) =o= (compose_ofun (compose_ofun f g) h).
  apply funOExt; intro a. simpl. reflexivity.
Qed.


(***
 *** The Constant OFun
 ***)

(* The constant ofun *)
Program Definition const_ofun {A B} `{OType A} `{OType B} b : A -o> B :=
  {| ofun_app := fun _ => b; ofun_Proper := fun _ _ _ => ltac:(reflexivity) |}.

(* FIXME: this proper-ness proof should include irrelevance of the OType arg *)
Instance Proper_const_ofun {A B} `{OType A} `{OType B} :
  Proper (oleq ==> oleq) (const_ofun (A:=A) (B:=B)).
Proof.
  intros b1 b2 Rb a1 a2 Ra. apply Rb.
Qed.

(* Composing with the constant ofun on the left *)
Lemma compose_const_ofun_f A B C `{OType A} `{OType B} `{OType C}
      b (f : B -o> C) :
  compose_ofun (const_ofun (A:=A) b) f =o= const_ofun (ofun_app f b).
  split; intros a1 a2 Ra; reflexivity.
Qed.

(* Composing with the constant ofun on the right *)
Lemma compose_f_const_ofun A B C `{OType A} `{OType B} `{OType C}
      (f : A -o> B) c :
  compose_ofun f (const_ofun c) =o= const_ofun c.
  split; intros a1 a2 Ra; reflexivity.
Qed.


(***
 *** Pairs
 ***)

(* Take the pair of the outputs of two ofuns *)
Program Definition pair_ofun {A B C}
        `{OType A} `{OType B} `{OType C}
        (f: A -o> B) (g: A -o> C) : A -o> (B * C) :=
  {| ofun_app := fun a => (ofun_app f a, ofun_app g a) |}.
Next Obligation.
  intros a1 a2 Ra; split; apply ofun_Proper; assumption.
Qed.

Instance Proper_pair_ofun A B C `{OType A} `{OType B} `{OType C} :
  Proper (oleq ==> oleq ==> oleq) (pair_ofun (A:=A) (B:=B) (C:=C)).
Proof.
  intros a1 a2 Ra b1 b2 Rb c1 c2 Rc; simpl; split.
  - apply Ra; assumption.
  - apply Rb; assumption.
Qed.


(* compose commutes with pair *)
Lemma compose_f_pair_ofun A B C D
      `{OType A} `{OType B} `{OType C} `{OType D}
      (f: A -o> B) (g: B -o> C) (h: B -o> D) :
  oeq (compose_ofun f (pair_ofun g h))
           (pair_ofun (compose_ofun f g) (compose_ofun f h)).
  split; intros a1 a2 Ra; simpl; split; repeat apply ofun_Proper; assumption.
Qed.

(* The first projection ofun *)
Definition fst_ofun {A B} `{OType A} `{OType B} : A * B -o> A :=
  {| ofun_app := fst; ofun_Proper := _ |}.

(* The second projection ofun *)
Definition snd_ofun {A B} `{OType A} `{OType B} : A * B -o> B :=
  {| ofun_app := snd; ofun_Proper := _ |}.

(* Composing pair with fst gives the first function in the pair *)
Lemma compose_pair_fst A B C `{OType A} `{OType B} `{OType C}
      (f: A -o> B) (g: A -o> C) :
  oeq (compose_ofun (pair_ofun f g) fst_ofun) f.
  split; intros a1 a2 Ra; simpl; apply ofun_Proper; assumption.
Qed.

(* Composing pair with snd gives the second function in the pair *)
Lemma compose_pair_snd A B C `{OType A} `{OType B} `{OType C}
      (f: A -o> B) (g: A -o> C) :
  oeq (compose_ofun (pair_ofun f g) snd_ofun) g.
  split; intros a1 a2 Ra; simpl; apply ofun_Proper; assumption.
Qed.

(* Taking the pair of fst and snd is the identity *)
Lemma pair_fst_snd_eta A B `{OType A} `{OType B} :
  oeq (pair_ofun (fst_ofun (A:=A) (B:=B)) snd_ofun) id_ofun.
  split; intros p1 p2 Rp; destruct Rp; split; simpl; assumption.
Qed.


(***
 *** Currying and UnCurrying
 ***)

(* Curry an OFun *)
Program Definition ofun_curry {A B C} `{OType A} `{OType B} `{OType C}
        (ofun : (A * B) -o> C)
  : A -o> (B -o> C) :=
  {| ofun_app :=
       fun a =>
         {| ofun_app := fun b => ofun_app ofun (a,b);
            ofun_Proper := _ |};
     ofun_Proper := _ |}.
Next Obligation.
Proof.
  intros b1 b2 Rb. apply ofun_Proper.
  split; [ reflexivity | assumption ].
Qed.
Next Obligation.
Proof.
  intros a1 a2 Ra b1 b2 Rb; simpl.
  apply ofun_Proper; split; assumption.
Qed.

(* Uncrry an OFun *)
Program Definition ofun_uncurry {A B C}
        `{OType A} `{OType B} `{OType C}
        (ofun : A -o> (B -o> C))
  : (A * B) -o> C :=
  {| ofun_app :=
       fun ab => ofun_app (ofun_app ofun (fst ab)) (snd ab);
     ofun_Proper := _ |}.
Next Obligation.
Proof.
  intros ab1 ab2 Rab. destruct Rab as [ Ra Rb ].
  exact (ofun_Proper ofun (fst ab1) (fst ab2) Ra (snd ab1) (snd ab2) Rb).
Qed.


(* ofun_curry is Proper *)
Instance Proper_ofun_curry A B C `{OType A} `{OType B} `{OType C}
  : Proper (oleq ==> oleq) (ofun_curry (A:=A) (B:=B) (C:=C)).
Proof.
  intros f1 f2 Rf a1 a2 Ra b1 b2 Rb. apply Rf. split; assumption.
Qed.

(* FIXME: Proper instance for ofun_uncurry *)

(* Currying and uncurrying of ofuns form an isomorphism: part 1 *)
Lemma ofun_curry_uncurry_eq A B C `{OType A} `{OType B} `{OType C}
      (f: (A * B) -o> C) :
  ofun_uncurry (ofun_curry f) =o= f.
  split; intros ab1 ab2 Rab; simpl; apply ofun_Proper;
    destruct Rab; split; assumption.
Qed.

(* Currying and uncurrying of ofuns form an isomorphism: part 2 *)
Lemma ofun_uncurry_curry_eq A B C `{OType A} `{OType B} `{OType C}
      (f: A -o> B -o> C) :
  ofun_curry (ofun_uncurry f) =o= f.
  split; intros a1 a2 Ra b1 b2 Rb; simpl; apply Proper_ofun_app;
    try apply ofun_Proper; assumption.
Qed.


(* The S combinator for ofuns (FIXME: do we need this?) *)
Program Definition ofun_S {A B C} `{OType A} `{OType B} `{OType C}
  : (A -o> B -o> C) -o> (A -o> B) -o> A -o> C :=
  {| ofun_app :=
       fun f =>
         {| ofun_app :=
              fun g =>
                {| ofun_app := fun a => ofun_app (ofun_app f a) (ofun_app g a) |}
         |}
  |}.
Next Obligation.
  intros a1 a2 Ra; apply Proper_ofun_app; try apply ofun_Proper; assumption.
Qed.
Next Obligation.
  intros g1 g2 Rg a1 a2 Ra. simpl. apply Proper_ofun_app; try assumption.
  - apply ofun_Proper; assumption.
  - apply Rg; assumption.
Qed.
Next Obligation.
  intros f1 f2 Rf g1 g2 Rg a1 a2 Ra. simpl. apply Proper_ofun_app; try assumption.
  - intros b1 b2 Rb. apply Rf; assumption.
  - apply Rg; assumption.
Qed.

(* This is the S combinator, but partially applied *)
Program Definition ofun_apply {A B C}
        `{OType A} `{OType B} `{OType C}
        (f: A -o> B -o> C) (g: A -o> B) : A -o> C :=
  {| ofun_app := fun a => ofun_app (ofun_app f a) (ofun_app g a) |}.
Next Obligation.
  intros a1 a2 Ra; apply Proper_ofun_app; try apply ofun_Proper; assumption.
Qed.

Instance Proper_ofun_apply A B C `{OType A} `{OType B} `{OType C} :
  Proper (oleq ==> oleq ==> oleq) (ofun_apply (A:=A) (B:=B) (C:=C)).
Proof.
  intros a1 a2 Ra b1 b2 Rb c1 c2 Rc. simpl.
  apply Ra; try assumption. apply Rb; try assumption.
Qed.

(* compose commutes with S *)
Lemma compose_ofun_apply A B C D `{OType A} `{OType B} `{OType C} `{OType D}
      (f : A -o> B) (g: B -o> C -o> D) h :
  compose_ofun f (ofun_apply g h)
  =o= ofun_apply (compose_ofun f g) (compose_ofun f h).
  split; intros a1 a2 Ra; simpl; rewrite Ra; reflexivity.
Qed.

(* compose commutes with currying *)
Lemma compose_ofun_curry A B C D `{OType A} `{OType B} `{OType C} `{OType D}
      (f: A -o> B) (g: B * C -o> D) :
  oeq (compose_ofun f (ofun_curry g))
           (ofun_curry
              (compose_ofun (pair_ofun (compose_ofun fst_ofun f) snd_ofun) g)).
  split; intros a1 a2 Ra c1 c2 Rc; simpl; rewrite Ra; rewrite Rc; reflexivity.
Qed.

(* Applying a const is just composition. Note that we add the extra OType
constraint to quantify over all possible proofs that B -o> C is an OType, so
this rule applies independently of this aOType proof. *)
Lemma ofun_apply_const A B C `{OType A} `{OType B} `{OType C}
      {OBC: OType (B -o> C)} (f: B -o> C) (g: A -o> B) :
  oeq (ofun_apply (A:=A) (const_ofun f) g) (compose_ofun g f).
  split; intros a1 a2 Ra; simpl; rewrite Ra; reflexivity.
Qed.

(* We can simplify ofun_S used with ofun_curry *)
Lemma ofun_apply_ofun_curry A B C `{OType A} `{OType B} `{OType C} f g :
  oeq (ofun_apply (A:=A) (B:=B) (C:=C) (ofun_curry f) g)
           (compose_ofun (pair_ofun id_ofun g) f).
  split; intros a1 a2 Ra; simpl; apply ofun_Proper; split;
    try apply ofun_Proper; assumption.
Qed.


(***
 *** Sums
 ***)

(* Proper function for inl *)
Program Definition inl_ofun {A B} `{OType A} `{OType B} : A -o> A + B :=
  {| ofun_app := inl; ofun_Proper := _ |}.
Next Obligation.
  intros x y Rxy. left. assumption.
Defined.

(* Proper function for inr *)
Program Definition inr_ofun {A B} `{OType A} `{OType B} : B -o> A + B :=
  {| ofun_app := inr; ofun_Proper := _ |}.
Next Obligation.
  intros x y Rxy. right. assumption.
Defined.

(* Proper function for eliminating sums *)
Program Definition sum_elim_ofun {A B C} `{OType A} `{OType B} `{OType C} :
  (A -o> C) -o> (B -o> C) -o> A + B -o> C :=
  {| ofun_app :=
       fun f1 =>
         {| ofun_app :=
              fun f2 =>
                {| ofun_app := fun (s : A+B) =>
                                 match s return C with
                                 | inl a => ofun_app f1 a
                                 | inr b => ofun_app f2 b
                                 end |} |} |}.
Next Obligation.
  intros s1 s2 Rs. destruct Rs; apply ofun_Proper; assumption.
Defined.
Next Obligation.
  intros f2 f2' Rf2 a1 a2 Ra. destruct Ra; simpl.
  - apply ofun_Proper; assumption.
  - apply Rf2; assumption.
Defined.
Next Obligation.
  intros f1 f1' Rf1 f2 f2' Rf2 a1 a2 Ra. destruct Ra; simpl.
  - apply Rf1; assumption.
  - apply Rf2; assumption.
Defined.

Lemma osum_elim_eta  {A B} `{OType A} `{OType B} :
  ofun_app (ofun_app (sum_elim_ofun (A:=A) (B:=B)) inl_ofun) inr_ofun =o= id_ofun.
Proof.
  split; intros s1 s2 Rs; destruct Rs; simpl; constructor; assumption.
Qed.


(***
 *** Boolean Operations
 ***)

Program Definition ite_ofun {A} `{OType A} : bool -o> A -o> A -o> A :=
  {| ofun_app :=
       fun (b:bool) =>
         {| ofun_app :=
              fun x =>
                {| ofun_app :=
                     fun y => if b then x else y |} |} |}.
Next Obligation.
  unfold OFunProper, ProperPair; intros a1 a2 Ra.
  destruct b; [ reflexivity | apply Ra ].
Defined.
Next Obligation.
  unfold OFunProper, ProperPair; intros a1 a2 R12 a3 a4 R34.
  destruct b; [ apply R12 | assumption ].
Defined.
Next Obligation.
  intro; intros. simpl.
  destruct x; destruct y; try discriminate; assumption.
Defined.


(***
 *** Propositional Connectives
 ***)

(* The universal combinator as an ordered function *)
Program Definition forall_ofun `{OType} : (A -o> Prop) -o> Prop :=
  {| ofun_app := fun (P:A -o> Prop) => forall x, ofun_app P x |}.
Next Obligation.
  intros P1 P2 R12 pf z. apply (R12 _ _ (reflexivity _) (pf z)).
Defined.

(* The existential combinator as an ordered function *)
Program Definition exists_ofun `{OType} : (A -o> Prop) -o> Prop :=
  {| ofun_app := fun P => exists x, ofun_app P x |}.
Next Obligation.
  intros P1 P2 R12 pf. destruct pf as [z pf].
  exists z. apply (R12 _ _ (reflexivity _) pf).
Defined.

(* The double existential combinator as an ordered function *)
Program Definition exists2_ofun `{OType}
  : (A -o> Prop) -o> (A -o> Prop) -o> Prop :=
  {| ofun_app :=
       fun P =>
         {| ofun_app := fun Q => exists2 x, ofun_app P x & ofun_app Q x |} |}.
Next Obligation.
  intros P1 P2 R12 pf. destruct pf as [z pf1 pf2].
  exists z; try assumption. apply (R12 _ _ (reflexivity _) pf2).
Defined.
Next Obligation.
  intros P1 P2 RP Q1 Q2 RQ pf. destruct pf as [z pf1 pf2].
  exists z; [ apply (RP _ _ (reflexivity _) pf1)
            | apply (RQ _ _ (reflexivity _) pf2) ].
Defined.

(* An existential with both a positive and a negative component *)
Program Definition exists2flip_ofun `{OType} : (A -o> Prop) -o>
                                               (Flip A -o> Prop) -o> Prop :=
  {| ofun_app :=
       fun P1 =>
         {| ofun_app :=
              fun P2 =>
                exists2 x, ofun_app P1 x & ofun_app P2 (flip x) |} |}.
Next Obligation.
  intro; intros. intros [z pf1 pf2].
  exists z; try assumption. apply (H0 _ _ (reflexivity _)). assumption.
Defined.
Next Obligation.
  intro; intros. intros [z pf1 pf2].
  exists z; [ apply (H0 _ _ (reflexivity _)) |
              apply (H1 _ _ (reflexivity _)) ]; assumption.
Defined.


(* Conjunction as an ordered function *)
Program Definition and_ofun : Prop -o> Prop -o> Prop :=
  {| ofun_app := fun P1 => {| ofun_app := fun P2 => P1 /\ P2 |} |}.
Next Obligation.
  intros P2' P2'' R2 H0. destruct H0; split; try assumption.
  apply R2; assumption.
Defined.
Next Obligation.
  intros P1 P1' R1 P2 P2' R2 H0. destruct H0.
  split; [ apply R1 | apply R2 ]; assumption.
Defined.

(* Disjunction as an ordered function *)
Program Definition or_ofun : Prop -o> Prop -o> Prop :=
  {| ofun_app := fun P1 => {| ofun_app := fun P2 => P1 \/ P2 |} |}.
Next Obligation.
  intros P2' P2'' R2 H0.
  destruct H0; [ left | right; apply R2 ]; assumption.
Defined.
Next Obligation.
  intros P1 P1' R1 P2 P2' R2 H0.
  destruct H0; [ left; apply R1 | right; apply R2 ]; assumption.
Defined.

(* Implication as an ordered function *)
Program Definition impl_ofun : Flip Prop -o> Prop -o> Prop :=
  {| ofun_app :=
       fun (P1:Flip Prop) =>
         {| ofun_app := fun (P2:Prop) => unflip P1 -> P2 |} |}.
Next Obligation.
  intros P2 P2' R2 pf12 pf1.
  apply R2; apply pf12; apply pf1; assumption.
Defined.
Next Obligation.
  intros P1 P1' R1 P2 P2' R2 pfx1 pfy.
  apply R2; apply pfx1; apply R1; apply pfy.
Defined.

(* Ordered type relations are themselves ordered propositional functions *)
Program Definition oleq_ofun `{OType} : Flip A -o> A -o> Prop :=
  {| ofun_app := fun (x:Flip A) =>
                   {| ofun_app := fun y => oleq (unflip x) y |} |}.
Next Obligation.
  intros a1 a2 Ra pf. etransitivity; eassumption.
Defined.
Next Obligation.
  intros a1 a2 R12 a3 a4 R34; simpl; intro pf.
  etransitivity; try eassumption.
  etransitivity; try eassumption.
Defined.
