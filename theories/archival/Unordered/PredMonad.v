Require Export PredMonad.Unordered.Monad.


(***
 *** The Predicate Monad Class
 ***)

Section PredMonad.
  Context {M : Type -> Type} {PM : Type -> Type} `{MonadOps PM}.

  (* FIXME: the universe constraints on M and PM could be different...? *)
  Class PredMonadOps `{MonadOps M} `{MonadOps PM} :=
    { forallP: forall {A B: Type}, (A -> PM B) -> PM B;
      existsP: forall {A B: Type}, (A -> PM B) -> PM B;
      impliesP: forall {A: Type}, PM A -> PM A -> PM A;
      liftP: forall {A: Type}, M A -> PM A
    }.

  Context `{PredMonadOps}.

  Definition andP {A:Type} (P1 P2: PM A) : PM A :=
    forallP (fun b:bool => elimBool b P1 P2).

  Class PredMonad : Prop :=
  {
    (* Both M and PM must be monads *)
    predmonad_monad_M :> Monad M;
    predmonad_monad_PM :> Monad PM;

    (* forallP is a complete meet operator. The laws for it being a lower bound
    and the greatest lower bound actually correspond to forall-elimination and
    forall-introduction rules, respectively. *)
    predmonad_forallP_elim :
      forall {A B} `{LR A} `{LR B} (f: A -> PM B) a,
        Proper lr_leq f -> Proper lr_leq a ->
        forallP f <~ f a;
    predmonad_forallP_intro :
      forall {A B} `{LR A} `{LR B} (f: A -> PM B) P,
        Proper lr_leq f -> Proper lr_leq P ->
        (forall a, P <~ f a) -> P <~ forallP f;

    (* existsP is a complete join operator. The laws for it being an upper bound
    and the least upper bound actually correspond to exists-introduction and
    exists-elimination rules, respectively. *)
    predmonad_existsP_intro :
      forall {A B} `{LR A} `{LR B} (f: A -> PM B) a,
        Proper lr_leq f -> Proper lr_leq a ->
        f a <~ existsP f;
    predmonad_existsP_elim :
      forall {A B} `{LR A} `{LR B} (f: A -> PM B) P,
        Proper lr_leq f -> Proper lr_leq P ->
        (forall a, f a <~ P) -> existsP f <~ P;

    (* impliesP is a right adjoint to andP, the laws for which correspond to
    implication introduction and generalization of implication elimination
    (where taking P1 = (impliesP P2 P3) yields the standard elimination rule) *)
    predmonad_impliesP_intro :
      forall {A} `{LR A} (P1 P2 P3: PM A),
        Proper lr_leq P1 -> Proper lr_leq P2 -> Proper lr_leq P3 ->
        andP P1 P2 <~ P3 -> P1 <~ impliesP P2 P3;
    predmonad_impliesP_elim :
      forall {A} `{LR A} (P1 P2 P3: PM A),
        Proper lr_leq P1 -> Proper lr_leq P2 -> Proper lr_leq P3 ->
        P1 <~ impliesP P2 P3 -> andP P1 P2 <~ P3;

    (* Introduction and elimination rules for assertP *)
(*
    predmonad_assertP_intro :
      forall {A:Type} `{Order A} (P:PM A),
        entailsP P (assertP True);
    predmonad_assertP_elim :
      forall {A:Type} `{Order A} (P:PM A) (Pr:Prop),
        (Pr -> entailsP (assertP True) P) ->
        entailsP (assertP Pr) P;
*)

    (* laws about liftP *)
    predmonad_liftP_return :
      forall {A} `{LR A} (a:A),
        Proper lr_leq a ->
        liftP (returnM a) ~~ returnM a;
    predmonad_liftP_bind :
      forall {A B} `{LR A} `{LR B} m (f:A -> M B),
        Proper lr_leq m -> Proper lr_leq f ->
        liftP (bindM m f) ~~ bindM (liftP m) (fun x => liftP (f x));

    (* FIXME: need laws about how the combinators interact *)

    (* Laws about the operators being proper *)
    predmonad_forallP_proper {A B} `{LR A} `{LR B} :
      Proper lr_leq (forallP : (A -> PM B) -> PM B);
    predmonad_existsP_proper {A B} `{LR A} `{LR B} :
      Proper lr_leq (existsP : (A -> PM B) -> PM B);
    predmonad_impliesP_proper {A} `{LR A} :
      Proper lr_leq (impliesP : PM A -> PM A -> PM A);
  }.

End PredMonad.

Arguments PredMonadOps M PM {_} {_}.
Arguments PredMonad M PM {_} {_} {_}.


(***
 *** Defined Predicate Monad Operators
 ***)

(* We define m |= P as holding iff (liftP m) entails P *)
Definition satisfiesP `{PredMonadOps} `{LR_Op} (m:M A) (P:PM A) :=
  liftP m <~ P.

(* Notation for satisfaction *)
Infix "|=" := satisfiesP (at level 80).

(* Disjunction is definable in terms of the existential *)
Definition orP `{PredMonadOps} {A} (P1 P2: PM A) : PM A :=
  existsP (fun b:bool => elimBool b P1 P2).

(* True and false, which correspond to top and bottom, respectively *)
Definition trueP `{PredMonadOps} {A} : PM A :=
  existsP (fun pm:PM A => pm).
Definition falseP `{PredMonadOps} {A} : PM A :=
  forallP (fun pm:PM A => pm).

(* Negation, which (as in normal Coq) is implication of false *)
Definition notP `{PredMonadOps} {A} (P: PM A) : PM A :=
  impliesP P falseP.

(* An assertion inside a predicate monad *)
Definition assertP `{PredMonadOps} (P:Prop) : PM unit :=
  existsP (fun pf:P => trueP).


(***
 *** Theorems about Predicate Monads
 ***)

Section PredMonad_thms.

Context `{PredMonad}.

(** True is the top element **)
Lemma predmonad_trueP_intro `{LR} (P: PM A) : Proper lr_leq P -> P <~ trueP.
  intro; apply (predmonad_existsP_intro (fun pm => pm) P);
    prove_lr_proper.
Qed.

(** False is the bottom element **)
Lemma predmonad_falseP_elim `{LR} (P: PM A) : Proper lr_leq P -> falseP <~ P.
  intro; apply (predmonad_forallP_elim (fun pm => pm) P); prove_lr_proper.
Qed.

(** Conjunction satisfies the usual rules **)
Lemma predmonad_andP_intro `{LR} (P1 P2 P: PM A) :
  Proper lr_leq P1 -> Proper lr_leq P2 -> Proper lr_leq P ->
  P <~ P1 -> P <~ P2 -> P <~ andP P1 P2.
  intros; apply predmonad_forallP_intro; try prove_lr_proper.
  (* FIXME HERE: why is this not applied by the prove_lr tactic? *)
  apply Proper_elimBool.
  intro b; destruct b; prove_lr.
Qed.

Lemma predmonad_andP_elim1 `{LR} (P1 P2: PM A) :
  Proper lr_leq P1 -> Proper lr_leq P2 -> andP P1 P2 <~ P1.
  intros; apply (predmonad_forallP_elim (fun b => elimBool b P1 P2) true);
    prove_lr_proper.
  apply Proper_elimBool.
Qed.

Lemma predmonad_andP_elim2 `{LR} (P1 P2: PM A) :
  Proper lr_leq P1 -> Proper lr_leq P2 -> andP P1 P2 <~ P2.
  intros; apply (predmonad_forallP_elim (fun b => elimBool b P1 P2) false);
    prove_lr_proper.
  apply Proper_elimBool.
Qed.

(** Disjunction satisfies the usual rules **)
Lemma predmonad_orP_intro1 `{LR} (P1 P2: PM A) :
  Proper lr_leq P1 -> Proper lr_leq P2 -> P1 <~ orP P1 P2.
  intros; apply (predmonad_existsP_intro (fun b => elimBool b P1 P2) true);
    prove_lr_proper.
  apply Proper_elimBool.
Qed.

Lemma predmonad_orP_intro2 `{LR} (P1 P2: PM A) :
  Proper lr_leq P1 -> Proper lr_leq P2 -> P2 <~ orP P1 P2.
  intros; apply (predmonad_existsP_intro (fun b => elimBool b P1 P2) false);
    prove_lr_proper.
  apply Proper_elimBool.
Qed.

Lemma predmonad_orP_elim `{LR} (P1 P2 P: PM A) :
  Proper lr_leq P1 -> Proper lr_leq P2 -> Proper lr_leq P ->
  P1 <~ P -> P2 <~ P -> orP P1 P2 <~ P.
  intros; apply predmonad_existsP_elim;
    prove_lr_proper; [ apply Proper_elimBool | ].
  intro x; destruct x; assumption.
Qed.


(*

FIXME HERE NOW: prove all these!

(** Nested foralls combine **)
Lemma predmonad_forallP_forallP {A B C} `{LR C}
            (Q : A -> B -> PM C) :
  forallP (fun x => forallP (fun y => Q x y)) ==
  forallP (fun xy => Q (fst xy) (snd xy)).
apply predmonad_entailsP_equalsM; split.
apply predmonad_forallP_intro; intro p; destruct p.
unfold fst, snd.
transitivity (forallP (fun y => Q a y)).
apply (predmonad_forallP_elim (fun x => _) a).
apply (predmonad_forallP_elim (fun y => _) b).
apply predmonad_forallP_intro; intro x.
apply predmonad_forallP_intro; intro y.
apply (predmonad_forallP_elim (fun xy => _) (x,y)).
Qed.

(** Nested exists combine **)
Lemma predmonad_existsP_existsP {A B C} `{LR C}
            (Q : A -> B -> PM C) :
  existsP (fun x => existsP (fun y => Q x y)) ==
  existsP (fun xy => Q (fst xy) (snd xy)).
apply predmonad_entailsP_equalsM; split.
apply predmonad_existsP_elim; intro x.
apply predmonad_existsP_elim; intro y.
apply (predmonad_existsP_intro (fun xy => Q (fst xy) (snd xy)) (x,y)).
apply predmonad_existsP_elim; intro p; destruct p.
unfold fst, snd.
transitivity (existsP (fun y => Q a y)).
apply (predmonad_existsP_intro (fun y => Q a y) b).
apply (predmonad_existsP_intro (fun x : A => existsP (fun y : B => Q x y)) a).
Qed.


(** Commutativity and Associativity of andP and orP **)
Lemma predmonad_andP_commutative `{LR}
            (P1 P2: PM A) : andP P1 P2 == andP P2 P1.
apply predmonad_entailsP_equalsM; split;
repeat (first [ apply predmonad_andP_intro | apply predmonad_andP_elim1
                | apply predmonad_andP_elim2 ]).
Qed.

Lemma predmonad_andP_associative `{LR}
            (P1 P2 P3: PM A) : andP P1 (andP P2 P3) == andP (andP P1 P2) P3.
apply predmonad_entailsP_equalsM; split;
repeat (apply predmonad_andP_intro);
first [ apply predmonad_andP_elim1 | apply predmonad_andP_elim2
      | transitivity (andP P2 P3);
        first [ apply predmonad_andP_elim1 | apply predmonad_andP_elim2 ]
      | transitivity (andP P1 P2);
        first [ apply predmonad_andP_elim1 | apply predmonad_andP_elim2 ]].
Qed.

Lemma predmonad_orP_commutative `{LR}
            (P1 P2: PM A) : orP P1 P2 == orP P2 P1.
apply predmonad_entailsP_equalsM; split;
repeat (first [ apply predmonad_orP_elim | apply predmonad_orP_intro1
                | apply predmonad_orP_intro2 ]).
Qed.

Lemma predmonad_orP_associative `{LR}
            (P1 P2 P3: PM A) : orP P1 (orP P2 P3) == orP (orP P1 P2) P3.
apply predmonad_entailsP_equalsM; split;
repeat (apply predmonad_orP_elim);
first [ apply predmonad_orP_intro1 | apply predmonad_orP_intro2
      | transitivity (orP P2 P3);
        first [ apply predmonad_orP_intro1 | apply predmonad_orP_intro2 ]
      | transitivity (orP P1 P2);
        first [ apply predmonad_orP_intro1 | apply predmonad_orP_intro2 ]].
Qed.


(** Theorems that the combinators mostly mean what we expect for satisfiesP **)
Theorem forallP_forall {A B} `{LR B} m (Q: A -> PM B) :
  m |= forallP Q <-> forall x, m |= Q x.
unfold satisfiesP; split; intros.
transitivity (forallP Q); [ assumption | ].
apply predmonad_forallP_elim.
apply predmonad_forallP_intro; assumption.
Qed.

Theorem andP_and `{LR} m (P1 P2: PM A) :
  m |= andP P1 P2 <-> m |= P1 /\ m |= P2.
unfold andP.
transitivity (forall b:bool, m |= if b then P1 else P2).
apply forallP_forall.
repeat split.
apply (H4 true).
apply (H4 false).
intros; destruct H4; destruct b; assumption.
Qed.

(* NOTE: the converse does not hold; e.g., a stateful computation that satisfies
existsP Q might satisfy Q x for different x depending on the input state *)
Theorem existsP_exists {A B} `{LR B} m (Q: A -> PM B) x :
  m |= Q x -> m |= existsP Q.
  unfold satisfiesP.
  intro.
  transitivity (Q x); [ assumption | apply predmonad_existsP_intro ].
Qed.

(* NOTE: the converse does not hold; e.g., a stateful computation that satisfies
orP P1 P2 might satisfy P1 for some inputs and P2 for others *)
Theorem orP_or `{LR} m (P1 P2: PM A) :
  m |= P1 \/ m |= P2 -> m |= orP P1 P2.
  unfold satisfiesP.
  intros; destruct H4.
  transitivity P1; [ assumption |  apply predmonad_orP_intro1 ].
  transitivity P2; [ assumption |  apply predmonad_orP_intro2 ].
Qed.

(** Distributivity lemmas **)

(* andP distributes over existsP *)
Lemma predmonad_andP_existsP {A B} `{LR B}
            (P: PM B) (Q: A -> PM B) :
  andP P (existsP Q) == existsP (fun x => andP P (Q x)).
apply predmonad_entailsP_equalsM; split.
rewrite predmonad_andP_commutative.
apply predmonad_impliesP_elim.
apply predmonad_existsP_elim; intro a.
apply predmonad_impliesP_intro.
rewrite predmonad_andP_commutative.
apply (predmonad_existsP_intro (fun x => andP P (Q x)) a).
apply predmonad_existsP_elim; intro a.
apply predmonad_andP_intro.
apply predmonad_andP_elim1.
transitivity (Q a).
apply predmonad_andP_elim2.
apply (predmonad_existsP_intro).
Qed.

(* Implication commutes with forall *)
Theorem predmonad_forallP_impliesP {A B} `{LR B}
      P (Q: A -> PM B) :
  impliesP P (forallP Q) == forallP (fun x => impliesP P (Q x)).
  rewrite predmonad_entailsP_equalsM; split.
  apply predmonad_forallP_intro; intro.
  apply predmonad_impliesP_intro.
  transitivity (forallP Q).
  apply predmonad_impliesP_elim; reflexivity.
  apply predmonad_forallP_elim.

  apply predmonad_impliesP_intro.
  apply predmonad_forallP_intro; intro.
  apply predmonad_impliesP_elim.
  apply (predmonad_forallP_elim (fun x : A => impliesP P (Q x)) a).
Qed.

(* impliesP reverse-distributes over orP (the implication only goes one way) *)
Theorem predmonad_existsP_impliesP
            `{LR} P (Q1 Q2: PM A) :
  entailsP (orP (impliesP P Q1) (impliesP P Q2)) (impliesP P (orP Q1 Q2)).
apply predmonad_orP_elim.
apply predmonad_impliesP_proper.
reflexivity.
apply predmonad_orP_intro1.
apply predmonad_impliesP_proper.
reflexivity.
apply predmonad_orP_intro2.
Qed.

(*
Lemma predmonad_commute_existsP_impliesP {A B} P (Q: A -> PM B) :
  impliesP P (existsP Q) == existsP (fun x => impliesP P (Q x)).
  intros; apply predmonad_equivalence; intros.
  repeat (first [ rewrite predmonad_impliesP_implies
                | rewrite predmonad_existsP_exists ]).
  split; intros.
  destruct (H0 H1).
*)

 *)

(* FIXME HERE: can we prove that bind commutes with forall? *)

End PredMonad_thms.


(***
 *** The Set monad as a predicate monad for the Identity monad
 ***)

Section IdentityPredMonad.

(* The type of sets over a carrier type X *)
Inductive SetM (X:Type) : Type := setM_compr (F:X -> Prop).
Arguments setM_compr {X} _.

(* Element of a SetM = elimination of SetM *)
Definition setM_elem {X} (m:SetM X) : X -> Prop :=
  let (F) := m in F.

(* The subset relation *)
Definition setM_subset {X} : relation (SetM X) :=
  fun m1 m2 => forall x, setM_elem m1 x -> setM_elem m2 x.

(* The union of two SetMs *)
Definition setM_union {A} (m1 m2 : SetM A) : SetM A :=
  setM_compr (fun x => setM_elem m1 x \/ setM_elem m2 x).

(* The intersection of two SetMs *)
Definition setM_intersect {A} (m1 m2 : SetM A) : SetM A :=
  setM_compr (fun x => setM_elem m1 x /\ setM_elem m2 x).

(* Build a SetM from an existential, i.e., the set of all z such that there
exists a y such that z is in (f y) *)
Definition setM_exists {A B} (f:A -> SetM B) : SetM B :=
  setM_compr (fun z => exists y, setM_elem (f y) z).

(* Build a SetM from an universal, i.e., the set of all z such that, for all y,
z is in (f y) *)
Definition setM_forall {A B} (f:A -> SetM B) : SetM B :=
  setM_compr (fun z => forall y, setM_elem (f y) z).

(* The set that is complete or empty depending on whether P holds *)
Definition setM_assert A (P:Prop) : SetM A :=
  setM_compr (fun z => P).

(* The downward closure of a set, i.e., the set of all objects x <~ z for some z
in the set *)
Definition downward_closure `{LR_Op} (m:SetM A) : SetM A :=
  setM_compr (fun x => exists2 z, x <~ z & setM_elem m z).

(* Elements of the downward closure are Proper *)
Lemma downward_closure_Proper `{LR} m x :
  setM_elem (downward_closure m) x -> Proper lr_leq x.
  intro x_elem; destruct x_elem; assumption_semi_refl.
Qed.

(* Valid elements of a set are in the downward closure *)
Lemma elem_downward_closure `{LR} m x :
  Proper lr_leq x -> setM_elem m x -> setM_elem (downward_closure m) x.
  intros Px x_elem; exists x; assumption.
Qed.

(* The LR for SetM says that the greater set, m2, has to "cover" all elements of
m1 with greater elements, and that m2 only contains "valid" elements (the fact
that m1 only contains valid elements follows from the first property) *)
Record LRSetM `{LR_Op} (m1 m2: SetM A) : Prop :=
  { LRSetM_subset : setM_subset m1 (downward_closure m2);
    LRSetM_Proper : forall x, setM_elem m2 x -> Proper lr_leq x }.

Instance LR_Op_SetM `{LR_Op} : LR_Op (SetM A) := LRSetM.

(* If a SetM is Proper then all its elements are Proper *)
Lemma setM_elem_Proper `{LR} m x :
  Proper lr_leq m -> setM_elem m x -> Proper lr_leq x.
  intros Pm x_elem; apply (LRSetM_Proper m m); assumption.
Qed.

(* If a SetM is <~ any other set then all its elements are Proper *)
Lemma setM_elem_Proper_l `{LR} m1 m2 x :
  m1 <~ m2 -> setM_elem m1 x -> Proper lr_leq x.
  intros Rm x_elem; destruct (LRSetM_subset _ _ Rm _ x_elem); assumption_semi_refl.
Qed.

(* If a SetM is ~> any other set then all its elements are Proper *)
Lemma setM_elem_Proper_r `{LR} m1 m2 x :
  m1 <~ m2 -> setM_elem m2 x -> Proper lr_leq x.
  intros Pm x_elem; apply (LRSetM_Proper m1 m2); assumption.
Qed.


(* The logical relation for SetM is a valid logical relation *)
Instance LR_SetM `{LR} : LR (SetM A).
Proof.
  constructor; constructor; unfold lr_leq, LR_Op_SetM.
  - constructor; intros m1 m2 Rm; constructor; intros x elem;
      try apply elem_downward_closure; try assumption;
        try (apply (setM_elem_Proper_l m1 m2); assumption);
        apply (setM_elem_Proper_r m1 m2); assumption.
  - intros m1 m2 m3 R12 R23; constructor; intros x x_elem.
    + destruct (LRSetM_subset _ _ R12 _ x_elem) as [ y Rxy y_elem ].
      destruct (LRSetM_subset _ _ R23 _ y_elem) as [ z Ryz z_elem ].
      exists z; [ transitivity y | ]; assumption.
    + apply (setM_elem_Proper_r m2 m3); assumption.
Qed.

Instance SetM_MonadOps : MonadOps SetM :=
  { returnM := fun {A} x => setM_compr (fun z => x = z);
    bindM := fun {A B} m f =>
               setM_compr (fun z => exists2 y, setM_elem m y & setM_elem (f y) z);
    lrM := fun _ _ => LR_Op_SetM }.

Instance SetM_Monad : Monad SetM.
Proof.
  constructor; unfold returnM, bindM, lrM, SetM_MonadOps; intros.
  { auto with typeclass_instances. }
  { apply fun_Proper_lr_leq. intros x y Rxy.
    constructor; intros z elem_z; rewrite <- elem_z.
    - exists y; [ assumption | reflexivity ].
    - assumption_semi_refl. }
  { apply fun_Proper_lr_leq; intros m1 m2 Rm.
    constructor; intros f g Rfg; constructor; intros y y_elem; destruct y_elem.
    - edestruct (LRSetM_subset (f x) (g x)) as [ z Ryz z_elem ]; try eassumption.
      apply apply_lr_leq; try assumption.
      apply (setM_elem_Proper_l _ _ _ Rm); assumption.
      exists z; try assumption.
      exists x; assumption.
    - apply (setM_elem_Proper_r (f x) (g x)); [ | assumption ].
      apply apply_lr_leq; [ assumption
                          | apply (setM_elem_Proper_l m1 m2); assumption ].
    - edestruct (LRSetM_subset (f x) (g x)) as [ z Ryz z_elem ]; try eassumption.
      apply apply_lr_leq; try assumption.
      apply (setM_elem_Proper_r _ _ _ Rm); assumption.
      exists z; try assumption.
      exists x; assumption.
    - apply (setM_elem_Proper_r (f x) (g x)); [ | assumption ].
      apply apply_lr_leq; [ assumption
                          | apply (setM_elem_Proper_r m1 m2); assumption ].
    - destruct (LRSetM_subset _ _ Rm _ H1) as [ x' Rx x'_elem ].
      edestruct (LRSetM_subset (f x) (g x')) as [ z Ryz z_elem ]; try eassumption.
      apply apply_lr_leq; try assumption.
      exists z; try assumption.
      exists x'; assumption.
    - apply (setM_elem_Proper_r (f x) (g x)); [ | assumption ].
      apply apply_lr_leq; [ assumption
                          | apply (setM_elem_Proper_r m1 m2); assumption ]. }
  { intros R1 R2 subR m1 m2 Rm1; constructor; intros x x_elem.
    - destruct (LRSetM_subset _ _ Rm1 x x_elem) as [ y Rxy y_elem ].
      exists y; [ apply subR; assumption | apply y_elem ].
    - apply subR. apply (LRSetM_Proper _ _ Rm1 _ x_elem). }
  { admit. }
  { admit. }
  { admit. }
Admitted.


(*
FIXME HERE NOW

Instance SetM_PredMonadOps : PredMonadOps Identity SetM :=
  {
    forallP := fun {A B} Q x => forall y, Q y x;
    existsP := fun {A B} Q x => exists y, Q y x;
    impliesP := fun {A} P1 P2 x => P1 x -> P2 x;
    liftP := fun {A} z x => z = x;
    entailsP := fun {A} ord P1 P2 =>
                  forall x, P1 x ->
                            exists y, ord x y /\ ord y x /\ P2 y
  }.

Instance SetM_PredMonad : PredMonad Identity SetM.
Proof.
  constructor; eauto with typeclass_instances.
  { intros; constructor; compute; intros.
    + exists x0; repeat split; try (apply (PreOrder_Reflexive)); assumption.
    + destruct (H x0 H1); destruct H3; destruct H4.
      destruct (H0 x1 H5); destruct H6; destruct H7.
      exists x2; repeat split;
        try (apply (PreOrder_Transitive _ x1)); assumption. }
  { intros. compute. repeat split; intros.
    + destruct (H x); clear H. destruct (H1 H0). clear H1; clear H3.
      repeat destruct H. exists x0; repeat split; assumption.
    + destruct (H x); clear H. destruct (H3 H0). clear H1; clear H3.
      repeat destruct H. exists x0; repeat split; assumption.
    + destruct H. destruct (H z1 H0). destruct H3. destruct H4.
      exists x; repeat split; assumption.
    + destruct H. destruct (H1 z1 H0). destruct H3. destruct H4.
      exists x; repeat split; assumption.
  }
  { red. simpl; intros.
    exists x.
    split; [ eapply equals_preorder | ].
    split; [ eapply equals_preorder | ].
    eauto. }
  { simpl. intros.
    exists x.
    split; [ eapply equals_preorder | ].
    split; [ eapply equals_preorder | ].
    intros.
    eapply H in H0.
    destruct H0. destruct H0. destruct H1.
    revert H3. instantiate (1:= y). admit. (* Requires antisymmetry of OrdOp *) }
  { simpl. intros.
    exists x.
    split; [ eapply equals_preorder | ].
    split; [ eapply equals_preorder | ].
    eauto. }
  { simpl. intros.
    destruct H0.
    eapply H in H0. eauto. }
  { simpl. intros.
    specialize (H x).
    exists x.
    split; [ eapply equals_preorder | ].
    split; [ eapply equals_preorder | ].
    intros.
    destruct H.
    { destruct y; auto. }
    { admit. (* requires antisymmetry of OrdOp *) } }
  { simpl. intros.
    destruct (H x (H0 true)).
    exists x0. destruct H1 as [ ? [ ? ? ] ].
    split; auto. split; auto.
    eapply H4. (* requires antisymmetry of OrdOp *) admit. }
  { simpl; intros.
    red. intros. split; intros; subst.
    { exists z1; split; eauto.
      compute. split; eapply equals_preorder. }
    { exists z1; split; eauto.
      compute. split; eapply equals_preorder. } }
  { simpl; intros.
    red. intros.
    split; intros.
    { exists z1. split. split; eapply equals_preorder. eauto. }
    { exists z1. split. split; eapply equals_preorder.
      destruct H. destruct H. subst; auto. } }
  { simpl. red. red. intros.
    exists x0.
    split; [ eapply equals_preorder | ].
    split; [ eapply equals_preorder | ].
    intros. specialize (H0 y0). eapply H in H0.
    2: reflexivity.
    (* antisymmetry of OrdOp *)
    admit. }
  { simpl; red. red. intros.
    exists x0.
    split; [ eapply equals_preorder | ].
    split; [ eapply equals_preorder | ].
    destruct H0. eapply H in H0; [| reflexivity ].
    admit. (* antisymmetry of OrdOp *) }
  { compute. intros.
    exists x1.
    split; [ eapply equals_preorder | ].
    split; [ eapply equals_preorder | ].
    intros.
    eapply H in H3.
    destruct H3 as [ ? [ ? [ ? ? ] ] ].
    (* antisymmetry of OrdOp *)
    admit. }
  { compute.
    intros. split; intros.
    { subst. eauto. }
    { subst. exists z1.
      (* anti-symmetry of Equals *)
      admit. } }
Admitted.
 *)

End IdentityPredMonad.
