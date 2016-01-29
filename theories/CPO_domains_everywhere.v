
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Arith.Arith_base.


(***
 *** Domains (which are just pre-orders with a fancy name)
 ***)

Class DomainOrder (A:Type) : Type :=
  approx : relation A.

(* Notation for approx *)
Notation "x '<<<' y" := (approx x y) (at level 80, no associativity).

Class Domain (A:Type) {DomainOrder:DomainOrder A} : Prop :=
  {
    domain_preorder :> PreOrder approx
  }.

(* For setoid_rewrite using approx *)
Add Parametric Relation `{Domain} : A approx
  reflexivity proved by PreOrder_Reflexive
  transitivity proved by PreOrder_Transitive
as Domain_morphism.

(* The restriction of an approximation relation to an equivalence *)
Definition approxEq `{DomainOrder} : relation A :=
  fun a1 a2 => approx a1 a2 /\ approx a2 a1.

(* Notation for approxEq *)
Notation "m1 '==' m2" := (approxEq m1 m2) (at level 80, no associativity).

(* approxEq is always an equivalence *)
Instance approxEq_Equivalence `{Domain} : Equivalence approxEq.
  constructor.
  intro m; split; reflexivity.
  intros m1 m2 H1; destruct H1; split; assumption.
  intros m1 m2 m3 H1 H2; destruct H1; destruct H2; split; transitivity m2; assumption.
Qed.

(* For setoid_rewrite using approxEq *)
Add Parametric Relation `{Domain} : A approxEq
  reflexivity proved by Equivalence_Reflexive
  symmetry proved by Equivalence_Symmetric
  transitivity proved by Equivalence_Transitive
as approxEq_morphism.

(* For rewriting the arguments of approx using approxEq *)
Instance proper_approxEq_approx `{Domain} : Proper (approxEq ==> approxEq ==> iff) approx.
  intros x1 y1 eq1 x2 y2 eq2; destruct eq1; destruct eq2; split; intro.
  transitivity x1; [ assumption | ]; transitivity x2; assumption.
  transitivity y1; [ assumption | ]; transitivity y2; assumption.
Qed.


(***
 *** Some useful domains
 ***)

(* Domains for pairs *)
Instance Pair_DomainOrder A {_:DomainOrder A} B {_:DomainOrder B} :
  DomainOrder (A*B) :=
  fun p1 p2 => approx (fst p1) (fst p2) /\ approx (snd p1) (snd p2).

Instance Pair_Domain A `{Domain A} B `{Domain B} : Domain (prod A B).
  repeat constructor; try reflexivity; destruct H1; destruct H2.
  transitivity (fst y); assumption.
  transitivity (snd y); assumption.
Qed.


(***
 *** Complete Partial Orders
 ***
 *** Technically, these are omega-complete preorders, since cpo_sup only deals
 *** with countable chains and we drop antisymmetry.
 ***)

(* States that a is an upper bound of chain *)
Definition upper_bound {A} (R: relation A) (chain: nat -> A) a :=
  forall n, R (chain n) a.

(* States that a is no greater than any upper bound of chain *)
Definition below_upper_bounds {A} (R: relation A) (chain: nat -> A) a :=
  forall a', upper_bound R chain a' -> R a a'.

(* The supremum function, which works on any countable set of A's *)
Class CPOSupremum (A:Type) {DomainOrder:DomainOrder A} : Type :=
  cpo_sup : (nat -> A) -> A.

(* The definition of a directed countable set *)
Definition directed `{CPOSupremum} (chain: nat -> A) : Prop :=
  forall n1 n2, exists n',
    approx (chain n1) (chain n') /\ approx (chain n2) (chain n').

(* (Omega)-CPO = preorder with least upper bounds of directed countable sets *)
Class CPO (A:Type) {DomainOrder:DomainOrder A}
      {CPOSupremum:@CPOSupremum A DomainOrder} : Prop :=
  {
    cpo_preorder :> Domain A;
    cpo_sup_upper_bound :
      forall chain, directed chain -> upper_bound approx chain (cpo_sup chain);
    cpo_sup_least :
      forall chain,
        directed chain -> below_upper_bounds approx chain (cpo_sup chain)
  }.

(* Two supremums are equivalent iff the chains dominate each other *)
Lemma supremums_equivalent `{CPO} chain1 chain2 :
  directed chain1 -> directed chain2 ->
  (forall n1, exists n2, approx (chain1 n1) (chain2 n2)) ->
  (forall n2, exists n1, approx (chain2 n2) (chain1 n1)) ->
  approxEq (cpo_sup chain1) (cpo_sup chain2).
  intros; split; apply cpo_sup_least; try assumption; intro n.
  destruct (H2 n) as [ n' ]; transitivity (chain2 n'); [ assumption | ].
  apply cpo_sup_upper_bound; assumption.
  destruct (H3 n) as [ n' ]; transitivity (chain1 n'); [ assumption | ].
  apply cpo_sup_upper_bound; assumption.
Qed.


(***
 *** Scott-Continuous Functions
 ***)

(* Scott-continuity = monotonicity + preservation of cpo_sup

NOTE: We put monotonicity as part of the definition of Scott-continuity because
we don't include antisymmetry in our definition of CPO, and the proof that
Scott-continuity implies monotonicity requires a congruence closure step to
prove that (f a2) = (f (cpo_sup (fun n => match n with | 0 => a1 | S _ => a2)))
and this does not work when we only know that a2 is equivalent up to R to this
supremum, not that it is equal. *)
Definition scott_continuous `{CPO} (f : A -> A) : Prop :=
  Proper (approx ==> approx) f /\
  (forall chain,
     directed chain ->
     approxEq (f (cpo_sup chain)) (cpo_sup (fun n => f (chain n)))).


(***
 *** Pointed (omega-)CPOs
 ***)

(* The bottom of a PCPO *)
Class PCPOBottom (A:Type) {DomainOrder:DomainOrder A} : Type :=
  pcpo_bottom : A.

(* PCPO = CPO + a bottom *)
Class PCPO (A:Type) {DomainOrder:DomainOrder A}
      {CPOSupremum:CPOSupremum A (DomainOrder:=DomainOrder)}
      {PCPOBottom:PCPOBottom A (DomainOrder:=DomainOrder)} : Prop :=
  {
    pcpo_cpo :> CPO A (CPOSupremum:=CPOSupremum);
    pcpo_least_element : forall a, approx pcpo_bottom a
  }.


(***
 *** Every Scott-continuous function has a least fixed-point
 ***)

(* Fixed-points of f, modulo the symmetric closure of R *)
Definition fixed_point `{DomainOrder} (f: A -> A) a :=
  approxEq (f a) a.

(* Least fixed-points of f, modulo the symmetric closure of R *)
Definition least_fixed_point `{DomainOrder} (f: A -> A) a :=
  fixed_point f a /\
  forall a', fixed_point f a' -> approx a a'.

(* Iterate a function n times *)
Fixpoint iterate_f {A} n (f: A -> A) :=
  match n with
    | 0 => fun x => x
    | S n' => fun x => f (iterate_f n' f x)
  end.

(* (f^n _|_) `R` (f^(n+1) _|_) for monotone f *)
Lemma iterate_f_increases1 `{PCPO} n f :
  Proper (approx ==> approx) f ->
  approx (iterate_f n f pcpo_bottom) (iterate_f (S n) f pcpo_bottom).
  intro mono; induction n.
  apply pcpo_least_element.
  unfold iterate_f; fold (@iterate_f A).
  apply mono. assumption.
Qed.

(* Similar to above, but for arbitrary n1 <= n2 *)
Lemma iterate_f_increases `{PCPO} n1 n2 f :
  n1 <= n2 -> Proper (approx ==> approx) f ->
  approx (iterate_f n1 f pcpo_bottom) (iterate_f n2 f pcpo_bottom).
  intro l; induction l; intros.
  reflexivity.
  transitivity (iterate_f m f pcpo_bottom).
  apply IHl; assumption.
  apply iterate_f_increases1; assumption.
Qed.

(* Building the least fixed-point of a Scott-continuous function f *)
Definition leastFP `{DomainOrder} {_:CPOSupremum A} {_:PCPOBottom A} f : A :=
  cpo_sup (fun n => iterate_f n f pcpo_bottom).

(* Proof that leastFP gives a fixed-point *)
Lemma leastFP_correct `{PCPO} f :
  scott_continuous f -> least_fixed_point f (leastFP f).
  intro sc; destruct sc.

  (* Helper lemma 1 *)
  assert (directed (fun n : nat => iterate_f n f pcpo_bottom)).
  intros n1 n2; exists (max n1 n2).
  split; apply iterate_f_increases;
    first [ assumption | apply Nat.le_max_l | apply Nat.le_max_r ].

  (* Helper lemma 2 *)
  assert (directed (fun n : nat => f (iterate_f n f pcpo_bottom))).
  intros n1 n2; exists (max n1 n2).
  unfold iterate_f; fold (@iterate_f A (S n1) f pcpo_bottom);
  fold (@iterate_f A (S n2) f pcpo_bottom);
  fold (@iterate_f A (S (max n1 n2)) f pcpo_bottom).
  split; apply iterate_f_increases; try (apply le_n_S);
    first [ assumption | apply Nat.le_max_l | apply Nat.le_max_r ].

  split; unfold leastFP, fixed_point.

  (* Proof that leastFP is a fixed-point *)
  transitivity (cpo_sup (fun n => f (iterate_f n f pcpo_bottom))).
  apply H1; assumption.
  apply supremums_equivalent; try assumption; intro.
  exists (S n1); reflexivity.
  exists n2. apply iterate_f_increases1; assumption.

  (* Proof that leastFP is a least fixed-point *)
  intros fp is_fp.
  apply cpo_sup_least; try assumption.
  intro n; induction n.
  apply pcpo_least_element.
  transitivity (f fp).
  apply H0; assumption.
  destruct is_fp; assumption.
Qed.
