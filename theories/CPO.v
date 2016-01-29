
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Arith.Arith_base.


(***
 *** Helper Definitions
 ***)

(* States that a is an upper bound of chain *)
Definition upper_bound {A} (R: relation A) (chain: nat -> A) a :=
  forall n, R (chain n) a.

(* States that a is no greater than any upper bound of chain *)
Definition below_upper_bounds {A} (R: relation A) (chain: nat -> A) a :=
  forall a', upper_bound R chain a' -> R a a'.

(* The symmetric intersection of a relation *)
Definition inter_sym {A} (R: relation A) : relation A :=
  fun a1 a2 => R a1 a2 /\ R a2 a1.

(* The symmetric intersection of a preorder is an equivalence *)
Instance inter_sym_equivalence {A} R {H:@PreOrder A R} :
  Equivalence (inter_sym R).
  constructor.
  intro a; split; reflexivity.
  intros a1 a2 e; destruct e; split; assumption.
  intros a1 a2 a3 e1 e2; destruct e1; destruct e2; split;
    transitivity a2; assumption.
Qed.


(***
 *** Complete Partial Orders
 ***
 *** Technically, these are omega-complete preorders, since cpo_sup only deals
 *** with countable chains and we drop antisymmetry.
 ***)

(* The supremum function, which works on any countable set of A's *)
Class CPOSupremum {A} (R: relation A) : Type :=
  cpo_sup : (nat -> A) -> A.

(* The definition of a directed countable set *)
Definition directed `{CPOSupremum} (chain: nat -> A) : Prop :=
  forall n1 n2, exists n',
    R (chain n1) (chain n') /\ R (chain n2) (chain n').

(* (Omega)-CPO = preorder with least upper bounds of directed countable sets *)
Class CPO {A} (R: relation A) {CPOSupremum:CPOSupremum R} : Prop :=
  {
    cpo_preorder :> PreOrder R;
    cpo_sup_upper_bound :
      forall chain, directed chain -> upper_bound R chain (cpo_sup chain);
    cpo_sup_least :
      forall chain,
        directed chain -> below_upper_bounds R chain (cpo_sup chain)
  }.

(* Two supremums are equivalent iff the chains dominate each other *)
Lemma supremums_equivalent `{CPO} chain1 chain2 :
  directed chain1 -> directed chain2 ->
  (forall n1, exists n2, R (chain1 n1) (chain2 n2)) ->
  (forall n2, exists n1, R (chain2 n2) (chain1 n1)) ->
  inter_sym R (cpo_sup chain1) (cpo_sup chain2).
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
  Proper (R ==> R) f /\
  (forall chain,
     directed chain ->
     inter_sym R (f (cpo_sup chain)) (cpo_sup (fun n => f (chain n)))).


(***
 *** Pointed (omega-)CPOs
 ***)

(* The bottom of a PCPO *)
Class PCPOBottom {A} (R: relation A) : Type :=
  pcpo_bottom : A.

(* PCPO = CPO + a bottom *)
Class PCPO {A} (R: relation A) {CPOSupremum:CPOSupremum R}
      {PCPOBottom:PCPOBottom R} : Prop :=
  {
    pcpo_cpo :> CPO R (CPOSupremum:=CPOSupremum);
    pcpo_least_element : forall a, R pcpo_bottom a
  }.


(***
 *** Every Scott-continuous function has a least fixed-point
 ***)

(* Fixed-points of f, modulo the symmetric closure of R *)
Definition fixed_point {A} (R: relation A) (f: A -> A) a :=
  inter_sym R (f a) a.

(* Least fixed-points of f, modulo the symmetric closure of R *)
Definition least_fixed_point {A} (R: relation A) (f: A -> A) a :=
  fixed_point R f a /\
  forall a', fixed_point R f a' -> R a a'.

(* Iterate a function n times *)
Fixpoint iterate_f {A} n (f: A -> A) :=
  match n with
    | 0 => fun x => x
    | S n' => fun x => f (iterate_f n' f x)
  end.

(* (f^n _|_) `R` (f^(n+1) _|_) for monotone f *)
Lemma iterate_f_increases1 `{PCPO} n f :
  Proper (R ==> R) f ->
  R (iterate_f n f pcpo_bottom) (iterate_f (S n) f pcpo_bottom).
  intro mono; induction n.
  apply pcpo_least_element.
  unfold iterate_f; fold (@iterate_f A).
  apply mono. assumption.
Qed.

(* Similar to above, but for arbitrary n1 <= n2 *)
Lemma iterate_f_increases `{PCPO} n1 n2 f :
  n1 <= n2 -> Proper (R ==> R) f ->
  R (iterate_f n1 f pcpo_bottom) (iterate_f n2 f pcpo_bottom).
  intro l; induction l; intros.
  reflexivity.
  transitivity (iterate_f m f pcpo_bottom).
  apply IHl; assumption.
  apply iterate_f_increases1; assumption.
Qed.

(* Building the least fixed-point of a Scott-continuous function f *)
Definition leastFP {A R} {CPOSupremum:@CPOSupremum A R}
           {PCPOBottom:@PCPOBottom A R} f : A :=
  cpo_sup (fun n => iterate_f n f pcpo_bottom).

(* Proof that leastFP gives a fixed-point *)
Lemma leastFP_correct `{PCPO} f :
  scott_continuous f -> least_fixed_point R f (leastFP f).
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
