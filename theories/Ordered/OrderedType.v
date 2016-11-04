Require Export Coq.Program.Tactics.
Require Export Coq.Setoids.Setoid.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Arith.Arith_base.
Require Export Coq.Relations.Relations.
Require Export Coq.Lists.List.

Import EqNotations.
Import ListNotations.


(***
 *** Ordered Types = Types with a PreOrder
 ***)

Record OType : Type :=
  {
    ot_Type : Type;
    ot_R :> relation ot_Type;
    ot_PreOrder :> PreOrder ot_R
  }.

Instance OType_Reflexive (A:OType) : Reflexive (ot_R A).
Proof.
  destruct A; auto with typeclass_instances.
Qed.

Instance OType_Transitive (A:OType) : Transitive (ot_R A).
Proof.
  destruct A; auto with typeclass_instances.
Qed.


(***
 *** Commonly-Used Ordered Types
 ***)

(* The ordered type of propositions *)
Program Definition OTProp : OType :=
  {|
    ot_Type := Prop;
    ot_R := Basics.impl;
  |}.
Next Obligation.
  constructor; auto with typeclass_instances.
Qed.

(* The discrete ordered type, where things are only related to themselves *)
Program Definition OTdiscrete (A:Type) : OType :=
  {|
    ot_Type := A;
    ot_R := eq;
  |}.

(* The only ordered type over unit is the discrete one *)
Definition OTunit : OType := OTdiscrete unit.

(* The ordered type of natural numbers using <= *)
Program Definition OTnat : OType :=
  {|
    ot_Type := nat;
    ot_R := le;
  |}.

(* Flip the ordering of an OType *)
Program Definition OTflip (A:OType) : OType :=
  {|
    ot_Type := ot_Type A;
    ot_R := fun x y => ot_R A y x
  |}.
Next Obligation.
  constructor.
  { intro x. reflexivity. }
  { intros x y z; transitivity y; assumption. }
Qed.

(* The non-dependent product ordered type, where pairs are related pointwise *)
Program Definition OTpair (A:OType) (B: OType) : OType :=
  {|
    ot_Type := ot_Type A * ot_Type B;
    ot_R := fun p1 p2 =>
              ot_R A (fst p1) (fst p2) /\ ot_R B (snd p1) (snd p2)
  |}.
Next Obligation.
  constructor.
  { intro p; split; reflexivity. }
  { intros p1 p2 p3 R12 R23; destruct R12; destruct R23; split.
    - transitivity (fst p2); assumption.
    - transitivity (snd p2); assumption. }
Qed.

(* The non-dependent sum ordered type, where objects are only related if they
are both "left"s or both "right"s *)
Program Definition OTsum (A:OType) (B: OType) : OType :=
  {|
    ot_Type := ot_Type A + ot_Type B;
    ot_R := fun sum1 sum2 =>
              match sum1, sum2 with
                | inl x, inl y => ot_R A x y
                | inl x, inr y => False
                | inr x, inl y => False
                | inr x, inr y => ot_R B x y
              end
  |}.
Next Obligation.
  constructor.
  { intro s; destruct s; reflexivity. }
  { intros s1 s2 s3 R12 R23.
    destruct s1; destruct s2; destruct s3; try (elimtype False; assumption).
    - transitivity o0; assumption.
    - transitivity o0; assumption. }
Qed.


(* NOTE: the following definition requires everything above to be polymorphic *)
(* NOTE: The definition we choose for OTType is actually deep: instead of
requiring ot_Type A = ot_Type B, we could just require a coercion function from
ot_Type A to ot_Type B, which would yield something more like HoTT... though
maybe it wouldn't work unless we assumed the HoTT axiom? As it is, we might need
UIP to hold if we want to use the definition given here... *)
(*
Program Definition OTType : OType :=
  {|
    ot_Type := OType;
    ot_R := (fun A B =>
               exists (e:ot_Type A = ot_Type B),
                 forall (x y:A),
                   ot_R A x y ->
                   ot_R B (rew [fun A => A] e in x)
                        (rew [fun A => A] e in y));
  |}.
*)


(***
 *** The Ordered Type for Functions
 ***)

(* The type of continuous, i.e. Proper, functions between ordered types *)
Record Pfun (A:OType) (B: OType) :=
  {
    pfun_app : ot_Type A -> ot_Type B;
    pfun_Proper :> Proper (ot_R A ==> ot_R B) pfun_app
  }.

Arguments pfun_app [_ _] _ _.
Arguments pfun_Proper [_ _] _ _ _ _.

(* Infix "@" := pfun_app (at level 50). *)

(* The non-dependent function ordered type *)
Program Definition OTarrow (A:OType) (B: OType) : OType :=
  {|
    ot_Type := Pfun A B;
    ot_R := fun f g =>
              forall a1 a2, ot_R A a1 a2 -> ot_R B (pfun_app f a1) (pfun_app g a2);
  |}.
Next Obligation.
  constructor.
  { intros f; apply (pfun_Proper f). }
  { intros f g h Rfg Rgh a1 a2 Ra. transitivity (pfun_app g a1).
    - apply (Rfg a1 a1). reflexivity.
    - apply Rgh; assumption. }
Qed.

(* Curry a Pfun *)
Program Definition pfun_curry {A B C} (pfun : Pfun (OTpair A B) C)
  : Pfun A (OTarrow B C) :=
  {| pfun_app :=
       fun a =>
         {| pfun_app := fun b => pfun_app pfun (a,b);
            pfun_Proper := _ |};
     pfun_Proper := _ |}.
Next Obligation.
Proof.
  intros b1 b2 Rb. apply pfun_Proper.
  split; [ reflexivity | assumption ].
Qed.
Next Obligation.
Proof.
  intros a1 a2 Ra b1 b2 Rb; simpl.
  apply pfun_Proper; split; assumption.
Qed.

(* Uncrry a Pfun *)
Program Definition pfun_uncurry {A B C} (pfun : Pfun A (OTarrow B C))
  : Pfun (OTpair A B) C :=
  {| pfun_app :=
       fun ab => pfun_app (pfun_app pfun (fst ab)) (snd ab);
     pfun_Proper := _ |}.
Next Obligation.
Proof.
  intros ab1 ab2 Rab. destruct Rab as [ Ra Rb ].
  exact (pfun_Proper pfun (fst ab1) (fst ab2) Ra (snd ab1) (snd ab2) Rb).
Qed.

(* Currying and uncurrying of pfuns form an adjunction *)
(* FIXME HERE: figure out the simplest way of stating this adjunction *)


(* OTarrow is right adjoint to OTpair, meaning that (OTarrow (OTpair A B) C) is
isomorphic to (OTarrow A (OTarrow B C)). The following is the first part of this
isomorphism, mapping left-to-right. *)


(* FIXME: could also do a forall type, but need the second type argument, B, to
itself be proper, i.e., to be an element of OTArrow A OType. Would also need a
dependent version of OTContext, below. *)


(***
 *** Ordered Types as Contexts of Nested Pairs
 ***)

(* FIXME HERE: documentation! *)

Inductive ContextExtends : OType -> OType -> Type :=
| ContextExtends_refl ctx : ContextExtends ctx ctx
| ContextExtends_cons_both {ctx1 ctx2} A :
    ContextExtends ctx1 ctx2 ->
    ContextExtends (OTpair ctx1 A) (OTpair ctx2 A)
| ContextExtends_cons_right {ctx1 ctx2} A :
    ContextExtends ctx1 ctx2 -> ContextExtends ctx1 (OTpair ctx2 A)
.

(* Context extension as a type class *)
Class OTCtxExtends ctx1 ctx2 : Type :=
  context_extends : ContextExtends ctx1 ctx2.

Arguments context_extends {_ _ _}.

(* The rules for context extension, as type class instances *)
Instance OTCtxExtends_refl ctx : OTCtxExtends ctx ctx :=
  ContextExtends_refl _.

Instance OTCtxExtends_cons_both ctx1 ctx2
         {ext:OTCtxExtends ctx1 ctx2} {B}
  : OTCtxExtends (OTpair ctx1 B) (OTpair ctx2 B) :=
  ContextExtends_cons_both _ context_extends.

Instance OTCtxExtends_cons_right ctx1 ctx2
         {ext:OTCtxExtends ctx1 ctx2} {B} : OTCtxExtends ctx1 (OTpair ctx2 B) :=
  ContextExtends_cons_right _ context_extends.

(* Context extension induces a mapping from the bigger to the smaller context *)
Fixpoint unextend_context {ctx1 ctx2} (ext: ContextExtends ctx1 ctx2) :
  ot_Type ctx2 -> ot_Type ctx1 :=
  match ext in ContextExtends ctx1 ctx2 return ot_Type ctx2 -> ot_Type ctx1 with
  | ContextExtends_refl ctx => fun celem => celem
  | ContextExtends_cons_both A ext' =>
    fun celem =>
      (unextend_context ext' (fst celem), snd celem)
  | ContextExtends_cons_right A ext' =>
    fun celem =>
      unextend_context ext' (fst celem)
  end.

(* unextend_context preserves ordering *)
Instance unextend_context_Proper {ctx1 ctx2} ext :
  Proper (ot_R ctx2 ==> ot_R ctx1) (unextend_context ext).
Proof.
  induction ext; simpl; intros celem1 celem2 R12.
  { assumption. }
  { destruct R12; split; [ apply IHext | ]; assumption. }
  { destruct R12. apply IHext. assumption. }
Qed.


(***
 *** Ordered Terms in Context
 ***)

(* An ordered term in context is just a proper function *)
Inductive OTermInCtx ctx A : Type :=
  | mkOTermInCtx (pfun: Pfun ctx A).

Arguments mkOTermInCtx {ctx A} pfun.

(* Helper to eliminate an OTermInCtx *)
Definition elimOTermInCtx {ctx A} (oterm: OTermInCtx ctx A) : Pfun ctx A :=
  let (pfun) := oterm in pfun.

(* Weakening the context of an OTermInCtx *)
Program Definition weaken_context {ctx1 ctx2} {ext: OTCtxExtends ctx1 ctx2}
           {A} (p: OTermInCtx ctx1 A) : OTermInCtx ctx2 A :=
  match p with
  | mkOTermInCtx pfun =>
    mkOTermInCtx
      {| pfun_app := fun celem => pfun_app pfun (unextend_context ext celem);
         pfun_Proper := _ |}
  end.
Next Obligation.
  intros celem1 celem2 R12. apply pfun_Proper.
  apply unextend_context_Proper. assumption.
Qed.

(* Helper to build a "variable" for the top of the context as an OTermInCtx *)
Program Definition top_var_in_context ctx A : OTermInCtx (OTpair ctx A) A :=
  mkOTermInCtx {| pfun_app := fun celem => snd celem;
                  pfun_Proper := _ |}.
Next Obligation.
  intros celem1 celem2 R12. destruct R12. assumption.
Qed.


(* Build an OTerm for a function *)
Definition pfun_lambda {ctx} {A} {B} (f: OTermInCtx (OTpair ctx A) A ->
                                         OTermInCtx (OTpair ctx A) B)
  : OTermInCtx ctx (OTarrow A B) :=
  mkOTermInCtx (pfun_curry (elimOTermInCtx (f (top_var_in_context ctx A)))).

(* Build an OTerm for a function, with weaken_context already pre-applied *)
Definition pfun_lambda' {ctx} {A} {B}
        (f: (forall {ctx'} `{ext: OTCtxExtends (OTpair ctx A) ctx'},
                OTermInCtx ctx' A) -> OTermInCtx (OTpair ctx A) B) :
  OTermInCtx ctx (OTarrow A B) :=
  mkOTermInCtx
    (pfun_curry
       (elimOTermInCtx (f (fun {ctx' ext} =>
                             weaken_context (top_var_in_context ctx A))))).


Definition ex1 : OTermInCtx OTunit (OTarrow OTnat OTnat) :=
  pfun_lambda'
    (fun (x : forall {ctx' ext}, _) => x).


(***
 *** Notations
 ***)

Module ProperTermNotations.

  Notation "A '-o>' B" :=
    (OTArrow A B) (right associativity, at level 99).
  Notation "A '*o*' B" :=
    (OTProd A B) (left associativity, at level 40).
  Notation "A '+o+' B" :=
    (OTSum A B) (left associativity, at level 50).
  Notation "'~o~' A" :=
    (OTFlip A) (right associativity, at level 35).

  Delimit Scope pterm_scope with pterm.
  Bind Scope pterm_scope with OTPairInCtx.
  Bind Scope pterm_scope with ProperTerm.

  Notation "x <o= y" :=
    (OT_leq x%pterm y%pterm) (no associativity, at level 70).
  Notation "x =o= y" :=
    (OT_equiv x%pterm y%pterm) (no associativity, at level 70).

  Notation "'pfun' ( x ::: T ) ==> y" :=
    (proper_fun (A:=T) (fun x => y%pterm))
      (at level 100, right associativity, x at level 99) : pterm_scope.

  Notation "'pvar' x" := (proper_var x) (no associativity, at level 10) : pterm_scope.

  Notation "'!' x" := (weaken_context (ctx2:=_) (ext:=_) x) (no associativity, at level 10) : pterm_scope.

  Notation "x @ y" :=
    (proper_apply x y) (left associativity, at level 20) : pterm_scope.

  Notation "( x ,o, y )" :=
    (proper_pair x%pterm y%pterm)
      (no associativity, at level 0) : pterm_scope.
  Notation "'ofst' x" :=
    (proper_proj1 x%pterm) (right associativity, at level 80) : pterm_scope.
  Notation "'osnd' x" :=
    (proper_proj2 x%pterm) (right associativity, at level 80) : pterm_scope.

  Notation "'pinl' ( B ) x" :=
    (proper_inl (B:=B) x) (right associativity, at level 80) : pterm_scope.
  Notation "'pinr' ( A ) x" :=
    (proper_inl (A:=A) x) (right associativity, at level 80) : pterm_scope.
  Notation "'pmatch_sum' x 'with' | 'inl' y1 => z1 | 'inr' y2 => z2 'end'" :=
    (proper_sum_elim x (proper_fun (fun y1 => z1))
                     (proper_fun (fun y2 => z2)))
      (no associativity, at level 0, x at level 100).

  (* NOTE: this notation needs to be in a Program Instance *)
  Notation "'pmap1' ( f ::: A --> B ) x" :=
    (map_OTPairInCtx (A:=A) (B:=B) f _ x)
      (right associativity, at level 80) : pterm_scope.

End ProperTermNotations.


(***
 *** Examples
 ***)

Module ProperTermExamples.

Import ProperTermNotations.

(* Example: the identity on Prop *)
Definition proper_id_Prop_fun : ProperTerm (OTProp -o> OTProp) :=
  pfun ( x ::: OTProp ) ==> pvar x.

(* You can see that it yields the identity function *)
Eval compute in (get_proper_term proper_id_Prop_fun : Prop -> Prop).

(* The proof of Proper-ness is automatic by typeclass instances *)
Goal (Proper (OTProp -o> OTProp) (get_proper_term proper_id_Prop_fun)).
auto with typeclass_instances.
Qed.

(* Example 2: the first projection function on 2 Props *)
Definition proper_proj1_Prop_fun : ProperTerm (OTProp -o> OTProp -o> OTProp) :=
  pfun ( P1 ::: OTProp ) ==>
    pfun ( P2 ::: OTProp ) ==>
      pvar P1.

(* Example 3: apply each of a pair of functions to an argument *)
Definition proper_example3 {A B C} :
  ProperTerm ((A -o> B) *o* (A -o> C) -o> A -o> (B *o* C)) :=
  pfun ( p ::: (A -o> B) *o* (A -o> C)) ==>
    pfun ( x ::: A ) ==>
      (((ofst (pvar p)) @ pvar x) ,o, ((osnd (pvar p)) @ pvar x)).

(* Example 4: match a sum of two A's and return an A *)
Definition proper_example4 {A} :
  ProperTerm (A +o+ A -o> A) :=
  pfun ( sum ::: A +o+ A) ==>
    pmatch_sum (pvar sum) with
      | inl x => pvar x
      | inr y => pvar y
    end.

End ProperTermExamples.
