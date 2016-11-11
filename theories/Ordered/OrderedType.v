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

(* The pointwise relation on pairs *)
Definition pairR {A B} (RA:relation A) (RB:relation B) : relation (A*B) :=
  fun p1 p2 => RA (fst p1) (fst p2) /\ RB (snd p1) (snd p2).

(* The non-dependent product ordered type, where pairs are related pointwise *)
Program Definition OTpair (A:OType) (B: OType) : OType :=
  {|
    ot_Type := ot_Type A * ot_Type B;
    ot_R := pairR A B;
  |}.
Next Obligation.
  constructor.
  { intro p; split; reflexivity. }
  { intros p1 p2 p3 R12 R23; destruct R12; destruct R23; split.
    - transitivity (fst p2); assumption.
    - transitivity (snd p2); assumption. }
Qed.

(* The sort-of pointwise relation on sum types *)
Definition sumR {A B} (RA:relation A) (RB:relation B) : relation (A+B) :=
  fun sum1 sum2 =>
    match sum1, sum2 with
    | inl x, inl y => RA x y
    | inl x, inr y => False
    | inr x, inl y => False
    | inr x, inr y => RB x y
    end.

(* The non-dependent sum ordered type, where objects are only related if they
are both "left"s or both "right"s *)
Program Definition OTsum (A B : OType) : OType :=
  {|
    ot_Type := ot_Type A + ot_Type B;
    ot_R := sumR A B
  |}.
Next Obligation.
  constructor.
  { intro s; destruct s; simpl; reflexivity. }
  { intros s1 s2 s3 R12 R23.
    destruct s1; destruct s2; destruct s3;
      try (elimtype False; assumption); simpl.
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
Definition OTarrow_R (A B : OType) : relation (Pfun A B) :=
  fun f g =>
    forall a1 a2, ot_R A a1 a2 -> ot_R B (pfun_app f a1) (pfun_app g a2).

Program Definition OTarrow (A:OType) (B: OType) : OType :=
  {|
    ot_Type := Pfun A B;
    ot_R := OTarrow_R A B;
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
itself be proper, i.e., to be an element of OTarrow A OType. Would also need a
dependent version of OTContext, below. *)


(***
 *** Contexts of Ordered Types
 ***)

(* An ordered type context is just a list *)
Definition OTCtx : Type := list OType.

(* The ordered type of elements of an ordered context *)
Fixpoint OTCtxElem (ctx:OTCtx) : OType :=
  match ctx with
  | [] => OTunit
  | A::ctx' => OTpair (OTCtxElem ctx') A
  end.

(* Helper to cons an element to a context *)
Definition context_cons {ctx A} (a:ot_Type A) (celem: ot_Type (OTCtxElem ctx)) :
  ot_Type (OTCtxElem (A::ctx)) :=
  (celem, a).

(* context_cons is Proper *)
Instance context_cons_Proper {ctx A} :
  Proper (ot_R A ==> ot_R (OTCtxElem ctx) ==>
               ot_R (OTCtxElem (A::ctx))) context_cons.
Proof.
  intros a1 a2 Ra celem1 celem2 Rc; split; assumption.
Qed.

(* Append two context elements *)
Fixpoint context_append {ctx1 ctx2} :
  ot_Type (OTCtxElem ctx1) -> ot_Type (OTCtxElem ctx2) ->
  ot_Type (OTCtxElem (ctx1 ++ ctx2)) :=
  match ctx1 return
        ot_Type (OTCtxElem ctx1) -> ot_Type (OTCtxElem ctx2) ->
        ot_Type (OTCtxElem (ctx1 ++ ctx2))
  with
  | [] => fun celem1 celem2 => celem2
  | A::ctx1' =>
    fun celem1 celem2 =>
      context_cons (snd celem1) (context_append (fst celem1) celem2)
  end.

(* context_append preserves ordering *)
Instance context_append_Proper {ctx1 ctx2} :
  Proper (ot_R (OTCtxElem ctx1) ==> ot_R (OTCtxElem ctx2) ==>
               ot_R (OTCtxElem (ctx1 ++ ctx2))) context_append.
Proof.
  induction ctx1; simpl; intros celem1 celem1' R1 celem2 celem2' R2.
  { assumption. }
  { destruct R1. split; [ apply IHctx1 | ]; assumption. }
Qed.

(* Take the prefix of a context element *)
Fixpoint context_prefix {ctx1 ctx2} :
  ot_Type (OTCtxElem (ctx1 ++ ctx2)) -> ot_Type (OTCtxElem ctx1) :=
  match ctx1 return
        ot_Type (OTCtxElem (ctx1 ++ ctx2)) -> ot_Type (OTCtxElem ctx1)
  with
  | [] => fun _ => tt
  | A::ctx1' =>
    fun celem =>
      context_cons (snd celem) (context_prefix (ctx1:=ctx1') (fst celem))
  end.

(* context_prefix preserves ordering *)
Instance context_prefix_Proper {ctx1 ctx2} :
  Proper (ot_R (OTCtxElem (ctx1 ++ ctx2)) ==>
               ot_R (OTCtxElem ctx1)) context_prefix.
Proof.
  induction ctx1; simpl; intros celem1 celem2 R12.
  { reflexivity. }
  { destruct R12. split; [ apply IHctx1 | ]; assumption. }
Qed.

(* Take the suffix of a context element *)
Fixpoint context_suffix {ctx1 ctx2} :
  ot_Type (OTCtxElem (ctx1 ++ ctx2)) -> ot_Type (OTCtxElem ctx2) :=
  match ctx1 return
        ot_Type (OTCtxElem (ctx1 ++ ctx2)) -> ot_Type (OTCtxElem ctx2)
  with
  | [] => fun celem => celem
  | A::ctx1' => fun celem => context_suffix (ctx1:=ctx1') (fst celem)
  end.

(* context_suffix preserves ordering *)
Instance context_suffix_Proper {ctx1 ctx2} :
  Proper (ot_R (OTCtxElem (ctx1 ++ ctx2)) ==>
               ot_R (OTCtxElem ctx2)) context_suffix.
Proof.
  induction ctx1; simpl; intros celem1 celem2 R12.
  { assumption. }
  { destruct R12. apply IHctx1. assumption. }
Qed.

(* A context extends another iff the latter is a suffix of the former *)
Inductive ContextExtends : OTCtx -> OTCtx -> Type :=
| ContextExtends_refl ctx : ContextExtends ctx ctx
| ContextExtends_cons {ctx1 ctx2} A :
    ContextExtends ctx1 ctx2 -> ContextExtends ctx1 (A::ctx2)
.

(* Context extension as a type class *)
Class OTCtxExtends ctx1 ctx2 : Type :=
  context_extends : ContextExtends ctx1 ctx2.

Arguments context_extends {_ _ _}.

(* The rules for context extension, as type class instances *)
Instance OTCtxExtends_refl ctx : OTCtxExtends ctx ctx :=
  ContextExtends_refl _.
Instance OTCtxExtends_cons ctx1 ctx2
         {ext:OTCtxExtends ctx1 ctx2} {A} : OTCtxExtends ctx1 (A::ctx2) :=
  ContextExtends_cons _ context_extends.
Instance OTCtxExtends_empty ctx : OTCtxExtends [] ctx.
Proof.
  induction ctx.
  apply ContextExtends_refl.
  apply ContextExtends_cons; assumption.
Qed.

(* Map elements of an extended context to the unextended context *)
Fixpoint unextend_context {ctx1 ctx2} (ext: ContextExtends ctx1 ctx2) :
  ot_Type (OTCtxElem ctx2) -> ot_Type (OTCtxElem ctx1) :=
  match ext in ContextExtends ctx1 ctx2
        return ot_Type (OTCtxElem ctx2) -> ot_Type (OTCtxElem ctx1) with
  | ContextExtends_refl ctx => fun celem => celem
  | ContextExtends_cons A ext' =>
    fun celem => unextend_context ext' (fst celem)
  end.

(* unextend_context preserves ordering *)
Instance unextend_context_Proper {ctx1 ctx2} ext :
  Proper (OTCtxElem ctx2 ==> OTCtxElem ctx1) (unextend_context ext).
Proof.
  induction ext; intros celem1 celem2 R12.
  { assumption. }
  { apply IHext. destruct R12. assumption. }
Qed.


(***
 *** Ordered Terms in Context
 ***)

(* An ordered term in context is just a proper function *)
Inductive OTerm ctx A : Type :=
  | mkOTerm (pfun: Pfun (OTCtxElem ctx) A).

Arguments mkOTerm {ctx A} pfun.

(* Helper to eliminate an OTerm *)
Definition elimOTerm {ctx A} (oterm: OTerm ctx A) :=
  let (pfun) := oterm in pfun.

(* An OTerm in the empty context *)
Definition TopOTerm A := OTerm [] A.

(* TopOTerm is "the" way to view an OrderedType as a Type *)
Coercion TopOTerm : OType >-> Sortclass.

(* Build a TopOTerm from an element of its type *)
Program Definition mkTopOTerm {A} (a:ot_Type A) : TopOTerm A :=
  mkOTerm {| pfun_app := fun _ => a; pfun_Proper := _ |}.

(* Eliminate a TopOTerm *)
Definition elimTopOTerm {A} (trm: TopOTerm A) : ot_Type A :=
  pfun_app (elimOTerm trm) tt.

(* Lifting pre-orders to ordered terms *)
Definition ot_leq {ctx A} (x y : OTerm ctx A) : Prop :=
  forall celem,
    ot_R _ (pfun_app (elimOTerm x) celem)
         (pfun_app (elimOTerm y) celem).

Instance ot_leq_PreOrder {ctx A} : PreOrder (@ot_leq ctx A).
Proof.
  constructor; intro; intros; intro; intros.
  reflexivity.
  transitivity ((pfun_app (elimOTerm y) celem)); [ apply H | apply H0 ].
Qed.

(* The equivalence relation for an OrderedType *)
Definition ot_equiv {ctx A} (x y : OTerm ctx A) : Prop :=
  ot_leq x y /\ ot_leq y x.

Instance ot_equiv_Equivalence {ctx A} : Equivalence (@ot_equiv ctx A).
Proof.
  constructor; intro; intros.
  { split; reflexivity. }
  { destruct H; split; assumption. }
  { destruct H; destruct H0; split; transitivity y; assumption. }
Qed.


(***
 *** Building Functional Ordered Terms
 ***)

(* Weaken the context of an OTerm *)
Program Definition ot_weaken {ctx1 ctx2} {ext: OTCtxExtends ctx1 ctx2}
           {A} (otrm: OTerm ctx1 A) : OTerm ctx2 A :=
  let (pfun) := otrm in
  mkOTerm
    {| pfun_app :=
         fun celem => pfun_app pfun (unextend_context context_extends celem);
       pfun_Proper := _ |}.
Next Obligation.
  intros celem1 celem2 R12. apply pfun_Proper.
  apply unextend_context_Proper. assumption.
Qed.

(* Build a "variable" for the top of the context as an OTerm *)
Program Definition ot_top_var ctx A : OTerm (A::ctx) A :=
  mkOTerm {| pfun_app := fun celem => snd celem;
                  pfun_Proper := _ |}.
Next Obligation.
  intros celem1 celem2 R12. destruct R12. assumption.
Qed.


(* Build an OTerm for a function *)
Definition ot_lambda {ctx} {A} {B} (f: OTerm (A::ctx) A ->
                                       OTerm (A::ctx) B)
  : OTerm ctx (OTarrow A B) :=
  mkOTerm (pfun_curry (elimOTerm (f (ot_top_var ctx A)))).

(* Build an OTerm for a function, with ot_weaken already pre-applied *)
Definition ot_lambda' {ctx} {A} {B}
           (f: (forall {ctx'} {ext:OTCtxExtends (A::ctx) ctx'}, OTerm ctx' A) ->
               OTerm (A::ctx) B) :
  OTerm ctx (OTarrow A B) :=
  mkOTerm
    (pfun_curry
       (elimOTerm (f (fun {ctx' ext} => ot_weaken (ot_top_var ctx A))))).


(***
 *** Substitutions into Ordered Terms
 ***)

(* Substitute for a variable in an ordered term *)
Program Definition ot_subst {ctx1 A ctx2 B}
        (otrm : OTerm (ctx1 ++ A::ctx2) B)
        (s : OTerm ctx2 A) : OTerm (ctx1 ++ ctx2) B :=
  mkOTerm
    {| pfun_app :=
         fun celem =>
           pfun_app (elimOTerm otrm)
                    (context_append
                       (ctx2:=A::ctx2)
                       (context_prefix celem)
                       (context_suffix celem,
                        pfun_app (elimOTerm s) (context_suffix celem)))
       ; pfun_Proper := _ |}.
Next Obligation.
  intros otrm1 otrm2 R12.
  apply pfun_Proper. apply context_append_Proper.
  { apply context_prefix_Proper. assumption. }
  { apply context_cons_Proper; [ apply pfun_Proper | ];
      apply context_suffix_Proper; assumption. }
Qed.

(* Apply an ordered term *)
Definition ot_apply {ctx A B} (f : OTerm ctx (OTarrow A B))
           (arg : OTerm ctx A) : OTerm ctx B :=
  ot_subst (ctx1:=[]) (mkOTerm (ctx:=A::ctx) (pfun_uncurry (elimOTerm f))) arg.

(* FIXME HERE: define rewrite rules for ot_subst *)


(***
 *** Lifting Proper Functions to Ordered Terms
 ***)

(* Class stating that the Proper elements of AU can be lifted to AO *)
Class OTLift (AU:Type) (R:relation AU) (AO:OType) : Type :=
  {
    ot_lift : forall (au:AU), Proper R au -> ot_Type AO;
    ot_lift_Proper :
      forall au1 au2 (Rau: R au1 au2) prp1 prp2,
        ot_R AO (ot_lift au1 prp1) (ot_lift au2 prp2);
  }.

Arguments OTLift AU%type R%signature AO.

(* Class stating that the lifting from AU to AO can be undone *)
Class OTLiftInv AU R AO {otl:OTLift AU R AO} :=
  {
    ot_unlift : ot_Type AO -> AU;
    ot_unlift_Proper : Proper (AO ==> R) ot_unlift;
    (* FIXME: these don't work for functions, since R could be non-transitive...
    ot_lift_iso1 : forall au prp, R (ot_unlift (ot_lift au prp)) au;
    ot_lift_iso2 : forall au prp, R au (ot_unlift (ot_lift au prp));
     *)
    ot_unlift_iso1 : forall ao prp, ot_R AO (ot_lift (ot_unlift ao) prp) ao;
    ot_unlift_iso2 : forall ao prp, ot_R AO ao (ot_lift (ot_unlift ao) prp);
  }.
(* FIXME: can we summarize the last 4 axioms above in a shorter way...? *)

Arguments OTLiftInv AU%type R%signature AO {_}.

(* Any PreOrder gets an OTLift instance *)
Program Instance PreOrder_OTLift A R (po:@PreOrder A R) :
  OTLift A R {| ot_Type := A; ot_R := R; ot_PreOrder := po |} :=
  Build_OTLift
    A R {| ot_Type := A; ot_R := R; ot_PreOrder := po |}
    (fun a _ => a) _.

(* Any PreOrder gets an OTLiftInv instance *)
Program Instance PreOrder_OTLiftInv A R (po:@PreOrder A R) :
  OTLiftInv A R {| ot_Type := A; ot_R := R; ot_PreOrder := po |} :=
  {|
    ot_unlift := fun a => a;
  |}.
Next Obligation.
  intros a1 a2 Ra; assumption.
Qed.

(* Pairs can be lifted if their components can be lifted *)
Program Instance pair_OTLift A RA AO B RB BO
        `{OTLift A RA AO} `{OTLift B RB BO}
  : OTLift (A*B) (pairR RA RB) (OTpair AO BO) :=
  {|
    ot_lift := fun p prp =>
                 (ot_lift (fst p) (proj1 prp), ot_lift (snd p) (proj2 prp));
  |}.
Next Obligation.
  destruct Rau; split; apply ot_lift_Proper; assumption.
Qed.

(* Pairs can be unlifted if their components can be unlifted *)
Program Instance pair_OTLiftInv A RA AO B RB BO
        `{OTLiftInv A RA AO} `{OTLiftInv B RB BO}
  : OTLiftInv (A*B) (pairR RA RB) (OTpair AO BO) :=
  {|
    ot_unlift := fun p => (ot_unlift (fst p), ot_unlift (snd p));
  |}.
Next Obligation.
  intros p1 p2 Rp; destruct Rp; split; apply ot_unlift_Proper; assumption.
Qed.
Next Obligation.
  destruct prp; split; apply ot_unlift_iso1.
Qed.
Next Obligation.
  destruct prp; split; apply ot_unlift_iso2.
Qed.

(* Functions can be lifted if their inputs can be unlifted *)
Program Instance fun_OTLift A RA AO B RB BO
        `{OTLiftInv A RA AO} `{OTLift B RB BO}
  : OTLift (A -> B) (RA ==> RB) (OTarrow AO BO) :=
  {|
    ot_lift :=
      fun f prp => {| pfun_app :=
                        fun a => ot_lift (f (ot_unlift a)) _;
                      pfun_Proper := _ |};
  |}.
Next Obligation.
  apply prp. apply ot_unlift_Proper. reflexivity.
Qed.
Next Obligation.
  intros a1 a2 Ra. apply ot_lift_Proper. apply prp.
  apply ot_unlift_Proper. assumption.
Qed.
Next Obligation.
  intros a1 a2 Ra. apply ot_lift_Proper. apply Rau.
  apply ot_unlift_Proper. assumption.
Qed.

(* Anything is Proper w.r.t. a pre-order *)
Instance Proper_PreOrder `{PreOrder} x : Proper R x :=
  PreOrder_Reflexive x.

(* Functions can be unlifted if their input types are PreOrders *)
Program Instance fun_OTLiftInv A RA (po:@PreOrder A RA) B RB BO
        `{OTLiftInv B RB BO}
  : OTLiftInv (A -> B) (RA ==> RB)
              (OTarrow (Build_OType A RA po) BO) :=
  {|
    ot_unlift := fun pf a => ot_unlift (pfun_app pf (ot_lift a _));
  |}.
Next Obligation.
  unfold Proper. reflexivity.
Qed.
Next Obligation.
  intros pf1 pf2 Rpf a1 a2 Ra. apply ot_unlift_Proper. apply Rpf. assumption.
Qed.
Next Obligation.
  intros a1 a2 Ra. transitivity (pfun_app ao a1).
  apply ot_unlift_iso1. apply pfun_Proper; assumption.
Qed.
Next Obligation.
  intros a1 a2 Ra. simpl. transitivity (pfun_app ao a2).
  apply pfun_Proper; assumption. apply ot_unlift_iso2.
Qed.

(* FIXME: are these what we want...? *)
Program Instance OTLift_any_OType A : OTLift (ot_Type A) A A :=
  {| ot_lift := fun a _ => a; |}.
Program Instance OTLiftInv_any_OType A : OTLiftInv (ot_Type A) A A :=
  {| ot_unlift := fun a => a; |}.
Next Obligation.
  intros a1 a2 Ra; assumption.
Qed.


(* Lift an operator to an ordered type *)
Definition ot_op `{OTLift} (op:AU) {prp:Proper R op} {ctx} : OTerm ctx AO :=
  mkOTerm {| pfun_app := fun _ => ot_lift op prp;
             pfun_Proper := fun _ _ _ => ot_lift_Proper op op prp _ _ |}.


(***
 *** Some Examples of Proper Operations as Ordered Terms
 ***)

(* Proper instance for fst *)
Instance fst_Proper A B : Proper (OTpair A B ==> A) fst.
Proof.
  intros p1 p2 Rp; destruct Rp. assumption.
Qed.

(* fst as an ordered term *)
Definition ot_fst {A B ctx} : OTerm ctx (OTarrow (OTpair A B) A) :=
  ot_op fst.

(* Proper instance for snd *)
Instance snd_Proper A B : Proper (OTpair A B ==> B) snd.
Proof.
  intros p1 p2 Rp; destruct Rp. assumption.
Qed.

(* snd as an ordered term *)
Definition ot_snd {A B ctx} : OTerm ctx (OTarrow (OTpair A B) B) :=
  ot_op snd.

(* Proper instance for pair *)
Instance pair_Proper (A B:OType) : Proper (A ==> B ==> OTpair A B) pair.
Proof.
  intros a1 a2 Ra b1 b2 Rb; split; assumption.
Qed.

(* pair as an ordered term *)
Definition ot_pair {A B ctx} : OTerm ctx (OTarrow A (OTarrow B (OTpair A B))) :=
  ot_op pair.


(***
 *** Notations
 ***)

Module OTermNotations.

  Notation "A '-o>' B" :=
    (OTarrow A B) (right associativity, at level 99).
  Notation "A '*o*' B" :=
    (OTpair A B) (left associativity, at level 40).
  Notation "A '+o+' B" :=
    (OTsum A B) (left associativity, at level 50).
  Notation "'~o~' A" :=
    (OTflip A) (right associativity, at level 35).

  Delimit Scope pterm_scope with pterm.
  Bind Scope pterm_scope with OTerm.
  Bind Scope pterm_scope with TopOTerm.

  Notation "x <o= y" :=
    (ot_R x%pterm y%pterm) (no associativity, at level 70).
  Notation "x =o= y" :=
    (ot_equiv x%pterm y%pterm) (no associativity, at level 70).

  Notation "'pfun' ( x ::: T ) ==> y" :=
    (ot_lambda (A:=T) (fun x => y%pterm))
      (at level 100, right associativity, x at level 99) : pterm_scope.

  Notation "'pfun' x ==> y" :=
    (ot_lambda (fun x => y%pterm))
      (at level 100, right associativity, x at level 99) : pterm_scope.

  Notation "'!' x" :=
    (ot_weaken x%pterm)
      (no associativity, at level 10) : pterm_scope.

  (*
  Notation "'pfun' ( x ::: T ) ==> y" :=
    (ot_lambda (A:=T) (fun (x : forall {ctx' ext}, _) => y%pterm))
      (at level 100, right associativity, x at level 99) : pterm_scope.

  Notation "'pfun' x ==> y" :=
    (ot_lambda (fun (x : forall {ctx' ext}, _) => y%pterm))
      (at level 100, right associativity, x at level 99) : pterm_scope.

  Notation "'pvar' x" :=
    (x _ _) (no associativity, at level 10, only parsing) : pterm_scope.
   *)

  Notation "x @o@ y" :=
    (ot_apply x y) (left associativity, at level 20) : pterm_scope.

  Notation "( x ,o, y )" :=
    (ot_apply (ot_apply ot_pair x%pterm) y%pterm)
      (no associativity, at level 0) : pterm_scope.

  (*
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
   *)

End OTermNotations.


(***
 *** Examples
 ***)

Module OTermExamples.
Import OTermNotations.

(* Example: the identity on Prop *)
Definition proper_id_Prop_fun : OTerm [] (OTProp -o> OTProp) :=
  pfun ( x ::: OTProp ) ==> ! x.

(* You can see that it yields the identity function *)
Eval compute in (pfun_app (elimTopOTerm proper_id_Prop_fun) : Prop -> Prop).

(* The proof of Proper-ness is automatic by typeclass instances *)
Goal (Proper (OTProp -o> OTProp) (elimTopOTerm proper_id_Prop_fun)).
auto with typeclass_instances.
Qed.

(* Example 2: the first projection function on 2 Props *)
Definition proper_proj1_Prop_fun : TopOTerm (OTProp -o> OTProp -o> OTProp) :=
  pfun ( P1 ::: OTProp ) ==>
    pfun ( P2 ::: OTProp ) ==>
      ! P1.

(* Example 3: apply each of a pair of functions to an argument *)
Definition proper_example3 {A B C} :
  TopOTerm ((A -o> B) *o* (A -o> C) -o> A -o> (B *o* C)) :=
  pfun ( p ::: (A -o> B) *o* (A -o> C)) ==>
    pfun ( x ::: A ) ==>
      (((ot_fst @o@ (!p)) @o@ !x) ,o, ((ot_snd @o@ (!p)) @o@ !x)).

(* Example 4: match a sum of two A's and return an A *)
(*
Definition proper_example4 {A} :
  OTerm (A +o+ A -o> A) :=
  pfun ( sum ::: A +o+ A) ==>
    pmatch_sum (pvar sum) with
      | inl x => pvar x
      | inr y => pvar y
    end.
 *)

End OTermExamples.
