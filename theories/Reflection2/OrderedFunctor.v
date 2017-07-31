Require Export PredMonad.Reflection2.OrderedType.

(* Neither of these work very well, and in fact get in the way sometimes. Also
their full generality has so far not been needed. So I am just storing them
here... *)


(***
 *** First-Order Ordered Type Functors
 ***)

(* A type portion of a first-order functor of a given arity *)
Fixpoint OTFunctor1 arity : Type :=
  match arity with
  | 0 => Type
  | S arity' => forall A {RA:OType A}, OTFunctor1 arity'
  end.

(* A relation portion of a first-order functor of a given arity *)
Fixpoint OTypeF1Fun arity : OTFunctor1 arity -> Type :=
  match arity with
  | 0 => OType
  | S arity' =>
    fun F => forall A {RA:OType A}, OTypeF1Fun arity' (F A RA)
  end.

(* Typeclass version of OTypeF1Fun *)
Class OTypeF1 arity F : Type :=
  otypeF1 : OTypeF1Fun arity F.

(* A list of arguments to a first-order functor *)
Inductive OTArgs : Type :=
| ArgsNil
| ArgsCons A {RA:OType A} (args:OTArgs)
.

(* Get the head argument of a list, or unit if we ran out *)
Definition OTArgs_head (args:OTArgs) : Type :=
  match args with
  | ArgsNil => unit
  | ArgsCons A args' => A
  end.

(* Get the head OType of a list, or unit if we ran out *)
Definition OTArgs_headOType (args:OTArgs) : OType (OTArgs_head args) :=
  match args with
  | ArgsNil => _
  | ArgsCons A args' => _
  end.

Instance OType_OTArgs_head args : OType (OTArgs_head args) :=
  OTArgs_headOType args.

(* Get the tail of a list of arguments, or the empty list if we ran out *)
Definition OTArgs_tail (args:OTArgs) : OTArgs :=
  match args with
  | ArgsNil => ArgsNil
  | ArgsCons A args' => args'
  end.

(* Apply a functor to a list of arguments. Note that we do not actually care how
long the list is, as we will just supply unit types if we run out of args. *)
Fixpoint OTFunctorApply arity : forall F:OTFunctor1 arity, OTArgs -> Type :=
  match arity return forall F:OTFunctor1 arity, OTArgs -> Type with
  | 0 => fun A _ => A
  | S arity' =>
    fun F args =>
      OTFunctorApply arity' (F (OTArgs_head args) _) (OTArgs_tail args)
  end.

(* Get out the OType from applying a functor *)
Instance OType_OTFunctorApply arity F (RF:OTypeF1 arity F) As :
  OType (OTFunctorApply arity F As).
Proof.
  revert F RF As; induction arity; intros; simpl.
  - assumption.
  - apply IHarity. apply RF.
Defined.

(* Get out the OType from applying a unary functor *)
Instance OType_OTFunctorApply1 F (RF:OTypeF1 1 F) A {RA:OType A} :
  OType (F A RA) := OType_OTFunctorApply 1 F RF (ArgsCons A ArgsNil).


(***
 *** Ordered Type Functors of Higher Kinds
 ***)

(* The language of kinds for type functors, built from * and -> *)
Inductive OKind : Type :=
| OKStar
| OKArrow (k1 k2:OKind)
.

(* The "semantics" of a kind, which is a type A plus a dependent type on A *)
Definition OKindSem := {A:Type & A -> Type}.

(* Typeclass for elements of the dependent type in an OKindSem *)
Class OKindSemRelation (sem:OKindSem) (A:projT1 sem) : Type :=
  okindSemRelation : projT2 sem A.

(* The type and relation types associated with kind k *)
Fixpoint OTFunctorTypes k : {A:Type & A -> Type} :=
  match k with
  | OKStar => existT _ Type OType
  | OKArrow k1 k2 =>
    existT
      (fun A => A -> Type)
      (forall A1 (R1:OKindSemRelation (OTFunctorTypes k1) A1),
          projT1 (OTFunctorTypes k2))
      (fun f => forall A1 R1, OKindSemRelation (OTFunctorTypes k2) (f A1 R1))
  end.
Arguments OTFunctorTypes !k.

(* Ordered type functors of kind k *)
Definition OTFunctor k : Type := projT1 (OTFunctorTypes k).

(* The relation portion of an ordered type functor of kind k *)
Class OTFunctorRel k (F: OTFunctor k) : Type :=
  otFunctorRel : projT2 (OTFunctorTypes k) F.

(* An OTFunctorRel at kind * is the same as an OType *)
Definition OType_OKindSemRelation
           A (RA: OKindSemRelation (OTFunctorTypes OKStar) A) :
  OType A := RA.

(* Only apply OType_OKindSemRelation when we have an OKindSemRelation in
the context *)
Hint Immediate OType_OKindSemRelation : typeclass_instances.

(* The unit type forms a trivial OTFunctor *)
Instance OTFunctorRel_unit : OTFunctorRel OKStar unit := OTunit.

(* Products form an OTFunctor *)
Instance OTFunctorRel_prod : OTFunctorRel
                               (OKArrow OKStar (OKArrow OKStar OKStar))
                               (fun A _ B _ => prod A B) :=
  fun A RA B RB => OTpair A B RA RB.


(* Sums form an OTFunctor *)
Instance OTFunctorRel_sum : OTFunctorRel
                               (OKArrow OKStar (OKArrow OKStar OKStar))
                               (fun A _ B _ => sum A B) :=
  fun A RA B RB => OTsum A B RA RB.

(* Pfuns form an OTFunctor *)
Instance OTFunctorRel_pfun : OTFunctorRel
                               (OKArrow OKStar (OKArrow OKStar OKStar))
                               (fun A _ B _ => A -o> B) :=
  fun A RA B RB => OTarrow A B.
