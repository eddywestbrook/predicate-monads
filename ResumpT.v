
Require Import Coq.Lists.List.
Import ListNotations.

Load Monad.


(***
 *** Descriptions of Strictly Positive Functors
 ***)

(* FIXME: by indexing descriptions by a list of types, we could also add
dependencies / propositions over one of those given types *)
(* FIXME: do we want the X argument to vary at all...? *)
Inductive PositiveFunctorDescr : Type :=
| PFD_ConstantArrow (n: nat) (pfd: PositiveFunctorDescr) : PositiveFunctorDescr
| PFD_Sum (pfd1 pfd2: PositiveFunctorDescr) : PositiveFunctorDescr
| PFD_Product (pfd1 pfd2: PositiveFunctorDescr) : PositiveFunctorDescr
| PFD_Unit : PositiveFunctorDescr
| PFD_Constant (n: nat) : PositiveFunctorDescr
| PFD_Variable : PositiveFunctorDescr
| PFD_Rec (pfd: PositiveFunctorDescr) : PositiveFunctorDescr
| PFD_RecVar (n: nat) : PositiveFunctorDescr
.

Inductive PositiveFunctorElem (Ts: list Type)
          (rec_pfds: list PositiveFunctorDescr) (X: Type) :
  PositiveFunctorDescr -> Type :=

| PFElem_ConstantArrow
    n pfd (elem: nth n Ts unit -> PositiveFunctorElem Ts rec_pfds X pfd) :
    PositiveFunctorElem Ts rec_pfds X (PFD_ConstantArrow n pfd)

| PFElem_Sum
    pfd1 pfd2
    (elem: sum (PositiveFunctorElem Ts rec_pfds X pfd1)
               (PositiveFunctorElem Ts rec_pfds X pfd2)) :
    PositiveFunctorElem Ts rec_pfds X (PFD_Sum pfd1 pfd2)

| PFElem_Product
    pfd1 pfd2
    (elem: prod (PositiveFunctorElem Ts rec_pfds X pfd1)
                (PositiveFunctorElem Ts rec_pfds X pfd2)) :
    PositiveFunctorElem Ts rec_pfds X (PFD_Product pfd1 pfd2)

| PFElem_Unit : PositiveFunctorElem Ts rec_pfds X PFD_Unit

| PFElem_Constant n (elem: nth n Ts unit) :
    PositiveFunctorElem Ts rec_pfds X (PFD_Constant n)

| PFElem_Variable (x:X) : PositiveFunctorElem Ts rec_pfds X PFD_Variable

| PFElem_Rec pfd (elem: PositiveFunctorElem Ts (pfd::rec_pfds) X pfd) :
    PositiveFunctorElem Ts rec_pfds X (PFD_Rec pfd)

| PFElem_RecVar
    n (elem: PositiveFunctorElem Ts (skipn n rec_pfds) X
                                 (nth n rec_pfds PFD_Unit)) :
    PositiveFunctorElem Ts rec_pfds X (PFD_RecVar n)
.


Arguments PFElem_ConstantArrow {Ts rec_pfds X n pfd} _.
Arguments PFElem_Sum {Ts rec_pfds X pfd1 pfd2} _.
Arguments PFElem_Product {Ts rec_pfds X pfd1 pfd2} _.
Arguments PFElem_Unit {Ts rec_pfds X}.
Arguments PFElem_Constant {Ts rec_pfds X n} _.
Arguments PFElem_Variable {Ts rec_pfds X} _.
Arguments PFElem_Rec {Ts rec_pfds X pfd} _.
Arguments PFElem_RecVar {Ts rec_pfds X n} _.


(***
 *** Decoding Descriptions to Functors
 ***)

(* A PFD context associates an optional type with each pfd in a list of pfds *)
Inductive PFDCtx : list PositiveFunctorDescr -> Type :=
| PFDCtx_Nil : PFDCtx []
| PFDCtx_Cons pfd (optT:option Type) {pfds} (ctx:PFDCtx pfds) : PFDCtx (pfd::pfds).

(* Look up the optional type at position n in ctx *)
Fixpoint PFDCtx_lookup {pfds} (ctx:PFDCtx pfds) (n:nat) : option Type :=
  match ctx with
    | PFDCtx_Nil => Some (unit:Type)
    | PFDCtx_Cons pfd optT ctx' =>
      match n with
        | 0 => optT
        | S n' => PFDCtx_lookup ctx' n'
      end
  end.

(* Remove the first n elements of ctx *)
Fixpoint PFDCtx_skipn {pfds} (ctx:PFDCtx pfds) (n:nat) {struct n} : PFDCtx (skipn n pfds) :=
  match n return PFDCtx (skipn n pfds) with
    | 0 => ctx
    | S n' =>
      match ctx in PFDCtx pfds return PFDCtx (skipn (S n') pfds) with
        | PFDCtx_Nil => PFDCtx_Nil
        | PFDCtx_Cons pfd optT ctx' =>
          PFDCtx_skipn ctx' n'
      end
  end.

(* Interpret an optional type for a RecVar *)
Definition interpPFDVarType (Ts: list Type) pfds (n: nat) (X:Type)
           (optT: option Type) : Type :=
  match optT with
    | Some T => T
    | None =>
      PositiveFunctorElem Ts (skipn n pfds) X (nth n pfds PFD_Unit)
  end.

(* Decode a PFD to a type *)
Fixpoint decodePFD (Ts: list Type) {pfds} (ctx: PFDCtx pfds)
         (pfd: PositiveFunctorDescr) (X:Type) : Type :=
  match pfd with
    | PFD_ConstantArrow n pfd' =>
      nth n Ts unit -> decodePFD Ts ctx pfd' X
    | PFD_Sum pfd1 pfd2 =>
      sum (decodePFD Ts ctx pfd1 X)
          (decodePFD Ts ctx pfd2 X)
    | PFD_Product pfd1 pfd2 =>
      prod (decodePFD Ts ctx pfd1 X)
           (decodePFD Ts ctx pfd2 X)
    | PFD_Unit => unit
    | PFD_Constant n => nth n Ts unit
    | PFD_Variable => X
    | PFD_Rec pfd =>
      decodePFD Ts (PFDCtx_Cons pfd None ctx) pfd X
    | PFD_RecVar n => interpPFDVarType Ts pfds n X (PFDCtx_lookup ctx n)
  end.

(* A context that maps each rec_pfd to a type *)
Inductive PFDecodingContext (Ts: list Type) : forall {pfds}, PFDCtx pfds -> Type :=
| PFDecCtx_Nil : PFDecodingContext Ts PFDCtx_Nil
| PFDecCtx_ConsNone pfd {pfds} ctx (dctx: @PFDecodingContext Ts pfds ctx) :
    PFDecodingContext Ts (PFDCtx_Cons pfd None ctx)
| PFDecCtx_ConsSome pfd T {pfds} ctx
                    (decf : forall X,
                              decodePFD Ts (PFDCtx_Cons pfd (Some T) ctx) pfd X ->
                              T)
                    (dctx: @PFDecodingContext Ts pfds ctx) :
    PFDecodingContext Ts (PFDCtx_Cons pfd (Some T) ctx).

(* Remove the first n elements of a PFDecodingContext *)
Fixpoint PFDecCtx_skipn Ts {pfds} {ctx:PFDCtx pfds}
         (dctx: PFDecodingContext Ts ctx) n {struct n} :
  PFDecodingContext Ts (PFDCtx_skipn ctx n) :=
  match n return PFDecodingContext Ts (PFDCtx_skipn ctx n) with
    | 0 => dctx
    | S n' =>
      match dctx in PFDecodingContext _ ctx
        return PFDecodingContext Ts (PFDCtx_skipn ctx (S n')) with
        | PFDecCtx_Nil _ => PFDecCtx_Nil Ts
        | PFDecCtx_ConsNone _ pfd ctx' dctx' =>
          PFDecCtx_skipn Ts dctx' n'
        | PFDecCtx_ConsSome _ pfd optT ctx' _ dctx' =>
          PFDecCtx_skipn Ts dctx' n'
      end
  end.

(* An variable element along with its decoding *)
Definition VarElemAndDec Ts {pfds} (ctx:PFDCtx pfds) n X :=
  prod (PositiveFunctorElem Ts (skipn n pfds) X (nth n pfds PFD_Unit))
       (decodePFD Ts (PFDCtx_skipn ctx n) (nth n pfds PFD_Unit) X).

(* Look up a decoding function in a PFDecodingContext *)
Fixpoint PFDecCtx_lookup Ts {pfds ctx}
         (dctx:@PFDecodingContext Ts pfds ctx) (n:nat) X :
  VarElemAndDec Ts ctx n X ->
  interpPFDVarType Ts pfds n X (PFDCtx_lookup ctx n) :=
  match dctx in @PFDecodingContext _ pfds ctx
        return VarElemAndDec Ts ctx n X ->
               interpPFDVarType Ts pfds n X (PFDCtx_lookup ctx n) with
    | PFDecCtx_Nil _ =>
      match n return VarElemAndDec Ts PFDCtx_Nil n X ->
                     interpPFDVarType Ts [] n X (PFDCtx_lookup PFDCtx_Nil n) with
        | 0 => fun _ => tt
        | S _ => fun _ => tt
      end
    | @PFDecCtx_ConsNone _ pfd pfds' ctx' dctx' =>
      match n return VarElemAndDec Ts (PFDCtx_Cons pfd None ctx') n X ->
                     interpPFDVarType Ts (pfd::pfds') n X
                                      (PFDCtx_lookup (PFDCtx_Cons pfd None ctx') n)
      with
        | 0 => fun elem_and_dec => fst elem_and_dec
        | S n' => PFDecCtx_lookup Ts dctx' n' X
      end
    | @PFDecCtx_ConsSome _ pfd T pfds' ctx' decf dctx' =>
      match n return VarElemAndDec Ts (PFDCtx_Cons pfd (Some T) ctx') n X ->
                     interpPFDVarType
                       Ts (pfd::pfds') n X
                       (PFDCtx_lookup (PFDCtx_Cons pfd (Some T) ctx') n)
      with
        | 0 => fun elem_and_dec => decf X (snd elem_and_dec)
        | S n' => PFDecCtx_lookup Ts dctx' n' X
      end
  end.

(* Decode a PFElem to its decodePFD type *)
Fixpoint decodePFElem (Ts: list Type) {pfds ctx}
         (dctx:@PFDecodingContext Ts pfds ctx)
         (pfd: PositiveFunctorDescr) (X:Type)
         (elem: PositiveFunctorElem Ts pfds X pfd) :
  decodePFD Ts ctx pfd X :=
  match elem in PositiveFunctorElem _ _ _ pfd
        return decodePFD Ts ctx pfd X with
    | PFElem_ConstantArrow elem' =>
      fun x => decodePFElem Ts dctx _ X (elem' x)
    | PFElem_Sum elem' =>
      match elem' with
        | inl elem_l => inl _ (decodePFElem Ts dctx _ X elem_l)
        | inr elem_r => inr _ (decodePFElem Ts dctx _ X elem_r)
      end
    | PFElem_Product elem' =>
      (decodePFElem Ts dctx _ X (fst elem'),
       decodePFElem Ts dctx _ X (snd elem'))
    | PFElem_Unit => tt
    | PFElem_Constant elem' => elem'
    | PFElem_Variable x => x
    | @PFElem_Rec _ _ _ pfd' elem' =>
      decodePFElem Ts (PFDecCtx_ConsNone Ts pfd' _ dctx) pfd' X elem'
    | @PFElem_RecVar _ _ _ n elem' =>
      PFDecCtx_lookup Ts dctx n X
                      (elem', decodePFElem Ts (PFDecCtx_skipn _ dctx n) _ _ elem')
  end.

Arguments decodePFElem {Ts pfds ctx} dctx {pfd X} elem.


(* FIXME HERE NOW: get the following to work; I think I need to replace optT in
PFDCtx_Cons with optF... *)

(* Helper function to decode an object of a recursive type *)
Definition decodeRec Ts {pfds ctx} (dctx:@PFDecodingContext Ts pfds ctx) pfd F
           (decf: forall X,
                    decodePFD Ts (PFDCtx_Cons pfd (Some (F X)) ctx) pfd X -> F X)
           X (elem: PositiveFunctorElem Ts pfds X (PFD_Rec pfd)) : F X.
  inversion elem.
  exact (decf X (decodePFElem (PFDecCtx_ConsSome Ts pfd (F X) ctx (fun _ => decf X) dctx) elem0)).
Defined.


(* Fold an element of an decodePFD type back into a PFElem *)
(*
Fixpoint foldPFElem (Ts: list Type)
         (rec_pfds: list PositiveFunctorDescr)
         (pfd: PositiveFunctorDescr) (X:Type) :
  decodePFD Ts rec_pfds pfd X ->
  PositiveFunctorElem Ts rec_pfds X pfd :=
  match pfd return decodePFD Ts rec_pfds pfd X ->
                   PositiveFunctorElem Ts rec_pfds X pfd with
    | PFD_ConstantArrow n pfd' =>
      fun obj =>
        PFElem_ConstantArrow
          (fun x => foldPFElem Ts rec_pfds pfd' X (obj x))
    | PFD_Sum pfd1 pfd2 =>
      fun obj =>
        match obj with
          | inl obj_l =>
            PFElem_Sum (inl _ (foldPFElem Ts rec_pfds pfd1 X obj_l))
          | inr obj_r =>
            PFElem_Sum (inr _ (foldPFElem Ts rec_pfds pfd2 X obj_r))
        end
    | PFD_Product pfd1 pfd2 =>
      fun obj =>
        PFElem_Product (foldPFElem Ts rec_pfds pfd1 X (fst obj),
                         foldPFElem Ts rec_pfds pfd2 X (snd obj))
    | PFD_Unit => fun obj => PFElem_Unit
    | PFD_Constant n => fun obj => PFElem_Constant obj
    | PFD_Variable => fun obj => PFElem_Variable obj
    | PFD_Rec pfd' =>
      fun obj =>
        PFElem_Rec (foldPFElem Ts (pfd'::rec_pfds) pfd' X obj)
    | PFD_RecVar n =>
      fun obj => PFElem_RecVar obj
  end.

Arguments foldPFElem {Ts rec_pfds pfd X} obj.
*)


(***
 *** Typeclasses for Positive Functors
 ***)

Section PositiveFunctorClasses.

Class PositiveFunctorPFD (F: Type -> Type) : Type :=
  functorDescr : PositiveFunctorDescr.

Class PositiveFunctorConstants (F: Type -> Type) : Type :=
  functorConstants : list Type.

Context (F: Type -> Type) {PositiveFunctorPFD:PositiveFunctorPFD F}
        {PositiveFunctorConstants:PositiveFunctorConstants F}.

Class PositiveFunctorIsoTo : Type :=
  functorIsoTo :
    forall {X},
      F X -> PositiveFunctorElem functorConstants nil X functorDescr.

Class PositiveFunctorIsoFrom : Type :=
  functorIsoFrom :
    forall {X},
      PositiveFunctorElem functorConstants nil X functorDescr -> F X.

Class PositiveFunctor
      {PositiveFunctorIsoTo:PositiveFunctorIsoTo}
      {PositiveFunctorIsoFrom:PositiveFunctorIsoFrom}
 : Prop :=
  {
    positive_functor_to_from :
      forall {X} x,
        functorIsoFrom (X:=X) (functorIsoTo x) = x;
    positive_functor_from_to :
      forall {X} elem,
        functorIsoTo (X:=X) (functorIsoFrom elem) = elem
  }.

End PositiveFunctorClasses.


(***
 *** Examples of Positive Functors
 ***)

Section PositiveFunctor_Examples.


(* Lists *)
Definition list_core_PFD :=
  PFD_Sum PFD_Unit (PFD_Product PFD_Variable (PFD_RecVar 0)).

Instance list_PositiveFunctorPFD : PositiveFunctorPFD list :=
  PFD_Rec list_core_PFD.

Instance list_PositiveFunctorConstants : PositiveFunctorConstants list := nil.

Fixpoint list_iso_to {X:Type} (l: list X) :
  PositiveFunctorElem [] [list_core_PFD] X list_core_PFD :=
  match l with
    | [] => PFElem_Sum (inl _ PFElem_Unit)
    | x::l' =>
      PFElem_Sum
        (inr
           _
           (PFElem_Product (PFElem_Variable x,
                            PFElem_RecVar (n:=0) (list_iso_to l'))))
  end.

(*
Fixpoint list_iso_to {X:Type} (l: list X) :
  PositiveFunctorElem [] [list_core_PFD] X list_core_PFD :=
  match l with
    | [] => foldPFElem (pfd:=list_core_PFD) (inl _ tt)
    | x::l' =>
      foldPFElem (pfd:=list_core_PFD) (inr _ (x, list_iso_to l'))
  end.
*)

Instance list_PositiveFunctorIsoTo : PositiveFunctorIsoTo list :=
  fun {X} l => PFElem_Rec (list_iso_to l).

Definition list_iso_from (X:Type)
           (elem: decodePFD [] (PFDCtx_Cons list_core_PFD
                                            (Some (list X)) PFDCtx_Nil)
                            list_core_PFD X) : list X :=
  match elem with
    | inl _ => nil
    | inr p => (fst p)::(snd p)
  end.

Instance list_PositiveFunctorIsoFrom : PositiveFunctorIsoFrom list :=
  fun {X} =>
    decodeRec [] (PFDecCtx_Nil []) list_core_PFD  list_iso_from.


End PositiveFunctor_Examples.
