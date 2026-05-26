Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.
Require Import Lia.
Require Import PeanoNat.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import Logics.
Require Import Assertion.
Require Import TPSimulation.
Require Import RGILogic.
Require Import examples.Common.AtomicLTS.
Require Import examples.CAS.CASRegSpec.
Require Import examples.Exchanger.ExchangerSpec.


Module ExchangerImpl.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import AssertionsSingle.
  Import RGILogic.
  Import TPSimulation.
  Import AtomicLTS CASRegSpec ExchSpec.
  Import (coercions, canonicals, notations) Sig.
  Import (notations) LinCCAL.
  Import (canonicals) Sig.Plus.

  Open Scope prog_scope.

  Context {A : Type}.

  Variant Offer :=
  | Offered (t1 : tid) (v1 : A)
  | Accepted (t1 t2 : tid) (v1 v2 : A)
  | Empty.
  Arguments Offer : clear implicits.

  Definition E : layer_interface :=
  {|
    li_sig := ECASReg Offer;
    li_lts := VCASReg;
    li_init := Idle Empty;
  |}.
  
  Definition F : layer_interface :=
  {|
    li_sig := EExch A;
    li_lts := VExch;
    li_init := ExSIdle
  |}.
  
  Definition exch_impl (v : A) (t:tid) : Prog (li_sig E) (option A) :=
    cas Empty (Offered t v) >= offered =>
    (* successfully proposed an offer *)
    if offered then
      cas (Offered t v) Empty >= revoked =>
      (* revoked *)
      if revoked then
        Ret None
      (* accepted *)
      else
        get >= w =>
        match w with
        | Accepted _ _ _ v' =>
           (* clean up *)
            cas w Empty >= _ =>
            Ret (Some v')
        (* impossible *)
        | _ => Ret None
        end
    (* already exists an offer *)
    else
      get >= w =>
      match w with
      (* attempt exchange *)
      | Offered t' v' =>
          cas w (Accepted t' t v' v) >= accepted =>
          Ret (if accepted then (Some v') else None)
      (* failed *)
      | _ => Ret None
      end
  .

  (* TODO: assertions and lemmas *)

  Program Definition Mexchanger : layer_implementation E F := {|
    li_impl m :=
      match m with
      | exch v => exch_impl v
      end
  |}.
  (* TODO: *)
End ExchangerImpl.