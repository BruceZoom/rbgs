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
Require Import examples.Common.Heap.
Require Import examples.Common.MemSpec.
Require Import examples.CAS.CASRegSpec.
Require Import examples.Stacks.StackSpec.


Module TryStackImpl.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import AssertionsSingle.
  Import RGILogic.
  Import TPSimulation.
  Import AtomicLTS TryStackSpec MemSpec MemSpec.WriteRacyMem CASRegSpec.
  Import (coercions, canonicals, notations) Sig.
  Import (notations) LinCCAL.
  Import (canonicals) Sig.Plus.

  Open Scope prog_scope.

  Context {A : Type}.

  Definition E : layer_interface :=
  {|
    li_sig := Sig.Plus.omap (ECASReg (option Addr)) (EMem (A * option Addr));
    li_lts := tens_lts VCASReg VMem;
    li_init := (Idle None, Idle empty_heap);
  |}.
  
  Definition F : layer_interface :=
  {|
    li_sig := ETryStack A;
    li_lts := VTryStack;
    li_init := Idle nil
  |}.

  Definition cas_op := Sig.op (ECASReg (option Addr)).
  Definition mem_op := Sig.op (EMem (A * option Addr)).
  Definition in_cas := @inl cas_op mem_op.
  Definition in_mem := @inr cas_op mem_op.
  
  Definition push_impl (v : A) (_ : tid) : Prog (li_sig E) (TryResult unit) :=
    in_cas get >= oldPtr =>
    in_mem malloc >= newLoc =>
    in_mem (mwrite newLoc (v, oldPtr)) >= _ =>
    in_cas (cas oldPtr (Some newLoc)) >= succ =>
    Ret (if succ then (OK tt) else FAIL).

  Definition pop_impl (_ : tid) : Prog (li_sig E) (TryResult (option A)) :=
    in_cas get >= oldPtr =>
    match oldPtr with
    | Some oldLoc =>
        in_mem (mread oldLoc) >= head =>
        in_cas (cas oldPtr (snd head)) >= succ =>
        Ret (if succ then (OK (Some (fst head))) else FAIL)
    | None => Ret (OK None)
    end.
    
  Program Definition Mtrystack : layer_implementation E F := {|
    li_impl m :=
      match m with
      | push v => push_impl v
      | pop => pop_impl
      end
  |}.
  (* TODO: *)
End TryStackImpl.