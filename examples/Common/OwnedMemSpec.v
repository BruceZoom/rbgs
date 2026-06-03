Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.
Require Import PeanoNat.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import examples.Common.Heap.
Require Import examples.Common.AtomicLTS.
Require Import examples.Common.MemSpec.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import Logics.
Require Import Assertion.
Require Import TPSimulation.
Require Import RGILogic.


Module OwnedMemSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.
  Import MemSpec.

  Module WriteOwnedMem.
    Variant LocStat :=
    | LAlloc (t : tid)
    | LWritten.

    Record OwnedMemState (A : Type) := {
      om_heap : @Heap A;
      om_loc : @Heap LocStat;
    }.
    Arguments om_heap {A} _.
    Arguments om_loc {A} _.

    Definition empty_owned_mem {A} : OwnedMemState A :=
      {| om_heap := empty_heap; om_loc := empty_heap |}.

    Variant StepMem {A} : @ThreadEvent (EMem A) -> OwnedMemState A -> OwnedMemState A -> Prop :=
    (* alloc steps *)
    | step_alloc_inv t s e:
      e = {| te_tid := t; te_ev := InvEv malloc |} ->
      StepMem e s s
    | step_alloc_res t s l e (v : A):
      e = {| te_tid := t; te_ev := ResEv malloc l |} ->
      om_heap s l = None ->
      StepMem e s
        {| om_heap := heap_update l v (om_heap s);
           om_loc := heap_update l (LAlloc t) (om_loc s) |}
    (* read steps *)
    | step_read_inv t l s e:
      e = {| te_tid := t; te_ev := InvEv (mread l) |} ->
      om_heap s l <> None ->
      StepMem e s s
    | step_read_res t l s v e:
      e = {| te_tid := t; te_ev := ResEv (mread l) v |} ->
      om_heap s l = Some v ->
      StepMem e s s
    (* write steps *)
	    | step_write_inv t l v s e:
	      e = {| te_tid := t; te_ev := InvEv (mwrite l v) |} ->
	      om_heap s l <> None ->
	      StepMem e s s
	    | step_write_res t l v s e:
	      e = {| te_tid := t; te_ev := ResEv (mwrite l v) tt |} ->
	      om_heap s l <> None ->
	      StepMem e s
	        {| om_heap := heap_update l v (om_heap s);
	           om_loc := heap_update l LWritten (om_loc s) |}.

    Variant ErrorMem {A} : @ThreadEvent (EMem A) -> (@AState (EMem A) (OwnedMemState A)) -> Prop :=
    | error_read_undefined t s l e:
      e = {| te_tid := t; te_ev := InvEv (mread l) |} ->
      om_heap s l = None ->
      ErrorMem e (Idle s)
    | error_write_undefined t s l v e:
      e = {| te_tid := t; te_ev := InvEv (mwrite l v) |} ->
      om_heap s l = None ->
      ErrorMem e (Idle s)
	    | error_write_racy t t' s l l' v v' e:
      t <> t' ->
      l = l' ->
      e = {| te_tid := t; te_ev := InvEv (mwrite l v) |} ->
      ErrorMem e (Pending s t' (mwrite l' v')).

    Definition VMem {A} : @LTS (EMem A) := VAE StepMem ErrorMem.
  End WriteOwnedMem.

  Module WriteOwnedMemLayer.
    Import Lang.
    Import AssertionsSingle.
    Import RGILogic.
    Import TPSimulation.
    Import MemSpec.WriteRacyMem.
    Import WriteOwnedMem.
    Import (coercions, canonicals, notations) Sig.
    Import (notations) LinCCAL.

    Open Scope prog_scope.

    Context {A : Type}.

    Definition E : layer_interface :=
    {|
      li_sig := EMem A;
      li_lts := MemSpec.WriteRacyMem.VMem;
      li_init := Idle empty_heap;
    |}.

    Definition F : layer_interface :=
    {|
      li_sig := EMem A;
      li_lts := WriteOwnedMem.VMem;
      li_init := Idle empty_owned_mem;
    |}.

	    Definition owned_mem_id_impl (m : Sig.op (EMem A)) (_ : tid) :
	      Prog (EMem A) (Sig.ar m) :=
	      m >= ret => Ret ret.
	  End WriteOwnedMemLayer.
	End OwnedMemSpec.
