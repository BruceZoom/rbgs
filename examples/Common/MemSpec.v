Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.
Require Import PeanoNat.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import examples.Common.Heap.
Require Import examples.Common.AtomicLTS.
Require Import LinCCAL.
Require Import LTS.
Require Import TPSimulation.


Module MemSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.
  Import TPSimulation.

  Variant EMem_op {A} :=
  | malloc
  | mwrite (addr : Addr) (v : A)
  | mread (addr : Addr).
  Arguments EMem_op : clear implicits.

  Definition EMem_ar {A} (m : EMem_op A) : Type :=
    match m with
    | malloc => Addr
    | mwrite _ _ => unit
    | mread _ => A
    end.
  
  Canonical Structure EMem A :=
  {|
    Sig.op := EMem_op A;
    Sig.ar := EMem_ar
  |}.

  Module WriteRacyMem.
    (* With separation logic, it is likely that the following definition is enough. *)
    (* Otherwise, check out https://github.com/ehatti/LHL/blob/main/Examples/Memory/MemSpec.v to add auxilliary location ownership mapping. *)
    Definition MemState {A} := @Heap A.
    
    Variant StepMem {A} : @ThreadEvent (EMem A) -> MemState -> MemState -> Prop :=
    (* alloc steps *)
    | step_alloc_inv t h e:
      e = {| te_tid := t; te_ev := InvEv malloc |} ->
      StepMem e h h
    | step_alloc_res t h l e (v : A):
      e = {| te_tid := t; te_ev := ResEv malloc l |} ->
      h l = None ->
      StepMem e h (heap_update l v h)
    (* read steps *)
    | step_read_inv t l h e:
      e = {| te_tid := t; te_ev := InvEv (mread l) |} ->
      h l <> None ->
      StepMem e h h
    | step_read_res t l h v e:
      e = {| te_tid := t; te_ev := ResEv (mread l) v |} ->
      h l = Some v ->
      StepMem e h h
    (* write steps *)
    | step_write_inv t l v h e:
      e = {| te_tid := t; te_ev := InvEv (mwrite l v) |} ->
      h l <> None ->
      StepMem e h h
    | step_write_res t l v h e:
      e = {| te_tid := t; te_ev := ResEv (mwrite l v) tt |} ->
      h l <> None ->
      StepMem e h (heap_update l v h).

    Variant ErrorMem {A} : @ThreadEvent (EMem A) -> (@AState (EMem A) (@MemState A)) -> Prop :=
    | error_read_undefined t h l e:
      e = {| te_tid := t; te_ev := InvEv (mread l) |} ->
      h l = None ->
      ErrorMem e (Idle h)
    | error_write_undefined t h l v e:
      e = {| te_tid := t; te_ev := InvEv (mwrite l v) |} ->
      h l = None ->
      ErrorMem e (Idle h)
    | error_write_racy t t' h l l' v v' e:
      t <> t' ->
      l = l' ->
      e = {| te_tid := t; te_ev := InvEv (mwrite l v) |} ->
      ErrorMem e (Pending h t' (mwrite l' v')).

    Definition VMem {A} : @LTS (EMem A) := VAE StepMem ErrorMem.
  End WriteRacyMem.

  Module WriteRacyMemLayer.
    Section Impl.
      Context {A : Type}.

      Definition L : layer_interface :=
      {|
        li_sig := EMem A;
        li_lts := WriteRacyMem.VMem;
        li_init := Idle empty_heap;
      |}.
    End Impl.
  End WriteRacyMemLayer.

End MemSpec.
