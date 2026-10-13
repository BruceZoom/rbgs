Require Import Coq.Lists.List.
Require Import Coq.PArith.PArith.

Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import TPSimulationSet.

Require Import examples.Common.AtomicLTS.


(** The atomic FIFO queue, the top specification of the Herlihy--Wing queue
    development (docs/proof-details/HWQueueProofDetails.tex, Section 6.1).

    The state is the list of queued values, oldest first.  [enq v] appends
    at the tail and returns [tt]; [deq] removes the head and returns it.
    [deq] has no response transition on the empty queue: a pending dequeue
    of an empty queue never responds, matching the implementation, which
    loops instead of reporting emptiness (Section 8.1 of the write-up). *)
Module QueueSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.
  Import TPSimulationSet.TPSimulation.

  Variant EQueue_op {A} :=
  | enq (v : A)
  | deq.
  Arguments EQueue_op : clear implicits.

  Definition EQueue_ar {A} (m : EQueue_op A) : Type :=
    match m with
    | enq _ => unit
    | deq => A
    end.

  Canonical Structure EQueue A :=
  {|
    Sig.op := EQueue_op A;
    Sig.ar := EQueue_ar
  |}.

  Variant StepQueue {A} : @ThreadEvent (EQueue A) -> list A -> list A -> Prop :=
  | step_enq_inv t q v e :
      e = {| te_tid := t; te_ev := InvEv (enq v) |} ->
      StepQueue e q q
  | step_enq_res t q v e :
      e = {| te_tid := t; te_ev := ResEv (enq v) tt |} ->
      StepQueue e q (q ++ v :: nil)
  | step_deq_inv t q e :
      e = {| te_tid := t; te_ev := InvEv deq |} ->
      StepQueue e q q
  | step_deq_res t q v e :
      e = {| te_tid := t; te_ev := ResEv deq v |} ->
      StepQueue e (v :: q) q.

  Definition VQueue {A} : @LTS (EQueue A) := VAE StepQueue NoError.

  Module QueueLayer.
    Section Layer.
      Context {A : Type}.

      Definition L : layer_interface :=
        {|
          li_sig := EQueue A;
          li_lts := @VQueue A;
          li_init := Idle nil
        |}.
    End Layer.
  End QueueLayer.

End QueueSpec.
