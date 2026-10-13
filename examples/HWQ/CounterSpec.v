Require Import Coq.PArith.PArith.
Require Import PeanoNat.

Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import TPSimulationSet.

Require Import examples.Common.AtomicLTS.


(** The atomic counter of the Herlihy--Wing queue development
    (docs/proof-details/HWQueueProofDetails.tex, Section 3, "Counter").

    The state is a natural number, initially [0].  [ctr_inc] returns the
    old value and advances the counter; [ctr_read] returns the value.  The
    object is total and error-free. *)
Module CounterSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.
  Import TPSimulationSet.TPSimulation.

  Variant ECounter_op :=
  | ctr_inc
  | ctr_read.

  Canonical Structure ECounter :=
  {|
    Sig.op := ECounter_op;
    Sig.ar _ := nat
  |}.

  Variant StepCounter : @ThreadEvent ECounter -> nat -> nat -> Prop :=
  | step_ctr_inc_inv t n e :
      e = {| te_tid := t; te_ev := InvEv ctr_inc |} ->
      StepCounter e n n
  | step_ctr_inc_res t n e :
      e = {| te_tid := t; te_ev := ResEv ctr_inc n |} ->
      StepCounter e n (S n)
  | step_ctr_read_inv t n e :
      e = {| te_tid := t; te_ev := InvEv ctr_read |} ->
      StepCounter e n n
  | step_ctr_read_res t n e :
      e = {| te_tid := t; te_ev := ResEv ctr_read n |} ->
      StepCounter e n n.

  Definition VCounter : @LTS ECounter := VAE StepCounter NoError.

  Module CounterLayer.
    Definition L : layer_interface :=
      {|
        li_sig := ECounter;
        li_lts := VCounter;
        li_init := Idle O
      |}.
  End CounterLayer.

End CounterSpec.
