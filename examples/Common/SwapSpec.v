Require Import Coq.PArith.PArith.
Require Import PeanoNat.

Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import TPSimulationSet.

Require Import examples.Common.AtomicLTS.


(** The swap array of the Herlihy--Wing queue development
    (docs/proof-details/HWQueueProofDetails.tex, Section 3, "Swap array").

    The state is an infinite array [nat -> option A], initially constantly
    [None] (the paper's [null]).  Modelling the array as a total function
    avoids allocation: slot [i] exists from the start and is claimed by the
    enqueue that receives [i] from the counter.  Both operations take a
    value or [None], as in the paper.

    [sa_swap] is atomic.  [sa_store] is a plain store and is racy against
    other stores to the same slot, exactly as [mwrite] in
    [MemSpec.WriteRacyMem]: a store to slot [i] invoked while another
    thread's store to slot [i] is pending is an error.  A store overlapping
    a swap of the same slot is not an error; the queue relies on that. *)
Module SwapSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.
  Import TPSimulationSet.TPSimulation.

  Section Spec.
    Context {A : Type}.

    Definition Cells : Type := nat -> option A.

    Definition empty_cells : Cells := fun _ => None.

    Definition cell_update (i : nat) (w : option A) (c : Cells) : Cells :=
      fun j => if Nat.eqb i j then w else c j.

    Lemma cell_update_same i w c :
      cell_update i w c i = w.
    Proof. unfold cell_update. now rewrite Nat.eqb_refl. Qed.

    Lemma cell_update_other i j w c :
      i <> j -> cell_update i w c j = c j.
    Proof.
      intros Hne. unfold cell_update.
      destruct (Nat.eqb i j) eqn:Heq; [|reflexivity].
      apply Nat.eqb_eq in Heq. congruence.
    Qed.

    Variant ESwapArray_op :=
    | sa_swap (i : nat) (w : option A)
    | sa_store (i : nat) (w : option A).
    Arguments ESwapArray_op : clear implicits.

    Definition ESwapArray_ar (op : ESwapArray_op) : Type :=
      match op with
      | sa_swap _ _ => option A
      | sa_store _ _ => unit
      end.

    Canonical Structure ESwapArray :=
    {|
      Sig.op := ESwapArray_op;
      Sig.ar := ESwapArray_ar
    |}.

    Variant StepSwapArray : @ThreadEvent ESwapArray -> Cells -> Cells -> Prop :=
    | step_sa_swap_inv t i w c e :
        e = {| te_tid := t; te_ev := InvEv (sa_swap i w) |} ->
        StepSwapArray e c c
    | step_sa_swap_res t i w c e :
        e = {| te_tid := t; te_ev := ResEv (sa_swap i w) (c i) |} ->
        StepSwapArray e c (cell_update i w c)
    | step_sa_store_inv t i w c e :
        e = {| te_tid := t; te_ev := InvEv (sa_store i w) |} ->
        StepSwapArray e c c
    | step_sa_store_res t i w c e :
        e = {| te_tid := t; te_ev := ResEv (sa_store i w) tt |} ->
        StepSwapArray e c (cell_update i w c).

    (** Same-slot store/store race.  The second store sees the control
        [Pending c t' (sa_store i w')] of the first; only [sa_store] is
        pending there, so a store overlapping a swap is not an error. *)
    Variant ErrorSwapArray : @ThreadEvent ESwapArray -> @AState ESwapArray Cells -> Prop :=
    | error_store_racy t t' c i i' w w' e :
        t <> t' ->
        i = i' ->
        e = {| te_tid := t; te_ev := InvEv (sa_store i w) |} ->
        ErrorSwapArray e (Pending c t' (sa_store i' w')).

    Definition VSwapArray : @LTS ESwapArray := VAE StepSwapArray ErrorSwapArray.

  End Spec.

  Module SwapArrayLayer.
    Section Layer.
      Context {A : Type}.

      Definition L : layer_interface :=
        {|
          li_sig := @ESwapArray A;
          li_lts := @VSwapArray A;
          li_init := Idle empty_cells
        |}.
    End Layer.
  End SwapArrayLayer.

End SwapSpec.
