Require Import Coq.Lists.List.
Require Import PeanoNat.

Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import TPSimulationSet.

Require Import examples.Common.AtomicLTS.
Require Import examples.Common.SwapSpec.
Require Import examples.HWQ.CounterSpec.
Require Import examples.HWQ.POQueueSpec.


(** The Herlihy--Wing queue over an atomic counter and a swap array whose
    swaps are atomic and whose stores are racy against each other
    (docs/proof-details/HWQueueProofDetails.tex, Sections 1.1 and 5.1).

    The underlay is [Counter ⊗ SwapArray]; the left component is the
    counter [back] and the right component is the array [items].  Indices
    are zero-based and [ctr_inc] returns the old counter value.

      enq(x):  i <- inc(back); store(items[i], x); return ok
      deq():   while true:
                 r <- read(back);
                 for i in 0 .. r-1:
                   x <- swap(items[i], null);
                   if x != null: return x

    The layer is proved against [POQueueSpec]: [ctr_inc] is the abstract
    enqueue invocation, [sa_store] the abstract enqueue response, and a
    successful [sa_swap] the atomic dequeue.  A dequeue never reports an
    empty queue; on an empty queue it loops. *)
Module HWQueueImpl.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import TPSimulationSet.TPSimulation.
  Import AtomicLTS.
  Import CounterSpec.
  Import SwapSpec.
  Import POQueueSpec.
  Import (coercions, canonicals, notations) Sig.
  Import (canonicals) Sig.Plus.

  Open Scope prog_scope.

  Section Impl.
    Context {A : Type}.

    Definition ECounterLayer : layer_interface := CounterLayer.L.

    Definition ESwapArrayLayer : layer_interface := @SwapArrayLayer.L A.

    Definition E : layer_interface := ECounterLayer ⊗ₗ ESwapArrayLayer.

    Definition F : layer_interface := @POQueueLayer.L A.

    Definition enq_impl (x : A) (_actor : tid) : Prog (li_sig E) unit :=
      inl ctr_inc >= i =>
      inr (sa_store i (Some x)) >= _ =>
      Ret tt.

    (** The inner [for] loop is a [ForEach] over the slots [0 .. r-1] that
        existed when the counter was read.  The accumulator is the value
        found so far; once it holds a value the remaining iterations do
        nothing, so no slot is swapped after the first hit. *)
    Definition deq_impl (_actor : tid) : Prog (li_sig E) A :=
      Do {
        inl ctr_read >= r =>
        (ForEach seq O r From None Using (fun found i =>
           match found with
           | Some v => Ret (Some v)
           | None =>
               inr (sa_swap i None) >= x =>
               Ret x
           end))
        p>= found =>
        match found with
        | Some v => Break (v)
        | None => Continue (tt)
        end
      } Loop.

    Definition hw_queue_impl : ModuleImpl (li_sig E) (li_sig F) :=
      fun op =>
        match op with
        | poq_enq x => enq_impl x
        | poq_deq => deq_impl
        end.

  End Impl.

End HWQueueImpl.
