Require Import LinCCAL.
Require Import TPSimulationSet.
Require Import CompLinLayer.

Require Import examples.HWQ.HWQueueProof.
Require Import examples.HWQ.QueueLinProof.

(** Top-level result for the Herlihy--Wing queue
    (docs/proof-details/HWQueueProofDetails.tex, Section 7).

      Queue ◁ POQueue ◁ (Counter ⊗ SwapArray)

    Layer 1 ([HWQueueProof]) is the singleton forward simulation of the
    code against the partial-order queue; Layer 2 ([QueueLinProof]) is
    the speculative linearization of the partial-order queue to the FIFO
    queue.  Vertical composition gives linearizability of the code
    against the FIFO queue. *)
Module HWQueueTopLevel.
  Import TPSimulationSet.TPSimulation.
  Import CompLinLayer.

  Section ComposedHWQueue.
    Context {A : Type}.

    Definition HWQueue_underlay : layer_interface := @HWQueueProof.E A.
    Definition Queue_spec : layer_interface := @QueueLinProof.F A.

    Definition MHWQueue_linearizable :
        layer_implementation_linearizability HWQueue_underlay Queue_spec :=
      @HWQueueProof.MHWQueueLinearizable A ▶ @QueueLinProof.MQueueLinLinearizable A.

    Print Assumptions MHWQueue_linearizable.
  End ComposedHWQueue.
End HWQueueTopLevel.

Export HWQueueTopLevel.
