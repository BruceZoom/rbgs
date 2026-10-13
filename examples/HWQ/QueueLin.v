Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import TPSimulationSet.

Require Import examples.HWQ.POQueueSpec.
Require Import examples.HWQ.QueueSpec.


(** The forwarding layer from the partial-order queue to the FIFO queue
    (docs/proof-details/HWQueueProofDetails.tex, Section 6.1).

    Each operation is forwarded to [POQueueSpec].  All the content of this
    layer is in its proof, which linearizes the DAG specification to the
    sequential queue by speculation over sets of possibilities, exactly as
    the TSStack layer over TryStack. *)
Module QueueLinImpl.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import TPSimulationSet.TPSimulation.
  Import POQueueSpec.
  Import QueueSpec.
  Import (coercions, canonicals, notations) Sig.

  Open Scope prog_scope.

  Section Impl.
    Context {A : Type}.

    Definition E : layer_interface := @POQueueLayer.L A.

    Definition F : layer_interface := @QueueLayer.L A.

    Definition enq_impl (v : A) (_actor : tid) : Prog (li_sig E) unit :=
      poq_enq v >= _ =>
      Ret tt.

    Definition deq_impl (_actor : tid) : Prog (li_sig E) A :=
      poq_deq >= v =>
      Ret v.

    Definition queue_lin_impl : ModuleImpl (li_sig E) (li_sig F) :=
      fun op =>
        match op with
        | enq v => enq_impl v
        | deq => deq_impl
        end.

  End Impl.

End QueueLinImpl.
