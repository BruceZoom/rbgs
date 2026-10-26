Require Import LinCCAL.
Require Import TPSimulationSet.
Require Import CompLinLayer.

Require Import examples.Common.ThreadDomain.
Require Import examples.Common.IndexedFamilySpec.
Require Import examples.Common.IndexedFamily.
Require Import examples.Common.IndexedFamilyProof.
Require Import examples.Common.OwnerMemSpec.
Require Import examples.Common.OwnerMemProof.
Require Import examples.TSStack.Timestamp.
Require Import examples.TSStack.TimestampProof.
Require Import examples.TSStack.NodeMemUnlinkProof.
Require Import examples.TSStack.SPListUnlinkProof.
Require Import examples.TSStack.SPListFamilySpec.
Require Import examples.TSStack.SPListUnlinkFamily.
Require Import examples.TSStack.SPListArraySpec.
Require Import examples.TSStack.SPListArrayProof.
Require Import examples.TSStack.ListPoolProof.
Require Import examples.TSStack.TSStackProof.

(** Top-level result for the verified timestamped stack whose per-owner
    lists unlink taken nodes (after Dodds, Haas and Kirsch).

    The chain is [TSStack_TopLevel]'s with the two lowest list layers
    replaced:

      TSStack ◁ TryStack ◁ TryStackAux ◁ ListPool
              ◁ (SPListArray ◁ SPListFamily ◁ per-owner SPListUnlink
                   ◁ (NodeMemUnlink ◁ five plain memories) ⊗ head CAS register)
                ⊗ (Timestamp ◁ counter CAS register)

    Everything from the SPList specification upwards is reused verbatim:
    the unlinking list is proved against the same [SPListSpec] overlay
    (through the ghost-log specification and [CompLinProj]), so the family
    adapter, the array, the list pool and the stack layers are the ones
    already verified. *)
Module TSStackTopLevelUnlink.
  Import LinCCALBase.
  Import TPSimulationSet.TPSimulation.
  Import CompLinLayer.
  Import IndexedFamilySpec.
  Import IndexedFamilyImpl.
  Import SPListFamilySpec.

  Section ComposedTSStack.
    Context {A : Type} (D : ThreadDomain.t).

    (** ** One unlinking SPList: five plain memories and the head register *)

    Definition SPList_underlay : layer_interface :=
      @NodeMemUnlinkProof.EPlain A ⊗ₗ SPListUnlinkProof.ECASLayer.

    Definition MSPList_underlay :
        layer_implementation_linearizability SPList_underlay
          (@SPListUnlinkProof.E A) :=
      @NodeMemUnlinkProof.MNodeMemUnlinkOverPlain A ⊗ LIId SPListUnlinkProof.ECASLayer.

    Definition MSPList_component (owner : tid) :
        layer_implementation_linearizability SPList_underlay
          (SetComponentLayer (@SPListIndexedObject A) owner) :=
      MSPList_underlay ▶ @SPListUnlinkFamilyImpl.splist_component_correct A owner.

    (** ** The family of SPLists, one per thread of [D] *)

    Definition SPListFamily_underlay : layer_interface :=
      TensorUnderlay (fun _ : tid => SPList_underlay) D.

    Definition MSPListFamily :
        layer_implementation_linearizability SPListFamily_underlay
          (@SPListFamilyLayer.L A D) :=
      IndexedFamilyProof.compose_verified_indexed_family D
        (@SPListIndexedObject A) (fun _ => SPList_underlay) MSPList_component.

    Definition MSPListArray :
        layer_implementation_linearizability SPListFamily_underlay
          (@SPListArraySpec.SPListArrayLayer.L A D) :=
      MSPListFamily ▶ @SPListArrayProof.MSPListArrayLinearizable A D.

    (** ** ListPool's underlay: the array of lists and the timestamp *)

    Definition TSStack_underlay : layer_interface :=
      SPListFamily_underlay ⊗ₗ TimestampImpl.E.

    Definition MListPool_underlay :
        layer_implementation_linearizability TSStack_underlay
          (@ListPoolProof.E A D) :=
      MSPListArray ⊗ TimestampProof.MTimestampLinearizable.

    (** ** The stack *)

    Definition TSStack_spec : layer_interface := @TSStackProof.F A D.

    Definition MTSStack_linearizable :
        layer_implementation_linearizability TSStack_underlay TSStack_spec :=
      MListPool_underlay ▶ @TSStackProof.MListPoolTSStack A D.

    Print Assumptions MTSStack_linearizable.
  End ComposedTSStack.
End TSStackTopLevelUnlink.

Export TSStackTopLevelUnlink.
