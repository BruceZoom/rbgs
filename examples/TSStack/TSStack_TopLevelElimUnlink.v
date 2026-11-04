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
Require Import examples.TSStack.ListPoolElimProof.
Require Import examples.TSStack.TryStackAuxElimProof.
Require Import examples.TSStack.DagStackProof.
Require Import examples.TSStack.TSStackElimProof.

(** Top-level result for the verified timestamped stack with both
    elimination and unlinking: the elimination chain of
    [TSStack_TopLevelElim] over the unlinking lists of
    [TSStack_TopLevelUnlink].

      TSStackElim ◁ DagStack ◁ TryStackAuxElim ◁ ListPoolElim
              ◁ (SPListArray ◁ SPListFamily ◁ per-owner SPListUnlink
                   ◁ (NodeMemUnlink ◁ five plain memories) ⊗ head CAS register)
                ⊗ (Timestamp ◁ counter CAS register)

    The two variants compose freely because the SPList array interface is
    untouched by either. *)
Module TSStackTopLevelElimUnlink.
  Import LinCCALBase.
  Import TPSimulationSet.TPSimulation.
  Import CompLinLayer.
  Import IndexedFamilySpec.
  Import IndexedFamilyImpl.
  Import SPListFamilySpec.

  Section ComposedTSStackElimUnlink.
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

    (** ** ListPoolElim's underlay: the array of lists and the timestamp *)

    Definition TSStack_underlay : layer_interface :=
      SPListFamily_underlay ⊗ₗ TimestampImpl.E.

    Definition MListPool_underlay :
        layer_implementation_linearizability TSStack_underlay
          (@ListPoolElimProof.E A D) :=
      MSPListArray ⊗ TimestampProof.MTimestampLinearizable.

    (** ** The layers above the array *)

    Definition MListPoolElim :
        layer_implementation_linearizability TSStack_underlay
          (@ListPoolElimProof.F A D) :=
      MListPool_underlay ▶ @ListPoolElimProof.MListPoolElimLinearizable A D.

    Definition MTryStackAuxElim :
        layer_implementation_linearizability TSStack_underlay
          (@TryStackAuxElimProof.F A D) :=
      MListPoolElim ▶ @TryStackAuxElimProof.MTryStackAuxElimLinearizable A D.

    Definition MDagStack :
        layer_implementation_linearizability TSStack_underlay
          (@DagStackProof.F A D) :=
      MTryStackAuxElim ▶ @DagStackProof.MDagStackLinearizable A D.

    (** ** The stack *)

    Definition TSStack_spec : layer_interface := @TSStackElimProof.F A D.

    Definition MTSStack_linearizable :
        layer_implementation_linearizability TSStack_underlay TSStack_spec :=
      MDagStack ▶ @TSStackElimProof.MTSStackElimLinearizable A D.

    Print Assumptions MTSStack_linearizable.
  End ComposedTSStackElimUnlink.
End TSStackTopLevelElimUnlink.

Export TSStackTopLevelElimUnlink.
