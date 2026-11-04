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
Require Import examples.TSStack.NodeMemProof.
Require Import examples.TSStack.SPListProof.
Require Import examples.TSStack.SPListFamilySpec.
Require Import examples.TSStack.SPListFamily.
Require Import examples.TSStack.SPListArraySpec.
Require Import examples.TSStack.SPListArrayProof.
Require Import examples.TSStack.ListPoolElimProof.
Require Import examples.TSStack.TryStackAuxElimProof.
Require Import examples.TSStack.DagStackProof.
Require Import examples.TSStack.TSStackElimProof.

(** Top-level result for the verified timestamped stack with elimination
    (docs/plans/TSStackEliminationPlan.tex).

    The chain is [TSStack_TopLevel]'s with the three layers above the
    array replaced by their elimination variants and the atomic boundary
    moved to the new DagStack layer:

      TSStackElim ◁ DagStack ◁ TryStackAuxElim ◁ ListPoolElim
              ◁ (SPListArray ◁ SPListFamily ◁ per-owner SPList
                   ◁ (NodeMem ◁ five plain memories) ⊗ head CAS register)
                ⊗ (Timestamp ◁ counter CAS register)

    Everything from the SPList array downwards is reused verbatim. *)
Module TSStackTopLevelElim.
  Import LinCCALBase.
  Import TPSimulationSet.TPSimulation.
  Import CompLinLayer.
  Import IndexedFamilySpec.
  Import IndexedFamilyImpl.
  Import SPListFamilySpec.

  Section ComposedTSStackElim.
    Context {A : Type} (D : ThreadDomain.t).

    (** ** One SPList: five plain memories and the head register *)

    Definition SPList_underlay : layer_interface :=
      @NodeMemProof.EPlain A ⊗ₗ SPListProof.ECASLayer.

    Definition MSPList_underlay :
        layer_implementation_linearizability SPList_underlay (@SPListProof.E A) :=
      @NodeMemProof.MNodeMemOverPlain A ⊗ LIId SPListProof.ECASLayer.

    Definition MSPList_component (owner : tid) :
        layer_implementation_linearizability SPList_underlay
          (SetComponentLayer (@SPListIndexedObject A) owner) :=
      MSPList_underlay ▶ @SPListFamilyImpl.splist_component_correct A owner.

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
  End ComposedTSStackElim.
End TSStackTopLevelElim.

Export TSStackTopLevelElim.
