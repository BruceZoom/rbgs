Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import Lang.
Require Import TPSimulationSet.
Require Import CompLinLayer.

Require Import examples.Common.ThreadDomain.
Require Import examples.Common.IndexedFamilySpec.
Require Import examples.Common.IndexedFamily.
Require Import examples.Common.IndexedFamilyProof.
Require Import examples.TSStack.SPListFamilySpec.
Require Import examples.TSStack.SPListUnlinkProof.


(** Composition of the verified per-owner unlinking SPLists into the
    tensor consumed by the indexed-family packaging adapter.  This is
    [SPListFamily] with [SPListUnlinkProof] in place of [SPListProof]; the
    overlay of each component is the unchanged [SPListSpec] layer. *)
Module SPListUnlinkFamilyImpl.
  Import LinCCALBase.
  Import Lang.
  Import TPSimulationSet.TPSimulation.
  Import CompLinLayer.
  Import IndexedFamilySpec.
  Import IndexedFamilyImpl.
  Import SPListFamilySpec.

  Section Family.
    Context {A : Type}.

    Definition SPListUnlinkUnderlay (owner : tid) : layer_interface :=
      @SPListUnlinkProof.E A.

    Lemma splist_component_layer_eq owner :
      @SPListUnlinkProof.FSpec A owner =
      SetComponentLayer (@SPListIndexedObject A) owner.
    Proof. reflexivity. Qed.

    Definition splist_component_correct owner :
        layer_implementation_linearizability
          (SPListUnlinkUnderlay owner)
          (SetComponentLayer (@SPListIndexedObject A) owner).
    Proof.
      eapply LICast.
      - reflexivity.
      - exact (splist_component_layer_eq owner).
      - exact (@SPListUnlinkProof.MSPListUnlinkLinearizable A owner).
    Defined.

    Definition TensorSPListUnderlay (D : ThreadDomain.t) : layer_interface :=
      TensorUnderlay SPListUnlinkUnderlay D.

    Definition TensorSPLists (D : ThreadDomain.t) : layer_interface :=
      TensorLayer (@SPListIndexedObject A) D.

    Definition pack_splist_family_correct (D : ThreadDomain.t) :
        layer_implementation_linearizability
          (TensorSPLists D) (@SPListFamilyLayer.L A D) :=
      IndexedFamilyProof.MPackIndexedFamilyLinearizable D
        (@SPListIndexedObject A).

    Definition compose_splist_family (D : ThreadDomain.t) :
        layer_implementation_linearizability
          (TensorSPListUnderlay D) (@SPListFamilyLayer.L A D) :=
      IndexedFamilyProof.compose_verified_indexed_family D
        (@SPListIndexedObject A) SPListUnlinkUnderlay splist_component_correct.

  End Family.

End SPListUnlinkFamilyImpl.
