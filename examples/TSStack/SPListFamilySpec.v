Require Import FMapPositive.
Require Import Coq.Lists.List.

Require Import models.EffectSignatures.
Require Import examples.Common.Heap.
Require Import examples.TSStack.SPListSpec.
Require Import examples.Common.ThreadDomain.
Require Import examples.Common.IndexedFamilySpec.
Require Import LinCCAL.
Require Import LTS.
Require Import TPSimulationSet.


(** The SPList instance of the reusable indexed-family construction. *)
Module SPListFamilySpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import SPListSpec.
  Import TPSimulationSet.TPSimulation.
  Import IndexedFamilySpec.

  Section Spec.
    Context {A : Type}.

    Definition empty_row_state : @SPListState A :=
      {|
        counter := 0;
        nodes := empty_heap;
        order := nil;
        snapshot := TMap.empty (list Addr * nat)
      |}.

    Definition SPListIndexedObject : IndexedObject (@ESPList A) :=
      {|
        component_state := @SPListControl A;
        component_step := fun owner => Step (@VSPList A owner);
        component_error := fun owner => Error (@VSPList A owner);
        component_init := fun _ => Ready empty_row_state
      |}.

    Definition family_call :
        forall (owner : tid) (op : @ESPList_op A),
          Sig.op (EIndexed (@ESPList A)) :=
      @indexed_call (@ESPList A).

  End Spec.

  Arguments family_call {A} _ _.

  Module SPListFamilyLayer.
    Section Layer.
      Context {A : Type}.
      Context (D : ThreadDomain.t).

      Definition L : layer_interface :=
        IndexedFamilyLayer D (@SPListIndexedObject A).
    End Layer.
  End SPListFamilyLayer.

End SPListFamilySpec.
