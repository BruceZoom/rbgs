Require Import CompLinLayer.
Require Import examples.Common.Heap.
Require Import examples.Common.OwnedMemSpec.
Require Import examples.Stacks.EBStack.
Require Import examples.Stacks.TryStack.
Require Import examples.Exchanger.Exchanger.

Section ComposedEBStack.
  Context {A : Type}.

  Definition TryStack_underlay : layer_interface :=
    to_set_layer_interface (TryStackImpl.ECASLayer) ⊗ₗ
    to_set_layer_interface (@OwnedMemSpec.WriteOwnedMemLayer.E (A * option Addr)).

  Definition Exchanger_underlay : layer_interface :=
    to_set_layer_interface (@ExchangerImpl.E (option A)).

  Definition EBStack_underlay : layer_interface :=
    TryStack_underlay ⊗ₗ Exchanger_underlay.

  Definition EBStack_spec : layer_interface :=
    to_set_layer_interface (@EBStackImpl.F A).

  Definition MTryStack_linearizable :
    layer_implementation_linearizability
      TryStack_underlay
      (to_set_layer_interface (@TryStackImpl.F A)) :=
    (LIId (to_set_layer_interface (TryStackImpl.ECASLayer)) ⊗
     ⟦ @OwnedMemSpec.WriteOwnedMemLayer.Mowned_mem (A * option Addr) ⟧ₛₗ) ▶
    ⟦ @TryStackImpl.Mtrystack A ⟧ₛₗ.

  Definition MExchanger_linearizable :
    layer_implementation_linearizability
      Exchanger_underlay
      (to_set_layer_interface (@ExchangerImpl.F (option A))) :=
    ⟦ @ExchangerImpl.Mexchanger (option A) ⟧ₛₗ.

  Definition MEBStack_linearizable :
    layer_implementation_linearizability EBStack_underlay EBStack_spec :=
    (MTryStack_linearizable ⊗ MExchanger_linearizable) ▶
    ⟦ @EBStackImpl.Mebstack A ⟧ₛₗ.
End ComposedEBStack.
