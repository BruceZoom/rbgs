Require Import CompLinLayer.
Require Import examples.Stacks.EBStackSepProof.

(** Set-native top-level result for the verified elimination-backoff stack.

    The verified implementation consumes the horizontal composition of the
    abstract try-stack and exchanger interfaces.  The concrete
    implementations in [TryStack.v] and [Exchanger.v] still use the legacy
    singleton logic, so they are deliberately not included in this theorem.
    Doing so would require set-native proofs of those objects; converting
    their interfaces or lifting their old proof records is not permitted. *)
Module EBStackTopLevel.
  Import TPSimulationSet.TPSimulation.
  Import CompLinLayer.

  Section ComposedEBStack.
    Context {A : Type}.

    Definition TryStack_spec : layer_interface :=
      @EBStackSepSetProof.ETryStackLayer A.

    Definition Exchanger_spec : layer_interface :=
      @EBStackSepSetProof.EExchangerLayer A.

    Definition EBStack_underlay : layer_interface :=
      TryStack_spec ⊗ₗ Exchanger_spec.

    Definition EBStack_spec : layer_interface :=
      @EBStackSepSetProof.F A.

    Definition MEBStack_simulation :
        layer_implementation_simulation EBStack_underlay EBStack_spec :=
      @EBStackSepSetProof.Mebstack A.

    Definition MEBStack_linearizable :
        layer_implementation_linearizability EBStack_underlay EBStack_spec :=
      LISim2LILin MEBStack_simulation.
  End ComposedEBStack.
End EBStackTopLevel.

Export EBStackTopLevel.
