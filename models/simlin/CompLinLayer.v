Require Import TPSimulation.
Require Import TPSimulationSet.
Require Import CompLin.
Require Import CompLinHComp.
Require Import CompLinVComp.
Require Import CompLinSound.

Module CompLinLayer.
  Definition layer_interface : Type := TPSimulationSet.TPSimulation.layer_interface.

  Definition layer_interface_hcomp (L1 L2 : layer_interface) : layer_interface :=
    TPSimulationSet.TPSimulation.layer_interface_hcomp L1 L2.

  Definition layer_implementation
      (L L' : TPSimulation.TPSimulation.layer_interface) : Type :=
    TPSimulation.TPSimulation.layer_implementation L L'.

  Definition layer_implementation_simulation
      (L L' : layer_interface) : Type :=
    TPSimulationSet.TPSimulation.layer_implementation_simulation L L'.

  Definition layer_implementation_linearizability
      (L L' : layer_interface) : Type :=
    CompLin.CompLin.layer_implementation_linearizability L L'.
  Arguments layer_implementation : clear implicits.
  Arguments layer_implementation_simulation : clear implicits.
  Arguments layer_implementation_linearizability : clear implicits.

  Definition to_set_layer_interface
      (L : TPSimulation.TPSimulation.layer_interface) : layer_interface :=
    TPSimulation.TPSimulation.to_set_layer_interface L.

  Definition layer_implementation_TPSimulationSet
      {L L' : TPSimulation.TPSimulation.layer_interface}
      (M : layer_implementation L L') :
      layer_implementation_simulation
        (to_set_layer_interface L) (to_set_layer_interface L') :=
    TPSimulation.TPSimulation.layer_implementation_TPSimulationSet M.

  Definition LISim2LILin {L L' : layer_interface}
      (M : layer_implementation_simulation L L') :
      layer_implementation_linearizability L L' :=
    CompLinSound.CompLinSound.LISim2LILin M.

  Definition LIHComp {L1 L1' L2 L2' : layer_interface}
      (M1 : layer_implementation_linearizability L1 L1')
      (M2 : layer_implementation_linearizability L2 L2') :
      layer_implementation_linearizability
        (layer_interface_hcomp L1 L2)
        (layer_interface_hcomp L1' L2') :=
    CompLinHComp.CompLinHComp.LIHComp M1 M2.

  Definition LIVComp {L1 L2 L3 : layer_interface}
      (M1 : layer_implementation_linearizability L1 L2)
      (M2 : layer_implementation_linearizability L2 L3) :
      layer_implementation_linearizability L1 L3 :=
    CompLinVComp.CompLinVComp.LIVComp M1 M2.

  Definition LIId (L : layer_interface) :
      layer_implementation_linearizability L L.
  Proof.
    refine (@CompLin.CompLin.Build_layer_implementation_linearizability
              L L CompLin.CompLin.idImpl _).
    intros s Htr. left. exact Htr.
  Defined.

  Definition LICast
      {L1 L2 L1' L2' : layer_interface}
      (HL : L1 = L1') (HR : L2 = L2')
      (M : layer_implementation_linearizability L1 L2) :
      layer_implementation_linearizability L1' L2'.
  Proof.
    subst. exact M.
  Defined.

  Notation "⟦ M ⟧ₛ" := (layer_implementation_TPSimulationSet M)
    (at level 0, M at level 200).
  Notation "⟦ M ⟧ₗ" := (LISim2LILin M)
    (at level 0, M at level 200).
  Notation "⟦ M ⟧ₛₗ" := (LISim2LILin (layer_implementation_TPSimulationSet M))
    (at level 0, M at level 200).
  Notation "L1 ⊗ₗ L2" := (layer_interface_hcomp L1 L2)
    (at level 40, left associativity).
  Notation "M1 ⊗ M2" := (LIHComp M1 M2)
    (at level 40, left associativity).
  Notation "M1 ▶ M2" := (LIVComp M1 M2)
    (at level 80, right associativity).
End CompLinLayer.

Export CompLinLayer.
