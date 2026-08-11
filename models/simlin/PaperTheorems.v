Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import Assertion.
Require Import RGISimulationSet.
Require Import RGILogicSet.
Require Import CompLin.
Require Import CompLinSound.

(** Paper-facing exports for the set-of-possibilities logic.  The general
    context-transforming frame rule is [RGILogicSet.RGILogic.provable_frame];
    [provable_frame_same_context] is its context-preserving companion. *)
Module PaperTheorems.
  Import Reg LinCCALBase LTSSpec Lang Semantics.
  Import AssertionsSet.
  Import RGISimulationSet.RGISimulation.

  Module SetLogic := RGILogicSet.RGILogic.
  Module Sound := CompLinSound.CompLinSound.

  Theorem framed_logic_soundness_CompLin
      {E F} (VE : @LTS E) (VF : @LTS F) (M : ModuleImpl E F)
      (R G : tid -> @RGRelation _ _ VE VF) I
      (HvalidRG : forall t, ValidRGI (R t) (G t) I t)
      (HRG : forall t1 t2 : tid, t1 <> t2 ->
        (I ⊓ (G t1 ∪ (GINV t1 ∪ GRET t1 ∪ GId)) ⊆ R t2)%RGRelation)
      (Hprovable : forall t f, exists P Q,
        SetLogic.MethodProvable VE VF M (R t) (G t) I t f P Q)
      σ0 ρ0
      (Hinit : I (σ0, ρ0, (@TMap.empty _))) :
      CompLin.CompLin M σ0 ρ0.
  Proof.
    apply Sound.cal_to_CompLin.
    eapply SetLogic.soundness; eauto.
  Qed.
End PaperTheorems.
