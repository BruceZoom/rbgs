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
Require Import TPSimulationSet.
Require Import CompLinComplete.
Require Import RGILogicSetComplete.
Require Import CompLinAux.
Require Import CompLinRGComplete.

(** Paper-facing exports for the set-of-possibilities logic.  The general
    context-transforming frame rule is [RGILogicSet.RGILogic.provable_frame];
    [provable_frame_same_context] is its context-preserving companion. *)
Module PaperTheorems.
  Import Reg LinCCALBase LTSSpec Lang Semantics.
  Import AssertionsSet.
  Import RGISimulationSet.RGISimulation.

  Module SetLogic := RGILogicSet.RGILogic.
  Module Sound := CompLinSound.CompLinSound.
  Module Complete := CompLinComplete.CompLinComplete.
  Module LogicComplete := RGILogicSetComplete.RGILogicComplete.
  Module RGComplete := CompLinRGComplete.CompLinRGComplete.

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

  (* Lemma 5.3: the Threadpool Simulation (Definition 5.2) is equivalent
     to Compositional Linearizability (Definition 4.1). *)
  Theorem threadpool_simulation_iff_CompLin
      {E F} (VE : @LTS E) (VF : @LTS F) (M : ModuleImpl E F)
      (σ0 : State VE) (ρ0 : State VF) :
    TPSimulationSet.TPSimulation.cal M σ0 ρ0 <-> CompLin.CompLin M σ0 ρ0.
  Proof.
    apply Complete.cal_iff_CompLin.
  Qed.

  (* Completeness of the program logic with respect to the method
     simulation: semantic assertions prove every method-simulated body. *)
  Theorem logic_complete_for_method_simulation
      {E F} (VE : @LTS E) (VF : @LTS F) (M : ModuleImpl E F)
      (R G : @RGRelation _ _ VE VF) (I : @ProofState _ _ VE VF -> Prop) (t : tid)
      (HGrefl : forall s, G s s)
      (HGtrans : forall s1 s2 s3, G s1 s2 -> G s2 s3 -> G s1 s3)
      (HGerr : forall σ1 Δ1 σ2 ev, te_tid ev = t -> Step VE ev σ1 σ2 ->
        APError (σ1, Δ1) -> G (σ1, Δ1) (σ2, Δ1))
      (HRerr : forall s s', R s s' -> APError s -> APError s')
      (HIerr : forall s, APError s -> I s)
      (HRlin : forall s s' f r, R s s' -> ALin t (ls_linr f r) s -> ALin t (ls_linr f r) s')
      (f : Sig.op F)
      (Hmsim : forall s, ComposeA I (Ginv t f) s ->
        MethodSimulation R G I t f (SetPossState.σ s) (M f t) None (SetPossState.Δ s)) :
    exists P Q, SetLogic.MethodProvable VE VF M R G I t f P Q.
  Proof.
    do 2 eexists.
    exact (LogicComplete.msim_MethodProvable M R G I t HGrefl HGtrans HGerr HRerr HIerr HRlin f Hmsim).
  Qed.

  (* Completeness of the thread-local reasoning for Compositional
     Linearizability, modulo auxiliary state: over the layer interfaces
     extended with the underlay history and the per-thread operation
     lists, every compositionally linearizable implementation has
     rely/guarantee/invariant triples under which all its methods are
     provable in the logic; and conversely the logic's soundness, the
     threadpool simulation's soundness and the erasure of the auxiliary
     state give back compositional linearizability. *)
  Theorem CompLin_logic_complete
      {E F} (VE : @LTS E) (VF : @LTS F) (M : ModuleImpl E F)
      (σ0 : State VE) (ρ0 : State VF) :
    CompLin.CompLin M σ0 ρ0 <->
    exists (R G : tid -> @RGRelation _ _ (CompLinAux.CompLinAux.hist_lts VE)
                                         (CompLinAux.CompLinAux.ops_lts VF))
           (I : @ProofState _ _ (CompLinAux.CompLinAux.hist_lts VE)
                               (CompLinAux.CompLinAux.ops_lts VF) -> Prop),
      (forall t, ValidRGI (R t) (G t) I t) /\
      (forall t1 t2, t1 <> t2 ->
        (I ⊓ (G t1 ∪ ((GINV t1 ∪ GRET t1) ∪ GId)) ⊆ R t2)%RGRelation) /\
      (forall t f, exists P Q,
        SetLogic.MethodProvable (CompLinAux.CompLinAux.hist_lts VE)
          (CompLinAux.CompLinAux.ops_lts VF) M (R t) (G t) I t f P Q) /\
      I (CompLinAux.CompLinAux.hist_init σ0, CompLinAux.CompLinAux.ops_init ρ0, (@TMap.empty _)).
  Proof.
    split.
    - intros Hcl.
      exists (RGComplete.R M σ0 ρ0), RGComplete.G, (RGComplete.I M σ0 ρ0).
      exact (RGComplete.RG_complete M σ0 ρ0 Hcl).
    - intros (R & G & I & Hv & Hrg & Hp & Hi).
      apply (CompLinAux.CompLinAux.CompLin_unaux M σ0 ρ0).
      apply Sound.cal_to_CompLin.
      eapply SetLogic.soundness; eauto.
  Qed.
End PaperTheorems.
