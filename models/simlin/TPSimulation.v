Require Import FMapPositive.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import TPSimulationSet.

(* threadpool simulation *)
Module TPSimulation.
  Import Reg.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import Semantics.

  Section Simulation.
    Context {E : Op.t}.
    Context {F : Op.t}.
    Context {VE : @LTS E}.
    Context {VF : @LTS F}.
    Context (M : ModuleImpl E F).

    Definition ConcreteConfig : Type := (State VE * @ThreadPoolState E F)%type.
    Definition AbstractConfig : Type := @Poss F VF%type.

    CoInductive TPSimulation (σ : State VE) c (ρ : State VF) π : Prop :=
    | TPSim_Error
        (Herror : poss_steps (PossOk ρ π) (PossError)) :
        TPSimulation σ c ρ π
    | TPSim_Continue
        (tpsim_invstep :
          forall t f c' (Hstep : invstep M t f c c'),
          TPSimulation σ c' ρ (TMap.add t (ls_inv f) π))
        (tpsim_retstep :
          forall t f ret c' (Hstep : retstep t f ret c c'),
          TMap.find t π = Some (ls_linr f ret) /\
          TPSimulation σ c' ρ (TMap.remove t π))
        (tpsim_ustep :
          forall ev σ' c' (Hstep : ustep ev σ c σ' c'),
          exists ρ' π',
            poss_steps (PossOk ρ π) (PossOk ρ' π') /\
            TPSimulation σ' c' ρ' π')
        (tpsim_linstep :
          exists ρ' π',
          poss_steps (PossOk ρ π) (PossOk ρ' π') /\
          TPSimulation σ c ρ' π')
        (tpsim_taustep :
          forall t c' (Hstep : taustep t c c'),
          TPSimulation σ c' ρ π)
        (tpsim_noerror :
          forall ev, ~ uerror ev σ c) :
        TPSimulation σ c ρ π.

    Definition cal (σ0 : State VE) (ρ0 : State VF) : Prop :=
      TPSimulation σ0 (TMap.empty _) ρ0 (TMap.empty _).

    (* TODO: soundness: linearizability *)
  End Simulation.


  Record layer_interface :=
  {
    li_sig : Op.t;
    li_lts : @LTS li_sig;
    li_init : State li_lts;
  }.

  Definition layer_interface_hcomp (L1 L2 : layer_interface) : layer_interface :=
  {|
    li_sig := Sig.Plus.omap (li_sig L1) (li_sig L2);
    li_lts := tens_lts (li_lts L1) (li_lts L2);
    li_init := pair (li_init L1) (li_init L2);
  |}.

  Notation "L1 ⊗ₗ L2" := (layer_interface_hcomp L1 L2)
    (at level 40, left associativity).

  Record layer_implementation {L L' : layer_interface} :=
  {
    li_impl : ModuleImpl (li_sig L) (li_sig L');
    li_correct : cal li_impl (li_init L) (li_init L');
  }.
  Arguments layer_implementation : clear implicits.

  Definition to_set_layer_interface (L : layer_interface) :
    TPSimulationSet.TPSimulation.layer_interface :=
  {|
    TPSimulationSet.TPSimulation.li_sig := li_sig L;
    TPSimulationSet.TPSimulation.li_lts := li_lts L;
    TPSimulationSet.TPSimulation.li_init := li_init L;
  |}.

  Section SingletonLift.
    Context {E : Op.t}.
    Context {F : Op.t}.
    Context {VE : @LTS E}.
    Context {VF : @LTS F}.
    Context (M : ModuleImpl E F).

    Lemma ac_singleton_subset_steps
        (Δ : Semantics.AbstractConfig VF) (ρ ρ' : State VF)
        (π π' : tmap (@LinState F))
        (Hequiv : ac_equiv Δ (ac_singleton ρ π))
        (Hsteps : poss_steps (PossOk ρ π) (PossOk ρ' π')) :
      (ac_singleton ρ' π' ⊆ ac_steps Δ)%AbstractConfig.
    Proof.
      intros ρ0 π0 Hsingle.
      inversion Hsingle; subst.
      econstructor; eauto.
      apply Hequiv. constructor.
    Qed.

    Theorem TPSimulation_singleton_lift σ c ρ π :
      TPSimulation M σ c ρ π ->
      forall (Δ : Semantics.AbstractConfig VF),
        ac_equiv Δ (ac_singleton ρ π) ->
        @TPSimulationSet.TPSimulation.TPSimulation E F VE VF M σ c Δ.
    Proof.
      revert σ c ρ π.
      cofix CIH.
      intros σ c ρ π HTPSim Δ Hequiv.
      inversion HTPSim; subst.
      - eapply TPSimulationSet.TPSimulation.TPSim_Error with (ρ := ρ) (π := π);
          eauto.
        apply Hequiv. constructor.
      - eapply TPSimulationSet.TPSimulation.TPSimRoll with (Δ' := Δ).
        + constructor.
        + right. constructor.
          * intros t f c' Hstep.
            eapply CIH; eauto.
            intros ρ0 π0. split; intro H.
            -- inversion H; subst.
               apply Hequiv in Hposs.
               inversion Hposs; subst.
               constructor.
            -- inversion H; subst.
               constructor.
               apply Hequiv. constructor.
          * intros t f ret c' Hstep.
            split.
            -- intros ρ0 π0 Hposs.
               apply Hequiv in Hposs.
               inversion Hposs; subst.
               destruct (tpsim_retstep t f ret c' Hstep) as [? _].
               auto.
            -- destruct (tpsim_retstep t f ret c' Hstep) as [_ Hsim].
               eapply CIH; eauto.
               intros ρ0 π0. split; intro H.
               ++ inversion H; subst.
                  apply Hequiv in Hposs.
                  inversion Hposs; subst.
                  constructor.
               ++ inversion H; subst.
                  constructor.
                  apply Hequiv. constructor.
          * intros ev σ' c' Hstep.
            destruct (tpsim_ustep ev σ' c' Hstep)
              as [ρ' [π' [Hsteps Hsim]]].
            exists (ac_singleton ρ' π'). split.
            -- eapply ac_singleton_subset_steps; eauto.
            -- eapply CIH; eauto. reflexivity.
          * intros t c' Hstep.
            eapply CIH; eauto.
          * auto.
    Qed.

    Corollary TPSimulation_singleton σ c ρ π :
      TPSimulation M σ c ρ π ->
      @TPSimulationSet.TPSimulation.TPSimulation E F VE VF M σ c (ac_singleton ρ π).
    Proof.
      intros.
      eapply TPSimulation_singleton_lift; eauto.
      reflexivity.
    Qed.
  End SingletonLift.

  Definition layer_implementation_TPSimulationSet
      {L L' : layer_interface}
      (LI : layer_implementation L L') :
    TPSimulationSet.TPSimulation.layer_implementation_simulation
      (to_set_layer_interface L) (to_set_layer_interface L').
  Proof.
    destruct LI as [M Hcorrect].
    refine (@TPSimulationSet.TPSimulation.Build_layer_implementation_simulation
              (to_set_layer_interface L) (to_set_layer_interface L') M _).
    unfold TPSimulationSet.TPSimulation.cal,
           TPSimulationSet.TPSimulation.ac_init,
           cal in *.
    apply TPSimulation_singleton.
    exact Hcorrect.
  Defined.

  Notation "{ M }" := (layer_implementation_TPSimulationSet M).

End TPSimulation.
