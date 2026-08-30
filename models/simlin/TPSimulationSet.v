Require Import FMapPositive.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.
Require Import Coq.Classes.RelationClasses.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.Program.Program.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.

Import Reg.
Import LinCCALBase.
Import LTSSpec.
Import Semantics.

(* threadpool simulation *)
Module TPSimulation.
  Import Lang.

  Section Simulation.
    Context {E : Op.t}.
    Context {F : Op.t}.
    Context {VE : @LTS E}.
    Context {VF : @LTS F}.
    Context (M : ModuleImpl E F).

    Record ContinueCore
        (X : State VE -> @ThreadPoolState E F -> AbstractConfig VF -> Prop)
        (σ : State VE) (c : @ThreadPoolState E F)
        (Δ : AbstractConfig VF) : Prop := {
        tpsim_invstep :
          forall t f c' (Hstep : invstep M t f c c'),
          X σ c' (ac_inv Δ t f);
        tpsim_retstep :
          forall t f ret c' (Hstep : retstep t f ret c c'),
          (forall ρ π, Δ ρ π -> TMap.find t π = Some (ls_linr f ret)) /\
          X σ c' (ac_res Δ t);
        tpsim_ustep :
          forall ev σ' c' (Hstep : ustep ev σ c σ' c'),
          exists (Δ' : AbstractConfig VF),
            (Δ' ⊆ ac_steps Δ)%AbstractConfig /\
            X σ' c' Δ';
        tpsim_taustep :
          forall t c' (Hstep : taustep t c c'),
          X σ c' Δ;
        tpsim_noerror : forall ev, ~ uerror ev σ c
      }.

    Definition ErrorCore (Δ : AbstractConfig VF) : Prop :=
      exists ρ π, Δ ρ π /\ poss_steps (PossOk ρ π) PossError.

    Inductive SimulationHead
        (X : State VE -> @ThreadPoolState E F -> AbstractConfig VF -> Prop)
        (σ : State VE) (c : @ThreadPoolState E F) :
        AbstractConfig VF -> Prop :=
    | HeadError Δ : ErrorCore Δ -> SimulationHead X σ c Δ
    | HeadContinue Δ : ContinueCore X σ c Δ -> SimulationHead X σ c Δ
    | HeadUpdate Δ Δ' :
        (Δ' ⊆ ac_steps Δ)%AbstractConfig ->
        SimulationHead X σ c Δ' -> SimulationHead X σ c Δ.

    Inductive AbstractUpdateSteps :
        AbstractConfig VF -> AbstractConfig VF -> Prop :=
    | AbstractUpdatesRefl Δ : AbstractUpdateSteps Δ Δ
    | AbstractUpdatesStep Δ Δ' Δ'' :
        (Δ' ⊆ ac_steps Δ)%AbstractConfig ->
        AbstractUpdateSteps Δ' Δ'' -> AbstractUpdateSteps Δ Δ''.

    (** Normalized presentation of the mixed fixed point.  A coinductive
        node contains exactly one finite abstract-update prefix followed by
        either an error or a concrete continuation core.  This is the
        normal form computed by [head_normalizes], and keeps recursive
        continuations directly guarded by the sole coinductive constructor. *)
    CoInductive TPSimulation (σ : State VE) (c : @ThreadPoolState E F)
        (Δ : AbstractConfig VF) : Prop :=
    | TPSimRoll : forall Δ', AbstractUpdateSteps Δ Δ' ->
        (ErrorCore Δ' \/ ContinueCore TPSimulation σ c Δ') ->
        TPSimulation σ c Δ.

    Lemma TPSim_Error (σ : State VE) (c : @ThreadPoolState E F)
        (Δ : AbstractConfig VF) (ρ : State VF) (π : tmap (@LinState F)) :
      Δ ρ π -> poss_steps (PossOk ρ π) PossError ->
      TPSimulation σ c Δ.
    Proof.
      intros Hposs Herror. eapply TPSimRoll with (Δ' := Δ).
      - constructor.
      - left. unfold ErrorCore. exists ρ, π. now split.
    Qed.

    Lemma TPSim_Continue (σ : State VE) (c : @ThreadPoolState E F)
        (Δ : AbstractConfig VF) :
      ContinueCore TPSimulation σ c Δ -> TPSimulation σ c Δ.
    Proof.
      intro H. eapply TPSimRoll with (Δ' := Δ).
      - constructor.
      - now right.
    Qed.

    Lemma TPSim_Update (σ : State VE) (c : @ThreadPoolState E F)
        (Δ Δ' : AbstractConfig VF) :
      (Δ' ⊆ ac_steps Δ)%AbstractConfig ->
      TPSimulation σ c Δ' -> TPSimulation σ c Δ.
    Proof.
      intros Hsub Hsim. destruct Hsim as [Δ'' Hupdates Hterminal].
      eapply TPSimRoll with (Δ' := Δ'').
      - econstructor; eauto.
      - exact Hterminal.
    Qed.

    Lemma head_normalizes
        (X : State VE -> @ThreadPoolState E F -> AbstractConfig VF -> Prop)
        (σ : State VE) (c : @ThreadPoolState E F)
        (Δ : AbstractConfig VF) :
      SimulationHead X σ c Δ ->
      exists Δ', AbstractUpdateSteps Δ Δ' /\
        (ErrorCore Δ' \/ ContinueCore X σ c Δ').
    Proof.
      intro H. induction H.
      - exists Δ. split; [constructor|auto].
      - exists Δ. split; [constructor|auto].
      - destruct IHSimulationHead as [Δ'' [Hs Hcore]].
        exists Δ''. split; [econstructor; eauto|exact Hcore].
    Qed.

    Lemma simulation_normalizes (σ : State VE)
        (c : @ThreadPoolState E F) (Δ : AbstractConfig VF) :
      TPSimulation σ c Δ ->
      exists Δ', AbstractUpdateSteps Δ Δ' /\
        (ErrorCore Δ' \/ ContinueCore TPSimulation σ c Δ').
    Proof.
      intros Hsim. destruct Hsim as [Δ' Hupdates Hterminal]. eauto.
    Qed.

    Lemma TPSim_Head (σ : State VE) (c : @ThreadPoolState E F)
        (Δ : AbstractConfig VF) :
      SimulationHead TPSimulation σ c Δ -> TPSimulation σ c Δ.
    Proof.
      intro Hhead. destruct (head_normalizes _ _ _ _ Hhead)
        as [Δ' [Hupdates Hterminal]].
      eapply TPSimRoll with (Δ' := Δ'); eauto.
    Qed.

    Lemma head_prepend_updates
        (X : State VE -> @ThreadPoolState E F -> AbstractConfig VF -> Prop)
        (σ : State VE) (c : @ThreadPoolState E F)
        (Δ Δ' : AbstractConfig VF) :
      AbstractUpdateSteps Δ Δ' -> SimulationHead X σ c Δ' ->
      SimulationHead X σ c Δ.
    Proof.
      intros Hupdates Hhead. induction Hupdates.
      - exact Hhead.
      - eapply HeadUpdate; eauto.
    Qed.

    Lemma TPSim_to_Head (σ : State VE) (c : @ThreadPoolState E F)
        (Δ : AbstractConfig VF) :
      TPSimulation σ c Δ -> SimulationHead TPSimulation σ c Δ.
    Proof.
      intros [Δ' Hupdates [Herror | Hcontinue]].
      - eapply head_prepend_updates; [exact Hupdates|].
        now apply HeadError.
      - eapply head_prepend_updates; [exact Hupdates|].
        now apply HeadContinue.
    Qed.

    Definition ac_init (ρ0 : State VF) := [(ρ0, (TMap.empty _))]%AbstractConfig.

    Definition cal (σ0 : State VE) (ρ0 : State VF) : Prop :=
      TPSimulation σ0 (TMap.empty _) (ac_init ρ0).
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

  Record layer_implementation_simulation {L L' : layer_interface} :=
  {
    li_impl : ModuleImpl (li_sig L) (li_sig L');
    li_correct : cal li_impl (li_init L) (li_init L');
  }.
  Arguments layer_implementation_simulation : clear implicits.
End TPSimulation.
