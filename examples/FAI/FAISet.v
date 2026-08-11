Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.
Require Import Lia.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import Logics.
Require Import Assertion.
Require Import TPSimulationSet.
Require Import RGILogicSet.
Require Import SingletonPossibility.
Require Import examples.Common.AtomicLTS.
Require Import examples.FAI.FAISpec.
Require Import examples.Locks.LockSpec.
Require Import examples.Registers.RegSpec.

(** The FAI proof carried out by the set-of-possibilities logic, using the
    singleton facade for its pointwise assertions and atomic updates.  The
    original proof remains in [FAI.v]. *)
Module FAISetImpl.
  Import LinCCALBase LTSSpec Lang Semantics.
  Import AssertionsSingle.
  Import SingletonPossibility.
  Import TPSimulationSet.TPSimulation.
  Import AtomicLTS FAISpec LockSpec RegSpec.
  Import (coercions, canonicals, notations) Sig.
  Import (notations) LinCCAL.
  Import (canonicals) Sig.Plus.
  Module SetLogic := RGILogicSet.RGILogic.
  Import SetLogic.

  Open Scope prog_scope.
  Open Scope rg_relation_scope.
  Open Scope assertion_scope.

  Definition E : layer_interface :=
  {|
    li_sig := Sig.Plus.omap ELock (EReg nat);
    li_lts := tens_lts VLock VReg;
    li_init := pair (Idle Unlocked) (Idle O);
  |}.

  Definition F : layer_interface :=
  {|
    li_sig := EFAI;
    li_lts := VFAI;
    li_init := Idle O
  |}.

  Definition fai_impl (_ : tid) : Prog (li_sig E) nat :=
    inl acq >= _ =>
    inr get >= c =>
    inr (set (S c)) >= _ =>
    inl rel >= _ =>
    Ret c.

  Definition assertion :=
    @Assertion (@SinglePossState.ProofState _ _ (li_lts E) (li_lts F)).
  Definition rg_relation :=
    @AssertionsSingle.A.RGRelation _ _ (li_lts E) (li_lts F).

  Definition I : assertion :=
    fun s => forall l r, σ s = pair l r -> ρ s = Idle (state r).

  Definition NotOwned : assertion :=
    fun s => state (fst (σ s)) = Unlocked.

  Definition OwnedBy t : assertion :=
    fun s => state (fst (σ s)) = Locked t.

  Definition NotOwnedBy t : assertion :=
    fun s => state (fst (σ s)) <> Locked t.

  Lemma OwnedByExclude : forall t1 t2 s,
    t1 <> t2 -> OwnedBy t2 s -> NotOwnedBy t1 s.
  Proof.
    unfold OwnedBy, NotOwnedBy.
    intros. intros ?. congruence.
  Qed.

  Lemma OwnedByIsOwned t : forall s, OwnedBy t s -> NotOwned s -> False.
  Proof.
    unfold OwnedBy, NotOwned.
    intros. congruence.
  Qed.

  Definition RegVal v : assertion :=
    fun s => snd (σ s) = v.

  Definition G_lock t : rg_relation :=
    fun s1 s2 => NotOwned s1 /\ OwnedBy t s2 /\ snd (σ s1) = snd (σ s2).

  Definition G_unlock t : rg_relation :=
    fun s1 s2 => OwnedBy t s1 /\ NotOwned s2 /\ snd (σ s1) = snd (σ s2).

  Definition G_id t : rg_relation :=
    fun s1 s2 => state (fst (σ s1)) = state (fst (σ s2))
                  /\ (NotOwnedBy t s1 -> snd (σ s1) = snd (σ s2)).

  Definition G t : rg_relation := (G_lock t ∪ G_unlock t ∪ G_id t)
                              ∩ fun s1 s2 => forall t', t <> t'
                                  -> TMap.find t' (π s1) = TMap.find t' (π s2).

  Definition R t : rg_relation :=
    fun s1 s2 => (OwnedBy t s1 -> OwnedBy t s2 /\ snd (σ s1) = snd (σ s2))
                  /\ (TMap.find t (π s1) = TMap.find t (π s2)).

  Lemma Istable {t} : Stable (R t) I I.
  Proof. unfold Stable. apply ConjRightImpl. apply ImplRefl. Qed.

  Lemma OwnedBystable {t} : Stable (R t) I (OwnedBy t).
  Proof.
    unfold Stable.
    intros ? [[? [? ?]] ?].
    unfold R in *. tauto.
  Qed.

  Lemma ALinstable {t ls}: Stable (R t) I (ALin t ls).
  Proof.
    unfold Stable, ALin, R.
    intros ? [[? [? [? ?]]] ?].
    rewrite <- H1. auto.
  Qed.

  Lemma OwnedRegStable {t v} : Stable (R t) I (OwnedBy t //\\ RegVal v).
  Proof.
    unfold Stable, RegVal, R.
    intros ? [[? [[? ?] [? ?]]] ?].
    apply H1 in H as [? ?].
    split; auto. rewrite <- H4; auto.
  Qed.

  Create HintDb stableDB.
  #[local] Hint Resolve Istable OwnedBystable ALinstable OwnedRegStable : stableDB.

  Lemma source_valid_rg t : forall s s', R t s s' -> I s' ->
    TMap.find t (π s) = None <-> TMap.find t (π s') = None.
  Proof.
    unfold R. intros. destruct H. rewrite H1. tauto.
  Qed.

  Lemma source_rg_compatible t1 t2 : t1 <> t2 -> forall s1 s2,
    (G t1 s1 s2 \/ (GINV t1 s1 s2 \/ GRET t1 s1 s2) \/ GId s1 s2) ->
    R t2 s1 s2.
  Proof.
    intros Hneq s1 s2 Hrel. unfold G, R in *.
    destruct Hrel as [HG | [[Hinv | Hret] | Hid]].
    - destruct HG as [HG Hπ]. split; auto.
      destruct HG as [[Hlock | Hunlock] | Hid']; try tauto.
      + destruct Hlock as [Hnot [Howned Hsame]]. intros Howned2.
        exfalso. eapply OwnedByIsOwned; eauto.
      + destruct Hunlock as [Howned [Hnot Hsame]]. intros Howned2.
        unfold OwnedBy in *. congruence.
      + destruct Hid' as [Hstate Hsame]. intros Howned.
        split.
        * unfold OwnedBy in *. rewrite <- Hstate. exact Howned.
        * apply Hsame. eapply OwnedByExclude; eauto.
    - unfold GINV, Ginv, LiftRelation_π in *.
      destruct Hinv as (? & ? & ? & ? & ?). unfold OwnedBy.
      rewrite H, H2. split; auto.
      rewrite PositiveMap.gso; try tauto; auto.
    - unfold GRET, Gret, LiftRelation_π in *.
      destruct Hret as (? & ? & ? & ? & ? & ?). unfold OwnedBy.
      rewrite H, H2. split; auto.
      rewrite PositiveMap.gro; try tauto; auto.
    - unfold GId in Hid. subst. auto.
  Qed.

  Program Definition Mfai : layer_implementation_simulation E F :=
  {| li_impl fai := fai_impl |}.
  Next Obligation.
    eapply SetLogic.soundness
      with (R := fun t => lift_relation (R t))
           (G := fun t => lift_relation (G t))
           (I := lift_assert I).
    (* valid RG *)
    {
      intros t. eapply lift_valid_rgi. apply source_valid_rg.
    }
    (* cross-thread compatibility *)
    {
      intros t1 t2 Hneq s s' Hrel.
      eapply lift_parallel_compat; [exact Hneq| |exact Hrel].
      apply source_rg_compatible; exact Hneq.
    }
    (* method provable *)
    {
      intros t. destruct f.
      exists (lift_assert (I //\\ ALin t (Semantics.ls_inv fai))).
      exists (fun ret => lift_assert
        (I //\\ ALin t (Semantics.ls_linr fai ret))).
      constructor.
      - intros s Hcompose.
        eapply (lift_ginv_compose t fai I
          (I //\\ ALin t (Semantics.ls_inv fai))); [|exact Hcompose].
        intros out [pre [HI Hginv]].
        unfold Ginv, LiftRelation_π in Hginv.
        destruct Hginv as [Hσ [Hρ [Hnone Hπ]]].
        split.
        + unfold I in *. intros l r Hout.
          etransitivity; [symmetry; exact Hρ|].
          apply (HI l r). etransitivity; [exact Hσ|exact Hout].
        + unfold ALin. simpl. etransitivity.
          * exact (f_equal (TMap.find t) Hπ).
          * apply PositiveMap.gss.
      - intros s Hlift. eapply lift_impl; [|exact Hlift].
        apply ConjLeftImpl. apply ImplRefl.
      - apply lift_stable. solve_conj_stable stableDB.
      - intros ret s Hcompose.
        eapply (lift_gret_compose t fai ret
          (I //\\ ALin t (Semantics.ls_linr fai ret)) I);
          [|exact Hcompose].
        intros out [pre [[HI Hlin] Hgret]].
        unfold Gret, LiftRelation_π in Hgret.
        destruct Hgret as [Hσ [Hρ [Hfind Hπ]]].
        unfold I in *. intros l r Hout.
        etransitivity; [symmetry; exact Hρ|].
        apply (HI l r). etransitivity; [exact Hσ|exact Hout].
      - intros ret σ0 Δ0 Hpost ρ0 π0 Hposs.
        eapply (lift_post_lin
          (I //\\ ALin t (Semantics.ls_linr fai ret)) t
          (Semantics.ls_linr fai ret)); [|exact Hpost|exact Hposs].
        unfold ALin. intros x [_ Hlin]. exact Hlin.
      - unfold fai_impl.
        (* acq *)
        singleton_vis_safe
          (I //\\ ALin t (Semantics.ls_inv fai))
          (fun _ => I //\\ ALin t (Semantics.ls_inv fai) //\\ OwnedBy t)
          using stableDB;
          [solve_no_error| | |intros ret_acq].
        (* inv *)
        {
          pupdate_intros_atomic.
          pupdate_finish; split.
          - unfold I, ALin in *.
            destruct Hpre.
            split; simpl in *; auto.
            intros l r Heq. inversion Heq; subst.
            apply (H _ _ eq_refl).
          - split; simpl; auto.
            right. unfold G_id. simpl; auto.
        }
        (* res *)
        {
          pupdate_intros_atomic.
          pupdate_finish; split.
          - unfold I, ALin, OwnedBy in *.
            destruct Hpre as [HI Hlin].
            split.
            + simpl in *. intros l r Heq.
              change (pair (Idle (Locked t)) s2 = pair l r) in Heq.
              injection Heq; intros; subst.
              apply (HI _ _ eq_refl).
            + split.
              * simpl in *. exact Hlin.
              * simpl. reflexivity.
          - split; simpl; auto.
            left; left. unfold G_lock, NotOwned, OwnedBy; simpl; auto.
        }

        (* get *)
        singleton_vis_safe
          (I //\\ ALin t (Semantics.ls_inv fai) //\\ OwnedBy t)
          (fun c => I //\\ ALin t (Semantics.ls_inv fai) //\\
            (OwnedBy t //\\ RegVal (Idle c)))
          using stableDB;
          [solve_no_error| | |intros c].
        (* inv *)
        {
          pupdate_intros_atomic.
          pupdate_finish; split.
          - destruct Hpre as [HI [Hlin Howned]].
            split; [|split; auto].
            unfold I in *. simpl in *.
            inversion 1; intros; subst; simpl.
            apply (HI _ _ eq_refl).
          - destruct Hpre as [_ [_ Howned]].
            split.
            + right. unfold G_id. split; simpl; auto.
              intros Hnot. exfalso. apply Hnot. exact Howned.
            + simpl; intros; reflexivity.
        }
        (* res *)
        {
          pupdate_intros_atomic.
          pupdate_finish; split.
          - destruct Hpre as [HI [Hlin Howned]].
            split.
            + unfold I in *. simpl in *.
              inversion 1; intros; subst; simpl.
              apply (HI _ _ eq_refl).
            + split; [exact Hlin|]. split; [exact Howned|].
              unfold RegVal; simpl; auto.
          - split; auto. right. split; auto.
            destruct Hpre as [? [? ?]]; congruence.
        }

        (* set *)
        singleton_vis_safe
          ((I //\\ ALin t (Semantics.ls_inv fai)) //\\
            (OwnedBy t //\\ RegVal (Pending c t (set (S c)))))
          (fun _ =>
            (I //\\ ALin t (Semantics.ls_linr fai c)) //\\ OwnedBy t)
          using stableDB;
          [| | |intros ret_set].
        (* safe *)
        {
          do 2 apply ConjRightImpl.
          intros x [Howned Hreg] Herr.
          unfold RegVal in Hreg.
          destruct (σ x) as [lock reg] eqn:Hσ.
          simpl in Hreg, Herr.
          inversion Herr; subst. congruence.
        }
        (* inv *)
        {
          pupdate_intros_atomic.
          pupdate_finish; split.
          - destruct Hpre as [HI [Hlin [Howned Hreg]]].
            split.
            + split.
              * unfold I in *; simpl in *.
                inversion 1; intros; subst. apply (HI _ _ eq_refl).
              * exact Hlin.
            + split; [exact Howned|].
              inversion Hreg; subst. unfold RegVal in *; simpl in *; auto.
          - destruct Hpre as [_ [_ [Howned _]]].
            split.
            + right. unfold G_id. split; simpl; auto.
              intros Hnot. exfalso. apply Hnot. exact Howned.
            + simpl; intros; reflexivity.
        }
        (* res: this is the linearization point *)
        {
          pupdate_intros_atomic.
          destruct Hpre as [[? ?] [? ?]].
          inversion H2; subst.
          specialize (H _ _ eq_refl). simpl in H; subst.
          inversion H0; subst.

          pupdate_start.
          pupdate_forward t (InvEv fai).
          pupdate_forward t (ResEv fai c).
          pupdate_finish.

          split.
          - unfold I, ALin, RegVal.
            split; auto. split.
            + simpl; inversion 1; subst. auto.
            + simpl. rewrite PositiveMap.gss. auto.
          - split.
            + right. split; auto. congruence.
            + simpl; intros. do 2 (rewrite PositiveMap.gso; auto).
        }

        (* rel *)
        singleton_vis_safe
          ((I //\\ ALin t (Semantics.ls_linr fai c)) //\\ OwnedBy t)
          (fun _ => I //\\ ALin t (Semantics.ls_linr fai c))
          using stableDB;
          [| | |intros ret_rel].
        (* safe *)
        {
          apply ConjRightImpl.
          intros ? ? ?. inversion H; subst.
          destruct σ. inversion H0; subst.
          inversion Herror; subst.
          - simpl in *; congruence.
          - inversion H2; congruence.
        }
        (* inv *)
        {
          pupdate_intros_atomic.
          pupdate_finish; split.
          - destruct Hpre as [[? ?] ?].
            do 2 (split; auto).
            unfold I in *; simpl in *.
            inversion 1; intros; subst. apply (H _ _ eq_refl).
          - split; auto. right. split; auto.
        }
        (* res *)
        {
          pupdate_intros_atomic.
          destruct Hpre as [[? ?] ?].
          pupdate_finish; split.
          - split; auto.
            unfold I in *; simpl in *.
            inversion 1; intros; subst. apply (H _ _ eq_refl).
          - split; auto. left; right.
            do 2 (split; auto). unfold NotOwned. auto.
        }

        singleton_ret_safe using stableDB.
    }
    (* initial singleton *)
    {
      apply lift_initial.
      unfold I. simpl; inversion 1; subst.
      intros; subst; auto.
    }
  Defined.

  Print Assumptions Mfai.
End FAISetImpl.
