Require Import FMapPositive.
Require Import Coq.PArith.PArith.
Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Relation_Operators Operators_Properties.
Require Import Classical.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import Logics.
Require Import SeparationAlgebra.
Require Import LTSLocality.
Require Import Assertion.
Require Import RGISimulationSet.
Require Import RGILogicSet.

(** Completeness of the set-based program logic ([RGILogicSet]) with
    respect to the method simulation ([RGISimulationSet.MethodSimulation]):
    whenever a method body is method-simulated from every state an
    invocation can reach, the logic proves it, with semantic assertions.

    The assertions are the natural ones: [SemP f p b] holds at a proof
    state when the simulation holds there for [p] (up to leading [Tau]s,
    which the logic's [CoreTau] consumes without an abstract update), and
    [SemQ f ret] is the rank-zero simulation of [Ret ret] whose return
    clause has fired. The abstract-update chains of the simulation are
    collapsed into a single [UpdateCons], which is why [G] is assumed
    transitive (and reflexive, for empty chains).

    Erroneous states need care: the simulation makes no demands once a
    possibility can error, while [CoreVis] demands a possibility update for
    every state between an invocation and its response. The theorem
    therefore assumes that erroneous configurations are frozen: [G] lets
    the thread's own underlay steps leave an erroneous [Δ] untouched, [R] never makes an
    erroneous [Δ] sound again, and [I] accepts erroneous states. These hold
    for the relations extracted from a thread-pool simulation, where the
    abstract configuration is never updated after it has become erroneous.
    Finally [R] must not disturb the invoking thread's own entry once it is
    linearized ([HRlin]), which every rely built from other threads'
    guarantees satisfies. *)
Module RGILogicComplete.
  Import Reg LinCCALBase LTSSpec Semantics AssertionsSet Lang.
  Import RGISimulationSet.RGISimulation.
  Import RGILogicSet.RGILogic.
  Open Scope assertion_scope.

  Section Completeness.
    Context {E F : Op.t} {VE : @LTS E} {VF : @LTS F}.
    Context (M : ModuleImpl E F).
    Context (R G : @RGRelation _ _ VE VF).
    Context (I : @Assertion (@ProofState _ _ VE VF)).
    Context (t : tid).

    Hypothesis HGrefl : forall s, G s s.
    Hypothesis HGtrans : forall s1 s2 s3, G s1 s2 -> G s2 s3 -> G s1 s3.
    Hypothesis HGerr : forall σ1 Δ1 σ2 ev, te_tid ev = t -> Step VE ev σ1 σ2 ->
      APError (σ1, Δ1) -> G (σ1, Δ1) (σ2, Δ1).
    Hypothesis HRerr : forall s s', R s s' -> APError s -> APError s'.
    Hypothesis HIerr : ⊨ APError ==>> I.
    Hypothesis HRlin : forall s s' f r, R s s' -> ALin t (ls_linr f r) s -> ALin t (ls_linr f r) s'.

    (** * Semantic assertions *)

    Fixpoint taus {A} (j : nat) (p : Prog E A) : Prog E A :=
      match j with O => p | S j' => Tau (taus j' p) end.

    Lemma taus_tau {A} j (p : Prog E A) : taus j (Tau p) = Tau (taus j p).
    Proof. induction j; simpl; [reflexivity | rewrite IHj; reflexivity]. Qed.

    Definition SemP f (p : Prog E (Sig.ar f)) (b : option (Sig.op E)) : Assertion :=
      fun s => exists j, MethodSimulation R G I t f (σ s) (taus j p) b (Δ s).

    Definition SemCore f (p : Prog E (Sig.ar f)) (b : option (Sig.op E)) : Assertion :=
      fun s => MethodSimulationRanked R G I t f 0 (σ s) p b (Δ s).

    Definition SemQ f (ret : Sig.ar f) : Assertion :=
      fun s => SemCore f (Ret ret) None s /\ ALin t (ls_linr f ret) s /\
               I (σ s, ac_res (Δ s) t).

    (** * Facts about the simulation *)

    Lemma core_I f X σ1 p b Δ1 :
      MethodCore R G I t f X σ1 p b Δ1 -> I (σ1, Δ1).
    Proof. intros Hcore. destruct Hcore; assumption. Qed.

    Lemma msim_I f n σ1 p b Δ1 :
      MethodSimulationRanked R G I t f n σ1 p b Δ1 -> I (σ1, Δ1).
    Proof.
      intros Hsim. destruct Hsim as [n σ1 p b Δ1 ΔC Hchain Hcore Hstab].
      inversion Hchain; subst.
      - eapply core_I; eauto.
      - assumption.
    Qed.

    Lemma chain_reach (σ1 : State VE) n (Δ1 Δ2 : AbstractConfig VF) :
      MethodUpdateSteps G I σ1 n Δ1 Δ2 ->
      (Δ2 ⊆ ac_steps Δ1)%AbstractConfig /\ G (σ1, Δ1) (σ1, Δ2).
    Proof.
      intros Hchain. induction Hchain as [Δ1 | n Δ1 Δ' Δ2 Hsub HG HI Hchain IH].
      - split; [apply ac_steps_refl | apply HGrefl].
      - destruct IH as [IHsub IHG]. split.
        + eapply ac_steps_subset_trans; eauto.
        + eapply HGtrans; eauto.
    Qed.

    Lemma rank0_core f σ1 p b Δ1 :
      MethodSimulationRanked R G I t f 0 σ1 p b Δ1 ->
      MethodCore R G I t f (MethodSimulationRanked R G I t f) σ1 p b Δ1.
    Proof.
      intros Hsim. inversion Hsim as [n σ0 p0 b0 Δ0 ΔC Hchain Hcore Hstab]; subst.
      inversion Hchain; subst; exact Hcore.
    Qed.

    Lemma apperror_state (σ1 σ2 : State VE) (Δ1 : AbstractConfig VF) : APError (σ1, Δ1) -> APError (σ2, Δ1).
    Proof.
      intros Herr. inversion Herr as [s ρ π Hposs Hsteps]; subst. simpl in *.
      eapply APErrorSome with (ρ := ρ) (π := π); simpl; assumption.
    Qed.

    Lemma apperror_steps (σ1 : State VE) (Δ1 Δ2 : AbstractConfig VF) :
      (Δ2 ⊆ ac_steps Δ1)%AbstractConfig -> APError (σ1, Δ2) -> APError (σ1, Δ1).
    Proof.
      intros Hsub Herr. inversion Herr as [s ρ π Hposs Hsteps]; subst. simpl in *.
      apply Hsub in Hposs. inversion Hposs as [ρ0 π0 ρ' π' Hposs0 Hsteps0]; subst.
      eapply APErrorSome with (ρ := ρ0) (π := π0); simpl; [exact Hposs0 |].
      eapply rt_trans; eauto.
    Qed.

    Lemma core_error_apperror f X (σ1 : State VE) p b (Δ1 : AbstractConfig VF) ρ π :
      Δ1 ρ π -> poss_steps (PossOk ρ π) PossError ->
      MethodCore R G I t f X σ1 p b Δ1 -> APError (σ1, Δ1).
    Proof.
      intros Hposs Hsteps _. eapply APErrorSome with (ρ := ρ) (π := π); simpl; assumption.
    Qed.

    (* A non-erroneous core is a rank-zero simulation: its own stability
       clause already re-establishes rank zero after rely moves. *)
    Lemma core_rank0 f σ1 p b Δ1 :
      MethodCore R G I t f (MethodSimulationRanked R G I t f) σ1 p b Δ1 ->
      ~ APError (σ1, Δ1) ->
      MethodSimulationRanked R G I t f 0 σ1 p b Δ1.
    Proof.
      intros Hcore Hnoerr.
      eapply MSimRoll with (DeltaCore := Δ1); [constructor | exact Hcore |].
      intros σ' Δ' HR HI'. exists O. split; [reflexivity |].
      destruct Hcore as [ρ π HI Hposs Herr | Hu Hret Htau HIc Hstab Hnoerror].
      - exfalso. apply Hnoerr. eapply APErrorSome with (ρ := ρ) (π := π); simpl; assumption.
      - apply Hstab; assumption.
    Qed.

    (* Running the simulation of [taus j p] up to a core for [p]: a single
       guaranteed, speculative update, after which either some possibility
       errors or [p] is simulated at rank zero. *)
    Lemma msim_reach f j : forall p b σ1 Δ1,
      MethodSimulation R G I t f σ1 (taus j p) b Δ1 ->
      exists Δc, (Δc ⊆ ac_steps Δ1)%AbstractConfig /\ G (σ1, Δ1) (σ1, Δc) /\
        (APError (σ1, Δc) \/ MethodSimulationRanked R G I t f 0 σ1 p b Δc).
    Proof.
      induction j as [| j IH]; intros p b σ1 Δ1 [n Hsim]; simpl in Hsim;
        inversion Hsim as [n0 σ0 p0 b0 Δ0 ΔC Hchain Hcore Hstab]; subst;
        destruct (chain_reach _ _ _ _ Hchain) as [Hsub HG].
      - exists ΔC. split; [exact Hsub |]. split; [exact HG |].
        destruct (classic (APError (σ1, ΔC))) as [Herr | Hnoerr]; [left; exact Herr |].
        right. apply core_rank0; assumption.
      - destruct (classic (APError (σ1, ΔC))) as [Herr | Hnoerr].
        { exists ΔC. split; [exact Hsub |]. split; [exact HG |]. left. exact Herr. }
        destruct Hcore as [ρ π HI Hposs Herr | Hu Hret Htau HIc Hstabc Hnoerror].
        { exfalso. apply Hnoerr. eapply APErrorSome with (ρ := ρ) (π := π); simpl; assumption. }
        destruct (Htau (taus j p) b) as [n1 Hsim1]; [constructor |].
        destruct (IH p b σ1 ΔC (ex_intro _ n1 Hsim1)) as [Δc [Hsubc [HGc Hres]]].
        exists Δc. split; [eapply ac_steps_subset_trans; eauto |].
        split; [eapply HGtrans; eauto | exact Hres].
    Qed.

    (* Steps of other threads never touch an entry that is already
       linearized, so an error path survives removing that entry. *)
    Lemma poss_error_mask_gen : forall (p q : @Poss F VF),
      clos_refl_trans_1n _ poss_step p q -> q = PossError ->
      forall ρ π f r (π2 : tmap (@LinState F)),
        p = PossOk ρ π ->
        TMap.find t π = Some (ls_linr f r) ->
        (forall t', t' <> t -> TMap.find t' π2 = TMap.find t' π) ->
        poss_steps (PossOk ρ π2) PossError.
    Proof.
      intros p q H. induction H as [| x y z Hxy Hyz IH];
        intros Hq ρ π f r π2 Hp Hlin Hagree; subst.
      - discriminate.
      - inversion Hxy as [t0 f0 s1 s2 π0 Hstep Hlin0 | t0 f0 ret s1 s2 π0 Hstep Hlin0
                         | t0 f0 s1 π0 Herr Hlin0]; subst.
        + assert (Hne : t0 <> t) by (intros ->; rewrite Hlin in Hlin0; discriminate).
          eapply rt_trans; [apply rt_step; eapply ps_inv; [exact Hstep | rewrite Hagree; auto] |].
          eapply IH; [reflexivity | reflexivity | rewrite TMap.gso; auto; exact Hlin |].
          intros t' Hne'. destruct (Pos.eq_dec t' t0); subst.
          * rewrite !TMap.gss. reflexivity.
          * rewrite !TMap.gso; auto.
        + assert (Hne : t0 <> t) by (intros ->; rewrite Hlin in Hlin0; discriminate).
          eapply rt_trans; [apply rt_step; eapply ps_ret; [exact Hstep | rewrite Hagree; auto] |].
          eapply IH; [reflexivity | reflexivity | rewrite TMap.gso; auto; exact Hlin |].
          intros t' Hne'. destruct (Pos.eq_dec t' t0); subst.
          * rewrite !TMap.gss. reflexivity.
          * rewrite !TMap.gso; auto.
        + assert (Hne : t0 <> t) by (intros ->; rewrite Hlin in Hlin0; discriminate).
          apply rt_step. eapply ps_error; [exact Herr | rewrite Hagree; auto].
    Qed.

    Lemma apperror_res (σ1 : State VE) (Δ1 : AbstractConfig VF) f r :
      APError (σ1, Δ1) -> ALin t (ls_linr f r) (σ1, Δ1) -> APError (σ1, ac_res Δ1 t).
    Proof.
      intros Herr Hlin. inversion Herr as [s ρ π Hposs Hsteps]; subst. simpl in *.
      eapply APErrorSome with (ρ := ρ) (π := TMap.remove t π); simpl.
      - constructor. exact Hposs.
      - eapply poss_error_mask_gen; [apply clos_rt_rt1n; exact Hsteps | reflexivity | reflexivity
                                    | exact (Hlin _ _ Hposs) |].
        intros t' Hne. rewrite TMap.gro; auto.
    Qed.

    (** * The semantic assertions behave *)

    Lemma semP_I f p b : ⊨ SemP f p b ==>> I.
    Proof.
      intros s [j [n Hsim]]. destruct s as [σ1 Δ1]. simpl in *.
      eapply msim_I; eauto.
    Qed.

    Lemma semCore_I f p b : ⊨ SemCore f p b ==>> I.
    Proof.
      intros s Hsim. destruct s as [σ1 Δ1]. simpl in *.
      eapply msim_I; eauto.
    Qed.

    Lemma semP_stable f p b : Stable R I (SemP f p b).
    Proof.
      intros s [[s' [[j [n Hsim]] HR]] HI]. destruct s as [σ1 Δ1]. destruct s' as [σ0 Δ0].
      simpl in *. exists j.
      destruct Hsim as [n σ0 p0 b0 Δ0 ΔC Hchain Hcore Hstab].
      destruct (Hstab σ1 Δ1 HR HI) as [n' [_ Hsim']]. exists n'. exact Hsim'.
    Qed.

    Lemma semCore_stable f p b : Stable R I (SemCore f p b).
    Proof.
      intros s [[s' [Hsim HR]] HI]. destruct s as [σ1 Δ1]. destruct s' as [σ0 Δ0].
      simpl in *.
      inversion Hsim as [n σ0' p0 b0 Δ0' ΔC Hchain Hcore Hstab]; subst.
      destruct (Hstab σ1 Δ1 HR HI) as [n' [Hle Hsim']].
      inversion Hle; subst. exact Hsim'.
    Qed.

    Lemma apperror_stable : Stable R I APError.
    Proof.
      intros s [[s' [Herr HR]] HI]. eapply HRerr; eauto.
    Qed.

    Lemma disj_I (P : Assertion) : (⊨ P ==>> I) -> ⊨ P \\// APError ==>> I.
    Proof. intros HP s [H | H]; [apply HP; exact H | apply HIerr; exact H]. Qed.

    Lemma disj_stable (P : Assertion) : Stable R I P -> Stable R I (P \\// APError).
    Proof.
      intros HP s [[s' [[H | H] HR]] HI].
      - left. apply HP. split; [exists s'; split; assumption | exact HI].
      - right. eapply HRerr; eauto.
    Qed.

    Lemma semQ_I f ret : ⊨ SemQ f ret ==>> I.
    Proof. intros s [Hcore _]. eapply semCore_I; eauto. Qed.

    Lemma semQ_stable f ret : Stable R I (SemQ f ret).
    Proof.
      intros s [[s' [[Hcore [Hlin HIres]] HR]] HI].
      assert (Hcore' : SemCore f (Ret ret) None s)
        by (apply (semCore_stable f (Ret ret) None); split; [exists s'; split; assumption | exact HI]).
      assert (Hlin' : ALin t (ls_linr f ret) s) by (eapply HRlin; [exact HR | exact Hlin]).
      split; [exact Hcore' |]. split; [exact Hlin' |].
      destruct s as [σ1 Δ1]. simpl in *.
      apply rank0_core in Hcore'.
      destruct Hcore' as [ρ π HI0 Hposs Herr | Hu Hret Htau HIc Hstab Hnoerr].
      - apply HIerr. apply apperror_res with (f := f) (r := ret); [| exact Hlin'].
        eapply APErrorSome with (ρ := ρ) (π := π); simpl; assumption.
      - destruct (Hret ret (conj eq_refl eq_refl)) as [_ [HIres' _]]. exact HIres'.
    Qed.

    (** * The coinductive view *)

    Definition XP f (P : Assertion) (p : Prog E (Sig.ar f)) (Q : Sig.ar f -> Assertion) : Prop :=
      (⊨ P ==>> SemP f p None \\// APError) /\ Q = SemQ f.

    Lemma XP_view f : forall P p Q, XP f P p Q -> HTripleView R G I t (XP f) P p Q.
    Proof.
      intros P p Q [HP HQ]. subst Q.
      exists (SemCore f p None \\// APError). split.
      - (* collapse the simulation's update chain into one update *)
        eapply UpdateCons with (P := SemP f p None) (P' := SemCore f p None \\// APError).
        + exact HP.
        + apply disj_I. apply semCore_I.
        + apply disj_stable. apply semCore_stable.
        + intros σ1 Δ1 [j Hsim].
          destruct (msim_reach f j p None σ1 Δ1 Hsim) as [Δc [Hsub [HG Hres]]].
          exists Δc. split; [exact Hsub |]. split; [| exact HG].
          destruct Hres as [Herr | Hsim0]; [right; exact Herr | left; exact Hsim0].
        + constructor.
      - destruct p as [m k | a | p'].
        + (* Vis: the logic's invocation/response rule *)
          eapply CoreVis with
            (P := fun s => SemCore f (Vis m k) None s /\ ~ APError s)
            (P' := SemP f (Vis m k) (Some m))
            (Q' := fun ret => SemP f (k ret) None \\// APError).
          * intros s [Hcore | Herr]; [| right; exact Herr].
            destruct (classic (APError s)) as [Herr | Hnoerr]; [right; exact Herr |].
            left. split; assumption.
          * intros s [Hcore Hnoerr] Herror. destruct s as [σ1 Δ1]. simpl in *.
            apply rank0_core in Hcore.
            destruct Hcore as [ρ π HI0 Hposs Herr | Hu Hret Htau HIc Hstab Hnoerror].
            { apply Hnoerr. eapply APErrorSome with (ρ := ρ) (π := π); simpl; assumption. }
            apply (Hnoerror (InvEv m)). constructor. exact Herror.
          * apply semP_I.
          * intros a. apply disj_I. apply semP_I.
          * apply semP_stable.
          * intros a. apply disj_stable. apply semP_stable.
          * intros σ1 Δ1 [Hcore Hnoerr] σ' Hstep. simpl in *.
            apply rank0_core in Hcore.
            destruct Hcore as [ρ π HI0 Hposs Herr | Hu Hret Htau HIc Hstab Hnoerror].
            { exfalso. apply Hnoerr. eapply APErrorSome with (ρ := ρ) (π := π); simpl; assumption. }
            destruct (Hu (InvEv m) σ' (Vis m k) (Some m)) as [Δ' [Hsub [HG [n Hsim']]]].
            { constructor. exact Hstep. }
            exists Δ'. split; [exact Hsub |]. split; [| exact HG].
            exists O, n. exact Hsim'.
          * intros ret σ1 Δ1 HP' σ' Hstep.
            destruct (classic (APError (σ1, Δ1))) as [Herr | Hnoerr].
            { exists Δ1. split; [apply ac_steps_refl |]. split.
              - right. eapply apperror_state. exact Herr.
              - exact (HGerr _ _ _ (Build_ThreadEvent t (ResEv m ret)) eq_refl Hstep Herr). }
            destruct HP' as [j Hsim].
            destruct (msim_reach f j (Vis m k) (Some m) σ1 Δ1 Hsim) as [Δc [Hsub [HG Hres]]].
            destruct Hres as [Herrc | Hsim0].
            { exfalso. apply Hnoerr. eapply apperror_steps; eauto. }
            apply rank0_core in Hsim0.
            destruct Hsim0 as [ρ π HI0 Hposs Herr | Hu Hret Htau HIc Hstab Hnoerror].
            { exfalso. apply Hnoerr. eapply apperror_steps; [exact Hsub |].
              eapply APErrorSome with (ρ := ρ) (π := π); simpl; assumption. }
            destruct (Hu (ResEv m ret) σ' (k ret) None) as [Δ'' [Hsub' [HG' [n Hsim']]]].
            { constructor. exact Hstep. }
            exists Δ''. split; [eapply ac_steps_subset_trans; eauto |].
            split; [left; exists O, n; exact Hsim' | eapply HGtrans; eauto].
          * intros ret. split; [intros s H; exact H | reflexivity].
        + (* Ret: the return clause has fired *)
          eapply CoreRet with (P := SemQ f a).
          * intros s [Hcore | Herr]; [| right; exact Herr].
            destruct (classic (APError s)) as [Herr | Hnoerr]; [right; exact Herr |].
            left. split; [exact Hcore |].
            destruct s as [σ1 Δ1]. simpl in *.
            apply rank0_core in Hcore.
            destruct Hcore as [ρ π HI0 Hposs Herr | Hu Hret Htau HIc Hstab Hnoerror].
            { exfalso. apply Hnoerr. eapply APErrorSome with (ρ := ρ) (π := π); simpl; assumption. }
            destruct (Hret a (conj eq_refl eq_refl)) as [_ [HIres Hlin]].
            split; [exact Hlin | exact HIres].
          * intros s H. exact H.
          * apply semQ_I.
          * apply semQ_stable.
        + (* Tau: consumed by the simulation's silent step *)
          apply CoreTau. split; [| reflexivity].
          intros s [Hcore | Herr]; [| right; exact Herr].
          destruct s as [σ1 Δ1]. simpl in *.
          apply rank0_core in Hcore.
          destruct Hcore as [ρ π HI0 Hposs Herr | Hu Hret Htau HIc Hstab Hnoerror].
          { right. eapply APErrorSome with (ρ := ρ) (π := π); simpl; assumption. }
          left. destruct (Htau p' None) as [n Hsim']; [constructor |].
          exists O, n. exact Hsim'.
    Qed.

    Theorem msim_provable f (p : Prog E (Sig.ar f)) :
      [VE, VF, R, G, I, t] ⊢ {{ SemP f p None }} p {{ SemQ f }}.
    Proof.
      eapply HTripleProvable_coinduction with (X := XP f); [apply XP_view |].
      split; [intros s H; left; exact H | reflexivity].
    Qed.

    (* Completeness of the logic with respect to the method simulation:
       the method's semantic precondition is provable, with the semantic
       postcondition, whenever every invocation state is simulated. *)
    Theorem msim_MethodProvable f
        (Hmsim : forall s, (Ginv t f ⊚ I) s ->
          MethodSimulation R G I t f (σ s) (M f t) None (Δ s)) :
      MethodProvable VE VF M R G I t f (SemP f (M f t) None) (SemQ f).
    Proof.
      constructor.
      - intros s Hinv. exists O. apply Hmsim. exact Hinv.
      - apply semP_I.
      - apply semP_stable.
      - intros ret s [s' [[Hcore [Hlin HIres]] [Hσ HΔ]]].
        destruct HΔ as [_ HΔ]. apply AbstractConfig_ext in HΔ.
        destruct s as [σ1 Δ1]. destruct s' as [σ0 Δ0]. simpl in *. subst. exact HIres.
      - intros ret σ1 Δ1 [_ [Hlin _]]. exact Hlin.
      - apply msim_provable.
    Qed.

  End Completeness.
End RGILogicComplete.
