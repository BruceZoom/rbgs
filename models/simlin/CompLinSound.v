Require Import Coq.Lists.List.
Require Import Coq.PArith.PArith.
Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.Program.Equality.

Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import TPSimulationSet.
Require Import CompLin.

(** Soundness of [TPSimulationSet.cal] (Definition 5.2, the Threadpool
    Simulation) with respect to [CompLin.CompLin] (Definition 4.1,
    Compositional Linearizability): §5.1's easy direction of Lemma 5.3.

    The speculative [Poss]/[AbstractConfig] machinery from [Semantics] tracks
    a *set* of possibilities without ever committing to one, which is
    exactly what makes it well suited to the coinductive unfolding of
    [TPSimulation]. [CompLin.CompLin], on the other hand, demands a single,
    literal execution of the identity implementation [CompLin.idImpl] via
    the generic thread-pool semantics. Bridging the two therefore takes two
    separate steps:

    - Layer 1 ([TPSimulation_abs_reaches]) unfolds [TPSimulation] alongside
      the concrete trace and produces a purely set-level judgement
      ([abs_reaches]) that some final [AbstractConfig] is reached. This
      mirrors the [ac_inv]/[ac_res]/[ac_steps] structure already used by
      [TPSimulation] itself.
    - Layer 2 ([abs_reaches_reify]) turns that set-level judgement into a
      single concrete execution of [idImpl], by picking one possibility and
      replaying, backwards, the steps that justify each set-level
      transition. *)
Module CompLinSound.
  Import Reg.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import Semantics.
  Import TPSimulationSet.TPSimulation.
  Import CompLin.CompLin.

  Section Adequacy.
    Context {E F : Op.t}.
    Context {VE : @LTS E}.
    Context {VF : @LTS F}.
    Context (M : ModuleImpl E F).

    (* Every possibility tracked by an [AbstractConfig] paired with a
       concrete pool [c] via [TPSimulation] has a linearization map whose
       domain (pending/started-but-not-yet-externally-returned overlay
       operations) exactly matches the domain of [c]. This is what lets us
       reuse the concrete side's [invstep]/[retstep] domain preconditions
       (e.g. "thread not already active") for the shadow [idImpl]
       execution. *)
    Definition dom_match (c : @ThreadPoolState E F) (Delta : AbstractConfig VF) : Prop :=
      forall rho pi, Delta rho pi ->
        forall t, TMap.find t c = None <-> TMap.find t pi = None.

    Lemma dom_match_init (rho0 : State VF) :
      dom_match (TMap.empty _) (ac_init rho0).
    Proof.
      intros rho pi Hposs t. inversion Hposs; subst.
      rewrite !TMap.gempty. tauto.
    Qed.

    Lemma dom_match_ac_inv c Delta t f ts :
      dom_match c Delta ->
      dom_match (TMap.add t ts c) (ac_inv Delta t f).
    Proof.
      intros Hdm rho pi Hposs t'.
      inversion Hposs as [rho0 pi0 Hposs0]; subst.
      destruct (Pos.eq_dec t' t); subst.
      - rewrite !TMap.gss. split; intro Hc; discriminate Hc.
      - rewrite !TMap.gso; auto. exact (Hdm _ _ Hposs0 t').
    Qed.

    Lemma dom_match_ac_res c Delta t :
      dom_match c Delta ->
      dom_match (TMap.remove t c) (ac_res Delta t).
    Proof.
      intros Hdm rho pi Hposs t'.
      inversion Hposs as [rho0 pi0 Hposs0]; subst.
      destruct (Pos.eq_dec t' t); subst.
      - rewrite !TMap.grs. tauto.
      - rewrite !TMap.gro; auto. exact (Hdm _ _ Hposs0 t').
    Qed.

    Lemma dom_match_ac_steps c Delta Delta' :
      dom_match c Delta ->
      (Delta' ⊆ ac_steps Delta)%AbstractConfig ->
      dom_match c Delta'.
    Proof.
      intros Hdm Hsub rho pi Hposs t.
      apply Hsub in Hposs. inversion Hposs as [rho0 pi0 rho' pi' Hposs0 Hpstep]; subst.
      pose proof (poss_steps_domexact _ _ _ _ Hpstep) as Hde.
      specialize (Hdm _ _ Hposs0 t). specialize (Hde t). tauto.
    Qed.

    (* Library ([ustep]) and silent ([taustep]) steps only ever update the
       value stored at an already-active thread, never the set of active
       threads, so they preserve the domain of the concrete pool. *)
    Lemma ustep_dom_preserved :
      forall ev (sigma : State VE) (c : @ThreadPoolState E F) sigma' c',
        ustep ev sigma c sigma' c' ->
        forall t, TMap.find t c = None <-> TMap.find t c' = None.
    Proof.
      intros ev sigma c sigma' c' Hstep t.
      inversion Hstep as [f0 ts1 ts2 Hfind Hstep0 Hupd]; subst.
      destruct (Pos.eq_dec t (te_tid ev)); subst.
      - rewrite Hfind, TMap.gss. split; discriminate.
      - rewrite TMap.gso; auto. tauto.
    Qed.

    Lemma taustep_dom_preserved :
      forall t (c : @ThreadPoolState E F) c', taustep t c c' ->
        forall t', TMap.find t' c = None <-> TMap.find t' c' = None.
    Proof.
      intros t c c' Hstep t'.
      inversion Hstep as [ts1 ts2 Hfind Hstep0 Hupd]; subst.
      destruct (Pos.eq_dec t' t); subst.
      - rewrite Hfind, TMap.gss. split; discriminate.
      - rewrite TMap.gso; auto. tauto.
    Qed.

    (* Every [LinState] entry of a possibility corresponds to the thread
       state that would be reached by running the identity implementation
       [CompLin.idImpl] on the same operation. *)
    Definition linstate_to_ts (ls : @LinState F) : @ThreadState F F :=
      match ls with
      | ls_inv f => Build_ThreadState f (Vis f (fun v => Ret v)) None
      | ls_lini f => Build_ThreadState f (Vis f (fun v => Ret v)) (Some f)
      | ls_linr f r => Build_ThreadState f (Ret r) None
      end.

    Definition pool_matches_lin (cabs : @ThreadPoolState F F) (pi : tmap (@LinState F)) : Prop :=
      forall t, TMap.find t cabs = option_map linstate_to_ts (TMap.find t pi).

    Lemma pool_matches_lin_empty : pool_matches_lin (TMap.empty _) (TMap.empty _).
    Proof.
      intros t. rewrite !TMap.gempty. reflexivity.
    Qed.

    (* A single [poss_step] (a linearization-point step of the speculative
       machinery) corresponds to a single [ustep] (a library-visible,
       trace-silent step) of [idImpl] run over [VF]. *)
    Lemma poss_step_shadow :
      forall rho pi rho' pi' cabs,
        poss_step (PossOk rho pi) (PossOk rho' pi') ->
        pool_matches_lin cabs pi ->
        exists ev cabs',
          @ustep F F VF ev rho cabs rho' cabs' /\ pool_matches_lin cabs' pi'.
    Proof.
      intros rho pi rho' pi' cabs Hstep Hmatch.
      dependent destruction Hstep.
      - (* ps_inv *)
        pose proof (Hmatch t0) as Hm. rewrite Hlin in Hm. simpl in Hm.
        eexists (Build_ThreadEvent t0 (InvEv f)),
          (TMap.add t0 (Build_ThreadState f (Vis f (fun v => Ret v)) (Some f)) cabs).
        split.
        + econstructor; eauto. econstructor. exact Hstep.
        + intros t'. destruct (Pos.eq_dec t' t0); subst.
          * rewrite !TMap.gss. reflexivity.
          * rewrite !TMap.gso; auto.
      - (* ps_ret *)
        pose proof (Hmatch t0) as Hm. rewrite Hlin in Hm. simpl in Hm.
        eexists (Build_ThreadEvent t0 (ResEv f ret)),
          (TMap.add t0 (Build_ThreadState f (Ret ret) None) cabs).
        split.
        + econstructor; eauto. econstructor. exact Hstep.
        + intros t'. destruct (Pos.eq_dec t' t0); subst.
          * rewrite !TMap.gss. reflexivity.
          * rewrite !TMap.gso; auto.
    Qed.

    Lemma poss_steps_from_error : forall (p q : @Poss F VF), poss_steps p q -> p = PossError -> q = PossError.
    Proof.
      intros p q Hpss.
      induction Hpss; intros Heq; subst.
      - inversion H.
      - reflexivity.
      - specialize (IHHpss1 eq_refl). apply IHHpss2. exact IHHpss1.
    Qed.

    (* A whole chain of [poss_step]s (never erroring) replays as a matching,
       trace-preserving chain of [ustep]s of [idImpl] over [VF]. *)
    Lemma poss_steps_shadow_gen :
      forall rho' pi' p1,
        poss_steps p1 (PossOk rho' pi') ->
        match p1 with
        | PossOk rho pi =>
            forall cabs s0, pool_matches_lin cabs pi ->
              exists cabs', pool_matches_lin cabs' pi' /\
                @trace_steps F F VF idImpl (mkTraceConfig s0 rho cabs) (mkTraceConfig s0 rho' cabs')
        | PossError => True
        end.
    Proof.
      intros rho' pi' p1 Hpss.
      unfold poss_steps in Hpss.
      refine (clos_refl_trans_ind_right _ poss_step
        (fun p1 => match p1 with
         | PossOk rho pi =>
             forall cabs s0, pool_matches_lin cabs pi ->
               exists cabs', pool_matches_lin cabs' pi' /\
                 @trace_steps F F VF idImpl (mkTraceConfig s0 rho cabs) (mkTraceConfig s0 rho' cabs')
         | PossError => True
         end)
        (PossOk rho' pi') _ _ p1 Hpss).
      - intros cabs s0 Hmatch. exists cabs. split; auto. apply rt_refl.
      - intros x y Hxy IH Hyz.
        destruct x as [rho pi | ]; [ | exact I].
        intros cabs s0 Hmatch.
        destruct y as [rho1 pi1 | ].
        + destruct (poss_step_shadow rho pi rho1 pi1 cabs Hxy Hmatch) as (ev & cabs1 & Hustep & Hmatch1).
          destruct (IH cabs1 s0 Hmatch1) as (cabs' & Hmatch' & Htrace').
          exists cabs'. split; auto.
          eapply rt_trans; [apply rt_step; econstructor; exact Hustep | exact Htrace'].
        + exfalso. eapply poss_steps_from_error in Hyz; [discriminate | reflexivity].
    Qed.

    Lemma poss_steps_shadow :
      forall rho pi rho' pi',
        poss_steps (PossOk rho pi) (PossOk rho' pi') ->
        forall cabs s0, pool_matches_lin cabs pi ->
          exists cabs', pool_matches_lin cabs' pi' /\
            @trace_steps F F VF idImpl (mkTraceConfig s0 rho cabs) (mkTraceConfig s0 rho' cabs').
    Proof.
      intros rho pi rho' pi' Hpss.
      exact (poss_steps_shadow_gen rho' pi' (PossOk rho pi) Hpss).
    Qed.

    (* If a possibility can reach an error, then it can be replayed, up to
       that point, into a matching [idImpl] execution, after which an
       arbitrary continuation [tl] of the trace is accepted (undefined
       behavior). *)
    Lemma poss_steps_error_shadow_gen :
      forall p1,
        poss_steps p1 PossError ->
        match p1 with
        | PossOk rho pi =>
            forall cabs s0 tl, pool_matches_lin cabs pi ->
              exists rho' cabs',
                @trace_steps F F VF idImpl (mkTraceConfig s0 rho cabs) (mkTraceConfig (s0 ++ tl) rho' cabs')
        | PossError => True
        end.
    Proof.
      intros p1 Hpss.
      unfold poss_steps in Hpss.
      refine (clos_refl_trans_ind_right _ poss_step
        (fun p1 => match p1 with
         | PossOk rho pi =>
             forall cabs s0 tl, pool_matches_lin cabs pi ->
               exists rho' cabs',
                 @trace_steps F F VF idImpl (mkTraceConfig s0 rho cabs) (mkTraceConfig (s0 ++ tl) rho' cabs')
         | PossError => True
         end)
        PossError _ _ p1 Hpss).
      - exact I.
      - intros x y Hxy IH Hyz.
        destruct x as [rho pi | ]; [ | exact I].
        intros cabs s0 tl Hmatch.
        destruct y as [rho1 pi1 | ].
        + destruct (poss_step_shadow rho pi rho1 pi1 cabs Hxy Hmatch) as (ev & cabs1 & Hustep & Hmatch1).
          destruct (IH cabs1 s0 tl Hmatch1) as (rho' & cabs' & Htrace').
          exists rho', cabs'.
          eapply rt_trans; [apply rt_step; econstructor; exact Hustep | exact Htrace'].
        + dependent destruction Hxy.
          pose proof (Hmatch t0) as Hm. rewrite Hlin in Hm. simpl in Hm.
          exists rho, cabs. apply rt_step.
          eapply (TraceStepError idImpl s0 rho cabs tl (Build_ThreadEvent t0 (InvEv f))).
          econstructor; eauto. econstructor. exact Herror.
    Qed.

    Lemma poss_steps_error_shadow :
      forall rho pi,
        poss_steps (PossOk rho pi) PossError ->
        forall cabs s0 tl, pool_matches_lin cabs pi ->
          exists rho' cabs',
            @trace_steps F F VF idImpl (mkTraceConfig s0 rho cabs) (mkTraceConfig (s0 ++ tl) rho' cabs').
    Proof.
      intros rho pi Hpss.
      exact (poss_steps_error_shadow_gen (PossOk rho pi) Hpss).
    Qed.

    (* The trace component of a [trace_steps] chain only ever grows by
       appending: this lets us recover, at any point reached along a
       concrete run, how much of the final trace is still left to produce. *)
    Lemma trace_step_app_witness :
      forall (X Y : @TraceConfig E F VE), trace_step M X Y -> exists tl, tc_trace Y = tc_trace X ++ tl.
    Proof.
      intros X Y Hstep. destruct Hstep; simpl.
      - eexists; reflexivity.
      - eexists; reflexivity.
      - exists nil; rewrite app_nil_r; reflexivity.
      - exists nil; rewrite app_nil_r; reflexivity.
      - eexists; reflexivity.
    Qed.

    Lemma trace_steps_monotone :
      forall (X Y : @TraceConfig E F VE), trace_steps M X Y -> exists tl, tc_trace Y = tc_trace X ++ tl.
    Proof.
      intros X Y Hpss. unfold trace_steps in Hpss.
      induction Hpss.
      - apply trace_step_app_witness; auto.
      - exists nil. rewrite app_nil_r. reflexivity.
      - destruct IHHpss1 as [tl1 Heq1]. destruct IHHpss2 as [tl2 Heq2].
        exists (tl1 ++ tl2). rewrite Heq2, Heq1, app_assoc. reflexivity.
    Qed.

    (* A set-level (speculative) counterpart of [TraceConfig]/[trace_step]:
       an accumulated trace paired with the current [AbstractConfig], and
       the corresponding notion of stepping. [abs_step] mirrors exactly the
       structure of [trace_step], one clause per kind of concrete step:
       [AbsStepInv]/[AbsStepRet] correspond to [TraceStepInv]/[TraceStepRet]
       (tp-inv/tp-ret, via [ac_inv]/[ac_res]), [AbsStepSteps] corresponds to
       [TraceStepU]/[TraceStepTau] (library/silent steps, replayed
       speculatively via [ac_steps]), and [AbsStepError] corresponds to
       [TraceStepError] (undefined behavior once some possibility errors). *)
    Record AbsConfigTr : Type := mkACTr {
      actr_trace : Trace F;
      actr_delta : AbstractConfig VF;
    }.

    Inductive abs_step : AbsConfigTr -> AbsConfigTr -> Prop :=
    | AbsStepInv (s : Trace F) (Delta : AbstractConfig VF) (t : tid) (f : Sig.op F)
        (Hdom : forall (rho : State VF) (pi : tmap (@LinState F)), Delta rho pi -> TMap.find t pi = None) :
        abs_step (mkACTr s Delta)
          (mkACTr (s ++ (Build_ThreadEvent t (InvEv f) :: nil)) (ac_inv Delta t f))
    | AbsStepRet (s : Trace F) (Delta : AbstractConfig VF) (t : tid) (f : Sig.op F) (ret : Sig.ar f)
        (Hlin : forall (rho : State VF) (pi : tmap (@LinState F)), Delta rho pi -> TMap.find t pi = Some (ls_linr f ret)) :
        abs_step (mkACTr s Delta)
          (mkACTr (s ++ (Build_ThreadEvent t (ResEv f ret) :: nil)) (ac_res Delta t))
    | AbsStepSteps (s : Trace F) (Delta Delta' : AbstractConfig VF)
        (Hsub : (Delta' ⊆ ac_steps Delta)%AbstractConfig) :
        abs_step (mkACTr s Delta) (mkACTr s Delta')
    | AbsStepError (s : Trace F) (Delta : AbstractConfig VF) (rho : State VF) (pi : tmap (@LinState F)) (tl : Trace F)
        (Hposs : Delta rho pi)
        (Herror : poss_steps (PossOk rho pi) PossError) :
        abs_step (mkACTr s Delta) (mkACTr (s ++ tl) Delta).

    Definition abs_reaches := clos_refl_trans _ abs_step.

    Lemma abs_step_app_witness :
      forall X Y, abs_step X Y -> exists tl, actr_trace Y = actr_trace X ++ tl.
    Proof.
      intros X Y Hstep. destruct Hstep; simpl.
      - eexists; reflexivity.
      - eexists; reflexivity.
      - exists nil; rewrite app_nil_r; reflexivity.
      - eexists; reflexivity.
    Qed.

    Lemma abs_reaches_monotone :
      forall X Y, abs_reaches X Y -> exists tl, actr_trace Y = actr_trace X ++ tl.
    Proof.
      intros X Y Hpss. unfold abs_reaches in Hpss.
      induction Hpss.
      - apply abs_step_app_witness; auto.
      - exists nil. rewrite app_nil_r. reflexivity.
      - destruct IHHpss1 as [tl1 Heq1]. destruct IHHpss2 as [tl2 Heq2].
        exists (tl1 ++ tl2). rewrite Heq2, Heq1, app_assoc. reflexivity.
    Qed.

    (* Layer 1: unfolding [TPSimulation] alongside a concrete run produces a
       matching set-level [abs_reaches] judgement, reproducing the exact
       same trace. This is the easy (sound) direction of Lemma 5.3, and
       adapts the classical argument that a rely-guarantee-style simulation
       implies trace refinement to the [AbstractConfig]-based setting
       already used by [TPSimulationSet]. *)
    Theorem TPSimulation_abs_reaches :
      forall (sigma : State VE) (c : @ThreadPoolState E F) (Delta : AbstractConfig VF),
        TPSimulation M sigma c Delta -> dom_match c Delta ->
        forall (s : Trace F) (sigma' : State VE) (c' : @ThreadPoolState E F),
          trace_steps M (mkTraceConfig nil sigma c) (mkTraceConfig s sigma' c') ->
          exists Delta', abs_reaches (mkACTr nil Delta) (mkACTr s Delta').
    Proof.
      intros sigma c Delta Hsim Hdm s sigma' c' Htrace.
      unfold trace_steps in Htrace.
      revert Delta Hsim Hdm.
      refine (clos_refl_trans_ind_right _ (trace_step M)
        (fun X => match X with
         | mkTraceConfig s0 sigma0 c0 =>
             forall Delta0, TPSimulation M sigma0 c0 Delta0 -> dom_match c0 Delta0 ->
               exists Delta', abs_reaches (mkACTr s0 Delta0) (mkACTr s Delta')
         end)
        (mkTraceConfig s sigma' c') _ _ (mkTraceConfig nil sigma c) Htrace).
      - intros Delta0 Hsim0 Hdm0. exists Delta0. apply rt_refl.
      - intros X Y HXY IH HYZ.
        destruct X as [s0 sigma0 c0].
        intros Delta0 Hsim0 Hdm0.
        destruct Hsim0 as [rho0 pi0 Hposs0 Herror0 | tpsim_invstep tpsim_retstep tpsim_ustep tpsim_linstep tpsim_taustep tpsim_noerror].
        + (* Delta0 already errors: absorb the rest of the run unconditionally *)
          assert (Hchain : trace_steps M (mkTraceConfig s0 sigma0 c0) (mkTraceConfig s sigma' c')).
          { unfold trace_steps. eapply rt_trans; [apply rt_step; exact HXY | exact HYZ]. }
          destruct (trace_steps_monotone _ _ Hchain) as [tl Heqtl].
          simpl in Heqtl.
          exists Delta0. apply rt_step. rewrite Heqtl.
          eapply AbsStepError; eauto.
        + dependent destruction HXY.
          * (* TraceStepInv *)
            rename t0 into thr. rename c'0 into c1.
            pose proof (tpsim_invstep thr f c1 Hstep) as Hcont.
            inversion Hstep as [Hfind Hupd].
            assert (Hdm1 : dom_match c1 (ac_inv Delta0 thr f))
              by (rewrite Hupd; apply dom_match_ac_inv; exact Hdm0).
            destruct (IH (ac_inv Delta0 thr f) Hcont Hdm1) as [Delta' Hreach].
            exists Delta'.
            unfold abs_reaches.
            eapply rt_trans with
              (y := mkACTr (s0 ++ (Build_ThreadEvent thr (InvEv f) :: nil)) (ac_inv Delta0 thr f)).
            -- apply rt_step. apply AbsStepInv.
               intros rho pi Hposs.
               specialize (Hdm0 rho pi Hposs thr). tauto.
            -- exact Hreach.
          * (* TraceStepRet *)
            rename t0 into thr. rename c'0 into c1.
            destruct (tpsim_retstep thr f ret c1 Hstep) as [Hlin Hcont].
            inversion Hstep as [Hfind Hupd].
            assert (Hdm1 : dom_match c1 (ac_res Delta0 thr))
              by (rewrite Hupd; apply dom_match_ac_res; exact Hdm0).
            destruct (IH (ac_res Delta0 thr) Hcont Hdm1) as [Delta' Hreach].
            exists Delta'.
            unfold abs_reaches.
            eapply rt_trans with
              (y := mkACTr (s0 ++ (Build_ThreadEvent thr (ResEv f ret) :: nil)) (ac_res Delta0 thr)).
            -- apply rt_step. apply AbsStepRet. exact Hlin.
            -- exact Hreach.
          * (* TraceStepU *)
            destruct (tpsim_ustep ev sigma'0 c'0 Hstep) as [Delta1 [Hsub Hcont]].
            assert (Hdm1 : dom_match c'0 Delta1).
            { intros rho pi Hposs t.
              apply Hsub in Hposs. inversion Hposs as [rho1 pi1 rho2 pi2 Hposs1 Hpstep]; subst.
              pose proof (poss_steps_domexact _ _ _ _ Hpstep) as Hde.
              pose proof (ustep_dom_preserved ev sigma0 c0 sigma'0 c'0 Hstep t) as Hpres.
              specialize (Hdm0 _ _ Hposs1 t). specialize (Hde t). tauto. }
            destruct (IH Delta1 Hcont Hdm1) as [Delta' Hreach].
            exists Delta'.
            unfold abs_reaches.
            eapply rt_trans with (y := mkACTr s0 Delta1).
            -- apply rt_step. apply AbsStepSteps. exact Hsub.
            -- exact Hreach.
          * (* TraceStepTau *)
            rename t0 into thr. rename c'0 into c1.
            pose proof (tpsim_taustep thr c1 Hstep) as Hcont.
            assert (Hdm1 : dom_match c1 Delta0).
            { intros rho pi Hposs t.
              pose proof (taustep_dom_preserved thr c0 c1 Hstep t) as Hpres.
              specialize (Hdm0 _ _ Hposs t). tauto. }
            destruct (IH Delta0 Hcont Hdm1) as [Delta' Hreach].
            exists Delta'. exact Hreach.
          * (* TraceStepError: impossible since Delta0 is not already erroring *)
            exfalso. eapply tpsim_noerror. exact Herror.
    Qed.

    (* Layer 2: replay a set-level [abs_reaches] judgement into a single,
       literal execution of [idImpl] reproducing the same trace, by
       picking one possibility at the very end and working backwards
       through the steps that justify each set-level transition. This is
       where the domain-tracking [Hdom] field of [AbsStepInv] (absent from
       [ac_inv] itself) becomes necessary: it lets us discharge [invstep]'s
       "not already active" precondition for whichever thread is chosen. *)
    Theorem abs_reaches_reify :
      forall (s0 : Trace F) (Delta0 : AbstractConfig VF) (s : Trace F) (Delta' : AbstractConfig VF),
        abs_reaches (mkACTr s0 Delta0) (mkACTr s Delta') ->
        exists (rho0 : State VF) (pi0 : tmap (@LinState F)),
          Delta0 rho0 pi0 /\
          forall cabs0, pool_matches_lin cabs0 pi0 ->
            exists rho_f cabs_f,
              @trace_steps F F VF idImpl (mkTraceConfig s0 rho0 cabs0) (mkTraceConfig s rho_f cabs_f).
    Proof.
      intros s0 Delta0 s Delta' Hreach.
      unfold abs_reaches in Hreach.
      refine (clos_refl_trans_ind_right _ abs_step
        (fun X => match X with
         | mkACTr s0' Delta0' =>
             exists rho0 pi0, Delta0' rho0 pi0 /\
               forall cabs0, pool_matches_lin cabs0 pi0 ->
                 exists rho_f cabs_f,
                   @trace_steps F F VF idImpl (mkTraceConfig s0' rho0 cabs0) (mkTraceConfig s rho_f cabs_f)
         end)
        (mkACTr s Delta') _ _ (mkACTr s0 Delta0) Hreach).
      - destruct (ac_nonempty Delta') as [rho0 [pi0 Hposs0]].
        exists rho0, pi0. split; auto.
        intros cabs0 Hmatch0. exists rho0, cabs0. apply rt_refl.
      - intros x y Hxy IH Hyz.
        destruct x as [s0' Delta0'].
        destruct y as [s1 Delta1].
        destruct IH as [rho1 [pi1 [Hposs1 Hcont1]]].
        dependent destruction Hxy.
        + (* AbsStepInv *)
          rename t0 into thr.
          inversion Hposs1 as [rho00 pi00 Hposs00]; subst.
          exists rho1, pi00. split; auto.
          intros cabs0 Hmatch0.
          pose proof (Hdom rho1 pi00 Hposs00) as Hnone.
          pose proof (Hmatch0 thr) as Hm. rewrite Hnone in Hm. simpl in Hm.
          eassert (Hcabs1 : trace_step idImpl
                     (mkTraceConfig s0' rho1 cabs0)
                     (mkTraceConfig (s0' ++ (Build_ThreadEvent thr (InvEv f) :: nil)) rho1
                        (TMap.add thr (Build_ThreadState f (Vis f (fun v => Ret v)) None) cabs0))).
          { apply TraceStepInv. econstructor; eauto. }
          assert (Hmatch1 : pool_matches_lin
                    (TMap.add thr (Build_ThreadState f (Vis f (fun v => Ret v)) None) cabs0)
                    (TMap.add thr (ls_inv f) pi00)).
          { intros t'. destruct (Pos.eq_dec t' thr); subst.
            - rewrite !TMap.gss. reflexivity.
            - rewrite !TMap.gso; auto. }
          destruct (Hcont1 _ Hmatch1) as [rho_f [cabs_f Htail]].
          exists rho_f, cabs_f.
          eapply rt_trans; [ apply rt_step; exact Hcabs1 | exact Htail ].
        + (* AbsStepRet *)
          rename t0 into thr.
          inversion Hposs1 as [rho00 pi00 Hposs00]; subst.
          exists rho1, pi00. split; auto.
          intros cabs0 Hmatch0.
          pose proof (Hlin rho1 pi00 Hposs00) as Hsome.
          pose proof (Hmatch0 thr) as Hm. rewrite Hsome in Hm. simpl in Hm.
          eassert (Hcabs1 : trace_step idImpl
                     (mkTraceConfig s0' rho1 cabs0)
                     (mkTraceConfig (s0' ++ (Build_ThreadEvent thr (ResEv f ret) :: nil)) rho1
                        (TMap.remove thr cabs0))).
          { apply TraceStepRet. econstructor; eauto. }
          assert (Hmatch1 : pool_matches_lin (TMap.remove thr cabs0) (TMap.remove thr pi00)).
          { intros t'. destruct (Pos.eq_dec t' thr); subst.
            - rewrite !TMap.grs. reflexivity.
            - rewrite !TMap.gro; auto. }
          destruct (Hcont1 _ Hmatch1) as [rho_f [cabs_f Htail]].
          exists rho_f, cabs_f.
          eapply rt_trans; [ apply rt_step; exact Hcabs1 | exact Htail ].
        + (* AbsStepSteps *)
          apply Hsub in Hposs1.
          inversion Hposs1 as [rho0 pi0 rho1' pi1' Hposs0 Hpstep]; subst.
          exists rho0, pi0. split; auto.
          intros cabs0 Hmatch0.
          destruct (poss_steps_shadow rho0 pi0 rho1 pi1 Hpstep cabs0 s1 Hmatch0)
            as [cabs1 [Hmatch1 Htrace1]].
          destruct (Hcont1 _ Hmatch1) as [rho_f [cabs_f Htail]].
          exists rho_f, cabs_f.
          eapply rt_trans; [ exact Htrace1 | exact Htail ].
        + (* AbsStepError *)
          exists rho, pi. split; auto.
          intros cabs0 Hmatch0.
          destruct (abs_reaches_monotone _ _ Hyz) as [tl2 Heqtl2].
          simpl in Heqtl2. rewrite List.app_assoc_reverse in Heqtl2.
          destruct (poss_steps_error_shadow rho pi Herror cabs0 s0' (tl ++ tl2) Hmatch0)
            as [rho_f [cabs_f Htrace1]].
          exists rho_f, cabs_f.
          rewrite Heqtl2. exact Htrace1.
    Qed.

    (* Lemma 5.3 (sound direction): the Threadpool Simulation (Definition
       5.2, mechanized as [TPSimulationSet.cal]) implies Compositional
       Linearizability (Definition 4.1, [CompLin.CompLin]). Combines Layer 1
       (produce a matching [abs_reaches] judgement) with Layer 2 (reify it
       into a single concrete execution of [idImpl]). *)
    Theorem cal_to_CompLin :
      forall (sigma0 : State VE) (rho0 : State VF),
        cal M sigma0 rho0 -> CompLin.CompLin M sigma0 rho0.
    Proof.
      intros sigma0 rho0 Hcal s Htr.
      destruct Htr as [sigma' [c' Htrace]].
      pose proof (dom_match_init rho0) as Hdm0.
      destruct (TPSimulation_abs_reaches sigma0 (TMap.empty _) (ac_init rho0) Hcal Hdm0
                  s sigma' c' Htrace) as [Delta' Hreach].
      destruct (abs_reaches_reify nil (ac_init rho0) s Delta' Hreach)
        as [rho00 [pi00 [Hposs00 Hcont]]].
      inversion Hposs00; subst.
      destruct (Hcont (TMap.empty _) pool_matches_lin_empty) as [rho_f [cabs_f Htrace_final]].
      exists rho_f, cabs_f. exact Htrace_final.
    Qed.

  End Adequacy.

  (* Corollary: any verified layer implementation from [TPSimulationSet]
     (i.e., anything already proven correct against the Threadpool
     Simulation) is compositionally linearizable in the sense of
     Definition 4.1. *)
  Theorem layer_implementation_CompLin {L L' : layer_interface} (LI : layer_implementation L L') :
    CompLin.CompLin (li_impl LI) (li_init L) (li_init L').
  Proof.
    apply cal_to_CompLin. exact (li_correct LI).
  Qed.

End CompLinSound.
