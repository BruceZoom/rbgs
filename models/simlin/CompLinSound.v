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
      [TPSimulation] itself. Since [CompLin.trace_step]'s undefined-behavior
      marker [TErr] is now a precise, terminal token (not an arbitrary
      concrete tail), this layer produces a genuine disjunction: either the
      concrete run reaches the target trace [s] cleanly, or it reaches some
      (necessarily earlier, since [dom_match]/[TPSim_Error] only kick in
      once a possibility genuinely errors) prefix [s1] of [s] followed by
      [TErr], with [s] itself simply extending [s1 ++ TErr :: nil] by
      whatever the concrete run went on to do (which the criterion does not
      need to reproduce).
    - Layer 2 ([abs_reaches_reify]) turns a set-level judgement into a
      single concrete execution of [idImpl], by picking one possibility and
      replaying, backwards, the steps that justify each set-level
      transition; it produces the same kind of "clean, or errors at some
      earlier prefix" disjunction.

    Assembling the two ([cal_to_CompLin]) matches the resulting trace
    against [CompLin.ImplTracesClosed]: [idImpl]'s own undefined-behavior
    marker licenses any trace extending wherever *it* errors, which is
    exactly what is needed once either layer above bottoms out in an
    error. *)
Module CompLinSound.
  Import Reg.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import Semantics.
  Import TPSimulationSet.TPSimulation.
  Import CompLin.CompLin.

  (* A trace ending in an explicit [TErr] can always be "unsnoc'd" against
     another trace ending in the same marker, provided the tail on the left
     is non-empty: this is exactly the situation when combining two
     "reaches an error at some prefix" facts about the same underlying
     run. *)
  Lemma trace_snoc_prefix {A} :
    forall (p tl s1 : list A) (x : A),
      tl <> nil ->
      p ++ tl = s1 ++ x :: nil ->
      exists q, s1 = p ++ q /\ tl = q ++ x :: nil.
  Proof.
    induction p as [| a p IH]; intros tl s1 x Htlnn Heq.
    - simpl in Heq. exists s1. split; [reflexivity | exact Heq].
    - destruct s1 as [| b s1'].
      + simpl in Heq. injection Heq as Heqa Heqrest.
        apply app_eq_nil in Heqrest as [Hp0 Htl0]. subst. contradiction.
      + simpl in Heq. injection Heq as Heqab Heqrest. subst b.
        destruct (IH tl s1' x Htlnn Heqrest) as [q [Heqs1 Heqtl]].
        exists q. split; [rewrite Heqs1; reflexivity | exact Heqtl].
  Qed.

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
      domain_equiv (pool_domain c) (ac_active Delta).

    Lemma dom_match_find_none c Delta rho pi t :
      dom_match c Delta -> Delta rho pi ->
      (TMap.find t c = None <-> TMap.find t pi = None).
    Proof.
      intros Hdm Hposs.
      pose proof (Hdm t) as Hactive.
      pose proof (ac_find_some_iff Delta rho pi t Hposs) as Hfind.
      unfold pool_domain, map_domain in Hactive.
      split; intros Hnone.
      - destruct (TMap.find t pi) eqn:Hpi; auto.
        exfalso.
        assert (ac_active Delta t).
        { apply (proj2 Hfind). eauto. }
        apply (proj2 Hactive) in H. destruct H as [x Hx]. congruence.
      - destruct (TMap.find t c) eqn:Hc; auto.
        exfalso.
        assert (ac_active Delta t).
        { apply (proj1 Hactive). eauto. }
        apply (proj1 Hfind) in H. destruct H as [x Hx]. congruence.
    Qed.

    Lemma pool_domain_preserved (c c' : @ThreadPoolState E F) :
      (forall t, TMap.find t c = None <-> TMap.find t c' = None) ->
      domain_equiv (pool_domain c) (pool_domain c').
    Proof.
      intros Hnone t. specialize (Hnone t).
      unfold pool_domain, map_domain.
      split; intros [x Hx].
      - destruct (TMap.find t c') eqn:Hc'; [eauto|].
        assert (TMap.find t c = None) by (apply (proj2 Hnone); reflexivity).
        congruence.
      - destruct (TMap.find t c) eqn:Hc; [eauto|].
        assert (TMap.find t c' = None) by (apply (proj1 Hnone); reflexivity).
        congruence.
    Qed.

    Lemma dom_match_pool_preserved c c' Delta :
      dom_match c Delta ->
      (forall t, TMap.find t c = None <-> TMap.find t c' = None) ->
      dom_match c' Delta.
    Proof.
      intros Hdm Hpres.
      eapply domain_equiv_trans; [|exact Hdm].
      apply domain_equiv_symm, pool_domain_preserved; exact Hpres.
    Qed.

    Lemma dom_match_init (rho0 : State VF) :
      dom_match (TMap.empty _) (ac_init rho0).
    Proof.
      unfold dom_match, pool_domain, ac_init. simpl.
      eapply domain_equiv_trans; [apply map_domain_empty|].
      apply domain_equiv_symm, map_domain_empty.
    Qed.

    Lemma dom_match_ac_inv c Delta t f ts :
      dom_match c Delta ->
      dom_match (TMap.add t ts c) (ac_inv Delta t f).
    Proof.
      intros Hdm t'.
      pose proof (map_domain_add c t ts t') as Hpool.
      pose proof (ac_inv_active Delta t f t') as Habs.
      specialize (Hdm t').
      unfold pool_domain, domain_add in *. firstorder.
    Qed.

    Lemma dom_match_ac_res c Delta t :
      dom_match c Delta ->
      dom_match (TMap.remove t c) (ac_res Delta t).
    Proof.
      intros Hdm t'.
      pose proof (map_domain_remove c t t') as Hpool.
      pose proof (ac_res_active Delta t t') as Habs.
      specialize (Hdm t').
      unfold pool_domain, domain_remove in *. firstorder.
    Qed.

    Lemma dom_match_ac_steps c Delta Delta' :
      dom_match c Delta ->
      (Delta' ⊆ ac_steps Delta)%AbstractConfig ->
      dom_match c Delta'.
    Proof.
      intros Hdm Hsub t.
      pose proof (ac_subset_active _ _ Hsub t) as Hsubdom.
      pose proof (ac_steps_active Delta t) as Hsteps.
      specialize (Hdm t). firstorder.
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

    (* A possibility that reaches [PossError] does so via some final
       [ps_error] step: extracting the witnessing thread/operation [t]/[f]
       (and the possibility [(rho1, pi1)] just before that step) is what
       lets the terminal marker recorded elsewhere (e.g. [TErr f] in
       [CompLin.v], or [AbsStepError] below) be tagged with the operation
       that was actually in flight, rather than left bare. *)
    Lemma poss_steps_error_last :
      forall rho pi, poss_steps (PossOk rho pi) PossError ->
        exists t f rho1 pi1,
          poss_steps (PossOk rho pi) (PossOk rho1 pi1) /\
          Error VF (Build_ThreadEvent t (InvEv f)) rho1 /\
          TMap.find t pi1 = Some (ls_inv f).
    Proof.
      intros rho pi Hpss.
      unfold poss_steps in Hpss.
      refine (clos_refl_trans_ind_right _ poss_step
        (fun p1 => match p1 with
         | PossOk rho0 pi0 =>
             exists t f rho1 pi1,
               poss_steps (PossOk rho0 pi0) (PossOk rho1 pi1) /\
               Error VF (Build_ThreadEvent t (InvEv f)) rho1 /\
               TMap.find t pi1 = Some (ls_inv f)
         | PossError => True
         end)
        PossError _ _ (PossOk rho pi) Hpss).
      - exact I.
      - intros x y Hxy IH Hyz.
        destruct x as [rho0 pi0 | ]; [ | exact I].
        destruct y as [rho1 pi1 | ].
        + destruct IH as [t [f [rho2 [pi2 [Hsteps [Herr Hlin]]]]]].
          exists t, f, rho2, pi2. split; auto.
          eapply rt_trans; [apply rt_step; exact Hxy | exact Hsteps].
        + dependent destruction Hxy.
          exists t0, f, rho0, pi0. split; [apply rt_refl | split; auto].
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
       that point, into a matching [idImpl] execution, after which the
       [TErr] marker is appended: undefined behavior from here on. *)
    Lemma poss_steps_error_shadow_gen :
      forall p1,
        poss_steps p1 PossError ->
        match p1 with
        | PossOk rho pi =>
            forall cabs s0, pool_matches_lin cabs pi ->
              exists f rho' cabs',
                @trace_steps F F VF idImpl (mkTraceConfig s0 rho cabs) (mkTraceConfig (s0 ++ TErr f :: nil) rho' cabs')
        | PossError => True
        end.
    Proof.
      intros p1 Hpss.
      unfold poss_steps in Hpss.
      refine (clos_refl_trans_ind_right _ poss_step
        (fun p1 => match p1 with
         | PossOk rho pi =>
             forall cabs s0, pool_matches_lin cabs pi ->
               exists f rho' cabs',
                 @trace_steps F F VF idImpl (mkTraceConfig s0 rho cabs) (mkTraceConfig (s0 ++ TErr f :: nil) rho' cabs')
         | PossError => True
         end)
        PossError _ _ p1 Hpss).
      - exact I.
      - intros x y Hxy IH Hyz.
        destruct x as [rho pi | ]; [ | exact I].
        intros cabs s0 Hmatch.
        destruct y as [rho1 pi1 | ].
        + destruct (poss_step_shadow rho pi rho1 pi1 cabs Hxy Hmatch) as (ev & cabs1 & Hustep & Hmatch1).
          destruct (IH cabs1 s0 Hmatch1) as (f & rho' & cabs' & Htrace').
          exists f, rho', cabs'.
          eapply rt_trans; [apply rt_step; econstructor; exact Hustep | exact Htrace'].
        + dependent destruction Hxy.
          pose proof (Hmatch t0) as Hm. rewrite Hlin in Hm. simpl in Hm.
          exists f, rho, cabs. apply rt_step.
          eapply (TraceStepError idImpl s0 rho cabs f (Build_ThreadEvent t0 (InvEv f))
                    (Build_ThreadState f (Vis f (fun v => Ret v)) None)).
          * exact Hm.
          * econstructor. exact Herror.
    Qed.

    Lemma poss_steps_error_shadow :
      forall rho pi,
        poss_steps (PossOk rho pi) PossError ->
        forall cabs s0, pool_matches_lin cabs pi ->
          exists f rho' cabs',
            @trace_steps F F VF idImpl (mkTraceConfig s0 rho cabs) (mkTraceConfig (s0 ++ TErr f :: nil) rho' cabs').
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
       [TraceStepError] (undefined behavior once some possibility errors),
       appending the same terminal [TErr] marker. *)
    Record AbsConfigTr : Type := mkACTr {
      actr_trace : Trace F;
      actr_delta : AbstractConfig VF;
    }.

    Inductive abs_step : AbsConfigTr -> AbsConfigTr -> Prop :=
    | AbsStepInv (s : Trace F) (Delta : AbstractConfig VF) (t : tid) (f : Sig.op F)
        (Hdom : forall (rho : State VF) (pi : tmap (@LinState F)), Delta rho pi -> TMap.find t pi = None) :
        abs_step (mkACTr s Delta)
          (mkACTr (s ++ (TEvent (Build_ThreadEvent t (InvEv f)) :: nil)) (ac_inv Delta t f))
    | AbsStepRet (s : Trace F) (Delta : AbstractConfig VF) (t : tid) (f : Sig.op F) (ret : Sig.ar f)
        (Hlin : forall (rho : State VF) (pi : tmap (@LinState F)), Delta rho pi -> TMap.find t pi = Some (ls_linr f ret)) :
        abs_step (mkACTr s Delta)
          (mkACTr (s ++ (TEvent (Build_ThreadEvent t (ResEv f ret)) :: nil)) (ac_res Delta t))
    | AbsStepSteps (s : Trace F) (Delta Delta' : AbstractConfig VF)
        (Hsub : (Delta' ⊆ ac_steps Delta)%AbstractConfig) :
        abs_step (mkACTr s Delta) (mkACTr s Delta')
    | AbsStepError (s : Trace F) (Delta : AbstractConfig VF)
        (rho : State VF) (pi : tmap (@LinState F))
        (t : tid) (f : Sig.op F) (rhoE : State VF) (piE : tmap (@LinState F))
        (Hposs : Delta rho pi)
        (Hsteps : poss_steps (PossOk rho pi) (PossOk rhoE piE))
        (Herror : Error VF (Build_ThreadEvent t (InvEv f)) rhoE)
        (Hlin : TMap.find t piE = Some (ls_inv f)) :
        abs_step (mkACTr s Delta) (mkACTr (s ++ TErr f :: nil) Delta).

    Definition abs_reaches := clos_refl_trans _ abs_step.

    Lemma abstract_update_steps_dom_match c Delta Delta' :
      dom_match c Delta -> TPSimulation.AbstractUpdateSteps Delta Delta' ->
      dom_match c Delta'.
    Proof.
      intros Hdom Hsteps. induction Hsteps.
      - exact Hdom.
      - apply IHHsteps. eapply dom_match_ac_steps; eauto.
    Qed.

    Lemma abstract_update_steps_abs_reaches s Delta Delta' :
      TPSimulation.AbstractUpdateSteps Delta Delta' ->
      abs_reaches (mkACTr s Delta) (mkACTr s Delta').
    Proof.
      intro Hsteps. induction Hsteps.
      - apply rt_refl.
      - eapply rt_trans; [apply rt_step; apply AbsStepSteps; exact H|].
        exact IHHsteps.
    Qed.

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
       matching set-level [abs_reaches] judgement: either reproducing the
       exact same trace [s] (clean run), or reaching some earlier prefix
       [s1] of [s] (i.e. [s = s1 ++ tl] for some [tl]) followed by [TErr],
       once some possibility errors along the way. This is the easy (sound)
       direction of Lemma 5.3, and adapts the classical argument that a
       rely-guarantee-style simulation implies trace refinement to the
       [AbstractConfig]-based setting already used by [TPSimulationSet]. *)
    Theorem TPSimulation_abs_reaches :
      forall (sigma : State VE) (c : @ThreadPoolState E F) (Delta : AbstractConfig VF),
        TPSimulation M sigma c Delta -> dom_match c Delta ->
        forall (s : Trace F) (sigma' : State VE) (c' : @ThreadPoolState E F),
          trace_steps M (mkTraceConfig nil sigma c) (mkTraceConfig s sigma' c') ->
          (exists Delta', abs_reaches (mkACTr nil Delta) (mkACTr s Delta')) \/
          (exists s1 f tl Delta', s = s1 ++ tl /\
            abs_reaches (mkACTr nil Delta) (mkACTr (s1 ++ TErr f :: nil) Delta')).
    Proof.
      intros sigma c Delta Hsim Hdm s sigma' c' Htrace.
      unfold trace_steps in Htrace.
      revert Delta Hsim Hdm.
      refine (clos_refl_trans_ind_right _ (trace_step M)
        (fun X => match X with
         | mkTraceConfig s0 sigma0 c0 =>
             forall Delta0,
               TPSimulation M sigma0 c0 Delta0 ->
               dom_match c0 Delta0 ->
               (exists Delta',
                  abs_reaches
                    (mkACTr s0 Delta0)
                    (mkACTr s Delta')) \/
               (exists s1 f tl Delta', s = s1 ++ tl /\
                  abs_reaches
                    (mkACTr s0 Delta0)
                    (mkACTr
                       (s1 ++ TErr f :: nil) Delta'))
         end)
        (mkTraceConfig s sigma' c') _ _
        (mkTraceConfig nil sigma c) Htrace).
      - intros Delta0 Hsim0 Hdm0. left. exists Delta0. apply rt_refl.
      - intros X Y HXY IH HYZ.
        destruct X as [s0 sigma0 c0].
        intros Delta0 Hsim0 Hdm0.
        destruct (simulation_normalizes M sigma0 c0 Delta0 Hsim0)
          as [DeltaN [Hupdates Hterminal]].
        pose proof
          (abstract_update_steps_abs_reaches s0 Delta0 DeltaN Hupdates)
          as Hprefix.
        pose proof
          (abstract_update_steps_dom_match c0 Delta0 DeltaN Hdm0 Hupdates)
          as HdmN.
        destruct Hterminal as [Herror | Hcontinue].
        + (* A finite update prefix reaches an abstract error before the
             pending concrete trace step. *)
          right. destruct Herror as [rho0 [pi0 [Hposs0 Herror0]]].
          destruct (poss_steps_error_last
                      rho0 pi0 Herror0)
            as [t [f [rho1 [pi1 [Hsteps [Herr Hlin]]]]]].
          assert (Hchain : trace_steps M
                    (mkTraceConfig s0 sigma0 c0)
                    (mkTraceConfig s sigma' c')).
          { unfold trace_steps. eapply rt_trans;
              [apply rt_step; exact HXY | exact HYZ]. }
          destruct (trace_steps_monotone _ _ Hchain) as [tl Heqtl].
          simpl in Heqtl.
          exists s0, f, tl, DeltaN. split; [exact Heqtl |].
          eapply rt_trans; [exact Hprefix |].
          apply rt_step.
          eapply (AbsStepError
                    s0 DeltaN rho0 pi0 t f rho1 pi1
                    Hposs0 Hsteps Herr Hlin).
        + destruct Hcontinue as
            [Hinv Hret Hu Htau Hnoerror].
          dependent destruction HXY.
          * (* invocation *)
            rename t0 into thr. rename c'0 into c1.
            pose proof (Hinv thr f c1 Hstep) as Hcont.
            inversion Hstep as [Hfind Hupd].
            assert (Hdm1 :
              dom_match c1
                (ac_inv DeltaN thr f)).
            { rewrite Hupd.
              eapply (dom_match_ac_inv); exact HdmN. }
            destruct (IH (ac_inv DeltaN thr f) Hcont Hdm1) as
              [[Delta' Hreach] |
               [s1 [f0 [tl [Delta' [Heqs Hreach]]]]]].
            -- left. exists Delta'.
               eapply rt_trans; [exact Hprefix |].
               eapply rt_trans with
                 (y := mkACTr
                   (s0 ++ TEvent (Build_ThreadEvent thr (InvEv f)) :: nil)
                   (ac_inv DeltaN thr f)).
               ++ apply rt_step.
                  apply AbsStepInv.
                  intros rho pi Hposs.
                  apply (proj1
                    (dom_match_find_none c0 DeltaN rho pi thr HdmN Hposs)).
                  exact Hfind.
               ++ exact Hreach.
            -- right. exists s1, f0, tl, Delta'. split; [exact Heqs |].
               eapply rt_trans; [exact Hprefix |].
               eapply rt_trans with
                 (y := mkACTr
                   (s0 ++ TEvent (Build_ThreadEvent thr (InvEv f)) :: nil)
                   (ac_inv DeltaN thr f)).
               ++ apply rt_step.
                  apply AbsStepInv.
                  intros rho pi Hposs.
                  apply (proj1
                    (dom_match_find_none c0 DeltaN rho pi thr HdmN Hposs)).
                  exact Hfind.
               ++ exact Hreach.
          * (* return *)
            rename t0 into thr. rename c'0 into c1.
            destruct (Hret thr f ret c1 Hstep) as [Hlin Hcont].
            inversion Hstep as [Hfind Hupd].
            assert (Hdm1 :
              dom_match c1
                (ac_res DeltaN thr)).
            { rewrite Hupd.
              apply (dom_match_ac_res). exact HdmN. }
            destruct (IH (ac_res DeltaN thr) Hcont Hdm1) as
              [[Delta' Hreach] |
               [s1 [f0 [tl [Delta' [Heqs Hreach]]]]]].
            -- left. exists Delta'.
               eapply rt_trans; [exact Hprefix |].
               eapply rt_trans with
                 (y := mkACTr
                   (s0 ++ TEvent (Build_ThreadEvent thr (ResEv f ret)) :: nil)
                   (ac_res DeltaN thr)).
               ++ apply rt_step.
                  apply AbsStepRet. exact Hlin.
               ++ exact Hreach.
            -- right. exists s1, f0, tl, Delta'. split; [exact Heqs |].
               eapply rt_trans; [exact Hprefix |].
               eapply rt_trans with
                 (y := mkACTr
                   (s0 ++ TEvent (Build_ThreadEvent thr (ResEv f ret)) :: nil)
                   (ac_res DeltaN thr)).
               ++ apply rt_step.
                  apply AbsStepRet. exact Hlin.
               ++ exact Hreach.
          * (* visible library step *)
            destruct (Hu ev sigma'0 c'0 Hstep)
              as [Delta1 [Hsub Hcont]].
            assert (Hdm1 :
              dom_match c'0 Delta1).
            { eapply (dom_match_pool_preserved).
              - eapply (dom_match_ac_steps); eauto.
              - exact (ustep_dom_preserved
                         ev sigma0 c0 sigma'0 c'0 Hstep). }
            destruct (IH Delta1 Hcont Hdm1) as
              [[Delta' Hreach] |
               [s1 [f0 [tl [Delta' [Heqs Hreach]]]]]].
            -- left. exists Delta'.
               eapply rt_trans; [exact Hprefix |].
               eapply rt_trans with
                 (y := mkACTr s0 Delta1).
               ++ apply rt_step.
                  apply AbsStepSteps. exact Hsub.
               ++ exact Hreach.
            -- right. exists s1, f0, tl, Delta'. split; [exact Heqs |].
               eapply rt_trans; [exact Hprefix |].
               eapply rt_trans with
                 (y := mkACTr s0 Delta1).
               ++ apply rt_step.
                  apply AbsStepSteps. exact Hsub.
               ++ exact Hreach.
          * (* Tau is a concrete step and does not create an abstract
               possibility update. *)
            rename t0 into thr. rename c'0 into c1.
            pose proof (Htau thr c1 Hstep) as Hcont.
            assert (Hdm1 :
              dom_match c1 DeltaN).
            { eapply (dom_match_pool_preserved);
                [exact HdmN |].
              exact (taustep_dom_preserved
                       thr c0 c1 Hstep). }
            destruct (IH DeltaN Hcont Hdm1) as
              [[Delta' Hreach] |
               [s1 [f0 [tl [Delta' [Heqs Hreach]]]]]].
            -- left. exists Delta'.
               eapply rt_trans; [exact Hprefix | exact Hreach].
            -- right. exists s1, f0, tl, Delta'. split; [exact Heqs |].
               eapply rt_trans; [exact Hprefix | exact Hreach].
          * (* concrete error contradicts the exposed continue core *)
            exfalso. eapply Hnoerror. econstructor; eassumption.
    Qed.

    (* Layer 2: replay a set-level [abs_reaches] judgement into a single,
       literal execution of [idImpl] reproducing the same target trace, or,
       if [abs_reaches] itself bottoms out in an (even earlier) internal
       error, one reproducing that earlier error instead. This is where the
       domain-tracking [Hdom] field of [AbsStepInv] (absent from [ac_inv]
       itself) becomes necessary: it lets us discharge [invstep]'s "not
       already active" precondition for whichever thread is chosen. *)
    Theorem abs_reaches_reify :
      forall (s0 : Trace F) (Delta0 : AbstractConfig VF) (s : Trace F) (Delta' : AbstractConfig VF),
        abs_reaches (mkACTr s0 Delta0) (mkACTr s Delta') ->
        exists (rho0 : State VF) (pi0 : tmap (@LinState F)),
          Delta0 rho0 pi0 /\
          forall cabs0, pool_matches_lin cabs0 pi0 ->
            (exists rho_f cabs_f,
              @trace_steps F F VF idImpl (mkTraceConfig s0 rho0 cabs0) (mkTraceConfig s rho_f cabs_f)) \/
            (exists p f tl0 rho_f cabs_f, s = p ++ (TErr f :: nil ++ tl0) /\
              @trace_steps F F VF idImpl (mkTraceConfig s0 rho0 cabs0) (mkTraceConfig (p ++ TErr f :: nil) rho_f cabs_f)).
    Proof.
      intros s0 Delta0 s Delta' Hreach.
      unfold abs_reaches in Hreach.
      refine (clos_refl_trans_ind_right _ abs_step
        (fun X => match X with
         | mkACTr s0' Delta0' =>
             exists rho0 pi0, Delta0' rho0 pi0 /\
               forall cabs0, pool_matches_lin cabs0 pi0 ->
                 (exists rho_f cabs_f,
                   @trace_steps F F VF idImpl (mkTraceConfig s0' rho0 cabs0) (mkTraceConfig s rho_f cabs_f)) \/
                 (exists p f tl0 rho_f cabs_f, s = p ++ (TErr f :: nil ++ tl0) /\
                   @trace_steps F F VF idImpl (mkTraceConfig s0' rho0 cabs0) (mkTraceConfig (p ++ TErr f :: nil) rho_f cabs_f))
         end)
        (mkACTr s Delta') _ _ (mkACTr s0 Delta0) Hreach).
      - destruct (ac_nonempty Delta') as [rho0 [pi0 Hposs0]].
        exists rho0, pi0. split; auto.
        intros cabs0 Hmatch0. left. exists rho0, cabs0. apply rt_refl.
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
                     (mkTraceConfig (s0' ++ (TEvent (Build_ThreadEvent thr (InvEv f)) :: nil)) rho1
                        (TMap.add thr (Build_ThreadState f (Vis f (fun v => Ret v)) None) cabs0))).
          { apply TraceStepInv. econstructor; eauto. }
          assert (Hmatch1 : pool_matches_lin
                    (TMap.add thr (Build_ThreadState f (Vis f (fun v => Ret v)) None) cabs0)
                    (TMap.add thr (ls_inv f) pi00)).
          { intros t'. destruct (Pos.eq_dec t' thr); subst.
            - rewrite !TMap.gss. reflexivity.
            - rewrite !TMap.gso; auto. }
          destruct (Hcont1 _ Hmatch1) as
            [[rho_f [cabs_f Htail]] | [p [f0 [tl [rho_f [cabs_f [Heqp Htail]]]]]]].
          * left. exists rho_f, cabs_f.
            eapply rt_trans; [ apply rt_step; exact Hcabs1 | exact Htail ].
          * right. exists p, f0, tl, rho_f, cabs_f. split; [exact Heqp|].
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
                     (mkTraceConfig (s0' ++ (TEvent (Build_ThreadEvent thr (ResEv f ret)) :: nil)) rho1
                        (TMap.remove thr cabs0))).
          { apply TraceStepRet. econstructor; eauto. }
          assert (Hmatch1 : pool_matches_lin (TMap.remove thr cabs0) (TMap.remove thr pi00)).
          { intros t'. destruct (Pos.eq_dec t' thr); subst.
            - rewrite !TMap.grs. reflexivity.
            - rewrite !TMap.gro; auto. }
          destruct (Hcont1 _ Hmatch1) as
            [[rho_f [cabs_f Htail]] | [p [f0 [tl [rho_f [cabs_f [Heqp Htail]]]]]]].
          * left. exists rho_f, cabs_f.
            eapply rt_trans; [ apply rt_step; exact Hcabs1 | exact Htail ].
          * right. exists p, f0, tl, rho_f, cabs_f. split; [exact Heqp|].
            eapply rt_trans; [ apply rt_step; exact Hcabs1 | exact Htail ].
        + (* AbsStepSteps *)
          apply Hsub in Hposs1.
          inversion Hposs1 as [rho0 pi0 rho1' pi1' Hposs0 Hpstep]; subst.
          exists rho0, pi0. split; auto.
          intros cabs0 Hmatch0.
          destruct (poss_steps_shadow rho0 pi0 rho1 pi1 Hpstep cabs0 s1 Hmatch0)
            as [cabs1 [Hmatch1 Htrace1]].
          destruct (Hcont1 _ Hmatch1) as
            [[rho_f [cabs_f Htail]] | [p [f0 [tl [rho_f [cabs_f [Heqp Htail]]]]]]].
          * left. exists rho_f, cabs_f.
            eapply rt_trans; [ exact Htrace1 | exact Htail ].
          * right. exists p, f0, tl, rho_f, cabs_f. split; [exact Heqp|].
            eapply rt_trans; [ exact Htrace1 | exact Htail ].
        + (* AbsStepError: replay [Hsteps] (no error yet, via [poss_steps_shadow])
             then append exactly one more [TraceStepError] tagged with our own
             [f], rather than going through [poss_steps_error_shadow] (which
             would re-derive its own, only propositionally-equal, witness). *)
          exists rho, pi. split; auto.
          intros cabs0 Hmatch0.
          right.
          destruct (poss_steps_shadow rho pi rhoE piE Hsteps cabs0 s0' Hmatch0)
            as [cabs1 [Hmatch1 Htrace1]].
          pose proof (Hmatch1 t0) as Hm. rewrite Hlin in Hm. simpl in Hm.
          eassert (Hcabs2 : trace_step idImpl
                     (mkTraceConfig s0' rhoE cabs1)
                     (mkTraceConfig (s0' ++ TErr f :: nil) rhoE cabs1)).
          { eapply (TraceStepError idImpl s0' rhoE cabs1 f (Build_ThreadEvent t0 (InvEv f))
                      (Build_ThreadState f (Vis f (fun v => Ret v)) None)).
            - exact Hm.
            - econstructor. exact Herror. }
          destruct (abs_reaches_monotone _ _ Hyz) as [tl2 Heqtl2].
          simpl in Heqtl2.
          exists s0', f, tl2, rhoE, cabs1. split.
          * rewrite Heqtl2. rewrite <- app_assoc. reflexivity.
          * eapply rt_trans; [ exact Htrace1 | apply rt_step; exact Hcabs2 ].
    Qed.

    (* Lemma 5.3 (sound direction): the Threadpool Simulation (Definition
       5.2, mechanized as [TPSimulationSet.cal]) implies Compositional
       Linearizability (Definition 4.1, [CompLin.CompLin]). Combines Layer 1
       (produce a matching [abs_reaches] judgement) with Layer 2 (reify it
       into a single concrete execution of [idImpl]), matching the result
       against [ImplTracesClosed]. *)
    Theorem cal_to_CompLin :
      forall (sigma0 : State VE) (rho0 : State VF),
        cal M sigma0 rho0 -> CompLin.CompLin M sigma0 rho0.
    Proof.
      intros sigma0 rho0 Hcal s Htr.
      destruct Htr as [sigma' [c' Htrace]].
      pose proof (dom_match_init rho0) as Hdm0.
      destruct (TPSimulation_abs_reaches sigma0 (TMap.empty _) (ac_init rho0) Hcal Hdm0
                  s sigma' c' Htrace) as
        [[Delta' Hreach] | [s1 [f [tl [Delta' [Heqs Hreach]]]]]].
      - (* clean all the way to s *)
        destruct (abs_reaches_reify nil (ac_init rho0) s Delta' Hreach)
          as [rho00 [pi00 [Hposs00 Hcont]]].
        inversion Hposs00; subst.
        destruct (Hcont (TMap.empty _) pool_matches_lin_empty) as
          [[rho_f [cabs_f Htrace_final]] | [p [f0 [tl0 [rho_f [cabs_f [Heqp Htrace_final]]]]]]].
        + left. exists rho_f, cabs_f. exact Htrace_final.
        + right. exists p, f0, (TErr f0 :: nil ++ tl0). split.
          * exists rho_f, cabs_f. exact Htrace_final.
          * exact Heqp.
      - (* errors at s1, with s = s1 ++ tl *)
        destruct (abs_reaches_reify nil (ac_init rho0) (s1 ++ TErr f :: nil) Delta' Hreach)
          as [rho00 [pi00 [Hposs00 Hcont]]].
        inversion Hposs00; subst.
        destruct (Hcont (TMap.empty _) pool_matches_lin_empty) as
          [[rho_f [cabs_f Htrace_final]] | [p [f0 [tl0 [rho_f [cabs_f [Heqp Htrace_final]]]]]]].
        + (* reaches s1 ++ TErr f :: nil exactly *)
          right. exists s1, f, tl. split.
          * exists rho_f, cabs_f. exact Htrace_final.
          * reflexivity.
        + (* reaches an even earlier p ++ TErr f0 :: nil, with
             s1 ++ TErr f :: nil = p ++ (TErr f0 :: nil ++ tl0) *)
          assert (Htlnn : TErr f0 :: nil ++ tl0 <> (@nil (TraceItem F)))
            by (simpl; discriminate).
          destruct (trace_snoc_prefix p (TErr f0 :: nil ++ tl0) s1 (TErr f) Htlnn (eq_sym Heqp))
            as [q [Heqs1 Heqtl0]].
          right. exists p, f0, (q ++ tl). split.
          * exists rho_f, cabs_f. exact Htrace_final.
          * rewrite Heqs1. rewrite app_assoc. reflexivity.
    Qed.

  End Adequacy.

  (* Corollary: any verified layer implementation from [TPSimulationSet]
     (i.e., anything already proven correct against the Threadpool
     Simulation) is compositionally linearizable in the sense of
     Definition 4.1. *)
  Theorem layer_implementation_CompLin {L L' : layer_interface} (LI : layer_implementation_simulation L L') :
    CompLin.CompLin (TPSimulationSet.TPSimulation.li_impl LI) (li_init L) (li_init L').
  Proof.
    apply cal_to_CompLin. exact (TPSimulationSet.TPSimulation.li_correct LI).
  Qed.

  Definition LISim2LILin {L L' : TPSimulation.layer_interface} (M : TPSimulation.layer_implementation_simulation L L') : layer_implementation_linearizability L L' :=
  {|
    li_impl := TPSimulation.li_impl M;
    li_correct := layer_implementation_CompLin M;
  |}.

  Notation "| M |" := (LISim2LILin M).

End CompLinSound.
