Require Import Coq.Lists.List.
Require Import Coq.PArith.PArith.
Require Import Lia.
Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Eqdep.

Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import CompLin.
Require Import CompLinHComp.

(** Vertical Compositionality of Compositional Linearizability (Lemma 4.3,
    §4.3): [CompLin] (Definition 4.1) composes vertically, when an
    implementation is stacked on top of another one.

    The composition operator on [ModuleImpl]s itself ([implVComp]/[▶]) is
    defined here fresh, independent of the [TPSimulationSet]/[AbstractConfig]
    machinery of Definition 5.2, since this file only needs it to state
    compositionality directly for the trace semantics of [CompLin.v].

    Horizontal compositionality (Lemma 4.2) is in [CompLinHComp.v]. *)
Module CompLinVComp.
  Import Reg.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import Semantics.
  Import CompLin.CompLin.
  Import CompLinHComp.CompLinHComp.

  (** * Vertical composition of [ModuleImpl]s.

      [implEF ▶ implFG] stacks [implEF : E -> F] below [implFG : F -> G]:
      every F-operation [implFG] invokes is substituted, per-thread, by its
      implementation in [implEF]. *)
  CoFixpoint substProg
      {E F} (t : tid) (impl : ModuleImpl E F)
      {R} (p : Prog F R) : Prog E R :=
    match p with
    | Vis m k => Tau (bindSubstProg t impl (impl m t) k)
    | Ret r => Ret r
    | Tau p => Tau (substProg t impl p)
    end

  with bindSubstProg
      (t : tid) {E F} (impl : ModuleImpl E F)
      {R R'} (p : Prog E R) (k : R -> Prog F R') : Prog E R' :=
    match p with
    | Vis m' k' => Vis m' (fun r => bindSubstProg t impl (k' r) k)
    | Ret r => Tau (substProg t impl (k r))
    | Tau p => Tau (bindSubstProg t impl p k)
    end.

  Definition implVComp {E F G}
      (implEF : ModuleImpl E F) (implFG : ModuleImpl F G) : ModuleImpl E G :=
    fun g t => substProg t implEF (implFG g t).

  Notation "M ▶ N" := (implVComp M N) (at level 80, right associativity).

  (* Dependent-pair equations left behind by [inversion] on constructors
     with dependently-typed arguments ([Vis], [Build_ThreadState], [ResEv],
     trace items...). *)
  Ltac clean_existT :=
    repeat (try subst;
            match goal with
            | H : existT _ _ _ = existT _ _ _ |- _ => apply inj_pair2 in H
            end);
    try subst.

  (* Saturate equations between [Some]-wrapped thread states, thread-state
     records, programs, trace items and events, peeling dependent pairs as
     they appear, and discriminating impossible combinations. *)
  Ltac prog_eq_clean :=
    repeat match goal with
    | H : Some _ = None |- _ => discriminate H
    | H : None = Some _ |- _ => discriminate H
    | H : Vis _ _ = Ret _ |- _ => discriminate H
    | H : Ret _ = Vis _ _ |- _ => discriminate H
    | H : Vis _ _ = Tau _ |- _ => discriminate H
    | H : Tau _ = Vis _ _ |- _ => discriminate H
    | H : Ret _ = Tau _ |- _ => discriminate H
    | H : Tau _ = Ret _ |- _ => discriminate H
    | H : TEvent _ = TErr _ |- _ => discriminate H
    | H : TErr _ = TEvent _ |- _ => discriminate H
    | H : InvEv _ = ResEv _ _ |- _ => discriminate H
    | H : ResEv _ _ = InvEv _ |- _ => discriminate H
    | H : _ :: _ = _ :: _ |- _ => inversion H; clear H; clean_existT
    | H : Some _ = Some _ |- _ => inversion H; clear H; clean_existT
    | H : Build_ThreadState _ _ _ = Build_ThreadState _ _ _ |- _ =>
        inversion H; clear H; clean_existT
    | H : Vis _ _ = Vis _ _ |- _ => inversion H; clear H; clean_existT
    | H : Ret _ = Ret _ |- _ => inversion H; clear H; clean_existT
    | H : Tau _ = Tau _ |- _ => inversion H; clear H; clean_existT
    | H : TEvent _ = TEvent _ |- _ => inversion H; clear H; clean_existT
    | H : TErr _ = TErr _ |- _ => inversion H; clear H; clean_existT
    | H : Build_ThreadEvent _ _ = Build_ThreadEvent _ _ |- _ =>
        inversion H; clear H; clean_existT
    | H : InvEv _ = InvEv _ |- _ => inversion H; clear H; clean_existT
    | H : ResEv _ _ = ResEv _ _ |- _ => inversion H; clear H; clean_existT
    end.

  (** * One-step unfolding equations for [substProg]/[bindSubstProg]
        (guarded cofixpoints only compute under [PP]). *)
  Section SubstProgFacts.
    Context {E F : Op.t}.
    Context (t : tid) (impl : ModuleImpl E F).

    Lemma substProgVis {R} m (k : Sig.ar m -> Prog F R) :
      substProg t impl (Vis m k) = Tau (bindSubstProg t impl (impl m t) k).
    Proof.
      rewrite (PPid (substProg t impl (Vis m k))) at 1.
      unfold PP, substProg at 1. reflexivity.
    Qed.

    Lemma substProgRet {R} (r : R) :
      substProg t impl (Ret r) = Ret r.
    Proof.
      rewrite (PPid (substProg t impl (Ret r))) at 1.
      unfold PP, substProg at 1. reflexivity.
    Qed.

    Lemma substProgTau {R} (p : Prog F R) :
      substProg t impl (Tau p) = Tau (substProg t impl p).
    Proof.
      rewrite (PPid (substProg t impl (Tau p))) at 1.
      unfold PP, substProg at 1. reflexivity.
    Qed.

    Lemma bindSubstProgVis {R R'} m (k' : Sig.ar m -> Prog E R) (k : R -> Prog F R') :
      bindSubstProg t impl (Vis m k') k
      = Vis m (fun r => bindSubstProg t impl (k' r) k).
    Proof.
      rewrite (PPid (bindSubstProg t impl (Vis m k') k)) at 1.
      unfold PP, bindSubstProg at 1. reflexivity.
    Qed.

    Lemma bindSubstProgRet {R R'} (r : R) (k : R -> Prog F R') :
      bindSubstProg t impl (Ret r) k = Tau (substProg t impl (k r)).
    Proof.
      rewrite (PPid (bindSubstProg t impl (Ret r) k)) at 1.
      unfold PP, bindSubstProg at 1. reflexivity.
    Qed.

    Lemma bindSubstProgTau {R R'} (p : Prog E R) (k : R -> Prog F R') :
      bindSubstProg t impl (Tau p) k = Tau (bindSubstProg t impl p k).
    Proof.
      rewrite (PPid (bindSubstProg t impl (Tau p) k)) at 1.
      unfold PP, bindSubstProg at 1. reflexivity.
    Qed.

    (** Inversion principles: what the source program must have been, given
        the head constructor of its substitution. *)

    Lemma substProg_eq_ret {R} (p : Prog F R) r :
      substProg t impl p = Ret r -> p = Ret r.
    Proof.
      destruct p; intros H.
      - rewrite substProgVis in H; discriminate.
      - rewrite substProgRet in H. injection H as H. subst r0. reflexivity.
      - rewrite substProgTau in H; discriminate.
    Qed.

    Lemma substProg_eq_vis {R} (p : Prog F R) m κ :
      substProg t impl p = Vis m κ -> False.
    Proof.
      destruct p; intros H.
      - rewrite substProgVis in H; discriminate.
      - rewrite substProgRet in H; discriminate.
      - rewrite substProgTau in H; discriminate.
    Qed.

    Lemma substProg_eq_tau {R} (p : Prog F R) q :
      substProg t impl p = Tau q ->
      (exists m k, p = Vis m k /\ q = bindSubstProg t impl (impl m t) k)
      \/ (exists p', p = Tau p' /\ q = substProg t impl p').
    Proof.
      destruct p as [m0 k0 | r0 | p0]; intros H.
      - rewrite substProgVis in H. injection H as H. subst q.
        left. exists m0, k0. auto.
      - rewrite substProgRet in H; discriminate.
      - rewrite substProgTau in H. injection H as H. subst q.
        right. exists p0. auto.
    Qed.

    Lemma bindSubstProg_eq_ret {R R'} (p : Prog E R) (k : R -> Prog F R') r :
      bindSubstProg t impl p k = Ret r -> False.
    Proof.
      destruct p; intros H.
      - rewrite bindSubstProgVis in H; discriminate.
      - rewrite bindSubstProgRet in H; discriminate.
      - rewrite bindSubstProgTau in H; discriminate.
    Qed.

    Lemma bindSubstProg_eq_vis {R R'} (p : Prog E R) (k : R -> Prog F R') m κ :
      bindSubstProg t impl p k = Vis m κ ->
      exists k', p = Vis m k'
        /\ κ = (fun r => bindSubstProg t impl (k' r) k).
    Proof.
      destruct p as [m0 k0 | r0 | p0]; intros H.
      - rewrite bindSubstProgVis in H.
        inversion H; clean_existT.
        exists k0. auto.
      - rewrite bindSubstProgRet in H; discriminate.
      - rewrite bindSubstProgTau in H; discriminate.
    Qed.

    Lemma bindSubstProg_eq_tau {R R'} (p : Prog E R) (k : R -> Prog F R') q :
      bindSubstProg t impl p k = Tau q ->
      (exists r, p = Ret r /\ q = substProg t impl (k r))
      \/ (exists p', p = Tau p' /\ q = bindSubstProg t impl p' k).
    Proof.
      destruct p as [m0 k0 | r0 | p0]; intros H.
      - rewrite bindSubstProgVis in H; discriminate.
      - rewrite bindSubstProgRet in H. injection H as H. subst q.
        left. exists r0. auto.
      - rewrite bindSubstProgTau in H. injection H as H. subst q.
        right. exists p0. auto.
    Qed.
  End SubstProgFacts.

  (** * Splitting a [trace_steps] run around its trace growth.

      Built on the generic [TraceStepsAux] toolkit of [CompLinHComp]: a run
      from the initial (empty-trace, empty-pool) configuration can be cut
      at any prefix of its final trace, and in particular right around the
      step that emitted the final item. *)
  Section RunSplitting.
    Context {E F : Op.t}.
    Context {VE : @LTS E}.
    Context (N : ModuleImpl E F).

    (* From the initial configuration, an empty final trace forces the
       degenerate run: no [trace_step] applies to an empty pool without
       emitting a trace item. *)
    Lemma trace_steps_nil_run :
      forall (s0 : State VE) (X : @TraceConfig E F VE),
        trace_steps N (mkTraceConfig nil s0 (TMap.empty _)) X ->
        tc_trace X = nil ->
        X = mkTraceConfig nil s0 (TMap.empty _).
    Proof.
      intros s0 X Hrun Hnil.
      apply clos_rt_rt1n_iff in Hrun.
      inversion Hrun; subst; [reflexivity | exfalso].
      apply clos_rt_rt1n_iff in H0.
      destruct (trace_steps_monotone N _ _ H0) as [tl Htl].
      inversion H; subst; simpl in *.
      - (* inv: trace grew *)
        rewrite Htl in Hnil. simpl in Hnil. discriminate.
      - (* ret: trace grew *)
        rewrite Htl in Hnil. simpl in Hnil. discriminate.
      - (* ustep: empty pool has no thread *)
        destruct Hstep. rewrite TMap.gempty in Hfind. discriminate.
      - (* taustep: empty pool has no thread *)
        destruct Hstep. rewrite TMap.gempty in Hfind. discriminate.
      - (* error: empty pool has no thread *)
        rewrite TMap.gempty in Hfind. discriminate.
    Qed.

    (* Cut a run right around the step emitting the last trace item: a
       prefix run realizing exactly [w], the single [trace_step] emitting
       [e], and a trace-silent suffix run. *)
    Lemma trace_steps_split_last :
      forall (s0 : State VE) (X : @TraceConfig E F VE) w e,
        trace_steps N (mkTraceConfig nil s0 (TMap.empty _)) X ->
        tc_trace X = w ++ e :: nil ->
        exists Y1 Y2,
          trace_steps N (mkTraceConfig nil s0 (TMap.empty _)) Y1 /\
          tc_trace Y1 = w /\
          trace_step N Y1 Y2 /\
          tc_trace Y2 = w ++ e :: nil /\
          trace_steps N Y2 X.
    Proof.
      intros s0 X w e Hrun Htr.
      destruct (trace_steps_reach_length N _ _ Hrun (List.length w))
        as [Y [Hr1 [Hr2 Hlen]]].
      { simpl. lia. }
      { rewrite Htr, app_length. simpl. lia. }
      destruct (trace_steps_monotone N _ _ Hr2) as [tl Htl].
      assert (Hyw : tc_trace Y = w).
      { eapply prefix_eq_of_same_length with (t1 := tl) (t2 := e :: nil).
        - rewrite <- Htl. exact Htr.
        - exact Hlen. }
      destruct (trace_steps_single_growth_split N Y X e Hr2)
        as [Mid1 [Mid2 [Hs1 [Hm1 [Hst [Hm2 Hs2]]]]]].
      { rewrite Htr, Hyw. reflexivity. }
      exists Mid1, Mid2.
      repeat split; auto.
      - eapply rt_trans; eauto.
      - rewrite Hm1, Hyw. reflexivity.
      - rewrite Hm2, Hyw. reflexivity.
    Qed.

    (* Every prefix of a generated trace is itself realized along the run. *)
    Lemma trace_steps_prefix_run :
      forall (s0 : State VE) (X : @TraceConfig E F VE) w1 w2,
        trace_steps N (mkTraceConfig nil s0 (TMap.empty _)) X ->
        tc_trace X = w1 ++ w2 ->
        exists Y,
          trace_steps N (mkTraceConfig nil s0 (TMap.empty _)) Y /\
          tc_trace Y = w1.
    Proof.
      intros s0 X w1 w2 Hrun Htr.
      destruct (trace_steps_reach_length N _ _ Hrun (List.length w1))
        as [Y [Hr1 [Hr2 Hlen]]].
      { simpl. lia. }
      { rewrite Htr, app_length. lia. }
      destruct (trace_steps_monotone N _ _ Hr2) as [tl Htl].
      exists Y. split; auto.
      eapply prefix_eq_of_same_length with (t1 := tl) (t2 := w2).
      - rewrite <- Htl. exact Htr.
      - exact Hlen.
    Qed.
  End RunSplitting.

  (* Splitting a list around the last element of another: if [p ++ tl]
     is [w] extended by one final [e], then either [p] swallows all of
     [w ++ e :: nil], or [p] is a prefix of [w]. *)
  Lemma app_snoc_cases {A} :
    forall (p tl w : list A) (e : A),
      p ++ tl = w ++ e :: nil ->
      (p = w ++ e :: nil /\ tl = nil) \/ (exists tl2, w = p ++ tl2).
  Proof.
    intros p tl w e H.
    destruct tl as [| x tl'].
    - left. rewrite app_nil_r in H. auto.
    - right.
      assert (Hne : x :: tl' <> nil) by discriminate.
      destruct (exists_last Hne) as [tl2 [y Hy]].
      rewrite Hy, app_assoc in H.
      apply app_inj_tail in H as [H1 H2].
      subst. eauto.
  Qed.

  Lemma app_one_absurd {A} :
    forall (l : list A) (x : A), l ++ x :: nil = l -> False.
  Proof.
    intros l x H.
    apply (f_equal (@List.length A)) in H.
    rewrite app_length in H. simpl in H. lia.
  Qed.

  (** * Controlled destruction principles for the per-thread step
        relations. [inversion] on these dependently-indexed variants
        substitutes context variables unpredictably; these lemmas expose
        the same information as explicit existentials with stable names. *)
  Section StepCases.
    Context {E F : Op.t}.
    Context {VE : @LTS E}.

    Lemma ts_step_cases :
      forall (f' : Sig.op F) ev (s1 : State VE) ts1 s2 ts2,
        @ts_step E F VE f' ev s1 ts1 s2 ts2 ->
        (exists t m (k : Sig.ar m -> Prog E (Sig.ar f')),
            ev = Build_ThreadEvent t (InvEv m) /\
            ts1 = Build_ThreadState f' (Vis m k) None /\
            ts2 = Build_ThreadState f' (Vis m k) (Some m) /\
            Step VE ev s1 s2)
        \/ (exists t m (r : Sig.ar m) (k : Sig.ar m -> Prog E (Sig.ar f')),
            ev = Build_ThreadEvent t (ResEv m r) /\
            ts1 = Build_ThreadState f' (Vis m k) (Some m) /\
            ts2 = Build_ThreadState f' (k r) None /\
            Step VE ev s1 s2).
    Proof.
      destruct 1; [left | right]; repeat eexists; eauto.
    Qed.

    Lemma ts_error_cases :
      forall (f' : Sig.op F) ev (s : State VE) ts,
        @ts_error E F VE f' ev s ts ->
        exists t m (k : Sig.ar m -> Prog E (Sig.ar f')),
          ev = Build_ThreadEvent t (InvEv m) /\
          ts = Build_ThreadState f' (Vis m k) None /\
          Error VE ev s.
    Proof.
      destruct 1; repeat eexists; eauto.
    Qed.

    Lemma ts_taustep_cases :
      forall (ts1 ts2 : @ThreadState E F),
        ts_taustep ts1 ts2 ->
        exists f' (p : Prog E (Sig.ar f')) b,
          ts1 = Build_ThreadState f' (Tau p) b /\
          ts2 = Build_ThreadState f' p b.
    Proof.
      destruct 1; repeat eexists; eauto.
    Qed.

    (* Constructor-shaped introduction lemmas for pool usteps, keeping
       every argument explicit so no unstable names are needed. *)
    Lemma ustep_vis_inv :
      forall t (g : Sig.op F) (m : Sig.op E) k (s s' : State VE)
             (c : @ThreadPoolState E F),
        TMap.find t c = Some (Build_ThreadState g (Vis m k) None) ->
        Step VE (Build_ThreadEvent t (InvEv m)) s s' ->
        ustep (Build_ThreadEvent t (InvEv m)) s c s'
          (TMap.add t (Build_ThreadState g (Vis m k) (Some m)) c).
    Proof.
      intros t g m k s s' c Hfind Hstep.
      eapply UStep with (ts1 := Build_ThreadState g (Vis m k) None).
      - simpl. exact Hfind.
      - eapply ts_inv; eauto.
      - reflexivity.
    Qed.

    Lemma ustep_vis_res :
      forall t (g : Sig.op F) (m : Sig.op E) (r : Sig.ar m) k (s s' : State VE)
             (c : @ThreadPoolState E F),
        TMap.find t c = Some (Build_ThreadState g (Vis m k) (Some m)) ->
        Step VE (Build_ThreadEvent t (ResEv m r)) s s' ->
        ustep (Build_ThreadEvent t (ResEv m r)) s c s'
          (TMap.add t (Build_ThreadState g (k r) None) c).
    Proof.
      intros t g m r k s s' c Hfind Hstep.
      eapply UStep with (ts1 := Build_ThreadState g (Vis m k) (Some m)).
      - simpl. exact Hfind.
      - eapply ts_res; eauto.
      - reflexivity.
    Qed.

    (* Constructor-shaped introduction lemmas for whole [trace_step]s. *)
    Lemma trace_invstep_intro :
      forall (N : ModuleImpl E F) s (sigma : State VE) c t (f : Sig.op F),
        TMap.find t c = None ->
        trace_step N (mkTraceConfig s sigma c)
          (mkTraceConfig (s ++ TEvent (Build_ThreadEvent t (InvEv f)) :: nil)
             sigma (TMap.add t (Build_ThreadState f (N f t) None) c)).
    Proof.
      intros. eapply TraceStepInv. constructor; auto.
    Qed.

    Lemma trace_retstep_intro :
      forall (N : ModuleImpl E F) s (sigma : State VE) c t (f : Sig.op F)
             (r : Sig.ar f),
        TMap.find t c = Some (Build_ThreadState f (Ret r) None) ->
        trace_step N (mkTraceConfig s sigma c)
          (mkTraceConfig (s ++ TEvent (Build_ThreadEvent t (ResEv f r)) :: nil)
             sigma (TMap.remove t c)).
    Proof.
      intros. eapply TraceStepRet. constructor; auto.
    Qed.

    Lemma trace_taustep_intro :
      forall (N : ModuleImpl E F) s (sigma : State VE) c t (g : Sig.op F) p b,
        TMap.find t c = Some (Build_ThreadState g (Tau p) b) ->
        trace_step N (mkTraceConfig s sigma c)
          (mkTraceConfig s sigma (TMap.add t (Build_ThreadState g p b) c)).
    Proof.
      intros. eapply TraceStepTau. econstructor; eauto. constructor.
    Qed.

    Lemma trace_errstep_intro :
      forall (N : ModuleImpl E F) s (sigma : State VE) c t
             (g : Sig.op F) (m : Sig.op E) k,
        TMap.find t c = Some (Build_ThreadState g (Vis m k) None) ->
        Error VE (Build_ThreadEvent t (InvEv m)) sigma ->
        trace_step N (mkTraceConfig s sigma c)
          (mkTraceConfig (s ++ TErr g :: nil) sigma c).
    Proof.
      intros N s sigma c t g m k Hfind Herr.
      eapply TraceStepError with (ev := Build_ThreadEvent t (InvEv m)); simpl; eauto.
      eapply ts_err; eauto.
    Qed.
  End StepCases.

  (** * The core simulation.

      Everything below is one big fused induction over a run of the
      composite implementation [M1 ▶ M2] over [VE], from which we
      extract:
      - an [M1]-over-[VE] run producing an intermediate F-trace [w]
        (fed to [CompLin M1] afterwards), and
      - a *transformer* turning any [idImpl]-over-[VF] run realizing [w]
        (or erroring at a prefix of [w]) into an [M2]-over-[VF] run
        reproducing the composite's G-trace (or an error witness).

      The per-thread bookkeeping is a ghost state: a thread is [TgIdle]
      (not running any G-operation), [TgOut g p2] (running [g], currently
      executing overlay code of [M2], with residual [M2]-program [p2]), or
      [TgIn g f k] (running [g], currently inside the substituted [M1]-code
      for an F-operation [f], with [M2]-continuation [k]). *)
  Section VCompCore.
    Context {E F G : Op.t}.
    Context {VE : @LTS E} {VF : @LTS F}.
    Context (M1 : ModuleImpl E F) (M2 : ModuleImpl F G).
    Context (sigma0 : State VE) (rho0 : State VF).

    Definition cinit : @TraceConfig E G VE :=
      mkTraceConfig nil sigma0 (TMap.empty _).
    Definition m1init : @TraceConfig E F VE :=
      mkTraceConfig nil sigma0 (TMap.empty _).
    Definition dinit : @TraceConfig F F VF :=
      mkTraceConfig nil rho0 (TMap.empty _).
    Definition m2init : @TraceConfig F G VF :=
      mkTraceConfig nil rho0 (TMap.empty _).

    Variant tghost : Type :=
    | TgIdle
    | TgOut (g : Sig.op G) (p2 : Prog F (Sig.ar g))
    | TgIn (g : Sig.op G) (f : Sig.op F) (k : Sig.ar f -> Prog F (Sig.ar g)).

    Definition ghost := tid -> tghost.

    Definition gupd (Gh : ghost) (t : tid) (st : tghost) : ghost :=
      fun t' => if Pos.eq_dec t' t then st else Gh t'.

    Lemma gupd_same Gh t st : gupd Gh t st t = st.
    Proof. unfold gupd. destruct (Pos.eq_dec t t); congruence. Qed.

    Lemma gupd_other Gh t st t' : t' <> t -> gupd Gh t st t' = Gh t'.
    Proof. unfold gupd. intros. destruct (Pos.eq_dec t' t); congruence. Qed.

    (* Pass-1 invariant: how a composite thread decomposes into an
       [M1]-side thread. Outside [M1]-code, the composite program is a
       substituted residual [M2]-program and the [M1] pool has no entry;
       inside, the composite program is [M1]'s residual code bind-composed
       with the [M2]-continuation, and the [M1] pool tracks exactly that
       residual code and the pending-underlay flag. *)
    Variant thread_inv1 (t : tid)
        (c : @ThreadPoolState E G) (c1 : @ThreadPoolState E F) : tghost -> Prop :=
    | TI1_Idle :
        TMap.find t c = None ->
        TMap.find t c1 = None ->
        thread_inv1 t c c1 TgIdle
    | TI1_Out g p2 :
        TMap.find t c = Some (Build_ThreadState g (substProg t M1 p2) None) ->
        TMap.find t c1 = None ->
        thread_inv1 t c c1 (TgOut g p2)
    | TI1_In g f k p1 pd :
        TMap.find t c = Some (Build_ThreadState g (bindSubstProg t M1 p1 k) pd) ->
        TMap.find t c1 = Some (Build_ThreadState f p1 pd) ->
        (forall m, pd = Some m -> exists k1, p1 = Vis m k1) ->
        thread_inv1 t c c1 (TgIn g f k).

    Definition inv1 (Gh : ghost) (c : @ThreadPoolState E G)
        (c1 : @ThreadPoolState E F) : Prop :=
      forall t, thread_inv1 t c c1 (Gh t).

    (* Pass-2 invariant: how the given [idImpl]-over-[VF] pool [d] and the
       constructed [M2]-over-[VF] pool [c2] relate, per thread. While a
       thread is inside [M1]-code for [f] ([TgIn]), the [idImpl] thread for
       [f] progresses through its three-phase lifecycle (not yet invoked
       [f] on [VF] / invoked / answered with [v]), and the [M2] thread
       mirrors the [VF]-facing part of it exactly. *)
    Variant thread_inv2 (t : tid)
        (d : @ThreadPoolState F F) (c2 : @ThreadPoolState F G) : tghost -> Prop :=
    | TI2_Idle :
        TMap.find t d = None ->
        TMap.find t c2 = None ->
        thread_inv2 t d c2 TgIdle
    | TI2_Out g p2 :
        TMap.find t d = None ->
        TMap.find t c2 = Some (Build_ThreadState g p2 None) ->
        thread_inv2 t d c2 (TgOut g p2)
    | TI2_In1 g f k :
        TMap.find t d = Some (Build_ThreadState f (Vis f (fun v => Ret v)) None) ->
        TMap.find t c2 = Some (Build_ThreadState g (Vis f k) None) ->
        thread_inv2 t d c2 (TgIn g f k)
    | TI2_In2 g f k :
        TMap.find t d = Some (Build_ThreadState f (Vis f (fun v => Ret v)) (Some f)) ->
        TMap.find t c2 = Some (Build_ThreadState g (Vis f k) (Some f)) ->
        thread_inv2 t d c2 (TgIn g f k)
    | TI2_In3 g f k v :
        TMap.find t d = Some (Build_ThreadState f (Ret v) None) ->
        TMap.find t c2 = Some (Build_ThreadState g (k v) None) ->
        thread_inv2 t d c2 (TgIn g f k).

    Definition inv2 (Gh : ghost) (d : @ThreadPoolState F F)
        (c2 : @ThreadPoolState F G) : Prop :=
      forall t, thread_inv2 t d c2 (Gh t).

    (* Both per-thread invariants only inspect the pools at their own
       thread, so they transport along any pool updates elsewhere. *)
    Lemma thread_inv1_frame t c c1 c' c1' st :
      thread_inv1 t c c1 st ->
      TMap.find t c' = TMap.find t c ->
      TMap.find t c1' = TMap.find t c1 ->
      thread_inv1 t c' c1' st.
    Proof.
      destruct 1; intros Hc Hc1.
      - apply TI1_Idle; congruence.
      - apply TI1_Out; congruence.
      - eapply TI1_In; eauto; congruence.
    Qed.

    Lemma thread_inv2_frame t d c2 d' c2' st :
      thread_inv2 t d c2 st ->
      TMap.find t d' = TMap.find t d ->
      TMap.find t c2' = TMap.find t c2 ->
      thread_inv2 t d' c2' st.
    Proof.
      destruct 1; intros Hd Hc2.
      - apply TI2_Idle; congruence.
      - apply TI2_Out; congruence.
      - apply TI2_In1; congruence.
      - apply TI2_In2; congruence.
      - apply TI2_In3 with (v := v); congruence.
    Qed.

    Definition no_err (w : Trace F) : Prop :=
      forall f0, ~ In (TErr f0) w.

    (* The idImpl-run side condition fed to the transformer: the run
       realizes [w] on the nose, or errors at some prefix of [w]. *)
    Definition err_covers (u w : Trace F) : Prop :=
      u = w \/ exists p f0 tl, u = p ++ TErr f0 :: nil /\ w = p ++ tl.

    (* Terminal error outcome on the [M2] side: [M2] over [VF] can reach
       an error at some prefix of [s]. *)
    Definition m2_err_witness (s : Trace G) : Prop :=
      exists q g0 tl,
        ImplTraces M2 rho0 (q ++ TErr g0 :: nil) /\ s = q ++ tl.

    Lemma m2_err_witness_app s x :
      m2_err_witness s -> m2_err_witness (s ++ x).
    Proof.
      intros [q [g0 [tl [Hq Hs]]]]. subst s.
      exists q, g0, (tl ++ x). split; auto. rewrite app_assoc; auto.
    Qed.

    (* The transformer produced by the fused induction: any [idImpl]-run
       over [VF] realizing [w] up to error yields an [M2]-run over [VF]
       reproducing [s] (with the invariant [inv2] linking the final pools,
       so that the induction can keep extending it), or an error witness. *)
    Definition d_concl (Gh : ghost) (s : Trace G) (w : Trace F) : Prop :=
      forall u rho d,
        trace_steps idImpl dinit (mkTraceConfig u rho d) ->
        err_covers u w ->
        (u = w /\ no_err w /\
          exists c2,
            trace_steps M2 m2init (mkTraceConfig s rho c2) /\ inv2 Gh d c2)
        \/ m2_err_witness s.

    Lemma m2_traces_intro :
      forall x rho' c2',
        trace_steps M2 m2init (mkTraceConfig x rho' c2') ->
        ImplTraces M2 rho0 x.
    Proof.
      intros x rho' c2' H. exists rho', c2'. exact H.
    Qed.

    (* Trace-silent [idImpl] steps are [VF]-usteps of some in-flight
       thread ([idImpl] programs never contain [Tau]); each is mirrored as
       the corresponding [VF]-ustep of the [M2] pool, advancing that
       thread's phase in [inv2], while leaving trace and [M2]-trace alike
       unchanged. *)
    Lemma mirror_flat :
      forall (D D' : @TraceConfig F F VF),
        trace_steps idImpl D D' ->
        tc_trace D' = tc_trace D ->
        forall Gh s2 c2,
          inv2 Gh (tc_pool D) c2 ->
          exists c2',
            trace_steps M2 (mkTraceConfig s2 (tc_state D) c2)
                          (mkTraceConfig s2 (tc_state D') c2') /\
            inv2 Gh (tc_pool D') c2'.
    Proof.
      intros D D' Hrun.
      induction Hrun as [D D' Hstep | D | D Dm D' H1 IH1 H2 IH2];
        intros Heq Gh s2 c2 Hinv.
      - (* single step *)
        destruct Hstep as [sD sigmaD cD tD fD cD' HD
                          | sD sigmaD cD tD fD retD cD' HD
                          | sD sigmaD cD evD sigmaD' cD' HD
                          | sD sigmaD cD tD cD' HD
                          | sD sigmaD cD fD evD tsD HfindD HerrD]; simpl in *.
        + exfalso. eapply app_one_absurd; eauto.
        + exfalso. eapply app_one_absurd; eauto.
        + (* silent ustep *)
          destruct HD as [fts ts1 ts2 Hfind Hts Hupd].
          apply ts_step_cases in Hts.
          destruct Hts as [[t1 [m1 [k1 [Hev [Hts1 [Hts2 Hvf]]]]]]
                          |[t1 [m1 [r1 [k1 [Hev [Hts1 [Hts2 Hvf]]]]]]]];
            subst evD ts1 ts2 cD'; simpl in *.
          * (* [VF]-invocation of thread t1 *)
            pose proof (Hinv t1) as Ht.
            remember (Gh t1) as gst eqn:Heqgst.
            destruct Ht as [Hd0 Hc0 | g2 p2 Hd0 Hc0 | g2 f2 k2 Hd0 Hc0
                           | g2 f2 k2 Hd0 Hc0 | g2 f2 k2 v2 Hd0 Hc0];
              rewrite Hfind in Hd0; prog_eq_clean.
            (* only phase 1 survives *)
            eexists. split.
            { apply rt_step. eapply TraceStepU.
              eapply ustep_vis_inv; eauto. }
            { intros t'.
              destruct (Pos.eq_dec t' t1) as [-> | Hne].
              - rewrite <- Heqgst.
                apply TI2_In2; rewrite TMap.gss; reflexivity.
              - eapply thread_inv2_frame;
                  [apply Hinv | rewrite TMap.gso; auto | rewrite TMap.gso; auto]. }
          * (* [VF]-response to thread t1 *)
            pose proof (Hinv t1) as Ht.
            remember (Gh t1) as gst eqn:Heqgst.
            destruct Ht as [Hd0 Hc0 | g2 p2 Hd0 Hc0 | g2 f2 k2 Hd0 Hc0
                           | g2 f2 k2 Hd0 Hc0 | g2 f2 k2 v2 Hd0 Hc0];
              rewrite Hfind in Hd0; prog_eq_clean.
            (* only phase 2 survives *)
            eexists. split.
            { apply rt_step. eapply TraceStepU.
              eapply ustep_vis_res; eauto. }
            { intros t'.
              destruct (Pos.eq_dec t' t1) as [-> | Hne].
              - rewrite <- Heqgst.
                apply TI2_In3 with (v := r1); rewrite TMap.gss; reflexivity.
              - eapply thread_inv2_frame;
                  [apply Hinv | rewrite TMap.gso; auto | rewrite TMap.gso; auto]. }
        + (* silent taustep: impossible, idImpl programs have no Tau *)
          destruct HD as [ts1 ts2 Hfind Hts Hupd].
          apply ts_taustep_cases in Hts.
          destruct Hts as [f1 [p1 [b1 [Hts1 Hts2]]]]. subst ts1 ts2 cD'.
          pose proof (Hinv tD) as Ht.
          remember (Gh tD) as gst eqn:Heqgst.
          destruct Ht as [Hd0 Hc0 | g2 p2 Hd0 Hc0 | g2 f2 k2 Hd0 Hc0
                         | g2 f2 k2 Hd0 Hc0 | g2 f2 k2 v2 Hd0 Hc0];
            rewrite Hfind in Hd0; prog_eq_clean.
        + (* error step: grows the trace *)
          exfalso. eapply app_one_absurd; eauto.
      - (* refl *)
        exists c2. split; [apply rt_refl | exact Hinv].
      - (* trans *)
        assert (Hm : tc_trace Dm = tc_trace D).
        { eapply trace_steps_flat_mid with (A := D) (B := D'); eauto.
          eapply rt_trans; eauto. }
        destruct (IH1 Hm Gh s2 c2 Hinv) as [c2m [Hrun1 Hinv1']].
        assert (Hm2 : tc_trace D' = tc_trace Dm) by congruence.
        destruct (IH2 Hm2 Gh s2 c2m Hinv1') as [c2' [Hrun2 Hinv2']].
        exists c2'. split; [eapply rt_trans; eauto | exact Hinv2'].
    Qed.

    (* The [idImpl] step emitting an F-invocation event must be exactly
       the [invstep] of that thread on that operation. *)
    Lemma consume_inv_step :
      forall (Y1 Y2 : @TraceConfig F F VF) t f,
        trace_step idImpl Y1 Y2 ->
        tc_trace Y2 = tc_trace Y1 ++ TEvent (Build_ThreadEvent t (InvEv f)) :: nil ->
        tc_state Y2 = tc_state Y1 /\
        tc_pool Y2 = TMap.add t (Build_ThreadState f (Vis f (fun v => Ret v)) None)
                       (tc_pool Y1) /\
        TMap.find t (tc_pool Y1) = None.
    Proof.
      intros Y1 Y2 t f Hstep Htr.
      destruct Hstep as [sD sigmaD cD tD fD cD' HD
                        | sD sigmaD cD tD fD retD cD' HD
                        | sD sigmaD cD evD sigmaD' cD' HD
                        | sD sigmaD cD tD cD' HD
                        | sD sigmaD cD fD evD tsD HfindD HerrD]; simpl in *;
        try (exfalso; eapply app_one_absurd; symmetry; exact Htr);
        apply app_inv_head in Htr; prog_eq_clean.
      destruct HD as [Hfind Hupd]. subst cD'.
      repeat split; auto.
    Qed.

    (* The [idImpl] step emitting an F-response event must be exactly the
       [retstep] of that thread, whose pool entry already holds the
       response value. *)
    Lemma consume_ret_step :
      forall (Y1 Y2 : @TraceConfig F F VF) t f (v : Sig.ar f),
        trace_step idImpl Y1 Y2 ->
        tc_trace Y2 = tc_trace Y1 ++ TEvent (Build_ThreadEvent t (ResEv f v)) :: nil ->
        tc_state Y2 = tc_state Y1 /\
        tc_pool Y2 = TMap.remove t (tc_pool Y1) /\
        TMap.find t (tc_pool Y1) = Some (Build_ThreadState f (Ret v) None).
    Proof.
      intros Y1 Y2 t f v Hstep Htr.
      destruct Hstep as [sD sigmaD cD tD fD cD' HD
                        | sD sigmaD cD tD fD retD cD' HD
                        | sD sigmaD cD evD sigmaD' cD' HD
                        | sD sigmaD cD tD cD' HD
                        | sD sigmaD cD fD evD tsD HfindD HerrD]; simpl in *;
        try (exfalso; eapply app_one_absurd; symmetry; exact Htr);
        apply app_inv_head in Htr; prog_eq_clean.
      destruct HD as [Hfind Hupd]. subst cD'.
      repeat split; auto.
    Qed.

    (* The [idImpl] step emitting a [TErr f] marker exposes a thread whose
       pool entry is still at its pre-invocation phase together with the
       [VF]-error justifying it. *)
    Lemma consume_err_step :
      forall (Y1 Y2 : @TraceConfig F F VF) f,
        trace_step idImpl Y1 Y2 ->
        tc_trace Y2 = tc_trace Y1 ++ TErr f :: nil ->
        exists t' op k0,
          TMap.find t' (tc_pool Y1) = Some (Build_ThreadState f (Vis op k0) None) /\
          Error VF (Build_ThreadEvent t' (InvEv op)) (tc_state Y1).
    Proof.
      intros Y1 Y2 f Hstep Htr.
      destruct Hstep as [sD sigmaD cD tD fD cD' HD
                        | sD sigmaD cD tD fD retD cD' HD
                        | sD sigmaD cD evD sigmaD' cD' HD
                        | sD sigmaD cD tD cD' HD
                        | sD sigmaD cD fD evD tsD HfindD HerrD]; simpl in *;
        try (exfalso; eapply app_one_absurd; symmetry; exact Htr);
        apply app_inv_head in Htr; prog_eq_clean.
      apply ts_error_cases in HerrD.
      destruct HerrD as [t2 [m2 [k2 [Hev [Hts Herr2]]]]].
      subst evD tsD. simpl in *.
      exists t2, m2, k2. split; auto.
    Qed.

    (* Mirror an [idImpl]-side [VF]-error into the [M2] pool: the ghost
       state of the erroring thread pins its [M2] entry at [Vis f k], so
       the same [VF]-error makes the [M2] pool error, tagged with that
       thread's G-operation. *)
    Lemma mirror_err_step :
      forall Gh d c2 (rho1 : State VF) (s2 : Trace G) t' f0 op k0,
        inv2 Gh d c2 ->
        TMap.find t' d = Some (Build_ThreadState f0 (Vis op k0) None) ->
        Error VF (Build_ThreadEvent t' (InvEv op)) rho1 ->
        exists g0,
          trace_step M2 (mkTraceConfig s2 rho1 c2)
                        (mkTraceConfig (s2 ++ TErr g0 :: nil) rho1 c2).
    Proof.
      intros Gh d c2 rho1 s2 t' f0 op k0 Hinv Hfind Herr.
      pose proof (Hinv t') as Ht.
      remember (Gh t') as gst eqn:Heqgst.
      destruct Ht as [Hd0 Hc0 | g2 p2 Hd0 Hc0 | g2 f2 k2 Hd0 Hc0
                     | g2 f2 k2 Hd0 Hc0 | g2 f2 k2 v2 Hd0 Hc0];
        rewrite Hfind in Hd0; prog_eq_clean.
      (* only phase 1 survives *)
      exists g2.
      eapply trace_errstep_intro; eauto.
    Qed.

    (** The fused induction over the composite run (see the header of this
        section). Everything is extracted in one pass so that the
        universally-quantified [idImpl]-run transformer ([d_concl]) can be
        maintained *inductively*: when the composite emits a new F-event,
        the given [idImpl] run realizing the extended F-trace is split at
        its final event ([trace_steps_split_last]) into a realization of
        the old F-trace — handled by the induction hypothesis — followed by
        exactly that event and a trace-silent tail, which are mirrored into
        the [M2] run by the lemmas above. *)
    Lemma vcomp_main :
      forall X : @TraceConfig E G VE,
        trace_steps (implVComp M1 M2) cinit X ->
        exists w c1 Gh,
          trace_steps M1 m1init (mkTraceConfig w (tc_state X) c1) /\
          inv1 Gh (tc_pool X) c1 /\
          d_concl Gh (tc_trace X) w.
    Proof.
      intros X Hrun.
      apply clos_rt_rtn1_iff in Hrun.
      induction Hrun as [| Xp X Hstep Hrun IH].
      - (* base: the empty run *)
        exists nil, (TMap.empty _), (fun _ => TgIdle).
        split; [| split].
        + apply rt_refl.
        + intros t'. apply TI1_Idle; apply TMap.gempty.
        + intros u rho d Hd Hcov.
          destruct Hcov as [-> | [p [f0 [tl [Hu Hnil]]]]].
          * (* u = nil: the degenerate idImpl run *)
            left.
            pose proof (trace_steps_nil_run idImpl rho0 _ Hd eq_refl) as Hnil2.
            inversion Hnil2. subst rho d.
            split; [reflexivity | split].
            -- intros f1 Hin. destruct Hin.
            -- exists (TMap.empty _). split.
               ++ apply rt_refl.
               ++ intros t'. apply TI2_Idle; apply TMap.gempty.
          * (* u = p ++ [TErr f0] with nil = p ++ tl: impossible *)
            exfalso.
            symmetry in Hnil. apply app_eq_nil in Hnil as [Hp Htl]. subst p tl.
            simpl in Hu. subst u.
            destruct (trace_steps_split_last idImpl rho0 _ nil (TErr f0) Hd eq_refl)
              as [Y1 [Y2 [HY1 [HtY1 [Hst1 [HtY2 _]]]]]].
            pose proof (trace_steps_nil_run idImpl rho0 Y1 HY1 HtY1) as HY1eq.
            rewrite HY1eq in Hst1.
            inversion Hst1; subst; simpl in *.
            -- prog_eq_clean.
            -- prog_eq_clean.
            -- match goal with HH : ustep _ _ _ _ _ |- _ =>
                 destruct HH as [f1 ts1 ts2 Hf1 Hts1 Hup1] end.
               rewrite TMap.gempty in Hf1. discriminate.
            -- match goal with HH : taustep _ _ _ |- _ =>
                 destruct HH as [ts1 ts2 Hf1 Hts1 Hup1] end.
               rewrite TMap.gempty in Hf1. discriminate.
            -- match goal with HH : TMap.find _ (TMap.empty _) = Some _ |- _ =>
                 rewrite TMap.gempty in HH; discriminate end.
      - (* inductive step: one more composite step *)
        destruct IH as [w [c1 [Gh [Hm1 [Hinv1 Hdc]]]]].
        destruct Hstep as [s sigma c t g c' HD
                          | s sigma c t g r c' HD
                          | s sigma c ev sigma' c' HD
                          | s sigma c t c' HD
                          | s sigma c gT ev ts Hfind Herror]; simpl in *.
        + (* composite invstep at the G level *)
          destruct HD as [Hfind Hupd]. subst c'.
          pose proof (Hinv1 t) as Ht1.
          remember (Gh t) as gst eqn:Hgst.
          destruct Ht1 as [Hc0 Hc10 | g2 p2 Hc0 Hc10 | g2 f2 k2 p1 pd Hc0 Hc10 Hpd];
            try congruence.
          exists w, c1, (gupd Gh t (TgOut g (M2 g t))).
          split; [| split].
          * exact Hm1.
          * intros t'.
            destruct (Pos.eq_dec t' t) as [-> | Hne].
            -- rewrite gupd_same. apply TI1_Out.
               ++ rewrite TMap.gss. reflexivity.
               ++ exact Hc10.
            -- rewrite gupd_other; auto.
               eapply thread_inv1_frame;
                 [apply Hinv1 | rewrite TMap.gso; auto | reflexivity].
          * intros u rho d HDu Hcov.
            destruct (Hdc u rho d HDu Hcov)
              as [[Hu [Hnoerr [c2 [Hm2 Hinv2]]]] | Herr].
            -- left. split; [exact Hu | split; [exact Hnoerr |]].
               pose proof (Hinv2 t) as Ht2. rewrite <- Hgst in Ht2.
               inversion Ht2; subst.
               match goal with HH : TMap.find t c2 = None |- _ =>
                 rename HH into Hc2 end.
               match goal with HH : TMap.find t d = None |- _ =>
                 rename HH into Hd2 end.
               exists (TMap.add t (Build_ThreadState g (M2 g t) None) c2).
               split.
               ++ eapply rt_trans; [exact Hm2 |]. apply rt_step.
                  apply trace_invstep_intro. exact Hc2.
               ++ intros t'.
                  destruct (Pos.eq_dec t' t) as [-> | Hne].
                  ** rewrite gupd_same. apply TI2_Out.
                     --- exact Hd2.
                     --- rewrite TMap.gss. reflexivity.
                  ** rewrite gupd_other; auto.
                     eapply thread_inv2_frame;
                       [apply Hinv2 | reflexivity | rewrite TMap.gso; auto].
            -- right. apply m2_err_witness_app. exact Herr.
        + (* composite retstep at the G level *)
          destruct HD as [Hfind Hupd]. subst c'.
          pose proof (Hinv1 t) as Ht1.
          remember (Gh t) as gst eqn:Hgst.
          destruct Ht1 as [Hc0 Hc10 | g2 p2 Hc0 Hc10 | g2 f2 k2 p1 pd Hc0 Hc10 Hpd].
          * congruence.
          * (* TgOut, with p2 = Ret r *)
            rewrite Hfind in Hc0. inversion Hc0; clean_existT.
            match goal with
            | HH : Ret _ = substProg _ _ _ |- _ =>
                symmetry in HH; apply substProg_eq_ret in HH; subst p2
            | HH : substProg _ _ _ = Ret _ |- _ =>
                apply substProg_eq_ret in HH; subst p2
            end.
            exists w, c1, (gupd Gh t TgIdle).
            split; [| split].
            -- exact Hm1.
            -- intros t'.
               destruct (Pos.eq_dec t' t) as [-> | Hne].
               ++ rewrite gupd_same. apply TI1_Idle.
                  ** rewrite TMap.grs. reflexivity.
                  ** exact Hc10.
               ++ rewrite gupd_other; auto.
                  eapply thread_inv1_frame;
                    [apply Hinv1 | rewrite TMap.gro; auto | reflexivity].
            -- intros u rho d HDu Hcov.
               destruct (Hdc u rho d HDu Hcov)
                 as [[Hu [Hnoerr [c2 [Hm2 Hinv2]]]] | Herr].
               ++ left. split; [exact Hu | split; [exact Hnoerr |]].
                  pose proof (Hinv2 t) as Ht2. rewrite <- Hgst in Ht2.
                  inversion Ht2; subst; clean_existT.
                  match goal with HH : TMap.find t c2 = Some _ |- _ =>
                    rename HH into Hc2 end.
                  match goal with HH : TMap.find t d = None |- _ =>
                    rename HH into Hd2 end.
                  exists (TMap.remove t c2).
                  split.
                  ** eapply rt_trans; [exact Hm2 |]. apply rt_step.
                     apply trace_retstep_intro. exact Hc2.
                  ** intros t'.
                     destruct (Pos.eq_dec t' t) as [-> | Hne].
                     --- rewrite gupd_same. apply TI2_Idle;
                           [exact Hd2 | rewrite TMap.grs; reflexivity].
                     --- rewrite gupd_other; auto.
                         eapply thread_inv2_frame;
                           [apply Hinv2 | reflexivity | rewrite TMap.gro; auto].
               ++ right. apply m2_err_witness_app. exact Herr.
          * (* TgIn: the composite program cannot be a bare [Ret] *)
            rewrite Hfind in Hc0. inversion Hc0; clean_existT.
            match goal with
            | HH : Ret _ = bindSubstProg _ _ _ _ |- _ =>
                symmetry in HH; apply bindSubstProg_eq_ret in HH; destruct HH
            | HH : bindSubstProg _ _ _ _ = Ret _ |- _ =>
                apply bindSubstProg_eq_ret in HH; destruct HH
            end.
        + (* composite ustep on VE *)
          destruct HD as [fG ts1 ts2 Hfindc Hts Hupd].
          apply ts_step_cases in Hts.
          destruct Hts as [[t1 [m1 [k1 [Hev [Hts1 [Hts2 Hvf]]]]]]
                          |[t1 [m1 [r1 [k1 [Hev [Hts1 [Hts2 Hvf]]]]]]]];
            subst ev ts1 ts2 c'; simpl in *.
          * (* underlay invocation *)
            pose proof (Hinv1 t1) as Ht1.
            remember (Gh t1) as gst eqn:Hgst.
            destruct Ht1 as [Hc0 Hc10 | g2 p2 Hc0 Hc10 | g2 f2 k2 p1 pd Hc0 Hc10 Hpd].
            -- congruence.
            -- (* TgOut: substProg is never a Vis *)
               rewrite Hfindc in Hc0. inversion Hc0; clean_existT.
               match goal with
               | HH : Vis _ _ = substProg _ _ _ |- _ =>
                   symmetry in HH; apply substProg_eq_vis in HH; destruct HH
               | HH : substProg _ _ _ = Vis _ _ |- _ =>
                   apply substProg_eq_vis in HH; destruct HH
               end.
            -- (* TgIn *)
               rewrite Hfindc in Hc0. inversion Hc0; clean_existT.
               match goal with
               | HH : Vis _ _ = bindSubstProg _ _ _ _ |- _ => symmetry in HH
               | HH : bindSubstProg _ _ _ _ = Vis _ _ |- _ => idtac
               end.
               match goal with
               | HH : bindSubstProg _ _ _ _ = Vis _ _ |- _ =>
                   apply bindSubstProg_eq_vis in HH;
                   destruct HH as [k1' [Hp1 Hk1]]
               end.
               subst p1 k1.
               exists w, (TMap.add t1 (Build_ThreadState f2 (Vis m1 k1') (Some m1)) c1), Gh.
               split; [| split].
               ++ eapply rt_trans; [exact Hm1 |]. apply rt_step.
                  eapply TraceStepU. eapply ustep_vis_inv; eauto.
               ++ intros t'.
                  destruct (Pos.eq_dec t' t1) as [-> | Hne].
                  ** rewrite <- Hgst.
                     eapply TI1_In with (p1 := Vis m1 k1') (pd := Some m1).
                     --- rewrite TMap.gss. rewrite bindSubstProgVis. reflexivity.
                     --- rewrite TMap.gss. reflexivity.
                     --- intros m' Hm'. inversion Hm'. subst m'.
                         exists k1'. reflexivity.
                  ** eapply thread_inv1_frame;
                       [apply Hinv1 | rewrite TMap.gso; auto | rewrite TMap.gso; auto].
               ++ exact Hdc.
          * (* underlay response *)
            pose proof (Hinv1 t1) as Ht1.
            remember (Gh t1) as gst eqn:Hgst.
            destruct Ht1 as [Hc0 Hc10 | g2 p2 Hc0 Hc10 | g2 f2 k2 p1 pd Hc0 Hc10 Hpd].
            -- congruence.
            -- (* TgOut: pending flag mismatch *)
               rewrite Hfindc in Hc0. inversion Hc0.
            -- (* TgIn *)
               rewrite Hfindc in Hc0. inversion Hc0; clean_existT.
               match goal with
               | HH : Vis _ _ = bindSubstProg _ _ _ _ |- _ => symmetry in HH
               | HH : bindSubstProg _ _ _ _ = Vis _ _ |- _ => idtac
               end.
               match goal with
               | HH : bindSubstProg _ _ _ _ = Vis _ _ |- _ =>
                   apply bindSubstProg_eq_vis in HH;
                   destruct HH as [k1' [Hp1 Hk1]]
               end.
               subst p1 k1.
               exists w, (TMap.add t1 (Build_ThreadState f2 (k1' r1) None) c1), Gh.
               split; [| split].
               ++ eapply rt_trans; [exact Hm1 |]. apply rt_step.
                  eapply TraceStepU. eapply ustep_vis_res; eauto.
               ++ intros t'.
                  destruct (Pos.eq_dec t' t1) as [-> | Hne].
                  ** rewrite <- Hgst.
                     eapply TI1_In with (p1 := k1' r1) (pd := None).
                     --- rewrite TMap.gss. reflexivity.
                     --- rewrite TMap.gss. reflexivity.
                     --- intros m' Hm'. discriminate Hm'.
                  ** eapply thread_inv1_frame;
                       [apply Hinv1 | rewrite TMap.gso; auto | rewrite TMap.gso; auto].
               ++ exact Hdc.
        + (* composite taustep *)
          destruct HD as [ts1 ts2 Hfindc Hts Hupd].
          apply ts_taustep_cases in Hts.
          destruct Hts as [gT0 [pT [bT [Hts1 Hts2]]]]. subst ts1 ts2 c'.
          pose proof (Hinv1 t) as Ht1.
          remember (Gh t) as gst eqn:Hgst.
          destruct Ht1 as [Hc0 Hc10 | g2 p2 Hc0 Hc10 | g2 f2 k2 p1 pd Hc0 Hc10 Hpd].
          * congruence.
          * (* TgOut: an M2-level step *)
            pose (gcur := g2).
            rewrite Hfindc in Hc0. inversion Hc0; clean_existT.
            match goal with
            | HH : Tau _ = substProg _ _ _ |- _ => symmetry in HH
            | HH : substProg _ _ _ = Tau _ |- _ => idtac
            end.
            match goal with
            | HH : substProg _ _ _ = Tau _ |- _ =>
                apply substProg_eq_tau in HH;
                destruct HH as [[f2 [k2 [Hp2 Hq]]] | [p2' [Hp2 Hq]]]
            end.
            -- (* SEGMENT ENTRY: p2 = Vis f2 k2 *)
               subst p2 pT.
               exists (w ++ TEvent (Build_ThreadEvent t (InvEv f2)) :: nil),
                      (TMap.add t (Build_ThreadState f2 (M1 f2 t) None) c1),
                      (gupd Gh t (TgIn gcur f2 k2)).
               split; [| split].
               ++ eapply rt_trans; [exact Hm1 |]. apply rt_step.
                  apply trace_invstep_intro. exact Hc10.
               ++ intros t'.
                  destruct (Pos.eq_dec t' t) as [-> | Hne].
                  ** rewrite gupd_same.
                     eapply TI1_In with (p1 := M1 f2 t) (pd := None).
                     --- rewrite TMap.gss. reflexivity.
                     --- rewrite TMap.gss. reflexivity.
                     --- intros m' Hm'. discriminate Hm'.
                  ** rewrite gupd_other; auto.
                     eapply thread_inv1_frame;
                       [apply Hinv1 | rewrite TMap.gso; auto | rewrite TMap.gso; auto].
               ++ (* d_concl for the extended F-trace *)
                  assert (HA : forall rho1 d1,
                      trace_steps idImpl dinit
                        (mkTraceConfig
                           (w ++ TEvent (Build_ThreadEvent t (InvEv f2)) :: nil)
                           rho1 d1) ->
                      (no_err w /\
                       exists c2,
                         trace_steps M2 m2init (mkTraceConfig s rho1 c2) /\
                         inv2 (gupd Gh t (TgIn gcur f2 k2)) d1 c2)
                      \/ m2_err_witness s).
                  { intros rho1 d1 HD1.
                    destruct (trace_steps_split_last idImpl rho0 _ w _ HD1 eq_refl)
                      as [Y1 [Y2 [HY1 [HtY1 [Hst1 [HtY2 Hpost]]]]]].
                    destruct Y1 as [uY1 rhoY1 dY1]. simpl in HtY1. subst uY1.
                    destruct (Hdc w rhoY1 dY1 HY1 (or_introl eq_refl))
                      as [[_ [Hnoerr [c2 [Hm2 Hinv2]]]] | Herr]; [| right; exact Herr].
                    left. split; [exact Hnoerr |].
                    destruct (consume_inv_step _ _ _ _ Hst1 HtY2)
                      as [HstY2 [HpY2 HfY2]].
                    destruct Y2 as [uY2 rhoY2 dY2]. simpl in *.
                    subst uY2 rhoY2 dY2.
                    assert (Hinv2' : inv2 (gupd Gh t (TgIn gcur f2 k2))
                        (TMap.add t
                           (Build_ThreadState f2 (Vis f2 (fun v => Ret v)) None) dY1)
                        c2).
                    { intros t'.
                      destruct (Pos.eq_dec t' t) as [-> | Hne].
                      - rewrite gupd_same.
                        pose proof (Hinv2 t) as Ht2. rewrite <- Hgst in Ht2.
                        inversion Ht2; subst; clean_existT.
                        apply TI2_In1.
                        + rewrite TMap.gss. reflexivity.
                        + assumption.
                      - rewrite gupd_other; auto.
                        eapply thread_inv2_frame;
                          [apply Hinv2 | rewrite TMap.gso; auto | reflexivity]. }
                    destruct (mirror_flat _ _ Hpost eq_refl
                                (gupd Gh t (TgIn gcur f2 k2)) s c2 Hinv2')
                      as [c2' [HmF HinvF]].
                    simpl in HmF.
                    exists c2'. split; [| exact HinvF].
                    eapply rt_trans; [exact Hm2 | exact HmF]. }
                  intros u rho d HDu Hcov.
                  destruct Hcov as [-> | [p [f0 [tl [Hu Hw']]]]].
                  ** (* u realizes the extended trace *)
                     destruct (HA rho d HDu)
                       as [[Hnoerr [c2 [Hm2 Hinv2]]] | Herr];
                       [| right; exact Herr].
                     left. split; [reflexivity | split].
                     --- intros f1 Hin. apply in_app_or in Hin.
                         destruct Hin as [Hin | [Hin | Hin]];
                           [eapply Hnoerr; eauto | discriminate Hin | destruct Hin].
                     --- exists c2. split; [exact Hm2 | exact Hinv2].
                  ** (* u errors at a prefix *)
                     subst u.
                     destruct (app_snoc_cases p tl w
                                 (TEvent (Build_ThreadEvent t (InvEv f2)))
                                 (eq_sym Hw'))
                       as [[Hp Htl] | [tl2 Hw2]].
                     --- (* the error strikes right after the full trace *)
                         subst p tl.
                         destruct (trace_steps_split_last idImpl rho0 _ _
                                     (TErr f0) HDu eq_refl)
                           as [Z1 [Z2 [HZ1 [HtZ1 [HstZ [HtZ2 _]]]]]].
                         destruct Z1 as [uZ1 rhoZ1 dZ1]. simpl in HtZ1. subst uZ1.
                         destruct (HA rhoZ1 dZ1 HZ1)
                           as [[Hnoerr [c2 [Hm2 Hinv2]]] | Herr];
                           [| right; exact Herr].
                         destruct (consume_err_step _ _ _ HstZ HtZ2)
                           as [t2 [op2 [k02 [Hfind2 Herr2]]]].
                         simpl in Hfind2, Herr2.
                         destruct (mirror_err_step _ _ _ rhoZ1 s _ _ _ _
                                     Hinv2 Hfind2 Herr2) as [g0 Hstep2].
                         right. exists s, g0, nil. split.
                         +++ eapply m2_traces_intro.
                             eapply rt_trans; [exact Hm2 |].
                             apply rt_step. exact Hstep2.
                         +++ rewrite app_nil_r. reflexivity.
                     --- (* the error strikes within the old trace *)
                         assert (Hcov' : err_covers (p ++ TErr f0 :: nil) w)
                           by (right; exists p, f0, tl2; auto).
                         destruct (Hdc _ rho d HDu Hcov')
                           as [[Hu' [Hnoerr _]] | Herr].
                         +++ exfalso. eapply (Hnoerr f0). rewrite <- Hu'.
                             apply in_or_app. right. left. reflexivity.
                         +++ right. exact Herr.
            -- (* M2-LEVEL TAU: p2 = Tau p2' *)
               subst p2 pT.
               exists w, c1, (gupd Gh t (TgOut gcur p2')).
               split; [| split].
               ++ exact Hm1.
               ++ intros t'.
                  destruct (Pos.eq_dec t' t) as [-> | Hne].
                  ** rewrite gupd_same. apply TI1_Out.
                     --- rewrite TMap.gss. reflexivity.
                     --- exact Hc10.
                  ** rewrite gupd_other; auto.
                     eapply thread_inv1_frame;
                       [apply Hinv1 | rewrite TMap.gso; auto | reflexivity].
               ++ intros u rho d HDu Hcov.
                  destruct (Hdc u rho d HDu Hcov)
                    as [[Hu [Hnoerr [c2 [Hm2 Hinv2]]]] | Herr];
                    [| right; exact Herr].
                  left. split; [exact Hu | split; [exact Hnoerr |]].
                  pose proof (Hinv2 t) as Ht2. rewrite <- Hgst in Ht2.
                  inversion Ht2; subst; clean_existT.
                  match goal with HH : TMap.find t c2 = Some _ |- _ =>
                    rename HH into Hc2 end.
                  match goal with HH : TMap.find t d = None |- _ =>
                    rename HH into Hd2 end.
                  eexists. split.
                  ** eapply rt_trans; [exact Hm2 |]. apply rt_step.
                     eapply trace_taustep_intro. exact Hc2.
                  ** intros t'.
                     destruct (Pos.eq_dec t' t) as [-> | Hne].
                     --- rewrite gupd_same. apply TI2_Out.
                         +++ exact Hd2.
                         +++ rewrite TMap.gss. reflexivity.
                     --- rewrite gupd_other; auto.
                         eapply thread_inv2_frame;
                           [apply Hinv2 | reflexivity | rewrite TMap.gso; auto].
          * (* TgIn: an M1-level step *)
            pose (gcur := g2).
            rewrite Hfindc in Hc0. inversion Hc0; clean_existT.
            match goal with
            | HH : Tau _ = bindSubstProg _ _ _ _ |- _ => symmetry in HH
            | HH : bindSubstProg _ _ _ _ = Tau _ |- _ => idtac
            end.
            match goal with
            | HH : bindSubstProg _ _ _ _ = Tau _ |- _ =>
                apply bindSubstProg_eq_tau in HH;
                destruct HH as [[v [Hp1 Hq]] | [p1' [Hp1 Hq]]]
            end.
            -- (* SEGMENT EXIT: p1 = Ret v *)
               subst p1 pT.
               (* the pending flag must be clear *)
               match type of Hc10 with
               | _ = Some (Build_ThreadState _ _ ?pdv) =>
                   destruct pdv as [m0 |] eqn:Hpdv
               end.
               { destruct (Hpd m0 eq_refl) as [kx Hkx]. discriminate Hkx. }
               exists (w ++ TEvent (Build_ThreadEvent t (ResEv f2 v)) :: nil),
                      (TMap.remove t c1),
                      (gupd Gh t (TgOut gcur (k2 v))).
               split; [| split].
               ++ eapply rt_trans; [exact Hm1 |]. apply rt_step.
                  apply trace_retstep_intro. exact Hc10.
               ++ intros t'.
                  destruct (Pos.eq_dec t' t) as [-> | Hne].
                  ** rewrite gupd_same. apply TI1_Out.
                     --- rewrite TMap.gss. reflexivity.
                     --- rewrite TMap.grs. reflexivity.
                  ** rewrite gupd_other; auto.
                     eapply thread_inv1_frame;
                       [apply Hinv1 | rewrite TMap.gso; auto | rewrite TMap.gro; auto].
               ++ (* d_concl for the extended F-trace *)
                  assert (HA : forall rho1 d1,
                      trace_steps idImpl dinit
                        (mkTraceConfig
                           (w ++ TEvent (Build_ThreadEvent t (ResEv f2 v)) :: nil)
                           rho1 d1) ->
                      (no_err w /\
                       exists c2,
                         trace_steps M2 m2init (mkTraceConfig s rho1 c2) /\
                         inv2 (gupd Gh t (TgOut gcur (k2 v))) d1 c2)
                      \/ m2_err_witness s).
                  { intros rho1 d1 HD1.
                    destruct (trace_steps_split_last idImpl rho0 _ w _ HD1 eq_refl)
                      as [Y1 [Y2 [HY1 [HtY1 [Hst1 [HtY2 Hpost]]]]]].
                    destruct Y1 as [uY1 rhoY1 dY1]. simpl in HtY1. subst uY1.
                    destruct (Hdc w rhoY1 dY1 HY1 (or_introl eq_refl))
                      as [[_ [Hnoerr [c2 [Hm2 Hinv2]]]] | Herr]; [| right; exact Herr].
                    left. split; [exact Hnoerr |].
                    destruct (consume_ret_step _ _ _ _ _ Hst1 HtY2)
                      as [HstY2 [HpY2 Hfd]].
                    destruct Y2 as [uY2 rhoY2 dY2]. simpl in *.
                    subst uY2 rhoY2 dY2.
                    assert (Hinv2' : inv2 (gupd Gh t (TgOut gcur (k2 v)))
                        (TMap.remove t dY1) c2).
                    { intros t'.
                      destruct (Pos.eq_dec t' t) as [-> | Hne].
                      - rewrite gupd_same.
                        pose proof (Hinv2 t) as Ht2. rewrite <- Hgst in Ht2.
                        pose proof (eq_sym Hfd) as Hfd'.
                        inversion Ht2; subst; clean_existT;
                          match goal with
                          | HH : TMap.find t dY1 = Some _ |- _ =>
                              rewrite <- Hfd' in HH; prog_eq_clean
                          end.
                        apply TI2_Out.
                        + rewrite TMap.grs. reflexivity.
                        + assumption.
                      - rewrite gupd_other; auto.
                        eapply thread_inv2_frame;
                          [apply Hinv2 | rewrite TMap.gro; auto | reflexivity]. }
                    destruct (mirror_flat _ _ Hpost eq_refl
                                (gupd Gh t (TgOut gcur (k2 v))) s c2 Hinv2')
                      as [c2' [HmF HinvF]].
                    simpl in HmF.
                    exists c2'. split; [| exact HinvF].
                    eapply rt_trans; [exact Hm2 | exact HmF]. }
                  intros u rho d HDu Hcov.
                  destruct Hcov as [-> | [p [f0 [tl [Hu Hw']]]]].
                  ** destruct (HA rho d HDu)
                       as [[Hnoerr [c2 [Hm2 Hinv2]]] | Herr];
                       [| right; exact Herr].
                     left. split; [reflexivity | split].
                     --- intros f1 Hin. apply in_app_or in Hin.
                         destruct Hin as [Hin | [Hin | Hin]];
                           [eapply Hnoerr; eauto | discriminate Hin | destruct Hin].
                     --- exists c2. split; [exact Hm2 | exact Hinv2].
                  ** subst u.
                     destruct (app_snoc_cases p tl w
                                 (TEvent (Build_ThreadEvent t (ResEv f2 v)))
                                 (eq_sym Hw'))
                       as [[Hp Htl] | [tl2 Hw2]].
                     --- subst p tl.
                         destruct (trace_steps_split_last idImpl rho0 _ _
                                     (TErr f0) HDu eq_refl)
                           as [Z1 [Z2 [HZ1 [HtZ1 [HstZ [HtZ2 _]]]]]].
                         destruct Z1 as [uZ1 rhoZ1 dZ1]. simpl in HtZ1. subst uZ1.
                         destruct (HA rhoZ1 dZ1 HZ1)
                           as [[Hnoerr [c2 [Hm2 Hinv2]]] | Herr];
                           [| right; exact Herr].
                         destruct (consume_err_step _ _ _ HstZ HtZ2)
                           as [t2 [op2 [k02 [Hfind2 Herr2]]]].
                         simpl in Hfind2, Herr2.
                         destruct (mirror_err_step _ _ _ rhoZ1 s _ _ _ _
                                     Hinv2 Hfind2 Herr2) as [g0 Hstep2].
                         right. exists s, g0, nil. split.
                         +++ eapply m2_traces_intro.
                             eapply rt_trans; [exact Hm2 |].
                             apply rt_step. exact Hstep2.
                         +++ rewrite app_nil_r. reflexivity.
                     --- assert (Hcov' : err_covers (p ++ TErr f0 :: nil) w)
                           by (right; exists p, f0, tl2; auto).
                         destruct (Hdc _ rho d HDu Hcov')
                           as [[Hu' [Hnoerr _]] | Herr].
                         +++ exfalso. eapply (Hnoerr f0). rewrite <- Hu'.
                             apply in_or_app. right. left. reflexivity.
                         +++ right. exact Herr.
            -- (* M1-LEVEL TAU: p1 = Tau p1' *)
               subst p1 pT.
               (* the pending flag must be clear here as well *)
               match type of Hc10 with
               | _ = Some (Build_ThreadState _ _ ?pdv) =>
                   destruct pdv as [m0 |] eqn:Hpdv
               end.
               { destruct (Hpd m0 eq_refl) as [kx Hkx]. discriminate Hkx. }
               exists w, (TMap.add t (Build_ThreadState f2 p1' None) c1), Gh.
               split; [| split].
               ++ eapply rt_trans; [exact Hm1 |]. apply rt_step.
                  eapply trace_taustep_intro. exact Hc10.
               ++ intros t'.
                  destruct (Pos.eq_dec t' t) as [-> | Hne].
                  ** rewrite <- Hgst.
                     eapply TI1_In with (p1 := p1') (pd := None).
                     --- rewrite TMap.gss. reflexivity.
                     --- rewrite TMap.gss. reflexivity.
                     --- intros m' Hm'. discriminate Hm'.
                  ** eapply thread_inv1_frame;
                       [apply Hinv1 | rewrite TMap.gso; auto | rewrite TMap.gso; auto].
               ++ exact Hdc.
        + (* composite error step *)
          apply ts_error_cases in Herror.
          destruct Herror as [t2 [m2 [κ2 [Hev [Hts Herr2]]]]].
          subst ev ts. simpl in *.
          pose proof (Hinv1 t2) as Ht1.
          remember (Gh t2) as gst eqn:Hgst.
          destruct Ht1 as [Hc0 Hc10 | g2 p2 Hc0 Hc10 | g2 f2 k2 p1 pd Hc0 Hc10 Hpd].
          * congruence.
          * (* TgOut: substProg is never a Vis *)
            rewrite Hfind in Hc0. inversion Hc0; clean_existT.
            match goal with
            | HH : Vis _ _ = substProg _ _ _ |- _ =>
                symmetry in HH; apply substProg_eq_vis in HH; destruct HH
            | HH : substProg _ _ _ = Vis _ _ |- _ =>
                apply substProg_eq_vis in HH; destruct HH
            end.
          * (* TgIn: mirror the error to M1, and prepare the transformer *)
            rewrite Hfind in Hc0. inversion Hc0; clean_existT.
            match goal with
            | HH : Vis _ _ = bindSubstProg _ _ _ _ |- _ => symmetry in HH
            | HH : bindSubstProg _ _ _ _ = Vis _ _ |- _ => idtac
            end.
            match goal with
            | HH : bindSubstProg _ _ _ _ = Vis _ _ |- _ =>
                apply bindSubstProg_eq_vis in HH;
                destruct HH as [κ1 [Hp1 Hκ]]
            end.
            subst p1.
            exists (w ++ TErr f2 :: nil), c1, Gh.
            split; [| split].
            -- eapply rt_trans; [exact Hm1 |]. apply rt_step.
               eapply trace_errstep_intro; eauto.
            -- exact Hinv1.
            -- (* d_concl: after an error, only the error witness survives *)
               assert (HA : forall rho1 d1,
                   trace_steps idImpl dinit
                     (mkTraceConfig (w ++ TErr f2 :: nil) rho1 d1) ->
                   m2_err_witness s).
               { intros rho1 d1 HD1.
                 destruct (trace_steps_split_last idImpl rho0 _ w _ HD1 eq_refl)
                   as [Y1 [Y2 [HY1 [HtY1 [Hst1 [HtY2 Hpost]]]]]].
                 destruct Y1 as [uY1 rhoY1 dY1]. simpl in HtY1. subst uY1.
                 destruct (Hdc w rhoY1 dY1 HY1 (or_introl eq_refl))
                   as [[_ [Hnoerr [c2 [Hm2 Hinv2]]]] | Herr]; [| exact Herr].
                 destruct (consume_err_step _ _ _ Hst1 HtY2)
                   as [t3 [op3 [k03 [Hfind3 Herr3]]]].
                 simpl in Hfind3, Herr3.
                 destruct (mirror_err_step _ _ _ rhoY1 s _ _ _ _
                             Hinv2 Hfind3 Herr3) as [g0 Hstep0].
                 exists s, g0, nil. split.
                 - eapply m2_traces_intro.
                   eapply rt_trans; [exact Hm2 |]. apply rt_step. exact Hstep0.
                 - rewrite app_nil_r. reflexivity. }
               intros u rho d HDu Hcov.
               destruct Hcov as [-> | [p [f0 [tl [Hu Hw']]]]].
               ++ right. apply m2_err_witness_app. eapply HA; eauto.
               ++ subst u.
                  destruct (app_snoc_cases p tl w (TErr f2) (eq_sym Hw'))
                    as [[Hp Htl] | [tl2 Hw2]].
                  ** (* p swallows the whole trace: cut the run at the prefix *)
                     subst p tl.
                     destruct (trace_steps_prefix_run idImpl rho0 _
                                 (w ++ TErr f2 :: nil) (TErr f0 :: nil) HDu eq_refl)
                       as [Z [HZ HtZ]].
                     destruct Z as [uZ rhoZ dZ]. simpl in HtZ. subst uZ.
                     right. apply m2_err_witness_app. eapply HA; eauto.
                  ** assert (Hcov' : err_covers (p ++ TErr f0 :: nil) w)
                       by (right; exists p, f0, tl2; auto).
                     destruct (Hdc _ rho d HDu Hcov')
                       as [[Hu' [Hnoerr _]] | Herr].
                     --- exfalso. eapply (Hnoerr f0). rewrite <- Hu'.
                         apply in_or_app. right. left. reflexivity.
                     --- right. apply m2_err_witness_app. exact Herr.
    Qed.
  End VCompCore.

  (* Absorbing one error closure into another: if the error-closed trace
     set of [idImpl] accepts [q ++ [TErr g0]], it accepts every extension
     of [q]. Together with the prefix-realizability of generated traces,
     this is what lets the [M2]-level error witness produced by
     [vcomp_main] be discharged against [CompLin M2]. *)
  Lemma closed_absorb {F' : Op.t} {VF' : @LTS F'} (rho0' : State VF') :
    forall q (g0 : Sig.op F') tl,
      ImplTracesClosed idImpl rho0' (q ++ TErr g0 :: nil) ->
      ImplTracesClosed idImpl rho0' (q ++ tl).
  Proof.
    intros q g0 tl [Hq | [p [f1 [tl1 [Hp Heq]]]]].
    - right. exists q, g0, tl. auto.
    - destruct (app_snoc_cases p tl1 q (TErr g0) (eq_sym Heq))
        as [[Hp' Htl'] | [tl2 Hq2]].
      + (* the spec's own error covers the whole of [q ++ [TErr g0]]:
           truncate its run at that prefix *)
        subst p tl1.
        destruct Hp as [rho' [d' Hrun']].
        destruct (trace_steps_prefix_run idImpl rho0' _ (q ++ TErr g0 :: nil)
                    (TErr f1 :: nil) Hrun' eq_refl) as [Y [HY HtY]].
        right. exists q, g0, tl. split; auto.
        destruct Y as [uY rY dY]. simpl in HtY. subst uY.
        exists rY, dY. exact HY.
      + (* the spec's error strikes within [q] *)
        subst q. right. exists p, f1, (tl2 ++ tl).
        split; [exact Hp | rewrite <- app_assoc; reflexivity].
  Qed.

  (** Lemma 4.3 (Vertical Compositionality of Compositional
      Linearizability): if [M1 : VE { VF] and [M2 : VF { VG], then their
      vertical composition [M1 ▶ M2 : VE { VG]. *)
  Module VComp.
    Lemma CompLin_vcomp
        {E F G : Op.t}
        {VE : @LTS E} {VF : @LTS F} {VG : @LTS G}
        (M1 : ModuleImpl E F) (M2 : ModuleImpl F G)
        (sigma0 : State VE) (rho0 : State VF) (tau0 : State VG) :
      CompLin M1 sigma0 rho0 ->
      CompLin M2 rho0 tau0 ->
      CompLin (M1 ▶ M2) sigma0 tau0.
    Proof.
      intros HM1 HM2 str Htr.
      destruct Htr as [sigma [c Hrun]].
      destruct (vcomp_main M1 M2 sigma0 rho0 (mkTraceConfig str sigma c) Hrun)
        as [w [c1 [Gh [Hm1run [_ Hdc]]]]].
      simpl in Hm1run, Hdc.
      assert (Hw : ImplTraces M1 sigma0 w) by (exists sigma, c1; exact Hm1run).
      destruct (HM1 w Hw) as [Hid | [p [f0 [tl [Hderr Hw']]]]].
      - (* the copy-cat realizes w on the nose: feed it to the transformer *)
        destruct Hid as [rho [d Hd]].
        destruct (Hdc w rho d Hd (or_introl eq_refl))
          as [[_ [_ [c2 [Hm2run _]]]] | Herr].
        + apply HM2. eapply m2_traces_intro; eauto.
        + destruct Herr as [q [g0 [tl [Hqerr Hstr]]]].
          subst str.
          eapply closed_absorb.
          apply HM2. exact Hqerr.
      - (* the copy-cat errors at a prefix of w *)
        destruct Hderr as [rho [d Hd]].
        assert (Hcov : err_covers (p ++ TErr f0 :: nil) w)
          by (right; exists p, f0, tl; auto).
        destruct (Hdc _ rho d Hd Hcov) as [[Hu' [Hnoerr _]] | Herr].
        + exfalso. eapply (Hnoerr f0). rewrite <- Hu'.
          apply in_or_app. right. left. reflexivity.
        + destruct Herr as [q [g0 [tl' [Hqerr Hstr]]]].
          subst str.
          eapply closed_absorb.
          apply HM2. exact Hqerr.
    Qed.

    Print Assumptions CompLin_vcomp.
  End VComp.

End CompLinVComp.
