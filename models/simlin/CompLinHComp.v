Require Import Coq.Lists.List.
Require Import Coq.PArith.PArith.
Require Import Lia.
Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.Program.Equality.
Require Import Logic.FunctionalExtensionality.

Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import CompLin.

(** Horizontal Compositionality of Compositional Linearizability (Lemma 4.2,
    §4.3): [CompLin] (Definition 4.1) composes horizontally, when two
    independent libraries/implementations are run side by side.

    The composition operator on [ModuleImpl]s itself ([implHComp]/[⊗]) is
    defined here fresh, independent of the [TPSimulationSet]/[AbstractConfig]
    machinery of Definition 5.2, since this file only needs it to state
    compositionality directly for the trace semantics of [CompLin.v].

    Vertical compositionality (Lemma 4.3) is in [CompLinVComp.v]. *)
Module CompLinHComp.
  Import Reg.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import Semantics.
  Import CompLin.CompLin.

  (** * Generic facts about [trace_step]/[trace_steps], for an arbitrary
      [M : ModuleImpl E F]: independent of the tensor construction, and
      needed to recompose two independently-replayed traces back into one
      matching a prescribed interleaving (below). *)
  Section TraceStepsAux.
    Context {E F : Op.t}.
    Context {VE : @LTS E}.
    Context (M : ModuleImpl E F).

    (* A single [trace_step] leaves the trace unchanged, or appends exactly
       one item. *)
    Lemma trace_step_app_bound :
      forall (X Y : @TraceConfig E F VE), trace_step M X Y ->
        tc_trace Y = tc_trace X \/ exists it, tc_trace Y = tc_trace X ++ it :: nil.
    Proof.
      intros X Y Hstep. destruct Hstep; simpl; auto.
      - right; eexists; reflexivity.
      - right; eexists; reflexivity.
      - right; eexists; reflexivity.
    Qed.

    (* Since the trace only ever grows by at most one item per step, every
       intermediate trace length between the endpoints of a [trace_steps]
       run is actually realized at some point along the run. This is what
       lets two independent runs (of two different implementations, or of
       the same implementation from two different derivations) be
       "resynchronized" at matching trace lengths. *)
    Lemma trace_steps_reach_length :
      forall (X Z : @TraceConfig E F VE), trace_steps M X Z ->
        forall n, List.length (tc_trace X) <= n -> n <= List.length (tc_trace Z) ->
        exists Y, trace_steps M X Y /\ trace_steps M Y Z /\ List.length (tc_trace Y) = n.
    Proof.
      intros X Z Htr.
      induction Htr as [X Z Hstep | X | X Y Z Htr1 IH1 Htr2 IH2]; intros n Hn1 Hn2.
      - destruct (trace_step_app_bound X Z Hstep) as [Heq | [it Heq]].
        + exists X. rewrite Heq in Hn2.
          assert (n = List.length (tc_trace X)) by lia.
          repeat split; [apply rt_refl | apply rt_step; exact Hstep | lia].
        + assert (Hlen : List.length (tc_trace Z) = (List.length (tc_trace X) + 1)%nat).
          { rewrite Heq, app_length. simpl. lia. }
          assert (Hn : n = List.length (tc_trace X) \/ n = List.length (tc_trace Z)) by lia.
          destruct Hn as [Hn | Hn].
          * exists X. repeat split; [apply rt_refl | apply rt_step; exact Hstep | lia].
          * exists Z. repeat split; [apply rt_step; exact Hstep | apply rt_refl | lia].
      - exists X. assert (n = List.length (tc_trace X)) by lia.
        repeat split; [apply rt_refl | apply rt_refl | lia].
      - destruct (Compare_dec.le_lt_dec n (List.length (tc_trace Y))) as [Hle | Hgt].
        + destruct (IH1 n Hn1 Hle) as [W [Hxw [Hwy Hlen]]].
          exists W. repeat split; [exact Hxw | eapply rt_trans; [exact Hwy | exact Htr2] | exact Hlen].
        + assert (Hn1' : List.length (tc_trace Y) <= n) by lia.
          destruct (IH2 n Hn1' Hn2) as [W [Hyw [Hwz Hlen]]].
          exists W. repeat split; [eapply rt_trans; [exact Htr1 | exact Hyw] | exact Hwz | exact Hlen].
    Qed.

    (* The trace only ever grows, by [trace_steps]; in particular, if it
       comes back to its starting value, every intermediate point along the
       way must share that same value too (a monotone quantity can't dip
       below its start and return without staying put throughout). *)
    Lemma trace_steps_monotone :
      forall (X Y : @TraceConfig E F VE), trace_steps M X Y -> exists tl, tc_trace Y = tc_trace X ++ tl.
    Proof.
      intros X Y Hpss. unfold trace_steps in Hpss.
      induction Hpss.
      - apply trace_step_app_bound in H as [Heq | [it Heq]].
        + exists nil. rewrite app_nil_r. exact Heq.
        + eexists; exact Heq.
      - exists nil. rewrite app_nil_r. reflexivity.
      - destruct IHHpss1 as [tl1 Heq1]. destruct IHHpss2 as [tl2 Heq2].
        exists (tl1 ++ tl2). rewrite Heq2, Heq1, app_assoc. reflexivity.
    Qed.

    Lemma trace_steps_flat_mid :
      forall (A B : @TraceConfig E F VE), trace_steps M A B ->
        tc_trace A = tc_trace B ->
        forall (Y : @TraceConfig E F VE), trace_steps M A Y -> trace_steps M Y B ->
          tc_trace Y = tc_trace A.
    Proof.
      intros A B Htr Heq Y Hay Hyb.
      destruct (trace_steps_monotone A Y Hay) as [tl1 Heq1].
      destruct (trace_steps_monotone Y B Hyb) as [tl2 Heq2].
      rewrite Heq1, <- app_assoc in Heq2.
      rewrite <- Heq in Heq2.
      assert (Hnil : tl1 ++ tl2 = nil).
      { apply (app_inv_head (tc_trace A)). rewrite app_nil_r. exact (eq_sym Heq2). }
      apply app_eq_nil in Hnil as [Hnil1 _].
      rewrite Heq1, Hnil1, app_nil_r. reflexivity.
    Qed.

    (* A run that grows the trace by exactly one item factors as: a
       trace-preserving prefix, then exactly the one growing [trace_step],
       then a trace-preserving suffix. This is what lets a single step of
       the *combined* system (which touches only one side, growing its
       projected trace by exactly one item) be matched against the *whole*
       given continuation on that side, which may pad the one visible step
       with arbitrarily many invisible ones on either side of it. *)
    Lemma trace_steps_single_growth_split :
      forall (A B : @TraceConfig E F VE) (it : TraceItem F), trace_steps M A B ->
        tc_trace B = tc_trace A ++ it :: nil ->
        exists Mid1 Mid2,
          trace_steps M A Mid1 /\ tc_trace Mid1 = tc_trace A /\
          trace_step M Mid1 Mid2 /\ tc_trace Mid2 = tc_trace A ++ it :: nil /\
          trace_steps M Mid2 B.
    Proof.
      intros A B it Htr.
      induction Htr as [A B Hstep | A | A Y B Htr1 IH1 Htr2 IH2]; intros Heq.
      - exists A, B. repeat split; auto; [apply rt_refl | apply rt_refl].
      - exfalso. apply (f_equal (@List.length _)) in Heq.
        rewrite app_length in Heq. simpl in Heq. lia.
      - destruct (trace_steps_monotone A Y Htr1) as [tlY HeqY].
        destruct (trace_steps_monotone Y B Htr2) as [tlB HeqB].
        assert (Hcomb : tlY ++ tlB = it :: nil).
        { apply (app_inv_head (tc_trace A)).
          rewrite app_assoc, <- HeqY, <- HeqB. exact Heq. }
        destruct tlY as [| itY tlY'].
        + (* Y's trace = A's trace: all the growth is within Y -> B *)
          simpl in Hcomb. rewrite app_nil_r in HeqY.
          assert (HeqB' : tc_trace B = tc_trace Y ++ it :: nil)
            by (rewrite HeqB, Hcomb; reflexivity).
          destruct (IH2 HeqB') as [Mid1 [Mid2 [Hs1 [Heqm1 [Hstepm [Heqm2 Hs2]]]]]].
          exists Mid1, Mid2. repeat split; auto.
          * eapply rt_trans; [exact Htr1 | exact Hs1].
          * rewrite Heqm1, HeqY. reflexivity.
          * rewrite Heqm2, HeqY. reflexivity.
        + (* Y's trace already strictly extends A's: the growth is within A -> Y *)
          injection Hcomb as Hcomb1 Hcomb2.
          apply app_eq_nil in Hcomb2 as [Hcomb2a Hcomb2b].
          subst itY tlY' tlB.
          destruct (IH1 HeqY) as [Mid1 [Mid2 [Hs1 [Heqm1 [Hstepm [Heqm2 Hs2]]]]]].
          exists Mid1, Mid2. repeat split; auto.
          eapply rt_trans; [exact Hs2 | exact Htr2].
    Qed.
  End TraceStepsAux.

  (* Whether a thread is "active" (has an outstanding, unanswered
     invocation) after a given trace is a property of the trace alone,
     independent of which implementation produced it: this is what lets two
     *different* implementations ([M1]/[idImpl1] or [M2]/[idImpl2]) that
     each replay the same projected trace be recombined, since the
     [invstep]/[retstep] domain preconditions they must separately satisfy
     ("thread [t] not already active") turn out to agree, both being
     determined by the trace itself. *)
  Section TraceActive.
    Context {F : Op.t}.

    Fixpoint trace_active (t : Trace F) (th : tid) (cur : bool) : bool :=
      match t with
      | nil => cur
      | TEvent (Build_ThreadEvent th' (InvEv _)) :: rest =>
          trace_active rest th (if Pos.eqb th th' then true else cur)
      | TEvent (Build_ThreadEvent th' (ResEv _ _)) :: rest =>
          trace_active rest th (if Pos.eqb th th' then false else cur)
      | TErr _ :: rest => trace_active rest th cur
      end.

    Lemma trace_active_app t1 t2 th cur :
      trace_active (t1 ++ t2) th cur = trace_active t2 th (trace_active t1 th cur).
    Proof.
      revert cur. induction t1 as [| it t1 IH]; intros cur; simpl; auto.
      destruct it as [ev | f].
      - destruct ev as [th' [op | op r]]; simpl; apply IH.
      - apply IH.
    Qed.

    Section Generic.
      Context {E : Op.t} {VE : @LTS E} (M : ModuleImpl E F).

      (* The domain invariant "[th] is pending in the pool iff [th] is
         active per the trace" is preserved by every kind of [trace_step]:
         [TraceStepInv]/[TraceStepRet] update the pool exactly matching how
         [trace_active] updates; [TraceStepU]/[TraceStepTau] only ever
         update the *value* stored at an already-active thread (never the
         active/inactive set); [TraceStepError] touches neither. *)
      Lemma pool_dom_invariant :
        forall (X Z : @TraceConfig E F VE), trace_steps M X Z ->
          forall th, (TMap.find th (tc_pool X) = None <-> trace_active (tc_trace X) th false = false) ->
            (TMap.find th (tc_pool Z) = None <-> trace_active (tc_trace Z) th false = false).
      Proof.
        intros X Z Htr.
        induction Htr as [X Z Hstep | X | X Y Z Htr1 IH1 Htr2 IH2]; intros th Hinv.
        - destruct Hstep as [s sigma c t f c' Hstep | s sigma c t f ret c' Hstep
                             | s sigma c ev sigma' c' Hstep | s sigma c t c' Hstep
                             | s sigma c f0 ev ts Hfind Herror]; simpl in *.
          + (* TraceStepInv *)
            inversion Hstep as [Hfind Hupd]; subst.
            destruct (Pos.eq_dec th t) as [Heq | Hneq]; subst.
            * rewrite TMap.gss, trace_active_app; simpl; rewrite Pos.eqb_refl.
              split; discriminate.
            * rewrite TMap.gso by auto.
              rewrite trace_active_app; simpl.
              destruct (Pos.eqb th t) eqn:Hpeq.
              -- apply Pos.eqb_eq in Hpeq. congruence.
              -- exact Hinv.
          + (* TraceStepRet *)
            inversion Hstep as [Hfind Hupd]; subst.
            destruct (Pos.eq_dec th t) as [Heq | Hneq]; subst.
            * rewrite TMap.grs, trace_active_app; simpl; rewrite Pos.eqb_refl.
              split; auto.
            * rewrite TMap.gro by auto.
              rewrite trace_active_app; simpl.
              destruct (Pos.eqb th t) eqn:Hpeq.
              -- apply Pos.eqb_eq in Hpeq. congruence.
              -- exact Hinv.
          + (* TraceStepU: pool value changes at [te_tid ev], domain doesn't *)
            inversion Hstep as [f0 ts1 ts2 Hfind Hstep0 Hupd]; subst.
            destruct (Pos.eq_dec th (te_tid ev)) as [Heq | Hneq]; subst.
            * rewrite TMap.gss. split.
              -- discriminate.
              -- intro Hact. apply Hinv in Hact. congruence.
            * rewrite TMap.gso by auto. exact Hinv.
          + (* TraceStepTau *)
            inversion Hstep as [ts1 ts2 Hfind Hstep0 Hupd]; subst.
            destruct (Pos.eq_dec th t) as [Heq | Hneq]; subst.
            * rewrite TMap.gss. split.
              -- discriminate.
              -- intro Hact. apply Hinv in Hact. congruence.
            * rewrite TMap.gso by auto. exact Hinv.
          + (* TraceStepError: pool unchanged; [TErr] doesn't affect any tid's activity *)
            rewrite trace_active_app. simpl. exact Hinv.
        - exact Hinv.
        - apply IH2. apply IH1. exact Hinv.
      Qed.

      Corollary pool_dom_from_init :
        forall (sigma0 : State VE) (t : Trace F) (sigma : State VE) (c : @ThreadPoolState E F),
          trace_steps M (mkTraceConfig nil sigma0 (TMap.empty _)) (mkTraceConfig t sigma c) ->
          forall th, TMap.find th c = None <-> trace_active t th false = false.
      Proof.
        intros sigma0 t sigma c Htr th.
        apply (pool_dom_invariant (mkTraceConfig nil sigma0 (TMap.empty _)) (mkTraceConfig t sigma c) Htr th).
        simpl. rewrite TMap.gempty. split; reflexivity.
      Qed.
    End Generic.
  End TraceActive.

  (** * Horizontal composition of [ModuleImpl]s.

      [impl1 ⊗ impl2] runs [impl1 : E1 -> F1] and [impl2 : E2 -> F2] side by
      side over the disjoint union (coproduct) of their signatures. *)
  CoFixpoint liftLeftProg
      {E1 E2} {R} (p : Prog E1 R) : Prog (Sig.Plus.omap E1 E2) R :=
    match p with
    | Vis m k =>
        @Vis (Sig.Plus.omap E1 E2) R
          (@inl (Sig.op E1) (Sig.op E2) m)
          (fun a => liftLeftProg (E2 := E2) (k a))
    | Ret r => Ret r
    | Tau p' => Tau (liftLeftProg (E2 := E2) p')
    end.

  CoFixpoint liftRightProg
      {E1 E2} {R} (p : Prog E2 R) : Prog (Sig.Plus.omap E1 E2) R :=
    match p with
    | Vis m k =>
        @Vis (Sig.Plus.omap E1 E2) R
          (@inr (Sig.op E1) (Sig.op E2) m)
          (fun a => liftRightProg (E1 := E1) (k a))
    | Ret r => Ret r
    | Tau p' => Tau (liftRightProg (E1 := E1) p')
    end.

  Definition implHComp {E1 F1 E2 F2}
      (impl1 : ModuleImpl E1 F1) (impl2 : ModuleImpl E2 F2) :
      ModuleImpl (Sig.Plus.omap E1 E2) (Sig.Plus.omap F1 F2) :=
    fun f t =>
      match f with
      | inl f => liftLeftProg (E2 := E2) (impl1 f t)
      | inr f => liftRightProg (E1 := E1) (impl2 f t)
      end.

  Notation "M ⊗ N" := (implHComp M N) (at level 40).

  (** * Splitting a combined thread pool over [Sig.Plus.omap E1 E2]/
      [Sig.Plus.omap F1 F2] into its two independent components (a
      trace-level, Poss-free analogue of the pool-splitting relations used
      for Threadpool Simulation's own horizontal compositionality). *)
  Section HCompSplit.
    Context {E1 F1 E2 F2 : Op.t}.

    Definition ts_left (ts1 : @ThreadState E1 F1) :
        @ThreadState (Sig.Plus.omap E1 E2) (Sig.Plus.omap F1 F2) :=
      @Build_ThreadState (Sig.Plus.omap E1 E2) (Sig.Plus.omap F1 F2)
        (@inl (Sig.op F1) (Sig.op F2) (ts_op ts1))
        (liftLeftProg (E2 := E2) (ts_prog ts1))
        (option_map (@inl (Sig.op E1) (Sig.op E2)) (ts_pend ts1)).

    Definition ts_right (ts2 : @ThreadState E2 F2) :
        @ThreadState (Sig.Plus.omap E1 E2) (Sig.Plus.omap F1 F2) :=
      @Build_ThreadState (Sig.Plus.omap E1 E2) (Sig.Plus.omap F1 F2)
        (@inr (Sig.op F1) (Sig.op F2) (ts_op ts2))
        (liftRightProg (E1 := E1) (ts_prog ts2))
        (option_map (@inr (Sig.op E1) (Sig.op E2)) (ts_pend ts2)).

    Variant hthread :
        option (@ThreadState (Sig.Plus.omap E1 E2) (Sig.Plus.omap F1 F2)) ->
        option (@ThreadState E1 F1) -> option (@ThreadState E2 F2) -> Prop :=
    | HT_None : hthread None None None
    | HT_Left ts1 : hthread (Some (ts_left ts1)) (Some ts1) None
    | HT_Right ts2 : hthread (Some (ts_right ts2)) None (Some ts2).

    Definition hpools
        (c : @ThreadPoolState (Sig.Plus.omap E1 E2) (Sig.Plus.omap F1 F2))
        (c1 : @ThreadPoolState E1 F1) (c2 : @ThreadPoolState E2 F2) : Prop :=
      forall t, hthread (TMap.find t c) (TMap.find t c1) (TMap.find t c2).

    Lemma hpools_empty :
      hpools (TMap.empty _) (TMap.empty _) (TMap.empty _).
    Proof. intro t. rewrite !TMap.gempty. constructor. Qed.

    Lemma hpools_update_left t c c1 c2 ts1 :
      hpools c c1 c2 -> TMap.find t c2 = None ->
      hpools (TMap.add t (ts_left ts1) c) (TMap.add t ts1 c1) c2.
    Proof.
      intros Hp Hf2 i. destruct (Pos.eq_dec i t); subst.
      - rewrite !TMap.gss, Hf2. apply HT_Left.
      - rewrite !TMap.gso by auto. apply Hp.
    Qed.

    Lemma hpools_update_right t c c1 c2 ts2 :
      hpools c c1 c2 -> TMap.find t c1 = None ->
      hpools (TMap.add t (ts_right ts2) c) c1 (TMap.add t ts2 c2).
    Proof.
      intros Hp Hf1 i. destruct (Pos.eq_dec i t); subst.
      - rewrite !TMap.gss, Hf1. apply HT_Right.
      - rewrite !TMap.gso by auto. apply Hp.
    Qed.

    Lemma hpools_remove_left t c c1 c2 :
      hpools c c1 c2 -> TMap.find t c2 = None ->
      hpools (TMap.remove t c) (TMap.remove t c1) c2.
    Proof.
      intros Hp Hf2 i. destruct (Pos.eq_dec i t); subst.
      - rewrite !TMap.grs, Hf2. constructor.
      - rewrite !TMap.gro by auto. apply Hp.
    Qed.

    Lemma hpools_remove_right t c c1 c2 :
      hpools c c1 c2 -> TMap.find t c1 = None ->
      hpools (TMap.remove t c) c1 (TMap.remove t c2).
    Proof.
      intros Hp Hf1 i. destruct (Pos.eq_dec i t); subst.
      - rewrite !TMap.grs, Hf1. constructor.
      - rewrite !TMap.gro by auto. apply Hp.
    Qed.

    Lemma hpools_update t c c1 c2 ec ec1 ec2 :
      hpools c c1 c2 -> hthread ec ec1 ec2 ->
      hpools
        (match ec with Some x => TMap.add t x c | None => TMap.remove t c end)
        (match ec1 with Some x => TMap.add t x c1 | None => TMap.remove t c1 end)
        (match ec2 with Some x => TMap.add t x c2 | None => TMap.remove t c2 end).
    Proof.
      intros Hp Ht i. destruct (Pos.eq_dec i t); subst.
      - destruct ec, ec1, ec2; simpl in *;
          repeat rewrite ?TMap.gss, ?TMap.grs; auto.
      - destruct ec, ec1, ec2; simpl in *;
          repeat rewrite ?TMap.gso, ?TMap.gro by auto; apply Hp.
    Qed.

    Lemma liftLeftProgVis {R} m (k : Sig.ar m -> Prog E1 R) :
      liftLeftProg (E2 := E2) (Vis m k) =
      @Vis (Sig.Plus.omap E1 E2) R
        (@inl (Sig.op E1) (Sig.op E2) m) (fun a => liftLeftProg (E2 := E2) (k a)).
    Proof.
      rewrite (PPid (liftLeftProg (E2 := E2) (Vis m k))) at 1.
      unfold PP, liftLeftProg at 1. reflexivity.
    Qed.

    Lemma liftLeftProgRet {R} (r : R) :
      liftLeftProg (E1 := E1) (E2 := E2) (Ret r) = Ret r.
    Proof.
      rewrite (PPid (liftLeftProg (E1 := E1) (E2 := E2) (Ret r))) at 1.
      unfold PP, liftLeftProg at 1. reflexivity.
    Qed.

    Lemma liftLeftProgTau {R} (p : Prog E1 R) :
      liftLeftProg (E2 := E2) (Tau p) = Tau (liftLeftProg (E2 := E2) p).
    Proof.
      rewrite (PPid (liftLeftProg (E2 := E2) (Tau p))) at 1.
      unfold PP, liftLeftProg at 1. reflexivity.
    Qed.

    Lemma liftRightProgVis {R} m (k : Sig.ar m -> Prog E2 R) :
      liftRightProg (E1 := E1) (Vis m k) =
      @Vis (Sig.Plus.omap E1 E2) R
        (@inr (Sig.op E1) (Sig.op E2) m) (fun a => liftRightProg (E1 := E1) (k a)).
    Proof.
      rewrite (PPid (liftRightProg (E1 := E1) (Vis m k))) at 1.
      unfold PP, liftRightProg at 1. reflexivity.
    Qed.

    Lemma liftRightProgRet {R} (r : R) :
      liftRightProg (E1 := E1) (E2 := E2) (Ret r) = Ret r.
    Proof.
      rewrite (PPid (liftRightProg (E1 := E1) (E2 := E2) (Ret r))) at 1.
      unfold PP, liftRightProg at 1. reflexivity.
    Qed.

    Lemma liftRightProgTau {R} (p : Prog E2 R) :
      liftRightProg (E1 := E1) (Tau p) = Tau (liftRightProg (E1 := E1) p).
    Proof.
      rewrite (PPid (liftRightProg (E1 := E1) (Tau p))) at 1.
      unfold PP, liftRightProg at 1. reflexivity.
    Qed.

    Lemma liftLeftProg_ret_inv {R} (p : Prog E1 R) r :
      liftLeftProg (E2 := E2) p = Ret r -> p = Ret r.
    Proof.
      destruct p.
      - rewrite liftLeftProgVis. discriminate.
      - rewrite liftLeftProgRet. inversion 1. reflexivity.
      - rewrite liftLeftProgTau. discriminate.
    Qed.

    Lemma liftRightProg_ret_inv {R} (p : Prog E2 R) r :
      liftRightProg (E1 := E1) p = Ret r -> p = Ret r.
    Proof.
      destruct p.
      - rewrite liftRightProgVis. discriminate.
      - rewrite liftRightProgRet. inversion 1. reflexivity.
      - rewrite liftRightProgTau. discriminate.
    Qed.
  End HCompSplit.

  (** * Projecting a combined trace back onto its two components. *)
  Section HCompProj.
    Context {F1 F2 : Op.t}.

    (* [TErr] is tagged with the overlay operation of the thread that
       errored ([CompLin.v]'s design note): in the combined signature that
       tag is itself an [inl _]/[inr _], which is exactly what lets the
       terminal marker be routed to the correct side, the same way
       [InvEv]/[ResEv] items already are. *)
    Fixpoint proj_l (s : Trace (Sig.Plus.omap F1 F2)) : Trace F1 :=
      match s with
      | nil => nil
      | TEvent ev :: rest =>
          match te_ev ev with
          | InvEv op =>
              match op with
              | inl f => TEvent (Build_ThreadEvent (te_tid ev) (InvEv f)) :: proj_l rest
              | inr _ => proj_l rest
              end
          | ResEv op r =>
              match op, r with
              | inl f, r => TEvent (Build_ThreadEvent (te_tid ev) (ResEv f r)) :: proj_l rest
              | inr _, _ => proj_l rest
              end
          end
      | TErr f :: rest =>
          match f with
          | inl f1 => TErr f1 :: proj_l rest
          | inr _ => proj_l rest
          end
      end.

    Fixpoint proj_r (s : Trace (Sig.Plus.omap F1 F2)) : Trace F2 :=
      match s with
      | nil => nil
      | TEvent ev :: rest =>
          match te_ev ev with
          | InvEv op =>
              match op with
              | inr f => TEvent (Build_ThreadEvent (te_tid ev) (InvEv f)) :: proj_r rest
              | inl _ => proj_r rest
              end
          | ResEv op r =>
              match op, r with
              | inr f, r => TEvent (Build_ThreadEvent (te_tid ev) (ResEv f r)) :: proj_r rest
              | inl _, _ => proj_r rest
              end
          end
      | TErr f :: rest =>
          match f with
          | inr f2 => TErr f2 :: proj_r rest
          | inl _ => proj_r rest
          end
      end.

    Lemma proj_l_app s1 s2 : proj_l (s1 ++ s2) = proj_l s1 ++ proj_l s2.
    Proof.
      induction s1 as [| it s1 IH]; simpl; auto.
      destruct it as [ev | f].
      - destruct (te_ev ev) as [[f | f] | [f | f] r]; simpl; rewrite IH; reflexivity.
      - destruct f as [f | f]; simpl; rewrite IH; reflexivity.
    Qed.

    Lemma proj_r_app s1 s2 : proj_r (s1 ++ s2) = proj_r s1 ++ proj_r s2.
    Proof.
      induction s1 as [| it s1 IH]; simpl; auto.
      destruct it as [ev | f].
      - destruct (te_ev ev) as [[f | f] | [f | f] r]; simpl; rewrite IH; reflexivity.
      - destruct f as [f | f]; simpl; rewrite IH; reflexivity.
    Qed.

    Lemma proj_l_inl_singleton t f :
      proj_l (TEvent (Build_ThreadEvent t (@InvEv (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) f))) :: nil) =
      TEvent (Build_ThreadEvent t (InvEv f)) :: nil.
    Proof. reflexivity. Qed.

    Lemma proj_r_inl_singleton t f :
      proj_r (TEvent (Build_ThreadEvent t (@InvEv (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) f))) :: nil) = nil.
    Proof. reflexivity. Qed.

    Lemma proj_l_inr_singleton t f :
      proj_l (TEvent (Build_ThreadEvent t (@InvEv (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) f))) :: nil) = nil.
    Proof. reflexivity. Qed.

    Lemma proj_r_inr_singleton t f :
      proj_r (TEvent (Build_ThreadEvent t (@InvEv (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) f))) :: nil) =
      TEvent (Build_ThreadEvent t (InvEv f)) :: nil.
    Proof. reflexivity. Qed.

    Lemma proj_l_inl_singleton_res t f (r : Sig.ar f) :
      proj_l (TEvent (Build_ThreadEvent t (@ResEv (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) f) r)) :: nil) =
      TEvent (Build_ThreadEvent t (ResEv f r)) :: nil.
    Proof. reflexivity. Qed.

    Lemma proj_r_inl_singleton_res t f (r : Sig.ar f) :
      proj_r (TEvent (Build_ThreadEvent t (@ResEv (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) f) r)) :: nil) = nil.
    Proof. reflexivity. Qed.

    Lemma proj_l_inr_singleton_res t f (r : Sig.ar f) :
      proj_l (TEvent (Build_ThreadEvent t (@ResEv (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) f) r)) :: nil) = nil.
    Proof. reflexivity. Qed.

    Lemma proj_r_inr_singleton_res t f (r : Sig.ar f) :
      proj_r (TEvent (Build_ThreadEvent t (@ResEv (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) f) r)) :: nil) =
      TEvent (Build_ThreadEvent t (ResEv f r)) :: nil.
    Proof. reflexivity. Qed.

    Lemma proj_l_err_inl_singleton f :
      proj_l (@TErr (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) f) :: nil) = TErr f :: nil.
    Proof. reflexivity. Qed.

    Lemma proj_r_err_inl_singleton f :
      proj_r (@TErr (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) f) :: nil) = nil.
    Proof. reflexivity. Qed.

    Lemma proj_l_err_inr_singleton f :
      proj_l (@TErr (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) f) :: nil) = nil.
    Proof. reflexivity. Qed.

    Lemma proj_r_err_inr_singleton f :
      proj_r (@TErr (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) f) :: nil) = TErr f :: nil.
    Proof. reflexivity. Qed.
  End HCompProj.

  (** * Decomposition: a run of [M1 ⊗ M2] over the tensor library splits
      into two independent runs, of [M1] and [M2] respectively. Purely
      structural; does not use [CompLin]. *)
  Section HCompDecompose.
    Context {E1 F1 E2 F2 : Op.t}.
    Context {VE1 : @LTS E1} {VE2 : @LTS E2}.
    Context (M1 : ModuleImpl E1 F1) (M2 : ModuleImpl E2 F2).

    Lemma hthread_none_inv (ec1 : option (@ThreadState E1 F1)) (ec2 : option (@ThreadState E2 F2)) :
      hthread None ec1 ec2 -> ec1 = None /\ ec2 = None.
    Proof. inversion 1; auto. Qed.

    Lemma hthread_inv
        (ec : option (@ThreadState (Sig.Plus.omap E1 E2) (Sig.Plus.omap F1 F2)))
        (ec1 : option (@ThreadState E1 F1)) (ec2 : option (@ThreadState E2 F2)) :
      hthread ec ec1 ec2 ->
      (ec = None /\ ec1 = None /\ ec2 = None) \/
      (exists ts1, ec = Some (ts_left ts1) /\ ec1 = Some ts1 /\ ec2 = None) \/
      (exists ts2, ec = Some (ts_right ts2) /\ ec1 = None /\ ec2 = Some ts2).
    Proof. destruct 1; [left | right; left | right; right]; eauto. Qed.

    Definition packThreadProg {E F} (ts : @ThreadState E F) :
        { q : Sig.op F & Prog E (Sig.ar q) } :=
      existT _ (ts_op ts) (ts_prog ts).

    Lemma ts_left_unfold_gen (ts1 : @ThreadState E1 F1) :
      ts_left ts1 =
      @Build_ThreadState (Sig.Plus.omap E1 E2) (Sig.Plus.omap F1 F2)
        (@inl (Sig.op F1) (Sig.op F2) (ts_op ts1))
        (liftLeftProg (E2 := E2) (ts_prog ts1))
        (option_map (@inl (Sig.op E1) (Sig.op E2)) (ts_pend ts1)).
    Proof. destruct ts1; reflexivity. Qed.

    Lemma ts_right_unfold_gen (ts2 : @ThreadState E2 F2) :
      ts_right ts2 =
      @Build_ThreadState (Sig.Plus.omap E1 E2) (Sig.Plus.omap F1 F2)
        (@inr (Sig.op F1) (Sig.op F2) (ts_op ts2))
        (liftRightProg (E1 := E1) (ts_prog ts2))
        (option_map (@inr (Sig.op E1) (Sig.op E2)) (ts_pend ts2)).
    Proof. destruct ts2; reflexivity. Qed.

    Lemma ts_left_unfold f1 (p1 : Prog E1 (Sig.ar f1)) b1 :
      ts_left (Build_ThreadState f1 p1 b1) =
      @Build_ThreadState (Sig.Plus.omap E1 E2) (Sig.Plus.omap F1 F2)
        (@inl (Sig.op F1) (Sig.op F2) f1)
        (liftLeftProg (E2 := E2) p1) (option_map (@inl (Sig.op E1) (Sig.op E2)) b1).
    Proof. reflexivity. Qed.

    Lemma ts_right_unfold f2 (p2 : Prog E2 (Sig.ar f2)) b2 :
      ts_right (Build_ThreadState f2 p2 b2) =
      @Build_ThreadState (Sig.Plus.omap E1 E2) (Sig.Plus.omap F1 F2)
        (@inr (Sig.op F1) (Sig.op F2) f2)
        (liftRightProg (E1 := E1) p2) (option_map (@inr (Sig.op E1) (Sig.op E2)) b2).
    Proof. reflexivity. Qed.

    Theorem hcomp_decompose :
      forall (X Y : @TraceConfig (Sig.Plus.omap E1 E2) (Sig.Plus.omap F1 F2) (tens_lts VE1 VE2)),
        trace_steps (M1 ⊗ M2) X Y ->
        forall sigma1 sigma2 c1 c2,
          tc_state X = pair sigma1 sigma2 -> hpools (tc_pool X) c1 c2 ->
          exists sigma1' sigma2' c1' c2',
            tc_state Y = pair sigma1' sigma2' /\
            trace_steps M1 (mkTraceConfig (proj_l (tc_trace X)) sigma1 c1)
              (mkTraceConfig (proj_l (tc_trace Y)) sigma1' c1') /\
            trace_steps M2 (mkTraceConfig (proj_r (tc_trace X)) sigma2 c2)
              (mkTraceConfig (proj_r (tc_trace Y)) sigma2' c2') /\
            hpools (tc_pool Y) c1' c2'.
    Proof.
      intros X Y Htr. unfold trace_steps in Htr.
      induction Htr as [X Y Hstep | X | X Y0 Z Htr1 IH1 Htr2 IH2];
        intros sigma1 sigma2 c1 c2 HX Hp.
      - destruct X as [s0 sigmaX cX]. simpl in HX. subst sigmaX.
        dependent destruction Hstep.
        + (* TraceStepInv *)
          rename c' into cX'. inversion Hstep; subst; clear Hstep.
          pose proof (Hp t0) as Ht. simpl in Ht. rewrite Hfind in Ht.
          apply hthread_none_inv in Ht as [Hn1 Hn2].
          destruct f as [f1 | f2].
          * pose proof (hpools_update_left t0 cX c1 c2
              (Build_ThreadState f1 (M1 f1 t0) None) Hp Hn2) as Hp'.
            rewrite ts_left_unfold in Hp'. simpl in Hp'.
            assert (Hs1 : trace_steps M1 (mkTraceConfig (proj_l s0) sigma1 c1)
                     (mkTraceConfig
                        (proj_l (s0 ++ TEvent (Build_ThreadEvent t0
                          (@InvEv (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) f1))) :: nil))
                        sigma1 (TMap.add t0 (Build_ThreadState f1 (M1 f1 t0) None) c1))).
            { rewrite proj_l_app, proj_l_inl_singleton.
              apply rt_step. econstructor. econstructor; eauto. }
            assert (Hs2 : trace_steps M2 (mkTraceConfig (proj_r s0) sigma2 c2)
                     (mkTraceConfig
                        (proj_r (s0 ++ TEvent (Build_ThreadEvent t0
                          (@InvEv (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) f1))) :: nil))
                        sigma2 c2)).
            { rewrite proj_r_app, proj_r_inl_singleton, app_nil_r. apply rt_refl. }
            exists sigma1, sigma2,
              (TMap.add t0 (Build_ThreadState f1 (M1 f1 t0) None) c1), c2.
            repeat split; auto.
          * pose proof (hpools_update_right t0 cX c1 c2
              (Build_ThreadState f2 (M2 f2 t0) None) Hp Hn1) as Hp'.
            rewrite ts_right_unfold in Hp'. simpl in Hp'.
            assert (Hs1 : trace_steps M1 (mkTraceConfig (proj_l s0) sigma1 c1)
                     (mkTraceConfig
                        (proj_l (s0 ++ TEvent (Build_ThreadEvent t0
                          (@InvEv (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) f2))) :: nil))
                        sigma1 c1)).
            { rewrite proj_l_app, proj_l_inr_singleton, app_nil_r. apply rt_refl. }
            assert (Hs2 : trace_steps M2 (mkTraceConfig (proj_r s0) sigma2 c2)
                     (mkTraceConfig
                        (proj_r (s0 ++ TEvent (Build_ThreadEvent t0
                          (@InvEv (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) f2))) :: nil))
                        sigma2 (TMap.add t0 (Build_ThreadState f2 (M2 f2 t0) None) c2))).
            { rewrite proj_r_app, proj_r_inr_singleton.
              apply rt_step. econstructor. econstructor; eauto. }
            exists sigma1, sigma2, c1,
              (TMap.add t0 (Build_ThreadState f2 (M2 f2 t0) None) c2).
            repeat split; auto.
        + (* TraceStepRet *)
          rename c' into cX'. inversion Hstep; subst; clear Hstep.
          pose proof (Hp t0) as Ht. simpl in Ht.
          apply hthread_inv in Ht.
          destruct Ht as
            [[Heqc [Heq1 Heq2]] | [[ts1 [Heqc [Heq1 Heq2]]] | [ts2 [Heqc [Heq1 Heq2]]]]];
            rewrite Hfind in Heqc; try discriminate.
          * (* Left *)
            injection Heqc as Heqc Hprogeq Hpend.
            dependent destruction Hprogeq.
            symmetry in x.
            apply liftLeftProg_ret_inv in x.
            destruct (ts_pend ts1) eqn:Hpendts1; simpl in Hpend; try discriminate.
            assert (Hfind1 : TMap.find t0 c1 = Some (Build_ThreadState (ts_op ts1) (Ret ret) None)).
            { rewrite Heq1. f_equal. rewrite <- x, <- Hpendts1. destruct ts1; reflexivity. }
            assert (Hp' : hpools (TMap.remove t0 cX) (TMap.remove t0 c1) c2).
            { apply hpools_remove_left; auto. }
            assert (Hs1 : trace_steps M1 (mkTraceConfig (proj_l s0) sigma1 c1)
                     (mkTraceConfig
                        (proj_l (s0 ++ TEvent (Build_ThreadEvent t0
                          (@ResEv (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) (ts_op ts1)) ret)) :: nil))
                        sigma1 (TMap.remove t0 c1))).
            { rewrite proj_l_app, proj_l_inl_singleton_res.
              apply rt_step. econstructor. econstructor.
              - exact Hfind1.
              - reflexivity. }
            assert (Hs2 : trace_steps M2 (mkTraceConfig (proj_r s0) sigma2 c2)
                     (mkTraceConfig
                        (proj_r (s0 ++ TEvent (Build_ThreadEvent t0
                          (@ResEv (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) (ts_op ts1)) ret)) :: nil))
                        sigma2 c2)).
            { rewrite proj_r_app, proj_r_inl_singleton_res, app_nil_r. apply rt_refl. }
            exists sigma1, sigma2, (TMap.remove t0 c1), c2.
            repeat split; auto.
          * (* Right *)
            injection Heqc as Heqc Hprogeq Hpend.
            dependent destruction Hprogeq.
            symmetry in x.
            apply liftRightProg_ret_inv in x.
            destruct (ts_pend ts2) eqn:Hpendts2; simpl in Hpend; try discriminate.
            assert (Hfind2 : TMap.find t0 c2 = Some (Build_ThreadState (ts_op ts2) (Ret ret) None)).
            { rewrite Heq2. f_equal. rewrite <- x, <- Hpendts2. destruct ts2; reflexivity. }
            assert (Hp' : hpools (TMap.remove t0 cX) c1 (TMap.remove t0 c2)).
            { apply hpools_remove_right; auto. }
            assert (Hs1 : trace_steps M1 (mkTraceConfig (proj_l s0) sigma1 c1)
                     (mkTraceConfig
                        (proj_l (s0 ++ TEvent (Build_ThreadEvent t0
                          (@ResEv (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) (ts_op ts2)) ret)) :: nil))
                        sigma1 c1)).
            { rewrite proj_l_app, proj_l_inr_singleton_res, app_nil_r. apply rt_refl. }
            assert (Hs2 : trace_steps M2 (mkTraceConfig (proj_r s0) sigma2 c2)
                     (mkTraceConfig
                        (proj_r (s0 ++ TEvent (Build_ThreadEvent t0
                          (@ResEv (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) (ts_op ts2)) ret)) :: nil))
                        sigma2 (TMap.remove t0 c2))).
            { rewrite proj_r_app, proj_r_inr_singleton_res.
              apply rt_step. econstructor. econstructor.
              - exact Hfind2.
              - reflexivity. }
            exists sigma1, sigma2, c1, (TMap.remove t0 c2).
            repeat split; auto.
        + (* TraceStepU *)
          inversion Hstep as [f ts1 ts2 Hfind Hstep0 Hupd]; subst.
          pose proof (Hp (te_tid ev)) as Hthread. simpl in Hthread.
          simpl in Hfind. rewrite Hfind in Hthread.
          apply hthread_inv in Hthread.
          destruct Hthread as
            [[Heqc _] | [[tsL [Heqc [HeqL HeqR]]] | [tsR [Heqc [HeqL HeqR]]]]];
            try (rewrite Heqc in Hfind; discriminate).
          * injection Heqc as Heqc. subst ts1.
            rewrite ts_left_unfold_gen in Hstep0.
            dependent destruction Hstep0.
            -- (* ts_inv *)
               destruct (ts_prog tsL) eqn:Hprogeq;
                 [ rewrite liftLeftProgVis in x
                 | rewrite liftLeftProgRet in x; discriminate
                 | rewrite liftLeftProgTau in x; discriminate ].
               dependent destruction x.
               destruct sigma' as [sigma1' sigma2'].
               simpl in Hstep0. destruct Hstep0 as [HstepVE1 Heqsigma2]. subst sigma2'.
               destruct (ts_pend tsL) as [p1|] eqn:Hpendeq; simpl in x0; try discriminate.
               simpl in HeqL.
               assert (HfindL : TMap.find t0 c1 = Some (Build_ThreadState (ts_op tsL) (Vis m0 k0) None)).
               { rewrite HeqL. f_equal. rewrite <- Hprogeq, <- Hpendeq. destruct tsL; reflexivity. }
               assert (Hp' : hpools
                   (TMap.add t0
                     (ts_left (Build_ThreadState (ts_op tsL) (Vis m0 k0) (Some m0))) cX)
                   (TMap.add t0 (Build_ThreadState (ts_op tsL) (Vis m0 k0) (Some m0)) c1) c2).
               { apply hpools_update_left; auto. }
               rewrite ts_left_unfold in Hp'. simpl in Hp'.
               rewrite liftLeftProgVis in Hp'.
               assert (Hs1 : trace_steps M1 (mkTraceConfig (proj_l s0) sigma1 c1)
                        (mkTraceConfig (proj_l s0) sigma1'
                          (TMap.add t0 (Build_ThreadState (ts_op tsL) (Vis m0 k0) (Some m0)) c1))).
               { apply rt_step.
                 eapply TraceStepU with (ev := Build_ThreadEvent t0 (InvEv m0)).
                 econstructor.
                 - exact HfindL.
                 - econstructor. exact HstepVE1.
                 - reflexivity. }
               assert (Hs2 : trace_steps M2 (mkTraceConfig (proj_r s0) sigma2 c2)
                        (mkTraceConfig (proj_r s0) sigma2 c2)).
               { apply rt_refl. }
               exists sigma1', sigma2,
                 (TMap.add t0 (Build_ThreadState (ts_op tsL) (Vis m0 k0) (Some m0)) c1), c2.
               repeat split.
               ++ exact Hs1.
               ++ exact Hs2.
               ++ exact Hp'.
            -- (* ts_res *)
               destruct (ts_prog tsL) eqn:Hprogeq;
                 [ rewrite liftLeftProgVis in x
                 | rewrite liftLeftProgRet in x; discriminate
                 | rewrite liftLeftProgTau in x; discriminate ].
               dependent destruction x.
               destruct sigma' as [sigma1' sigma2'].
               simpl in Hstep0. destruct Hstep0 as [HstepVE1 Heqsigma2]. subst sigma2'.
               destruct (ts_pend tsL) as [p1|] eqn:Hpendeq; simpl in x0; try discriminate.
               injection x0 as x0. subst p1.
               simpl in HeqL.
               assert (HfindL : TMap.find t0 c1 = Some (Build_ThreadState (ts_op tsL) (Vis m0 k0) (Some m0))).
               { rewrite HeqL. f_equal. rewrite <- Hprogeq, <- Hpendeq. destruct tsL; reflexivity. }
               assert (Hp' : hpools
                   (TMap.add t0 (ts_left (Build_ThreadState (ts_op tsL) (k0 ret) None)) cX)
                   (TMap.add t0 (Build_ThreadState (ts_op tsL) (k0 ret) None) c1) c2).
               { apply hpools_update_left; auto. }
               rewrite ts_left_unfold in Hp'. simpl in Hp'.
               assert (Hs1 : trace_steps M1 (mkTraceConfig (proj_l s0) sigma1 c1)
                        (mkTraceConfig (proj_l s0) sigma1'
                          (TMap.add t0 (Build_ThreadState (ts_op tsL) (k0 ret) None) c1))).
               { apply rt_step.
                 eapply TraceStepU with (ev := Build_ThreadEvent t0 (ResEv m0 ret)).
                 econstructor.
                 - exact HfindL.
                 - econstructor. exact HstepVE1.
                 - reflexivity. }
               assert (Hs2 : trace_steps M2 (mkTraceConfig (proj_r s0) sigma2 c2)
                        (mkTraceConfig (proj_r s0) sigma2 c2)).
               { apply rt_refl. }
               exists sigma1', sigma2,
                 (TMap.add t0 (Build_ThreadState (ts_op tsL) (k0 ret) None) c1), c2.
               repeat split; auto.
          * injection Heqc as Heqc. subst ts1.
            rewrite ts_right_unfold_gen in Hstep0.
            dependent destruction Hstep0.
            -- (* ts_inv *)
               destruct (ts_prog tsR) eqn:Hprogeq;
                 [ rewrite liftRightProgVis in x
                 | rewrite liftRightProgRet in x; discriminate
                 | rewrite liftRightProgTau in x; discriminate ].
               dependent destruction x.
               destruct sigma' as [sigma1' sigma2'].
               simpl in Hstep0. destruct Hstep0 as [HstepVE2 Heqsigma1]. subst sigma1'.
               destruct (ts_pend tsR) as [p1|] eqn:Hpendeq; simpl in x0; try discriminate.
               simpl in HeqR.
               assert (HfindR : TMap.find t0 c2 = Some (Build_ThreadState (ts_op tsR) (Vis m0 k0) None)).
               { rewrite HeqR. f_equal. rewrite <- Hprogeq, <- Hpendeq. destruct tsR; reflexivity. }
               assert (Hp' : hpools
                   (TMap.add t0
                     (ts_right (Build_ThreadState (ts_op tsR) (Vis m0 k0) (Some m0))) cX)
                   c1 (TMap.add t0 (Build_ThreadState (ts_op tsR) (Vis m0 k0) (Some m0)) c2)).
               { apply hpools_update_right; auto. }
               rewrite ts_right_unfold in Hp'. simpl in Hp'.
               rewrite liftRightProgVis in Hp'.
               assert (Hs1 : trace_steps M1 (mkTraceConfig (proj_l s0) sigma1 c1)
                        (mkTraceConfig (proj_l s0) sigma1 c1)).
               { apply rt_refl. }
               assert (Hs2 : trace_steps M2 (mkTraceConfig (proj_r s0) sigma2 c2)
                        (mkTraceConfig (proj_r s0) sigma2'
                          (TMap.add t0 (Build_ThreadState (ts_op tsR) (Vis m0 k0) (Some m0)) c2))).
               { apply rt_step.
                 eapply TraceStepU with (ev := Build_ThreadEvent t0 (InvEv m0)).
                 econstructor.
                 - exact HfindR.
                 - econstructor. exact HstepVE2.
                 - reflexivity. }
               exists sigma1, sigma2',
                 c1, (TMap.add t0 (Build_ThreadState (ts_op tsR) (Vis m0 k0) (Some m0)) c2).
               repeat split; auto.
            -- (* ts_res *)
               destruct (ts_prog tsR) eqn:Hprogeq;
                 [ rewrite liftRightProgVis in x
                 | rewrite liftRightProgRet in x; discriminate
                 | rewrite liftRightProgTau in x; discriminate ].
               dependent destruction x.
               destruct sigma' as [sigma1' sigma2'].
               simpl in Hstep0. destruct Hstep0 as [HstepVE2 Heqsigma1]. subst sigma1'.
               destruct (ts_pend tsR) as [p1|] eqn:Hpendeq; simpl in x0; try discriminate.
               injection x0 as x0. subst p1.
               simpl in HeqR.
               assert (HfindR : TMap.find t0 c2 = Some (Build_ThreadState (ts_op tsR) (Vis m0 k0) (Some m0))).
               { rewrite HeqR. f_equal. rewrite <- Hprogeq, <- Hpendeq. destruct tsR; reflexivity. }
               assert (Hp' : hpools
                   (TMap.add t0 (ts_right (Build_ThreadState (ts_op tsR) (k0 ret) None)) cX)
                   c1 (TMap.add t0 (Build_ThreadState (ts_op tsR) (k0 ret) None) c2)).
               { apply hpools_update_right; auto. }
               rewrite ts_right_unfold in Hp'. simpl in Hp'.
               assert (Hs1 : trace_steps M1 (mkTraceConfig (proj_l s0) sigma1 c1)
                        (mkTraceConfig (proj_l s0) sigma1 c1)).
               { apply rt_refl. }
               assert (Hs2 : trace_steps M2 (mkTraceConfig (proj_r s0) sigma2 c2)
                        (mkTraceConfig (proj_r s0) sigma2'
                          (TMap.add t0 (Build_ThreadState (ts_op tsR) (k0 ret) None) c2))).
               { apply rt_step.
                 eapply TraceStepU with (ev := Build_ThreadEvent t0 (ResEv m0 ret)).
                 econstructor.
                 - exact HfindR.
                 - econstructor. exact HstepVE2.
                 - reflexivity. }
               exists sigma1, sigma2',
                 c1, (TMap.add t0 (Build_ThreadState (ts_op tsR) (k0 ret) None) c2).
               repeat split; auto.
        + (* TraceStepTau *)
          rename c' into cX'. inversion Hstep as [ts1 ts2 Hfind Hstep0 Hupd]; subst.
          pose proof (Hp t0) as Ht. simpl in Ht. simpl in Hfind. rewrite Hfind in Ht.
          apply hthread_inv in Ht.
          destruct Ht as
            [[Heqc _] | [[tsL [Heqc [HeqL HeqR]]] | [tsR [Heqc [HeqL HeqR]]]]];
            try (rewrite Heqc in Hfind; discriminate).
          * injection Heqc as Heqc. subst ts1.
            rewrite ts_left_unfold_gen in Hstep0.
            destruct (ts_prog tsL) eqn:Hprogeq.
            -- rewrite liftLeftProgVis in Hstep0. inversion Hstep0.
            -- rewrite liftLeftProgRet in Hstep0. inversion Hstep0.
            -- rewrite liftLeftProgTau in Hstep0. dependent destruction Hstep0.
               simpl in HeqL.
               assert (HfindL : TMap.find t0 c1 = Some (Build_ThreadState (ts_op tsL) (Tau p) (ts_pend tsL))).
               { rewrite HeqL. f_equal. rewrite <- Hprogeq. destruct tsL; reflexivity. }
               assert (Hp' : hpools
                   (TMap.add t0 (ts_left (Build_ThreadState (ts_op tsL) p (ts_pend tsL))) cX)
                   (TMap.add t0 (Build_ThreadState (ts_op tsL) p (ts_pend tsL)) c1) c2).
               { apply hpools_update_left; auto. }
               rewrite ts_left_unfold in Hp'. simpl in Hp'.
               assert (Hs1 : trace_steps M1 (mkTraceConfig (proj_l s0) sigma1 c1)
                        (mkTraceConfig (proj_l s0) sigma1
                          (TMap.add t0 (Build_ThreadState (ts_op tsL) p (ts_pend tsL)) c1))).
               { apply rt_step. eapply TraceStepTau. econstructor.
                 - exact HfindL.
                 - constructor.
                 - reflexivity. }
               assert (Hs2 : trace_steps M2 (mkTraceConfig (proj_r s0) sigma2 c2)
                        (mkTraceConfig (proj_r s0) sigma2 c2)).
               { apply rt_refl. }
               exists sigma1, sigma2,
                 (TMap.add t0 (Build_ThreadState (ts_op tsL) p (ts_pend tsL)) c1), c2.
               repeat split; auto.
          * injection Heqc as Heqc. subst ts1.
            rewrite ts_right_unfold_gen in Hstep0.
            destruct (ts_prog tsR) eqn:Hprogeq.
            -- rewrite liftRightProgVis in Hstep0. inversion Hstep0.
            -- rewrite liftRightProgRet in Hstep0. inversion Hstep0.
            -- rewrite liftRightProgTau in Hstep0. dependent destruction Hstep0.
               simpl in HeqR.
               assert (HfindR : TMap.find t0 c2 = Some (Build_ThreadState (ts_op tsR) (Tau p) (ts_pend tsR))).
               { rewrite HeqR. f_equal. rewrite <- Hprogeq. destruct tsR; reflexivity. }
               assert (Hp' : hpools
                   (TMap.add t0 (ts_right (Build_ThreadState (ts_op tsR) p (ts_pend tsR))) cX)
                   c1 (TMap.add t0 (Build_ThreadState (ts_op tsR) p (ts_pend tsR)) c2)).
               { apply hpools_update_right; auto. }
               rewrite ts_right_unfold in Hp'. simpl in Hp'.
               assert (Hs1 : trace_steps M1 (mkTraceConfig (proj_l s0) sigma1 c1)
                        (mkTraceConfig (proj_l s0) sigma1 c1)).
               { apply rt_refl. }
               assert (Hs2 : trace_steps M2 (mkTraceConfig (proj_r s0) sigma2 c2)
                        (mkTraceConfig (proj_r s0) sigma2
                          (TMap.add t0 (Build_ThreadState (ts_op tsR) p (ts_pend tsR)) c2))).
               { apply rt_step. eapply TraceStepTau. econstructor.
                 - exact HfindR.
                 - constructor.
                 - reflexivity. }
               exists sigma1, sigma2,
                 c1, (TMap.add t0 (Build_ThreadState (ts_op tsR) p (ts_pend tsR)) c2).
               repeat split; auto.
        + (* TraceStepError *)
          pose proof (Hp (te_tid ev)) as Ht. simpl in Ht. simpl in Hfind. rewrite Hfind in Ht.
          apply hthread_inv in Ht.
          destruct Ht as
            [[Heqc _] | [[tsL [Heqc [HeqL HeqR]]] | [tsR [Heqc [HeqL HeqR]]]]];
            try (rewrite Heqc in Hfind; discriminate).
          * (* left half errors *)
            injection Heqc as Heqc. subst ts.
            rewrite ts_left_unfold_gen in Herror.
            dependent destruction Herror.
            destruct (ts_prog tsL) eqn:Hprogeq;
              [ rewrite liftLeftProgVis in x
              | rewrite liftLeftProgRet in x; discriminate
              | rewrite liftLeftProgTau in x; discriminate ].
            dependent destruction x.
            destruct (ts_pend tsL) as [p1|] eqn:Hpendeq; simpl in x0; try discriminate.
            simpl in HeqL.
            assert (HfindL : TMap.find t0 c1 = Some (Build_ThreadState (ts_op tsL) (Vis m0 k0) None)).
            { rewrite HeqL. f_equal. rewrite <- Hprogeq, <- Hpendeq. destruct tsL; reflexivity. }
            assert (Hs1 : trace_steps M1 (mkTraceConfig (proj_l s0) sigma1 c1)
                     (mkTraceConfig
                        (proj_l (s0 ++ @TErr (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) (ts_op tsL)) :: nil))
                        sigma1 c1)).
            { rewrite proj_l_app, proj_l_err_inl_singleton.
              apply rt_step. eapply (TraceStepError M1 (proj_l s0) sigma1 c1 (ts_op tsL)
                            (Build_ThreadEvent t0 (InvEv m0))
                            (Build_ThreadState (ts_op tsL) (Vis m0 k0) None)).
              - exact HfindL.
              - econstructor. exact Herror. }
            assert (Hs2 : trace_steps M2 (mkTraceConfig (proj_r s0) sigma2 c2)
                     (mkTraceConfig
                        (proj_r (s0 ++ @TErr (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) (ts_op tsL)) :: nil))
                        sigma2 c2)).
            { rewrite proj_r_app, proj_r_err_inl_singleton, app_nil_r. apply rt_refl. }
            exists sigma1, sigma2, c1, c2.
            repeat split; auto.
          * (* right half errors *)
            injection Heqc as Heqc. subst ts.
            rewrite ts_right_unfold_gen in Herror.
            dependent destruction Herror.
            destruct (ts_prog tsR) eqn:Hprogeq;
              [ rewrite liftRightProgVis in x
              | rewrite liftRightProgRet in x; discriminate
              | rewrite liftRightProgTau in x; discriminate ].
            dependent destruction x.
            destruct (ts_pend tsR) as [p1|] eqn:Hpendeq; simpl in x0; try discriminate.
            simpl in HeqR.
            assert (HfindR : TMap.find t0 c2 = Some (Build_ThreadState (ts_op tsR) (Vis m0 k0) None)).
            { rewrite HeqR. f_equal. rewrite <- Hprogeq, <- Hpendeq. destruct tsR; reflexivity. }
            assert (Hs1 : trace_steps M1 (mkTraceConfig (proj_l s0) sigma1 c1)
                     (mkTraceConfig
                        (proj_l (s0 ++ @TErr (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) (ts_op tsR)) :: nil))
                        sigma1 c1)).
            { rewrite proj_l_app, proj_l_err_inr_singleton, app_nil_r. apply rt_refl. }
            assert (Hs2 : trace_steps M2 (mkTraceConfig (proj_r s0) sigma2 c2)
                     (mkTraceConfig
                        (proj_r (s0 ++ @TErr (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) (ts_op tsR)) :: nil))
                        sigma2 c2)).
            { rewrite proj_r_app, proj_r_err_inr_singleton.
              apply rt_step. eapply (TraceStepError M2 (proj_r s0) sigma2 c2 (ts_op tsR)
                            (Build_ThreadEvent t0 (InvEv m0))
                            (Build_ThreadState (ts_op tsR) (Vis m0 k0) None)).
              - exact HfindR.
              - econstructor. exact Herror. }
            exists sigma1, sigma2, c1, c2.
            repeat split; auto.
      - (* rt_refl *)
        exists sigma1, sigma2, c1, c2.
        repeat split; auto; apply rt_refl.
      - (* rt_trans *)
        destruct (IH1 sigma1 sigma2 c1 c2 HX Hp)
          as [sigma1' [sigma2' [c1' [c2' [HY0 [Hs1 [Hs2 Hp']]]]]]].
        destruct (IH2 sigma1' sigma2' c1' c2' HY0 Hp')
          as [sigma1'' [sigma2'' [c1'' [c2'' [HZ [Hs1' [Hs2' Hp'']]]]]]].
        exists sigma1'', sigma2'', c1'', c2''.
        repeat split; auto.
        + eapply rt_trans; eauto.
        + eapply rt_trans; eauto.
    Qed.
  End HCompDecompose.

  (** * Recomposition: the converse of [hcomp_decompose], specialized to
      recombining two independently-witnessed [idImpl] replays (one for
      [proj_l], one for [proj_r]) back into a single [idImpl ⊗ idImpl]
      replay of the *original* combined trace, in its exact original
      interleaving. Unlike [hcomp_decompose] this cannot be proven for
      [M1]/[M2] in isolation: embedding a step of (say) [idImpl1] via
      [ts_left] needs the *other* side's thread to be inactive, which is
      not visible from [idImpl1]'s own run. What makes it provable here is
      [pool_dom_invariant]/[trace_active] (thread activity is a function of
      the trace alone, not of which implementation replays it) together
      with the *original* [M1 ⊗ M2] run's own [hpools] invariant (already
      established by [hcomp_decompose]): both [c1]/[c2] (the original run's
      own pools) and [cabs1]/[cabs2] (the [idImpl] replay's pools) satisfy
      the same "domain = trace_active" criterion, so exclusivity transfers
      from one to the other. *)
  Section HCompRecombine.
    Context {E1 F1 E2 F2 : Op.t}.
    Context {VE1 : @LTS E1} {VE2 : @LTS E2}.
    Context (M1 : ModuleImpl E1 F1) (M2 : ModuleImpl E2 F2).
    Context {VF1 : @LTS F1} {VF2 : @LTS F2}.

    (* A trace-preserving (purely invisible) run of one side embeds into
       the combined system unconditionally: [ustep]/[taustep] only ever
       update the value already stored at an already-active thread, and
       [hpools]'s own exclusivity (an active thread is on exactly one side)
       already gives the needed "other side untouched" fact directly, with
       no need for [trace_active] reasoning. *)
    Lemma hcomp_embed_invisible_left :
      forall (A B : @TraceConfig F1 F1 VF1), trace_steps CompLin.idImpl A B ->
        tc_trace A = tc_trace B ->
        forall (s0 : Trace (Sig.Plus.omap F1 F2)) (sigma2 : State VF2) (c2 : @ThreadPoolState F2 F2)
          (cX : @ThreadPoolState (Sig.Plus.omap F1 F2) (Sig.Plus.omap F1 F2)),
          proj_l s0 = tc_trace A -> hpools cX (tc_pool A) c2 ->
          exists cX', trace_steps (implHComp CompLin.idImpl CompLin.idImpl)
            (mkTraceConfig s0 (pair (tc_state A) sigma2 : State (tens_lts VF1 VF2)) cX)
            (mkTraceConfig s0 (pair (tc_state B) sigma2 : State (tens_lts VF1 VF2)) cX') /\
            hpools cX' (tc_pool B) c2.
    Proof.
      intros A B Htr.
      induction Htr as [A B Hstep | A | A Y B Htr1 IH1 Htr2 IH2];
        intros Heq s0 sigma2 c2 cX Hpl Hp.
      - destruct Hstep as [s sigma c t f c' Hstep | s sigma c t f ret c' Hstep
                           | s sigma c ev sigma' c' Hstep | s sigma c t c' Hstep
                           | s sigma c f0 ev ts Hfind Herror]; simpl in *.
        + exfalso. inversion Hstep as [Hfind Hupd]; subst.
          apply (f_equal (@List.length _)) in Heq. rewrite app_length in Heq. simpl in Heq. lia.
        + exfalso. inversion Hstep as [Hfind Hupd]; subst.
          apply (f_equal (@List.length _)) in Heq. rewrite app_length in Heq. simpl in Heq. lia.
        + (* TraceStepU *)
          inversion Hstep as [f0 ts1 ts2 Hfind Hstep0 Hupd]; subst.
          pose proof (Hp (te_tid ev)) as Ht. simpl in Ht.
          apply hthread_inv in Ht.
          destruct Ht as
            [[Heqc [Heq1 Heq2]] | [[tsL [Heqc [HeqL HeqR]]] | [tsR [Heqc [HeqL HeqR]]]]].
          * rewrite Heq1 in Hfind. discriminate.
          * rewrite HeqL in Hfind. injection Hfind as Hfind. subst tsL.
            dependent destruction Hstep0.
            -- (* ts_inv *)
               exists (TMap.add t0 (ts_left (Build_ThreadState f0 (Vis op k) (Some op))) cX).
               split.
               ++ apply rt_step.
                  eapply TraceStepU with (ev := Build_ThreadEvent t0 (@InvEv (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) op))).
                  eapply (UStep _ _ _ _ _ (@inl (Sig.op F1) (Sig.op F2) f0 : Sig.op (Sig.Plus.omap F1 F2))
                    (ts_left (Build_ThreadState f0 (Vis op k) None))
                    (ts_left (Build_ThreadState f0 (Vis op k) (Some op)))).
                  ** exact Heqc.
                  ** rewrite !ts_left_unfold. simpl. rewrite !liftLeftProgVis.
                     eapply (ts_inv (@inl (Sig.op F1) (Sig.op F2) f0 : Sig.op (Sig.Plus.omap F1 F2)) t0 (@inl (Sig.op F1) (Sig.op F2) op : Sig.op (Sig.Plus.omap F1 F2)) (fun a => liftLeftProg (k a))).
                     split; [exact Hstep0 | reflexivity].
                  ** reflexivity.
               ++ apply hpools_update_left; auto.
            -- (* ts_res *)
               exists (TMap.add t0 (ts_left (Build_ThreadState f0 (k ret) None)) cX).
               split.
               ++ apply rt_step.
                  eapply TraceStepU with (ev := Build_ThreadEvent t0 (@ResEv (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) op) ret)).
                  eapply (UStep _ _ _ _ _ (@inl (Sig.op F1) (Sig.op F2) f0 : Sig.op (Sig.Plus.omap F1 F2))
                    (ts_left (Build_ThreadState f0 (Vis op k) (Some op)))
                    (ts_left (Build_ThreadState f0 (k ret) None))).
                  ** exact Heqc.
                  ** rewrite !ts_left_unfold. simpl. rewrite !liftLeftProgVis.
                     eapply (ts_res (@inl (Sig.op F1) (Sig.op F2) f0 : Sig.op (Sig.Plus.omap F1 F2)) t0 (@inl (Sig.op F1) (Sig.op F2) op : Sig.op (Sig.Plus.omap F1 F2)) ret (fun a => liftLeftProg (k a))).
                     split; [exact Hstep0 | reflexivity].
                  ** reflexivity.
               ++ apply hpools_update_left; auto.
          * rewrite HeqL in Hfind. discriminate.
        + (* TraceStepTau *)
          inversion Hstep as [ts1 ts2 Hfind Hstep0 Hupd]; subst.
          pose proof (Hp t) as Ht. simpl in Ht.
          apply hthread_inv in Ht.
          destruct Ht as
            [[Heqc [Heq1 Heq2]] | [[tsL [Heqc [HeqL HeqR]]] | [tsR [Heqc [HeqL HeqR]]]]].
          * rewrite Heq1 in Hfind. discriminate.
          * rewrite HeqL in Hfind. injection Hfind as Hfind. subst tsL.
            dependent destruction Hstep0.
            exists (TMap.add t (ts_left (Build_ThreadState f p b)) cX).
            split.
            -- apply rt_step. eapply TraceStepTau.
               eapply (TauStep _ _ _ (ts_left (Build_ThreadState f (Tau p) b))
                 (ts_left (Build_ThreadState f p b))).
               ++ exact Heqc.
               ++ unfold ts_left; simpl; rewrite liftLeftProgTau; simpl.
                  apply (@ts_tau (Sig.Plus.omap F1 F2) (Sig.Plus.omap F1 F2)
                    (@inl (Sig.op F1) (Sig.op F2) f) (liftLeftProg (E2 := F2) p)
                    (option_map (@inl (Sig.op F1) (Sig.op F2)) b)).
               ++ reflexivity.
            -- apply hpools_update_left; auto.
          * rewrite HeqL in Hfind. discriminate.
        + exfalso.
          apply (f_equal (@List.length _)) in Heq. rewrite app_length in Heq. simpl in Heq. lia.
      - exists cX. split; [apply rt_refl | exact Hp].
      - assert (HeqY : tc_trace Y = tc_trace A).
        { eapply trace_steps_flat_mid.
          - eapply rt_trans; [exact Htr1 | exact Htr2].
          - exact Heq.
          - exact Htr1.
          - exact Htr2. }
        destruct (IH1 (eq_sym HeqY) s0 sigma2 c2 cX Hpl Hp) as [cX1 [Hs1 Hp1]].
        assert (HplY : proj_l s0 = tc_trace Y) by (rewrite Hpl, HeqY; reflexivity).
        destruct (IH2 (eq_trans HeqY Heq) s0 sigma2 c2 cX1 HplY Hp1) as [cX2 [Hs2 Hp2]].
        exists cX2. split; [eapply rt_trans; eauto | exact Hp2].
    Qed.

    Lemma hcomp_embed_invisible_right :
      forall (A B : @TraceConfig F2 F2 VF2), trace_steps CompLin.idImpl A B ->
        tc_trace A = tc_trace B ->
        forall (s0 : Trace (Sig.Plus.omap F1 F2)) (sigma1 : State VF1) (c1 : @ThreadPoolState F1 F1)
          (cX : @ThreadPoolState (Sig.Plus.omap F1 F2) (Sig.Plus.omap F1 F2)),
          proj_r s0 = tc_trace A -> hpools cX c1 (tc_pool A) ->
          exists cX', trace_steps (implHComp CompLin.idImpl CompLin.idImpl)
            (mkTraceConfig s0 (pair sigma1 (tc_state A) : State (tens_lts VF1 VF2)) cX)
            (mkTraceConfig s0 (pair sigma1 (tc_state B) : State (tens_lts VF1 VF2)) cX') /\
            hpools cX' c1 (tc_pool B).
    Proof.
      intros A B Htr.
      induction Htr as [A B Hstep | A | A Y B Htr1 IH1 Htr2 IH2];
        intros Heq s0 sigma1 c1 cX Hpr Hp.
      - destruct Hstep as [s sigma c t f c' Hstep | s sigma c t f ret c' Hstep
                           | s sigma c ev sigma' c' Hstep | s sigma c t c' Hstep
                           | s sigma c f0 ev ts Hfind Herror]; simpl in *.
        + exfalso. inversion Hstep as [Hfind Hupd]; subst.
          apply (f_equal (@List.length _)) in Heq. rewrite app_length in Heq. simpl in Heq. lia.
        + exfalso. inversion Hstep as [Hfind Hupd]; subst.
          apply (f_equal (@List.length _)) in Heq. rewrite app_length in Heq. simpl in Heq. lia.
        + (* TraceStepU *)
          inversion Hstep as [f0 ts1 ts2 Hfind Hstep0 Hupd]; subst.
          pose proof (Hp (te_tid ev)) as Ht. simpl in Ht.
          apply hthread_inv in Ht.
          destruct Ht as
            [[Heqc [Heq1 Heq2]] | [[tsL [Heqc [HeqL HeqR]]] | [tsR [Heqc [HeqL HeqR]]]]].
          * rewrite Heq2 in Hfind. discriminate.
          * rewrite HeqR in Hfind. discriminate.
          * rewrite HeqR in Hfind. injection Hfind as Hfind. subst tsR.
            dependent destruction Hstep0.
            -- (* ts_inv *)
               exists (TMap.add t0 (ts_right (Build_ThreadState f0 (Vis op k) (Some op))) cX).
               split.
               ++ apply rt_step.
                  eapply TraceStepU with (ev := Build_ThreadEvent t0 (@InvEv (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) op))).
                  eapply (UStep _ _ _ _ _ (@inr (Sig.op F1) (Sig.op F2) f0 : Sig.op (Sig.Plus.omap F1 F2))
                    (ts_right (Build_ThreadState f0 (Vis op k) None))
                    (ts_right (Build_ThreadState f0 (Vis op k) (Some op)))).
                  ** exact Heqc.
                  ** unfold ts_right; simpl.
                     rewrite liftRightProgVis.
                     eapply (ts_inv (@inr (Sig.op F1) (Sig.op F2) f0 : Sig.op (Sig.Plus.omap F1 F2)) t0
                       (@inr (Sig.op F1) (Sig.op F2) op : Sig.op (Sig.Plus.omap F1 F2))
                       (fun a => liftRightProg (k a))).
                     split; [exact Hstep0 | reflexivity].
                  ** reflexivity.
               ++ apply hpools_update_right; auto.
            -- (* ts_res *)
               exists (TMap.add t0 (ts_right (Build_ThreadState f0 (k ret) None)) cX).
               split.
               ++ apply rt_step.
                  eapply TraceStepU with (ev := Build_ThreadEvent t0 (@ResEv (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) op) ret)).
                  eapply (UStep _ _ _ _ _ (@inr (Sig.op F1) (Sig.op F2) f0 : Sig.op (Sig.Plus.omap F1 F2))
                    (ts_right (Build_ThreadState f0 (Vis op k) (Some op)))
                    (ts_right (Build_ThreadState f0 (k ret) None))).
                  ** exact Heqc.
                  ** unfold ts_right; simpl.
                     rewrite liftRightProgVis.
                     eapply (ts_res (@inr (Sig.op F1) (Sig.op F2) f0 : Sig.op (Sig.Plus.omap F1 F2)) t0
                       (@inr (Sig.op F1) (Sig.op F2) op : Sig.op (Sig.Plus.omap F1 F2)) ret
                       (fun a => liftRightProg (k a))).
                     split; [exact Hstep0 | reflexivity].
                  ** reflexivity.
               ++ apply hpools_update_right; auto.
        + (* TraceStepTau *)
          inversion Hstep as [ts1 ts2 Hfind Hstep0 Hupd]; subst.
          pose proof (Hp t) as Ht. simpl in Ht.
          apply hthread_inv in Ht.
          destruct Ht as
            [[Heqc [Heq1 Heq2]] | [[tsL [Heqc [HeqL HeqR]]] | [tsR [Heqc [HeqL HeqR]]]]].
          * rewrite Heq2 in Hfind. discriminate.
          * rewrite HeqR in Hfind. discriminate.
          * rewrite HeqR in Hfind. injection Hfind as Hfind. subst tsR.
            dependent destruction Hstep0.
            exists (TMap.add t (ts_right (Build_ThreadState f p b)) cX).
            split.
            -- apply rt_step. eapply TraceStepTau.
               eapply (TauStep _ _ _ (ts_right (Build_ThreadState f (Tau p) b))
                 (ts_right (Build_ThreadState f p b))).
               ++ exact Heqc.
               ++ unfold ts_right; simpl; rewrite liftRightProgTau; simpl.
                  apply (@ts_tau (Sig.Plus.omap F1 F2) (Sig.Plus.omap F1 F2)
                    (@inr (Sig.op F1) (Sig.op F2) f) (liftRightProg (E1 := F1) p)
                    (option_map (@inr (Sig.op F1) (Sig.op F2)) b)).
               ++ reflexivity.
            -- apply hpools_update_right; auto.
        + exfalso.
          apply (f_equal (@List.length _)) in Heq. rewrite app_length in Heq. simpl in Heq. lia.
      - exists cX. split; [apply rt_refl | exact Hp].
      - assert (HeqY : tc_trace Y = tc_trace A).
        { eapply trace_steps_flat_mid.
          - eapply rt_trans; [exact Htr1 | exact Htr2].
          - exact Heq.
          - exact Htr1.
          - exact Htr2. }
        destruct (IH1 (eq_sym HeqY) s0 sigma1 c1 cX Hpr Hp) as [cX1 [Hs1 Hp1]].
        assert (HprY : proj_r s0 = tc_trace Y) by (rewrite Hpr, HeqY; reflexivity).
        destruct (IH2 (eq_trans HeqY Heq) s0 sigma1 c1 cX1 HprY Hp1) as [cX2 [Hs2 Hp2]].
        exists cX2. split; [eapply rt_trans; eauto | exact Hp2].
    Qed.

    (* Tagging a single [F1]- (resp. [F2]-)side trace item with [inl]
       (resp. [inr]) to embed it into the combined signature: the
       counterpart, at the single-item level, of [proj_l]/[proj_r]. *)
    Definition embed_l_item (x : TraceItem F1) : TraceItem (Sig.Plus.omap F1 F2) :=
      match x with
      | TEvent ev =>
          TEvent (Build_ThreadEvent (te_tid ev)
            (match te_ev ev with
             | InvEv f => @InvEv (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) f)
             | ResEv f r => @ResEv (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) f) r
             end))
      | TErr f => @TErr (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) f)
      end.

    Definition embed_r_item (x : TraceItem F2) : TraceItem (Sig.Plus.omap F1 F2) :=
      match x with
      | TEvent ev =>
          TEvent (Build_ThreadEvent (te_tid ev)
            (match te_ev ev with
             | InvEv f => @InvEv (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) f)
             | ResEv f r => @ResEv (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) f) r
             end))
      | TErr f => @TErr (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) f)
      end.

    (* A single growing step ([TraceStepInv]/[TraceStepRet]/[TraceStepError])
       of [idImpl] embeds via [ts_left], exactly like the invisible steps
       above, EXCEPT that opening a brand new thread ([TraceStepInv]) needs
       the other side to already be known-inactive for that thread — the
       one place [pool_dom_invariant]/[trace_active] genuinely earns its
       keep, since [hpools]'s own exclusivity (used for every other case)
       isn't enough on its own. [TraceStepU]/[TraceStepTau] are ruled out by
       the growth hypothesis (they never grow the trace). *)
    Lemma hcomp_embed_one_left :
      forall (Mid1 Mid2 : @TraceConfig F1 F1 VF1) (it : TraceItem F1),
        trace_step CompLin.idImpl Mid1 Mid2 -> tc_trace Mid2 = tc_trace Mid1 ++ it :: nil ->
        forall (s0 : Trace (Sig.Plus.omap F1 F2)) (sigma2 : State VF2) (c2 : @ThreadPoolState F2 F2)
          (cX : @ThreadPoolState (Sig.Plus.omap F1 F2) (Sig.Plus.omap F1 F2)),
          proj_l s0 = tc_trace Mid1 -> hpools cX (tc_pool Mid1) c2 ->
          (forall t f, it = TEvent (Build_ThreadEvent t (InvEv f)) -> TMap.find t c2 = None) ->
          exists cX',
            trace_steps (implHComp CompLin.idImpl CompLin.idImpl)
              (mkTraceConfig s0 (pair (tc_state Mid1) sigma2 : State (tens_lts VF1 VF2)) cX)
              (mkTraceConfig (s0 ++ embed_l_item it :: nil) (pair (tc_state Mid2) sigma2 : State (tens_lts VF1 VF2)) cX') /\
            hpools cX' (tc_pool Mid2) c2.
    Proof.
      intros Mid1 Mid2 it Hstep Hgrow s0 sigma2 c2 cX Hpl Hp Hcross.
      revert Hgrow Hpl Hp Hcross.
      destruct Hstep as [s sigma c t f c' Hstep | s sigma c t f ret c' Hstep
                         | s sigma c ev sigma' c' Hstep | s sigma c t c' Hstep
                         | s sigma c f0 ev ts Hfind Herror]; simpl in *;
        intros Hgrow Hpl Hp Hcross.
      - (* TraceStepInv *)
        inversion Hstep as [Hfindnone Hupd]; subst.
        apply app_inv_head in Hgrow. injection Hgrow as Hgrow. subst it.
        pose proof (Hcross t f eq_refl) as Hc2none.
        simpl.
        exists (TMap.add t (ts_left (Build_ThreadState f (CompLin.idImpl f t) None)) cX).
        split.
        + apply rt_step. eapply TraceStepInv. econstructor.
          * pose proof (Hp t) as Ht.
            apply hthread_inv in Ht.
            destruct Ht as
              [[Heqc _] | [[tsL [Heqc [HeqL HeqR]]] | [tsR [Heqc [HeqL HeqR]]]]].
            -- exact Heqc.
            -- rewrite HeqL in Hfindnone. discriminate.
            -- rewrite HeqR in Hc2none. discriminate.
          * reflexivity.
        + apply hpools_update_left; auto.
      - (* TraceStepRet *)
        inversion Hstep as [Hfindsome Hupd]; subst.
        apply app_inv_head in Hgrow. injection Hgrow as Hgrow. subst it.
        pose proof (Hp t) as Ht. simpl in Ht.
        apply hthread_inv in Ht.
        destruct Ht as
          [[Heqc [Heq1 Heq2]] | [[tsL [Heqc [HeqL HeqR]]] | [tsR [Heqc [HeqL HeqR]]]]].
        + rewrite Heq1 in Hfindsome. discriminate.
        + simpl.
          exists (TMap.remove t cX).
          split.
          * apply rt_step. eapply TraceStepRet. econstructor.
            -- rewrite HeqL in Hfindsome. injection Hfindsome as Hfindsome. subst tsL.
               unfold ts_left in Heqc; simpl in Heqc; rewrite liftLeftProgRet in Heqc.
               exact Heqc.
            -- reflexivity.
          * apply hpools_remove_left; auto.
        + rewrite HeqL in Hfindsome. discriminate.
      - (* TraceStepU: impossible, doesn't grow the trace *)
        exfalso. inversion Hstep as [f0 ts1 ts2 Hfind0 Hstep0 Hupd]; subst.
        apply (f_equal (@List.length _)) in Hgrow. rewrite app_length in Hgrow. simpl in Hgrow. lia.
      - (* TraceStepTau: impossible, doesn't grow the trace *)
        exfalso. inversion Hstep as [ts1 ts2 Hfind0 Hstep0 Hupd]; subst.
        apply (f_equal (@List.length _)) in Hgrow. rewrite app_length in Hgrow. simpl in Hgrow. lia.
      - (* TraceStepError *)
        apply app_inv_head in Hgrow. injection Hgrow as Hgrow. subst it.
        pose proof (Hp (te_tid ev)) as Ht. simpl in Ht.
        apply hthread_inv in Ht.
        destruct Ht as
          [[Heqc [Heq1 Heq2]] | [[tsL [Heqc [HeqL HeqR]]] | [tsR [Heqc [HeqL HeqR]]]]].
        + rewrite Heq1 in Hfind. discriminate.
        + rewrite HeqL in Hfind. injection Hfind as Hfind. subst tsL.
          rename s0 into sX.
          dependent destruction Herror.
          simpl.
          exists cX.
          split.
          * apply rt_step.
            eapply (TraceStepError (implHComp CompLin.idImpl CompLin.idImpl)
                       sX (pair s0 sigma2 : State (tens_lts VF1 VF2)) cX
                       (@inl (Sig.op F1) (Sig.op F2) f0 : Sig.op (Sig.Plus.omap F1 F2))
                       (Build_ThreadEvent t0 (@InvEv (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) op)))
                       (ts_left (Build_ThreadState f0 (Vis op k) None))).
            -- exact Heqc.
            -- unfold ts_left; simpl; rewrite liftLeftProgVis.
               eapply (ts_err (@inl (Sig.op F1) (Sig.op F2) f0 : Sig.op (Sig.Plus.omap F1 F2)) t0
                 (@inl (Sig.op F1) (Sig.op F2) op : Sig.op (Sig.Plus.omap F1 F2))
                 (pair s0 sigma2 : State (tens_lts VF1 VF2))
                 (fun a => liftLeftProg (k a))).
               exact Herror.
          * exact Hp.
        + rewrite HeqL in Hfind. discriminate.
    Qed.

    Lemma hcomp_embed_one_right :
      forall (Mid1 Mid2 : @TraceConfig F2 F2 VF2) (it : TraceItem F2),
        trace_step CompLin.idImpl Mid1 Mid2 -> tc_trace Mid2 = tc_trace Mid1 ++ it :: nil ->
        forall (s0 : Trace (Sig.Plus.omap F1 F2)) (sigma1 : State VF1) (c1 : @ThreadPoolState F1 F1)
          (cX : @ThreadPoolState (Sig.Plus.omap F1 F2) (Sig.Plus.omap F1 F2)),
          proj_r s0 = tc_trace Mid1 -> hpools cX c1 (tc_pool Mid1) ->
          (forall t f, it = TEvent (Build_ThreadEvent t (InvEv f)) -> TMap.find t c1 = None) ->
          exists cX',
            trace_steps (implHComp CompLin.idImpl CompLin.idImpl)
              (mkTraceConfig s0 (pair sigma1 (tc_state Mid1) : State (tens_lts VF1 VF2)) cX)
              (mkTraceConfig (s0 ++ embed_r_item it :: nil) (pair sigma1 (tc_state Mid2) : State (tens_lts VF1 VF2)) cX') /\
            hpools cX' c1 (tc_pool Mid2).
    Proof.
      intros Mid1 Mid2 it Hstep Hgrow s0 sigma1 c1 cX Hpr Hp Hcross.
      revert Hgrow Hpr Hp Hcross.
      destruct Hstep as [s sigma c t f c' Hstep | s sigma c t f ret c' Hstep
                         | s sigma c ev sigma' c' Hstep | s sigma c t c' Hstep
                         | s sigma c f0 ev ts Hfind Herror]; simpl in *;
        intros Hgrow Hpr Hp Hcross.
      - (* TraceStepInv *)
        inversion Hstep as [Hfindnone Hupd]; subst.
        apply app_inv_head in Hgrow. injection Hgrow as Hgrow. subst it.
        pose proof (Hcross t f eq_refl) as Hc1none.
        simpl.
        exists (TMap.add t (ts_right (Build_ThreadState f (CompLin.idImpl f t) None)) cX).
        split.
        + apply rt_step. eapply TraceStepInv. econstructor.
          * pose proof (Hp t) as Ht.
            apply hthread_inv in Ht.
            destruct Ht as
              [[Heqc _] | [[tsL [Heqc [HeqL HeqR]]] | [tsR [Heqc [HeqL HeqR]]]]].
            -- exact Heqc.
            -- rewrite HeqL in Hc1none. discriminate.
            -- rewrite HeqR in Hfindnone. discriminate.
          * reflexivity.
        + apply hpools_update_right; auto.
      - (* TraceStepRet *)
        inversion Hstep as [Hfindsome Hupd]; subst.
        apply app_inv_head in Hgrow. injection Hgrow as Hgrow. subst it.
        pose proof (Hp t) as Ht. simpl in Ht.
        apply hthread_inv in Ht.
        destruct Ht as
          [[Heqc [Heq1 Heq2]] | [[tsL [Heqc [HeqL HeqR]]] | [tsR [Heqc [HeqL HeqR]]]]].
        + rewrite Heq2 in Hfindsome. discriminate.
        + rewrite HeqR in Hfindsome. discriminate.
        + simpl.
          exists (TMap.remove t cX).
          split.
          * apply rt_step. eapply TraceStepRet. econstructor.
            -- rewrite HeqR in Hfindsome. injection Hfindsome as Hfindsome. subst tsR.
               unfold ts_right in Heqc; simpl in Heqc; rewrite liftRightProgRet in Heqc.
               exact Heqc.
            -- reflexivity.
          * apply hpools_remove_right; auto.
      - (* TraceStepU: impossible, doesn't grow the trace *)
        exfalso. inversion Hstep as [f0 ts1 ts2 Hfind0 Hstep0 Hupd]; subst.
        apply (f_equal (@List.length _)) in Hgrow. rewrite app_length in Hgrow. simpl in Hgrow. lia.
      - (* TraceStepTau: impossible, doesn't grow the trace *)
        exfalso. inversion Hstep as [ts1 ts2 Hfind0 Hstep0 Hupd]; subst.
        apply (f_equal (@List.length _)) in Hgrow. rewrite app_length in Hgrow. simpl in Hgrow. lia.
      - (* TraceStepError *)
        apply app_inv_head in Hgrow. injection Hgrow as Hgrow. subst it.
        pose proof (Hp (te_tid ev)) as Ht. simpl in Ht.
        apply hthread_inv in Ht.
        destruct Ht as
          [[Heqc [Heq1 Heq2]] | [[tsL [Heqc [HeqL HeqR]]] | [tsR [Heqc [HeqL HeqR]]]]].
        + rewrite Heq2 in Hfind. discriminate.
        + rewrite HeqR in Hfind. discriminate.
        + rewrite HeqR in Hfind. injection Hfind as Hfind. subst tsR.
          rename s0 into sX.
          dependent destruction Herror.
          simpl.
          exists cX.
          split.
          * apply rt_step.
            eapply (TraceStepError (implHComp CompLin.idImpl CompLin.idImpl)
                       sX (pair sigma1 s0 : State (tens_lts VF1 VF2)) cX
                       (@inr (Sig.op F1) (Sig.op F2) f0 : Sig.op (Sig.Plus.omap F1 F2))
                       (Build_ThreadEvent t0 (@InvEv (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) op)))
                       (ts_right (Build_ThreadState f0 (Vis op k) None))).
            -- exact Heqc.
            -- unfold ts_right; simpl; rewrite liftRightProgVis.
               eapply (ts_err (@inr (Sig.op F1) (Sig.op F2) f0 : Sig.op (Sig.Plus.omap F1 F2)) t0
                 (@inr (Sig.op F1) (Sig.op F2) op : Sig.op (Sig.Plus.omap F1 F2))
                 (pair sigma1 s0 : State (tens_lts VF1 VF2))
                 (fun a => liftRightProg (k a))).
               exact Herror.
          * exact Hp.
    Qed.

    (* Whether a single combined item is dropped or kept (and re-tagged)
       by [proj_l]/[proj_r] depends only on the item itself, not on what
       follows it. *)
    Lemma proj_l_cons_case (it : TraceItem (Sig.Plus.omap F1 F2)) :
      (forall s'', proj_l (it :: s'') = proj_l s'') \/
      (exists it', forall s'', proj_l (it :: s'') = it' :: proj_l s'').
    Proof.
      destruct it as [ev | f].
      - destruct ev as [t ev0]. destruct ev0 as [[f1|f2] | [f1|f2] r].
        + right. exists (TEvent (Build_ThreadEvent t (InvEv f1))). intro s''. reflexivity.
        + left. intro s''. reflexivity.
        + right. exists (TEvent (Build_ThreadEvent t (ResEv f1 r))). intro s''. reflexivity.
        + left. intro s''. reflexivity.
      - destruct f as [f1|f2].
        + right. exists (TErr f1). intro s''. reflexivity.
        + left. intro s''. reflexivity.
    Qed.

    Lemma proj_r_cons_case (it : TraceItem (Sig.Plus.omap F1 F2)) :
      (forall s'', proj_r (it :: s'') = proj_r s'') \/
      (exists it', forall s'', proj_r (it :: s'') = it' :: proj_r s'').
    Proof.
      destruct it as [ev | f].
      - destruct ev as [t ev0]. destruct ev0 as [[f1|f2] | [f1|f2] r].
        + left. intro s''. reflexivity.
        + right. exists (TEvent (Build_ThreadEvent t (InvEv f2))). intro s''. reflexivity.
        + left. intro s''. reflexivity.
        + right. exists (TEvent (Build_ThreadEvent t (ResEv f2 r))). intro s''. reflexivity.
      - destruct f as [f1|f2].
        + left. intro s''. reflexivity.
        + right. exists (TErr f2). intro s''. reflexivity.
    Qed.

    (* Given that a prefix [p1] of [proj_l s] is known (i.e. [proj_l s]
       extends it), there is an actual prefix [p] of the combined trace [s]
       itself whose own [proj_l] is exactly [p1] — needed to convert a
       "[idImpl1] errors at [p1]" fact into a "the combined system errors
       at some actual prefix of [s]" fact. *)
    Lemma proj_l_prefix_exists :
      forall (s : Trace (Sig.Plus.omap F1 F2)) (p1 : Trace F1),
        (exists tl1, proj_l s = p1 ++ tl1) ->
        exists (p tl : Trace (Sig.Plus.omap F1 F2)), s = p ++ tl /\ proj_l p = p1.
    Proof.
      induction s as [| it s' IH]; intros p1 [tl1 Heq].
      - simpl in Heq. symmetry in Heq. apply app_eq_nil in Heq as [Heq1 _].
        subst p1. exists nil, nil. auto.
      - destruct p1 as [| it1 p1'].
        + exists nil, (it :: s'). auto.
        + destruct (proj_l_cons_case it) as [Hdrop | [it' Hkeep]].
          * rewrite Hdrop in Heq.
            destruct (IH (it1 :: p1') (ex_intro _ tl1 Heq)) as [p [tl [Heqs Heqp]]].
            exists (it :: p), tl. split.
            -- simpl. rewrite Heqs. reflexivity.
            -- rewrite Hdrop. exact Heqp.
          * rewrite Hkeep in Heq. simpl in Heq. injection Heq as Heqit Heqrest. subst it'.
            destruct (IH p1' (ex_intro _ tl1 Heqrest)) as [p [tl [Heqs Heqp]]].
            exists (it :: p), tl. split.
            -- simpl. rewrite Heqs. reflexivity.
            -- rewrite Hkeep, Heqp. reflexivity.
    Qed.

    Lemma proj_r_prefix_exists :
      forall (s : Trace (Sig.Plus.omap F1 F2)) (p2 : Trace F2),
        (exists tl2, proj_r s = p2 ++ tl2) ->
        exists (p tl : Trace (Sig.Plus.omap F1 F2)), s = p ++ tl /\ proj_r p = p2.
    Proof.
      induction s as [| it s' IH]; intros p2 [tl2 Heq].
      - simpl in Heq. symmetry in Heq. apply app_eq_nil in Heq as [Heq1 _].
        subst p2. exists nil, nil. auto.
      - destruct p2 as [| it2 p2'].
        + exists nil, (it :: s'). auto.
        + destruct (proj_r_cons_case it) as [Hdrop | [it' Hkeep]].
          * rewrite Hdrop in Heq.
            destruct (IH (it2 :: p2') (ex_intro _ tl2 Heq)) as [p [tl [Heqs Heqp]]].
            exists (it :: p), tl. split.
            -- simpl. rewrite Heqs. reflexivity.
            -- rewrite Hdrop. exact Heqp.
          * rewrite Hkeep in Heq. simpl in Heq. injection Heq as Heqit Heqrest. subst it'.
            destruct (IH p2' (ex_intro _ tl2 Heqrest)) as [p [tl [Heqs Heqp]]].
            exists (it :: p), tl. split.
            -- simpl. rewrite Heqs. reflexivity.
            -- rewrite Hkeep, Heqp. reflexivity.
    Qed.

    (* Two prefixes of the same list, of the same length, coincide. *)
    Lemma prefix_eq_of_same_length {A} :
      forall (l1 l2 t1 t2 : list A),
        l1 ++ t1 = l2 ++ t2 -> List.length l1 = List.length l2 -> l1 = l2.
    Proof.
      induction l1 as [| a l1 IH]; intros l2 t1 t2 Heq Hlen.
      - destruct l2 as [| b l2]; [reflexivity | simpl in Hlen; discriminate].
      - destruct l2 as [| b l2]; [simpl in Hlen; discriminate |].
        simpl in Heq, Hlen. injection Heq as Heqa Heqrest. injection Hlen as Hlen'.
        subst a. f_equal. eapply IH; eauto.
    Qed.

    (* If two lists [l1]/[l2] extend to the same list (i.e. are both
       prefixes of a common list, via possibly different tails) and [l1] is
       no longer than [l2], then [l2] extends [l1]: there is a "middle"
       chunk [m] with [l2 = l1 ++ m]. *)
    Lemma prefix_le_extends {A} :
      forall (l1 l2 t1 t2 : list A),
        l1 ++ t1 = l2 ++ t2 -> List.length l1 <= List.length l2 ->
        exists m, l2 = l1 ++ m.
    Proof.
      induction l1 as [| a l1 IH]; intros l2 t1 t2 Heq Hlen.
      - exists l2. reflexivity.
      - destruct l2 as [| b l2]; [simpl in Hlen; lia |].
        simpl in Heq, Hlen. injection Heq as Heqa Heqrest.
        subst b.
        destruct (IH l2 t1 t2 Heqrest (le_S_n _ _ Hlen)) as [m Heqm].
        exists m. simpl. f_equal. exact Heqm.
    Qed.

    (* The main recomposition theorem: given the *original* [M1 ⊗ M2] run
       (which supplies, via [hcomp_decompose] and the domain-tracking
       hypotheses, exactly the cross-side exclusivity facts that
       [hcomp_embed_one_left]/[_right] need) together with two
       independently-witnessed [idImpl] replays of its two projections,
       produce a single [idImpl ⊗ idImpl] replay of the whole original
       (combined) trace. *)
    Theorem hcomp_recombine :
      forall (X Z : @TraceConfig (Sig.Plus.omap E1 E2) (Sig.Plus.omap F1 F2) (tens_lts VE1 VE2)),
        trace_steps (M1 ⊗ M2) X Z ->
        forall sigma1 sigma2 c1 c2,
          tc_state X = pair sigma1 sigma2 -> hpools (tc_pool X) c1 c2 ->
          (forall th, TMap.find th c1 = None <-> trace_active (proj_l (tc_trace X)) th false = false) ->
          (forall th, TMap.find th c2 = None <-> trace_active (proj_r (tc_trace X)) th false = false) ->
          forall (rho1 : State VF1) (cabs1 : @ThreadPoolState F1 F1) (rho2 : State VF2)
            (cabs2 : @ThreadPoolState F2 F2) cabsX,
            hpools cabsX cabs1 cabs2 ->
            (forall th, TMap.find th cabs1 = None <-> trace_active (proj_l (tc_trace X)) th false = false) ->
            (forall th, TMap.find th cabs2 = None <-> trace_active (proj_r (tc_trace X)) th false = false) ->
            forall (rho1_f : State VF1) (cabs1_f : @ThreadPoolState F1 F1),
              trace_steps CompLin.idImpl (mkTraceConfig (proj_l (tc_trace X)) rho1 cabs1)
                (mkTraceConfig (proj_l (tc_trace Z)) rho1_f cabs1_f) ->
            forall (rho2_f : State VF2) (cabs2_f : @ThreadPoolState F2 F2),
              trace_steps CompLin.idImpl (mkTraceConfig (proj_r (tc_trace X)) rho2 cabs2)
                (mkTraceConfig (proj_r (tc_trace Z)) rho2_f cabs2_f) ->
              exists cabsX_f,
                trace_steps (implHComp CompLin.idImpl CompLin.idImpl)
                  (mkTraceConfig (tc_trace X) (pair rho1 rho2 : State (tens_lts VF1 VF2)) cabsX)
                  (mkTraceConfig (tc_trace Z) (pair rho1_f rho2_f : State (tens_lts VF1 VF2)) cabsX_f) /\
                hpools cabsX_f cabs1_f cabs2_f.
    Proof.
      intros X Z Htr.
      induction Htr as [X Z Hstep | X | X Y Z Htr1 IH1 Htr2 IH2];
        intros sigma1 sigma2 c1 c2 HX Hp Hd1 Hd2
          rho1 cabs1 rho2 cabs2 cabsX Hcp Hdc1 Hdc2
          rho1_f cabs1_f Htri1 rho2_f cabs2_f Htri2.
      - (* rt_step *)
        destruct X as [s0 sigmaX cX]. simpl in HX. subst sigmaX.
        rename cX into cX0.
        revert Hp Hd1 Hd2 Htri1 Htri2.
        destruct Hstep as [s sigma c t f c' Hstep | s sigma c t f ret c' Hstep
                           | s sigma c ev sigma' c' Hstep | s sigma c t c' Hstep
                           | s sigma c f0 ev ts0 Hfind0 Herror0]; simpl in *;
          intros Hp Hd1 Hd2 Htri1 Htri2.
        + (* TraceStepInv *)
          inversion Hstep as [Hfindnone Hupd]; subst.
          destruct f as [f1 | f2].
          * (* left grows *)
            assert (Htri2' : trace_steps CompLin.idImpl (mkTraceConfig (proj_r s) rho2 cabs2) (mkTraceConfig (proj_r s) rho2_f cabs2_f)).
            { rewrite proj_r_app, proj_r_inl_singleton, app_nil_r in Htri2. exact Htri2. }
            destruct (hcomp_embed_invisible_right
                        (mkTraceConfig (proj_r s) rho2 cabs2) (mkTraceConfig (proj_r s) rho2_f cabs2_f)
                        Htri2' eq_refl s rho1 cabs1 cabsX eq_refl Hcp) as [cabsXR [HsR HpR]].
            assert (Heql : proj_l (s ++ TEvent (Build_ThreadEvent t (@InvEv (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) f1))) :: nil)
                      = proj_l s ++ TEvent (Build_ThreadEvent t (InvEv f1)) :: nil).
            { rewrite proj_l_app, proj_l_inl_singleton. reflexivity. }
            destruct (trace_steps_single_growth_split CompLin.idImpl
                        (mkTraceConfig (proj_l s) rho1 cabs1)
                        (mkTraceConfig (proj_l (s ++ TEvent (Build_ThreadEvent t (@InvEv (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) f1))) :: nil)) rho1_f cabs1_f)
                        (TEvent (Build_ThreadEvent t (InvEv f1))) Htri1 Heql)
              as [Mid1 [Mid2 [Hspre [Heqm1 [Hstepvis [Heqm2 Hssuf]]]]]].
            destruct (hcomp_embed_invisible_left (mkTraceConfig (proj_l s) rho1 cabs1) Mid1 Hspre (eq_sym Heqm1)
                        s rho2_f cabs2_f cabsXR eq_refl HpR) as [cabsXL1 [HsL1 HpL1]].
            assert (Hfindc2 : TMap.find t c2 = None).
            { pose proof (Hp t) as Ht. rewrite Hfindnone in Ht.
              apply hthread_none_inv in Ht as [_ Ht2]. exact Ht2. }
            assert (Hfindcabs2 : TMap.find t cabs2 = None).
            { apply Hdc2. apply Hd2. exact Hfindc2. }
            assert (Hfindcabs2f : TMap.find t cabs2_f = None).
            { pose proof (pool_dom_invariant CompLin.idImpl
                (mkTraceConfig (proj_r s) rho2 cabs2) (mkTraceConfig (proj_r s) rho2_f cabs2_f)
                Htri2' t (Hdc2 t)) as Hinv.
              simpl in Hinv. apply Hinv. apply Hdc2. exact Hfindcabs2. }
            assert (Hcross1 : forall t' f', TEvent (Build_ThreadEvent t (InvEv f1)) = TEvent (Build_ThreadEvent t' (InvEv f')) ->
                       TMap.find t' cabs2_f = None).
            { intros t' f' Heqit. injection Heqit as Heqit; subst t'; exact Hfindcabs2f. }
            assert (Hgrow2 : tc_trace Mid2 = proj_l (s ++ TEvent (Build_ThreadEvent t (@InvEv (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) f1))) :: nil)).
            { rewrite Heqm2. symmetry. exact Heql. }
            destruct (hcomp_embed_one_left Mid1 Mid2 (TEvent (Build_ThreadEvent t (InvEv f1))) Hstepvis
                        (eq_trans Heqm2 (f_equal (fun x => x ++ TEvent (Build_ThreadEvent t (InvEv f1)) :: nil) (eq_sym Heqm1)))
                        s rho2_f cabs2_f cabsXL1 (eq_sym Heqm1) HpL1 Hcross1)
              as [cabsXL2 [HsV HpV]].
            destruct (hcomp_embed_invisible_left Mid2
                        (mkTraceConfig (proj_l (s ++ TEvent (Build_ThreadEvent t (@InvEv (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) f1))) :: nil)) rho1_f cabs1_f)
                        Hssuf (eq_trans Heqm2 (eq_sym Heql)) (s ++ TEvent (Build_ThreadEvent t (@InvEv (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) f1))) :: nil)
                        rho2_f cabs2_f cabsXL2 (eq_sym Hgrow2) HpV) as [cabsXf [HsSuf HpSuf]].
            exists cabsXf.
            split.
            -- eapply rt_trans; [exact HsR|].
               eapply rt_trans; [exact HsL1|].
               eapply rt_trans; [exact HsV|].
               exact HsSuf.
            -- exact HpSuf.
          * (* right grows: symmetric *)
            assert (Htri1' : trace_steps CompLin.idImpl (mkTraceConfig (proj_l s) rho1 cabs1) (mkTraceConfig (proj_l s) rho1_f cabs1_f)).
            { rewrite proj_l_app, proj_l_inr_singleton, app_nil_r in Htri1. exact Htri1. }
            destruct (hcomp_embed_invisible_left
                        (mkTraceConfig (proj_l s) rho1 cabs1) (mkTraceConfig (proj_l s) rho1_f cabs1_f)
                        Htri1' eq_refl s rho2 cabs2 cabsX eq_refl Hcp) as [cabsXL [HsL HpL]].
            assert (Heqr : proj_r (s ++ TEvent (Build_ThreadEvent t (@InvEv (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) f2))) :: nil)
                      = proj_r s ++ TEvent (Build_ThreadEvent t (InvEv f2)) :: nil).
            { rewrite proj_r_app, proj_r_inr_singleton. reflexivity. }
            destruct (trace_steps_single_growth_split CompLin.idImpl
                        (mkTraceConfig (proj_r s) rho2 cabs2)
                        (mkTraceConfig (proj_r (s ++ TEvent (Build_ThreadEvent t (@InvEv (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) f2))) :: nil)) rho2_f cabs2_f)
                        (TEvent (Build_ThreadEvent t (InvEv f2))) Htri2 Heqr)
              as [Mid1 [Mid2 [Hspre [Heqm1 [Hstepvis [Heqm2 Hssuf]]]]]].
            destruct (hcomp_embed_invisible_right (mkTraceConfig (proj_r s) rho2 cabs2) Mid1 Hspre (eq_sym Heqm1)
                        s rho1_f cabs1_f cabsXL eq_refl HpL) as [cabsXR1 [HsR1 HpR1]].
            assert (Hfindc1 : TMap.find t c1 = None).
            { pose proof (Hp t) as Ht. rewrite Hfindnone in Ht.
              apply hthread_none_inv in Ht as [Ht1 _]. exact Ht1. }
            assert (Hfindcabs1 : TMap.find t cabs1 = None).
            { apply Hdc1. apply Hd1. exact Hfindc1. }
            assert (Hfindcabs1f : TMap.find t cabs1_f = None).
            { pose proof (pool_dom_invariant CompLin.idImpl
                (mkTraceConfig (proj_l s) rho1 cabs1) (mkTraceConfig (proj_l s) rho1_f cabs1_f)
                Htri1' t (Hdc1 t)) as Hinv.
              simpl in Hinv. apply Hinv. apply Hdc1. exact Hfindcabs1. }
            assert (Hcross1 : forall t' f', TEvent (Build_ThreadEvent t (InvEv f2)) = TEvent (Build_ThreadEvent t' (InvEv f')) ->
                       TMap.find t' cabs1_f = None).
            { intros t' f' Heqit. injection Heqit as Heqit; subst t'; exact Hfindcabs1f. }
            assert (Hgrow2 : tc_trace Mid2 = proj_r (s ++ TEvent (Build_ThreadEvent t (@InvEv (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) f2))) :: nil)).
            { rewrite Heqm2. symmetry. exact Heqr. }
            destruct (hcomp_embed_one_right Mid1 Mid2 (TEvent (Build_ThreadEvent t (InvEv f2))) Hstepvis
                        (eq_trans Heqm2 (f_equal (fun x => x ++ TEvent (Build_ThreadEvent t (InvEv f2)) :: nil) (eq_sym Heqm1)))
                        s rho1_f cabs1_f cabsXR1 (eq_sym Heqm1) HpR1 Hcross1)
              as [cabsXR2 [HsV HpV]].
            destruct (hcomp_embed_invisible_right Mid2
                        (mkTraceConfig (proj_r (s ++ TEvent (Build_ThreadEvent t (@InvEv (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) f2))) :: nil)) rho2_f cabs2_f)
                        Hssuf (eq_trans Heqm2 (eq_sym Heqr)) (s ++ TEvent (Build_ThreadEvent t (@InvEv (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) f2))) :: nil)
                        rho1_f cabs1_f cabsXR2 (eq_sym Hgrow2) HpV) as [cabsXf [HsSuf HpSuf]].
            exists cabsXf.
            split.
            -- eapply rt_trans; [exact HsL|].
               eapply rt_trans; [exact HsR1|].
               eapply rt_trans; [exact HsV|].
               exact HsSuf.
            -- exact HpSuf.
        + (* TraceStepRet *)
          inversion Hstep as [Hfindsome Hupd]; subst.
          destruct f as [f1 | f2].
          * (* left grows *)
            assert (Htri2' : trace_steps CompLin.idImpl (mkTraceConfig (proj_r s) rho2 cabs2) (mkTraceConfig (proj_r s) rho2_f cabs2_f)).
            { rewrite proj_r_app, proj_r_inl_singleton_res, app_nil_r in Htri2. exact Htri2. }
            destruct (hcomp_embed_invisible_right
                        (mkTraceConfig (proj_r s) rho2 cabs2) (mkTraceConfig (proj_r s) rho2_f cabs2_f)
                        Htri2' eq_refl s rho1 cabs1 cabsX eq_refl Hcp) as [cabsXR [HsR HpR]].
            assert (Heql : proj_l (s ++ TEvent (Build_ThreadEvent t (@ResEv (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) f1) ret)) :: nil)
                      = proj_l s ++ TEvent (Build_ThreadEvent t (ResEv f1 ret)) :: nil).
            { rewrite proj_l_app, proj_l_inl_singleton_res. reflexivity. }
            destruct (trace_steps_single_growth_split CompLin.idImpl
                        (mkTraceConfig (proj_l s) rho1 cabs1)
                        (mkTraceConfig (proj_l (s ++ TEvent (Build_ThreadEvent t (@ResEv (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) f1) ret)) :: nil)) rho1_f cabs1_f)
                        (TEvent (Build_ThreadEvent t (ResEv f1 ret))) Htri1 Heql)
              as [Mid1 [Mid2 [Hspre [Heqm1 [Hstepvis [Heqm2 Hssuf]]]]]].
            destruct (hcomp_embed_invisible_left (mkTraceConfig (proj_l s) rho1 cabs1) Mid1 Hspre (eq_sym Heqm1)
                        s rho2_f cabs2_f cabsXR eq_refl HpR) as [cabsXL1 [HsL1 HpL1]].
            assert (Hcross1 : forall t' f', TEvent (Build_ThreadEvent t (ResEv f1 ret)) = TEvent (Build_ThreadEvent t' (InvEv f')) ->
                       TMap.find t' cabs2_f = None).
            { intros t' f' Heqit. discriminate. }
            assert (Hgrow2 : tc_trace Mid2 = proj_l (s ++ TEvent (Build_ThreadEvent t (@ResEv (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) f1) ret)) :: nil)).
            { rewrite Heqm2. symmetry. exact Heql. }
            destruct (hcomp_embed_one_left Mid1 Mid2 (TEvent (Build_ThreadEvent t (ResEv f1 ret))) Hstepvis
                        (eq_trans Heqm2 (f_equal (fun x => x ++ TEvent (Build_ThreadEvent t (ResEv f1 ret)) :: nil) (eq_sym Heqm1)))
                        s rho2_f cabs2_f cabsXL1 (eq_sym Heqm1) HpL1 Hcross1)
              as [cabsXL2 [HsV HpV]].
            destruct (hcomp_embed_invisible_left Mid2
                        (mkTraceConfig (proj_l (s ++ TEvent (Build_ThreadEvent t (@ResEv (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) f1) ret)) :: nil)) rho1_f cabs1_f)
                        Hssuf (eq_trans Heqm2 (eq_sym Heql)) (s ++ TEvent (Build_ThreadEvent t (@ResEv (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) f1) ret)) :: nil)
                        rho2_f cabs2_f cabsXL2 (eq_sym Hgrow2) HpV) as [cabsXf [HsSuf HpSuf]].
            exists cabsXf.
            split.
            -- eapply rt_trans; [exact HsR|].
               eapply rt_trans; [exact HsL1|].
               eapply rt_trans; [exact HsV|].
               exact HsSuf.
            -- exact HpSuf.
          * (* right grows: symmetric *)
            assert (Htri1' : trace_steps CompLin.idImpl (mkTraceConfig (proj_l s) rho1 cabs1) (mkTraceConfig (proj_l s) rho1_f cabs1_f)).
            { rewrite proj_l_app, proj_l_inr_singleton_res, app_nil_r in Htri1. exact Htri1. }
            destruct (hcomp_embed_invisible_left
                        (mkTraceConfig (proj_l s) rho1 cabs1) (mkTraceConfig (proj_l s) rho1_f cabs1_f)
                        Htri1' eq_refl s rho2 cabs2 cabsX eq_refl Hcp) as [cabsXL [HsL HpL]].
            assert (Heqr : proj_r (s ++ TEvent (Build_ThreadEvent t (@ResEv (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) f2) ret)) :: nil)
                      = proj_r s ++ TEvent (Build_ThreadEvent t (ResEv f2 ret)) :: nil).
            { rewrite proj_r_app, proj_r_inr_singleton_res. reflexivity. }
            destruct (trace_steps_single_growth_split CompLin.idImpl
                        (mkTraceConfig (proj_r s) rho2 cabs2)
                        (mkTraceConfig (proj_r (s ++ TEvent (Build_ThreadEvent t (@ResEv (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) f2) ret)) :: nil)) rho2_f cabs2_f)
                        (TEvent (Build_ThreadEvent t (ResEv f2 ret))) Htri2 Heqr)
              as [Mid1 [Mid2 [Hspre [Heqm1 [Hstepvis [Heqm2 Hssuf]]]]]].
            destruct (hcomp_embed_invisible_right (mkTraceConfig (proj_r s) rho2 cabs2) Mid1 Hspre (eq_sym Heqm1)
                        s rho1_f cabs1_f cabsXL eq_refl HpL) as [cabsXR1 [HsR1 HpR1]].
            assert (Hcross1 : forall t' f', TEvent (Build_ThreadEvent t (ResEv f2 ret)) = TEvent (Build_ThreadEvent t' (InvEv f')) ->
                       TMap.find t' cabs1_f = None).
            { intros t' f' Heqit. discriminate. }
            assert (Hgrow2 : tc_trace Mid2 = proj_r (s ++ TEvent (Build_ThreadEvent t (@ResEv (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) f2) ret)) :: nil)).
            { rewrite Heqm2. symmetry. exact Heqr. }
            destruct (hcomp_embed_one_right Mid1 Mid2 (TEvent (Build_ThreadEvent t (ResEv f2 ret))) Hstepvis
                        (eq_trans Heqm2 (f_equal (fun x => x ++ TEvent (Build_ThreadEvent t (ResEv f2 ret)) :: nil) (eq_sym Heqm1)))
                        s rho1_f cabs1_f cabsXR1 (eq_sym Heqm1) HpR1 Hcross1)
              as [cabsXR2 [HsV HpV]].
            destruct (hcomp_embed_invisible_right Mid2
                        (mkTraceConfig (proj_r (s ++ TEvent (Build_ThreadEvent t (@ResEv (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) f2) ret)) :: nil)) rho2_f cabs2_f)
                        Hssuf (eq_trans Heqm2 (eq_sym Heqr)) (s ++ TEvent (Build_ThreadEvent t (@ResEv (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) f2) ret)) :: nil)
                        rho1_f cabs1_f cabsXR2 (eq_sym Hgrow2) HpV) as [cabsXf [HsSuf HpSuf]].
            exists cabsXf.
            split.
            -- eapply rt_trans; [exact HsL|].
               eapply rt_trans; [exact HsR1|].
               eapply rt_trans; [exact HsV|].
               exact HsSuf.
            -- exact HpSuf.
        + (* TraceStepU: neither side's trace grows *)
          inversion Hstep as [f0 ts1 ts2 Hfind0 Hstep0 Hupd]; subst.
          destruct (hcomp_embed_invisible_left
                      (mkTraceConfig (proj_l s) rho1 cabs1) (mkTraceConfig (proj_l s) rho1_f cabs1_f)
                      Htri1 eq_refl s rho2 cabs2 cabsX eq_refl Hcp) as [cabsX1 [Hstep1 Hp1]].
          destruct (hcomp_embed_invisible_right
                      (mkTraceConfig (proj_r s) rho2 cabs2) (mkTraceConfig (proj_r s) rho2_f cabs2_f)
                      Htri2 eq_refl s rho1_f cabs1_f cabsX1 eq_refl Hp1) as [cabsXf [Hstep2 Hp2]].
          exists cabsXf. split; [eapply rt_trans; [exact Hstep1 | exact Hstep2] | exact Hp2].
        + (* TraceStepTau: neither side's trace grows *)
          inversion Hstep as [ts1 ts2 Hfind0 Hstep0 Hupd]; subst.
          destruct (hcomp_embed_invisible_left
                      (mkTraceConfig (proj_l s) rho1 cabs1) (mkTraceConfig (proj_l s) rho1_f cabs1_f)
                      Htri1 eq_refl s rho2 cabs2 cabsX eq_refl Hcp) as [cabsX1 [Hstep1 Hp1]].
          destruct (hcomp_embed_invisible_right
                      (mkTraceConfig (proj_r s) rho2 cabs2) (mkTraceConfig (proj_r s) rho2_f cabs2_f)
                      Htri2 eq_refl s rho1_f cabs1_f cabsX1 eq_refl Hp1) as [cabsXf [Hstep2 Hp2]].
          exists cabsXf. split; [eapply rt_trans; [exact Hstep1 | exact Hstep2] | exact Hp2].
        + (* TraceStepError *)
          destruct f0 as [f1 | f2].
          * (* left errors *)
            assert (Htri2' : trace_steps CompLin.idImpl (mkTraceConfig (proj_r s) rho2 cabs2) (mkTraceConfig (proj_r s) rho2_f cabs2_f)).
            { rewrite proj_r_app, proj_r_err_inl_singleton, app_nil_r in Htri2. exact Htri2. }
            destruct (hcomp_embed_invisible_right
                        (mkTraceConfig (proj_r s) rho2 cabs2) (mkTraceConfig (proj_r s) rho2_f cabs2_f)
                        Htri2' eq_refl s rho1 cabs1 cabsX eq_refl Hcp) as [cabsXR [HsR HpR]].
            assert (Heql : proj_l (s ++ @TErr (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) f1) :: nil)
                      = proj_l s ++ @TErr F1 f1 :: nil).
            { rewrite proj_l_app, proj_l_err_inl_singleton. reflexivity. }
            destruct (trace_steps_single_growth_split CompLin.idImpl
                        (mkTraceConfig (proj_l s) rho1 cabs1)
                        (mkTraceConfig (proj_l (s ++ @TErr (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) f1) :: nil)) rho1_f cabs1_f)
                        (@TErr F1 f1) Htri1 Heql)
              as [Mid1 [Mid2 [Hspre [Heqm1 [Hstepvis [Heqm2 Hssuf]]]]]].
            destruct (hcomp_embed_invisible_left (mkTraceConfig (proj_l s) rho1 cabs1) Mid1 Hspre (eq_sym Heqm1)
                        s rho2_f cabs2_f cabsXR eq_refl HpR) as [cabsXL1 [HsL1 HpL1]].
            assert (Hcross1 : forall t' f', @TErr F1 f1 = TEvent (Build_ThreadEvent t' (InvEv f')) -> TMap.find t' cabs2_f = None).
            { intros t' f' Heqit. discriminate. }
            assert (Hgrow2 : tc_trace Mid2 = proj_l (s ++ @TErr (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) f1) :: nil)).
            { rewrite Heqm2. symmetry. exact Heql. }
            destruct (hcomp_embed_one_left Mid1 Mid2 (@TErr F1 f1) Hstepvis
                        (eq_trans Heqm2 (f_equal (fun x => x ++ @TErr F1 f1 :: nil) (eq_sym Heqm1)))
                        s rho2_f cabs2_f cabsXL1 (eq_sym Heqm1) HpL1 Hcross1)
              as [cabsXL2 [HsV HpV]].
            destruct (hcomp_embed_invisible_left Mid2
                        (mkTraceConfig (proj_l (s ++ @TErr (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) f1) :: nil)) rho1_f cabs1_f)
                        Hssuf (eq_trans Heqm2 (eq_sym Heql)) (s ++ @TErr (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) f1) :: nil)
                        rho2_f cabs2_f cabsXL2 (eq_sym Hgrow2) HpV) as [cabsXf [HsSuf HpSuf]].
            exists cabsXf.
            split.
            -- eapply rt_trans; [exact HsR|].
               eapply rt_trans; [exact HsL1|].
               eapply rt_trans; [exact HsV|].
               exact HsSuf.
            -- exact HpSuf.
          * (* right errors: symmetric *)
            assert (Htri1' : trace_steps CompLin.idImpl (mkTraceConfig (proj_l s) rho1 cabs1) (mkTraceConfig (proj_l s) rho1_f cabs1_f)).
            { rewrite proj_l_app, proj_l_err_inr_singleton, app_nil_r in Htri1. exact Htri1. }
            destruct (hcomp_embed_invisible_left
                        (mkTraceConfig (proj_l s) rho1 cabs1) (mkTraceConfig (proj_l s) rho1_f cabs1_f)
                        Htri1' eq_refl s rho2 cabs2 cabsX eq_refl Hcp) as [cabsXL [HsL HpL]].
            assert (Heqr : proj_r (s ++ @TErr (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) f2) :: nil)
                      = proj_r s ++ @TErr F2 f2 :: nil).
            { rewrite proj_r_app, proj_r_err_inr_singleton. reflexivity. }
            destruct (trace_steps_single_growth_split CompLin.idImpl
                        (mkTraceConfig (proj_r s) rho2 cabs2)
                        (mkTraceConfig (proj_r (s ++ @TErr (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) f2) :: nil)) rho2_f cabs2_f)
                        (@TErr F2 f2) Htri2 Heqr)
              as [Mid1 [Mid2 [Hspre [Heqm1 [Hstepvis [Heqm2 Hssuf]]]]]].
            destruct (hcomp_embed_invisible_right (mkTraceConfig (proj_r s) rho2 cabs2) Mid1 Hspre (eq_sym Heqm1)
                        s rho1_f cabs1_f cabsXL eq_refl HpL) as [cabsXR1 [HsR1 HpR1]].
            assert (Hcross1 : forall t' f', @TErr F2 f2 = TEvent (Build_ThreadEvent t' (InvEv f')) -> TMap.find t' cabs1_f = None).
            { intros t' f' Heqit. discriminate. }
            assert (Hgrow2 : tc_trace Mid2 = proj_r (s ++ @TErr (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) f2) :: nil)).
            { rewrite Heqm2. symmetry. exact Heqr. }
            destruct (hcomp_embed_one_right Mid1 Mid2 (@TErr F2 f2) Hstepvis
                        (eq_trans Heqm2 (f_equal (fun x => x ++ @TErr F2 f2 :: nil) (eq_sym Heqm1)))
                        s rho1_f cabs1_f cabsXR1 (eq_sym Heqm1) HpR1 Hcross1)
              as [cabsXR2 [HsV HpV]].
            destruct (hcomp_embed_invisible_right Mid2
                        (mkTraceConfig (proj_r (s ++ @TErr (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) f2) :: nil)) rho2_f cabs2_f)
                        Hssuf (eq_trans Heqm2 (eq_sym Heqr)) (s ++ @TErr (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) f2) :: nil)
                        rho1_f cabs1_f cabsXR2 (eq_sym Hgrow2) HpV) as [cabsXf [HsSuf HpSuf]].
            exists cabsXf.
            split.
            -- eapply rt_trans; [exact HsL|].
               eapply rt_trans; [exact HsR1|].
               eapply rt_trans; [exact HsV|].
               exact HsSuf.
            -- exact HpSuf.
      - (* rt_refl *)
        destruct (hcomp_embed_invisible_left
                    (mkTraceConfig (proj_l (tc_trace X)) rho1 cabs1)
                    (mkTraceConfig (proj_l (tc_trace X)) rho1_f cabs1_f)
                    Htri1 eq_refl (tc_trace X) rho2 cabs2 cabsX eq_refl Hcp) as [cabsX1 [Hstep1 Hp1]].
        destruct (hcomp_embed_invisible_right
                    (mkTraceConfig (proj_r (tc_trace X)) rho2 cabs2)
                    (mkTraceConfig (proj_r (tc_trace X)) rho2_f cabs2_f)
                    Htri2 eq_refl (tc_trace X) rho1_f cabs1_f cabsX1 eq_refl Hp1) as [cabsXf [Hstep2 Hp2]].
        exists cabsXf. split; [eapply rt_trans; [exact Hstep1 | exact Hstep2] | exact Hp2].
      - (* rt_trans *)
        destruct (hcomp_decompose M1 M2 X Y Htr1 sigma1 sigma2 c1 c2 HX Hp)
          as [sigma1_Y [sigma2_Y [c1_Y [c2_Y [HY [Hm1 [Hm2 Hp_Y]]]]]]].
        assert (Hd1_Y : forall th, TMap.find th c1_Y = None <-> trace_active (proj_l (tc_trace Y)) th false = false).
        { intro th. exact (pool_dom_invariant M1 (mkTraceConfig (proj_l (tc_trace X)) sigma1 c1)
                             (mkTraceConfig (proj_l (tc_trace Y)) sigma1_Y c1_Y) Hm1 th (Hd1 th)). }
        assert (Hd2_Y : forall th, TMap.find th c2_Y = None <-> trace_active (proj_r (tc_trace Y)) th false = false).
        { intro th. exact (pool_dom_invariant M2 (mkTraceConfig (proj_r (tc_trace X)) sigma2 c2)
                             (mkTraceConfig (proj_r (tc_trace Y)) sigma2_Y c2_Y) Hm2 th (Hd2 th)). }
        assert (Hlen1a : List.length (proj_l (tc_trace X)) <= List.length (proj_l (tc_trace Y))).
        { destruct (trace_steps_monotone (M1 ⊗ M2) X Y Htr1) as [tl Heqtl].
          rewrite Heqtl, proj_l_app, app_length. lia. }
        assert (Hlen1b : List.length (proj_l (tc_trace Y)) <= List.length (proj_l (tc_trace Z))).
        { destruct (trace_steps_monotone (M1 ⊗ M2) Y Z Htr2) as [tl Heqtl].
          rewrite Heqtl, proj_l_app, app_length. lia. }
        destruct (trace_steps_reach_length CompLin.idImpl _ _ Htri1 (List.length (proj_l (tc_trace Y))) Hlen1a Hlen1b)
          as [MidL [HtriL1 [HtriL2 HlenL]]].
        assert (Heqtrl : proj_l (tc_trace Y) = tc_trace MidL).
        { destruct (trace_steps_monotone CompLin.idImpl _ _ HtriL2) as [tl1 Heq1].
          destruct (trace_steps_monotone (M1 ⊗ M2) Y Z Htr2) as [tl2 Heq2].
          apply prefix_eq_of_same_length with (t1 := proj_l tl2) (t2 := tl1).
          - rewrite <- proj_l_app, <- Heq2. exact Heq1.
          - symmetry. exact HlenL. }
        destruct MidL as [trMidL rho1_Y cabs1_Y]. simpl in Heqtrl, HtriL1, HtriL2.
        assert (Hlen2a : List.length (proj_r (tc_trace X)) <= List.length (proj_r (tc_trace Y))).
        { destruct (trace_steps_monotone (M1 ⊗ M2) X Y Htr1) as [tl Heqtl].
          rewrite Heqtl, proj_r_app, app_length. lia. }
        assert (Hlen2b : List.length (proj_r (tc_trace Y)) <= List.length (proj_r (tc_trace Z))).
        { destruct (trace_steps_monotone (M1 ⊗ M2) Y Z Htr2) as [tl Heqtl].
          rewrite Heqtl, proj_r_app, app_length. lia. }
        destruct (trace_steps_reach_length CompLin.idImpl _ _ Htri2 (List.length (proj_r (tc_trace Y))) Hlen2a Hlen2b)
          as [MidR [HtriR1 [HtriR2 HlenR]]].
        assert (Heqtrr : proj_r (tc_trace Y) = tc_trace MidR).
        { destruct (trace_steps_monotone CompLin.idImpl _ _ HtriR2) as [tl1 Heq1].
          destruct (trace_steps_monotone (M1 ⊗ M2) Y Z Htr2) as [tl2 Heq2].
          apply prefix_eq_of_same_length with (t1 := proj_r tl2) (t2 := tl1).
          - rewrite <- proj_r_app, <- Heq2. exact Heq1.
          - symmetry. exact HlenR. }
        destruct MidR as [trMidR rho2_Y cabs2_Y]. simpl in Heqtrr, HtriR1, HtriR2.
        rewrite <- Heqtrl in HtriL1, HtriL2.
        rewrite <- Heqtrr in HtriR1, HtriR2.
        destruct (IH1 sigma1 sigma2 c1 c2 HX Hp Hd1 Hd2
                    rho1 cabs1 rho2 cabs2 cabsX Hcp Hdc1 Hdc2
                    rho1_Y cabs1_Y HtriL1 rho2_Y cabs2_Y HtriR1)
          as [cabsX_Y [HsXY HpXY]].
        assert (Hdc1_Y : forall th, TMap.find th cabs1_Y = None <-> trace_active (proj_l (tc_trace Y)) th false = false).
        { intro th.
          exact (pool_dom_invariant CompLin.idImpl (mkTraceConfig (proj_l (tc_trace X)) rho1 cabs1)
                   (mkTraceConfig (proj_l (tc_trace Y)) rho1_Y cabs1_Y)
                   HtriL1 th (Hdc1 th)). }
        assert (Hdc2_Y : forall th, TMap.find th cabs2_Y = None <-> trace_active (proj_r (tc_trace Y)) th false = false).
        { intro th.
          exact (pool_dom_invariant CompLin.idImpl (mkTraceConfig (proj_r (tc_trace X)) rho2 cabs2)
                   (mkTraceConfig (proj_r (tc_trace Y)) rho2_Y cabs2_Y)
                   HtriR1 th (Hdc2 th)). }
        destruct (IH2 sigma1_Y sigma2_Y c1_Y c2_Y HY Hp_Y Hd1_Y Hd2_Y
                    rho1_Y cabs1_Y rho2_Y cabs2_Y cabsX_Y HpXY Hdc1_Y Hdc2_Y
                    rho1_f cabs1_f HtriL2 rho2_f cabs2_f HtriR2)
          as [cabsX_f [HsYZ HpYZ]].
        exists cabsX_f.
        split; [eapply rt_trans; [exact HsXY | exact HsYZ] | exact HpYZ].
    Qed.
  End HCompRecombine.

  (** * [implHComp CompLin.idImpl CompLin.idImpl] and the combined
      signature's own [CompLin.idImpl] are the very same [ModuleImpl]:
      spawning an [inl f1]/[inr f2] thread produces, on both sides,
      [Vis (inl f1) (fun v => Ret v)] / [Vis (inr f2) (fun v => Ret v)]
      (the only place a [ModuleImpl] is consulted is [invstep], to build the
      freshly spawned thread's program). This lets [hcomp_recombine]'s
      conclusion (stated in terms of [implHComp idImpl idImpl]) be
      transported to a statement about the combined signature's native
      [idImpl], which is what [CompLin] itself is stated against. *)
  Section HCompIdEta.
    Context {F1 F2 : Op.t}.
    Context {VE VF : @LTS (Sig.Plus.omap F1 F2)}.

    Lemma implHComp_idImpl_eq :
      forall (f : Sig.op (Sig.Plus.omap F1 F2)) t,
        @implHComp F1 F1 F2 F2 CompLin.idImpl CompLin.idImpl f t = CompLin.idImpl f t.
    Proof.
      intros [f1 | f2] t; simpl; unfold CompLin.idImpl.
      - rewrite liftLeftProgVis. f_equal.
        apply functional_extensionality. intro a. apply liftLeftProgRet.
      - rewrite liftRightProgVis. f_equal.
        apply functional_extensionality. intro a. apply liftRightProgRet.
    Qed.

    Lemma invstep_idImpl_eq :
      forall t f c1 c2,
        invstep (@implHComp F1 F1 F2 F2 CompLin.idImpl CompLin.idImpl) t f c1 c2 ->
        invstep CompLin.idImpl t f c1 c2.
    Proof.
      intros t f c1 c2 Hstep. destruct Hstep as [Hfind Hupd].
      rewrite (implHComp_idImpl_eq f t) in Hupd.
      exact (InvStep _ t f c1 c2 Hfind Hupd).
    Qed.

    Lemma trace_step_idImpl_eq :
      forall A B,
        @trace_step (Sig.Plus.omap F1 F2) (Sig.Plus.omap F1 F2) VE
          (@implHComp F1 F1 F2 F2 CompLin.idImpl CompLin.idImpl) A B ->
        @trace_step (Sig.Plus.omap F1 F2) (Sig.Plus.omap F1 F2) VE CompLin.idImpl A B.
    Proof.
      intros A B Hstep. destruct Hstep.
      - eapply TraceStepInv, invstep_idImpl_eq, Hstep.
      - eapply TraceStepRet, Hstep.
      - eapply TraceStepU, Hstep.
      - eapply TraceStepTau, Hstep.
      - eapply TraceStepError; eauto.
    Qed.

    Lemma trace_steps_idImpl_eq :
      forall A B,
        @trace_steps (Sig.Plus.omap F1 F2) (Sig.Plus.omap F1 F2) VE
          (@implHComp F1 F1 F2 F2 CompLin.idImpl CompLin.idImpl) A B ->
        @trace_steps (Sig.Plus.omap F1 F2) (Sig.Plus.omap F1 F2) VE CompLin.idImpl A B.
    Proof.
      intros A B H. induction H.
      - apply rt_step, trace_step_idImpl_eq, H.
      - apply rt_refl.
      - eapply rt_trans; eauto.
    Qed.
  End HCompIdEta.

  (** Lemma 4.2 (Horizontal Compositionality of Compositional
      Linearizability): if [M1 : VE1 { VF1] and [M2 : VE2 { VF2], then their
      horizontal composition [M1 ⊗ M2 : VE1 ⊗ VE2 { VF1 ⊗ VF2], where the
      underlay and overlay libraries themselves are combined with
      [tens_lts] and the initial states are paired up. *)
  Module HComp.
    Lemma CompLin_hcomp
        {E1 F1 E2 F2 : Op.t}
        {VE1 : @LTS E1} {VF1 : @LTS F1}
        {VE2 : @LTS E2} {VF2 : @LTS F2}
        (M1 : ModuleImpl E1 F1) (M2 : ModuleImpl E2 F2)
        (sigma01 : State VE1) (rho01 : State VF1)
        (sigma02 : State VE2) (rho02 : State VF2) :
      CompLin M1 sigma01 rho01 ->
      CompLin M2 sigma02 rho02 ->
      @CompLin _ _ (tens_lts VE1 VE2) (tens_lts VF1 VF2)
        (M1 ⊗ M2) (pair sigma01 sigma02) (pair rho01 rho02).
    Proof.
      intros HCL1 HCL2 s [sigmaX [cX Htr]].
      destruct (hcomp_decompose M1 M2
                  (mkTraceConfig nil (pair sigma01 sigma02 : State (tens_lts VE1 VE2)) (TMap.empty _))
                  (mkTraceConfig s sigmaX cX) Htr sigma01 sigma02 (TMap.empty _) (TMap.empty _)
                  eq_refl hpools_empty)
        as [sigma1' [sigma2' [c1' [c2' [HeqX' [Htr1 [Htr2 Hp']]]]]]].
      simpl in Htr1, Htr2.
      pose proof (HCL1 (proj_l s) (ex_intro _ sigma1' (ex_intro _ c1' Htr1))) as HC1.
      pose proof (HCL2 (proj_r s) (ex_intro _ sigma2' (ex_intro _ c2' Htr2))) as HC2.
      unfold ImplTracesClosed in HC1, HC2.
      unfold ImplTraces in HC1, HC2.
      (* Given ANY actual prefix [p] of [s] (with [proj_l p]/[proj_r p]
         reached by [M1]'s/[M2]'s replays), recombine the two replays over
         [p] into a single combined [idImpl] run over [p]. This single
         helper covers all four clean/error combinations: apply it to [p :=
         s] when both sides are clean, or to the actual prefix
         corresponding to whichever side errors first. *)
      assert (Hgo :
        forall (p tl : Trace (Sig.Plus.omap F1 F2)), s = p ++ tl ->
        forall (rho1_f : State VF1) (cabs1_f : @ThreadPoolState F1 F1),
          trace_steps CompLin.idImpl (mkTraceConfig nil rho01 (TMap.empty _))
            (mkTraceConfig (proj_l p) rho1_f cabs1_f) ->
        forall (rho2_f : State VF2) (cabs2_f : @ThreadPoolState F2 F2),
          trace_steps CompLin.idImpl (mkTraceConfig nil rho02 (TMap.empty _))
            (mkTraceConfig (proj_r p) rho2_f cabs2_f) ->
          exists cabsX_f,
            trace_steps CompLin.idImpl
              (mkTraceConfig nil (pair rho01 rho02 : State (tens_lts VF1 VF2)) (TMap.empty _))
              (mkTraceConfig p (pair rho1_f rho2_f : State (tens_lts VF1 VF2)) cabsX_f) /\
            hpools cabsX_f cabs1_f cabs2_f).
      { intros p tl Heqs rho1_f cabs1_f Htri1 rho2_f cabs2_f Htri2.
        destruct (trace_steps_reach_length (M1 ⊗ M2)
                    (mkTraceConfig nil (pair sigma01 sigma02 : State (tens_lts VE1 VE2)) (TMap.empty _))
                    (mkTraceConfig s sigmaX cX) Htr (List.length p))
          as [MidP [HtrP1 [HtrP2 HlenP]]].
        - simpl. lia.
        - simpl. rewrite Heqs, app_length. lia.
        - assert (Heqtrp : p = tc_trace MidP).
          { destruct (trace_steps_monotone (M1 ⊗ M2) _ _ HtrP2) as [tlp Heq1].
            apply prefix_eq_of_same_length with (t1 := tl) (t2 := tlp).
            - simpl in Heq1. rewrite <- Heqs. exact Heq1.
            - symmetry. exact HlenP. }
          destruct MidP as [trMidP sigmaMidP cMidP]. simpl in Heqtrp, HtrP1, HtrP2.
          subst trMidP.
          assert (Hd1P : forall th, TMap.find th (TMap.empty (@ThreadState E1 F1)) = None <-> trace_active (@nil (TraceItem F1)) th false = false).
          { intro th. rewrite TMap.gempty. split; reflexivity. }
          assert (Hd2P : forall th, TMap.find th (TMap.empty (@ThreadState E2 F2)) = None <-> trace_active (@nil (TraceItem F2)) th false = false).
          { intro th. rewrite TMap.gempty. split; reflexivity. }
          assert (Hdc1P : forall th, TMap.find th (TMap.empty (@ThreadState F1 F1)) = None <-> trace_active (@nil (TraceItem F1)) th false = false).
          { intro th. rewrite TMap.gempty. split; reflexivity. }
          assert (Hdc2P : forall th, TMap.find th (TMap.empty (@ThreadState F2 F2)) = None <-> trace_active (@nil (TraceItem F2)) th false = false).
          { intro th. rewrite TMap.gempty. split; reflexivity. }
          destruct (hcomp_recombine M1 M2
                      (mkTraceConfig nil (pair sigma01 sigma02 : State (tens_lts VE1 VE2)) (TMap.empty _))
                      (mkTraceConfig p sigmaMidP cMidP) HtrP1
                      sigma01 sigma02 (TMap.empty _) (TMap.empty _) eq_refl hpools_empty
                      Hd1P Hd2P
                      rho01 (TMap.empty _) rho02 (TMap.empty _) (TMap.empty _)
                      hpools_empty Hdc1P Hdc2P
                      rho1_f cabs1_f Htri1 rho2_f cabs2_f Htri2)
            as [cabsX_f [Hsteps Hpf]].
          exists cabsX_f. split; [| exact Hpf].
          apply trace_steps_idImpl_eq. exact Hsteps. }
      destruct HC1 as [[rho1_f [cabs1_f Htri1]] | [p1 [f1 [tl1 [[rho1_f [cabs1_f Htri1]] Heqs1]]]]];
        destruct HC2 as [[rho2_f [cabs2_f Htri2]] | [p2 [f2 [tl2 [[rho2_f [cabs2_f Htri2]] Heqs2]]]]].
      - (* clean / clean: recombine over the whole trace [s] *)
        left.
        destruct (Hgo s nil (eq_sym (app_nil_r s)) rho1_f cabs1_f Htri1 rho2_f cabs2_f Htri2)
          as [cabsX_f [Hsteps _]].
        exists (pair rho1_f rho2_f : State (tens_lts VF1 VF2)), cabsX_f. exact Hsteps.
      - (* clean / error: [M2] errors at [p2]; find an actual prefix [p] of
           [s] whose [proj_r] is [p2], recombine the two sides up to [p],
           then embed [M2]'s one remaining (error) step via
           [hcomp_embed_one_right]. *)
        destruct (proj_r_prefix_exists s p2 (ex_intro _ tl2 Heqs2))
          as [p [tl [Heqsplit Heqprojr]]].
        assert (Hlex1 : List.length (proj_l p) <= List.length (proj_l s)).
        { destruct (trace_steps_monotone (M1 ⊗ M2)
                      (mkTraceConfig nil (pair sigma01 sigma02 : State (tens_lts VE1 VE2)) (TMap.empty _))
                      (mkTraceConfig s sigmaX cX) Htr) as [tlm Heqm].
          simpl in Heqm. rewrite Heqsplit, proj_l_app, app_length. lia. }
        destruct (trace_steps_reach_length CompLin.idImpl
                    (mkTraceConfig nil rho01 (TMap.empty _))
                    (mkTraceConfig (proj_l s) rho1_f cabs1_f) Htri1
                    (List.length (proj_l p)))
          as [MidL [HtriL1 [HtriL2 HlenL]]].
        + simpl. lia.
        + simpl. exact Hlex1.
        + assert (Heqtrl : proj_l p = tc_trace MidL).
          { destruct (trace_steps_monotone CompLin.idImpl _ _ HtriL2) as [tll Heq1].
            apply prefix_eq_of_same_length with (t1 := proj_l tl) (t2 := tll).
            - simpl in Heq1. rewrite <- proj_l_app, <- Heqsplit. exact Heq1.
            - symmetry. exact HlenL. }
          destruct MidL as [trMidL rho1_p cabs1_p]. simpl in Heqtrl, HtriL1, HtriL2.
          subst trMidL.
          destruct (trace_steps_reach_length CompLin.idImpl
                      (mkTraceConfig nil rho02 (TMap.empty _))
                      (mkTraceConfig (p2 ++ TErr f2 :: nil) rho2_f cabs2_f) Htri2
                      (List.length p2))
            as [MidE0 [HtriE0 [HtriE0' HlenE0]]].
          { simpl. lia. }
          { simpl. rewrite app_length. simpl. lia. }
          assert (HeqtrE0 : tc_trace MidE0 = p2).
          { destruct (trace_steps_monotone CompLin.idImpl _ _ HtriE0') as [tlE Heq1].
            simpl in Heq1. symmetry.
            apply prefix_eq_of_same_length with (t1 := (TErr f2 :: nil : Trace F2)) (t2 := tlE).
            - exact Heq1.
            - symmetry. exact HlenE0. }
          destruct (trace_steps_single_growth_split CompLin.idImpl MidE0
                      (mkTraceConfig (p2 ++ TErr f2 :: nil) rho2_f cabs2_f)
                      (TErr f2) HtriE0' (eq_trans (eq_refl _) (f_equal (fun t => t ++ TErr f2 :: nil) (eq_sym HeqtrE0))))
            as [MidE1 [MidE2 [HtriE1 [HeqE1 [HstepE [HeqE2 HtriE2]]]]]].
          destruct MidE1 as [trE1 rho2_p cabs2_p]. simpl in HeqE1, HtriE1, HstepE.
          rewrite HeqtrE0 in HeqE1. subst trE1.
          destruct MidE2 as [trE2 rho2_q cabs2_q]. simpl in HeqE2, HstepE, HtriE2.
          rewrite HeqtrE0 in HeqE2.
          assert (HtriR : trace_steps CompLin.idImpl (mkTraceConfig nil rho02 (TMap.empty _))
                            (mkTraceConfig (proj_r p) rho2_p cabs2_p)).
          { rewrite Heqprojr.
            eapply rt_trans; [exact HtriE0 | exact HtriE1]. }
          destruct (Hgo p tl Heqsplit rho1_p cabs1_p HtriL1 rho2_p cabs2_p HtriR)
            as [cabsX_p [HstepsP HpP]].
          assert (HstepE' : trace_step CompLin.idImpl (mkTraceConfig (proj_r p) rho2_p cabs2_p)
                              (mkTraceConfig (proj_r p ++ TErr f2 :: nil) rho2_q cabs2_q)).
          { rewrite Heqprojr, <- HeqE2. exact HstepE. }
          destruct (hcomp_embed_one_right (mkTraceConfig (proj_r p) rho2_p cabs2_p)
                      (mkTraceConfig (proj_r p ++ TErr f2 :: nil) rho2_q cabs2_q)
                      (TErr f2) HstepE' eq_refl
                      p rho1_p cabs1_p cabsX_p eq_refl HpP
                      (fun t f Hcontra => match Hcontra with end))
            as [cabsX_q [HstepF HpF]].
          assert (HtriE2' : trace_steps CompLin.idImpl
                              (mkTraceConfig (proj_r p ++ TErr f2 :: nil) rho2_q cabs2_q)
                              (mkTraceConfig (proj_r p ++ TErr f2 :: nil) rho2_f cabs2_f)).
          { rewrite HeqE2 in HtriE2. rewrite Heqprojr. exact HtriE2. }
          assert (Hprs0 : proj_r (p ++ @TErr (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) f2) :: nil)
                            = proj_r p ++ TErr f2 :: nil).
          { rewrite proj_r_app, proj_r_err_inr_singleton. reflexivity. }
          destruct (hcomp_embed_invisible_right
                      (mkTraceConfig (proj_r p ++ TErr f2 :: nil) rho2_q cabs2_q)
                      (mkTraceConfig (proj_r p ++ TErr f2 :: nil) rho2_f cabs2_f)
                      HtriE2' eq_refl
                      (p ++ @TErr (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) f2) :: nil)
                      rho1_p cabs1_p cabsX_q Hprs0 HpF)
            as [cabsX_f [HstepG HpG]].
          right. exists p, (@inr (Sig.op F1) (Sig.op F2) f2), tl. split; [| exact Heqsplit].
          exists (pair rho1_p rho2_f : State (tens_lts VF1 VF2)), cabsX_f.
          eapply rt_trans; [exact HstepsP |].
          eapply rt_trans; [apply trace_steps_idImpl_eq; exact HstepF
                            | apply trace_steps_idImpl_eq; exact HstepG].
      - (* error / clean: [M1] errors at [p1]; symmetric to the previous
           case, using [hcomp_embed_one_left]/[hcomp_embed_invisible_left]. *)
        destruct (proj_l_prefix_exists s p1 (ex_intro _ tl1 Heqs1))
          as [p [tl [Heqsplit Heqprojl]]].
        assert (Hlex2 : List.length (proj_r p) <= List.length (proj_r s)).
        { destruct (trace_steps_monotone (M1 ⊗ M2)
                      (mkTraceConfig nil (pair sigma01 sigma02 : State (tens_lts VE1 VE2)) (TMap.empty _))
                      (mkTraceConfig s sigmaX cX) Htr) as [tlm Heqm].
          simpl in Heqm. rewrite Heqsplit, proj_r_app, app_length. lia. }
        destruct (trace_steps_reach_length CompLin.idImpl
                    (mkTraceConfig nil rho02 (TMap.empty _))
                    (mkTraceConfig (proj_r s) rho2_f cabs2_f) Htri2
                    (List.length (proj_r p)))
          as [MidR [HtriR1 [HtriR2 HlenR]]].
        + simpl. lia.
        + simpl. exact Hlex2.
        + assert (Heqtrr : proj_r p = tc_trace MidR).
          { destruct (trace_steps_monotone CompLin.idImpl _ _ HtriR2) as [tlr Heq1].
            apply prefix_eq_of_same_length with (t1 := proj_r tl) (t2 := tlr).
            - simpl in Heq1. rewrite <- proj_r_app, <- Heqsplit. exact Heq1.
            - symmetry. exact HlenR. }
          destruct MidR as [trMidR rho2_p cabs2_p]. simpl in Heqtrr, HtriR1, HtriR2.
          subst trMidR.
          destruct (trace_steps_reach_length CompLin.idImpl
                      (mkTraceConfig nil rho01 (TMap.empty _))
                      (mkTraceConfig (p1 ++ TErr f1 :: nil) rho1_f cabs1_f) Htri1
                      (List.length p1))
            as [MidE0 [HtriE0 [HtriE0' HlenE0]]].
          { simpl. lia. }
          { simpl. rewrite app_length. simpl. lia. }
          assert (HeqtrE0 : tc_trace MidE0 = p1).
          { destruct (trace_steps_monotone CompLin.idImpl _ _ HtriE0') as [tlE Heq1].
            simpl in Heq1. symmetry.
            apply prefix_eq_of_same_length with (t1 := (TErr f1 :: nil : Trace F1)) (t2 := tlE).
            - exact Heq1.
            - symmetry. exact HlenE0. }
          destruct (trace_steps_single_growth_split CompLin.idImpl MidE0
                      (mkTraceConfig (p1 ++ TErr f1 :: nil) rho1_f cabs1_f)
                      (TErr f1) HtriE0' (eq_trans (eq_refl _) (f_equal (fun t => t ++ TErr f1 :: nil) (eq_sym HeqtrE0))))
            as [MidE1 [MidE2 [HtriE1 [HeqE1 [HstepE [HeqE2 HtriE2]]]]]].
          destruct MidE1 as [trE1 rho1_p cabs1_p]. simpl in HeqE1, HtriE1, HstepE.
          rewrite HeqtrE0 in HeqE1. subst trE1.
          destruct MidE2 as [trE2 rho1_q cabs1_q]. simpl in HeqE2, HstepE, HtriE2.
          rewrite HeqtrE0 in HeqE2.
          assert (HtriL : trace_steps CompLin.idImpl (mkTraceConfig nil rho01 (TMap.empty _))
                            (mkTraceConfig (proj_l p) rho1_p cabs1_p)).
          { rewrite Heqprojl.
            eapply rt_trans; [exact HtriE0 | exact HtriE1]. }
          destruct (Hgo p tl Heqsplit rho1_p cabs1_p HtriL rho2_p cabs2_p HtriR1)
            as [cabsX_p [HstepsP HpP]].
          assert (HstepE' : trace_step CompLin.idImpl (mkTraceConfig (proj_l p) rho1_p cabs1_p)
                              (mkTraceConfig (proj_l p ++ TErr f1 :: nil) rho1_q cabs1_q)).
          { rewrite Heqprojl, <- HeqE2. exact HstepE. }
          destruct (hcomp_embed_one_left (mkTraceConfig (proj_l p) rho1_p cabs1_p)
                      (mkTraceConfig (proj_l p ++ TErr f1 :: nil) rho1_q cabs1_q)
                      (TErr f1) HstepE' eq_refl
                      p rho2_p cabs2_p cabsX_p eq_refl HpP
                      (fun t f Hcontra => match Hcontra with end))
            as [cabsX_q [HstepF HpF]].
          assert (HtriE2' : trace_steps CompLin.idImpl
                              (mkTraceConfig (proj_l p ++ TErr f1 :: nil) rho1_q cabs1_q)
                              (mkTraceConfig (proj_l p ++ TErr f1 :: nil) rho1_f cabs1_f)).
          { rewrite HeqE2 in HtriE2. rewrite Heqprojl. exact HtriE2. }
          assert (Hpls0 : proj_l (p ++ @TErr (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) f1) :: nil)
                            = proj_l p ++ TErr f1 :: nil).
          { rewrite proj_l_app, proj_l_err_inl_singleton. reflexivity. }
          destruct (hcomp_embed_invisible_left
                      (mkTraceConfig (proj_l p ++ TErr f1 :: nil) rho1_q cabs1_q)
                      (mkTraceConfig (proj_l p ++ TErr f1 :: nil) rho1_f cabs1_f)
                      HtriE2' eq_refl
                      (p ++ @TErr (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) f1) :: nil)
                      rho2_p cabs2_p cabsX_q Hpls0 HpF)
            as [cabsX_f [HstepG HpG]].
          right. exists p, (@inl (Sig.op F1) (Sig.op F2) f1), tl. split; [| exact Heqsplit].
          exists (pair rho1_f rho2_p : State (tens_lts VF1 VF2)), cabsX_f.
          eapply rt_trans; [exact HstepsP |].
          eapply rt_trans; [apply trace_steps_idImpl_eq; exact HstepF
                            | apply trace_steps_idImpl_eq; exact HstepG].
      - (* error / error: both [M1] (at [p1]) and [M2] (at [p2]) error;
           locate the actual prefixes of [s] realizing each, and report
           whichever is shorter (occurs no later in [s]) — the other side's
           clean replay is only ever needed up to that point, which is
           always available since both [pL]/[pR] are prefixes of [s], one
           of the other. *)
        destruct (proj_l_prefix_exists s p1 (ex_intro _ tl1 Heqs1))
          as [pL [tlL [HeqsplitL HeqprojlL]]].
        destruct (proj_r_prefix_exists s p2 (ex_intro _ tl2 Heqs2))
          as [pR [tlR [HeqsplitR HeqprojrR]]].
        destruct (Compare_dec.le_ge_dec (List.length pL) (List.length pR)) as [HleLR | HgeLR].
        + (* [pL] does not exceed [pR]: report [M1]'s error, truncating
             [M2]'s clean replay to [proj_r pL] (which is no longer than
             [p2], since [pL] is a prefix of [pR] and [proj_r pR = p2]). *)
          destruct (prefix_le_extends pL pR tlL tlR
                      (eq_trans (eq_sym HeqsplitL) HeqsplitR) HleLR) as [m Heqm].
          assert (Heqprm : p2 = proj_r pL ++ proj_r m).
          { rewrite <- HeqprojrR, Heqm, proj_r_app. reflexivity. }
          assert (Hlex2 : List.length (proj_r pL) <= List.length (p2 ++ TErr f2 :: nil)).
          { rewrite Heqprm, app_length, app_length. lia. }
          destruct (trace_steps_reach_length CompLin.idImpl
                      (mkTraceConfig nil rho02 (TMap.empty _))
                      (mkTraceConfig (p2 ++ TErr f2 :: nil) rho2_f cabs2_f) Htri2
                      (List.length (proj_r pL)))
            as [MidR [HtriR1 [HtriR2 HlenR]]].
          * simpl. lia.
          * simpl. exact Hlex2.
          * assert (Heqtrr : proj_r pL = tc_trace MidR).
            { destruct (trace_steps_monotone CompLin.idImpl _ _ HtriR2) as [tlr Heq1].
              simpl in Heq1.
              apply prefix_eq_of_same_length with (t1 := proj_r m ++ TErr f2 :: nil) (t2 := tlr).
              - rewrite app_assoc, <- Heqprm. exact Heq1.
              - symmetry. exact HlenR. }
            destruct MidR as [trMidR rho2_p cabs2_p]. simpl in Heqtrr, HtriR1, HtriR2.
            subst trMidR.
            destruct (trace_steps_reach_length CompLin.idImpl
                        (mkTraceConfig nil rho01 (TMap.empty _))
                        (mkTraceConfig (p1 ++ TErr f1 :: nil) rho1_f cabs1_f) Htri1
                        (List.length p1))
              as [MidE0 [HtriE0 [HtriE0' HlenE0]]].
            { simpl. lia. }
            { simpl. rewrite app_length. simpl. lia. }
            assert (HeqtrE0 : tc_trace MidE0 = p1).
            { destruct (trace_steps_monotone CompLin.idImpl _ _ HtriE0') as [tlE Heq1].
              simpl in Heq1. symmetry.
              apply prefix_eq_of_same_length with (t1 := (TErr f1 :: nil : Trace F1)) (t2 := tlE).
              - exact Heq1.
              - symmetry. exact HlenE0. }
            destruct (trace_steps_single_growth_split CompLin.idImpl MidE0
                        (mkTraceConfig (p1 ++ TErr f1 :: nil) rho1_f cabs1_f)
                        (TErr f1) HtriE0' (eq_trans (eq_refl _) (f_equal (fun t => t ++ TErr f1 :: nil) (eq_sym HeqtrE0))))
              as [MidE1 [MidE2 [HtriE1 [HeqE1 [HstepE [HeqE2 HtriE2]]]]]].
            destruct MidE1 as [trE1 rho1_p cabs1_p]. simpl in HeqE1, HtriE1, HstepE.
            rewrite HeqtrE0 in HeqE1. subst trE1.
            destruct MidE2 as [trE2 rho1_q cabs1_q]. simpl in HeqE2, HstepE, HtriE2.
            rewrite HeqtrE0 in HeqE2.
            assert (HtriL : trace_steps CompLin.idImpl (mkTraceConfig nil rho01 (TMap.empty _))
                              (mkTraceConfig (proj_l pL) rho1_p cabs1_p)).
            { rewrite HeqprojlL.
              eapply rt_trans; [exact HtriE0 | exact HtriE1]. }
            destruct (Hgo pL tlL HeqsplitL rho1_p cabs1_p HtriL rho2_p cabs2_p HtriR1)
              as [cabsX_p [HstepsP HpP]].
            assert (HstepE' : trace_step CompLin.idImpl (mkTraceConfig (proj_l pL) rho1_p cabs1_p)
                                (mkTraceConfig (proj_l pL ++ TErr f1 :: nil) rho1_q cabs1_q)).
            { rewrite HeqprojlL, <- HeqE2. exact HstepE. }
            destruct (hcomp_embed_one_left (mkTraceConfig (proj_l pL) rho1_p cabs1_p)
                        (mkTraceConfig (proj_l pL ++ TErr f1 :: nil) rho1_q cabs1_q)
                        (TErr f1) HstepE' eq_refl
                        pL rho2_p cabs2_p cabsX_p eq_refl HpP
                        (fun t f Hcontra => match Hcontra with end))
              as [cabsX_q [HstepF HpF]].
            assert (HtriE2' : trace_steps CompLin.idImpl
                                (mkTraceConfig (proj_l pL ++ TErr f1 :: nil) rho1_q cabs1_q)
                                (mkTraceConfig (proj_l pL ++ TErr f1 :: nil) rho1_f cabs1_f)).
            { rewrite HeqE2 in HtriE2. rewrite HeqprojlL. exact HtriE2. }
            assert (Hpls0 : proj_l (pL ++ @TErr (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) f1) :: nil)
                              = proj_l pL ++ TErr f1 :: nil).
            { rewrite proj_l_app, proj_l_err_inl_singleton. reflexivity. }
            destruct (hcomp_embed_invisible_left
                        (mkTraceConfig (proj_l pL ++ TErr f1 :: nil) rho1_q cabs1_q)
                        (mkTraceConfig (proj_l pL ++ TErr f1 :: nil) rho1_f cabs1_f)
                        HtriE2' eq_refl
                        (pL ++ @TErr (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) f1) :: nil)
                        rho2_p cabs2_p cabsX_q Hpls0 HpF)
              as [cabsX_f [HstepG HpG]].
            right. exists pL, (@inl (Sig.op F1) (Sig.op F2) f1), tlL. split; [| exact HeqsplitL].
            exists (pair rho1_f rho2_p : State (tens_lts VF1 VF2)), cabsX_f.
            eapply rt_trans; [exact HstepsP |].
            eapply rt_trans; [apply trace_steps_idImpl_eq; exact HstepF
                              | apply trace_steps_idImpl_eq; exact HstepG].
        + (* [pR] does not exceed [pL]: report [M2]'s error, truncating
             [M1]'s clean replay to [proj_l pR] (which is no longer than
             [p1], since [pR] is a prefix of [pL] and [proj_l pL = p1]). *)
          destruct (prefix_le_extends pR pL tlR tlL
                      (eq_trans (eq_sym HeqsplitR) HeqsplitL) HgeLR) as [m Heqm].
          assert (Heqplm : p1 = proj_l pR ++ proj_l m).
          { rewrite <- HeqprojlL, Heqm, proj_l_app. reflexivity. }
          assert (Hlex1 : List.length (proj_l pR) <= List.length (p1 ++ TErr f1 :: nil)).
          { rewrite Heqplm, app_length, app_length. lia. }
          destruct (trace_steps_reach_length CompLin.idImpl
                      (mkTraceConfig nil rho01 (TMap.empty _))
                      (mkTraceConfig (p1 ++ TErr f1 :: nil) rho1_f cabs1_f) Htri1
                      (List.length (proj_l pR)))
            as [MidL [HtriL1 [HtriL2 HlenL]]].
          * simpl. lia.
          * simpl. exact Hlex1.
          * assert (Heqtrl : proj_l pR = tc_trace MidL).
            { destruct (trace_steps_monotone CompLin.idImpl _ _ HtriL2) as [tll Heq1].
              simpl in Heq1.
              apply prefix_eq_of_same_length with (t1 := proj_l m ++ TErr f1 :: nil) (t2 := tll).
              - rewrite app_assoc, <- Heqplm. exact Heq1.
              - symmetry. exact HlenL. }
            destruct MidL as [trMidL rho1_p cabs1_p]. simpl in Heqtrl, HtriL1, HtriL2.
            subst trMidL.
            destruct (trace_steps_reach_length CompLin.idImpl
                        (mkTraceConfig nil rho02 (TMap.empty _))
                        (mkTraceConfig (p2 ++ TErr f2 :: nil) rho2_f cabs2_f) Htri2
                        (List.length p2))
              as [MidE0 [HtriE0 [HtriE0' HlenE0]]].
            { simpl. lia. }
            { simpl. rewrite app_length. simpl. lia. }
            assert (HeqtrE0 : tc_trace MidE0 = p2).
            { destruct (trace_steps_monotone CompLin.idImpl _ _ HtriE0') as [tlE Heq1].
              simpl in Heq1. symmetry.
              apply prefix_eq_of_same_length with (t1 := (TErr f2 :: nil : Trace F2)) (t2 := tlE).
              - exact Heq1.
              - symmetry. exact HlenE0. }
            destruct (trace_steps_single_growth_split CompLin.idImpl MidE0
                        (mkTraceConfig (p2 ++ TErr f2 :: nil) rho2_f cabs2_f)
                        (TErr f2) HtriE0' (eq_trans (eq_refl _) (f_equal (fun t => t ++ TErr f2 :: nil) (eq_sym HeqtrE0))))
              as [MidE1 [MidE2 [HtriE1 [HeqE1 [HstepE [HeqE2 HtriE2]]]]]].
            destruct MidE1 as [trE1 rho2_p cabs2_p]. simpl in HeqE1, HtriE1, HstepE.
            rewrite HeqtrE0 in HeqE1. subst trE1.
            destruct MidE2 as [trE2 rho2_q cabs2_q]. simpl in HeqE2, HstepE, HtriE2.
            rewrite HeqtrE0 in HeqE2.
            assert (HtriR : trace_steps CompLin.idImpl (mkTraceConfig nil rho02 (TMap.empty _))
                              (mkTraceConfig (proj_r pR) rho2_p cabs2_p)).
            { rewrite HeqprojrR.
              eapply rt_trans; [exact HtriE0 | exact HtriE1]. }
            destruct (Hgo pR tlR HeqsplitR rho1_p cabs1_p HtriL1 rho2_p cabs2_p HtriR)
              as [cabsX_p [HstepsP HpP]].
            assert (HstepE' : trace_step CompLin.idImpl (mkTraceConfig (proj_r pR) rho2_p cabs2_p)
                                (mkTraceConfig (proj_r pR ++ TErr f2 :: nil) rho2_q cabs2_q)).
            { rewrite HeqprojrR, <- HeqE2. exact HstepE. }
            destruct (hcomp_embed_one_right (mkTraceConfig (proj_r pR) rho2_p cabs2_p)
                        (mkTraceConfig (proj_r pR ++ TErr f2 :: nil) rho2_q cabs2_q)
                        (TErr f2) HstepE' eq_refl
                        pR rho1_p cabs1_p cabsX_p eq_refl HpP
                        (fun t f Hcontra => match Hcontra with end))
              as [cabsX_q [HstepF HpF]].
            assert (HtriE2' : trace_steps CompLin.idImpl
                                (mkTraceConfig (proj_r pR ++ TErr f2 :: nil) rho2_q cabs2_q)
                                (mkTraceConfig (proj_r pR ++ TErr f2 :: nil) rho2_f cabs2_f)).
            { rewrite HeqE2 in HtriE2. rewrite HeqprojrR. exact HtriE2. }
            assert (Hprs0 : proj_r (pR ++ @TErr (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) f2) :: nil)
                              = proj_r pR ++ TErr f2 :: nil).
            { rewrite proj_r_app, proj_r_err_inr_singleton. reflexivity. }
            destruct (hcomp_embed_invisible_right
                        (mkTraceConfig (proj_r pR ++ TErr f2 :: nil) rho2_q cabs2_q)
                        (mkTraceConfig (proj_r pR ++ TErr f2 :: nil) rho2_f cabs2_f)
                        HtriE2' eq_refl
                        (pR ++ @TErr (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) f2) :: nil)
                        rho1_p cabs1_p cabsX_q Hprs0 HpF)
              as [cabsX_f [HstepG HpG]].
            right. exists pR, (@inr (Sig.op F1) (Sig.op F2) f2), tlR. split; [| exact HeqsplitR].
            exists (pair rho1_p rho2_f : State (tens_lts VF1 VF2)), cabsX_f.
            eapply rt_trans; [exact HstepsP |].
            eapply rt_trans; [apply trace_steps_idImpl_eq; exact HstepF
                              | apply trace_steps_idImpl_eq; exact HstepG].
    Qed.
  End HComp.

End CompLinHComp.
