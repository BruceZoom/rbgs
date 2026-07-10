Require Import Coq.Lists.List.
Require Import Coq.PArith.PArith.
Require Import Lia.
Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.Program.Equality.

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

  (* Unfolding equations for the [substProg]/[bindSubstProg] CoFixpoints,
     standard boilerplate via [PPid]/[PP] (see [Lang.v]). Needed throughout
     the vertical-compositionality proof to recognize exactly when a
     composite thread's step crosses an F-level invocation/return
     boundary. *)
  Lemma substProgVis {E F R} t (impl : ModuleImpl E F) m (k : Sig.ar m -> Prog F R) :
    substProg t impl (Vis m k) = Tau (bindSubstProg t impl (impl m t) k).
  Proof. rewrite (PPid (substProg t impl (Vis m k))) at 1. unfold PP, substProg at 1. reflexivity. Qed.

  Lemma substProgRet {E F R} t (impl : ModuleImpl E F) (r : R) :
    substProg t impl (Ret r) = Ret r.
  Proof. rewrite (PPid (substProg t impl (Ret r))) at 1. unfold PP, substProg at 1. reflexivity. Qed.

  Lemma substProgTau {E F R} t (impl : ModuleImpl E F) (p : Prog F R) :
    substProg t impl (Tau p) = Tau (substProg t impl p).
  Proof. rewrite (PPid (substProg t impl (Tau p))) at 1. unfold PP, substProg at 1. reflexivity. Qed.

  Lemma bindSubstProgVis {E F R R'} t (impl : ModuleImpl E F) m
      (k' : Sig.ar m -> Prog E R) (k : R -> Prog F R') :
    bindSubstProg t impl (Vis m k') k = Vis m (fun r => bindSubstProg t impl (k' r) k).
  Proof. rewrite (PPid (bindSubstProg t impl (Vis m k') k)) at 1. unfold PP, bindSubstProg at 1. reflexivity. Qed.

  Lemma bindSubstProgRet {E F R R'} t (impl : ModuleImpl E F) (r : R) (k : R -> Prog F R') :
    bindSubstProg t impl (Ret r) k = Tau (substProg t impl (k r)).
  Proof. rewrite (PPid (bindSubstProg t impl (Ret r) k)) at 1. unfold PP, bindSubstProg at 1. reflexivity. Qed.

  Lemma bindSubstProgTau {E F R R'} t (impl : ModuleImpl E F) (p : Prog E R) (k : R -> Prog F R') :
    bindSubstProg t impl (Tau p) k = Tau (bindSubstProg t impl p k).
  Proof. rewrite (PPid (bindSubstProg t impl (Tau p) k)) at 1. unfold PP, bindSubstProg at 1. reflexivity. Qed.

  Lemma substProg_ret_inv {E F R} t (impl : ModuleImpl E F) (p : Prog F R) r :
    substProg t impl p = Ret r -> p = Ret r.
  Proof.
    destruct p.
    - rewrite substProgVis. discriminate.
    - rewrite substProgRet. inversion 1. reflexivity.
    - rewrite substProgTau. discriminate.
  Qed.

  Lemma bindSubstProg_not_ret {E F R R'} t (impl : ModuleImpl E F)
      (p : Prog E R) (k : R -> Prog F R') r :
    bindSubstProg t impl p k <> Ret r.
  Proof.
    destruct p.
    - rewrite bindSubstProgVis. discriminate.
    - rewrite bindSubstProgRet. discriminate.
    - rewrite bindSubstProgTau. discriminate.
  Qed.

  Lemma substProg_not_vis {E F R} t (impl : ModuleImpl E F)
      (p : Prog F R) m (k : Sig.ar m -> Prog E R) :
    substProg t impl p <> Vis m k.
  Proof.
    destruct p.
    - rewrite substProgVis. discriminate.
    - rewrite substProgRet. discriminate.
    - rewrite substProgTau. discriminate.
  Qed.

  (* [trace_step] is prefix-agnostic: every constructor either leaves the
     trace unchanged or appends exactly one item at the end, so prepending
     a common prefix to both sides is always valid. Used to splice a
     locally-nil-based sub-witness into an already-accumulated prefix. *)
  Section TraceFraming.
    Context {E F : Op.t}.
    Context {VE : @LTS E}.
    Context (M : ModuleImpl E F).

    Lemma trace_step_frame :
      forall p s0 (sigma : State VE) (c : @ThreadPoolState E F) s1 (sigma' : State VE) c',
        trace_step M (mkTraceConfig s0 sigma c) (mkTraceConfig s1 sigma' c') ->
        trace_step M (mkTraceConfig (p ++ s0) sigma c) (mkTraceConfig (p ++ s1) sigma' c').
    Proof.
      intros p s0 sigma c s1 sigma' c' Hstep.
      inversion Hstep; subst.
      - rewrite app_assoc. eapply TraceStepInv; eauto.
      - rewrite app_assoc. eapply TraceStepRet; eauto.
      - eapply TraceStepU; eauto.
      - eapply TraceStepTau; eauto.
      - rewrite app_assoc. eapply TraceStepError; eauto.
    Qed.

    Lemma trace_steps_frame :
      forall p (A B : @TraceConfig E F VE), trace_steps M A B ->
        trace_steps M (mkTraceConfig (p ++ tc_trace A) (tc_state A) (tc_pool A))
                       (mkTraceConfig (p ++ tc_trace B) (tc_state B) (tc_pool B)).
    Proof.
      intros p A B Htr.
      induction Htr as [A B Hstep | A | A Y B Htr1 IH1 Htr2 IH2].
      - destruct A as [s0 sigma c], B as [s1 sigma' c']. simpl.
        apply rt_step. apply trace_step_frame. exact Hstep.
      - destruct A. simpl. apply rt_refl.
      - eapply rt_trans; eauto.
    Qed.
  End TraceFraming.

  (* [TMap.add] commutes at distinct keys. Needed to justify inserting an
     untouched thread's bookkeeping entry at an earlier point of a
     derivation than where it "really" occurs (see [csilent_steps_add_extra]
     below), which is what lets [M]'s internal, per-thread-independent
     progress be reordered relative to unrelated threads' invocation
     events. Proved directly by induction on [PositiveMap.add]'s own
     recursive structure: keys with a different leading bit land in
     different [Node] fields and commute "for free" by unfolding; keys
     sharing a leading bit recurse on the shared subtree via the IH. *)
  Lemma tmap_add_add {A} :
    forall (i j : positive) (x y : A) (m : TMap.t A),
      i <> j -> TMap.add i x (TMap.add j y m) = TMap.add j y (TMap.add i x m).
  Proof.
    induction i as [i IH | i IH | ]; intros j x y m Hne;
      destruct j as [j | j | ]; destruct m as [ | l o r]; simpl;
      try reflexivity;
      try (exfalso; apply Hne; reflexivity);
      f_equal; apply IH; congruence.
  Qed.

  (** * The composed-object LTS [compLTS VE M] : the derived [@LTS F]
      obtained by running [M] over [VE] and hiding the underlay, used as
      the "intermediate library" against which the top implementation is
      measured when relating [M1 ▶ M2]'s traces over [VE] to [M2]'s traces.
      This is the trace-level analogue of overObj/[Spec T F] in LHL's
      vertical-compositionality proof (see VerticalCompositionalityPlan.md). *)
  Section CompLTS.
    Context {E F : Op.t}.
    Context (VE : @LTS E).
    Context (M : ModuleImpl E F).

    Definition CState : Type := State VE * @ThreadPoolState E F.

    (* A single [trace_step] that leaves the trace unchanged: exactly the
       [TraceStepU]/[TraceStepTau] cases. *)
    Definition csilent_step (X Y : CState) : Prop :=
      trace_step M (mkTraceConfig nil (fst X) (snd X)) (mkTraceConfig nil (fst Y) (snd Y)).

    Definition csilent_steps := clos_refl_trans _ csilent_step.

    (* [csilent_step] only ever exercises [TraceStepU]/[TraceStepTau] (the
       other three constructors all grow the trace, ruled out here since
       both sides are [nil]), both of which touch [TMap.add] at a single
       key -- so an untouched extra thread's entry commutes past it
       freely. This is what lets [M]'s internal work for one thread be
       reordered relative to bookkeeping-only invocation events for
       unrelated threads (see [VerticalCompositionalityPlan.md]). *)
    Lemma csilent_step_dom_preserved :
      forall X Y, csilent_step X Y ->
        forall t2, TMap.find t2 (snd X) = None <-> TMap.find t2 (snd Y) = None.
    Proof.
      intros [sigma c] [sigma' c'] Hstep t2.
      unfold csilent_step in Hstep. simpl in Hstep.
      inversion Hstep; subst; simpl in *.
      - inversion Hstep0 as [f0 ts1 ts2' Hfind Hts Hupd]; subst.
        destruct (Pos.eq_dec (te_tid ev) t2); subst.
        + rewrite Hfind, TMap.gss. split; discriminate.
        + rewrite TMap.gso; auto. tauto.
      - inversion Hstep0 as [ts1 ts2' Hfind Hts Hupd]; subst.
        destruct (Pos.eq_dec t0 t2); subst.
        + rewrite Hfind, TMap.gss. split; discriminate.
        + rewrite TMap.gso; auto. tauto.
    Qed.

    Lemma csilent_steps_dom_preserved :
      forall X Y, csilent_steps X Y ->
        forall t2, TMap.find t2 (snd X) = None <-> TMap.find t2 (snd Y) = None.
    Proof.
      intros X Y Htr.
      unfold csilent_steps in Htr.
      induction Htr as [X Y Hstep | X | X Y Z Htr1 IH1 Htr2 IH2]; intros t2.
      - apply csilent_step_dom_preserved. exact Hstep.
      - tauto.
      - rewrite IH1, IH2. tauto.
    Qed.

    Lemma csilent_step_add_extra :
      forall X Y, csilent_step X Y ->
        forall t2 tse, TMap.find t2 (snd X) = None -> TMap.find t2 (snd Y) = None ->
          csilent_step (pair (fst X) (TMap.add t2 tse (snd X))) (pair (fst Y) (TMap.add t2 tse (snd Y))).
    Proof.
      intros [sigma c] [sigma' c'] Hstep t2 tse Hf Hf'.
      unfold csilent_step in *. simpl in *.
      inversion Hstep; subst; simpl in *.
      - inversion Hstep0 as [f0 ts1 ts2' Hfind Hts Hupd]; subst.
        assert (Ht2 : te_tid ev <> t2) by (intro Heq; subst; rewrite Hfind in Hf; discriminate).
        assert (Hustep' : ustep ev sigma (TMap.add t2 tse c) sigma'
                             (TMap.add t2 tse (TMap.add (te_tid ev) ts2' c))).
        { eapply UStep with (ts1 := ts1) (ts2 := ts2').
          - rewrite TMap.gso; eauto.
          - exact Hts.
          - symmetry. apply (tmap_add_add (te_tid ev) t2); auto. }
        apply (TraceStepU M nil sigma (TMap.add t2 tse c) ev sigma' _ Hustep').
      - inversion Hstep0 as [ts1 ts2' Hfind Hts Hupd]; subst.
        assert (Ht2 : t0 <> t2) by (intro Heq; subst; rewrite Hfind in Hf; discriminate).
        assert (Htau' : taustep t0 (TMap.add t2 tse c) (TMap.add t2 tse (TMap.add t0 ts2' c))).
        { eapply TauStep with (ts1 := ts1) (ts2 := ts2').
          - rewrite TMap.gso; eauto.
          - exact Hts.
          - symmetry. apply (tmap_add_add t0 t2); auto. }
        apply (TraceStepTau M nil sigma' (TMap.add t2 tse c) t0 _ Htau').
    Qed.

    Lemma csilent_steps_add_extra :
      forall X Y, csilent_steps X Y ->
        forall t2 tse, TMap.find t2 (snd X) = None -> TMap.find t2 (snd Y) = None ->
          csilent_steps (pair (fst X) (TMap.add t2 tse (snd X))) (pair (fst Y) (TMap.add t2 tse (snd Y))).
    Proof.
      intros X Y Htr.
      unfold csilent_steps in Htr.
      induction Htr as [X Y Hstep | X | X Y Z Htr1 IH1 Htr2 IH2]; intros t2 tse Hf Hf'.
      - apply rt_step. apply csilent_step_add_extra; auto.
      - apply rt_refl.
      - assert (HfY : TMap.find t2 (snd Y) = None).
        { apply (csilent_steps_dom_preserved X Y Htr1 t2). exact Hf. }
        eapply rt_trans; [apply IH1 | apply IH2]; auto.
    Qed.

    (* [compStep] is split asymmetrically between invocation and return,
       unlike a naive "silent closure then one visible event" bundling
       (which is unsound: a run can legitimately stop right after an
       invocation event, before any of [M]'s internal computation for it
       has actually run).

       - Invocation is *pure bookkeeping*, mirroring [invstep] directly:
         always available, no closure, no reference to [M]'s internal
         computation at all. This matches how a fresh call is recorded
         "for free" the instant it's issued (mirrors [substProg]'s own
         [Vis m k -> Tau (bindSubstProg ...)] unfold, which is a single,
         unconditional silent step of the real vertical composite).
       - Return bundles the *entire* internal computation: arbitrary
         silent (VE-level) closure, then exactly the one [TraceStepRet]
         completing [M]'s own execution of this operation. This is sound
         because a completed return is only ever exposed once [M] has
         actually finished computing it -- there is no "stops early"
         case to worry about here. *)
    Inductive compStep : ThreadEvent -> CState -> CState -> Prop :=
    | CompStepInv t op sigma c
        (Hfree : TMap.find t c = None) :
        compStep (Build_ThreadEvent t (InvEv op)) (pair sigma c)
          (pair sigma (TMap.add t (Build_ThreadState op (M op t) None) c))
    | CompStepRet t op r X X' Y
        (Hsilent : csilent_steps X X')
        (Hvis : trace_step M (mkTraceConfig nil (fst X') (snd X'))
                  (mkTraceConfig (TEvent (Build_ThreadEvent t (ResEv op r)) :: nil) (fst Y) (snd Y))) :
        compStep (Build_ThreadEvent t (ResEv op r)) X Y.

    (* Invoking [op] fresh from [X] is doomed: silent closure, then the
       fresh invocation immediately errors (one more [trace_step], the
       [TraceStepError] case). Matches the one-shot-oracle shape [Error]
       has at every other layer of this development ([ts_error]). *)
    Definition compError (te : ThreadEvent) (X : CState) : Prop :=
      match te_ev te with
      | InvEv op =>
          exists X' c1,
            csilent_steps X X' /\
            TMap.find (te_tid te) (snd X') = None /\
            trace_step M
              (mkTraceConfig nil (fst X')
                 (TMap.add (te_tid te) (Build_ThreadState op (M op (te_tid te)) None) (snd X')))
              (mkTraceConfig (TErr op :: nil) (fst X') c1)
      | ResEv _ _ => False
      end.

    Definition compLTS : @LTS F :=
      {| State := CState; Step := compStep; Error := compError |}.

  End CompLTS.

  (** * Three-way pool-splitting invariant for vertical composition.

      Unlike [compLTS] (used to package "M1 over VE" as an independently
      queryable object -- abandoned for the main proof, see
      [VerticalCompositionalityPlan.md]), this section supports a *direct*
      two-pass argument against the real [M1 ▶ M2] derivation:
      - Pass 1 walks a given [trace_steps (M1 ▶ M2)] run once and extracts
        the F-level trace [m] of operations [M1] actually completes, in the
        order it actually completes them (no comparison to any
        independently-generated ordering, so no reordering obstacle).
      - [CompLin M1 sigma0 rho0] is applied exactly once, to the complete,
        already-fixed [m], producing a witnessing [idImpl]-over-[rho0] run.
      - Pass 2 walks the *same* derivation again, in the *same* order,
        building [M2]'s shadow run over that witness via [pools_vcomp].

      [thread_vcomp]/[pools_vcomp] relate, per thread: the composite's own
      [ThreadState E G] (running [substProg t M1 (M2 g t)]-shaped programs),
      [M2]'s shadow [ThreadState F G] (as if [M2] ran directly over an
      abstract F-level library), and [M1]'s own in-flight [ThreadState E F]
      bookkeeping. This is the vertical-stacking analogue of [hpools] in
      [CompLinHComp.v] (there, splitting a tensor product; here, splitting a
      layered stack), rederived fresh against [ThreadPoolState] rather than
      reused from [Compositionality.v]'s [thread_comp] (which additionally
      threads speculative [LinState] linearization bookkeeping this proof
      doesn't need, since it works with concretely-completed values, not
      speculative linearization points). *)
  Section VCompPools.
    Context {E F G : Op.t}.
    Context (M1 : ModuleImpl E F).

    (* Tracks whether [M1]'s own in-flight E-level continuation [u] is
       itself mid an E-level call; mirrors [ts_pend]. *)
    Definition pending_ok {R} (p : Prog E R) (b : option (Sig.op E)) : Prop :=
      match b with
      | None => True
      | Some m => exists k : Sig.ar m -> Prog E R, p = Vis m k
      end.

    Variant thread_vcomp t :
        option (@ThreadState E G) -> option (@ThreadState F G) -> option (@ThreadState E F) -> Prop :=
    | TVC_None : thread_vcomp t None None None
    | TVC_Idle q (p : Prog F (Sig.ar q)) :
        thread_vcomp t
          (Some (Build_ThreadState q (substProg t M1 p) None))
          (Some (Build_ThreadState q p None))
          None
    | TVC_Mid q m (k : Sig.ar m -> Prog F (Sig.ar q)) (u : Prog E (Sig.ar m)) b
        (Hb : pending_ok u b) :
        thread_vcomp t
          (Some (Build_ThreadState q (bindSubstProg t M1 u k) b))
          (Some (Build_ThreadState q (Vis m k) (Some m)))
          (Some (Build_ThreadState m u b)).

    Definition pools_vcomp
        (c : @ThreadPoolState E G) (cFG : @ThreadPoolState F G) (cEF : @ThreadPoolState E F) : Prop :=
      forall t, thread_vcomp t (TMap.find t c) (TMap.find t cFG) (TMap.find t cEF).

    Lemma pools_vcomp_empty :
      pools_vcomp (TMap.empty _) (TMap.empty _) (TMap.empty _).
    Proof. intro t. rewrite !TMap.gempty. constructor. Qed.

    Lemma pools_vcomp_set t c cFG cEF ec eFG eEF :
      pools_vcomp c cFG cEF -> thread_vcomp t ec eFG eEF ->
      pools_vcomp
        (match ec with Some x => TMap.add t x c | None => TMap.remove t c end)
        (match eFG with Some x => TMap.add t x cFG | None => TMap.remove t cFG end)
        (match eEF with Some x => TMap.add t x cEF | None => TMap.remove t cEF end).
    Proof.
      intros Hp Ht i. destruct (Pos.eq_dec i t); subst.
      - destruct ec, eFG, eEF; simpl in *;
          repeat rewrite ?TMap.gss, ?TMap.grs; auto.
      - destruct ec, eFG, eEF; simpl in *;
          repeat rewrite ?TMap.gso, ?TMap.gro by auto; apply Hp.
    Qed.

  End VCompPools.

  (** * Pass 1 (see [VerticalCompositionalityPlan.md]): walk a given
      [trace_steps (M1 ▶ M2)] run once and extract the F-level trace of
      operations [M1] actually completes, in the order it actually
      completes them -- self-consistent by construction (no comparison to
      any independently-generated ordering), unlike the abandoned
      [compLTS] route. *)
  Section VCompPass1.
    Context {E F G : Op.t}.
    Context {VE : @LTS E}.
    Context (M1 : ModuleImpl E F) (M2 : ModuleImpl F G).

    (* An [M1]-level witness that [M1], run from [sigma0]/[cEF0], can reach
       an internal error at some prefix [tr] (undefined behavior from that
       point on, per [CompLin.v]'s [TErr]/[ImplTracesClosed] design). *)
    Definition m1_reaches_error (sigma0 : State VE) (cEF0 : @ThreadPoolState E F) : Prop :=
      exists f tr sigma_e cEF_e,
        trace_steps M1 (mkTraceConfig nil sigma0 cEF0) (mkTraceConfig (tr ++ TErr f :: nil) sigma_e cEF_e).

    Lemma vcomp_pass1_step :
      forall (A B : @TraceConfig E G VE),
        trace_step (implVComp M1 M2) A B ->
        forall cFG cEF, pools_vcomp M1 (tc_pool A) cFG cEF ->
          (exists tr cFG' cEF',
            trace_steps M1 (mkTraceConfig nil (tc_state A) cEF) (mkTraceConfig tr (tc_state B) cEF') /\
            pools_vcomp M1 (tc_pool B) cFG' cEF')
          \/ m1_reaches_error (tc_state A) cEF.
    Proof.
      intros [s0 sigma c] [s1 sigma' c'] Hstep cFG cEF Hp.
      simpl in *.
      inversion Hstep; subst; simpl in *.
      - (* TraceStepInv *)
        left.
        inversion Hstep0; subst.
        pose proof (Hp t0) as Ht.
        rewrite Hfind in Ht.
        inversion Ht as [ | | ]; subst.
        exists nil, (TMap.add t0 (Build_ThreadState f (M2 f t0) None) cFG), cEF.
        split.
        + apply rt_refl.
        + intro i. destruct (Pos.eq_dec i t0); subst.
          * unfold implVComp. rewrite !TMap.gss, <- H0. constructor.
          * unfold implVComp. rewrite !TMap.gso by auto. apply Hp.
      - (* TraceStepRet *)
        left.
        inversion Hstep0; subst.
        pose proof (Hp t0) as Ht.
        rewrite Hfind in Ht.
        dependent destruction Ht.
        2: { exfalso. eapply bindSubstProg_not_ret. eassumption. }
        apply substProg_ret_inv in x0. subst p.
        exists nil, (TMap.remove t0 cFG), cEF.
        split.
        + apply rt_refl.
        + intro i. destruct (Pos.eq_dec i t0); subst.
          * rewrite TMap.grs, TMap.grs, <- x. constructor.
          * rewrite TMap.gro, TMap.gro by auto. apply Hp.
      - (* TraceStepU *)
        inversion Hstep0; subst.
        inversion Hstep1; subst.
        + (* ts_inv sub-case: M1's underlay op [op] is being invoked *)
          left.
          simpl in Hfind.
          pose proof (Hp t0) as Ht.
          rewrite Hfind in Ht.
          dependent destruction Ht.
          1: { exfalso. eapply substProg_not_vis. eassumption. }
          destruct u; try (rewrite bindSubstProgRet in x0 || rewrite bindSubstProgTau in x0); try discriminate.
          rewrite bindSubstProgVis in x0.
          dependent destruction x0.
          simpl.
          exists nil,
            (TMap.add t0 (Build_ThreadState f (Vis m0 k0) (Some m0)) cFG),
            (TMap.add t0 (Build_ThreadState m0 (Vis op k1) (Some op)) cEF).
          split.
          * apply rt_step.
            apply (TraceStepU M1 nil sigma cEF (Build_ThreadEvent t0 (InvEv op)) sigma' _).
            eapply UStep with
              (ts1 := Build_ThreadState m0 (Vis op k1) None)
              (ts2 := Build_ThreadState m0 (Vis op k1) (Some op)).
            -- symmetry. exact x.
            -- econstructor. exact Hstep2.
            -- reflexivity.
          * intro i. destruct (Pos.eq_dec i t0); subst.
            -- rewrite !TMap.gss.
               pose proof (TVC_Mid M1 t0 f m0 k0 (Vis op k1) (Some op) (ex_intro _ k1 eq_refl)) as HH.
               rewrite bindSubstProgVis in HH.
               exact HH.
            -- rewrite !TMap.gso by auto. apply Hp.
        + (* ts_res sub-case *)
          left.
          simpl in Hfind.
          pose proof (Hp t0) as Ht.
          rewrite Hfind in Ht.
          dependent destruction Ht.
          destruct u; try (rewrite bindSubstProgRet in x0 || rewrite bindSubstProgTau in x0); try discriminate.
          rewrite bindSubstProgVis in x0.
          dependent destruction x0.
          simpl.
          exists nil, cFG, (TMap.add t0 (Build_ThreadState m0 (k1 ret) None) cEF).
          split.
          * apply rt_step.
            apply (TraceStepU M1 nil sigma cEF (Build_ThreadEvent t0 (ResEv op ret)) sigma' _).
            eapply UStep with
              (ts1 := Build_ThreadState m0 (Vis op k1) (Some op))
              (ts2 := Build_ThreadState m0 (k1 ret) None).
            -- symmetry. exact x.
            -- econstructor. exact Hstep2.
            -- reflexivity.
          * intro i. destruct (Pos.eq_dec i t0); subst.
            -- rewrite !TMap.gss, <- x1.
               exact (TVC_Mid M1 t0 f m0 k0 (k1 ret) None I).
            -- rewrite !TMap.gso by auto. apply Hp.
      - (* TraceStepTau *)
        left.
        inversion Hstep0; subst.
        inversion Hstep1; subst.
        pose proof (Hp t0) as Ht.
        rewrite Hfind in Ht.
        dependent destruction Ht.
        + (* TVC_Idle: M2's own continuation p0 stepped to Tau p *)
          destruct p0 as [m k | r | p1].
          * (* Vis m k: F-op invocation *)
            rewrite substProgVis in x0. inversion x0; subst.
            exists (TEvent (Build_ThreadEvent t0 (InvEv m)) :: nil),
              (TMap.add t0 (Build_ThreadState f (Vis m k) (Some m)) cFG),
              (TMap.add t0 (Build_ThreadState m (M1 m t0) None) cEF).
            split.
            -- apply rt_step.
               apply (TraceStepInv M1 nil sigma' cEF t0 m).
               constructor.
               ++ symmetry. exact x.
               ++ reflexivity.
            -- intro i. destruct (Pos.eq_dec i t0); subst.
               ++ rewrite !TMap.gss. apply TVC_Mid. exact I.
               ++ rewrite !TMap.gso by auto. apply Hp.
          * (* Ret r: impossible, substProgRet never produces Tau *)
            rewrite substProgRet in x0. discriminate.
          * (* Tau p1: pure M2-level silent step *)
            rewrite substProgTau in x0. inversion x0; subst.
            exists nil, (TMap.add t0 (Build_ThreadState f p1 None) cFG), cEF.
            split.
            -- apply rt_refl.
            -- intro i. destruct (Pos.eq_dec i t0); subst.
               ++ rewrite !TMap.gss, <- x. apply TVC_Idle.
               ++ rewrite !TMap.gso by auto. apply Hp.
        + (* TVC_Mid *)
          destruct u as [m' k' | r | u1].
          * (* Vis: impossible, bindSubstProgVis never produces Tau *)
            rewrite bindSubstProgVis in x0. discriminate.
          * (* Ret r: F-op completion *)
            rewrite bindSubstProgRet in x0. inversion x0; subst.
            destruct b as [m' |].
            { destruct Hb as [k'' Hk'']. discriminate. }
            exists (TEvent (Build_ThreadEvent t0 (ResEv m0 r)) :: nil),
              (TMap.add t0 (Build_ThreadState f (k r) None) cFG),
              (TMap.remove t0 cEF).
            split.
            -- apply rt_step.
               apply (TraceStepRet M1 nil sigma' cEF t0 m0 r).
               constructor.
               ++ symmetry. exact x.
               ++ reflexivity.
            -- intro i. destruct (Pos.eq_dec i t0); subst.
               ++ rewrite !TMap.gss, TMap.grs. apply TVC_Idle.
               ++ rewrite !TMap.gso, TMap.gro by auto. apply Hp.
          * (* Tau u1: pure M1-internal silent step *)
            rewrite bindSubstProgTau in x0. inversion x0; subst.
            destruct b as [m' |].
            { destruct Hb as [k'' Hk'']. discriminate. }
            exists nil, cFG, (TMap.add t0 (Build_ThreadState m0 u1 None) cEF).
            split.
            -- apply rt_step.
               apply (TraceStepTau M1 nil sigma' cEF t0).
               apply (TauStep t0 cEF _ (Build_ThreadState m0 (Tau u1) None) (Build_ThreadState m0 u1 None)).
               ++ symmetry. exact x.
               ++ constructor.
               ++ reflexivity.
            -- intro i. destruct (Pos.eq_dec i t0); subst.
               ++ rewrite !TMap.gss, <- x1. apply TVC_Mid. exact I.
               ++ rewrite !TMap.gso by auto. apply Hp.
      - (* TraceStepError *)
        right.
        inversion Herror; subst.
        simpl in Hfind.
        pose proof (Hp t0) as Ht.
        rewrite Hfind in Ht.
        dependent destruction Ht.
        1: { exfalso. eapply substProg_not_vis. eassumption. }
        destruct u; try (rewrite bindSubstProgRet in x0 || rewrite bindSubstProgTau in x0); try discriminate.
        rewrite bindSubstProgVis in x0.
        dependent destruction x0.
        exists m0, nil, sigma', cEF.
        apply rt_step.
        apply (TraceStepError M1 nil sigma' cEF m0 (Build_ThreadEvent t0 (InvEv op)) (Build_ThreadState m0 (Vis op k1) None)).
        + symmetry. exact x.
        + econstructor. exact Herror0.
    Qed.

    Theorem vcomp_pass1 :
      forall (A B : @TraceConfig E G VE),
        trace_steps (implVComp M1 M2) A B ->
        forall cFG cEF, pools_vcomp M1 (tc_pool A) cFG cEF ->
          (exists tr cFG' cEF',
            trace_steps M1 (mkTraceConfig nil (tc_state A) cEF) (mkTraceConfig tr (tc_state B) cEF') /\
            pools_vcomp M1 (tc_pool B) cFG' cEF')
          \/ m1_reaches_error (tc_state A) cEF.
    Proof.
      intros A B Htr.
      induction Htr as [A B Hstep | A | A Y B Htr1 IH1 Htr2 IH2]; intros cFG cEF Hp.
      - eapply vcomp_pass1_step; eauto.
      - left. exists nil, cFG, cEF. split; [apply rt_refl | exact Hp].
      - destruct (IH1 cFG cEF Hp) as [[m1 [cFG1 [cEF1 [Htr1' Hp1]]]] | Herr1].
        + destruct (IH2 cFG1 cEF1 Hp1) as [[m2 [cFG2 [cEF2 [Htr2' Hp2]]]] | Herr2].
          * left. exists (m1 ++ m2), cFG2, cEF2. split; [| exact Hp2].
            eapply rt_trans.
            -- exact Htr1'.
            -- pose proof (trace_steps_frame M1 m1 _ _ Htr2') as H.
               simpl in H. rewrite app_nil_r in H. exact H.
          * right.
            destruct Herr2 as (f & tr2 & sigma_e & cEF_e & Herr2').
            exists f, (m1 ++ tr2), sigma_e, cEF_e.
            pose proof (trace_steps_frame M1 m1 _ _ Herr2') as H.
            simpl in H. rewrite app_nil_r, app_assoc in H.
            eapply rt_trans; [exact Htr1' | exact H].
        + right. exact Herr1.
    Qed.
  End VCompPass1.

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
    Admitted.
  End VComp.

End CompLinVComp.
