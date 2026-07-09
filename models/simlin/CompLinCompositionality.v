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
Require Import CompLin.

(** Compositionality of Compositional Linearizability (Lemma 4.2, Lemma 4.3,
    §4.3): [CompLin] (Definition 4.1) composes horizontally, when two
    independent libraries/implementations are run side by side, and
    vertically, when an implementation is stacked on top of another one.

    The composition operators on [ModuleImpl] themselves ([implHComp]/[⊗]
    and [implVComp]/[▶]) are redefined here from scratch rather than reused
    from [Compositionality.v]: that file builds them to support the
    [TPSimulationSet]/[AbstractConfig] machinery of Definition 5.2, while
    this file only needs them to state compositionality directly for the
    trace semantics of [CompLin.v]. *)
Module CompLinCompositionality.
  Import Reg.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import Semantics.
  Import CompLin.CompLin.

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
      [Sig.Plus.omap F1 F2] into its two independent components. This is
      the trace-level (Poss-free) analogue of [hpools]/[hthread] from
      [Compositionality.v]'s [HCompTPSim] section. *)
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

    Fixpoint proj_l (s : Trace (Sig.Plus.omap F1 F2)) : Trace F1 :=
      match s with
      | nil => nil
      | ev :: rest =>
          match te_ev ev with
          | InvEv op =>
              match op with
              | inl f => Build_ThreadEvent (te_tid ev) (InvEv f) :: proj_l rest
              | inr _ => proj_l rest
              end
          | ResEv op r =>
              match op, r with
              | inl f, r => Build_ThreadEvent (te_tid ev) (ResEv f r) :: proj_l rest
              | inr _, _ => proj_l rest
              end
          end
      end.

    Fixpoint proj_r (s : Trace (Sig.Plus.omap F1 F2)) : Trace F2 :=
      match s with
      | nil => nil
      | ev :: rest =>
          match te_ev ev with
          | InvEv op =>
              match op with
              | inr f => Build_ThreadEvent (te_tid ev) (InvEv f) :: proj_r rest
              | inl _ => proj_r rest
              end
          | ResEv op r =>
              match op, r with
              | inr f, r => Build_ThreadEvent (te_tid ev) (ResEv f r) :: proj_r rest
              | inl _, _ => proj_r rest
              end
          end
      end.

    Lemma proj_l_app s1 s2 : proj_l (s1 ++ s2) = proj_l s1 ++ proj_l s2.
    Proof.
      induction s1 as [| ev s1 IH]; simpl; auto.
      destruct (te_ev ev) as [[f | f] | [f | f] r]; simpl; rewrite IH; reflexivity.
    Qed.

    Lemma proj_r_app s1 s2 : proj_r (s1 ++ s2) = proj_r s1 ++ proj_r s2.
    Proof.
      induction s1 as [| ev s1 IH]; simpl; auto.
      destruct (te_ev ev) as [[f | f] | [f | f] r]; simpl; rewrite IH; reflexivity.
    Qed.

    Lemma proj_l_inl_singleton t f :
      proj_l (Build_ThreadEvent t (@InvEv (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) f)) :: nil) =
      Build_ThreadEvent t (InvEv f) :: nil.
    Proof. reflexivity. Qed.

    Lemma proj_r_inl_singleton t f :
      proj_r (Build_ThreadEvent t (@InvEv (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) f)) :: nil) = nil.
    Proof. reflexivity. Qed.

    Lemma proj_l_inr_singleton t f :
      proj_l (Build_ThreadEvent t (@InvEv (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) f)) :: nil) = nil.
    Proof. reflexivity. Qed.

    Lemma proj_r_inr_singleton t f :
      proj_r (Build_ThreadEvent t (@InvEv (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) f)) :: nil) =
      Build_ThreadEvent t (InvEv f) :: nil.
    Proof. reflexivity. Qed.

    Lemma proj_l_inl_singleton_res t f (r : Sig.ar f) :
      proj_l (Build_ThreadEvent t (@ResEv (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) f) r) :: nil) =
      Build_ThreadEvent t (ResEv f r) :: nil.
    Proof. reflexivity. Qed.

    Lemma proj_r_inl_singleton_res t f (r : Sig.ar f) :
      proj_r (Build_ThreadEvent t (@ResEv (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) f) r) :: nil) = nil.
    Proof. reflexivity. Qed.

    Lemma proj_l_inr_singleton_res t f (r : Sig.ar f) :
      proj_l (Build_ThreadEvent t (@ResEv (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) f) r) :: nil) = nil.
    Proof. reflexivity. Qed.

    Lemma proj_r_inr_singleton_res t f (r : Sig.ar f) :
      proj_r (Build_ThreadEvent t (@ResEv (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) f) r) :: nil) =
      Build_ThreadEvent t (ResEv f r) :: nil.
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
                        (proj_l (s0 ++ Build_ThreadEvent t0
                          (@InvEv (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) f1)) :: nil))
                        sigma1 (TMap.add t0 (Build_ThreadState f1 (M1 f1 t0) None) c1))).
            { rewrite proj_l_app, proj_l_inl_singleton.
              apply rt_step. econstructor. econstructor; eauto. }
            assert (Hs2 : trace_steps M2 (mkTraceConfig (proj_r s0) sigma2 c2)
                     (mkTraceConfig
                        (proj_r (s0 ++ Build_ThreadEvent t0
                          (@InvEv (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) f1)) :: nil))
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
                        (proj_l (s0 ++ Build_ThreadEvent t0
                          (@InvEv (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) f2)) :: nil))
                        sigma1 c1)).
            { rewrite proj_l_app, proj_l_inr_singleton, app_nil_r. apply rt_refl. }
            assert (Hs2 : trace_steps M2 (mkTraceConfig (proj_r s0) sigma2 c2)
                     (mkTraceConfig
                        (proj_r (s0 ++ Build_ThreadEvent t0
                          (@InvEv (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) f2)) :: nil))
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
                        (proj_l (s0 ++ Build_ThreadEvent t0
                          (@ResEv (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) (ts_op ts1)) ret) :: nil))
                        sigma1 (TMap.remove t0 c1))).
            { rewrite proj_l_app, proj_l_inl_singleton_res.
              apply rt_step. econstructor. econstructor.
              - exact Hfind1.
              - reflexivity. }
            assert (Hs2 : trace_steps M2 (mkTraceConfig (proj_r s0) sigma2 c2)
                     (mkTraceConfig
                        (proj_r (s0 ++ Build_ThreadEvent t0
                          (@ResEv (Sig.Plus.omap F1 F2) (@inl (Sig.op F1) (Sig.op F2) (ts_op ts1)) ret) :: nil))
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
                        (proj_l (s0 ++ Build_ThreadEvent t0
                          (@ResEv (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) (ts_op ts2)) ret) :: nil))
                        sigma1 c1)).
            { rewrite proj_l_app, proj_l_inr_singleton_res, app_nil_r. apply rt_refl. }
            assert (Hs2 : trace_steps M2 (mkTraceConfig (proj_r s0) sigma2 c2)
                     (mkTraceConfig
                        (proj_r (s0 ++ Build_ThreadEvent t0
                          (@ResEv (Sig.Plus.omap F1 F2) (@inr (Sig.op F1) (Sig.op F2) (ts_op ts2)) ret) :: nil))
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
    Admitted.
  End HCompDecompose.

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
    Admitted.
  End HComp.

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

End CompLinCompositionality.
