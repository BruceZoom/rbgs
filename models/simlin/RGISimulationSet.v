Require Import FMapPositive.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Lia.
Require Import Classical.

Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import Logics.
Require Import Assertion.
Require Import TPSimulationSet.

(** Set-level rely/guarantee simulations with a finite abstract-update
    prefix.  The natural-number index is internal: it is the exact number
    of remaining possibility updates.  Rely transitions may only preserve
    or decrease it. *)
Module RGISimulation.
  Import Reg LinCCALBase LTSSpec Semantics AssertionsSet Lang.
  Import TPSimulationSet.TPSimulation.

  Section Simulations.
    Context {E F : Op.t} {VE : @LTS E} {VF : @LTS F}.
    Context (M : ModuleImpl E F).

    Inductive MethodUpdateSteps (G : @RGRelation _ _ VE VF) (I : Assertion)
        (sigma : State VE) : nat ->
        AbstractConfig VF -> AbstractConfig VF -> Prop :=
    | MethodUpdatesRefl Delta : MethodUpdateSteps G I sigma 0 Delta Delta
    | MethodUpdatesStep n Delta Delta' DeltaFinal :
        (Delta' ⊆ ac_steps Delta)%AbstractConfig ->
        G (sigma, Delta) (sigma, Delta') ->
        I (sigma, Delta) ->
        MethodUpdateSteps G I sigma n Delta' DeltaFinal ->
        MethodUpdateSteps G I sigma (S n) Delta DeltaFinal.

    Inductive RGIUpdateSteps (G : @RGRelation _ _ VE VF) (I : Assertion) t
        (sigma : State VE) (c : @ThreadPoolState E F) : nat ->
        AbstractConfig VF -> AbstractConfig VF -> Prop :=
    | RGIUpdatesRefl Delta : RGIUpdateSteps G I t sigma c 0 Delta Delta
    | RGIUpdatesStep n Delta Delta' DeltaFinal ts :
        TMap.find t c = Some ts ->
        (Delta' ⊆ ac_steps Delta)%AbstractConfig ->
        G (sigma, Delta) (sigma, Delta') ->
        I (sigma, Delta) ->
        RGIUpdateSteps G I t sigma c n Delta' DeltaFinal ->
        RGIUpdateSteps G I t sigma c (S n) Delta DeltaFinal.

    Lemma method_updates_to_rgi G I t sigma c n Delta DeltaFinal ts :
      TMap.find t c = Some ts ->
      MethodUpdateSteps G I sigma n Delta DeltaFinal ->
      RGIUpdateSteps G I t sigma c n Delta DeltaFinal.
    Proof.
      intros Hfind Hadmin. induction Hadmin.
      - constructor.
      - econstructor; eauto.
    Qed.

    Lemma method_updates_find_some G I sigma n Delta DeltaFinal t :
      MethodUpdateSteps G I sigma n Delta DeltaFinal ->
      (forall rho pi, Delta rho pi -> exists ls,
        TMap.find t pi = Some ls) ->
      forall rho pi, DeltaFinal rho pi -> exists ls,
        TMap.find t pi = Some ls.
    Proof.
      intros Hadmin. induction Hadmin; intros Hfind rho pi Hposs.
      - eauto.
      - eapply IHHadmin.
        + intros rho0 pi0 Hposs0. apply H in Hposs0.
          inversion Hposs0; subst.
          destruct (Hfind _ _ Hposs1) as [ls Hls].
          eapply poss_steps_nondec; eauto.
        + exact Hposs.
    Qed.

    Lemma rgi_updates_absent G I t sigma c n Delta DeltaFinal :
      TMap.find t c = None ->
      RGIUpdateSteps G I t sigma c n Delta DeltaFinal ->
      n = O /\ DeltaFinal = Delta.
    Proof.
      intros Hnone Hadmin. inversion Hadmin; subst; auto. congruence.
    Qed.

    Lemma rgi_updates_local G I t sigma c c' n Delta DeltaFinal :
      TMap.find t c = TMap.find t c' ->
      RGIUpdateSteps G I t sigma c n Delta DeltaFinal ->
      RGIUpdateSteps G I t sigma c' n Delta DeltaFinal.
    Proof.
      intros Hfind Hadmin. induction Hadmin.
      - constructor.
      - econstructor; eauto. rewrite <- Hfind. exact H.
    Qed.

    Inductive MethodCore (R G : @RGRelation _ _ VE VF) (I : Assertion)
        t (f : Sig.op F)
        (X : nat -> State VE -> Prog E (Sig.ar f) -> option (Sig.op E) ->
          AbstractConfig VF -> Prop)
        (sigma : State VE) (p : Prog E (Sig.ar f))
        (b : option (Sig.op E)) (Delta : AbstractConfig VF) : Prop :=
    | MCore_Error rho pi
        (Hinvariant : I (sigma, Delta))
        (Hposs : Delta rho pi)
        (Herror : poss_steps (PossOk rho pi) PossError)
    | MCore_Continue
        (msim_ustep : forall ev sigma' p' b'
          (Hstep : ts_step f (Build_ThreadEvent t ev) sigma
            (Build_ThreadState f p b) sigma'
            (Build_ThreadState f p' b')),
          exists Delta', (Delta' ⊆ ac_steps Delta)%AbstractConfig /\
            G (sigma, Delta) (sigma', Delta') /\
            exists n, X n sigma' p' b' Delta')
        (msim_retstep : forall ret (Hretv : p = Ret ret /\ b = None),
          (Gret t f ret ⊆ G)%RGRelation /\ I (sigma, ac_res Delta t) /\
          (forall rho pi, Delta rho pi ->
            TMap.find t pi = Some (ls_linr f ret)))
        (msim_taustep : forall p' b'
          (Hstep : ts_taustep (Build_ThreadState f p b)
            (Build_ThreadState f p' b')),
          exists n, X n sigma p' b' Delta)
        (msim_invariant : I (sigma, Delta))
        (msim_stable : forall sigma' Delta',
          R (sigma, Delta) (sigma', Delta') -> I (sigma', Delta') ->
          X O sigma' p b Delta')
        (msim_noerror : forall ev,
          ~ ts_error f (Build_ThreadEvent t ev) sigma
              (Build_ThreadState f p b)).

    CoInductive MethodSimulationRanked
        (R G : @RGRelation _ _ VE VF) (I : Assertion) t (f : Sig.op F) :
        nat -> State VE -> Prog E (Sig.ar f) -> option (Sig.op E) ->
        AbstractConfig VF -> Prop :=
    | MSimRoll : forall n sigma p b Delta DeltaCore,
        MethodUpdateSteps G I sigma n Delta DeltaCore ->
        MethodCore R G I t f (MethodSimulationRanked R G I t f)
          sigma p b DeltaCore ->
        (forall sigma' Delta',
          R (sigma, Delta) (sigma', Delta') -> I (sigma', Delta') ->
          exists n', n' <= n /\
            MethodSimulationRanked R G I t f n' sigma' p b Delta') ->
        MethodSimulationRanked R G I t f n sigma p b Delta.

    Definition MethodSimulation (R G : @RGRelation _ _ VE VF)
        (I : Assertion) t (f : Sig.op F) sigma p b Delta : Prop :=
      exists n, MethodSimulationRanked R G I t f n sigma p b Delta.

    Definition MethodViewRanked R G I t f
        (X : nat -> State VE -> Prog E (Sig.ar f) -> option (Sig.op E) ->
          AbstractConfig VF -> Prop)
        n sigma p b Delta : Prop :=
      exists DeltaCore,
        MethodUpdateSteps G I sigma n Delta DeltaCore /\
        MethodCore R G I t f X
          sigma p b DeltaCore /\
        (forall sigma' Delta',
          R (sigma, Delta) (sigma', Delta') -> I (sigma', Delta') ->
          exists n', n' <= n /\ X n' sigma' p b Delta').

    Lemma MethodSimulation_coinduction_ranked R G I t f
        (X : nat -> State VE -> Prog E (Sig.ar f) -> option (Sig.op E) ->
          AbstractConfig VF -> Prop) :
      (forall n sigma p b Delta, X n sigma p b Delta ->
        MethodViewRanked R G I t f X n sigma p b Delta) ->
      forall n sigma p b Delta, X n sigma p b Delta ->
        MethodSimulationRanked R G I t f n sigma p b Delta.
    Proof.
      intros Hstep. cofix CIH. intros n sigma p b Delta HX.
      destruct (Hstep _ _ _ _ _ HX) as
        [DeltaCore [Hadmin [Hcore Hstable]]].
      econstructor; [exact Hadmin| |].
      - destruct Hcore as [rho pi HI HP HE |
          Hustep Hret Htau HI Hcorestable Hnoerror].
        + eapply MCore_Error; eauto.
        + eapply MCore_Continue.
          * intros ev sigma' p' b' Hconcrete.
            destruct (Hustep _ _ _ _ Hconcrete) as
              [Delta' [Hreach [HG [n' HX']]]].
            exists Delta'. split; [exact Hreach|]. split; [exact HG|].
            exists n'. now apply CIH.
          * exact Hret.
          * intros p' b' Hconcrete.
            destruct (Htau _ _ Hconcrete) as [n' HX'].
            exists n'. now apply CIH.
          * exact HI.
          * intros sigma' Delta' HR HI'. now apply CIH, Hcorestable.
          * exact Hnoerror.
      - intros sigma' Delta' HR HI'.
        destruct (Hstable _ _ HR HI') as [n' [Hle HX']].
        exists n'. split; [exact Hle|]. now apply CIH.
    Qed.

    Lemma method_simulation_normalizes R G I t f n sigma p b Delta :
      MethodSimulationRanked R G I t f n sigma p b Delta ->
      exists DeltaCore,
        MethodUpdateSteps G I sigma n Delta DeltaCore /\
        MethodCore R G I t f (MethodSimulationRanked R G I t f)
          sigma p b DeltaCore.
    Proof. intro Hsim. inversion Hsim; subst. eauto. Qed.

    Inductive RGICore (R G : @RGRelation _ _ VE VF) (I : Assertion) t
        (X : nat -> State VE -> ThreadPoolState -> AbstractConfig VF -> Prop)
        (sigma : State VE) (c : ThreadPoolState)
        (Delta : AbstractConfig VF) : Prop :=
    | RGICore_Error rho pi
        (Hinvariant : I (sigma, Delta)) (Hposs : Delta rho pi)
        (Herror : poss_steps (PossOk rho pi) PossError)
    | RGICore_Continue
        (rgisim_invstep : forall f c' (Hstep : invstep M t f c c'),
          (Ginv t f ⊆ G)%RGRelation /\
          (forall rho pi, Delta rho pi -> TMap.find t pi = None) /\
          exists n, X n sigma c' (ac_inv Delta t f))
        (rgisim_retstep : forall f ret c'
          (Hstep : retstep t f ret c c'),
          (Gret t f ret ⊆ G)%RGRelation /\
          (forall rho pi, Delta rho pi ->
            TMap.find t pi = Some (ls_linr f ret)) /\
          exists n, X n sigma c' (ac_res Delta t))
        (rgisim_ustep : forall ev sigma' c'
          (Hstep : ustep (Build_ThreadEvent t ev) sigma c sigma' c'),
          exists Delta', (Delta' ⊆ ac_steps Delta)%AbstractConfig /\
            G (sigma, Delta) (sigma', Delta') /\
            exists n, X n sigma' c' Delta')
        (rgisim_taustep : forall c' (Hstep : taustep t c c'),
          exists n, X n sigma c' Delta)
        (rgisim_invariant : I (sigma, Delta))
        (rgisim_stable : forall sigma' Delta',
          R (sigma, Delta) (sigma', Delta') -> I (sigma', Delta') ->
          X O sigma' c Delta')
        (rgisim_noerror : forall ev,
          ~ uerror (Build_ThreadEvent t ev) sigma c).

    CoInductive RGISimulationRanked
        (R G : @RGRelation _ _ VE VF) (I : Assertion) t :
        nat -> State VE -> ThreadPoolState -> AbstractConfig VF -> Prop :=
    | RGISimRoll : forall n sigma c Delta DeltaCore,
        RGIUpdateSteps G I t sigma c n Delta DeltaCore ->
        RGICore R G I t (RGISimulationRanked R G I t)
          sigma c DeltaCore ->
        (forall sigma' Delta',
          R (sigma, Delta) (sigma', Delta') -> I (sigma', Delta') ->
          exists n', n' <= n /\
            RGISimulationRanked R G I t n' sigma' c Delta') ->
        RGISimulationRanked R G I t n sigma c Delta.

    Definition RGISimulation (R G : @RGRelation _ _ VE VF)
        (I : Assertion) t sigma c Delta : Prop :=
      exists n, RGISimulationRanked R G I t n sigma c Delta.

    Definition RGIViewRanked R G I t
        (X : nat -> State VE -> ThreadPoolState -> AbstractConfig VF -> Prop)
        n sigma c Delta : Prop :=
      exists DeltaCore,
        RGIUpdateSteps G I t sigma c n Delta DeltaCore /\
        RGICore R G I t X
          sigma c DeltaCore /\
        (forall sigma' Delta',
          R (sigma, Delta) (sigma', Delta') -> I (sigma', Delta') ->
          exists n', n' <= n /\ X n' sigma' c Delta').

    Lemma RGISimulation_coinduction_ranked R G I t
        (X : nat -> State VE -> ThreadPoolState -> AbstractConfig VF -> Prop) :
      (forall n sigma c Delta, X n sigma c Delta ->
        RGIViewRanked R G I t X n sigma c Delta) ->
      forall n sigma c Delta, X n sigma c Delta ->
        RGISimulationRanked R G I t n sigma c Delta.
    Proof.
      intros Hstep. cofix CIH. intros n sigma c Delta HX.
      destruct (Hstep _ _ _ _ HX) as
        [DeltaCore [Hadmin [Hcore Hstable]]].
      econstructor; [exact Hadmin| |].
      - destruct Hcore as [rho pi HI HP HE |
          Hinv Hret Hustep Htau HI Hcorestable Hnoerror].
        + eapply RGICore_Error; eauto.
        + eapply RGICore_Continue.
          * intros f c' Hconcrete.
            destruct (Hinv _ _ Hconcrete) as [HG [Hnone [n' HX']]].
            split; [exact HG|]. split; [exact Hnone|].
            exists n'. now apply CIH.
          * intros f ret c' Hconcrete.
            destruct (Hret _ _ _ Hconcrete) as [HG [Hlin [n' HX']]].
            split; [exact HG|]. split; [exact Hlin|].
            exists n'. now apply CIH.
          * intros ev sigma' c' Hconcrete.
            destruct (Hustep _ _ _ Hconcrete) as
              [Delta' [Hreach [HG [n' HX']]]].
            exists Delta'. split; [exact Hreach|]. split; [exact HG|].
            exists n'. now apply CIH.
          * intros c' Hconcrete.
            destruct (Htau _ Hconcrete) as [n' HX'].
            exists n'. now apply CIH.
          * exact HI.
          * intros sigma' Delta' HR HI'. now apply CIH, Hcorestable.
          * exact Hnoerror.
      - intros sigma' Delta' HR HI'.
        destruct (Hstable _ _ HR HI') as [n' [Hle HX']].
        exists n'. split; [exact Hle|]. now apply CIH.
    Qed.

    Lemma rgi_simulation_normalizes R G I t n sigma c Delta :
      RGISimulationRanked R G I t n sigma c Delta ->
      exists DeltaCore,
        RGIUpdateSteps G I t sigma c n Delta DeltaCore /\
        RGICore R G I t (RGISimulationRanked R G I t)
          sigma c DeltaCore.
    Proof. intro Hsim. inversion Hsim; subst. eauto. Qed.

    Lemma rgi_core_invariant R G I t X sigma c Delta :
      RGICore R G I t X sigma c Delta -> I (sigma, Delta).
    Proof. intros Hcore. destruct Hcore; assumption. Qed.

    Lemma rgi_updates_source_invariant R G I t sigma c n Delta DeltaFinal X :
      RGIUpdateSteps G I t sigma c n Delta DeltaFinal ->
      RGICore R G I t X sigma c DeltaFinal -> I (sigma, Delta).
    Proof.
      intros Hadmin Hcore. dependent destruction Hadmin.
      - destruct Hcore; assumption.
      - assumption.
    Qed.

    Lemma rgi_updates_to_tpsim G I t sigma c n Delta DeltaFinal :
      RGIUpdateSteps G I t sigma c n Delta DeltaFinal ->
      TPSimulation.AbstractUpdateSteps Delta DeltaFinal.
    Proof.
      intro Hadmin. induction Hadmin.
      - constructor.
      - econstructor; eauto.
    Qed.

    Lemma tpsim_updates_trans (Delta1 Delta2 Delta3 : AbstractConfig VF) :
      TPSimulation.AbstractUpdateSteps Delta1 Delta2 ->
      TPSimulation.AbstractUpdateSteps Delta2 Delta3 ->
      TPSimulation.AbstractUpdateSteps Delta1 Delta3.
    Proof.
      intros H12 H23. induction H12.
      - exact H23.
      - econstructor; eauto.
    Qed.

    Lemma rgisim_follow_updates
        (R G : tid -> RGRelation) I
        (HRG : forall t1 t2, t1 <> t2 ->
          (I ⊓ G t1 ⊆ R t2)%RGRelation)
        actor other sigma c n Delta DeltaFinal X
        (Hneq : actor <> other)
        (Hupdates : RGIUpdateSteps (G actor) I actor sigma c n
          Delta DeltaFinal)
        (Hcore : RGICore (R actor) (G actor) I actor X
          sigma c DeltaFinal) :
      forall rank,
        RGISimulationRanked (R other) (G other) I other rank sigma c Delta ->
        exists rank', rank' <= rank /\
          RGISimulationRanked (R other) (G other) I other rank'
            sigma c DeltaFinal.
    Proof.
      induction Hupdates; intros rank Hsim.
      - exists rank. split; [lia|exact Hsim].
      - inversion Hsim as
          [rank0 sigma0 c0 Delta0 DeltaCore Hadmin0 Hcore0 Hstable0];
          subst.
        assert (HItarget : I (sigma, Delta')).
        { eapply rgi_updates_source_invariant; eauto. }
        assert (HRely : R other (sigma, Delta) (sigma, Delta')).
        { apply (HRG actor other Hneq). split; assumption. }
        destruct (Hstable0 _ _ HRely HItarget) as
          [rank1 [Hle1 Hsim1]].
        destruct (IHHupdates Hcore rank1 Hsim1) as
          [rank2 [Hle2 Hsim2]].
        exists rank2. split; [lia|exact Hsim2].
    Qed.

    Lemma rgisim_core_rank_zero R G I t sigma c Delta
        (Hcore : RGICore R G I t (RGISimulationRanked R G I t)
          sigma c Delta) :
      (forall rho pi, Delta rho pi ->
        ~ poss_steps (PossOk rho pi) PossError) ->
      RGISimulationRanked R G I t O sigma c Delta.
    Proof.
      intro Hnoerror.
      destruct Hcore as [rho pi HI Hposs Herr |
        Hinv Hret Hu Htau HI Hstable Hnoerr].
      - exfalso. eapply (Hnoerror rho pi Hposs); exact Herr.
      - econstructor; [constructor| |].
        + eapply RGICore_Continue; eauto.
        + intros sigma' Delta' HR HI'. exists O. split; [lia|].
          eapply Hstable; eauto.
    Qed.

    Lemma rgisim_local_cont_ranked :
      forall R G I t rank sigma Delta c c',
      TMap.find t c = TMap.find t c' ->
      RGISimulationRanked R G I t rank sigma c Delta ->
      RGISimulationRanked R G I t rank sigma c' Delta.
    Proof.
      intros R G I t. cofix CIH.
      intros rank sigma Delta c c' Hfind Hsim.
      inversion Hsim as
        [rank0 sigma0 c0 Delta0 DeltaCore Hadmin Hcore Hstable]; subst.
      econstructor.
      - eapply rgi_updates_local; eauto.
      - destruct Hcore as [rho pi HI Hposs Herr |
          Hinv Hret Hu Htau HI Hcorestable Hnoerror].
        + eapply RGICore_Error; eauto.
        + eapply RGICore_Continue.
          * intros f c1 Hstep.
            eapply invstep_local_determ with (c2 := c) in Hstep
              as [c2 [Hstep2 Hlocal]]; eauto.
            destruct (Hinv _ _ Hstep2) as [HG [Hnone [n Hnext]]].
            split; [exact HG|]. split; [exact Hnone|]. exists n.
            exact (CIH n sigma (ac_inv DeltaCore t f) c2 c1
              (eq_sym Hlocal) Hnext).
          * intros f ret c1 Hstep.
            eapply retstep_local_determ with (c2 := c) in Hstep
              as [c2 [Hstep2 Hlocal]]; eauto.
            destruct (Hret _ _ _ Hstep2) as [HG [Hlin [n Hnext]]].
            split; [exact HG|]. split; [exact Hlin|]. exists n.
            exact (CIH n sigma (ac_res DeltaCore t) c2 c1
              (eq_sym Hlocal) Hnext).
          * intros ev sigma' c1 Hstep.
            eapply ustep_local_determ with (c2 := c) in Hstep
              as [c2 [Hstep2 Hlocal]]; eauto.
            destruct (Hu _ _ _ Hstep2) as
              [Delta' [Hreach [HG [n Hnext]]]].
            exists Delta'. split; [exact Hreach|]. split; [exact HG|].
            exists n. exact (CIH n sigma' Delta' c2 c1
              (eq_sym Hlocal) Hnext).
          * intros c1 Hstep.
            eapply taustep_local_determ with (c2 := c) in Hstep
              as [c2 [Hstep2 Hlocal]]; eauto.
            destruct (Htau _ Hstep2) as [n Hnext]. exists n.
            exact (CIH n sigma DeltaCore c2 c1
              (eq_sym Hlocal) Hnext).
          * exact HI.
          * intros sigma' Delta' HR HI'.
            exact (CIH O sigma' Delta' c c' Hfind
              (Hcorestable sigma' Delta' HR HI')).
          * intros ev Herr.
            assert (Herr' : uerror (Build_ThreadEvent t ev) sigma c).
            { eapply uerror_local_determ; [exact Herr|].
              symmetry. exact Hfind. }
            exact (Hnoerror ev Herr').
      - intros sigma' Delta' HR HI'.
        destruct (Hstable _ _ HR HI') as [n [Hle Hnext]].
        exists n. split; [exact Hle|].
        exact (CIH n sigma' Delta' c c' Hfind Hnext).
    Qed.

    Definition ThreadSimulations (R G : tid -> RGRelation) I
        (sigma : State VE) (c : @ThreadPoolState E F)
        (Delta : AbstractConfig VF) : Prop :=
      forall t, exists rank,
        RGISimulationRanked (R t) (G t) I t rank sigma c Delta.

    Definition active_tids (c : @ThreadPoolState E F) : list tid :=
      map (@fst tid ThreadState) (TMap.elements c).

    Lemma inA_elements_key (t : tid) (ts : @ThreadState E F)
        (c : @ThreadPoolState E F) :
      SetoidList.InA (TMap.eq_key_elt (A := ThreadState))
        (pair t ts) (TMap.elements c) -> List.In t (active_tids c).
    Proof.
      intro Hin. apply SetoidList.InA_alt in Hin.
      destruct Hin as [[u v] [Heq Hin]].
      unfold TMap.eq_key_elt in Heq. simpl in Heq.
      destruct Heq as [Heq _]. change (t = u) in Heq. subst u.
      apply (in_map (@fst tid ThreadState)) in Hin. exact Hin.
    Qed.

    Lemma find_some_active (t : tid) (ts : @ThreadState E F)
        (c : @ThreadPoolState E F) :
      TMap.find t c = Some ts -> List.In t (active_tids c).
    Proof.
      intro Hfind. apply (inA_elements_key t ts), TMap.elements_1, TMap.find_2.
      exact Hfind.
    Qed.

    (** Normalization uses the active-thread list as its outer inductive
        measure and each selected thread's [RGIUpdateSteps] derivation as
        its inner structural measure.  The final clause states the key
        non-growth fact needed by the induction: rank-zero simulations not
        selected by this list remain rank zero. *)
    Lemma normalize_thread_list
        (R G : tid -> RGRelation) I
        (HRG : forall t1 t2, t1 <> t2 ->
          (I ⊓ G t1 ⊆ R t2)%RGRelation) :
      forall (threads : list tid) sigma c Delta,
      ThreadSimulations R G I sigma c Delta ->
      (exists DeltaError,
        TPSimulation.AbstractUpdateSteps Delta DeltaError /\ ErrorCore DeltaError) \/
      (exists DeltaFinal,
        TPSimulation.AbstractUpdateSteps Delta DeltaFinal /\
        ThreadSimulations R G I sigma c DeltaFinal /\
        (forall t, List.In t threads ->
          RGISimulationRanked (R t) (G t) I t O sigma c DeltaFinal) /\
        (forall t, ~ List.In t threads ->
          RGISimulationRanked (R t) (G t) I t O sigma c Delta ->
          RGISimulationRanked (R t) (G t) I t O sigma c DeltaFinal)).
    Proof.
      induction threads as [|actor threads IH];
        intros sigma c Delta Hthreads.
      - right. exists Delta. split; [constructor|].
        split; [exact Hthreads|]. split.
        + intros t Hin. inversion Hin.
        + intros t Hnin Hzero. exact Hzero.
      - destruct (Hthreads actor) as [rank Hactor].
        inversion Hactor as
          [rank0 sigma0 c0 Delta0 DeltaCore Hadmin Hcore Hstable]; subst.
        pose proof (rgi_updates_to_tpsim _ _ _ _ _ _ _ _ Hadmin) as Hprefix.
        pose proof Hcore as HcoreFull.
        destruct Hcore as [rho pi HI Hposs Herr |
          Hinv Hret Hu Htau HI Hcorestable Hnoerror].
        + left. exists DeltaCore. split; [exact Hprefix|].
          unfold ErrorCore. eauto.
        + assert (Hactor0 :
            RGISimulationRanked (R actor) (G actor) I actor O
              sigma c DeltaCore).
          { econstructor; [constructor| |].
            - exact HcoreFull.
            - intros sigma' Delta' HR HI'. exists O. split; [lia|].
              eapply Hcorestable; eauto. }
          assert (HthreadsCore : ThreadSimulations R G I sigma c DeltaCore).
          { intros other. destruct (Pos.eq_dec actor other) as [->|Hneq].
            - exists O. exact Hactor0.
            - destruct (Hthreads other) as [otherRank Hother].
              destruct (rgisim_follow_updates R G I HRG actor other
                sigma c rank Delta DeltaCore
                (RGISimulationRanked (R actor) (G actor) I actor)
                Hneq Hadmin HcoreFull
                otherRank Hother) as [otherRank' [Hle Hother']].
              exists otherRank'. exact Hother'. }
          destruct (IH sigma c DeltaCore HthreadsCore) as
            [[DeltaError [Hrest Herror]] |
             [DeltaFinal [Hrest [HthreadsFinal [Hzero Hpreserve]]]]].
          * left. exists DeltaError. split.
            -- eapply tpsim_updates_trans; eauto.
            -- exact Herror.
          * right. exists DeltaFinal. split.
            -- eapply tpsim_updates_trans; eauto.
            -- split; [exact HthreadsFinal|]. split.
               ++ intros t [Ht | Ht].
                  ** subst t.
                     destruct (classic (List.In actor threads)) as [Hin|Hnin].
                     --- apply Hzero. exact Hin.
                     --- apply Hpreserve; assumption.
                  ** apply Hzero. exact Ht.
               ++ intros t Hnotin HzeroStart.
                  assert (Hneq : actor <> t).
                  { intro Heq. subst. apply Hnotin. now left. }
                  destruct (rgisim_follow_updates R G I HRG actor t
                    sigma c rank Delta DeltaCore
                    (RGISimulationRanked (R actor) (G actor) I actor)
                    Hneq Hadmin HcoreFull
                    O HzeroStart) as [rank' [Hle HzeroCore]].
                  assert (rank' = O) by lia. subst rank'.
                  apply Hpreserve.
                  ** intro Hin. apply Hnotin. now right.
                  ** exact HzeroCore.
    Qed.

    Lemma normalize_active_threads
        (R G : tid -> RGRelation) I
        (HRG : forall t1 t2, t1 <> t2 ->
          (I ⊓ G t1 ⊆ R t2)%RGRelation)
        sigma c Delta :
      ThreadSimulations R G I sigma c Delta ->
      (exists DeltaError,
        TPSimulation.AbstractUpdateSteps Delta DeltaError /\ ErrorCore DeltaError) \/
      (exists DeltaFinal,
        TPSimulation.AbstractUpdateSteps Delta DeltaFinal /\
        ThreadSimulations R G I sigma c DeltaFinal /\
        forall t,
          RGISimulationRanked (R t) (G t) I t O sigma c DeltaFinal).
    Proof.
      intro Hthreads.
      destruct (normalize_thread_list R G I HRG (active_tids c)
        sigma c Delta Hthreads) as
        [[DeltaError [Hadmin Herror]] |
         [DeltaFinal [Hadmin [Hfinal [Hzero Hpreserve]]]]].
      - left. eauto.
      - right. exists DeltaFinal. repeat split; auto.
        intro t. destruct (Hfinal t) as [rank Hsim].
        destruct (TMap.find t c) eqn:Hfind.
        + apply Hzero. eapply find_some_active; eauto.
        + inversion Hsim as
            [rank0 sigma0 c0 Delta0 DeltaCore Hrank Hcore Hstable]; subst.
          destruct (rgi_updates_absent _ _ _ _ _ _ _ _ Hfind Hrank)
            as [-> Heq]. subst DeltaCore. exact Hsim.
    Qed.

    Lemma rgisim_rank_zero_core R G I t sigma c Delta :
      RGISimulationRanked R G I t O sigma c Delta ->
      RGICore R G I t (RGISimulationRanked R G I t) sigma c Delta.
    Proof.
      intro Hsim. inversion Hsim as
        [n sigma0 c0 Delta0 DeltaCore Hadmin Hcore Hstable]; subst.
      dependent destruction Hadmin. exact Hcore.
    Qed.

    Lemma rgisim_ranked_invariant R G I t rank sigma c Delta :
      RGISimulationRanked R G I t rank sigma c Delta -> I (sigma, Delta).
    Proof.
      intro Hsim. inversion Hsim as
        [n sigma0 c0 Delta0 DeltaCore Hadmin Hcore Hstable]; subst.
      eapply rgi_updates_source_invariant; eauto.
    Qed.

    Lemma rgisim_parapllel_composition :
      forall (R G : tid -> RGRelation) (I : Assertion)
        (HRG : forall t1 t2, t1 <> t2 ->
          (I ⊓ G t1 ⊆ R t2)%RGRelation),
      forall sigma c Delta,
        ThreadSimulations R G I sigma c Delta ->
        TPSimulation M sigma c Delta.
    Proof.
      intros R G I HRG. cofix CIH.
      intros sigma c Delta Hthreads.
      destruct (normalize_active_threads R G I HRG sigma c Delta Hthreads)
        as [[DeltaError [Hadmin Herror]] |
            [DeltaCore [Hadmin [HthreadsCore Hzero]]]].
      - eapply TPSimRoll with (Δ' := DeltaError).
        + exact Hadmin.
        + left. exact Herror.
      - destruct (classic (exists rho pi, DeltaCore rho pi /\
          poss_steps (PossOk rho pi) PossError)) as
          [[rho [pi [Hposs Herr]]] | Hnoerror].
        + eapply TPSimRoll with (Δ' := DeltaCore).
          * exact Hadmin.
          * left. unfold ErrorCore. eauto.
        + assert (Hnoterror : forall rho pi, DeltaCore rho pi ->
            ~ poss_steps (PossOk rho pi) PossError).
          { intros rho0 pi0 Hposs0 Herr0. apply Hnoerror.
            exists rho0, pi0. now split. }
          eapply TPSimRoll with (Δ' := DeltaCore).
          * exact Hadmin.
          * right. constructor.
          -- (* invocation *)
            intros actor f c' Hstep.
            pose proof (rgisim_rank_zero_core _ _ _ _ _ _ _
              (Hzero actor)) as HactorCore.
            destruct HactorCore as [rho pi HI Hposs Herr |
              Hinv Hret Hu Htau HI HactorStable HactorNoerror].
            { exfalso. eapply (Hnoterror rho pi Hposs); exact Herr. }
            destruct (Hinv _ _ Hstep) as [HGinv [Hnone [rank Hnext]]].
            eapply CIH. intros other.
            destruct (Pos.eq_dec actor other) as [->|Hneq].
            ++ exists rank. exact Hnext.
            ++ pose proof (rgisim_rank_zero_core _ _ _ _ _ _ _
                 (Hzero other)) as HotherCore.
               destruct HotherCore as [rho pi HIother Hposs Herr |
                 Oinv Oret Ou Otau HIother HotherStable HotherNoerror].
               { exfalso. eapply (Hnoterror rho pi Hposs); exact Herr. }
               assert (HRely : R other (sigma, DeltaCore)
                   (sigma, ac_inv DeltaCore actor f)).
               { apply (HRG actor other Hneq). split.
                 - apply HGinv. unfold Ginv, LiftRelation_Δ. simpl.
                   repeat split; auto.
                 - exact HI. }
               assert (HItarget : I (sigma, ac_inv DeltaCore actor f)).
               { eapply rgisim_ranked_invariant; exact Hnext. }
               pose proof (HotherStable _ _ HRely HItarget) as Hstable0.
               exists O. eapply rgisim_local_cont_ranked.
               ** eapply invstep_local_cont; eauto.
               ** exact Hstable0.
          -- (* return *)
            intros actor f ret c' Hstep.
            pose proof (rgisim_rank_zero_core _ _ _ _ _ _ _
              (Hzero actor)) as HactorCore.
            destruct HactorCore as [rho pi HI Hposs Herr |
              Hinv Hret Hu Htau HI HactorStable HactorNoerror].
            { exfalso. eapply (Hnoterror rho pi Hposs); exact Herr. }
            destruct (Hret _ _ _ Hstep) as [HGret [Hlin [rank Hnext]]].
            split; [exact Hlin|].
            eapply CIH. intros other.
            destruct (Pos.eq_dec actor other) as [->|Hneq].
            ++ exists rank. exact Hnext.
            ++ pose proof (rgisim_rank_zero_core _ _ _ _ _ _ _
                 (Hzero other)) as HotherCore.
               destruct HotherCore as [rho pi HIother Hposs Herr |
                 Oinv Oret Ou Otau HIother HotherStable HotherNoerror].
               { exfalso. eapply (Hnoterror rho pi Hposs); exact Herr. }
               assert (HRely : R other (sigma, DeltaCore)
                   (sigma, ac_res DeltaCore actor)).
               { apply (HRG actor other Hneq). split.
                 - apply HGret. unfold Gret, LiftRelation_Δ. simpl.
                   repeat split; auto.
                 - exact HI. }
               assert (HItarget : I (sigma, ac_res DeltaCore actor)).
               { eapply rgisim_ranked_invariant; exact Hnext. }
               pose proof (HotherStable _ _ HRely HItarget) as Hstable0.
               exists O. eapply rgisim_local_cont_ranked.
               ** eapply retstep_local_cont; eauto.
               ** exact Hstable0.
          -- (* visible library step *)
            intros tev sigma' c' Hstep. destruct tev as [actor ev].
            pose proof (rgisim_rank_zero_core _ _ _ _ _ _ _
              (Hzero actor)) as HactorCore.
            destruct HactorCore as [rho pi HI Hposs Herr |
              Hinv Hret Hu Htau HI HactorStable HactorNoerror].
            { exfalso. eapply (Hnoterror rho pi Hposs); exact Herr. }
            destruct (Hu _ _ _ Hstep) as
              [Delta' [Hreach [HG [rank Hnext]]]].
            exists Delta'. split; [exact Hreach|].
            eapply CIH. intros other.
            destruct (Pos.eq_dec actor other) as [->|Hneq].
            ++ exists rank. exact Hnext.
            ++ pose proof (rgisim_rank_zero_core _ _ _ _ _ _ _
                 (Hzero other)) as HotherCore.
               destruct HotherCore as [rho pi HIother Hposs Herr |
                 Oinv Oret Ou Otau HIother HotherStable HotherNoerror].
               { exfalso. eapply (Hnoterror rho pi Hposs); exact Herr. }
               assert (HRely : R other (sigma, DeltaCore) (sigma', Delta')).
               { apply (HRG actor other Hneq). split; assumption. }
               assert (HItarget : I (sigma', Delta')).
               { eapply rgisim_ranked_invariant; exact Hnext. }
               pose proof (HotherStable _ _ HRely HItarget) as Hstable0.
               exists O. eapply rgisim_local_cont_ranked.
               ** eapply ustep_local_cont; eauto.
               ** exact Hstable0.
          -- (* Tau *)
            intros actor c' Hstep.
            eapply CIH. intros other.
            pose proof (rgisim_rank_zero_core _ _ _ _ _ _ _
              (Hzero other)) as HotherCore.
            destruct HotherCore as [rho pi HI Hposs Herr |
              Hinv Hret Hu Htau HI Hstable Hnoerr].
            { exfalso. eapply (Hnoterror rho pi Hposs); exact Herr. }
            destruct (Pos.eq_dec actor other) as [->|Hneq].
            ++ destruct (Htau _ Hstep) as [rank Hnext].
               exists rank. exact Hnext.
            ++ exists O. eapply rgisim_local_cont_ranked.
               ** eapply taustep_local_cont; eauto.
               ** exact (Hzero other).
          -- (* no concrete error *)
            intros tev Herr. destruct tev as [actor ev].
            pose proof (rgisim_rank_zero_core _ _ _ _ _ _ _
              (Hzero actor)) as HactorCore.
            destruct HactorCore as [rho pi HI Hposs HabsErr |
              Hinv Hret Hu Htau HI Hstable Hnoerr].
            ++ exfalso. eapply (Hnoterror rho pi Hposs); exact HabsErr.
            ++ exact (Hnoerr ev Herr).
    Qed.

    Record ValidRGI (R G : @RGRelation _ _ VE VF) (I : Assertion) t : Prop := {
      HRinv : forall s s', R s s' -> I s' ->
        (forall rho pi, Δ s rho pi -> TMap.find t pi = None) <->
        (forall rho pi, Δ s' rho pi -> TMap.find t pi = None)
    }.

    (** Sequential composition preserves the method's exact abstract-update
        rank.  The absent-thread state has rank zero. *)
    Lemma msim_sequential_composition :
      forall (R G : RGRelation) (I : Assertion) t
      (Hrgi : ValidRGI R G I t)
      (Hmsim : forall f sigma Delta,
        (Ginv t f ⊚ I)%Assertion (sigma, Delta) ->
        (forall rho pi, Delta rho pi ->
          TMap.find t pi = Some (ls_inv f)) ->
        MethodSimulation R G I t f sigma (M f t) None Delta)
      sigma rho
      (Hinvariant : I (sigma, ac_init rho))
      (HGinv : forall f, (Ginv t f ⊆ G)%RGRelation)
      (HGid : forall s, G s s),
      RGISimulation R G I t sigma (@TMap.empty _) (ac_init rho).
    Proof.
      intros R0 G0 I0 t0 Hrgi Hmethods sigma0 rho0 HI HGinv HGid.
      exists O.
      eapply RGISimulation_coinduction_ranked with
        (X := fun n sigma c (Delta : AbstractConfig VF) =>
          (n = O /\
           (forall rho pi, Delta rho pi -> TMap.find t0 pi = None) /\
           TMap.find t0 c = None /\ I0 (sigma, Delta)) \/
          (exists f p b,
            TMap.find t0 c = Some (Build_ThreadState f p b) /\
            MethodSimulationRanked R0 G0 I0 t0 f n sigma p b Delta)).
      - intros n sigma c Delta Hstate.
        destruct Hstate as [[-> [Hnone [Hfindc Hinv]]] |
          [f0 [p0 [b0 [Hfindc Hmethod]]]]].
        + exists Delta. split; [constructor|]. split.
          * destruct (classic (exists rho pi, Delta rho pi /\
              poss_steps (PossOk rho pi) PossError)) as
              [[rho [pi [Hposs Herr]]] | Hnoerr].
            -- eapply RGICore_Error; eauto.
            -- eapply RGICore_Continue; intros.
               ++ inversion Hstep; subst. clear Hfind.
                  split; [exact (HGinv f)|]. split; [exact Hnone|].
                  destruct (Hmethods f sigma (ac_inv Delta t0 f)) as
                    [nm Hm].
                  ** exists (sigma, Delta). split; [exact Hinv|].
                     unfold Ginv, LiftRelation_Δ. simpl.
                     repeat split; auto.
                  ** inversion 1; subst. rewrite PositiveMap.gss. reflexivity.
                  ** exists nm. right. exists f, (M f t0), None. split.
                     --- rewrite PositiveMap.gss. reflexivity.
                     --- exact Hm.
               ++ inversion Hstep; subst; simpl in *; congruence.
               ++ inversion Hstep; subst; simpl in *; congruence.
               ++ inversion Hstep; subst; simpl in *; congruence.
               ++ exact Hinv.
               ++ left. repeat split; auto.
                  destruct Hrgi as [HRinv0].
                  apply (proj1 (HRinv0 _ _ H H0)); assumption.
               ++ intro Huerr. inversion Huerr; subst; simpl in *.
                  rewrite Hfindc in Hfind. congruence.
          * intros sigma' Delta' HR HI'. exists O. split; [lia|].
            left. repeat split; auto.
            destruct Hrgi as [HRinv0].
            apply (proj1 (HRinv0 _ _ HR HI')); assumption.
        + destruct Hmethod as
            [n sigma p b Delta DeltaCore Hadmin Hcore Hstable].
          exists DeltaCore. split.
          * eapply method_updates_to_rgi; eauto.
          * split.
            -- destruct Hcore as [rho pi Hinv Hposs Herr |
                 Hustep Hreturn Htau Hinv Hmethodcorestable Hnoerror].
               ++ eapply RGICore_Error; eauto.
               ++ eapply RGICore_Continue; intros.
                  ** inversion Hstep; subst; simpl in *; congruence.
                  ** inversion Hstep; subst.
                     rewrite Hfindc in Hfind. dependent destruction Hfind.
                     simpl in *.
                     specialize (Hreturn ret (conj eq_refl eq_refl))
                       as [HGret [HIret Hlin]].
                     split; [exact HGret|]. split; [exact Hlin|].
                     exists O. left. repeat split; auto.
                     --- inversion 1; subst. rewrite PositiveMap.grs.
                         reflexivity.
                     --- rewrite PositiveMap.grs. reflexivity.
                  ** inversion Hstep; subst. simpl in *.
                     rewrite Hfindc in Hfind. dependent destruction Hfind.
                     destruct (ts_step_inversion _ _ _ _ _ _ _ _ Hstep0)
                       as [ev0 [p' [b' Heq]]]. subst. simpl in *.
                     destruct (Hustep _ _ _ _ Hstep0) as
                       [Delta' [Hreach [HG [nm Hnext]]]].
                     exists Delta'. repeat split; auto.
                     exists nm. right. exists f0, p', b'. split.
                     --- rewrite PositiveMap.gss. reflexivity.
                     --- exact Hnext.
                  ** inversion Hstep; subst.
                     rewrite Hfindc in Hfind. dependent destruction Hfind.
                     inversion Hstep0; subst; simpl in *.
                     destruct (Htau _ _ Hstep0) as [nm Hnext].
                     exists nm. right. exists f0, p1, b. split.
                     --- rewrite PositiveMap.gss. reflexivity.
                     --- exact Hnext.
                  ** exact Hinv.
                  ** right. exists f0, p, b. split; [exact Hfindc|].
                     eapply Hmethodcorestable; eauto.
                  ** intro Huerr. inversion Huerr; subst. simpl in *.
                     inversion Herror; subst. simpl in *.
                     rewrite Hfindc in Hfind. dependent destruction Hfind.
                     eapply Hnoerror; eauto.
            -- intros sigma' Delta' HR HI'.
               destruct (Hstable _ _ HR HI') as [nm [Hle Hnext]].
               exists nm. split; [exact Hle|]. right.
               exists f0, p, b. split; [exact Hfindc|exact Hnext].
      - left. repeat split; auto.
        + inversion 1; subst. rewrite PositiveMap.gempty. reflexivity.
        + rewrite PositiveMap.gempty. reflexivity.
    Qed.

  End Simulations.
End RGISimulation.
