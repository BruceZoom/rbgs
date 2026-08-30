Require Import FMapPositive.
Require Import Coq.Program.Equality.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import Logics.
Require Import Assertion.
Require Import RGISimulationSet.
Require Import RGILogicSet.

(** A proof-engineering facade for using the set-of-possibilities logic while
    deliberately retaining exactly one abstract possibility.  This module is
    not a second program logic: it only embeds the old, convenient pointwise
    assertion language into [AssertionsSet]. *)
Module SingletonPossibility.
  Import Reg LinCCALBase LTSSpec Semantics Lang.

  Open Scope assertion_scope.

  Module Single := AssertionsSingle.
  Module Many := AssertionsSet.
  Module SingleState := SinglePossState.
  Module ManyState := SetPossState.
  Module SetRGI := RGISimulationSet.RGISimulation.
  Module SetLogic := RGILogicSet.RGILogic.

  Section SingletonView.
    Context {E F : Op.t} {VE : @LTS E} {VF : @LTS F}.

    Definition single_state := @SingleState.ProofState E F VE VF.
    Definition set_state := @ManyState.ProofState E F VE VF.
    Definition single_assertion := @Logics.Assertion single_state.
    Definition set_assertion := @Logics.Assertion set_state.
    Definition single_relation := @Single.A.RGRelation E F VE VF.
    Definition set_relation := @Many.A.RGRelation E F VE VF.

    (** [singleton_view x s] says that the set proof state [s] is merely the
        extensional singleton presentation of the pointwise proof state [x].
        Extensional equivalence is intentional: [ac_inv], [ac_res], and
        client-defined configurations need not be definitionally equal. *)
    Definition singleton_view (x : single_state) (s : set_state) : Prop :=
      ManyState.σ s = SingleState.σ x /\
      ac_equiv (ManyState.Δ s)
        (ac_singleton (SingleState.ρ x) (SingleState.π x)).

    Definition lift_assert (P : single_assertion) : set_assertion :=
      fun s => exists x, singleton_view x s /\ P x.

    Definition lift_relation (R : single_relation) : set_relation :=
      fun s s' => exists x x',
        singleton_view x s /\ singleton_view x' s' /\ R x x'.

    Lemma singleton_view_build (x : single_state) :
      singleton_view x
        (ManyState.Build_ProofStateSet _ _ _ _ (SingleState.σ x)
          (ac_singleton (SingleState.ρ x) (SingleState.π x))).
    Proof. split; [reflexivity|reflexivity]. Qed.

    Lemma singleton_view_member x s :
      singleton_view x s ->
      ManyState.Δ s (SingleState.ρ x) (SingleState.π x).
    Proof.
      intros [_ Heq]. apply Heq. constructor.
    Qed.

    Lemma singleton_view_unique x y s :
      singleton_view x s -> singleton_view y s -> x = y.
    Proof.
      intros [Hσx Hx] [Hσy Hy].
      destruct x as [σx ρx πx], y as [σy ρy πy], s as [σ Δ].
      simpl in *. subst σx σy.
      assert (Δ ρx πx) as Hmem by (apply Hx; constructor).
      apply Hy in Hmem. inversion Hmem; subst. reflexivity.
    Qed.

    Lemma singleton_view_inv x s t f :
      singleton_view x s ->
      singleton_view
        (SingleState.Build_ProofStateSingle _ _ _ _
          (SingleState.σ x) (SingleState.ρ x)
          (TMap.add t (ls_inv f) (SingleState.π x)))
        (ManyState.Build_ProofStateSet _ _ _ _
          (ManyState.σ s) (ac_inv (ManyState.Δ s) t f)).
    Proof.
      intros [Hσ HΔ]. split; simpl; auto.
      intros ρ π; split.
      - intros Hinv. inversion Hinv; subst.
        apply HΔ in Hposs. inversion Hposs; subst. constructor.
      - intros Hsingle. inversion Hsingle; subst.
        constructor. apply HΔ. constructor.
    Qed.

    Lemma singleton_view_res x s t :
      singleton_view x s ->
      singleton_view
        (SingleState.Build_ProofStateSingle _ _ _ _
          (SingleState.σ x) (SingleState.ρ x)
          (TMap.remove t (SingleState.π x)))
        (ManyState.Build_ProofStateSet _ _ _ _
          (ManyState.σ s) (ac_res (ManyState.Δ s) t)).
    Proof.
      intros [Hσ HΔ]. split; simpl; auto.
      intros ρ π; split.
      - intros Hres. inversion Hres; subst.
        apply HΔ in Hposs. inversion Hposs; subst. constructor.
      - intros Hsingle. inversion Hsingle; subst.
        constructor. apply HΔ. constructor.
    Qed.

    Lemma lift_impl (P Q : single_assertion) :
      (forall x, P x -> Q x) ->
      forall s, lift_assert P s -> lift_assert Q s.
    Proof. intros HPQ s [x [Hview HP]]; exists x; auto. Qed.

    Lemma lift_no_error ev (P : single_assertion) :
      (forall x, P x -> Single.A.ANoError ev x) ->
      forall s, lift_assert P s -> Many.A.ANoError ev s.
    Proof.
      intros Hsafe s [x [[Hσ _] HP]].
      unfold Single.A.ANoError, Many.A.ANoError in *.
      simpl in *. rewrite Hσ. auto.
    Qed.

    Lemma lift_stable (R : single_relation) (I P : single_assertion) :
      Single.A.Stable R I P ->
      Many.A.Stable (lift_relation R) (lift_assert I) (lift_assert P).
    Proof.
      unfold Single.A.Stable, Many.A.Stable,
        Single.A.ComposeA, Many.A.ComposeA.
      intros Hstable s [[pre [[x [Hviewx HP]] Hrel]] [y [Hviewy HI]]].
      destruct Hrel as (x0 & x' & Hview0 & Hview' & HR).
      assert (x = x0) by (eapply singleton_view_unique; eauto).
      assert (y = x') by (eapply singleton_view_unique; eauto).
      subst x0 y. exists x'. split; auto.
      eapply Hstable. split; [exists x; auto|exact HI].
    Qed.

    Lemma ac_singleton_subset_steps
        (s : set_state) (x x' : single_state) :
      singleton_view x s ->
      poss_steps (PossOk (SingleState.ρ x) (SingleState.π x))
                 (PossOk (SingleState.ρ x') (SingleState.π x')) ->
      (ac_singleton (SingleState.ρ x') (SingleState.π x')
        ⊆ ac_steps (ManyState.Δ s))%AbstractConfig.
    Proof.
      intros Hview Hsteps ρ π Hsingle. inversion Hsingle; subst.
      econstructor; eauto. eapply singleton_view_member; eauto.
    Qed.

    Lemma lift_pupdate (G : single_relation) ev (P Q : single_assertion) :
      Single.PUpdate G ev P Q ->
      Many.PUpdate (lift_relation G) ev (lift_assert P) (lift_assert Q).
    Proof.
      intros Hupd σ Δ [x [Hview HP]] σ' Hstep.
      destruct x as [σ0 ρ π]. unfold singleton_view in Hview; simpl in Hview.
      destruct Hview as [Hσ HΔ]. subst σ0.
      destruct (Hupd σ ρ π HP σ' Hstep)
        as (ρ' & π' & Hsteps & HQ & HG).
      exists (ac_singleton ρ' π'). split.
      - intros ρ0 π0 Hsingle. inversion Hsingle; subst.
        econstructor; eauto. apply HΔ. constructor.
      - split.
        + exists (SingleState.Build_ProofStateSingle _ _ _ _ σ' ρ' π').
          split; [apply singleton_view_build|exact HQ].
        + exists (SingleState.Build_ProofStateSingle _ _ _ _ σ ρ π),
            (SingleState.Build_ProofStateSingle _ _ _ _ σ' ρ' π').
          split.
          * split; simpl; [reflexivity|exact HΔ].
          * split; [apply singleton_view_build|exact HG].
    Qed.

    Lemma lift_pupdate_id (G : single_relation) (P Q : single_assertion) :
      Single.PUpdateId G P Q ->
      Many.PUpdateId (lift_relation G) (lift_assert P) (lift_assert Q).
    Proof.
      intros Hupd σ Δ [x [Hview HP]].
      destruct x as [σ0 ρ π]. unfold singleton_view in Hview; simpl in Hview.
      destruct Hview as [Hσ HΔ]. subst σ0.
      destruct (Hupd σ ρ π HP) as (ρ' & π' & Hsteps & HQ & HG).
      exists (ac_singleton ρ' π'). split.
      - intros ρ0 π0 Hsingle. inversion Hsingle; subst.
        econstructor; eauto. apply HΔ. constructor.
      - split.
        + exists (SingleState.Build_ProofStateSingle _ _ _ _ σ ρ' π').
          split; [apply singleton_view_build|exact HQ].
        + exists (SingleState.Build_ProofStateSingle _ _ _ _ σ ρ π),
            (SingleState.Build_ProofStateSingle _ _ _ _ σ ρ' π').
          split.
          * split; simpl; [reflexivity|exact HΔ].
          * split; [apply singleton_view_build|exact HG].
    Qed.

    Lemma singleton_view_all_find x s t :
      singleton_view x s ->
      ((forall ρ π, ManyState.Δ s ρ π -> TMap.find t π = None) <->
       TMap.find t (SingleState.π x) = None).
    Proof.
      intros Hview. split.
      - intros Hall. apply Hall with (ρ := SingleState.ρ x).
        eapply singleton_view_member; eauto.
      - intros Hfind ρ π Hposs.
        destruct Hview as [_ Heq]. apply Heq in Hposs.
        inversion Hposs; subst. exact Hfind.
    Qed.

    Lemma singleton_view_all_lin x s t ls :
      singleton_view x s ->
      TMap.find t (SingleState.π x) = Some ls ->
      forall ρ π, ManyState.Δ s ρ π -> TMap.find t π = Some ls.
    Proof.
      intros [_ Heq] Hfind ρ π Hposs. apply Heq in Hposs.
      inversion Hposs; subst. exact Hfind.
    Qed.

    Lemma set_ginv_to_single t f x s s' :
      singleton_view x s -> Many.Ginv t f s s' ->
      exists x', singleton_view x' s' /\ Single.Ginv t f x x'.
    Proof.
      intros Hview [Hσ [Hfind HΔ]].
      pose proof (singleton_view_inv x s t f Hview) as [_ Hinv].
      exists (SingleState.Build_ProofStateSingle _ _ _ _
        (SingleState.σ x) (SingleState.ρ x)
        (TMap.add t (ls_inv f) (SingleState.π x))).
      split.
      - split; simpl.
        + destruct Hview as [Hviewσ _]. congruence.
        + etransitivity; eauto.
      - unfold Single.Ginv, Single.LiftRelation_π. simpl.
        repeat split; auto.
        apply Hfind with (ρ := SingleState.ρ x).
        eapply singleton_view_member; eauto.
    Qed.

    Lemma set_gret_to_single t f ret x s s' :
      singleton_view x s -> Many.Gret t f ret s s' ->
      exists x', singleton_view x' s' /\ Single.Gret t f ret x x'.
    Proof.
      intros Hview [Hσ [Hfind HΔ]].
      pose proof (singleton_view_res x s t Hview) as [_ Hres].
      exists (SingleState.Build_ProofStateSingle _ _ _ _
        (SingleState.σ x) (SingleState.ρ x)
        (TMap.remove t (SingleState.π x))).
      split.
      - split; simpl.
        + destruct Hview as [Hviewσ _]. congruence.
        + etransitivity; eauto.
      - unfold Single.Gret, Single.LiftRelation_π. simpl.
        repeat split; auto.
        apply Hfind with (ρ := SingleState.ρ x).
        eapply singleton_view_member; eauto.
    Qed.

    Lemma lift_ginv_compose t f (I P : single_assertion) :
      (forall x, Single.A.ComposeA I (Single.Ginv t f) x -> P x) ->
      forall s, Many.A.ComposeA (lift_assert I) (Many.Ginv t f) s ->
        lift_assert P s.
    Proof.
      intros Himpl s [s0 [[x [Hview HI]] Hginv]].
      destruct (set_ginv_to_single t f x s0 s Hview Hginv)
        as [x' [Hview' Hginv']].
      exists x'. split; auto. apply Himpl.
      exists x. auto.
    Qed.

    Lemma lift_gret_compose t f ret (Q I : single_assertion) :
      (forall x, Single.A.ComposeA Q (Single.Gret t f ret) x -> I x) ->
      forall s, Many.A.ComposeA (lift_assert Q) (Many.Gret t f ret) s ->
        lift_assert I s.
    Proof.
      intros Himpl s [s0 [[x [Hview HQ]] Hgret]].
      destruct (set_gret_to_single t f ret x s0 s Hview Hgret)
        as [x' [Hview' Hgret']].
      exists x'. split; auto. apply Himpl.
      exists x. auto.
    Qed.

    Lemma lift_valid_rgi (R G : single_relation) (I : single_assertion) t :
      (forall x x', R x x' -> I x' ->
        TMap.find t (SingleState.π x) = None <->
        TMap.find t (SingleState.π x') = None) ->
      SetRGI.ValidRGI (lift_relation R) (lift_relation G) (lift_assert I) t.
    Proof.
      intros Hvalid. constructor.
      intros s s' Hrel HI.
      destruct Hrel as (x & x' & Hview & Hview' & HR).
      destruct HI as [y [Hviewy HI]].
      assert (y = x') by (eapply singleton_view_unique; eauto). subst y.
      rewrite (singleton_view_all_find x s t Hview).
      rewrite (singleton_view_all_find x' s' t Hview').
      eapply Hvalid; eauto.
    Qed.

    Lemma lift_parallel_compat
        (I : single_assertion)
        (R G : tid -> single_relation) t1 t2 :
      t1 <> t2 ->
      (forall x x',
        (G t1 x x' \/
         (Single.GINV t1 x x' \/ Single.GRET t1 x x') \/
         Single.A.GId x x') ->
        R t2 x x') ->
      forall s s',
        (lift_relation (G t1) s s' \/
         (Many.GINV t1 s s' \/ Many.GRET t1 s s') \/
         Many.A.GId s s') /\
        lift_assert I s ->
        lift_relation (R t2) s s'.
    Proof.
      intros Hneq Hcompat s s' [Hrel HI].
      destruct Hrel as [HG | [[Hinv | Hret] | Hid]].
      - destruct HG as (x & x' & Hview & Hview' & HG).
        exists x, x'. split; [exact Hview|]. split; [exact Hview'|].
        apply Hcompat. left; exact HG.
      - destruct HI as [x [Hview HI]]. destruct Hinv as [f Hinv].
        destruct (set_ginv_to_single t1 f x s s' Hview Hinv)
          as [x' [Hview' Hinv']].
        exists x, x'. split; [exact Hview|]. split; [exact Hview'|].
        apply Hcompat. right; left; left. exists f; exact Hinv'.
      - destruct HI as [x [Hview HI]].
        destruct Hret as [f [ret Hret]].
        destruct (set_gret_to_single t1 f ret x s s' Hview Hret)
          as [x' [Hview' Hret']].
        exists x, x'. split; [exact Hview|]. split; [exact Hview'|].
        apply Hcompat. right; left; right. exists f, ret; exact Hret'.
      - unfold Many.A.GId in Hid. subst s'.
        destruct HI as [x [Hview HI]]. exists x, x.
        split; [exact Hview|]. split; [exact Hview|].
        apply Hcompat. right; right; reflexivity.
    Qed.

    Lemma lift_initial (P : single_assertion) σ ρ π :
      P (SingleState.Build_ProofStateSingle _ _ _ _ σ ρ π) ->
      lift_assert P
        (ManyState.Build_ProofStateSet _ _ _ _ σ (ac_singleton ρ π)).
    Proof.
      intros HP.
      exists (SingleState.Build_ProofStateSingle _ _ _ _ σ ρ π).
      split; [apply singleton_view_build|exact HP].
    Qed.

    Lemma lift_post_lin (P : single_assertion) t ls :
      (forall x, P x -> TMap.find t (SingleState.π x) = Some ls) ->
      forall s, lift_assert P s ->
      forall ρ π, ManyState.Δ s ρ π -> TMap.find t π = Some ls.
    Proof.
      intros Hlin s [x [Hview HP]].
      eapply singleton_view_all_lin; [exact Hview|eapply Hlin; exact HP].
    Qed.

    Section SingletonProgramRules.
      Context (R G : single_relation) (I : single_assertion) (t : tid).

      (** Tactic-facing specialization of [SetLogic.provable_linstep].
          The singleton update is lifted into the set-of-possibilities logic;
          the concrete program is unchanged, so this rule introduces no
          [Tau] step. *)
      Lemma singleton_provable_linstep {A}
          (P P' : single_assertion) (Q : A -> single_assertion)
          (p : Prog E A) :
        (⊨ P' ==>> I) ->
        Single.A.Stable R I P' ->
        Single.PUpdateId G P P' ->
        SetLogic.HTripleProvable (lift_relation R) (lift_relation G)
          (lift_assert I) t (lift_assert P') p
          (fun a => lift_assert (Q a)) ->
        SetLogic.HTripleProvable (lift_relation R) (lift_relation G)
          (lift_assert I) t (lift_assert P) p
          (fun a => lift_assert (Q a)).
      Proof.
        intros Hinv Hstable Hupdate Hproof.
        eapply SetLogic.provable_linstep.
        - intros s HP. eapply lift_impl; [exact Hinv|exact HP].
        - apply lift_stable. exact Hstable.
        - apply lift_pupdate_id. exact Hupdate.
        - exact Hproof.
      Qed.

      (** Tactic-facing specialization of [SetLogic.provable_vis_safe].
          It changes only the leaf obligations to their pointwise form; the
          produced proof and its continuation both use [RGILogicSet]. *)
      Lemma singleton_provable_vis_safe {A}
          (P : single_assertion) (Q : A -> single_assertion)
          (m : Sig.op E) (k : Sig.ar m -> Prog E A)
          (P' : single_assertion) (Q' : Sig.ar m -> single_assertion) :
        (⊨ P ==>> Single.A.ANoError (Build_ThreadEvent t (InvEv m))) ->
        (⊨ P' ==>> I) ->
        (forall a, ⊨ Q' a ==>> I) ->
        Single.A.Stable R I P' ->
        (forall a, Single.A.Stable R I (Q' a)) ->
        Single.PUpdate G (Build_ThreadEvent t (InvEv m)) P P' ->
        (forall ret,
          Single.PUpdate G (Build_ThreadEvent t (ResEv m ret)) P' (Q' ret)) ->
        (forall ret,
          SetLogic.HTripleProvable (lift_relation R) (lift_relation G)
            (lift_assert I) t (lift_assert (Q' ret)) (k ret)
            (fun a => lift_assert (Q a))) ->
        SetLogic.HTripleProvable (lift_relation R) (lift_relation G)
          (lift_assert I) t (lift_assert P) (Vis m k)
          (fun a => lift_assert (Q a)).
      Proof.
        intros Herror HinvP HinvQ HstableP HstableQ Hpinv Hpret Hnext.
        eapply SetLogic.provable_vis_safe.
        - intros s HP. eapply lift_no_error; [exact Herror|exact HP].
        - intros s HP. eapply lift_impl; [exact HinvP|exact HP].
        - intros a s HQ. eapply lift_impl; [exact (HinvQ a)|exact HQ].
        - apply lift_stable; exact HstableP.
        - intros a. apply lift_stable; exact (HstableQ a).
        - apply lift_pupdate; exact Hpinv.
        - intros ret. apply lift_pupdate; exact (Hpret ret).
        - exact Hnext.
      Qed.

      (** Tactic-facing specialization of [SetLogic.provable_ret_safe]. *)
      Lemma singleton_provable_ret_safe {A}
          (a : A) (P : single_assertion) (Q : A -> single_assertion) :
        (⊨ P ==>> Q a) ->
        (⊨ Q a ==>> I) ->
        Single.A.Stable R I (Q a) ->
        SetLogic.HTripleProvable (lift_relation R) (lift_relation G)
          (lift_assert I) t (lift_assert P) (Ret a)
          (fun r => lift_assert (Q r)).
      Proof.
        intros HP Hinv Hstable.
        eapply SetLogic.provable_ret_safe.
        - intros s Hpre. eapply lift_impl; [exact HP|exact Hpre].
        - intros s Hpost. eapply lift_impl; [exact Hinv|exact Hpost].
        - apply lift_stable; exact Hstable.
      Qed.
    End SingletonProgramRules.

  End SingletonView.

  (** These tactics are the public entry points for the singleton-only leaf
      rules.  Structural rules (including framing and consequence) continue
      to be applied directly from [RGILogicSet]. *)
  Import AssertionsSingle.

  Tactic Notation "singleton_vis_safe" uconstr(Pp) uconstr(Qp) :=
    eapply singleton_provable_vis_safe with (P' := Pp) (Q' := Qp).

  Tactic Notation "singleton_linstep" uconstr(Pp) :=
    eapply singleton_provable_linstep with (P' := Pp).

  Tactic Notation "singleton_linstep" uconstr(Pp)
      "using" ident(stability_db) :=
    eapply singleton_provable_linstep with (P' := Pp);
    try solve_conj_impl;
    try solve_conj_stable stability_db.

  Tactic Notation "singleton_vis_safe" uconstr(Pp) uconstr(Qp)
      "using" ident(stability_db) :=
    eapply singleton_provable_vis_safe with (P' := Pp) (Q' := Qp);
    try solve_conj_impl;
    try solve_conj_stable stability_db.

  Tactic Notation "singleton_ret_safe" :=
    eapply singleton_provable_ret_safe.

  Tactic Notation "singleton_ret_safe" "using" ident(stability_db) :=
    eapply singleton_provable_ret_safe;
    try solve_conj_impl;
    try solve_conj_stable stability_db.
End SingletonPossibility.
