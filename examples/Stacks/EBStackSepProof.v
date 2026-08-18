Require Import FMapPositive.
Require Import Coq.Program.Equality.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import Logics.
Require Import SeparationAlgebra.
Require Import Assertion.
Require Import TPSimulationSet.
Require Import RGILogicSet.
Require Import SingletonPossibility.
Require Import examples.Common.AtomicLTS.
Require Import examples.Stacks.StackSpec.
Require Import examples.Exchanger.ExchangerSpec.
Require Import examples.Stacks.EBStackSep.

(** The set-of-possibilities proof.  All assertions below are the singleton
    embedding of the spatial assertions in [EBStackSep]; the program logic
    and its structural rules are those of [RGILogicSet]. *)
Module EBStackSepSetProof.
  Import Reg LinCCALBase LTSSpec Lang Semantics.
  Import AssertionsSingle SingletonPossibility.
  Import TPSimulationSet.TPSimulation.
  Import AtomicLTS TryStackSpec ExchSpec StackSpec.
  Import (coercions, canonicals, notations) Sig.
  Import (notations) LinCCAL.
  Module SetLogic := RGILogicSet.RGILogic.
  Import SetLogic.

  Open Scope prog_scope.
  Open Scope assertion_scope.
  Open Scope rg_relation_scope.

  Section Proof.
    Context {A : Type}.

    Definition ETryStackLayer : layer_interface :=
      {| li_sig := ETryStack A; li_lts := VTryStack; li_init := Idle nil |}.

    Definition EExchangerLayer : layer_interface :=
      {| li_sig := EExch (option A); li_lts := VExch; li_init := ExSIdle |}.

    Definition E : layer_interface := ETryStackLayer ⊗ₗ EExchangerLayer.

    Definition F : layer_interface :=
      {| li_sig := EStack A; li_lts := VStack; li_init := Idle nil |}.
    Definition push_impl := @EBStackSep.push_impl A.
    Definition pop_impl := @EBStackSep.pop_impl A.

    Definition SI := lift_assert (@EBStackSep.I A).
    Definition SActive t m := lift_assert (@EBStackSep.Active A t m).
    Definition SCompleted t m ret :=
      lift_assert (@EBStackSep.Completed A t m ret).
    Definition SPending t m := lift_assert (@EBStackSep.Pending A t m).
    Definition SReady t v := lift_assert (@EBStackSep.ExchangeReady A t v).

    Definition ExchangePost (t : tid) (v : option A)
        (other : option (option A)) :=
      match v, other with
      | Some a, Some None => @EBStackSep.Completed A t (StackSpec.push a) tt
      | None, Some (Some a) =>
          @EBStackSep.Completed A t StackSpec.pop (Some a)
      | _, _ => @EBStackSep.Active A t (EBStackSep.op_of v)
      end.

    Definition source_R_facts (t : tid) :
        @AssertionsSingle.A.RGRelation _ _ (li_lts E) (li_lts F) :=
      fun s s' =>
        (TMap.find t (SinglePossState.π s) = None <->
         TMap.find t (SinglePossState.π s') = None) /\
        ((@EBStackSep.I A s') ->
          forall ls, @EBStackSep.Exposed A t ls s ->
            @EBStackSep.Exposed A t ls s') /\
        ((@EBStackSep.I A s') ->
          forall m, @EBStackSep.Pending A t m s ->
            @EBStackSep.Pending A t m s') /\
        ((@EBStackSep.I A s') ->
          forall v, @EBStackSep.ExchangeReady A t v s ->
            @EBStackSep.ExchangeReady A t v s').

    Definition single_state :=
      @SinglePossState.ProofStateSingle _ _ (li_lts E) (li_lts F).

    Local Existing Instance EBStackSep.proof_Join.
    Local Existing Instance EBStackSep.proof_SA.
    Local Existing Instance EBStackSep.proof_unit.

    Definition stack_part
        (ts : State (@TryStackSpec.VTryStack A)) : single_state :=
      @SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
        (pair ts EBStackSep.exch_empty) (Idle (state ts))
        (@TMap.empty (@LinState (li_sig F))).

    Definition required_map
        (xs : @EExchState (option A)) : tmap (@LinState (li_sig F)) :=
      match xs with
      | ExSOffered t v =>
          TMap.add t (EBStackSep.offered_token v)
            (@TMap.empty (@LinState (li_sig F)))
      | ExSPaired t1 (Some a) _ None =>
          TMap.add t1 (EBStackSep.done_token (Some a) None)
            (@TMap.empty (@LinState (li_sig F)))
      | ExSPaired t1 None _ (Some a) =>
          TMap.add t1 (EBStackSep.done_token None (Some a))
            (@TMap.empty (@LinState (li_sig F)))
      | ExSPaired t1 v1 _ _ =>
          TMap.add t1 (EBStackSep.offered_token v1)
            (@TMap.empty (@LinState (li_sig F)))
      | _ => @TMap.empty (@LinState (li_sig F))
      end.

    Definition map_residual
        (xs : @EExchState (option A))
        (pi : tmap (@LinState (li_sig F))) :=
      match EBStackSep.required_owner xs with
      | Some t => EBStackSep.lin_residual t pi
      | None => pi
      end.

    Definition exch_part (xs : @EExchState (option A)) : single_state :=
      @SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
        (pair EBStackSep.try_empty xs) EBStackSep.stack_empty
        (required_map xs).

    Definition maps_part (xs : @EExchState (option A))
        (pi : tmap (@LinState (li_sig F))) : single_state :=
      @SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
        (pair EBStackSep.try_empty EBStackSep.exch_empty)
        EBStackSep.stack_empty (map_residual xs pi).

    Definition shared_part
        (ts : State (@TryStackSpec.VTryStack A))
        (xs : @EExchState (option A)) : single_state :=
      @SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
        (pair ts xs) (Idle (state ts)) (required_map xs).

    Lemma required_map_residual_join xs pi :
      EBStackSep.required_ok xs pi ->
      @join _ tmap_Join
        (required_map xs) (map_residual xs pi) pi.
    Proof.
      destruct xs as [t v|t1 v1 t2 v2|t1 v1 t2 v2|];
        try destruct v1; try destruct v2; simpl; intro Hreq.
      all: try solve
        [apply EBStackSep.lin_cell_join_residual; exact Hreq].
      all: exact (@unit_join_left _ tmap_Join tmap_SA tmap_unit pi).
    Qed.

    Lemma stack_exch_join ts xs :
      @join _ EBStackSep.proof_Join
        (stack_part ts) (exch_part xs) (shared_part ts xs).
    Proof. unfold stack_part, exch_part, shared_part; simpl.
      repeat split; constructor.
    Qed.

    Lemma shared_maps_join ts xs pi :
      EBStackSep.required_ok xs pi ->
      @join _ EBStackSep.proof_Join
        (shared_part ts xs) (maps_part xs pi)
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair ts xs) (Idle (state ts)) pi).
    Proof.
      intro Hreq. unfold shared_part, maps_part; simpl.
      repeat split; try constructor.
      apply required_map_residual_join; exact Hreq.
    Qed.

    Inductive ExchangerEffect (actor : tid) :
        @EExchState (option A) -> @EExchState (option A) -> Prop :=
    | xe_id xs : ExchangerEffect actor xs xs
    | xe_offer v : ExchangerEffect actor ExSIdle (ExSOffered actor v)
    | xe_pair offerer v1 v2 : offerer <> actor ->
        ExchangerEffect actor (ExSOffered offerer v1)
          (ExSPaired offerer v1 actor v2)
    | xe_revoke v : ExchangerEffect actor (ExSOffered actor v) ExSIdle
    | xe_accept accepter v1 v2 :
        ExchangerEffect actor (ExSPaired actor v1 accepter v2)
          (ExSAccepted actor v1 accepter v2)
    | xe_finish offerer v1 v2 :
        ExchangerEffect actor (ExSAccepted offerer v1 actor v2) ExSIdle.

    Definition StackRelation :
        @AssertionsSingle.A.RGRelation _ _ (li_lts E) (li_lts F) :=
      fun s s' => exists ts ts', s = stack_part ts /\ s' = stack_part ts'.

    Definition ExchangerGuarantee (actor : tid) :
        @AssertionsSingle.A.RGRelation _ _ (li_lts E) (li_lts F) :=
      fun s s' => exists xs xs', s = exch_part xs /\ s' = exch_part xs' /\
        ExchangerEffect actor xs xs'.

    Definition MapsGuarantee (actor : tid) :
        @AssertionsSingle.A.RGRelation _ _ (li_lts E) (li_lts F) :=
      fun s s' => exists xs pi xs' pi',
        s = maps_part xs pi /\ s' = maps_part xs' pi' /\
        forall q, q <> actor ->
          TMap.find q (map_residual xs pi) =
          TMap.find q (map_residual xs' pi').

    (** The guarantee records the small ownership effect performed by one
        atomic implementation step.  It deliberately does not quantify over
        every other thread's rely: that implication is proved once below. *)
    Inductive GuaranteeEffect (actor : tid) :
        single_state -> single_state -> Prop :=
    | ge_local (s s' : single_state) :
        snd (SinglePossState.σ s) = snd (SinglePossState.σ s') ->
        (forall q, q <> actor ->
          TMap.find q (SinglePossState.π s) =
          TMap.find q (SinglePossState.π s')) ->
        GuaranteeEffect actor s s'
    | ge_offer ts rho pi v :
        GuaranteeEffect actor
          (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
            (pair ts ExSIdle) rho pi)
          (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
            (pair ts (ExSOffered actor v)) rho pi)
    | ge_pair_same offerer v1 v2 ts pi :
        offerer <> actor -> ~ EBStackSep.complementary v1 v2 ->
        EBStackSep.required_ok (ExSOffered offerer v1) pi ->
        GuaranteeEffect actor
          (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
            (pair ts (ExSOffered offerer v1)) (Idle (state ts)) pi)
          (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
            (pair ts (ExSPaired offerer v1 actor v2)) (Idle (state ts)) pi)
    | ge_pair_comp offerer v1 v2 ts pi pi' :
        offerer <> actor -> EBStackSep.complementary v1 v2 ->
        EBStackSep.required_ok (ExSOffered offerer v1) pi ->
        EBStackSep.required_ok (ExSPaired offerer v1 actor v2) pi' ->
        (forall q, q <> offerer -> q <> actor ->
          TMap.find q pi = TMap.find q pi') ->
        GuaranteeEffect actor
          (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
            (pair ts (ExSOffered offerer v1)) (Idle (state ts)) pi)
          (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
            (pair ts (ExSPaired offerer v1 actor v2)) (Idle (state ts)) pi')
    | ge_revoke ts rho pi v :
        GuaranteeEffect actor
          (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
            (pair ts (ExSOffered actor v)) rho pi)
          (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
            (pair ts ExSIdle) rho pi)
    | ge_accept accepter v1 v2 ts rho pi :
        GuaranteeEffect actor
          (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
            (pair ts (ExSPaired actor v1 accepter v2)) rho pi)
          (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
            (pair ts (ExSAccepted actor v1 accepter v2)) rho pi)
    | ge_finish offerer v1 v2 ts rho pi :
        GuaranteeEffect actor
          (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
            (pair ts (ExSAccepted offerer v1 actor v2)) rho pi)
          (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
            (pair ts ExSIdle) rho pi).

    Inductive source_G_effect (actor : tid) :
        @AssertionsSingle.A.RGRelation _ _ (li_lts E) (li_lts F) :=
    | guarantee_step s s' :
        @EBStackSep.I A s -> @EBStackSep.I A s' ->
        ExchangerEffect actor (snd (SinglePossState.σ s))
          (snd (SinglePossState.σ s')) ->
        (forall q, q <> actor ->
          TMap.find q
              (map_residual (snd (SinglePossState.σ s))
                (SinglePossState.π s)) =
          TMap.find q
              (map_residual (snd (SinglePossState.σ s'))
                (SinglePossState.π s'))) ->
        source_G_effect actor s s'.

    Definition spatial_G (actor : tid) :
        @AssertionsSingle.A.RGRelation _ _ (li_lts E) (li_lts F) :=
      AssertionsSingle.A.RelSep3
        StackRelation (ExchangerGuarantee actor) (MapsGuarantee actor).

    Lemma spatial_G_intro actor ts xs pi ts' xs' pi' :
      EBStackSep.required_ok xs pi ->
      EBStackSep.required_ok xs' pi' ->
      ExchangerEffect actor xs xs' ->
      (forall q, q <> actor ->
        TMap.find q (map_residual xs pi) =
        TMap.find q (map_residual xs' pi')) ->
      spatial_G actor
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair ts xs) (Idle (state ts)) pi)
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair ts' xs') (Idle (state ts')) pi').
    Proof.
      intros Hreq Hreq' Hexch Hmaps. unfold spatial_G.
      eapply AssertionsSingle.A.RelSep3_intro with
        (s1 := stack_part ts) (s2 := exch_part xs)
        (s12 := shared_part ts xs) (s3 := maps_part xs pi)
        (s1' := stack_part ts') (s2' := exch_part xs')
        (s12' := shared_part ts' xs') (s3' := maps_part xs' pi').
      - apply stack_exch_join.
      - apply shared_maps_join; exact Hreq.
      - apply stack_exch_join.
      - apply shared_maps_join; exact Hreq'.
      - exists ts, ts'. auto.
      - exists xs, xs'. repeat split; auto.
      - exists xs, pi, xs', pi'. repeat split; auto.
    Qed.

    Lemma map_residual_same xs pi pi' q :
      TMap.find q pi = TMap.find q pi' ->
      TMap.find q (map_residual xs pi) =
        TMap.find q (map_residual xs pi').
    Proof.
      intro Hfind.
      unfold map_residual. destruct (EBStackSep.required_owner xs) as [r|].
      - destruct (PositiveMap.E.eq_dec r q) as [->|Hneq].
        + repeat rewrite EBStackSep.lin_residual_find_none. reflexivity.
        + repeat rewrite EBStackSep.lin_residual_find_other by congruence.
          exact Hfind.
      - exact Hfind.
    Qed.

    Lemma guarantee_effect_exchanger actor s s' :
      GuaranteeEffect actor s s' ->
      ExchangerEffect actor (snd (SinglePossState.σ s))
        (snd (SinglePossState.σ s')).
    Proof.
      intros H. destruct H; simpl in *.
      - rewrite H. constructor.
      - constructor.
      - constructor; assumption.
      - constructor; assumption.
      - constructor.
      - constructor.
      - constructor.
    Qed.

    Lemma guarantee_effect_maps actor s s' :
      GuaranteeEffect actor s s' -> forall q, q <> actor ->
      TMap.find q
          (map_residual (snd (SinglePossState.σ s))
            (SinglePossState.π s)) =
      TMap.find q
          (map_residual (snd (SinglePossState.σ s'))
            (SinglePossState.π s')).
    Proof.
      intros Heffect.
      destruct Heffect as
        [s0 s1 Hexch Hkeep
        |ts rho pi v
        |offerer v1 v2 ts pi Hdistinct Hsame Hoffer
        |offerer v1 v2 ts pi pi' Hdistinct Hcomp Hoffer Hpaired Hkeep
        |ts rho pi v
        |accepter v1 v2 ts rho pi
        |offerer v1 v2 ts rho pi]; intros q Hactor; simpl in *.
      - rewrite Hexch. apply map_residual_same. apply Hkeep; exact Hactor.
      - unfold map_residual; simpl.
        rewrite EBStackSep.lin_residual_find_other by congruence.
        reflexivity.
      - destruct v1, v2; simpl in *; try contradiction; reflexivity.
      - unfold map_residual; simpl.
        destruct v1, v2; simpl in *; try contradiction.
        all: destruct (PositiveMap.E.eq_dec offerer q) as [->|Hofferer].
        all: try solve
          [repeat rewrite EBStackSep.lin_residual_find_none; reflexivity].
        all: repeat rewrite EBStackSep.lin_residual_find_other by congruence;
          apply Hkeep; congruence.
      - unfold map_residual; simpl.
        rewrite EBStackSep.lin_residual_find_other by congruence.
        reflexivity.
      - unfold map_residual; simpl.
        destruct v1, v2; simpl;
          rewrite EBStackSep.lin_residual_find_other by congruence;
          reflexivity.
      - reflexivity.
    Qed.

    Lemma guarantee_effect_spatial actor s s' :
      @EBStackSep.I A s -> @EBStackSep.I A s' ->
      GuaranteeEffect actor s s' -> spatial_G actor s s'.
    Proof.
      intros HI HI' Heffect.
      destruct s as [[ts xs] rho pi], s' as [[ts' xs'] rho' pi'].
      destruct (EBStackSep.I_observe _ HI)
        as [tso [xso [Eσ [Eρ Hreq]]]].
      destruct (EBStackSep.I_observe _ HI')
        as [tso' [xso' [Eσ' [Eρ' Hreq']]]].
      simpl in *. inversion Eσ; inversion Eσ'; subst.
      eapply spatial_G_intro.
      - exact Hreq.
      - exact Hreq'.
      - pose proof (guarantee_effect_exchanger actor _ _ Heffect) as HX.
        simpl in HX. exact HX.
      - intros q Hq.
        pose proof (guarantee_effect_maps actor _ _ Heffect q Hq) as HM.
        simpl in HM. exact HM.
    Qed.

    Definition source_G actor :=
      AssertionsSingle.A.GuaranteeWithFootprint
        (source_G_effect actor) (spatial_G actor).

    (** Program interference is generated directly from the guarantees of
        the other threads; generic invocation/return steps form the second
        administrative branch. *)
    Definition source_R t :=
      AssertionsSingle.GuaranteeGeneratedRely source_G t.

    Lemma source_G_step actor s s' :
      @EBStackSep.I A s -> @EBStackSep.I A s' ->
      GuaranteeEffect actor s s' -> source_G actor s s'.
    Proof.
      intros HI HI' Heffect.
      apply AssertionsSingle.A.GuaranteeWithFootprint_intro.
      - constructor.
        + exact HI.
        + exact HI'.
        + eapply guarantee_effect_exchanger; exact Heffect.
        + eapply guarantee_effect_maps; exact Heffect.
      - eapply guarantee_effect_spatial; eauto.
    Qed.

    Definition R t := lift_relation (source_R t).
    Definition G t := lift_relation (source_G t).

    Lemma source_R_observer_view_facts t :
      AssertionsSingle.A.Subset
        (AssertionsSingle.ObserverViewEq t) (source_R_facts t).
    Proof.
      intros s s' [Hsigma [_ Hmap]].
      unfold source_R_facts. repeat split.
      - rewrite Hmap; auto.
      - rewrite Hmap; auto.
      - intros HI ls Hexp. eapply (@EBStackSep.preserve_exposed
          A t ls s s'); eauto using f_equal.
      - intros HI op Hpending.
        eapply EBStackSep.preserve_pending;
          [exact HI|exact (f_equal snd Hsigma)| |exact Hpending].
        intros ls Hexp. eapply (@EBStackSep.preserve_exposed
          A t ls s s'); eauto using f_equal.
      - intros HI v Hready.
        eapply EBStackSep.preserve_exchange_ready;
          [exact HI|exact (f_equal snd Hsigma)| |exact Hready].
        intros ls Hexp. eapply (@EBStackSep.preserve_exposed
          A t ls s s'); eauto using f_equal.
    Qed.

    Lemma exchanger_effect_other_owner actor xs xs' q :
      actor <> q -> ExchangerEffect actor xs xs' ->
      (EBStackSep.required_owner xs = Some q <->
       EBStackSep.required_owner xs' = Some q).
    Proof.
      intros Hneq Heffect. destruct Heffect; simpl.
      - tauto.
      - split; intro H; [discriminate|congruence].
      - destruct v1, v2; simpl; tauto.
      - split; intro H; [congruence|discriminate].
      - destruct v1, v2; simpl; split; intro H;
          try discriminate; congruence.
      - split; discriminate.
    Qed.

    Lemma map_residual_find_other_owner xs pi q :
      EBStackSep.required_owner xs <> Some q ->
      TMap.find q (map_residual xs pi) = TMap.find q pi.
    Proof.
      intro Howner. unfold map_residual.
      destruct (EBStackSep.required_owner xs) as [r|] eqn:Eowner;
        [|reflexivity].
      rewrite EBStackSep.lin_residual_find_other; [reflexivity|congruence].
    Qed.

    Lemma required_owner_find_some
        (xs : @EExchState (option A))
        (pi : tmap (@LinState (li_sig F))) q :
      EBStackSep.required_ok xs pi ->
      EBStackSep.required_owner xs = Some q ->
      exists ls, TMap.find q pi = Some ls.
    Proof.
      destruct xs as [t v|t1 v1 t2 v2|t1 v1 t2 v2|];
        try destruct v1; try destruct v2; simpl; intros Hreq Howner;
        try discriminate; inversion Howner; subst; eauto.
    Qed.

    Lemma exchanger_effect_other_find_none actor q xs xs' pi pi' :
      actor <> q -> ExchangerEffect actor xs xs' ->
      EBStackSep.required_ok xs pi -> EBStackSep.required_ok xs' pi' ->
      TMap.find q (map_residual xs pi) =
        TMap.find q (map_residual xs' pi') ->
      (TMap.find q pi = None <-> TMap.find q pi' = None).
    Proof.
      intros Hneq Heffect Hreq Hreq' Hmaps.
      eapply AssertionsSingle.owned_residual_find_none_iff
        with (owner := EBStackSep.required_owner)
             (residual := map_residual)
             (owner_ok := EBStackSep.required_ok).
      - apply map_residual_find_other_owner.
      - apply required_owner_find_some.
      - eapply exchanger_effect_other_owner; eauto.
      - exact Hreq.
      - exact Hreq'.
      - exact Hmaps.
    Qed.

    Lemma exchanger_effect_other_find actor q xs xs' pi pi' :
      actor <> q -> ExchangerEffect actor xs xs' ->
      EBStackSep.required_owner xs <> Some q ->
      TMap.find q (map_residual xs pi) =
        TMap.find q (map_residual xs' pi') ->
      TMap.find q pi = TMap.find q pi'.
    Proof.
      intros Hneq Heffect Howner Hmaps.
      eapply AssertionsSingle.owned_residual_find
        with (owner := EBStackSep.required_owner)
             (residual := map_residual).
      - apply map_residual_find_other_owner.
      - eapply exchanger_effect_other_owner; eauto.
      - exact Howner.
      - exact Hmaps.
    Qed.

    Lemma exchanger_effect_preserves_other_fact actor q xs xs' m :
      actor <> q -> ExchangerEffect actor xs xs' ->
      EBStackSep.in_exchanger_fact q m xs ->
      EBStackSep.in_exchanger_fact q m xs'.
    Proof.
      intros Hneq Heffect Hfact. destruct Heffect.
      - exact Hfact.
      - simpl in Hfact. contradiction.
      - destruct v1, v2; simpl in *; destruct Hfact; split; congruence.
      - simpl in Hfact. destruct Hfact; congruence.
      - destruct v1, v2; simpl in Hfact; destruct Hfact; congruence.
      - simpl in Hfact. contradiction.
    Qed.

    Lemma exchanger_effect_preserves_other_exposed actor q s s' ls :
      actor <> q -> @EBStackSep.I A s -> @EBStackSep.I A s' ->
      ExchangerEffect actor (snd (SinglePossState.σ s))
        (snd (SinglePossState.σ s')) ->
      TMap.find q
          (map_residual (snd (SinglePossState.σ s))
            (SinglePossState.π s)) =
      TMap.find q
          (map_residual (snd (SinglePossState.σ s'))
            (SinglePossState.π s')) ->
      @EBStackSep.Exposed A q ls s -> @EBStackSep.Exposed A q ls s'.
    Proof.
      intros Hneq HI HI' Heffect Hmaps Hexp.
      eapply EBStackSep.I_ALin_exposes.
      - exact HI'.
      - unfold AssertionsSingle.ALin.
        assert (Howner : EBStackSep.required_owner
          (snd (SinglePossState.σ s)) <> Some q).
        { eapply EBStackSep.Exposed_owner_distinct; exact Hexp. }
        pose proof (exchanger_effect_other_find actor q
          (snd (SinglePossState.σ s)) (snd (SinglePossState.σ s'))
          (SinglePossState.π s) (SinglePossState.π s') Hneq Heffect
          Howner Hmaps) as Hfull.
        transitivity (TMap.find q (SinglePossState.π s)).
        + symmetry; exact Hfull.
        + eapply EBStackSep.Exposed_ALin; exact Hexp.
      - intro Hpost.
        pose proof (EBStackSep.Exposed_owner_distinct q ls s Hexp) as Hpre.
        apply Hpre. apply (proj2 (exchanger_effect_other_owner actor
          (snd (SinglePossState.σ s)) (snd (SinglePossState.σ s')) q
          Hneq Heffect)). exact Hpost.
    Qed.

    Lemma exchanger_effect_preserves_other_pending actor q s s' m :
      actor <> q -> @EBStackSep.I A s -> @EBStackSep.I A s' ->
      ExchangerEffect actor (snd (SinglePossState.σ s))
        (snd (SinglePossState.σ s')) ->
      TMap.find q
          (map_residual (snd (SinglePossState.σ s))
            (SinglePossState.π s)) =
      TMap.find q
          (map_residual (snd (SinglePossState.σ s'))
            (SinglePossState.π s')) ->
      @EBStackSep.Pending A q m s -> @EBStackSep.Pending A q m s'.
    Proof.
      intros Hneq HI HI' Heffect Hmaps Hpending.
      destruct (EBStackSep.Pending_cases q m s Hpending)
        as [[_ Hfact] | [Hactive | [ret Hcompleted]]].
      - eapply EBStackSep.I_inexchanger_pending; [exact HI'|].
        eapply exchanger_effect_preserves_other_fact; eauto.
      - apply EBStackSep.Active_entails_Pending.
        eapply exchanger_effect_preserves_other_exposed;
          [exact Hneq|exact HI|exact HI'|exact Heffect|exact Hmaps|exact Hactive].
      - eapply EBStackSep.Completed_entails_Pending.
        eapply exchanger_effect_preserves_other_exposed;
          [exact Hneq|exact HI|exact HI'|exact Heffect|exact Hmaps|
           exact Hcompleted].
    Qed.

    Lemma exchanger_effect_preserves_other_ready actor q s s' v :
      actor <> q -> @EBStackSep.I A s -> @EBStackSep.I A s' ->
      ExchangerEffect actor (snd (SinglePossState.σ s))
        (snd (SinglePossState.σ s')) ->
      TMap.find q
          (map_residual (snd (SinglePossState.σ s))
            (SinglePossState.π s)) =
      TMap.find q
          (map_residual (snd (SinglePossState.σ s'))
            (SinglePossState.π s')) ->
      @EBStackSep.ExchangeReady A q v s ->
      @EBStackSep.ExchangeReady A q v s'.
    Proof.
      intros Hneq HI HI' Heffect Hmaps Hready.
      dependent destruction Heffect.
      - eapply (@EBStackSep.preserve_exchange_ready A q v s s').
        + exact HI'.
        + exact x.
        + intros ls Hexp. eapply exchanger_effect_preserves_other_exposed.
          * exact Hneq.
          * exact HI.
          * exact HI'.
          * rewrite x. constructor.
          * exact Hmaps.
          * exact Hexp.
        + exact Hready.
      - inversion Hready; subst; simpl in *; congruence.
      - inversion Hready; subst; simpl in *; try discriminate; try congruence;
          repeat match goal with
          | E : ExSOffered _ _ = ExSOffered _ _ |- _ =>
              inversion E; clear E; subst
          end.
        assert (q = offerer) by congruence. subst q.
        assert (v = v1) by congruence. subst v.
        destruct v1, v2; simpl in *.
        + eapply EBStackSep.ready_pair_offerer_same
              with (t2 := actor) (v2 := Some a0).
          * exact H.
          * simpl; tauto.
          * exact HI'.
          * symmetry; exact x.
        + eapply EBStackSep.ready_pair_offerer_comp
              with (t2 := actor) (v2 := None).
          * exact H.
          * simpl; tauto.
          * exact HI'.
          * symmetry; exact x.
        + eapply EBStackSep.ready_pair_offerer_comp
              with (t2 := actor) (v2 := Some a).
          * exact H.
          * simpl; tauto.
          * exact HI'.
          * symmetry; exact x.
        + eapply EBStackSep.ready_pair_offerer_same
              with (t2 := actor) (v2 := None).
          * exact H.
          * simpl; tauto.
          * exact HI'.
          * symmetry; exact x.
        all: try congruence.
      - inversion Hready; subst; simpl in *; try discriminate; try congruence;
          repeat match goal with
          | E : ExSOffered _ _ = ExSOffered _ _ |- _ =>
              inversion E; clear E; subst
          end; congruence.
      - assert (Haccept : ExchangerEffect actor
            (snd (SinglePossState.σ s)) (snd (SinglePossState.σ s'))).
        { rewrite <- x0. rewrite <- x. apply xe_accept. }
        inversion Hready; subst; simpl in *; try discriminate; try congruence;
          repeat match goal with
          | E : ExSPaired _ _ _ _ = ExSPaired _ _ _ _ |- _ =>
              inversion E; clear E; subst
          end; try contradiction.
        + assert (Hlocal' : @EBStackSep.Exposed A q
              (EBStackSep.done_token v v0) s').
          { eapply exchanger_effect_preserves_other_exposed;
              [exact Hneq|exact HI|exact HI'|exact Haccept|exact Hmaps|
               exact H1]. }
          assert (Epair : ExSPaired actor v1 accepter v2 =
              ExSPaired t1 v0 q v).
          { transitivity (snd (SinglePossState.σ s)); assumption. }
          inversion Epair; subst.
          assert (Epost : snd (SinglePossState.σ s') =
              ExSAccepted t1 v0 q v) by (symmetry; exact x).
          eapply EBStackSep.ready_accepted_accepter_comp
            with (t1 := t1) (v1 := v0);
            [exact H|exact H0|exact Hlocal'|exact Epost].
        + assert (Hlocal' : @EBStackSep.Exposed A q
              (ls_inv (EBStackSep.op_of v)) s').
          { eapply exchanger_effect_preserves_other_exposed;
              [exact Hneq|exact HI|exact HI'|exact Haccept|exact Hmaps|
               exact H1]. }
          assert (Epair : ExSPaired actor v1 accepter v2 =
              ExSPaired t1 v0 q v).
          { transitivity (snd (SinglePossState.σ s)); assumption. }
          inversion Epair; subst.
          assert (Epost : snd (SinglePossState.σ s') =
              ExSAccepted t1 v0 q v) by (symmetry; exact x).
          eapply EBStackSep.ready_accepted_accepter_same
            with (t1 := t1) (v1 := v0);
            [exact H|exact H0|exact Hlocal'|exact Epost].
      - inversion Hready; subst; simpl in *; try discriminate;
          repeat match goal with
          | E : ExSAccepted _ _ _ _ = ExSAccepted _ _ _ _ |- _ =>
              inversion E; clear E; subst
          end; congruence.
    Qed.

    Lemma source_G_effect_other_facts actor observer :
      actor <> observer ->
      (AssertionsSingle.A.Subset
        (source_G_effect actor) (source_R_facts observer)).
    Proof.
      intros Hneq s s' HG.
      inversion HG as [s0 s1 HI HI' Heffect Hmaps]; subst.
      destruct s as [[tss xss] rhos pis],
        s' as [[tss' xss'] rhos' pis']; simpl in *.
      destruct (EBStackSep.I_observe _ HI)
        as [ts [xs [Eσ [Eρ Hreq]]]].
      destruct (EBStackSep.I_observe _ HI')
        as [ts' [xs' [Eσ' [Eρ' Hreq']]]].
      simpl in Eσ, Eσ'. inversion Eσ; inversion Eσ'; subst.
      unfold source_R_facts. split.
      - eapply (exchanger_effect_other_find_none
          actor observer xs xs' pis pis').
        + exact Hneq.
        + exact Heffect.
        + exact Hreq.
        + exact Hreq'.
        + apply Hmaps. exact (not_eq_sym Hneq).
      - split.
        + intros _ ls Hexp.
          eapply exchanger_effect_preserves_other_exposed.
          * exact Hneq.
          * exact HI.
          * exact HI'.
          * exact Heffect.
          * apply Hmaps. exact (not_eq_sym Hneq).
          * exact Hexp.
        + split.
          * intros _ m Hpending.
            eapply exchanger_effect_preserves_other_pending.
            -- exact Hneq.
            -- exact HI.
            -- exact HI'.
            -- exact Heffect.
            -- apply Hmaps. exact (not_eq_sym Hneq).
            -- exact Hpending.
          * intros _ v Hready.
            eapply exchanger_effect_preserves_other_ready.
            -- exact Hneq.
            -- exact HI.
            -- exact HI'.
            -- exact Heffect.
            -- apply Hmaps. exact (not_eq_sym Hneq).
            -- exact Hready.
    Qed.

    Lemma source_G_try_update (actor : tid) (s s' : single_state) :
      @EBStackSep.I A s ->
      @EBStackSep.I A s' ->
      snd (SinglePossState.σ s) = snd (SinglePossState.σ s') ->
      (forall q, q <> actor ->
        TMap.find q (SinglePossState.π s) =
        TMap.find q (SinglePossState.π s')) ->
      source_G actor s s'.
    Proof.
      intros HI HI' Hexch Hkeep. eapply source_G_step; [exact HI|exact HI'|].
      constructor; auto.
    Qed.

    Lemma source_G_accept_update actor v1 accepter v2 ts rho pi :
      @EBStackSep.I A
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair ts (ExSPaired actor v1 accepter v2)) rho pi) ->
      @EBStackSep.I A
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair ts (ExSAccepted actor v1 accepter v2)) rho pi) ->
      source_G actor
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair ts (ExSPaired actor v1 accepter v2)) rho pi)
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair ts (ExSAccepted actor v1 accepter v2)) rho pi).
    Proof.
      intros HI HI'. eapply source_G_step; [exact HI|exact HI'|apply ge_accept].
    Qed.

    Lemma source_G_finish_update offerer v1 actor v2 ts rho pi :
      @EBStackSep.I A
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair ts (ExSAccepted offerer v1 actor v2)) rho pi) ->
      @EBStackSep.I A
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair ts ExSIdle) rho pi) ->
      source_G actor
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair ts (ExSAccepted offerer v1 actor v2)) rho pi)
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair ts ExSIdle) rho pi).
    Proof.
      intros HI HI'. eapply source_G_step; [exact HI|exact HI'|apply ge_finish].
    Qed.

    Lemma try_push_inv_update t v :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t
          (@InvEv (li_sig E) (inl (TryStackSpec.push v))))
        (@EBStackSep.Active A t (StackSpec.push v))
        (@EBStackSep.Active A t (StackSpec.push v)).
    Proof.
      pupdate_intros_atomic.
      pose proof (EBStackSep.Active_entails_I _ _ _ Hpre) as HIpre.
      destruct (EBStackSep.I_observe _ HIpre)
        as [ts [xs [Ephysical [Eabstract Hrequired]]]].
      simpl in Ephysical, Eabstract, Hrequired.
      inversion Ephysical; subst ts xs.
      assert (Hpost : @EBStackSep.Active A t0 (StackSpec.push v0)
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair (Pending s3 t0 (TryStackSpec.push v0)) s2) ρ1 π1)).
      { eapply EBStackSep.Exposed_rebuild_try with
          (ts := Idle s3) (pi := π1); eauto.
        exact (EBStackSep.Active_ALin t0 (StackSpec.push v0) _ Hpre). }
      pupdate_finish. split.
      - exact Hpost.
      - eapply source_G_try_update.
        + exact HIpre.
        + eapply EBStackSep.Active_entails_I; exact Hpost.
        + reflexivity.
        + intros; reflexivity.
    Qed.

    Lemma try_push_fail_update t v :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t
          (@ResEv (li_sig E) (inl (TryStackSpec.push v)) FAIL))
        (@EBStackSep.Active A t (StackSpec.push v))
        (@EBStackSep.Active A t (StackSpec.push v)).
    Proof.
      pupdate_intros_atomic.
      pose proof (EBStackSep.Active_entails_I _ _ _ Hpre) as HIpre.
      destruct (EBStackSep.I_observe _ HIpre)
        as [ts [xs [Ephysical [Eabstract Hrequired]]]].
      simpl in Ephysical, Eabstract, Hrequired.
      inversion Ephysical; subst ts xs.
      assert (Hpost : @EBStackSep.Active A t0 (StackSpec.push v0)
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair (Idle s3) s2) ρ1 π1)).
      { eapply EBStackSep.Exposed_rebuild_try with
          (ts := Pending s3 t0 (TryStackSpec.push v0)) (pi := π1); eauto.
        exact (EBStackSep.Active_ALin t0 (StackSpec.push v0) _ Hpre). }
      pupdate_finish. split.
      - exact Hpost.
      - eapply source_G_try_update.
        + exact HIpre.
        + eapply EBStackSep.Active_entails_I; exact Hpost.
        + reflexivity.
        + intros; reflexivity.
    Qed.

    Lemma try_push_ok_update t v :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t
          (@ResEv (li_sig E) (inl (TryStackSpec.push v)) (OK tt)))
        (@EBStackSep.Active A t (StackSpec.push v))
        (@EBStackSep.Completed A t (StackSpec.push v) tt).
    Proof.
      pupdate_intros_atomic.
      pose proof (EBStackSep.Active_entails_I _ _ _ Hpre) as HIpre.
      destruct (EBStackSep.I_observe _ HIpre)
        as [ts [xs [Ephysical [Eabstract Hrequired]]]].
      pose proof (EBStackSep.Active_owner_distinct _ _ _ Hpre) as Howner.
      simpl in Ephysical, Eabstract, Hrequired, Howner.
      inversion Ephysical; subst ts xs.
      subst ρ1.
      assert (Hlin : TMap.find t0 π1 =
        Some (ls_inv (StackSpec.push v0))).
      { exact (EBStackSep.Active_ALin t0 (StackSpec.push v0) _ Hpre). }
      pupdate_start.
      pupdate_forward t0 (InvEv (StackSpec.push v0)).
      pupdate_forward t0 (ResEv (StackSpec.push v0) tt);
        try exact Hlin.
      pupdate_finish.
      assert (Hrequired' : EBStackSep.required_ok s2
        (TMap.add t0 (ls_linr (StackSpec.push v0) tt)
          (TMap.add t0 (ls_lini (StackSpec.push v0)) π1))).
      { apply EBStackSep.required_ok_add_other; [|exact Howner].
        apply EBStackSep.required_ok_add_other; assumption. }
      assert (Hpost : @EBStackSep.Completed A t0 (StackSpec.push v0) tt
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair (Idle (cons v0 s0)) s2) (Idle (cons v0 s0))
          (TMap.add t0 (ls_linr (StackSpec.push v0) tt)
            (TMap.add t0 (ls_lini (StackSpec.push v0)) π1)))).
      { eapply EBStackSep.Exposed_rebuild_try with
          (ts := Pending s0 t0 (TryStackSpec.push v0)) (pi := π1).
        - exact Hpre.
        - reflexivity.
        - exact Hrequired'.
        - rewrite TMap.gss. reflexivity. }
      split; [exact Hpost|].
      eapply source_G_try_update.
      - exact HIpre.
      - eapply EBStackSep.Completed_entails_I; exact Hpost.
      - reflexivity.
      - intros q Hneq. simpl.
        repeat rewrite TMap.gso by congruence. reflexivity.
    Qed.

    Lemma try_pop_inv_update t :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t (@InvEv (li_sig E) (inl TryStackSpec.pop)))
        (@EBStackSep.Active A t StackSpec.pop)
        (@EBStackSep.Active A t StackSpec.pop).
    Proof.
      pupdate_intros_atomic.
      pose proof (EBStackSep.Active_entails_I _ _ _ Hpre) as HIpre.
      destruct (EBStackSep.I_observe _ HIpre)
        as [ts [xs [Ephysical [Eabstract Hrequired]]]].
      simpl in Ephysical, Eabstract, Hrequired.
      inversion Ephysical; subst ts xs.
      assert (Hpost : @EBStackSep.Active A t0 StackSpec.pop
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair (Pending s3 t0 TryStackSpec.pop) s2) ρ1 π1)).
      { eapply EBStackSep.Exposed_rebuild_try with
          (ts := Idle s3) (pi := π1); eauto.
        exact (EBStackSep.Active_ALin t0 StackSpec.pop _ Hpre). }
      pupdate_finish. split; [exact Hpost|].
      eapply source_G_try_update.
      - exact HIpre.
      - eapply EBStackSep.Active_entails_I; exact Hpost.
      - reflexivity.
      - intros; reflexivity.
    Qed.

    Lemma try_pop_fail_update t :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t
          (@ResEv (li_sig E) (inl TryStackSpec.pop) FAIL))
        (@EBStackSep.Active A t StackSpec.pop)
        (@EBStackSep.Active A t StackSpec.pop).
    Proof.
      pupdate_intros_atomic.
      pose proof (EBStackSep.Active_entails_I _ _ _ Hpre) as HIpre.
      destruct (EBStackSep.I_observe _ HIpre)
        as [ts [xs [Ephysical [Eabstract Hrequired]]]].
      simpl in Ephysical, Eabstract, Hrequired.
      inversion Ephysical; subst ts xs.
      assert (Hpost : @EBStackSep.Active A t0 StackSpec.pop
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair (Idle s3) s2) ρ1 π1)).
      { eapply EBStackSep.Exposed_rebuild_try with
          (ts := Pending s3 t0 TryStackSpec.pop) (pi := π1); eauto.
        exact (EBStackSep.Active_ALin t0 StackSpec.pop _ Hpre). }
      pupdate_finish. split; [exact Hpost|].
      eapply source_G_try_update.
      - exact HIpre.
      - eapply EBStackSep.Active_entails_I; exact Hpost.
      - reflexivity.
      - intros; reflexivity.
    Qed.

    Lemma try_pop_none_update t :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t
          (@ResEv (li_sig E) (inl TryStackSpec.pop) (OK None)))
        (@EBStackSep.Active A t StackSpec.pop)
        (@EBStackSep.Completed A t StackSpec.pop None).
    Proof.
      pupdate_intros_atomic.
      pose proof (EBStackSep.Active_entails_I _ _ _ Hpre) as HIpre.
      destruct (EBStackSep.I_observe _ HIpre)
        as [ts [xs [Ephysical [Eabstract Hrequired]]]].
      pose proof (EBStackSep.Active_owner_distinct _ _ _ Hpre) as Howner.
      simpl in Ephysical, Eabstract, Hrequired, Howner.
      inversion Ephysical; subst ts xs. subst ρ1.
      assert (Hlin : TMap.find t0 π1 = Some (ls_inv StackSpec.pop)).
      { exact (EBStackSep.Active_ALin t0 StackSpec.pop _ Hpre). }
      pupdate_start.
      pupdate_forward t0 (InvEv (@StackSpec.pop A)).
      pupdate_forward t0 (ResEv (@StackSpec.pop A) None); try exact Hlin.
      pupdate_finish.
      assert (Hrequired' : EBStackSep.required_ok s2
        (TMap.add t0 (ls_linr StackSpec.pop None)
          (TMap.add t0 (ls_lini StackSpec.pop) π1))).
      { apply EBStackSep.required_ok_add_other; [|exact Howner].
        apply EBStackSep.required_ok_add_other; assumption. }
      assert (Hpost : @EBStackSep.Completed A t0 StackSpec.pop None
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair (Idle nil) s2) (Idle nil)
          (TMap.add t0 (ls_linr StackSpec.pop None)
            (TMap.add t0 (ls_lini StackSpec.pop) π1)))).
      { eapply EBStackSep.Exposed_rebuild_try with
          (ts := Pending nil t0 TryStackSpec.pop) (pi := π1).
        - exact Hpre.
        - reflexivity.
        - exact Hrequired'.
        - rewrite TMap.gss. reflexivity. }
      split; [exact Hpost|].
      eapply source_G_try_update.
      - exact HIpre.
      - eapply EBStackSep.Completed_entails_I; exact Hpost.
      - reflexivity.
      - intros q Hneq. simpl.
        repeat rewrite TMap.gso by congruence. reflexivity.
    Qed.

    Lemma try_pop_some_update t (a : A) :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t
          (@ResEv (li_sig E) (inl TryStackSpec.pop) (OK (Some a))))
        (@EBStackSep.Active A t StackSpec.pop)
        (@EBStackSep.Completed A t StackSpec.pop (Some a)).
    Proof.
      pupdate_intros_atomic.
      pose proof (EBStackSep.Active_entails_I _ _ _ Hpre) as HIpre.
      destruct (EBStackSep.I_observe _ HIpre)
        as [ts [xs [Ephysical [Eabstract Hrequired]]]].
      pose proof (EBStackSep.Active_owner_distinct _ _ _ Hpre) as Howner.
      simpl in Ephysical, Eabstract, Hrequired, Howner.
      inversion Ephysical; subst ts xs. subst ρ1.
      assert (Hlin : TMap.find t0 π1 = Some (ls_inv StackSpec.pop)).
      { exact (EBStackSep.Active_ALin t0 StackSpec.pop _ Hpre). }
      pupdate_start.
      pupdate_forward t0 (InvEv (@StackSpec.pop A)).
      pupdate_forward t0 (ResEv (@StackSpec.pop A) (Some a)); try exact Hlin.
      pupdate_finish.
      assert (Hrequired' : EBStackSep.required_ok s2
        (TMap.add t0 (ls_linr StackSpec.pop (Some a))
          (TMap.add t0 (ls_lini StackSpec.pop) π1))).
      { apply EBStackSep.required_ok_add_other; [|exact Howner].
        apply EBStackSep.required_ok_add_other; assumption. }
      assert (Hpost : @EBStackSep.Completed A t0 StackSpec.pop (Some a)
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair (Idle s3) s2) (Idle s3)
          (TMap.add t0 (ls_linr StackSpec.pop (Some a))
            (TMap.add t0 (ls_lini StackSpec.pop) π1)))).
      { eapply EBStackSep.Exposed_rebuild_try with
          (ts := Pending (cons a s3) t0 TryStackSpec.pop) (pi := π1).
        - exact Hpre.
        - reflexivity.
        - exact Hrequired'.
        - rewrite TMap.gss. reflexivity. }
      split; [exact Hpost|].
      eapply source_G_try_update.
      - exact HIpre.
      - eapply EBStackSep.Completed_entails_I; exact Hpost.
      - reflexivity.
      - intros q Hneq. simpl.
        repeat rewrite TMap.gso by congruence. reflexivity.
    Qed.

    Lemma exch_offer_update t (v : option A) :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t (@InvEv (li_sig E) (inr (ExchSpec.exch v))))
        (@EBStackSep.Active A t (EBStackSep.op_of v))
        (@EBStackSep.ExchangeReady A t v).
    Proof.
      pupdate_intros_atomic.
      match type of Hpre with
      | EBStackSep.Active ?who (EBStackSep.op_of ?offered)
          (@SinglePossState.Build_ProofStateSingle _ _ _ _
            (pair ?under ExSIdle) ?abs ?lm) =>
          set (actor := who); set (value := offered);
          set (concrete_try := under); set (abstract_state := abs);
          set (linearization_map := lm)
      end.
      pose proof (EBStackSep.Active_entails_I _ _ _ Hpre) as HIpre.
      destruct (EBStackSep.I_observe _ HIpre)
        as [ts [xs [Ephysical [Eabstract Hrequired]]]].
      simpl in Ephysical, Eabstract, Hrequired.
      inversion Ephysical; subst ts xs.
      assert (Hlin : TMap.find actor linearization_map =
        Some (ls_inv (EBStackSep.op_of value))).
      { exact (EBStackSep.Active_ALin actor
          (EBStackSep.op_of value) _ Hpre). }
      assert (HIpost : @EBStackSep.I A
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair concrete_try (ExSOffered actor value))
          abstract_state linearization_map)).
      { unfold abstract_state, concrete_try, linearization_map.
        rewrite Eabstract.
        apply EBStackSep.I_intro_observed. exact Hlin. }
      assert (Hpost : @EBStackSep.ExchangeReady A actor value
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair concrete_try (ExSOffered actor value))
          abstract_state linearization_map)).
      { eapply EBStackSep.ready_offered; [exact HIpost|reflexivity]. }
      pupdate_finish. split; [exact Hpost|].
      eapply source_G_step; [exact HIpre|exact HIpost|apply ge_offer].
      - destruct v1 as [a|], v2 as [b|].
        + pose proof (EBStackSep.Active_entails_I _ _ _ Hpre) as HIpre.
          destruct (EBStackSep.I_observe _ HIpre)
            as [ts [xs [Ephysical [Eabstract Hoffer]]]].
          pose proof (EBStackSep.Active_owner_distinct _ _ _ Hpre) as Hneq.
          assert (Hcurrent : TMap.find t2 π1 =
            Some (ls_inv (StackSpec.push b))).
          { exact (EBStackSep.Active_ALin t2 (StackSpec.push b) _ Hpre). }
          simpl in Ephysical, Eabstract, Hoffer, Hneq.
          inversion Ephysical; subst ts xs. subst ρ1.
          assert (HIpost : @EBStackSep.I A
            (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
              (pair s1 (ExSPaired t1 (Some a) t2 (Some b)))
              (Idle (state s1)) π1)).
          { apply EBStackSep.I_intro_observed. exact Hoffer. }
          assert (Hactive : @EBStackSep.Active A t2 (StackSpec.push b)
            (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
              (pair s1 (ExSPaired t1 (Some a) t2 (Some b)))
              (Idle (state s1)) π1)).
          { eapply EBStackSep.I_ALin_exposes; [exact HIpost|exact Hcurrent|].
            simpl. congruence. }
          assert (Hpost : @EBStackSep.ExchangeReady A t2 (Some b)
            (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
              (pair s1 (ExSPaired t1 (Some a) t2 (Some b)))
              (Idle (state s1)) π1)).
          { eapply EBStackSep.ready_pair_accepter_same with
              (t1 := t1) (v1 := Some a).
            - congruence.
            - unfold EBStackSep.complementary; tauto.
            - exact Hactive.
            - reflexivity. }
          pupdate_finish. split; [exact Hpost|].
          eapply source_G_step; [exact HIpre|exact HIpost|].
          eapply ge_pair_same.
          * congruence.
          * unfold EBStackSep.complementary; tauto.
          * exact Hoffer.
        + pose proof (EBStackSep.Active_entails_I _ _ _ Hpre) as HIpre.
          destruct (EBStackSep.I_observe _ HIpre)
            as [ts [xs [Ephysical [Eabstract Hoffer]]]].
          pose proof (EBStackSep.Active_owner_distinct _ _ _ Hpre) as Hneq.
          assert (Hcurrent : TMap.find t2 π1 =
            Some (ls_inv StackSpec.pop)).
          { exact (EBStackSep.Active_ALin t2 StackSpec.pop _ Hpre). }
          simpl in Ephysical, Eabstract, Hoffer, Hneq.
          inversion Ephysical; subst ts xs. subst ρ1.
          pupdate_start.
          pupdate_forward t1 (InvEv (StackSpec.push a)); try exact Hoffer.
          pupdate_forward t1 (ResEv (StackSpec.push a) tt);
            try exact Hoffer.
          pupdate_forward t2 (InvEv (@StackSpec.pop A));
            try (repeat rewrite TMap.gso by congruence; exact Hcurrent).
          pupdate_forward t2 (ResEv (@StackSpec.pop A) (Some a)).
          pupdate_finish.
          set (post_map :=
            TMap.add t2 (ls_linr StackSpec.pop (Some a))
              (TMap.add t2 (ls_lini StackSpec.pop)
                (TMap.add t1 (ls_linr (StackSpec.push a) tt)
                  (TMap.add t1 (ls_lini (StackSpec.push a)) π1)))).
          assert (Hrequired' : EBStackSep.required_ok
            (ExSPaired t1 (Some a) t2 None) post_map).
          { unfold post_map; simpl.
            repeat rewrite TMap.gso by congruence.
            rewrite TMap.gss. reflexivity. }
          assert (HIpost : @EBStackSep.I A
            (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
              (pair s1 (ExSPaired t1 (Some a) t2 None))
              (Idle (state s1)) post_map)).
          { apply EBStackSep.I_intro_observed. exact Hrequired'. }
          assert (Hcompleted : @EBStackSep.Completed A t2 StackSpec.pop (Some a)
            (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
              (pair s1 (ExSPaired t1 (Some a) t2 None))
              (Idle (state s1)) post_map)).
          { eapply EBStackSep.I_ALin_exposes; [exact HIpost| |].
            - unfold AssertionsSingle.ALin, post_map; simpl.
              rewrite TMap.gss. reflexivity.
            - simpl. congruence. }
          assert (Hpost : @EBStackSep.ExchangeReady A t2 None
            (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
              (pair s1 (ExSPaired t1 (Some a) t2 None))
              (Idle (state s1)) post_map)).
          { eapply EBStackSep.ready_pair_accepter_comp with
              (t1 := t1) (v1 := Some a).
            - congruence.
            - simpl; auto.
            - exact Hcompleted.
            - reflexivity. }
          split; [exact Hpost|].
          eapply source_G_step; [exact HIpre|exact HIpost|].
          eapply ge_pair_comp.
          * congruence.
          * simpl; auto.
          * exact Hoffer.
          * exact Hrequired'.
          * intros q Hq1 Hq2. unfold post_map.
            repeat rewrite TMap.gso by congruence. reflexivity.
        + pose proof (EBStackSep.Active_entails_I _ _ _ Hpre) as HIpre.
          destruct (EBStackSep.I_observe _ HIpre)
            as [ts [xs [Ephysical [Eabstract Hoffer]]]].
          pose proof (EBStackSep.Active_owner_distinct _ _ _ Hpre) as Hneq.
          assert (Hcurrent : TMap.find t2 π1 =
            Some (ls_inv (StackSpec.push b))).
          { exact (EBStackSep.Active_ALin t2 (StackSpec.push b) _ Hpre). }
          simpl in Ephysical, Eabstract, Hoffer, Hneq.
          inversion Ephysical; subst ts xs. subst ρ1.
          pupdate_start.
          pupdate_forward t2 (InvEv (StackSpec.push b)); try exact Hcurrent.
          pupdate_forward t2 (ResEv (StackSpec.push b) tt);
            try exact Hcurrent.
          pupdate_forward t1 (InvEv (@StackSpec.pop A));
            try (repeat rewrite TMap.gso by congruence; exact Hoffer).
          pupdate_forward t1 (ResEv (@StackSpec.pop A) (Some b)).
          pupdate_finish.
          set (post_map :=
            TMap.add t1 (ls_linr StackSpec.pop (Some b))
              (TMap.add t1 (ls_lini StackSpec.pop)
                (TMap.add t2 (ls_linr (StackSpec.push b) tt)
                  (TMap.add t2 (ls_lini (StackSpec.push b)) π1)))).
          assert (Hrequired' : EBStackSep.required_ok
            (ExSPaired t1 None t2 (Some b)) post_map).
          { unfold post_map; simpl. rewrite TMap.gss. reflexivity. }
          assert (HIpost : @EBStackSep.I A
            (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
              (pair s1 (ExSPaired t1 None t2 (Some b)))
              (Idle (state s1)) post_map)).
          { apply EBStackSep.I_intro_observed. exact Hrequired'. }
          assert (Hcompleted : @EBStackSep.Completed A t2 (StackSpec.push b) tt
            (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
              (pair s1 (ExSPaired t1 None t2 (Some b)))
              (Idle (state s1)) post_map)).
          { eapply EBStackSep.I_ALin_exposes; [exact HIpost| |].
            - unfold AssertionsSingle.ALin, post_map; simpl.
              repeat rewrite TMap.gso by congruence.
              rewrite TMap.gss. reflexivity.
            - simpl. congruence. }
          assert (Hpost : @EBStackSep.ExchangeReady A t2 (Some b)
            (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
              (pair s1 (ExSPaired t1 None t2 (Some b)))
              (Idle (state s1)) post_map)).
          { eapply EBStackSep.ready_pair_accepter_comp with
              (t1 := t1) (v1 := None).
            - congruence.
            - simpl; auto.
            - exact Hcompleted.
            - reflexivity. }
          split; [exact Hpost|].
          eapply source_G_step; [exact HIpre|exact HIpost|].
          eapply ge_pair_comp.
          * congruence.
          * simpl; auto.
          * exact Hoffer.
          * exact Hrequired'.
          * intros q Hq1 Hq2. unfold post_map.
            repeat rewrite TMap.gso by congruence. reflexivity.
        + pose proof (EBStackSep.Active_entails_I _ _ _ Hpre) as HIpre.
          destruct (EBStackSep.I_observe _ HIpre)
            as [ts [xs [Ephysical [Eabstract Hoffer]]]].
          pose proof (EBStackSep.Active_owner_distinct _ _ _ Hpre) as Hneq.
          assert (Hcurrent : TMap.find t2 π1 = Some (ls_inv StackSpec.pop)).
          { exact (EBStackSep.Active_ALin t2 StackSpec.pop _ Hpre). }
          simpl in Ephysical, Eabstract, Hoffer, Hneq.
          inversion Ephysical; subst ts xs. subst ρ1.
          assert (HIpost : @EBStackSep.I A
            (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
              (pair s1 (ExSPaired t1 None t2 None))
              (Idle (state s1)) π1)).
          { apply EBStackSep.I_intro_observed. exact Hoffer. }
          assert (Hactive : @EBStackSep.Active A t2 StackSpec.pop
            (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
              (pair s1 (ExSPaired t1 None t2 None))
              (Idle (state s1)) π1)).
          { eapply EBStackSep.I_ALin_exposes; [exact HIpost|exact Hcurrent|].
            simpl. congruence. }
          assert (Hpost : @EBStackSep.ExchangeReady A t2 None
            (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
              (pair s1 (ExSPaired t1 None t2 None))
              (Idle (state s1)) π1)).
          { eapply EBStackSep.ready_pair_accepter_same with
              (t1 := t1) (v1 := None).
            - congruence.
            - unfold EBStackSep.complementary; tauto.
            - exact Hactive.
            - reflexivity. }
          pupdate_finish. split; [exact Hpost|].
          eapply source_G_step; [exact HIpre|exact HIpost|].
          eapply ge_pair_same.
          * congruence.
          * unfold EBStackSep.complementary; tauto.
          * exact Hoffer.
    Qed.

    Lemma exch_response_update t (v : option A)
        (other : option (option A)) :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t
          (@ResEv (li_sig E) (inr (ExchSpec.exch v)) other))
        (@EBStackSep.ExchangeReady A t v)
        (ExchangePost t v other).
    Proof.
      pupdate_intros_atomic.
      - inversion H0; subst; clear H0.
        inversion Hpre; subst; simpl in *; try discriminate.
        repeat match goal with
        | H : ExSOffered _ _ = ExSOffered _ _ |- _ =>
            inversion H; clear H; subst
        end.
        match goal with
        | Eev : Build_ThreadEvent _ (ResEv _ other) =
            Build_ThreadEvent _ (ResEv _ None) |- _ =>
            let Hret := fresh "Hret" in
            pose proof (f_equal te_ev Eev) as Hret;
            simpl in Hret; apply ResEvInversion in Hret; subst other
        end.
        destruct (EBStackSep.I_observe _ H0)
          as [ts [xs [Ephysical [Eabstract Hrequired]]]].
        simpl in Ephysical, Eabstract, Hrequired.
        inversion Ephysical; subst ts xs.
        assert (HIpost : @EBStackSep.I A
          (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
            (pair s1 ExSIdle) ρ1 π1)).
        { rewrite Eabstract. apply EBStackSep.I_intro_observed. exact I. }
        assert (Hpost : @EBStackSep.Active A t1 (EBStackSep.op_of v1)
          (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
            (pair s1 ExSIdle) ρ1 π1)).
        { eapply EBStackSep.I_ALin_exposes; [exact HIpost|exact Hrequired|].
          simpl. congruence. }
        pupdate_finish. split.
        + destruct v1; exact Hpost.
        + eapply source_G_step; [exact H0|exact HIpost|apply ge_revoke].
      - match goal with
        | Eev : Build_ThreadEvent _ (ResEv _ other) =
            Build_ThreadEvent _ (ResEv _ (Some v2)) |- _ =>
            let Hret := fresh "Hret" in
            pose proof (f_equal te_ev Eev) as Hret;
            simpl in Hret; apply ResEvInversion in Hret; subst other
        end.
        set (accepting_thread := t2).
        destruct v1 as [a|], v2 as [b|].
        + inversion Hpre; subst;
          simpl in *; try discriminate; try contradiction;
          repeat match goal with
          | E : ExSPaired _ _ _ _ = ExSPaired _ _ _ _ |- _ =>
              inversion E; clear E; subst
          end; try contradiction.
          match goal with
          | HI : EBStackSep.I _ |- _ => pose proof HI as HIpre
          end.
          destruct (EBStackSep.I_observe _ HIpre)
            as [ts [xs [Ephysical [Eabstract Hrequired]]]].
          simpl in Ephysical, Eabstract, Hrequired.
          inversion Ephysical; subst ts xs.
          assert (HIpost : @EBStackSep.I A
            (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
              (pair s1 (ExSAccepted t1 (Some a) accepting_thread (Some b))) ρ1 π1)).
          { rewrite Eabstract. apply EBStackSep.I_intro_observed. exact I. }
          assert (Hpost : @EBStackSep.Active A t1 (StackSpec.push a)
            (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
              (pair s1 (ExSAccepted t1 (Some a) accepting_thread (Some b))) ρ1 π1)).
          { eapply EBStackSep.I_ALin_exposes.
            - exact HIpost.
            - exact Hrequired.
            - simpl. congruence. }
          pupdate_finish. split; [exact Hpost|].
          apply source_G_accept_update; [exact HIpre|exact HIpost].
        + inversion Hpre; subst;
          simpl in *; try discriminate; try contradiction;
          repeat match goal with
          | E : ExSPaired _ _ _ _ = ExSPaired _ _ _ _ |- _ =>
              inversion E; clear E; subst
          end; try contradiction.
          match goal with
          | HI : EBStackSep.I _ |- _ => pose proof HI as HIpre
          end.
          destruct (EBStackSep.I_observe _ HIpre)
            as [ts [xs [Ephysical [Eabstract Hrequired]]]].
          simpl in Ephysical, Eabstract, Hrequired.
          inversion Ephysical; subst ts xs.
          assert (HIpost : @EBStackSep.I A
            (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
              (pair s1 (ExSAccepted t1 (Some a) accepting_thread None)) ρ1 π1)).
          { rewrite Eabstract. apply EBStackSep.I_intro_observed. exact I. }
          assert (Hpost : @EBStackSep.Completed A t1 (StackSpec.push a) tt
            (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
              (pair s1 (ExSAccepted t1 (Some a) accepting_thread None)) ρ1 π1)).
          { eapply EBStackSep.I_ALin_exposes; [exact HIpost|exact Hrequired|].
            simpl. congruence. }
          pupdate_finish. split; [exact Hpost|].
          apply source_G_accept_update; [exact HIpre|exact HIpost].
        + inversion Hpre; subst;
          simpl in *; try discriminate; try contradiction;
          repeat match goal with
          | E : ExSPaired _ _ _ _ = ExSPaired _ _ _ _ |- _ =>
              inversion E; clear E; subst
          end; try contradiction.
          match goal with
          | HI : EBStackSep.I _ |- _ => pose proof HI as HIpre
          end.
          destruct (EBStackSep.I_observe _ HIpre)
            as [ts [xs [Ephysical [Eabstract Hrequired]]]].
          simpl in Ephysical, Eabstract, Hrequired.
          inversion Ephysical; subst ts xs.
          assert (HIpost : @EBStackSep.I A
            (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
              (pair s1 (ExSAccepted t1 None accepting_thread (Some b))) ρ1 π1)).
          { rewrite Eabstract. apply EBStackSep.I_intro_observed. exact I. }
          assert (Hpost : @EBStackSep.Completed A t1 StackSpec.pop (Some b)
            (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
              (pair s1 (ExSAccepted t1 None accepting_thread (Some b))) ρ1 π1)).
          { eapply EBStackSep.I_ALin_exposes; [exact HIpost|exact Hrequired|].
            simpl. congruence. }
          pupdate_finish. split; [exact Hpost|].
          apply source_G_accept_update; [exact HIpre|exact HIpost].
        + inversion Hpre; subst;
          simpl in *; try discriminate; try contradiction;
          repeat match goal with
          | E : ExSPaired _ _ _ _ = ExSPaired _ _ _ _ |- _ =>
              inversion E; clear E; subst
          end; try contradiction.
          match goal with
          | HI : EBStackSep.I _ |- _ => pose proof HI as HIpre
          end.
          destruct (EBStackSep.I_observe _ HIpre)
            as [ts [xs [Ephysical [Eabstract Hrequired]]]].
          simpl in Ephysical, Eabstract, Hrequired.
          inversion Ephysical; subst ts xs.
          assert (HIpost : @EBStackSep.I A
            (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
              (pair s1 (ExSAccepted t1 None accepting_thread None)) ρ1 π1)).
          { rewrite Eabstract. apply EBStackSep.I_intro_observed. exact I. }
          assert (Hpost : @EBStackSep.Active A t1 StackSpec.pop
            (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
              (pair s1 (ExSAccepted t1 None accepting_thread None)) ρ1 π1)).
          { eapply EBStackSep.I_ALin_exposes.
            - exact HIpost.
            - exact Hrequired.
            - simpl. congruence. }
          pupdate_finish. split; [exact Hpost|].
          apply source_G_accept_update; [exact HIpre|exact HIpost].
      - match goal with
        | Eev : Build_ThreadEvent _ (ResEv _ other) =
            Build_ThreadEvent _ (ResEv _ (Some v1)) |- _ =>
            let Hret := fresh "Hret" in
            pose proof (f_equal te_ev Eev) as Hret;
            simpl in Hret; apply ResEvInversion in Hret; subst other
        end.
        set (offering_thread := t1).
        set (finishing_thread := t2).
        destruct v1 as [a|], v2 as [b|].
        + inversion Hpre; subst; unfold EBStackSep.complementary in *;
            simpl in *; try discriminate; try contradiction;
            repeat match goal with
            | E : ExSAccepted _ _ _ _ = ExSAccepted _ _ _ _ |- _ =>
                inversion E; clear E; subst
            end; try contradiction.
          match goal with
          | Hlocal : EBStackSep.Exposed _ (ls_inv (StackSpec.push b)) _ |- _ =>
              pose proof Hlocal as Hcell
          end.
          pose proof (EBStackSep.Exposed_entails_I _ _ _ Hcell) as HIpre.
          destruct (EBStackSep.I_observe _ HIpre)
            as [ts [xs [Ephysical [Eabstract Hrequired]]]].
          simpl in Ephysical, Eabstract, Hrequired.
          inversion Ephysical; subst ts xs.
          assert (HIpost : @EBStackSep.I A
            (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
              (pair s1 ExSIdle) ρ1 π1)).
          { rewrite Eabstract. apply EBStackSep.I_intro_observed. exact I. }
          assert (Hpost : @EBStackSep.Active A finishing_thread
              (StackSpec.push b)
            (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
              (pair s1 ExSIdle) ρ1 π1)).
          { eapply EBStackSep.I_ALin_exposes.
            - exact HIpost.
            - simpl. exact (EBStackSep.Exposed_ALin _ _ _ Hcell).
            - simpl. congruence. }
          pupdate_finish. split; [exact Hpost|].
          apply source_G_finish_update; [exact HIpre|exact HIpost].
        + inversion Hpre; subst; unfold EBStackSep.complementary in *;
            simpl in *; try discriminate; try contradiction;
            repeat match goal with
            | E : ExSAccepted _ _ _ _ = ExSAccepted _ _ _ _ |- _ =>
                inversion E; clear E; subst
            end; try contradiction.
          match goal with
          | Hlocal : EBStackSep.Exposed _ (ls_linr StackSpec.pop (Some a)) _ |- _ =>
              pose proof Hlocal as Hcell
          end.
          pose proof (EBStackSep.Exposed_entails_I _ _ _ Hcell) as HIpre.
          destruct (EBStackSep.I_observe _ HIpre)
            as [ts [xs [Ephysical [Eabstract Hrequired]]]].
          simpl in Ephysical, Eabstract, Hrequired.
          inversion Ephysical; subst ts xs.
          assert (HIpost : @EBStackSep.I A
            (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
              (pair s1 ExSIdle) ρ1 π1)).
          { rewrite Eabstract. apply EBStackSep.I_intro_observed. exact I. }
          assert (Hpost : @EBStackSep.Completed A finishing_thread
              StackSpec.pop (Some a)
            (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
              (pair s1 ExSIdle) ρ1 π1)).
          { eapply EBStackSep.I_ALin_exposes.
            - exact HIpost.
            - simpl. exact (EBStackSep.Exposed_ALin _ _ _ Hcell).
            - simpl. congruence. }
          pupdate_finish. split; [exact Hpost|].
          apply source_G_finish_update; [exact HIpre|exact HIpost].
        + inversion Hpre; subst; unfold EBStackSep.complementary in *;
            simpl in *; try discriminate; try contradiction;
            repeat match goal with
            | E : ExSAccepted _ _ _ _ = ExSAccepted _ _ _ _ |- _ =>
                inversion E; clear E; subst
            end; try contradiction.
          match goal with
          | Hlocal : EBStackSep.Exposed _
              (ls_linr (StackSpec.push b) tt) _ |- _ =>
              pose proof Hlocal as Hcell
          end.
          pose proof (EBStackSep.Exposed_entails_I _ _ _ Hcell) as HIpre.
          destruct (EBStackSep.I_observe _ HIpre)
            as [ts [xs [Ephysical [Eabstract Hrequired]]]].
          simpl in Ephysical, Eabstract, Hrequired.
          inversion Ephysical; subst ts xs.
          assert (HIpost : @EBStackSep.I A
            (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
              (pair s1 ExSIdle) ρ1 π1)).
          { rewrite Eabstract. apply EBStackSep.I_intro_observed. exact I. }
          assert (Hpost : @EBStackSep.Completed A finishing_thread
              (StackSpec.push b) tt
            (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
              (pair s1 ExSIdle) ρ1 π1)).
          { eapply EBStackSep.I_ALin_exposes.
            - exact HIpost.
            - simpl. exact (EBStackSep.Exposed_ALin _ _ _ Hcell).
            - simpl. congruence. }
          pupdate_finish. split; [exact Hpost|].
          apply source_G_finish_update; [exact HIpre|exact HIpost].
        + inversion Hpre; subst; unfold EBStackSep.complementary in *;
            simpl in *; try discriminate; try contradiction;
            repeat match goal with
            | E : ExSAccepted _ _ _ _ = ExSAccepted _ _ _ _ |- _ =>
                inversion E; clear E; subst
            end; try contradiction.
          match goal with
          | Hlocal : EBStackSep.Exposed _ (ls_inv StackSpec.pop) _ |- _ =>
              pose proof Hlocal as Hcell
          end.
          pose proof (EBStackSep.Exposed_entails_I _ _ _ Hcell) as HIpre.
          destruct (EBStackSep.I_observe _ HIpre)
            as [ts [xs [Ephysical [Eabstract Hrequired]]]].
          simpl in Ephysical, Eabstract, Hrequired.
          inversion Ephysical; subst ts xs.
          assert (HIpost : @EBStackSep.I A
            (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
              (pair s1 ExSIdle) ρ1 π1)).
          { rewrite Eabstract. apply EBStackSep.I_intro_observed. exact I. }
          assert (Hpost : @EBStackSep.Active A finishing_thread StackSpec.pop
            (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
              (pair s1 ExSIdle) ρ1 π1)).
          { eapply EBStackSep.I_ALin_exposes.
            - exact HIpost.
            - simpl. exact (EBStackSep.Exposed_ALin _ _ _ Hcell).
            - simpl. congruence. }
          pupdate_finish. split; [exact Hpost|].
          apply source_G_finish_update; [exact HIpre|exact HIpost].
    Qed.

    Lemma source_R_other_facts t :
      AssertionsSingle.A.Subset (source_R t) (source_R_facts t).
    Proof.
      unfold source_R.
      eapply AssertionsSingle.guarantee_generated_rely_facts.
      - intros actor Hneq s s' [Heffect _].
        eapply source_G_effect_other_facts; eauto.
      - apply source_R_observer_view_facts.
    Qed.

    Lemma source_valid_rg t :
      forall s s', source_R t s s' -> @EBStackSep.I A s' ->
        TMap.find t (SinglePossState.π s) = None <->
        TMap.find t (SinglePossState.π s') = None.
    Proof.
      intros s s' HR _. pose proof (source_R_other_facts t s s' HR)
        as [Hnone _]. exact Hnone.
    Qed.

    Lemma source_parallel_compatible t1 t2 :
      t1 <> t2 -> forall s s',
      (source_G t1 s s' \/
       (AssertionsSingle.GINV t1 s s' \/ AssertionsSingle.GRET t1 s s') \/
      AssertionsSingle.A.GId s s') -> source_R t2 s s'.
    Proof.
      intros Hneq. unfold source_R.
      apply AssertionsSingle.guarantee_generated_parallel_compatible.
      exact Hneq.
    Qed.

    Lemma source_I_stable t :
      AssertionsSingle.A.Stable (source_R t) (@EBStackSep.I A)
        (@EBStackSep.I A).
    Proof. apply AssertionsSingle.A.Stable_invariant. Qed.

    Lemma source_exposed_stable t ls :
      AssertionsSingle.A.Stable (source_R t) (@EBStackSep.I A)
        (@EBStackSep.Exposed A t ls).
    Proof.
      eapply AssertionsSingle.A.Stable_from_facts;
        [apply source_R_other_facts|].
      intros s s' [_ [Hpres _]] HI Hexp. eapply Hpres; eauto.
    Qed.

    Lemma source_pending_stable t m :
      AssertionsSingle.A.Stable (source_R t) (@EBStackSep.I A)
        (@EBStackSep.Pending A t m).
    Proof.
      eapply AssertionsSingle.A.Stable_from_facts;
        [apply source_R_other_facts|].
      intros s s' [_ [_ [Hpres _]]] HI Hpending. eapply Hpres; eauto.
    Qed.

    Lemma source_ready_stable t v :
      AssertionsSingle.A.Stable (source_R t) (@EBStackSep.I A)
        (@EBStackSep.ExchangeReady A t v).
    Proof.
      eapply AssertionsSingle.A.Stable_from_facts;
        [apply source_R_other_facts|].
      intros s s' [_ [_ [_ Hpres]]] HI Hready. eapply Hpres; eauto.
    Qed.

    Lemma valid_rg t :
      RGISimulationSet.RGISimulation.ValidRGI (R t) (G t) SI t.
    Proof. apply lift_valid_rgi. apply source_valid_rg. Qed.

    Lemma parallel_compatible t1 t2 :
      t1 <> t2 -> forall s s',
      (G t1 s s' \/
       (AssertionsSet.GINV t1 s s' \/ AssertionsSet.GRET t1 s s') \/
       AssertionsSet.A.GId s s') /\ SI s -> R t2 s s'.
    Proof.
      intros Hneq. eapply lift_parallel_compat; [exact Hneq|].
      apply source_parallel_compatible; exact Hneq.
    Qed.

    Lemma I_stable t : AssertionsSet.A.Stable (R t) SI SI.
    Proof. apply lift_stable. apply source_I_stable. Qed.

    Lemma active_stable t m :
      AssertionsSet.A.Stable (R t) SI (SActive t m).
    Proof. apply lift_stable. apply source_exposed_stable. Qed.

    Lemma completed_stable t m ret :
      AssertionsSet.A.Stable (R t) SI (SCompleted t m ret).
    Proof. apply lift_stable. apply source_exposed_stable. Qed.

    Lemma pending_stable t m :
      AssertionsSet.A.Stable (R t) SI (SPending t m).
    Proof. apply lift_stable. apply source_pending_stable. Qed.

    Lemma ready_stable t v :
      AssertionsSet.A.Stable (R t) SI (SReady t v).
    Proof. apply lift_stable. apply source_ready_stable. Qed.

    Lemma source_exchange_post_I t v other :
      ⊨ ExchangePost t v other ==>> @EBStackSep.I A.
    Proof.
      destruct v as [a|], other as [[ov|]|]; try destruct ov; simpl;
        intros s H;
        first [eapply EBStackSep.Active_entails_I; exact H |
               eapply EBStackSep.Completed_entails_I; exact H].
    Qed.

    Lemma source_exchange_post_stable t v other :
      AssertionsSingle.A.Stable (source_R t) (@EBStackSep.I A)
        (ExchangePost t v other).
    Proof.
      destruct v as [a|], other as [[ov|]|]; try destruct ov; simpl;
        first [apply source_exposed_stable | apply source_exposed_stable].
    Qed.

    Lemma no_error t (m : Sig.op (li_sig E))
        (P : @Logics.Assertion
          (@SinglePossState.ProofState _ _ (li_lts E) (li_lts F))) :
      ⊨ P ==>> AssertionsSingle.A.ANoError
        (Build_ThreadEvent t (InvEv m)).
    Proof.
      unfold AssertionsSingle.A.ANoError.
      intros [sigma rho pi] _ Herr.
      destruct sigma as [ts xs], m as [m|m]; simpl in *; contradiction.
    Qed.

    Definition PushLoopPost t v (r : unit + unit) :=
      match r with
      | inl _ => @EBStackSep.Active A t (StackSpec.push v)
      | inr _ => @EBStackSep.Completed A t (StackSpec.push v) tt
      end.

    Lemma push_try_fragment t v :
      [li_lts E, li_lts F, R t, G t, SI, t] ⊢
        {{ SActive t (StackSpec.push v) }}
        (@Vis (li_sig E) (unit + unit)
          (inl (TryStackSpec.push v)) (fun succ =>
          Ret (match succ with
               | FAIL => inl tt
               | OK _ => inr tt
               end)))
        {{ fun r => lift_assert (PushLoopPost t v r) }}.
    Proof.
      eapply singleton_provable_vis_safe with
        (P' := @EBStackSep.Active A t (StackSpec.push v))
        (Q' := fun succ =>
          match succ with
          | OK _ => @EBStackSep.Completed A t (StackSpec.push v) tt
          | FAIL => @EBStackSep.Active A t (StackSpec.push v)
          end).
      - apply no_error.
      - apply EBStackSep.Active_entails_I.
      - intros [u|]; [destruct u|];
          first [apply EBStackSep.Completed_entails_I |
                 apply EBStackSep.Active_entails_I].
      - apply source_exposed_stable.
      - intros [u|]; [destruct u|]; apply source_exposed_stable.
      - apply try_push_inv_update.
      - intros [u|].
        + destruct u. apply try_push_ok_update.
        + apply try_push_fail_update.
      - intros [u|].
        + destruct u. simpl. singleton_ret_safe.
          * exact ImplRefl.
          * apply EBStackSep.Completed_entails_I.
          * apply source_exposed_stable.
        + simpl. singleton_ret_safe.
          * exact ImplRefl.
          * apply EBStackSep.Active_entails_I.
          * apply source_exposed_stable.
    Qed.

    Definition PopLoopPost t (r : unit + option A) :=
      match r with
      | inl _ => @EBStackSep.Active A t StackSpec.pop
      | inr ret => @EBStackSep.Completed A t StackSpec.pop ret
      end.

    Lemma pop_try_fragment t :
      [li_lts E, li_lts F, R t, G t, SI, t] ⊢
        {{ SActive t StackSpec.pop }}
        (@Vis (li_sig E) (unit + option A)
          (inl TryStackSpec.pop) (fun succ =>
          Ret (match succ with
               | FAIL => inl tt
               | OK ret => inr ret
               end)))
        {{ fun r => lift_assert (PopLoopPost t r) }}.
    Proof.
      eapply singleton_provable_vis_safe with
        (P' := @EBStackSep.Active A t StackSpec.pop)
        (Q' := fun succ =>
          match succ with
          | OK ret => @EBStackSep.Completed A t StackSpec.pop ret
          | FAIL => @EBStackSep.Active A t StackSpec.pop
          end).
      - apply no_error.
      - apply EBStackSep.Active_entails_I.
      - intros [ret|];
          first [apply EBStackSep.Completed_entails_I |
                 apply EBStackSep.Active_entails_I].
      - apply source_exposed_stable.
      - intros [ret|]; apply source_exposed_stable.
      - apply try_pop_inv_update.
      - intros [ret|].
        + destruct ret as [a|].
          * apply try_pop_some_update.
          * apply try_pop_none_update.
        + apply try_pop_fail_update.
      - intros [ret|].
        + destruct ret as [a|]; simpl; singleton_ret_safe.
          * exact ImplRefl.
          * apply EBStackSep.Completed_entails_I.
          * apply source_exposed_stable.
          * exact ImplRefl.
          * apply EBStackSep.Completed_entails_I.
          * apply source_exposed_stable.
        + simpl. singleton_ret_safe.
          * exact ImplRefl.
          * apply EBStackSep.Active_entails_I.
          * apply source_exposed_stable.
    Qed.

    Lemma push_triple t v :
      [li_lts E, li_lts F, R t, G t, SI, t] ⊢
        {{ SActive t (StackSpec.push v) }}
        (push_impl v t)
        {{ fun _ => SCompleted t (StackSpec.push v) tt }}.
    Proof.
      unfold push_impl, EBStackSep.push_impl.
      eapply provable_doloop.
      - intros [] s Hcompleted. eapply lift_impl; [|exact Hcompleted].
        apply EBStackSep.Completed_entails_I.
      - intros []. apply lift_stable. apply source_exposed_stable.
      - eapply provable_conseq_weak_post with
          (Q' := fun r => lift_assert (PushLoopPost t v r)).
        + intros [u|]; destruct u; simpl.
          * intros s H. eapply lift_impl; [|exact H].
            apply EBStackSep.Active_entails_I.
          * intros s H. eapply lift_impl; [|exact H].
            apply EBStackSep.Completed_entails_I.
        + intros [u|]; destruct u; simpl; apply lift_stable;
            apply source_exposed_stable.
        + intros [u|]; destruct u; simpl; intros s H; exact H.
        + eapply (@singleton_provable_vis_safe
          (li_sig E) (li_sig F) (li_lts E) (li_lts F)
          (source_R t) (source_G t) (@EBStackSep.I A) t
          (unit + unit)
          (@EBStackSep.Active A t (StackSpec.push v))
          (PushLoopPost t v)
          (inr (ExchSpec.exch (Some v))) _
          (@EBStackSep.ExchangeReady A t (Some v))
          (ExchangePost t (Some v))).
          * apply no_error.
          * apply EBStackSep.ExchangeReady_entails_I.
          * apply source_exchange_post_I.
          * apply source_ready_stable.
          * apply source_exchange_post_stable.
          * apply exch_offer_update.
          * apply exch_response_update.
          * intros [[other|]|]; simpl.
            -- apply push_try_fragment.
            -- singleton_ret_safe.
               ++ exact ImplRefl.
               ++ apply EBStackSep.Completed_entails_I.
               ++ apply source_exposed_stable.
            -- apply push_try_fragment.
    Qed.

    Lemma pop_triple t :
      [li_lts E, li_lts F, R t, G t, SI, t] ⊢
        {{ SActive t StackSpec.pop }}
        (pop_impl t)
        {{ fun ret => SCompleted t StackSpec.pop ret }}.
    Proof.
      unfold pop_impl, EBStackSep.pop_impl.
      eapply provable_doloop.
      - intros ret s Hcompleted. eapply lift_impl; [|exact Hcompleted].
        apply EBStackSep.Completed_entails_I.
      - intros ret. apply lift_stable. apply source_exposed_stable.
      - eapply provable_conseq_weak_post with
          (Q' := fun r => lift_assert (PopLoopPost t r)).
        + intros [u|ret]; simpl.
          * destruct u. intros s H. eapply lift_impl; [|exact H].
            apply EBStackSep.Active_entails_I.
          * intros s H. eapply lift_impl; [|exact H].
            apply EBStackSep.Completed_entails_I.
        + intros [u|ret]; simpl; apply lift_stable;
            apply source_exposed_stable.
        + intros [u|ret]; simpl; intros s H; exact H.
        + eapply (@singleton_provable_vis_safe
          (li_sig E) (li_sig F) (li_lts E) (li_lts F)
          (source_R t) (source_G t) (@EBStackSep.I A) t
          (unit + option A)
          (@EBStackSep.Active A t StackSpec.pop)
          (PopLoopPost t)
          (inr (ExchSpec.exch None)) _
          (@EBStackSep.ExchangeReady A t None)
          (ExchangePost t None)).
          * apply no_error.
          * apply EBStackSep.ExchangeReady_entails_I.
          * apply source_exchange_post_I.
          * apply source_ready_stable.
          * apply source_exchange_post_stable.
          * apply exch_offer_update.
          * apply exch_response_update.
          * intros [[other|]|]; simpl.
            -- singleton_ret_safe.
               ++ exact ImplRefl.
               ++ apply EBStackSep.Completed_entails_I.
               ++ apply source_exposed_stable.
            -- apply pop_try_fragment.
            -- apply pop_try_fragment.
    Qed.

    Lemma set_ginv_exposes_active t m :
      forall s,
        AssertionsSet.A.ComposeA SI (AssertionsSet.Ginv t m) s ->
        SActive t m s.
    Proof.
      eapply lift_ginv_compose.
      intros out [pre [HI Hginv]].
      eapply EBStackSep.ginv_exposes_active; eauto.
    Qed.

    Lemma active_closes_invariant t m :
      ⊨ SActive t m ==>> SI.
    Proof.
      intros s H. eapply lift_impl; [|exact H].
      apply EBStackSep.Active_entails_I.
    Qed.

    Lemma completed_closes_invariant t m ret :
      ⊨ SCompleted t m ret ==>> SI.
    Proof.
      intros s H. eapply lift_impl; [|exact H].
      apply EBStackSep.Completed_entails_I.
    Qed.

    Lemma set_gret_closes_completed t m ret :
      forall s,
        AssertionsSet.A.ComposeA (SCompleted t m ret)
          (AssertionsSet.Gret t m ret) s -> SI s.
    Proof.
      eapply lift_gret_compose.
      intros out [pre [Hcompleted Hgret]].
      eapply EBStackSep.gret_closes_completed; eauto.
    Qed.

    Lemma completed_has_return_token t m ret :
      forall s, SCompleted t m ret s ->
      forall rho pi, SetPossState.Δ s rho pi ->
        TMap.find t pi = Some (ls_linr m ret).
    Proof.
      eapply lift_post_lin.
      intros x Hcompleted.
      eapply EBStackSep.Completed_ALin; exact Hcompleted.
    Qed.

    Lemma initial_spatial_invariant :
      SI (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
        (li_init E)
        (ac_singleton (li_init F) (@TMap.empty (@LinState (li_sig F))))).
    Proof.
      apply lift_initial. exact EBStackSep.initial_I.
    Qed.

    Program Definition Mebstack : layer_implementation_simulation E F :=
      {| li_impl m :=
          match m with
          | StackSpec.push v => push_impl v
          | StackSpec.pop => pop_impl
          end |}.
    Next Obligation.
      eapply SetLogic.soundness with (R := R) (G := G) (I := SI).
      - exact valid_rg.
      - exact parallel_compatible.
      - intros t f. destruct f as [v|].
        + exists (SActive t (StackSpec.push v)).
          exists (fun _ => SCompleted t (StackSpec.push v) tt).
          constructor.
          * intros s Hcompose. eapply set_ginv_exposes_active.
            exact Hcompose.
          * exact (active_closes_invariant t (StackSpec.push v)).
          * exact (active_stable t (StackSpec.push v)).
          * intros [] s Hcompose. eapply set_gret_closes_completed.
            exact Hcompose.
          * intros [] σ Δ Hcompleted ρ pi Hposs.
            eapply completed_has_return_token; eauto.
          * apply push_triple.
        + exists (SActive t StackSpec.pop).
          exists (fun ret => SCompleted t StackSpec.pop ret).
          constructor.
          * intros s Hcompose. eapply set_ginv_exposes_active.
            exact Hcompose.
          * exact (active_closes_invariant t StackSpec.pop).
          * exact (active_stable t StackSpec.pop).
          * intros ret s Hcompose. eapply set_gret_closes_completed.
            exact Hcompose.
          * intros ret σ Δ Hcompleted ρ pi Hposs.
            eapply completed_has_return_token; eauto.
          * apply pop_triple.
      - exact initial_spatial_invariant.
    Qed.

  End Proof.
End EBStackSepSetProof.
