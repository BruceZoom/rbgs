Require Import FMapPositive.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.ClassicalChoice.
Require Import Coq.Program.Equality.
Require Import Relation_Operators.

Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import Logics.
Require Import Assertion.
Require Import TPSimulationSet.
Require Import RGISimulationSet.
Require Import RGILogicSet.
Require Import SingletonPossibility.
Require Import CompLinLayer.

Require Import examples.Common.ThreadDomain.
Require Import examples.Common.IndexedFamilySpec.
Require Import examples.Common.IndexedFamily.


(** Program-logic verification of the generic indexed-family packaging
    adapter.  No separation algebra is required: this proof uses no frame
    rule and keeps one abstract possibility throughout. *)
Module IndexedFamilyProof.
  Import Reg.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import Semantics.
  Import AssertionsSingle.
  Import SingletonPossibility.
  Import TPSimulationSet.TPSimulation.
  Import CompLinLayer.
  Import IndexedFamilySpec.
  Import IndexedFamilyImpl.

  Module SetLogic := RGILogicSet.RGILogic.

  Open Scope assertion_scope.
  Open Scope rg_relation_scope.

  Section Proof.
    Context {E : Op.t}.
    Context (D : ThreadDomain.t).
    Context (O : IndexedObject E).

    Let VE := li_lts (TensorLayer O D).
    Let VF := li_lts
      (to_set_layer_interface (IndexedFamilyLayer D O)).

    Definition proof_state :=
      @SinglePossState.ProofState (li_sig (TensorLayer O D))
        (EIndexed E) VE VF.
    Definition assertion := @Logics.Assertion proof_state.
    Definition rg_relation :=
      @AssertionsSingle.A.RGRelation (li_sig (TensorLayer O D))
        (EIndexed E) VE VF.

    Definition source_I : assertion :=
      fun w => SinglePossState.ρ w =
        flatten O D (SinglePossState.σ w).

    Definition SI := lift_assert source_I.

    Definition source_G (actor : tid) : rg_relation :=
      fun w w' =>
        source_I w /\ source_I w' /\
        (forall observer, observer <> actor ->
          TMap.find observer (SinglePossState.π w) =
          TMap.find observer (SinglePossState.π w')).

    Definition source_R (observer : tid) : rg_relation :=
      AssertionsSingle.GuaranteeGeneratedRely source_G observer.

    Definition R observer := lift_relation (source_R observer).
    Definition G actor := lift_relation (source_G actor).

    Definition Active (actor : tid) (m : Sig.op (EIndexed E)) : assertion :=
      fun w => source_I w /\
        TMap.find actor (SinglePossState.π w) = Some (ls_inv m).

    Definition Linearizing
        (actor : tid) (m : Sig.op (EIndexed E)) : assertion :=
      fun w => source_I w /\
        TMap.find actor (SinglePossState.π w) = Some (ls_lini m).

    Definition Completed (actor : tid) (m : Sig.op (EIndexed E))
        (ret : Sig.ar m) : assertion :=
      fun w => source_I w /\
        TMap.find actor (SinglePossState.π w) = Some (ls_linr m ret).

    Definition SActive actor m := lift_assert (Active actor m).
    Definition SCompleted actor m ret := lift_assert (Completed actor m ret).

    Definition token_eq (observer : tid) : rg_relation :=
      fun w w' =>
        TMap.find observer (SinglePossState.π w) =
        TMap.find observer (SinglePossState.π w').

    Lemma source_G_token_other actor observer :
      actor <> observer ->
      (source_G actor ⊆ token_eq observer)%RGRelation.
    Proof.
      intros Hneq w w' [_ [_ Htokens]]. apply Htokens. congruence.
    Qed.

    Lemma observer_view_token observer :
      (AssertionsSingle.ObserverViewEq observer ⊆
        token_eq observer)%RGRelation.
    Proof. intros w w' [_ [_ Htoken]]. exact Htoken. Qed.

    Lemma source_R_token observer :
      (source_R observer ⊆ token_eq observer)%RGRelation.
    Proof.
      eapply AssertionsSingle.guarantee_generated_rely_facts.
      - intros actor Hneq. apply source_G_token_other. exact Hneq.
      - apply observer_view_token.
    Qed.

    Lemma source_valid_rg observer w w' :
      source_R observer w w' -> source_I w' ->
      TMap.find observer (SinglePossState.π w) = None <->
      TMap.find observer (SinglePossState.π w') = None.
    Proof.
      intros HR _. pose proof (source_R_token observer _ _ HR) as Heq.
      rewrite Heq. tauto.
    Qed.

    Lemma valid_rg observer :
      RGISimulationSet.RGISimulation.ValidRGI
        (R observer) (G observer) SI observer.
    Proof. eapply lift_valid_rgi. apply source_valid_rg. Qed.

    Lemma source_parallel_compatible actor observer :
      actor <> observer -> forall w w',
      (source_G actor w w' \/
       (AssertionsSingle.GINV actor w w' \/
        AssertionsSingle.GRET actor w w') \/
       AssertionsSingle.A.GId w w') ->
      source_R observer w w'.
    Proof.
      intros Hneq.
      eapply AssertionsSingle.guarantee_generated_parallel_compatible.
      exact Hneq.
    Qed.

    Lemma parallel_compatible actor observer :
      actor <> observer -> forall w w',
      (G actor w w' \/
       (AssertionsSet.GINV actor w w' \/ AssertionsSet.GRET actor w w') \/
       AssertionsSet.A.GId w w') /\ SI w ->
      R observer w w'.
    Proof.
      intros Hneq. eapply lift_parallel_compat; [exact Hneq|].
      apply source_parallel_compatible. exact Hneq.
    Qed.

    Lemma source_R_preserves_token observer w w' :
      source_R observer w w' ->
      TMap.find observer (SinglePossState.π w) =
      TMap.find observer (SinglePossState.π w').
    Proof. apply source_R_token. Qed.

    Lemma active_entails_I actor m :
      ⊨ Active actor m ==>> source_I.
    Proof. intros w [HI _]. exact HI. Qed.

    Lemma linearizing_entails_I actor m :
      ⊨ Linearizing actor m ==>> source_I.
    Proof. intros w [HI _]. exact HI. Qed.

    Lemma completed_entails_I actor m ret :
      ⊨ Completed actor m ret ==>> source_I.
    Proof. intros w [HI _]. exact HI. Qed.

    Lemma active_stable actor m :
      AssertionsSingle.A.Stable (source_R actor) source_I (Active actor m).
    Proof.
      unfold AssertionsSingle.A.Stable, AssertionsSingle.A.ComposeA.
      intros w [[pre [[HI Hlin] HR]] HI']. split; [exact HI'|].
      rewrite <- (source_R_preserves_token actor pre w HR). exact Hlin.
    Qed.

    Lemma linearizing_stable actor m :
      AssertionsSingle.A.Stable
        (source_R actor) source_I (Linearizing actor m).
    Proof.
      unfold AssertionsSingle.A.Stable, AssertionsSingle.A.ComposeA.
      intros w [[pre [[HI Hlin] HR]] HI']. split; [exact HI'|].
      rewrite <- (source_R_preserves_token actor pre w HR). exact Hlin.
    Qed.

    Lemma completed_stable actor m ret :
      AssertionsSingle.A.Stable
        (source_R actor) source_I (Completed actor m ret).
    Proof.
      unfold AssertionsSingle.A.Stable, AssertionsSingle.A.ComposeA.
      intros w [[pre [[HI Hlin] HR]] HI']. split; [exact HI'|].
      rewrite <- (source_R_preserves_token actor pre w HR). exact Hlin.
    Qed.

    Lemma ginv_exposes_active actor m :
      ⊨ AssertionsSingle.Ginv actor m ⊚ source_I ==>> Active actor m.
    Proof.
      intros w [pre [HI [Hsigma [Hrho [Hnone Hpi]]]]].
      destruct pre as [sigma rho pi]. destruct w as [sigma' rho' pi'].
      simpl in *. subst sigma' rho' pi'. split; [exact HI|].
      apply TMap.gss.
    Qed.

    Lemma gret_closes_completed actor m ret :
      ⊨ AssertionsSingle.Gret actor m ret ⊚ Completed actor m ret ==>>
        source_I.
    Proof.
      intros w [pre [[HI Hlin] [Hsigma [Hrho [Hfind Hpi]]]]].
      destruct pre as [sigma rho pi]. destruct w as [sigma' rho' pi'].
      simpl in *. subst sigma' rho' pi'. exact HI.
    Qed.

    Lemma set_ginv_exposes_active actor m :
      ⊨ AssertionsSet.A.ComposeA SI (AssertionsSet.Ginv actor m) ==>>
        SActive actor m.
    Proof.
      intros w Hcompose.
      eapply lift_ginv_compose; [apply ginv_exposes_active|exact Hcompose].
    Qed.

    Lemma set_gret_closes_completed actor m ret :
      ⊨ AssertionsSet.A.ComposeA (SCompleted actor m ret)
        (AssertionsSet.Gret actor m ret) ==>> SI.
    Proof.
      intros w Hcompose.
      eapply lift_gret_compose; [apply gret_closes_completed|exact Hcompose].
    Qed.

    Lemma completed_has_return_token actor m ret sigma Delta :
      SCompleted actor m ret
        (@SetPossState.Build_ProofStateSet _ _ VE VF sigma Delta) ->
      forall rho pi, Delta rho pi ->
        TMap.find actor pi = Some (ls_linr m ret).
    Proof.
      intros [w [Hview [_ Hlin]]] rho pi Hposs.
      eapply singleton_view_all_lin; eauto.
    Qed.

    Lemma initial_SI :
      SI (@SetPossState.Build_ProofStateSet _ _ VE VF
        (li_init (TensorLayer O D))
        (@ac_singleton (EIndexed E) VF
          (initial_family_state D O) (TMap.empty _))).
    Proof.
      apply lift_initial. unfold source_I. simpl.
      symmetry. apply flatten_initial.
    Qed.

    Definition SafeActive actor m nested : assertion :=
      fun w => Active actor m w /\
        AssertionsSingle.A.ANoError
          (Build_ThreadEvent actor (InvEv nested)) w.

    Lemma routed_inv_update actor owner op nested
        (Hroute : RoutesFrom O (ThreadDomain.first_thread D)
          (ThreadDomain.other_threads D) owner op nested)
        (Hcontains : ThreadDomain.contains D owner) :
      AssertionsSingle.PUpdate (source_G actor)
        (Build_ThreadEvent actor (InvEv nested))
        (Active actor (indexed_call owner op))
        (Linearizing actor (indexed_call owner op)).
    Proof.
      intros sigma rho pi [HI Hlin] sigma' Hstep.
      exists (flatten O D sigma').
      exists (TMap.add actor (ls_lini (indexed_call owner op)) pi).
      split.
      - apply rt_step. econstructor.
        + rewrite HI.
          eapply routes_inv_step_sound; eauto.
        + exact Hlin.
      - split.
        + split; simpl. reflexivity. apply TMap.gss.
        + repeat split; simpl; auto.
          intros observer Hneq. rewrite TMap.gso by congruence.
          reflexivity.
    Qed.

    Lemma routed_res_update actor owner op nested
        (nested_ret : Sig.ar nested) (ret : Sig.ar op)
        (Hreturn : RoutesReturn O (ThreadDomain.first_thread D)
          (ThreadDomain.other_threads D) owner op nested nested_ret ret)
        (Hcontains : ThreadDomain.contains D owner) :
      AssertionsSingle.PUpdate (source_G actor)
        (Build_ThreadEvent actor (ResEv nested nested_ret))
        (Linearizing actor (indexed_call owner op))
        (Completed actor (indexed_call owner op) ret).
    Proof.
      intros sigma rho pi [HI Hlin] sigma' Hstep.
      exists (flatten O D sigma').
      exists (TMap.add actor
        (ls_linr (indexed_call owner op) ret) pi).
      split.
      - apply rt_step. econstructor.
        + rewrite HI.
          eapply routes_return_res_step_sound; eauto.
        + exact Hlin.
      - split.
        + split; simpl. reflexivity. apply TMap.gss.
        + repeat split; simpl; auto.
          intros observer Hneq. rewrite TMap.gso by congruence.
          reflexivity.
    Qed.

    Lemma active_safe_or_error actor owner op nested
        (Hroute : RoutesFrom O (ThreadDomain.first_thread D)
          (ThreadDomain.other_threads D) owner op nested)
        (Hcontains : ThreadDomain.contains D owner) :
      forall w, Active actor (indexed_call owner op) w ->
        SafeActive actor (indexed_call owner op) nested w \/
        AssertionsSingle.APError w.
    Proof.
      intros w Hactive.
      destruct (classic (Error VE
        (Build_ThreadEvent actor (InvEv nested))
        (SinglePossState.σ w))) as [Herror | Hsafe].
      - right. destruct Hactive as [HI Hlin].
        unfold AssertionsSingle.APError. apply rt_step.
        econstructor.
        + rewrite HI.
          eapply routes_error_sound; eauto.
        + exact Hlin.
      - left. split; auto.
    Qed.

    Lemma active_outside_error actor owner op
        (Houtside : ~ ThreadDomain.contains D owner) :
      forall w, Active actor (indexed_call owner op) w ->
        AssertionsSingle.APError w.
    Proof.
      intros w [HI Hlin]. unfold AssertionsSingle.APError.
      apply rt_step. econstructor.
      - rewrite HI. constructor. exact Houtside.
      - exact Hlin.
    Qed.

    Lemma lift_safe_or_error actor owner op nested
        (Hroute : RoutesFrom O (ThreadDomain.first_thread D)
          (ThreadDomain.other_threads D) owner op nested)
        (Hcontains : ThreadDomain.contains D owner) :
      forall s, SActive actor (indexed_call owner op) s ->
        lift_assert (SafeActive actor (indexed_call owner op) nested) s \/
        AssertionsSet.APError s.
    Proof.
      intros s [w [Hview Hactive]].
      destruct (active_safe_or_error actor owner op nested
        Hroute Hcontains w Hactive) as [Hsafe | Herror].
      - left. exists w. auto.
      - right. econstructor.
        + eapply singleton_view_member; eauto.
        + exact Herror.
    Qed.

    Lemma lift_outside_error actor owner op
        (Houtside : ~ ThreadDomain.contains D owner) :
      forall s, SActive actor (indexed_call owner op) s ->
        AssertionsSet.APError s.
    Proof.
      intros s [w [Hview Hactive]]. econstructor.
      - eapply singleton_view_member; eauto.
      - eapply active_outside_error; eauto.
    Qed.

    Definition SFalse :
        @Logics.Assertion
          (@SetPossState.ProofState (li_sig (TensorLayer O D))
            (EIndexed E) VE VF) :=
      fun _ => False.

    Lemma sfalse_entails_I : ⊨ SFalse ==>> SI.
    Proof. intros s H. contradiction. Qed.

    Lemma sfalse_stable actor :
      AssertionsSet.A.Stable (R actor) SI SFalse.
    Proof.
      unfold AssertionsSet.A.Stable, AssertionsSet.A.ComposeA.
      intros s [[pre [Hfalse _]] _]. contradiction.
    Qed.

    Lemma false_triple actor {A}
        (p : Prog (li_sig (TensorLayer O D)) A)
        (Q : A -> @Logics.Assertion
          (@SetPossState.ProofState (li_sig (TensorLayer O D))
            (EIndexed E) VE VF))
        (HQI : forall a, ⊨ Q a ==>> SI)
        (HQstable : forall a,
          AssertionsSet.A.Stable (R actor) SI (Q a)) :
      SetLogic.HTripleProvable (R actor) (G actor) SI actor SFalse p Q.
    Proof.
      revert p. cofix IH. intros p. destruct p as [m k | a | p].
      - eapply SetLogic.provable_vis with
          (P := SFalse) (P' := SFalse) (Q' := fun _ => SFalse).
        + intros s Hfalse. left. exact Hfalse.
        + intros s Hfalse. contradiction.
        + apply sfalse_entails_I.
        + intros. apply sfalse_entails_I.
        + apply sfalse_stable.
        + intros. apply sfalse_stable.
        + intros sigma Delta Hfalse. contradiction.
        + intros ret sigma Delta Hfalse. contradiction.
        + intros ret. apply IH; assumption.
      - eapply SetLogic.provable_ret with (P := SFalse).
        + intros s Hfalse. left. exact Hfalse.
        + intros s Hfalse. contradiction.
        + apply HQI.
        + apply HQstable.
      - apply SetLogic.provable_tau. apply IH; assumption.
    Qed.

    Lemma pack_method_triple actor owner op :
      SetLogic.HTripleProvable (R actor) (G actor) SI actor
        (SActive actor (indexed_call owner op))
        (pack_impl O D (indexed_call owner op) actor)
        (fun ret => SCompleted actor (indexed_call owner op) ret).
    Proof.
      destruct (ThreadDomain.contains_dec D owner) as [Hcontains | Houtside].
      - destruct (dispatch_from_valid_full O
          (ThreadDomain.first_thread D) (ThreadDomain.other_threads D)
          owner op (ThreadDomain.contains_nodup D) Hcontains)
          as [nested [k [Hroute [Hdispatch Hreturns]]]].
        destruct (choice (fun nested_ret ret =>
          k nested_ret = Ret ret /\
          RoutesReturn O (ThreadDomain.first_thread D)
            (ThreadDomain.other_threads D) owner op nested nested_ret ret)
          Hreturns) as [ret_of Hret_of].
        unfold pack_impl. simpl. unfold dispatch. rewrite Hdispatch.
        eapply SetLogic.provable_perror with
          (P' := lift_assert
            (SafeActive actor (indexed_call owner op) nested)).
        + intros s Hactive.
          eapply lift_safe_or_error; eauto.
        + eapply singleton_provable_vis_safe with
            (P' := Linearizing actor (indexed_call owner op))
            (Q' := fun nested_ret =>
              Completed actor (indexed_call owner op) (ret_of nested_ret)).
          * intros w [_ Hsafe]. exact Hsafe.
          * apply linearizing_entails_I.
          * intros nested_ret. apply completed_entails_I.
          * apply linearizing_stable.
          * intros nested_ret. apply completed_stable.
          * intros sigma rho pi [Hactive Hsafe] sigma' Hstep.
            eapply routed_inv_update; eauto.
          * intros nested_ret.
            destruct (Hret_of nested_ret) as [_ Hreturn].
            eapply routed_res_update; eauto.
          * intros nested_ret.
            destruct (Hret_of nested_ret) as [Hk Hreturn]. rewrite Hk.
            eapply singleton_provable_ret_safe.
            -- intros w Hcompleted. exact Hcompleted.
            -- apply completed_entails_I.
            -- apply completed_stable.
      - destruct (dispatch_outside_tau O D owner op Houtside) as [p Hp].
        unfold pack_impl. simpl. rewrite Hp.
        eapply SetLogic.provable_perror with (P' := SFalse).
        + intros s Hactive. right. eapply lift_outside_error; eauto.
        + eapply false_triple.
          * intros ret s Hcompleted.
            eapply lift_impl; [apply completed_entails_I|exact Hcompleted].
          * intros ret. apply lift_stable. apply completed_stable.
    Qed.

    Lemma active_closes_invariant actor m :
      ⊨ SActive actor m ==>> SI.
    Proof.
      intros s Hactive.
      eapply lift_impl; [apply active_entails_I|exact Hactive].
    Qed.

    Lemma pack_method_provable actor m :
      exists P Q,
        SetLogic.MethodProvable VE VF (pack_impl O D)
          (R actor) (G actor) SI actor m P Q.
    Proof.
      destruct m as [owner op].
      exists (SActive actor (indexed_call owner op)).
      exists (fun ret =>
        SCompleted actor (indexed_call owner op) ret).
      constructor.
      - apply set_ginv_exposes_active.
      - apply active_closes_invariant.
      - apply lift_stable. apply active_stable.
      - intros ret. apply set_gret_closes_completed.
      - intros ret sigma Delta Hcompleted rho pi Hposs.
        eapply completed_has_return_token; eauto.
      - apply pack_method_triple.
    Qed.

    Program Definition MPackIndexedFamily :
        layer_implementation_simulation
          (TensorLayer O D)
          (to_set_layer_interface (IndexedFamilyLayer D O)) :=
      {| li_impl := pack_impl O D |}.
    Next Obligation.
      eapply SetLogic.soundness with (R := R) (G := G) (I := SI).
      - exact valid_rg.
      - exact parallel_compatible.
      - exact pack_method_provable.
      - exact initial_SI.
    Qed.

    Definition MPackIndexedFamilyLinearizable :
        layer_implementation_linearizability
          (TensorLayer O D)
          (to_set_layer_interface (IndexedFamilyLayer D O)) :=
      LISim2LILin MPackIndexedFamily.

  End Proof.

  Arguments MPackIndexedFamily {E} D O.
  Arguments MPackIndexedFamilyLinearizable {E} D O.

  Section Composition.
    Context {E : Op.t}.
    Context (D : ThreadDomain.t).
    Context (O : IndexedObject E).
    Context (Underlay : tid -> layer_interface).
    Context (component_correct : forall owner,
      layer_implementation_linearizability
        (Underlay owner) (SetComponentLayer O owner)).

    Definition compose_verified_indexed_family :
        layer_implementation_linearizability
          (TensorUnderlay Underlay D)
          (to_set_layer_interface (IndexedFamilyLayer D O)) :=
      compose_indexed_family O Underlay component_correct D
        (MPackIndexedFamilyLinearizable D O).
  End Composition.

End IndexedFamilyProof.
