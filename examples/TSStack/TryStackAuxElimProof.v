Require Import FMapPositive.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Program.Equality.
Require Import Coq.Relations.Relation_Operators.

Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import Logics.
Require Import Assertion.
Require Import RGILogicSet.
Require Import SingletonPossibility.
Require Import CompLinLayer.

Require Import examples.Common.Heap.
Require Import examples.Common.ThreadDomain.
Require Import examples.TSStack.TimestampSpec.
Require Import examples.TSStack.ListPoolSpec.
Require Import examples.TSStack.ListPoolElimSpec.
Require Import examples.TSStack.TryStackAuxElimSpec.
Require Import examples.TSStack.TryStackAuxElim.
Require Import examples.TSStack.ListPoolElimProof.


(** Correctness proof for TryStackAux with elimination over ListPoolElim
    (docs/plans/TSStackEliminationPlan.tex, Section 7.2).

    The structure is that of [TryStackAuxProof]: the abstract trypop
    response is delayed until the ListPool operation that determines it,
    so the singleton facade of the set-of-possibilities logic suffices.

    Sessions.  [startPop] is a lock-step pass-through.  The two session
    maps are related one-directionally ([session_protocol]): a session
    open in the TryStackAux state is open with the same data in the
    ListPool state.  The converse fails because TryStackAux closes the
    session on the terminal trypop results while ListPool never does.

    Elimination.  After [getTop start] returns a node, the ListPool step
    is inverted three ways (top of the snapshot, garbage, outside the
    start set) and the corresponding fact is carried to [tryRemove] in
    [TryRemoveReady].  A successful removal then uses
    [step_tsa_trypop_succ] or [step_tsa_trypop_elim]; the garbage case
    cannot succeed. *)
Module TryStackAuxElimProof.
  Import Reg LinCCALBase LTSSpec Lang Semantics.
  Import AssertionsSingle SingletonPossibility.
  Import TPSimulationSet.TPSimulation CompLinLayer.
  Import ListPoolSpec.
  Import ListPoolElimSpec.
  Import TryStackAuxElimSpec TryStackAuxElimImpl.
  Import (coercions, canonicals, notations) Sig.
  Module SetLogic := RGILogicSet.RGILogic.
  Import SetLogic.

  Open Scope prog_scope.
  Open Scope assertion_scope.
  Open Scope rg_relation_scope.

  Section Proof.
    Context {A : Type} (D : ThreadDomain.t).

    Definition E : layer_interface := @TryStackAuxElimImpl.E A D.
    Definition F : layer_interface := @TryStackAuxElimImpl.F A D.

    Definition concrete_state := State (li_lts E).
    Definition abstract_state := State (li_lts F).
    Definition single_state :=
      @SinglePossState.ProofStateSingle _ _ (li_lts E) (li_lts F).
    Definition assertion := @Logics.Assertion single_state.
    Definition rg_relation :=
      @AssertionsSingle.A.RGRelation _ _ (li_lts E) (li_lts F).

    Definition concrete_payload (c : @ListPoolControl A) :
        @ListPoolState A :=
      match c with
      | LPReady p => p
      | LPAtomicPending p _ _ => p
      end.

    Definition abstract_payload (c : @TryStackAuxControl A) :
        @TryStackAuxState A :=
      match c with
      | TSAReady s => s
      | TSAAtomicPending s _ _ => s
      end.

    Definition graph_represents
        (p : @ListPoolState A) (s : @TryStackAuxState A) : Prop :=
      lp_vertices p = tsa_vertices s /\
      lp_edges p = tsa_edges s /\
      lp_pending_pushes p = tsa_pending_pushes s /\
      lp_garbage p = tsa_garbage s.

    Definition snapshot_protocol
        (p : @ListPoolState A) (s : @TryStackAuxState A)
        (pi : tmap (@LinState (li_sig F))) : Prop :=
      (forall actor N,
        TMap.find actor (lp_snapshots p) = Some N ->
        TMap.find actor (tsa_snapshots s) = Some N) /\
      (forall actor,
        (exists N, TMap.find actor (tsa_snapshots s) = Some N) <->
        exists start,
          TMap.find actor pi = Some (ls_lini (tsa_trypop start))) /\
      (forall actor,
        (exists loc, TMap.find actor (tsa_pending_pushes s) = Some loc) <->
        exists v, TMap.find actor pi = Some (ls_lini (tsa_push v))) /\
      (forall actor N,
        TMap.find actor (tsa_snapshots s) = Some N ->
        forall n, N n -> tsa_is_vertex s n).

    (** Sessions: open in TryStackAux implies open with the same data in
        ListPool; a TryStackAux token implies a start set; a pending
        [startPop] is exactly a start set without token. *)
    Definition session_protocol
        (p : @ListPoolState A) (s : @TryStackAuxState A)
        (pi : tmap (@LinState (li_sig F))) : Prop :=
      (forall actor N0,
        TMap.find actor (tsa_pop_starts s) = Some N0 ->
        TMap.find actor (lp_pop_starts p) = Some N0) /\
      (forall actor ts,
        TMap.find actor (tsa_pop_ts s) = Some ts ->
        TMap.find actor (lp_pop_ts p) = Some ts) /\
      (forall actor ts,
        TMap.find actor (tsa_pop_ts s) = Some ts ->
        exists N0, TMap.find actor (tsa_pop_starts s) = Some N0) /\
      (forall actor,
        (TMap.find actor (tsa_pop_ts s) = None /\
         exists N0, TMap.find actor (tsa_pop_starts s) = Some N0) <->
        TMap.find actor pi = Some (ls_lini tsa_startPop)).

    Definition vertices_owned (p : @ListPoolState A) : Prop :=
      forall n, is_vertex p n -> ThreadDomain.contains D (fst n).

    Definition source_I : assertion :=
      fun w =>
        exists s,
          SinglePossState.ρ w = TSAReady s /\
          graph_represents
            (concrete_payload (SinglePossState.σ w)) s /\
          snapshot_protocol
            (concrete_payload (SinglePossState.σ w)) s
            (SinglePossState.π w) /\
          session_protocol
            (concrete_payload (SinglePossState.σ w)) s
            (SinglePossState.π w) /\
          vertices_owned (concrete_payload (SinglePossState.σ w)).

    Definition SI := lift_assert source_I.

    Definition graph_evol
        (p p' : @ListPoolState A) : Prop :=
      (forall n v, lp_vertices p n = Some v ->
        lp_vertices p' n = Some v) /\
      (forall newer older, is_vertex p newer ->
        (lp_edges p newer older <-> lp_edges p' newer older)) /\
      (forall n, lp_garbage p n -> lp_garbage p' n).

    Definition actor_local_eq (actor : tid)
        (w w' : single_state) : Prop :=
      TMap.find actor
        (lp_snapshots (concrete_payload (SinglePossState.σ w))) =
      TMap.find actor
        (lp_snapshots (concrete_payload (SinglePossState.σ w'))) /\
      TMap.find actor
        (tsa_snapshots (abstract_payload (SinglePossState.ρ w))) =
      TMap.find actor
        (tsa_snapshots (abstract_payload (SinglePossState.ρ w'))) /\
      TMap.find actor
        (lp_pending_pushes (concrete_payload (SinglePossState.σ w))) =
      TMap.find actor
        (lp_pending_pushes (concrete_payload (SinglePossState.σ w'))) /\
      TMap.find actor
        (lp_pop_starts (concrete_payload (SinglePossState.σ w))) =
      TMap.find actor
        (lp_pop_starts (concrete_payload (SinglePossState.σ w'))) /\
      TMap.find actor
        (lp_pop_ts (concrete_payload (SinglePossState.σ w))) =
      TMap.find actor
        (lp_pop_ts (concrete_payload (SinglePossState.σ w'))) /\
      TMap.find actor
        (tsa_pop_starts (abstract_payload (SinglePossState.ρ w))) =
      TMap.find actor
        (tsa_pop_starts (abstract_payload (SinglePossState.ρ w'))) /\
      TMap.find actor
        (tsa_pop_ts (abstract_payload (SinglePossState.ρ w))) =
      TMap.find actor
        (tsa_pop_ts (abstract_payload (SinglePossState.ρ w'))) /\
      TMap.find actor (SinglePossState.π w) =
      TMap.find actor (SinglePossState.π w').

    Definition atomic_control_owned (actor : tid)
        (c : @ListPoolControl A) : Prop :=
      match c with
      | LPReady _ => True
      | LPAtomicPending _ pending_actor _ => pending_actor = actor
      end.

    Definition source_G (actor : tid) : rg_relation :=
      fun w w' =>
        source_I w /\ source_I w' /\
        graph_evol
          (concrete_payload (SinglePossState.σ w))
          (concrete_payload (SinglePossState.σ w')) /\
        (forall observer, actor <> observer -> actor_local_eq observer w w') /\
        atomic_control_owned actor (SinglePossState.σ w').

    Definition source_R (observer : tid) : rg_relation :=
      AssertionsSingle.GuaranteeGeneratedRely source_G observer.

    Definition R actor := lift_relation (source_R actor).
    Definition G actor := lift_relation (source_G actor).

    Definition Active (actor : tid) (op : Sig.op (li_sig F)) : assertion :=
      source_I //\\ AssertionsSingle.ALin actor (ls_inv op).

    Definition Completed (actor : tid) (op : Sig.op (li_sig F))
        (ret : Sig.ar op) : assertion :=
      source_I //\\ AssertionsSingle.ALin actor (ls_linr op ret).

    Definition SActive actor op := lift_assert (Active actor op).
    Definition SCompleted actor op ret := lift_assert (Completed actor op ret).

    (** Small tactics for token obligations. *)
    Ltac old_token_neq Htoken :=
      let Hb := fresh "Hb" in
      let Habs := fresh "Habs" in
      intros; intro Hb;
      pose proof (eq_trans (eq_sym Htoken) Hb) as Habs;
      discriminate Habs.

    Ltac new_token_neq :=
      let Hb := fresh "Hb" in
      intros; intro Hb; simpl in Hb;
      rewrite TMap.gss in Hb; discriminate.

    Ltac other_token :=
      let b := fresh "b" in
      let Hneq := fresh "Hneq" in
      intros b Hneq; simpl;
      repeat rewrite TMap.gso by congruence;
      repeat rewrite TMap.gro by congruence;
      reflexivity.

    Lemma initial_graph_represents :
      graph_represents (@empty_list_pool_state A)
        (@empty_try_stack_aux_state A).
    Proof. unfold graph_represents; simpl; repeat split; reflexivity. Qed.

    Lemma initial_snapshot_protocol :
      snapshot_protocol (@empty_list_pool_state A)
        (@empty_try_stack_aux_state A)
        (@TMap.empty (@LinState (li_sig F))).
    Proof.
      unfold snapshot_protocol, empty_list_pool_state,
        empty_try_stack_aux_state; simpl.
      split; [intros actor N Hfind; rewrite TMap.gempty in Hfind;
              discriminate|].
      split.
      { intro actor. split.
        - intros [N Hfind]. rewrite TMap.gempty in Hfind. discriminate.
        - intros [start Hfind]. rewrite TMap.gempty in Hfind. discriminate. }
      split.
      { intro actor. split.
        - intros [loc Hfind]. rewrite TMap.gempty in Hfind. discriminate.
        - intros [v Hfind]. rewrite TMap.gempty in Hfind. discriminate. }
      intros actor N Hfind. rewrite TMap.gempty in Hfind. discriminate.
    Qed.

    Lemma initial_session_protocol :
      session_protocol (@empty_list_pool_state A)
        (@empty_try_stack_aux_state A)
        (@TMap.empty (@LinState (li_sig F))).
    Proof.
      unfold session_protocol, empty_list_pool_state,
        empty_try_stack_aux_state; simpl.
      split; [intros actor N0 Hfind; rewrite TMap.gempty in Hfind;
              discriminate|].
      split; [intros actor ts Hfind; rewrite TMap.gempty in Hfind;
              discriminate|].
      split; [intros actor ts Hfind; rewrite TMap.gempty in Hfind;
              discriminate|].
      intro actor. split.
      - intros [_ [N0 Hfind]]. rewrite TMap.gempty in Hfind. discriminate.
      - intro Hfind. rewrite TMap.gempty in Hfind. discriminate.
    Qed.

    Lemma initial_vertices_owned :
      vertices_owned (@empty_list_pool_state A).
    Proof.
      intros n Hvertex. exfalso.
      now apply (@empty_state_has_no_vertex A n).
    Qed.

    Lemma vertices_owned_start_push p actor loc (v : A) :
      ThreadDomain.contains D actor -> vertices_owned p ->
      vertices_owned (start_push actor loc v p).
    Proof.
      intros Hactor Howned [owner addr] Hvertex.
      unfold is_vertex, start_push in Hvertex; simpl in Hvertex.
      unfold node_update in Hvertex.
      destruct (node_eq_dec (pair actor loc) (pair owner addr))
        as [Heq|Hneq].
      - inversion Heq; subst. exact Hactor.
      - apply (Howned (pair owner addr)). exact Hvertex.
    Qed.

    Lemma vertices_owned_finish_push p actor :
      vertices_owned p -> vertices_owned (finish_push actor p).
    Proof. unfold vertices_owned, is_vertex, finish_push; simpl; auto. Qed.

    Lemma vertices_owned_start_snapshot p actor :
      vertices_owned p -> vertices_owned (start_snapshot actor p).
    Proof. unfold vertices_owned, is_vertex, start_snapshot; simpl; auto. Qed.

    Lemma vertices_owned_clear_snapshot p actor :
      vertices_owned p -> vertices_owned (clear_snapshot actor p).
    Proof. unfold vertices_owned, is_vertex, clear_snapshot; simpl; auto. Qed.

    Lemma vertices_owned_mark_garbage p n :
      vertices_owned p -> vertices_owned (mark_garbage n p).
    Proof. unfold vertices_owned, is_vertex, mark_garbage; simpl; auto. Qed.

    Lemma vertices_owned_start_pop_session p actor :
      vertices_owned p -> vertices_owned (start_pop_session actor p).
    Proof.
      unfold vertices_owned, is_vertex, start_pop_session; simpl; auto.
    Qed.

    Lemma vertices_owned_finish_pop_session p actor ts :
      vertices_owned p -> vertices_owned (finish_pop_session actor ts p).
    Proof.
      unfold vertices_owned, is_vertex, finish_pop_session; simpl; auto.
    Qed.

    Lemma initial_source_I :
      source_I
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (li_init E) (li_init F)
          (@TMap.empty (@LinState (li_sig F)))).
    Proof.
      exists (@empty_try_stack_aux_state A). simpl.
      split; [reflexivity|]. split.
      - apply initial_graph_represents.
      - split; [apply initial_snapshot_protocol|].
        split; [apply initial_session_protocol|].
        apply initial_vertices_owned.
    Qed.

    Lemma initial_SI :
      SI (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
        (li_init E)
        (ac_singleton (li_init F)
          (@TMap.empty (@LinState (li_sig F))))).
    Proof. apply lift_initial. exact initial_source_I. Qed.

    Definition token_eq (observer : tid) : rg_relation :=
      fun w w' =>
        TMap.find observer (SinglePossState.π w) =
        TMap.find observer (SinglePossState.π w').

    Lemma source_G_token_other actor observer :
      actor <> observer ->
      (source_G actor ⊆ token_eq observer)%RGRelation.
    Proof.
      intros Hneq w w' [_ [_ [_ [Hlocal _]]]].
      destruct (Hlocal observer Hneq)
        as [_ [_ [_ [_ [_ [_ [_ Htoken]]]]]]].
      exact Htoken.
    Qed.

    Lemma observer_view_token observer :
      (AssertionsSingle.ObserverViewEq observer ⊆
        token_eq observer)%RGRelation.
    Proof. intros w w' [_ [_ Htoken]]. exact Htoken. Qed.

    Lemma source_R_token observer :
      (source_R observer ⊆ token_eq observer)%RGRelation.
    Proof.
      eapply AssertionsSingle.guarantee_generated_rely_facts.
      - intros actor Hneq. now apply source_G_token_other.
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
      intros Hneq. eapply
        AssertionsSingle.guarantee_generated_parallel_compatible.
      exact Hneq.
    Qed.

    Lemma parallel_compatible actor observer :
      actor <> observer -> forall w w',
      (G actor w w' \/
       (AssertionsSet.GINV actor w w' \/
        AssertionsSet.GRET actor w w') \/
       AssertionsSet.A.GId w w') /\ SI w ->
      R observer w w'.
    Proof.
      intros Hneq. eapply lift_parallel_compat; [exact Hneq|].
      apply source_parallel_compatible; exact Hneq.
    Qed.

    Lemma active_entails_I actor op :
      ⊨ Active actor op ==>> source_I.
    Proof. apply ConjLeftImpl. apply ImplRefl. Qed.

    Lemma completed_entails_I actor op ret :
      ⊨ Completed actor op ret ==>> source_I.
    Proof. apply ConjLeftImpl. apply ImplRefl. Qed.

    Lemma active_stable actor op :
      AssertionsSingle.A.Stable (source_R actor) source_I
        (Active actor op).
    Proof.
      unfold AssertionsSingle.A.Stable, Active.
      intros out [[pre [[HIpre Hlin] HR]] HIout].
      split; [exact HIout|]. unfold AssertionsSingle.ALin in *.
      rewrite <- (source_R_token actor _ _ HR). exact Hlin.
    Qed.

    Lemma completed_stable actor op ret :
      AssertionsSingle.A.Stable (source_R actor) source_I
        (Completed actor op ret).
    Proof.
      unfold AssertionsSingle.A.Stable, Completed.
      intros out [[pre [[HIpre Hlin] HR]] HIout].
      split; [exact HIout|]. unfold AssertionsSingle.ALin in *.
      rewrite <- (source_R_token actor _ _ HR). exact Hlin.
    Qed.

    (** Generic preservation lemmas for the two protocols. *)

    Lemma snapshot_protocol_fields p s pi p' s' :
      snapshot_protocol p s pi ->
      lp_snapshots p' = lp_snapshots p ->
      tsa_snapshots s' = tsa_snapshots s ->
      tsa_pending_pushes s' = tsa_pending_pushes s ->
      tsa_vertices s' = tsa_vertices s ->
      snapshot_protocol p' s' pi.
    Proof.
      intros Hprotocol H1 H2 H3 H4.
      unfold snapshot_protocol, tsa_is_vertex in *.
      rewrite H1, H2, H3, H4. exact Hprotocol.
    Qed.

    Lemma snapshot_protocol_retoken p s pi pi' actor :
      snapshot_protocol p s pi ->
      (forall start,
        TMap.find actor pi <> Some (ls_lini (tsa_trypop start))) ->
      (forall start,
        TMap.find actor pi' <> Some (ls_lini (tsa_trypop start))) ->
      (forall v, TMap.find actor pi <> Some (ls_lini (tsa_push v))) ->
      (forall v, TMap.find actor pi' <> Some (ls_lini (tsa_push v))) ->
      (forall a, a <> actor -> TMap.find a pi' = TMap.find a pi) ->
      snapshot_protocol p s pi'.
    Proof.
      intros [Hconcrete [Hsnapshot [Hpush Hwf]]]
        Hold_snap Hnew_snap Hold_push Hnew_push Hother.
      split; [exact Hconcrete|]. split.
      - intro observer.
        destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
        + split.
          * intros Hsome.
            destruct (proj1 (Hsnapshot actor) Hsome) as [start Hbad].
            exfalso. exact (Hold_snap start Hbad).
          * intros [start Hbad]. exfalso. exact (Hnew_snap start Hbad).
        + rewrite Hother by exact Hneq. apply Hsnapshot.
      - split; [|exact Hwf].
        intro observer.
        destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
        + split.
          * intros Hsome.
            destruct (proj1 (Hpush actor) Hsome) as [v Hbad].
            exfalso. exact (Hold_push v Hbad).
          * intros [v Hbad]. exfalso. exact (Hnew_push v Hbad).
        + rewrite Hother by exact Hneq. apply Hpush.
    Qed.

    Lemma snapshot_protocol_keep p s pi p' s' pi' actor :
      snapshot_protocol p s pi ->
      lp_snapshots p' = lp_snapshots p ->
      tsa_snapshots s' = tsa_snapshots s ->
      tsa_pending_pushes s' = tsa_pending_pushes s ->
      tsa_vertices s' = tsa_vertices s ->
      (forall start,
        TMap.find actor pi <> Some (ls_lini (tsa_trypop start))) ->
      (forall start,
        TMap.find actor pi' <> Some (ls_lini (tsa_trypop start))) ->
      (forall v, TMap.find actor pi <> Some (ls_lini (tsa_push v))) ->
      (forall v, TMap.find actor pi' <> Some (ls_lini (tsa_push v))) ->
      (forall a, a <> actor -> TMap.find a pi' = TMap.find a pi) ->
      snapshot_protocol p' s' pi'.
    Proof.
      intros Hprotocol H1 H2 H3 H4 Hos Hns Hop Hnp Hother.
      apply (snapshot_protocol_retoken p' s' pi pi' actor);
        [|exact Hos|exact Hns|exact Hop|exact Hnp|exact Hother].
      exact (snapshot_protocol_fields p s pi p' s' Hprotocol H1 H2 H3 H4).
    Qed.

    Lemma session_protocol_fields p s pi p' s' :
      session_protocol p s pi ->
      lp_pop_starts p' = lp_pop_starts p ->
      lp_pop_ts p' = lp_pop_ts p ->
      tsa_pop_starts s' = tsa_pop_starts s ->
      tsa_pop_ts s' = tsa_pop_ts s ->
      session_protocol p' s' pi.
    Proof.
      intros Hsession H1 H2 H3 H4.
      unfold session_protocol in *.
      rewrite H1, H2, H3, H4. exact Hsession.
    Qed.

    Lemma session_protocol_retoken p s pi pi' actor :
      session_protocol p s pi ->
      TMap.find actor pi <> Some (ls_lini tsa_startPop) ->
      TMap.find actor pi' <> Some (ls_lini tsa_startPop) ->
      (forall a, a <> actor -> TMap.find a pi' = TMap.find a pi) ->
      session_protocol p s pi'.
    Proof.
      intros [H1 [H2 [H3 H4]]] Hold Hnew Hother.
      split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
      intro observer.
      destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
      - split.
        + intros Hopen. exfalso. exact (Hold (proj1 (H4 actor) Hopen)).
        + intros Hbad. exfalso. exact (Hnew Hbad).
      - rewrite Hother by exact Hneq. apply H4.
    Qed.

    Lemma session_protocol_keep p s pi p' s' pi' actor :
      session_protocol p s pi ->
      lp_pop_starts p' = lp_pop_starts p ->
      lp_pop_ts p' = lp_pop_ts p ->
      tsa_pop_starts s' = tsa_pop_starts s ->
      tsa_pop_ts s' = tsa_pop_ts s ->
      TMap.find actor pi <> Some (ls_lini tsa_startPop) ->
      TMap.find actor pi' <> Some (ls_lini tsa_startPop) ->
      (forall a, a <> actor -> TMap.find a pi' = TMap.find a pi) ->
      session_protocol p' s' pi'.
    Proof.
      intros Hsession H1 H2 H3 H4 Hold Hnew Hother.
      apply (session_protocol_retoken p' s' pi pi' actor);
        [|exact Hold|exact Hnew|exact Hother].
      exact (session_protocol_fields p s pi p' s' Hsession H1 H2 H3 H4).
    Qed.

    (** Closing the actor's session in the abstract state only. *)
    Lemma session_protocol_close p s pi p' s' pi' actor :
      session_protocol p s pi ->
      lp_pop_starts p' = lp_pop_starts p ->
      lp_pop_ts p' = lp_pop_ts p ->
      tsa_pop_starts s' = TMap.remove actor (tsa_pop_starts s) ->
      tsa_pop_ts s' = TMap.remove actor (tsa_pop_ts s) ->
      TMap.find actor pi' <> Some (ls_lini tsa_startPop) ->
      (forall a, a <> actor -> TMap.find a pi' = TMap.find a pi) ->
      session_protocol p' s' pi'.
    Proof.
      intros [H1 [H2 [H3 H4]]] Hp1 Hp2 Hstarts Hts Hnew Hother.
      unfold session_protocol. rewrite Hp1, Hp2, Hstarts, Hts.
      split.
      - intros observer N0 Hfind.
        destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
        + rewrite TMap.grs in Hfind. discriminate.
        + rewrite TMap.gro in Hfind by exact Hneq. now apply H1.
      - split.
        + intros observer ts Hfind.
          destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
          * rewrite TMap.grs in Hfind. discriminate.
          * rewrite TMap.gro in Hfind by exact Hneq. now apply H2.
        + split.
          * intros observer ts Hfind.
            destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
            -- rewrite TMap.grs in Hfind. discriminate.
            -- rewrite TMap.gro in Hfind by exact Hneq.
               rewrite TMap.gro by exact Hneq.
               now apply (H3 observer ts).
          * intro observer.
            destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
            -- repeat rewrite TMap.grs. split.
               ++ intros [_ [N0 Hbad]]. discriminate.
               ++ intro Hbad. exfalso. exact (Hnew Hbad).
            -- repeat rewrite TMap.gro by exact Hneq.
               rewrite Hother by exact Hneq. apply H4.
    Qed.

    Lemma protocols_add_inv p s pi actor op :
      snapshot_protocol p s pi -> session_protocol p s pi ->
      TMap.find actor pi = None ->
      snapshot_protocol p s (TMap.add actor (ls_inv op) pi) /\
      session_protocol p s (TMap.add actor (ls_inv op) pi).
    Proof.
      intros Hprotocol Hsession Hnone. split.
      - eapply snapshot_protocol_retoken; [exact Hprotocol| | | | |].
        + old_token_neq Hnone.
        + new_token_neq.
        + old_token_neq Hnone.
        + new_token_neq.
        + other_token.
      - eapply session_protocol_retoken; [exact Hsession| | |].
        + old_token_neq Hnone.
        + new_token_neq.
        + other_token.
    Qed.

    Lemma protocols_remove_linr p s pi actor op ret :
      snapshot_protocol p s pi -> session_protocol p s pi ->
      TMap.find actor pi = Some (ls_linr op ret) ->
      snapshot_protocol p s (TMap.remove actor pi) /\
      session_protocol p s (TMap.remove actor pi).
    Proof.
      intros Hprotocol Hsession Hlin. split.
      - eapply snapshot_protocol_retoken; [exact Hprotocol| | | | |].
        + old_token_neq Hlin.
        + intros start Hbad. rewrite TMap.grs in Hbad. discriminate.
        + old_token_neq Hlin.
        + intros v Hbad. rewrite TMap.grs in Hbad. discriminate.
        + other_token.
      - eapply session_protocol_retoken; [exact Hsession| | |].
        + old_token_neq Hlin.
        + intros Hbad. rewrite TMap.grs in Hbad. discriminate.
        + other_token.
    Qed.

    Lemma ginv_exposes_active actor op :
      forall out,
        AssertionsSingle.A.ComposeA source_I
          (AssertionsSingle.Ginv actor op) out ->
        Active actor op out.
    Proof.
      intros out [pre [HI Hginv]].
      unfold AssertionsSingle.Ginv, AssertionsSingle.LiftRelation_π in Hginv.
      destruct Hginv as [Hsigma [Hrho [Hnone Hpi]]].
      destruct HI as (s & Eρ & Hgraph & Hprotocol & Hsession & Howned).
      destruct (protocols_add_inv _ _ _ actor op Hprotocol Hsession Hnone)
        as [Hprotocol' Hsession'].
      split.
      - exists s. split; [rewrite <- Hrho; exact Eρ|]. split.
        + rewrite <- Hsigma. exact Hgraph.
        + split; [|split].
          * rewrite <- Hsigma, Hpi. exact Hprotocol'.
          * rewrite <- Hsigma, Hpi. exact Hsession'.
          * now rewrite <- Hsigma.
      - unfold AssertionsSingle.ALin. rewrite Hpi, TMap.gss. reflexivity.
    Qed.

    Lemma gret_closes_completed actor op ret :
      forall out,
        AssertionsSingle.A.ComposeA (Completed actor op ret)
          (AssertionsSingle.Gret actor op ret) out ->
        source_I out.
    Proof.
      intros out [pre [[HI Hlin] Hgret]].
      unfold AssertionsSingle.Gret, AssertionsSingle.LiftRelation_π in Hgret.
      destruct Hgret as [Hsigma [Hrho [Hfind Hpi]]].
      destruct HI as (s & Eρ & Hgraph & Hprotocol & Hsession & Howned).
      destruct (protocols_remove_linr _ _ _ actor op ret
        Hprotocol Hsession Hfind) as [Hprotocol' Hsession'].
      exists s. split; [rewrite <- Hrho; exact Eρ|]. split.
      - rewrite <- Hsigma. exact Hgraph.
      - split; [|split].
        + rewrite <- Hsigma, Hpi. exact Hprotocol'.
        + rewrite <- Hsigma, Hpi. exact Hsession'.
        + now rewrite <- Hsigma.
    Qed.

    Lemma set_ginv_exposes_active actor op :
      forall w,
        AssertionsSet.A.ComposeA SI (AssertionsSet.Ginv actor op) w ->
        SActive actor op w.
    Proof. eapply lift_ginv_compose. apply ginv_exposes_active. Qed.

    Lemma set_gret_closes_completed actor op ret :
      forall w,
        AssertionsSet.A.ComposeA (SCompleted actor op ret)
          (AssertionsSet.Gret actor op ret) w -> SI w.
    Proof. eapply lift_gret_compose. apply gret_closes_completed. Qed.

    Lemma completed_has_return_token actor op ret :
      forall w, SCompleted actor op ret w ->
      forall rho pi, SetPossState.Δ w rho pi ->
        TMap.find actor pi = Some (ls_linr op ret).
    Proof.
      eapply lift_post_lin. intros x [_ Hlin]. exact Hlin.
    Qed.

    Lemma graph_represents_is_vertex p s n :
      graph_represents p s -> is_vertex p n <-> tsa_is_vertex s n.
    Proof.
      intros [Hvertices _]. unfold is_vertex, tsa_is_vertex.
      now rewrite <- Hvertices.
    Qed.

    Lemma graph_represents_is_pending p s n :
      graph_represents p s -> is_pending p n <-> tsa_is_pending s n.
    Proof.
      intros [_ [_ [Hpending _]]]. unfold is_pending, tsa_is_pending.
      now rewrite <- Hpending.
    Qed.

    Lemma graph_represents_is_live p s n :
      graph_represents p s -> is_live p n <-> tsa_is_live s n.
    Proof.
      intros Hrep. unfold is_live, tsa_is_live.
      rewrite <- (graph_represents_is_vertex p s n Hrep).
      destruct Hrep as [_ [_ [_ Hgarbage]]]. now rewrite <- Hgarbage.
    Qed.

    Lemma graph_represents_fresh p s n :
      graph_represents p s -> fresh_node p n <-> tsa_fresh_node s n.
    Proof.
      intros [Hvertices [_ [_ Hgarbage]]].
      unfold fresh_node, tsa_fresh_node.
      now rewrite <- Hvertices, <- Hgarbage.
    Qed.

    Lemma completed_set_represents p s :
      graph_represents p s -> completed_set p = tsa_completed_set s.
    Proof.
      intros Hrep. apply functional_extensionality; intro n.
      apply propositional_extensionality.
      unfold completed_set, tsa_completed_set.
      rewrite (graph_represents_is_vertex p s n Hrep).
      rewrite (graph_represents_is_pending p s n Hrep).
      tauto.
    Qed.

    Lemma graph_represents_start_push p s actor loc (v : A) :
      graph_represents p s ->
      graph_represents (start_push actor loc v p)
        (tsa_start_push actor loc v s).
    Proof.
      intros Hrep. destruct Hrep as [HV [HE [HP HG]]].
      unfold graph_represents, start_push, tsa_start_push; simpl.
      split.
      - now rewrite HV.
      - split.
        + apply functional_extensionality; intro newer.
          apply functional_extensionality; intro older.
          rewrite HE.
          unfold is_vertex, tsa_is_vertex, is_pending, tsa_is_pending.
          now rewrite <- HV, <- HP.
        + split; [now rewrite HP|now rewrite HG].
    Qed.

    Lemma graph_represents_finish_push p s actor :
      graph_represents p s ->
      graph_represents (finish_push actor p) (tsa_finish_push actor s).
    Proof.
      intros [HV [HE [HP HG]]].
      unfold graph_represents, finish_push, tsa_finish_push; simpl.
      now rewrite HV, HE, HP, HG.
    Qed.

    Lemma graph_represents_start_snapshot p s actor :
      graph_represents p s ->
      graph_represents (start_snapshot actor p) (tsa_start_snapshot actor s).
    Proof.
      unfold graph_represents, start_snapshot, tsa_start_snapshot; simpl.
      tauto.
    Qed.

    Lemma graph_represents_clear_concrete_snapshot p s actor :
      graph_represents p s ->
      graph_represents (clear_snapshot actor p) s.
    Proof.
      unfold graph_represents, clear_snapshot; simpl. tauto.
    Qed.

    Lemma graph_represents_clear_abstract_snapshot p s actor :
      graph_represents p s ->
      graph_represents p (tsa_clear_snapshot actor s).
    Proof.
      unfold graph_represents, tsa_clear_snapshot; simpl. tauto.
    Qed.

    Lemma graph_represents_mark_garbage p s actor n :
      graph_represents p s ->
      graph_represents (mark_garbage n p) (tsa_remove_node actor n s).
    Proof.
      intros [HV [HE [HP HG]]].
      unfold graph_represents, mark_garbage, tsa_remove_node; simpl.
      now rewrite HV, HE, HP, HG.
    Qed.

    Lemma graph_represents_start_pop_session p s actor :
      graph_represents p s ->
      graph_represents (start_pop_session actor p)
        (tsa_start_pop_session actor s).
    Proof.
      unfold graph_represents, start_pop_session, tsa_start_pop_session;
        simpl. tauto.
    Qed.

    Lemma graph_represents_finish_pop_session p s actor ts :
      graph_represents p s ->
      graph_represents (finish_pop_session actor ts p)
        (tsa_finish_pop_session actor ts s).
    Proof.
      unfold graph_represents, finish_pop_session, tsa_finish_pop_session;
        simpl. tauto.
    Qed.

    Lemma graph_represents_close_session p s actor :
      graph_represents p s ->
      graph_represents p (tsa_close_session actor s).
    Proof.
      unfold graph_represents, tsa_close_session; simpl. tauto.
    Qed.

    Lemma graph_evol_refl p : graph_evol p p.
    Proof. unfold graph_evol; repeat split; auto. Qed.

    Lemma graph_evol_start_push actor loc (v : A) p :
      fresh_node p (pair actor loc) ->
      graph_evol p (start_push actor loc v p).
    Proof.
      intros [Hfresh _]. unfold graph_evol. split.
      - intros n value Hvalue. unfold start_push; simpl.
        destruct (node_eq_dec (pair actor loc) n) as [Heq|Hneq].
        + subst n. rewrite Hfresh in Hvalue. discriminate.
        + now rewrite node_update_neq.
      - split.
        + intros newer older Hvertex. unfold start_push; simpl. split.
          * now left.
          * intros [Hedge|[Heq _]]; [exact Hedge|]. subst newer.
            unfold is_vertex in Hvertex. rewrite Hfresh in Hvertex.
            contradiction.
        + auto.
    Qed.

    Lemma graph_evol_mark_garbage p n :
      graph_evol p (mark_garbage n p).
    Proof.
      unfold graph_evol, mark_garbage, set_add; simpl.
      repeat split; auto.
    Qed.

    Lemma graph_evol_finish_push p actor :
      graph_evol p (finish_push actor p).
    Proof.
      unfold graph_evol, finish_push; simpl. repeat split; auto.
    Qed.

    Lemma graph_evol_start_snapshot p actor :
      graph_evol p (start_snapshot actor p).
    Proof.
      unfold graph_evol, start_snapshot; simpl. repeat split; auto.
    Qed.

    Lemma graph_evol_clear_snapshot p actor :
      graph_evol p (clear_snapshot actor p).
    Proof.
      unfold graph_evol, clear_snapshot; simpl. repeat split; auto.
    Qed.

    Lemma graph_evol_start_pop_session p actor :
      graph_evol p (start_pop_session actor p).
    Proof.
      unfold graph_evol, start_pop_session; simpl. repeat split; auto.
    Qed.

    Lemma graph_evol_finish_pop_session p actor ts :
      graph_evol p (finish_pop_session actor ts p).
    Proof.
      unfold graph_evol, finish_pop_session; simpl. repeat split; auto.
    Qed.

    Lemma snapshot_protocol_push_inv p s pi actor loc (v : A) :
      snapshot_protocol p s pi ->
      TMap.find actor pi = Some (ls_inv (tsa_push v)) ->
      TMap.find actor (tsa_pending_pushes s) = None ->
      snapshot_protocol (start_push actor loc v p)
        (tsa_start_push actor loc v s)
        (TMap.add actor (ls_lini (tsa_push v)) pi).
    Proof.
      intros [Hconcrete [Hsnapshot [Hpush Hwf]]] Htoken Hnone.
      unfold snapshot_protocol, start_push, tsa_start_push; simpl.
      split; [exact Hconcrete|]. split.
      - intro observer.
        destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
        + rewrite TMap.gss. split.
          * intros [N Hfind].
            destruct (proj1 (Hsnapshot actor) (ex_intro _ N Hfind))
              as [start Hbad]. rewrite Htoken in Hbad. discriminate.
          * intros [start Hbad]. discriminate.
        + rewrite TMap.gso by exact Hneq. apply Hsnapshot.
      - split.
        + intro observer.
          destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
          * repeat rewrite TMap.gss. split.
            -- intros _. exists v. reflexivity.
            -- intros _. exists loc. reflexivity.
          * repeat rewrite TMap.gso by exact Hneq. apply Hpush.
        + intros observer N Hfind n Hmember.
          simpl in Hfind. specialize (Hwf observer N Hfind n Hmember).
          unfold tsa_is_vertex in *. simpl.
          unfold node_update.
          destruct (node_eq_dec (pair actor loc) n); [discriminate|exact Hwf].
    Qed.

    Lemma snapshot_protocol_push_res p s pi actor loc (v : A) :
      snapshot_protocol p s pi ->
      TMap.find actor pi = Some (ls_lini (tsa_push v)) ->
      TMap.find actor (tsa_pending_pushes s) = Some loc ->
      snapshot_protocol (finish_push actor p)
        (tsa_finish_push actor s)
        (TMap.add actor (ls_linr (tsa_push v) tt) pi).
    Proof.
      intros [Hconcrete [Hsnapshot [Hpush Hwf]]] Htoken Hpending.
      unfold snapshot_protocol, finish_push, tsa_finish_push; simpl.
      split; [exact Hconcrete|]. split.
      - intro observer.
        destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
        + rewrite TMap.gss. split.
          * intros [N Hfind].
            destruct (proj1 (Hsnapshot actor) (ex_intro _ N Hfind))
              as [start Hbad]. rewrite Htoken in Hbad. discriminate.
          * intros [start Hbad]. discriminate.
        + rewrite TMap.gso by exact Hneq. apply Hsnapshot.
      - split.
        + intro observer.
          destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
          * rewrite TMap.grs, TMap.gss. split.
            -- intros [loc' Hfind]. discriminate.
            -- intros [value Hbad]. discriminate.
          * rewrite TMap.gro, TMap.gso by exact Hneq. apply Hpush.
        + exact Hwf.
    Qed.

    (** The session protocol across a lock-step [startPop]. *)
    Lemma session_protocol_startPop_inv p s pi actor :
      graph_represents p s -> session_protocol p s pi ->
      TMap.find actor pi = Some (ls_inv tsa_startPop) ->
      session_protocol (start_pop_session actor p)
        (tsa_start_pop_session actor s)
        (TMap.add actor (ls_lini tsa_startPop) pi).
    Proof.
      intros Hrep [H1 [H2 [H3 H4]]] Htoken.
      unfold session_protocol, start_pop_session, tsa_start_pop_session;
        simpl.
      split.
      - intros observer N0 Hfind.
        destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
        + rewrite TMap.gss in Hfind. rewrite TMap.gss. rewrite <- Hfind.
          f_equal. now apply completed_set_represents.
        + rewrite TMap.gso in Hfind by exact Hneq.
          rewrite TMap.gso by exact Hneq. now apply H1.
      - split.
        + intros observer ts Hfind.
          destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
          * rewrite TMap.grs in Hfind. discriminate.
          * rewrite TMap.gro in Hfind by exact Hneq.
            rewrite TMap.gro by exact Hneq. now apply H2.
        + split.
          * intros observer ts Hfind.
            destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
            -- rewrite TMap.grs in Hfind. discriminate.
            -- rewrite TMap.gro in Hfind by exact Hneq.
               rewrite TMap.gso by exact Hneq. now apply (H3 observer ts).
          * intro observer.
            destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
            -- rewrite TMap.grs. repeat rewrite TMap.gss. split.
               ++ intros _. reflexivity.
               ++ intros _. split; [reflexivity|]. eexists. reflexivity.
            -- rewrite TMap.gro by exact Hneq.
               repeat rewrite TMap.gso by exact Hneq. apply H4.
    Qed.

    Lemma session_protocol_startPop_res p s pi actor ts :
      session_protocol p s pi ->
      TMap.find actor pi = Some (ls_lini tsa_startPop) ->
      session_protocol (finish_pop_session actor ts p)
        (tsa_finish_pop_session actor ts s)
        (TMap.add actor (ls_linr tsa_startPop ts) pi).
    Proof.
      intros [H1 [H2 [H3 H4]]] Htoken.
      unfold session_protocol, finish_pop_session, tsa_finish_pop_session;
        simpl.
      split; [exact H1|]. split.
      - intros observer ts' Hfind.
        destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
        + rewrite TMap.gss in Hfind. rewrite TMap.gss. exact Hfind.
        + rewrite TMap.gso in Hfind by exact Hneq.
          rewrite TMap.gso by exact Hneq. now apply H2.
      - split.
        + intros observer ts' Hfind.
          destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
          * destruct (proj2 (H4 actor) Htoken) as [_ Hstarts]. exact Hstarts.
          * rewrite TMap.gso in Hfind by exact Hneq.
            now apply (H3 observer ts').
        + intro observer.
          destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
          * repeat rewrite TMap.gss. split.
            -- intros [Hbad _]. discriminate.
            -- intro Hbad. discriminate.
          * repeat rewrite TMap.gso by exact Hneq. apply H4.
    Qed.

    (** Push. *)

    Definition PushInside actor (v : A) : assertion :=
      fun w => Active actor (tsa_push v) w /\
        ThreadDomain.contains D actor.

    Definition PushPending actor (v : A) : assertion :=
      fun w => source_I w /\
        AssertionsSingle.ALin actor (ls_lini (tsa_push v)) w /\
        ThreadDomain.contains D actor.

    Lemma push_inside_entails_I actor v :
      ⊨ PushInside actor v ==>> source_I.
    Proof. firstorder. Qed.

    Lemma push_pending_entails_I actor v :
      ⊨ PushPending actor v ==>> source_I.
    Proof. firstorder. Qed.

    Lemma push_inside_stable actor v :
      AssertionsSingle.A.Stable (source_R actor) source_I
        (PushInside actor v).
    Proof.
      unfold AssertionsSingle.A.Stable, PushInside.
      intros out [[pre [[[HI Htoken] Hinside] HR]] HIout].
      split; [|exact Hinside]. split; [exact HIout|].
      unfold AssertionsSingle.ALin in *.
      rewrite <- (source_R_token actor _ _ HR). exact Htoken.
    Qed.

    Lemma push_pending_stable actor v :
      AssertionsSingle.A.Stable (source_R actor) source_I
        (PushPending actor v).
    Proof.
      unfold AssertionsSingle.A.Stable, PushPending.
      intros out [[pre [[HI [Htoken Hinside]] HR]] HIout].
      split; [exact HIout|]. split; [|exact Hinside].
      pose proof (source_R_token actor _ _ HR) as Heq.
      unfold token_eq in Heq.
      unfold AssertionsSingle.ALin in Htoken |- *.
      exact (eq_trans (eq_sym Heq) Htoken).
    Qed.

    Lemma push_inv_update actor (v : A) :
      AssertionsSingle.PUpdate (source_G actor)
        (Build_ThreadEvent actor (InvEv (lpool_push v)))
        (PushInside actor v) (PushPending actor v).
    Proof.
      pupdate_intros_atomic.
      destruct Hpre as [[HIpre Htoken] Hinside].
      pose proof HIpre as HIpre0.
      destruct HIpre as (a & Hrho & Hgraph & Hprotocol & Hsession & Howned).
      simpl in Hrho. subst ρ1.
      assert (Hpending :
        TMap.find actor0 (tsa_pending_pushes a) = None).
      { destruct Hgraph as [_ [_ [HP _]]]. now rewrite <- HP. }
      assert (Hfresh : tsa_fresh_node a (pair actor0 loc)).
      { apply (proj1 (graph_represents_fresh s a (pair actor0 loc) Hgraph)).
        assumption. }
      exists (TSAReady (tsa_start_push actor0 loc v0 a)),
        (TMap.add actor0 (ls_lini (tsa_push v0)) π1).
      split.
      - apply rt_step. eapply ps_inv.
        + eapply step_tsa_push_inv; eauto.
        + exact Htoken.
      - assert (HIpost : source_I
          (@SinglePossState.Build_ProofStateSingle _ _
            (li_lts E) (li_lts F)
            (LPReady (start_push actor0 loc v0 s))
            (TSAReady (tsa_start_push actor0 loc v0 a))
            (TMap.add actor0 (ls_lini (tsa_push v0)) π1))).
        { exists (tsa_start_push actor0 loc v0 a). split; [reflexivity|].
          split.
          - now apply graph_represents_start_push.
          - split; [|split].
            + eapply snapshot_protocol_push_inv; eauto.
            + eapply session_protocol_keep;
                [exact Hsession|reflexivity|reflexivity|reflexivity|
                 reflexivity| | |].
              * old_token_neq Htoken.
              * new_token_neq.
              * other_token.
            + eapply vertices_owned_start_push; eauto. }
        split.
        + unfold PushPending. split; [exact HIpost|]. split.
          * unfold AssertionsSingle.ALin. simpl. apply TMap.gss.
          * exact Hinside.
        + unfold source_G.
          refine (conj _ (conj _ (conj _ (conj _ _)))).
          * exact HIpre0.
          * exact HIpost.
          * now apply graph_evol_start_push.
          * intros observer Hneq. unfold actor_local_eq; simpl.
            repeat split; try reflexivity;
              rewrite TMap.gso by congruence; reflexivity.
          * exact Logic.I.
    Qed.

    Lemma push_res_update actor (v : A) :
      AssertionsSingle.PUpdate (source_G actor)
        (Build_ThreadEvent actor (ResEv (lpool_push v) tt))
        (PushPending actor v) (Completed actor (tsa_push v) tt).
    Proof.
      pupdate_intros_atomic.
      destruct Hpre as [HIpre [Htoken Hinside]].
      pose proof HIpre as HIpre0.
      destruct HIpre as (a & Hrho & Hgraph & Hprotocol & Hsession & Howned).
      simpl in Hrho. subst ρ1.
      assert (Hpending :
        TMap.find actor0 (tsa_pending_pushes a) = Some loc).
      { destruct Hgraph as [_ [_ [HP _]]]. now rewrite <- HP. }
      exists (TSAReady (tsa_finish_push actor0 a)),
        (TMap.add actor0 (ls_linr (tsa_push v0) tt) π1).
      split.
      - apply rt_step. eapply ps_ret.
        + eapply step_tsa_push_res; eauto.
        + exact Htoken.
      - assert (HIpost : source_I
          (@SinglePossState.Build_ProofStateSingle _ _
            (li_lts E) (li_lts F)
            (LPReady (finish_push actor0 s))
            (TSAReady (tsa_finish_push actor0 a))
            (TMap.add actor0 (ls_linr (tsa_push v0) tt) π1))).
        { exists (tsa_finish_push actor0 a). split; [reflexivity|]. split.
          - now apply graph_represents_finish_push.
          - split; [|split].
            + eapply snapshot_protocol_push_res; eauto.
            + eapply session_protocol_keep;
                [exact Hsession|reflexivity|reflexivity|reflexivity|
                 reflexivity| | |].
              * old_token_neq Htoken.
              * new_token_neq.
              * other_token.
            + now apply vertices_owned_finish_push. }
        split.
        + split; [exact HIpost|].
          unfold AssertionsSingle.ALin. simpl. apply TMap.gss.
        + unfold source_G.
          refine (conj _ (conj _ (conj _ (conj _ _)))).
          * exact HIpre0.
          * exact HIpost.
          * apply graph_evol_finish_push.
          * intros observer Hneq. unfold actor_local_eq; simpl.
            repeat split; try reflexivity;
              rewrite ?TMap.gro, ?TMap.gso by congruence; reflexivity.
          * exact Logic.I.
    Qed.

    Lemma push_inside_no_error actor (v : A) :
      ⊨ PushInside actor v ==>>
        AssertionsSingle.A.ANoError
          (Build_ThreadEvent actor (InvEv (lpool_push v))).
    Proof.
      intros [sigma rho pi] [[HI Htoken] Hinside] Herror.
      simpl in Herror. remember
        (Build_ThreadEvent actor (InvEv (lpool_push v))) as ev eqn:Hev
        in Herror.
      inversion Herror; subst; try contradiction.
      all: inversion_thread_event_eq.
      contradiction.
    Qed.

    Lemma push_active_or_error actor (v : A) w :
      SActive actor (tsa_push v) w ->
      lift_assert (PushInside actor v) w \/ AssertionsSet.APError w.
    Proof.
      intros [x [Hview [HI Htoken]]].
      destruct (ThreadDomain.contains_dec D actor) as [Hinside|Houtside].
      - left. exists x. split; [exact Hview|].
        split; [split; assumption|exact Hinside].
      - right. destruct w as [sigma Delta].
        destruct HI as (s & Hrho & _).
        econstructor.
        + eapply singleton_view_member; eauto.
        + apply rt_step. eapply (ps_error actor (tsa_push v)).
          * rewrite Hrho.
            eapply error_tsa_actor_outside; [exact Houtside|reflexivity].
          * exact Htoken.
    Qed.

    Lemma push_method_triple actor (v : A) :
      SetLogic.HTripleProvable (R actor) (G actor) SI actor
        (SActive actor (tsa_push v))
        (push_impl D v actor)
        (fun ret => SCompleted actor (tsa_push v) ret).
    Proof.
      eapply SetLogic.provable_perror with
        (P' := lift_assert (PushInside actor v)).
      - intros w Hactive. now apply push_active_or_error.
      - unfold push_impl.
        eapply singleton_provable_vis_safe with
          (P' := PushPending actor v)
          (Q' := fun _ => Completed actor (tsa_push v) tt).
        + apply push_inside_no_error.
        + apply push_pending_entails_I.
        + intros []. apply completed_entails_I.
        + apply push_pending_stable.
        + intros []. apply completed_stable.
        + apply push_inv_update.
        + intros []. apply push_res_update.
        + intros []. eapply singleton_provable_ret_safe.
          * apply ImplRefl.
          * apply completed_entails_I.
          * apply completed_stable.
    Qed.

    (** startPop: a lock-step pass-through. *)

    Definition StartPopInside actor : assertion :=
      fun w => Active actor tsa_startPop w /\
        ThreadDomain.contains D actor.

    Definition StartPopPending actor : assertion :=
      fun w => source_I w /\
        AssertionsSingle.ALin actor (ls_lini tsa_startPop) w /\
        ThreadDomain.contains D actor.

    Lemma startPop_inside_entails_I actor :
      ⊨ StartPopInside actor ==>> source_I.
    Proof. firstorder. Qed.

    Lemma startPop_pending_entails_I actor :
      ⊨ StartPopPending actor ==>> source_I.
    Proof. firstorder. Qed.

    Lemma startPop_inside_stable actor :
      AssertionsSingle.A.Stable (source_R actor) source_I
        (StartPopInside actor).
    Proof.
      unfold AssertionsSingle.A.Stable, StartPopInside.
      intros out [[pre [[[HI Htoken] Hinside] HR]] HIout].
      split; [|exact Hinside]. split; [exact HIout|].
      unfold AssertionsSingle.ALin in *.
      rewrite <- (source_R_token actor _ _ HR). exact Htoken.
    Qed.

    Lemma startPop_pending_stable actor :
      AssertionsSingle.A.Stable (source_R actor) source_I
        (StartPopPending actor).
    Proof.
      unfold AssertionsSingle.A.Stable, StartPopPending.
      intros out [[pre [[HI [Htoken Hinside]] HR]] HIout].
      split; [exact HIout|]. split; [|exact Hinside].
      pose proof (source_R_token actor _ _ HR) as Heq.
      unfold token_eq in Heq.
      unfold AssertionsSingle.ALin in Htoken |- *.
      exact (eq_trans (eq_sym Heq) Htoken).
    Qed.

    Lemma startPop_inv_update actor :
      AssertionsSingle.PUpdate (source_G actor)
        (Build_ThreadEvent actor (InvEv lpool_startPop))
        (StartPopInside actor) (StartPopPending actor).
    Proof.
      pupdate_intros_atomic.
      destruct Hpre as [[HIpre Htoken] Hinside].
      pose proof HIpre as HIpre0.
      destruct HIpre as (a & Hrho & Hgraph & Hprotocol & Hsession & Howned).
      simpl in Hrho. subst ρ1.
      exists (TSAReady (tsa_start_pop_session actor0 a)),
        (TMap.add actor0 (ls_lini tsa_startPop) π1).
      split.
      - apply rt_step. eapply ps_inv.
        + eapply step_tsa_startPop_inv; reflexivity.
        + exact Htoken.
      - assert (HIpost : source_I
          (@SinglePossState.Build_ProofStateSingle _ _
            (li_lts E) (li_lts F)
            (LPReady (start_pop_session actor0 s))
            (TSAReady (tsa_start_pop_session actor0 a))
            (TMap.add actor0 (ls_lini tsa_startPop) π1))).
        { exists (tsa_start_pop_session actor0 a). split; [reflexivity|].
          split.
          - now apply graph_represents_start_pop_session.
          - split; [|split].
            + eapply snapshot_protocol_keep;
                [exact Hprotocol|reflexivity|reflexivity|reflexivity|
                 reflexivity| | | | |].
              * old_token_neq Htoken.
              * new_token_neq.
              * old_token_neq Htoken.
              * new_token_neq.
              * other_token.
            + eapply session_protocol_startPop_inv; eauto.
            + now apply vertices_owned_start_pop_session. }
        split.
        + unfold StartPopPending. split; [exact HIpost|]. split.
          * unfold AssertionsSingle.ALin. simpl. apply TMap.gss.
          * exact Hinside.
        + unfold source_G.
          refine (conj _ (conj _ (conj _ (conj _ _)))).
          * exact HIpre0.
          * exact HIpost.
          * apply graph_evol_start_pop_session.
          * intros observer Hneq. unfold actor_local_eq; simpl.
            repeat split; try reflexivity;
              rewrite ?TMap.gro, ?TMap.gso by congruence; reflexivity.
          * exact Logic.I.
    Qed.

    Lemma startPop_res_update actor ts :
      AssertionsSingle.PUpdate (source_G actor)
        (Build_ThreadEvent actor (ResEv lpool_startPop ts))
        (StartPopPending actor) (Completed actor tsa_startPop ts).
    Proof.
      pupdate_intros_atomic.
      destruct Hpre as [HIpre [Htoken Hinside]].
      pose proof HIpre as HIpre0.
      destruct HIpre as (a & Hrho & Hgraph & Hprotocol & Hsession & Howned).
      simpl in Hrho. subst ρ1.
      match goal with
      | |- context [finish_pop_session _ ?t _] => set (tsv := t) in *
      end.
      exists (TSAReady (tsa_finish_pop_session actor0 tsv a)),
        (TMap.add actor0 (ls_linr tsa_startPop tsv) π1).
      split.
      - apply rt_step. eapply ps_ret.
        + eapply step_tsa_startPop_res; reflexivity.
        + exact Htoken.
      - assert (HIpost : source_I
          (@SinglePossState.Build_ProofStateSingle _ _
            (li_lts E) (li_lts F)
            (LPReady (finish_pop_session actor0 tsv s))
            (TSAReady (tsa_finish_pop_session actor0 tsv a))
            (TMap.add actor0 (ls_linr tsa_startPop tsv) π1))).
        { exists (tsa_finish_pop_session actor0 tsv a).
          split; [reflexivity|]. split.
          - now apply graph_represents_finish_pop_session.
          - split; [|split].
            + eapply snapshot_protocol_keep;
                [exact Hprotocol|reflexivity|reflexivity|reflexivity|
                 reflexivity| | | | |].
              * old_token_neq Htoken.
              * new_token_neq.
              * old_token_neq Htoken.
              * new_token_neq.
              * other_token.
            + eapply session_protocol_startPop_res; eauto.
            + now apply vertices_owned_finish_pop_session. }
        split.
        + split; [exact HIpost|].
          unfold AssertionsSingle.ALin. simpl. apply TMap.gss.
        + unfold source_G.
          refine (conj _ (conj _ (conj _ (conj _ _)))).
          * exact HIpre0.
          * exact HIpost.
          * apply graph_evol_finish_pop_session.
          * intros observer Hneq. unfold actor_local_eq; simpl.
            repeat split; try reflexivity;
              rewrite ?TMap.gro, ?TMap.gso by congruence; reflexivity.
          * exact Logic.I.
    Qed.

    Lemma startPop_inside_no_error actor :
      ⊨ StartPopInside actor ==>>
        AssertionsSingle.A.ANoError
          (Build_ThreadEvent actor (InvEv lpool_startPop)).
    Proof.
      intros [sigma rho pi] [[HI Htoken] Hinside] Herror.
      simpl in Herror. remember
        (Build_ThreadEvent actor (InvEv lpool_startPop)) as ev eqn:Hev
        in Herror.
      inversion Herror; subst; try contradiction.
      all: inversion_thread_event_eq.
      contradiction.
    Qed.

    Lemma startPop_active_or_error actor w :
      SActive actor tsa_startPop w ->
      lift_assert (StartPopInside actor) w \/ AssertionsSet.APError w.
    Proof.
      intros [x [Hview [HI Htoken]]].
      destruct (ThreadDomain.contains_dec D actor) as [Hinside|Houtside].
      - left. exists x. split; [exact Hview|].
        split; [split; assumption|exact Hinside].
      - right. destruct w as [sigma Delta].
        destruct HI as (s & Hrho & _).
        econstructor.
        + eapply singleton_view_member; eauto.
        + apply rt_step. eapply (ps_error actor tsa_startPop).
          * rewrite Hrho.
            eapply error_tsa_actor_outside; [exact Houtside|reflexivity].
          * exact Htoken.
    Qed.

    Lemma startPop_method_triple actor :
      SetLogic.HTripleProvable (R actor) (G actor) SI actor
        (SActive actor tsa_startPop)
        (startPop_impl D actor)
        (fun ret => SCompleted actor tsa_startPop ret).
    Proof.
      eapply SetLogic.provable_perror with
        (P' := lift_assert (StartPopInside actor)).
      - intros w Hactive. now apply startPop_active_or_error.
      - unfold startPop_impl.
        eapply singleton_provable_vis_safe with
          (P' := StartPopPending actor)
          (Q' := fun ts => Completed actor tsa_startPop ts).
        + apply startPop_inside_no_error.
        + apply startPop_pending_entails_I.
        + intros ts. apply completed_entails_I.
        + apply startPop_pending_stable.
        + intros ts. apply completed_stable.
        + apply startPop_inv_update.
        + intros ts. apply startPop_res_update.
        + intros ts. eapply singleton_provable_ret_safe.
          * apply ImplRefl.
          * apply completed_entails_I.
          * apply completed_stable.
    Qed.

    (** Rely facts. *)

    Definition local_eq_relation (observer : tid) : rg_relation :=
      actor_local_eq observer.

    Lemma source_G_local_other actor observer :
      actor <> observer ->
      (source_G actor ⊆ local_eq_relation observer)%RGRelation.
    Proof. intros Hneq w w' [_ [_ [_ [Hlocal _]]]]. now apply Hlocal. Qed.

    Lemma observer_view_local observer :
      (AssertionsSingle.ObserverViewEq observer ⊆
        local_eq_relation observer)%RGRelation.
    Proof.
      intros w w' [Hsigma [Hrho Htoken]].
      unfold local_eq_relation, actor_local_eq.
      now rewrite Hsigma, Hrho, Htoken.
    Qed.

    Lemma source_R_local observer :
      (source_R observer ⊆ local_eq_relation observer)%RGRelation.
    Proof.
      eapply AssertionsSingle.guarantee_generated_rely_facts.
      - intros actor Hneq. now apply source_G_local_other.
      - apply observer_view_local.
    Qed.

    Definition graph_evol_relation : rg_relation :=
      fun w w' => graph_evol
        (concrete_payload (SinglePossState.σ w))
        (concrete_payload (SinglePossState.σ w')).

    Definition graph_evol_facts (_ : tid) : rg_relation :=
      graph_evol_relation.

    Lemma source_G_graph_evol actor :
      (source_G actor ⊆ graph_evol_relation)%RGRelation.
    Proof. intros w w' [_ [_ [Hevol _]]]. exact Hevol. Qed.

    Lemma observer_view_graph_evol observer :
      (AssertionsSingle.ObserverViewEq observer ⊆
        graph_evol_relation)%RGRelation.
    Proof.
      intros w w' [Hsigma _]. unfold graph_evol_relation.
      rewrite Hsigma. apply graph_evol_refl.
    Qed.

    Lemma source_R_graph_evol observer :
      (source_R observer ⊆ graph_evol_facts observer)%RGRelation.
    Proof.
      eapply AssertionsSingle.guarantee_generated_rely_facts.
      - intros actor Hneq. exact (source_G_graph_evol actor).
      - exact (observer_view_graph_evol observer).
    Qed.

    (** Snapshot protocol across the trypop steps. *)

    Lemma snapshot_protocol_snapshot_inv p s pi actor start :
      graph_represents p s -> snapshot_protocol p s pi ->
      TMap.find actor pi = Some (ls_inv (tsa_trypop start)) ->
      TMap.find actor (lp_snapshots p) = None ->
      TMap.find actor (tsa_snapshots s) = None ->
      snapshot_protocol (start_snapshot actor p)
        (tsa_start_snapshot actor s)
        (TMap.add actor (ls_lini (tsa_trypop start)) pi).
    Proof.
      intros Hgraph [Hconcrete [Hsnapshot [Hpush Hwf]]] Htoken Hcp Has.
      unfold snapshot_protocol, start_snapshot, tsa_start_snapshot; simpl.
      split.
      - intros observer N Hfind.
        destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
        + rewrite TMap.gss in Hfind. inversion Hfind; subst N.
          rewrite TMap.gss. f_equal. apply functional_extensionality.
          intro n. apply propositional_extensionality.
          symmetry. now apply graph_represents_is_vertex.
        + rewrite TMap.gso in Hfind by exact Hneq.
          rewrite TMap.gso by exact Hneq. now apply Hconcrete.
      - split.
        + intro observer.
          destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
          * rewrite TMap.gss, TMap.gss. split.
            -- intros _. exists start. reflexivity.
            -- intros _. eexists. reflexivity.
          * repeat rewrite TMap.gso by exact Hneq. apply Hsnapshot.
        + split.
          * intro observer.
            destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
            -- rewrite TMap.gss. split.
               ++ intros [loc Hfind].
                  destruct (proj1 (Hpush actor) (ex_intro _ loc Hfind))
                    as [v Hbad]. rewrite Htoken in Hbad. discriminate.
               ++ intros [v Hbad]. discriminate.
            -- rewrite TMap.gso by exact Hneq. apply Hpush.
          * intros observer N Hfind n Hmember.
            destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
            -- rewrite TMap.gss in Hfind. inversion Hfind; subst N.
               exact Hmember.
            -- rewrite TMap.gso in Hfind by exact Hneq.
               now apply (Hwf observer N Hfind n Hmember).
    Qed.

    Lemma snapshot_protocol_clear_concrete p s pi actor :
      snapshot_protocol p s pi ->
      snapshot_protocol (clear_snapshot actor p) s pi.
    Proof.
      intros [Hconcrete [Hsnapshot [Hpush Hwf]]].
      unfold snapshot_protocol, clear_snapshot; simpl.
      split.
      - intros observer N Hfind.
        destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
        + rewrite TMap.grs in Hfind. discriminate.
        + rewrite TMap.gro in Hfind by exact Hneq. now apply Hconcrete.
      - split; [exact Hsnapshot|]. split; assumption.
    Qed.

    Lemma snapshot_protocol_atomic_same p s pi actor start ret :
      snapshot_protocol p s pi ->
      TMap.find actor pi = Some (ls_inv (tsa_trypop start)) ->
      TMap.find actor (lp_snapshots p) = None ->
      TMap.find actor (tsa_snapshots s) = None ->
      snapshot_protocol p s
        (TMap.add actor (ls_linr (tsa_trypop start) ret)
          (TMap.add actor (ls_lini (tsa_trypop start)) pi)).
    Proof.
      intros [Hconcrete [Hsnapshot [Hpush Hwf]]] Htoken Hcp Has.
      unfold snapshot_protocol. split; [exact Hconcrete|]. split.
      - intro observer.
        destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
        + repeat rewrite TMap.gss. split.
          * intros [N Hfind]. rewrite Has in Hfind. discriminate.
          * intros [st Hbad]. discriminate.
        + repeat rewrite TMap.gso by exact Hneq. apply Hsnapshot.
      - split.
        + intro observer.
          destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
          * repeat rewrite TMap.gss. split.
            -- intros [loc Hfind].
               destruct (proj1 (Hpush actor) (ex_intro _ loc Hfind))
                 as [v Hbad]. rewrite Htoken in Hbad. discriminate.
            -- intros [v Hbad]. discriminate.
          * repeat rewrite TMap.gso by exact Hneq. apply Hpush.
        + exact Hwf.
    Qed.

    Lemma snapshot_protocol_atomic_fail p s pi actor start :
      snapshot_protocol p s pi ->
      TMap.find actor pi = Some (ls_inv (tsa_trypop start)) ->
      TMap.find actor (lp_snapshots p) = None ->
      TMap.find actor (tsa_snapshots s) = None ->
      snapshot_protocol p
        (tsa_clear_snapshot actor (tsa_start_snapshot actor s))
        (TMap.add actor (ls_linr (tsa_trypop start) TFail)
          (TMap.add actor (ls_lini (tsa_trypop start)) pi)).
    Proof.
      intros [Hconcrete [Hsnapshot [Hpush Hwf]]] Htoken Hcp Has.
      unfold snapshot_protocol, tsa_clear_snapshot, tsa_start_snapshot;
        simpl.
      split.
      - intros observer N Hfind.
        destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
        + rewrite Hcp in Hfind. discriminate.
        + rewrite TMap.gro by exact Hneq.
          rewrite TMap.gso by exact Hneq. now apply Hconcrete.
      - split.
        + intro observer.
          destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
          * rewrite TMap.grs. repeat rewrite TMap.gss. split.
            -- intros [N Hbad]. discriminate.
            -- intros [st Hbad]. discriminate.
          * rewrite TMap.gro by exact Hneq.
            rewrite TMap.gso by exact Hneq.
            repeat rewrite TMap.gso by exact Hneq. apply Hsnapshot.
        + split.
          * intro observer.
            destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
            -- repeat rewrite TMap.gss. split.
               ++ intros [loc Hfind].
                  destruct (proj1 (Hpush actor) (ex_intro _ loc Hfind))
                    as [v Hbad]. rewrite Htoken in Hbad. discriminate.
               ++ intros [v Hbad]. discriminate.
            -- repeat rewrite TMap.gso by exact Hneq. apply Hpush.
          * intros observer N Hfind n Hmember.
            destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
            -- rewrite TMap.grs in Hfind. discriminate.
            -- rewrite TMap.gro in Hfind by exact Hneq.
               rewrite TMap.gso in Hfind by exact Hneq.
               now apply (Hwf observer N Hfind n Hmember).
    Qed.

    Lemma graph_represents_atomic_fail p s actor :
      graph_represents p s ->
      graph_represents p
        (tsa_clear_snapshot actor (tsa_start_snapshot actor s)).
    Proof. unfold graph_represents, tsa_clear_snapshot, tsa_start_snapshot;
      simpl; tauto. Qed.

    Lemma all_vertices_garbage_represents p s :
      graph_represents p s -> all_vertices_garbage p ->
      tsa_all_vertices_garbage s.
    Proof.
      intros [HV [_ [_ HG]]] Hall n.
      specialize (Hall n).
      unfold is_vertex, tsa_is_vertex in *.
      now rewrite <- HV, <- HG.
    Qed.

    Lemma snapshot_protocol_trypop_fail p s pi actor start N ret :
      snapshot_protocol p s pi ->
      TMap.find actor pi = Some (ls_lini (tsa_trypop start)) ->
      TMap.find actor (lp_snapshots p) = None ->
      TMap.find actor (tsa_snapshots s) = Some N ->
      snapshot_protocol p (tsa_clear_snapshot actor s)
        (TMap.add actor (ls_linr (tsa_trypop start) ret) pi).
    Proof.
      intros [Hconcrete [Hsnapshot [Hpush Hwf]]] Htoken Hcp Has.
      unfold snapshot_protocol, tsa_clear_snapshot; simpl.
      split.
      - intros observer N' Hfind.
        destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
        + rewrite Hcp in Hfind. discriminate.
        + rewrite TMap.gro by exact Hneq. now apply Hconcrete.
      - split.
        + intro observer.
          destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
          * rewrite TMap.grs, TMap.gss. split.
            -- intros [N' Hbad]. discriminate.
            -- intros [st Hbad]. discriminate.
          * rewrite TMap.gro, TMap.gso by exact Hneq. apply Hsnapshot.
        + split.
          * intro observer.
            destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
            -- rewrite TMap.gss. split.
               ++ intros [loc Hfind].
                  destruct (proj1 (Hpush actor) (ex_intro _ loc Hfind))
                    as [v Hbad]. rewrite Htoken in Hbad. discriminate.
               ++ intros [v Hbad]. discriminate.
            -- rewrite TMap.gso by exact Hneq. apply Hpush.
          * intros observer N' Hfind n Hmember.
            destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
            -- rewrite TMap.grs in Hfind. discriminate.
            -- rewrite TMap.gro in Hfind by exact Hneq.
               now apply (Hwf observer N' Hfind n Hmember).
    Qed.

    Lemma snapshot_protocol_trypop_succ p s pi actor start N n ret :
      snapshot_protocol p s pi ->
      TMap.find actor pi = Some (ls_lini (tsa_trypop start)) ->
      TMap.find actor (lp_snapshots p) = None ->
      TMap.find actor (tsa_snapshots s) = Some N ->
      snapshot_protocol (mark_garbage n p)
        (tsa_remove_node actor n s)
        (TMap.add actor (ls_linr (tsa_trypop start) ret) pi).
    Proof.
      intros Hprotocol Htoken Hcp Has.
      pose proof (snapshot_protocol_trypop_fail p s pi actor start N ret
        Hprotocol Htoken Hcp Has) as Hfail.
      eapply snapshot_protocol_fields;
        [exact Hfail|reflexivity|reflexivity|reflexivity|reflexivity].
    Qed.

    Lemma graph_represents_trypop_fail p s actor :
      graph_represents p s ->
      graph_represents p (tsa_clear_snapshot actor s).
    Proof. unfold graph_represents, tsa_clear_snapshot; simpl; tauto. Qed.

    Lemma graph_represents_trypop_succ p s actor n :
      graph_represents p s ->
      graph_represents (mark_garbage n p)
        (tsa_remove_node actor n s).
    Proof.
      unfold graph_represents, mark_garbage, tsa_remove_node; simpl.
      intros [HV [HE [HP HG]]]. repeat split; try assumption.
      now rewrite HG.
    Qed.

    (** trypop assertions. *)

    Definition TryPopInside actor start : assertion :=
      fun w => Active actor (tsa_trypop start) w /\
        ThreadDomain.contains D actor /\
        TMap.find actor
          (tsa_pop_ts (abstract_payload (SinglePossState.ρ w))) =
          Some start.

    Definition GetTopAtomicPhase actor start : assertion :=
      fun w =>
        AssertionsSingle.ALin actor (ls_inv (tsa_trypop start)) w /\
        TMap.find actor
          (lp_snapshots (concrete_payload (SinglePossState.σ w))) = None /\
        TMap.find actor
          (tsa_snapshots (abstract_payload (SinglePossState.ρ w))) = None.

    Definition SelfAtomicGetTop actor start : assertion :=
      fun w =>
        match SinglePossState.σ w with
        | LPReady _ => True
        | LPAtomicPending _ pending_actor op =>
            pending_actor = actor ->
            op = lpool_getTop start /\ GetTopAtomicPhase actor start w
        end.

    Definition GetTopPending actor start : assertion :=
      fun w =>
        source_I w /\ ThreadDomain.contains D actor /\
        TMap.find actor
          (tsa_pop_ts (abstract_payload (SinglePossState.ρ w))) =
          Some start /\
        ((GetTopAtomicPhase actor start w) \/
         (exists N,
          AssertionsSingle.ALin actor (ls_lini (tsa_trypop start)) w /\
          TMap.find actor
            (lp_snapshots (concrete_payload (SinglePossState.σ w))) =
              Some N /\
          TMap.find actor
            (tsa_snapshots (abstract_payload (SinglePossState.ρ w))) =
              Some N)) /\
        SelfAtomicGetTop actor start w.

    Lemma trypop_inside_entails_I actor start :
      ⊨ TryPopInside actor start ==>> source_I.
    Proof. firstorder. Qed.

    Lemma getTop_pending_entails_I actor start :
      ⊨ GetTopPending actor start ==>> source_I.
    Proof. firstorder. Qed.

    Lemma trypop_inside_stable actor start :
      AssertionsSingle.A.Stable (source_R actor) source_I
        (TryPopInside actor start).
    Proof.
      unfold AssertionsSingle.A.Stable, TryPopInside.
      intros out [[pre [[[HI Htoken] [Hinside Hts]] HR]] HIout].
      pose proof (source_R_local actor _ _ HR) as Hlocal.
      unfold local_eq_relation, actor_local_eq in Hlocal.
      destruct Hlocal as
        [Hcs [Has [Hpush [Hcstarts [Hcts [Hastarts [Hats Htoken_eq]]]]]]].
      split; [|split; [exact Hinside|exact (eq_trans (eq_sym Hats) Hts) ] ].
      split; [exact HIout|].
      unfold AssertionsSingle.ALin in Htoken |- *.
      exact (eq_trans (eq_sym Htoken_eq) Htoken).
    Qed.

    Lemma getTop_pending_stable actor start :
      AssertionsSingle.A.Stable (source_R actor) source_I
        (GetTopPending actor start).
    Proof.
      unfold AssertionsSingle.A.Stable, GetTopPending.
      intros out [[pre [[HI [Hinside [Hts [Hphase Hself]]]] HR]] HIout].
      pose proof (source_R_local actor _ _ HR) as Hlocal.
      unfold local_eq_relation, actor_local_eq in Hlocal.
      destruct Hlocal as
        [Hcs [Has [Hpush [Hcstarts [Hcts [Hastarts [Hats Htoken]]]]]]].
      split; [exact HIout|]. split; [exact Hinside|].
      split; [exact (eq_trans (eq_sym Hats) Hts)|]. split.
      destruct Hphase as [[Hlin [Hcnone Hanone]]|Hphase].
      - left. unfold GetTopAtomicPhase in *. split.
        + unfold AssertionsSingle.ALin in Hlin |- *.
          exact (eq_trans (eq_sym Htoken) Hlin).
        + split.
          * exact (eq_trans (eq_sym Hcs) Hcnone).
          * exact (eq_trans (eq_sym Has) Hanone).
      - destruct Hphase as (N & Hlin & Hcsome & Hasome).
        right. exists N. split.
        + unfold AssertionsSingle.ALin in Hlin |- *.
          exact (eq_trans (eq_sym Htoken) Hlin).
        + split.
          * exact (eq_trans (eq_sym Hcs) Hcsome).
          * exact (eq_trans (eq_sym Has) Hasome).
      - unfold SelfAtomicGetTop in *.
        destruct (SinglePossState.σ out) as [p|p pending op] eqn:Hout;
          [exact Logic.I|].
        intro Hpending. subst pending.
        unfold source_R, AssertionsSingle.GuaranteeGeneratedRely,
          AssertionsSingle.A.Union in HR.
        destruct HR as [[other [Hneq HG]]|Hadmin].
        + destruct HG as [_ [_ [_ [_ Howned]]]].
          rewrite Hout in Howned. simpl in Howned. congruence.
        + pose proof
            (AssertionsSingle.linearization_rely_observer_view actor
              _ _ Hadmin) as [Hsigma [Hrho_eq Hpi_eq]].
          assert (Hpre_control : SinglePossState.σ pre =
              LPAtomicPending p actor op) by congruence.
          rewrite Hpre_control in Hself. simpl in Hself.
          destruct (Hself eq_refl) as [Hop [Hlin [Hcnone Hanone]]].
          split; [exact Hop|]. unfold GetTopAtomicPhase. split.
          * unfold AssertionsSingle.ALin in Hlin |- *.
            exact (eq_trans (eq_sym Htoken) Hlin).
          * split.
            -- rewrite Hout. exact (eq_trans (eq_sym Hcs) Hcnone).
            -- exact (eq_trans (eq_sym Has) Hanone).
    Qed.

    (** After [getTop start] returned [YSuccNode v owner loc]: the node is
        garbage, or top of the actor's live snapshot, or outside the
        actor's start set (the elimination candidate). *)
    Definition TryRemoveReady actor start (v : A) owner loc : assertion :=
      fun w =>
        source_I w /\ ThreadDomain.contains D actor /\
        exists s N,
          SinglePossState.ρ w = TSAReady s /\
          AssertionsSingle.ALin actor (ls_lini (tsa_trypop start)) w /\
          TMap.find actor (tsa_snapshots s) = Some N /\
          TMap.find actor
            (lp_snapshots
              (concrete_payload (SinglePossState.σ w))) = None /\
          tsa_vertices s (pair owner loc) = Some v /\
          (tsa_garbage s (pair owner loc) \/
           lp_top (fun n => N n /\ ~ tsa_garbage s n)
             (tsa_edges s) (pair owner loc) \/
           (exists N0,
             TMap.find actor (tsa_pop_starts s) = Some N0 /\
             ~ N0 (pair owner loc))).

    Definition GetTopPost actor start (result : @YResult A) : assertion :=
      match result with
      | YSuccNode v owner loc => TryRemoveReady actor start v owner loc
      | YSuccEmpty => Completed actor (tsa_trypop start) TSuccEmpty
      | YFail => Completed actor (tsa_trypop start) TFail
      end.

    Lemma tryRemove_ready_entails_I actor start v owner loc :
      ⊨ TryRemoveReady actor start v owner loc ==>> source_I.
    Proof. firstorder. Qed.

    Lemma getTop_post_entails_I actor start result :
      ⊨ GetTopPost actor start result ==>> source_I.
    Proof.
      destruct result as [v owner loc| |]; simpl.
      - apply tryRemove_ready_entails_I.
      - apply completed_entails_I.
      - apply completed_entails_I.
    Qed.

    Lemma tryRemove_ready_stable actor start v owner loc :
      AssertionsSingle.A.Stable (source_R actor) source_I
        (TryRemoveReady actor start v owner loc).
    Proof.
      unfold AssertionsSingle.A.Stable, TryRemoveReady.
      intros out [[pre [[HIpre [Hinside Hdata]] HR]] HIout].
      destruct Hdata as
        (s & N & Hrho & Htoken & Hsnapshot & Hcsnone & Hvalue & Hstatus).
      pose proof (source_R_local actor _ _ HR) as Hlocal.
      unfold local_eq_relation, actor_local_eq in Hlocal.
      destruct Hlocal as
        [Hcs [Has [Hpush [Hcstarts [Hcts [Hastarts [Hats Htoken_eq]]]]]]].
      pose proof (source_R_graph_evol actor _ _ HR) as Hevol.
      unfold graph_evol_facts, graph_evol_relation in Hevol.
      destruct HIpre as (s0 & Hrho0 & Hgraph0 & Hprotocol0 & Hsession0 & Howned0).
      simpl in Hrho, Hrho0. rewrite Hrho in Hrho0.
      inversion Hrho0; subst s0.
      pose proof HIout as HIout0.
      destruct HIout as (s' & Hrho' & Hgraph' & Hprotocol' & Hsession' & Howned').
      split; [exact HIout0|].
      split; [exact Hinside|]. exists s', N.
      repeat split; try assumption.
      - unfold AssertionsSingle.ALin in Htoken |- *.
        exact (eq_trans (eq_sym Htoken_eq) Htoken).
      - pose proof (f_equal
          (fun r => TMap.find actor (tsa_snapshots (abstract_payload r)))
          Hrho) as Epre.
        pose proof (f_equal
          (fun r => TMap.find actor (tsa_snapshots (abstract_payload r)))
          Hrho') as Eout.
        simpl in Epre, Eout.
        exact (eq_trans (eq_sym Eout)
          (eq_trans (eq_sym Has) (eq_trans Epre Hsnapshot))).
      - exact (eq_trans (eq_sym Hcs) Hcsnone).
      - destruct Hgraph0 as [HV0 [HE0 [HP0 HG0]]].
        destruct Hgraph' as [HV' [HE' [HP' HG']]].
        destruct Hevol as [HVevol [HEevol HGevol]].
        assert (Hold_value :
          lp_vertices (concrete_payload (SinglePossState.σ pre))
            (pair owner loc) = Some v).
        { now rewrite HV0. }
        specialize (HVevol (pair owner loc) v Hold_value).
        now rewrite HV' in HVevol.
      - destruct Hstatus as [Hgarbage|[Htop|Helim]].
        + destruct Hgraph0 as [HV0 [HE0 [HP0 HG0]]].
          destruct Hgraph' as [HV' [HE' [HP' HG']]].
          destruct Hevol as [HVevol [HEevol HGevol]].
          left. rewrite <- HG'. apply HGevol. now rewrite HG0.
        + destruct Hgraph0 as [HV0 [HE0 [HP0 HG0]]].
          destruct Hgraph' as [HV' [HE' [HP' HG']]].
          destruct Hevol as [HVevol [HEevol HGevol]].
          destruct (classic (tsa_garbage s' (pair owner loc)))
            as [Hnew_garbage|Hnew_live].
          * now left.
          * right. left. destruct Htop as [Hmember Htop]. split.
            -- split; [exact (proj1 Hmember)|exact Hnew_live].
            -- intros n' [HN Hnotgarbage] Hedge'.
               assert (Hold_notgarbage : ~ tsa_garbage s n').
               { intro Hold. apply Hnotgarbage. rewrite <- HG'.
                 apply HGevol. now rewrite HG0. }
               apply (Htop n' (conj HN Hold_notgarbage)).
               assert (Hvertex :
                 is_vertex (concrete_payload (SinglePossState.σ pre)) n').
               { unfold is_vertex. intro Hnone.
                 destruct Hprotocol0 as [_ [_ [_ Hwf]]].
                 specialize (Hwf actor N Hsnapshot n' HN).
                 unfold tsa_is_vertex in Hwf.
                 rewrite <- HV0 in Hwf. contradiction. }
               assert (Hedge_new :
                 lp_edges (concrete_payload (SinglePossState.σ out))
                   n' (pair owner loc)).
               { now rewrite HE'. }
               pose proof
                 (proj2 (HEevol n' (pair owner loc) Hvertex) Hedge_new)
                 as Hedge_old.
               now rewrite HE0 in Hedge_old.
        + right. right. destruct Helim as (N0 & Hstarts & Hnot).
          exists N0. split; [|exact Hnot].
          pose proof (f_equal
            (fun r => TMap.find actor (tsa_pop_starts (abstract_payload r)))
            Hrho) as Epre.
          pose proof (f_equal
            (fun r => TMap.find actor (tsa_pop_starts (abstract_payload r)))
            Hrho') as Eout.
          simpl in Epre, Eout.
          exact (eq_trans (eq_sym Eout)
            (eq_trans (eq_sym Hastarts) (eq_trans Epre Hstarts))).
    Qed.

    Lemma getTop_post_stable actor start result :
      AssertionsSingle.A.Stable (source_R actor) source_I
        (GetTopPost actor start result).
    Proof.
      destruct result as [v owner loc| |]; simpl.
      - apply tryRemove_ready_stable.
      - apply completed_stable.
      - apply completed_stable.
    Qed.

    (** The three node responses of [getTop] share the invariant
        bookkeeping; only the carried fact differs. *)
    Lemma getTop_node_post actor start (s : @ListPoolState A) a π1 N
        owner loc (v : A) :
      source_I (@SinglePossState.Build_ProofStateSingle _ _
        (li_lts E) (li_lts F) (LPReady s) (TSAReady a) π1) ->
      ThreadDomain.contains D actor ->
      AssertionsSingle.ALin actor (ls_lini (tsa_trypop start))
        (@SinglePossState.Build_ProofStateSingle _ _
          (li_lts E) (li_lts F) (LPReady s) (TSAReady a) π1) ->
      TMap.find actor (tsa_snapshots a) = Some N ->
      lp_vertices s (pair owner loc) = Some v ->
      (tsa_garbage a (pair owner loc) \/
       lp_top (fun n => N n /\ ~ tsa_garbage a n)
         (tsa_edges a) (pair owner loc) \/
       (exists N0,
         TMap.find actor (tsa_pop_starts a) = Some N0 /\
         ~ N0 (pair owner loc))) ->
      exists (ρ' : State (li_lts F)) (π' : tmap (@LinState (li_sig F))),
        @poss_steps _ (li_lts F)
          (@PossOk _ (li_lts F) (TSAReady a) π1)
          (@PossOk _ (li_lts F) ρ' π') /\
        TryRemoveReady actor start v owner loc
          (@SinglePossState.Build_ProofStateSingle _ _
            (li_lts E) (li_lts F)
            (LPReady (clear_snapshot actor s)) ρ' π') /\
        source_G actor
          (@SinglePossState.Build_ProofStateSingle _ _
            (li_lts E) (li_lts F) (LPReady s) (TSAReady a) π1)
          (@SinglePossState.Build_ProofStateSingle _ _
            (li_lts E) (li_lts F)
            (LPReady (clear_snapshot actor s)) ρ' π').
    Proof.
      intros HIpre Hinside Hlin Habstract Hcvalue Hstatus.
      pose proof HIpre as HIpre0.
      destruct HIpre as (a' & Hrho & Hgraph & Hprotocol & Hsession & Howned).
      simpl in Hrho. inversion Hrho; subst a'.
      simpl in Hgraph, Hprotocol, Hsession, Howned.
      exists (TSAReady a), π1. split; [apply rt_refl|].
      assert (HIpost : source_I
        (@SinglePossState.Build_ProofStateSingle _ _
          (li_lts E) (li_lts F)
          (LPReady (clear_snapshot actor s))
          (TSAReady a) π1)).
      { exists a. split; [reflexivity|]. split.
        - now apply graph_represents_clear_concrete_snapshot.
        - split; [|split].
          + now apply snapshot_protocol_clear_concrete.
          + eapply session_protocol_fields;
              [exact Hsession|reflexivity|reflexivity|reflexivity|
               reflexivity].
          + now apply vertices_owned_clear_snapshot. }
      split.
      - unfold TryRemoveReady. split; [exact HIpost|].
        split; [exact Hinside|]. exists a, N.
        split; [reflexivity|]. split; [exact Hlin|].
        split; [exact Habstract|].
        split; [simpl; apply TMap.grs|].
        split; [|exact Hstatus].
        destruct Hgraph as [HV _]. now rewrite <- HV.
      - unfold source_G.
        refine (conj _ (conj _ (conj _ (conj _ _)))).
        + exact HIpre0.
        + exact HIpost.
        + apply graph_evol_clear_snapshot.
        + intros observer Hneq. unfold actor_local_eq; simpl.
          repeat split; try reflexivity;
            rewrite TMap.gro by congruence; reflexivity.
        + exact Logic.I.
    Qed.

    Lemma getTop_res_update actor start result :
      AssertionsSingle.PUpdate (source_G actor)
        (Build_ThreadEvent actor (ResEv (lpool_getTop start) result))
        (GetTopPending actor start) (GetTopPost actor start result).
    Proof.
      pupdate_intros_atomic.
      - (* top of the snapshot *)
        match goal with
        | H : TMap.find _ (lp_snapshots _) = Some _ |- _ =>
            rename H into Hcsnap
        end.
        match goal with
        | H : lp_top _ _ _ |- _ => rename H into Hctop
        end.
        match goal with
        | H : lp_vertices _ _ = Some _ |- _ => rename H into Hcvalue
        end.
        destruct n as [owner loc]. simpl in *.
        destruct Hpre as [HIpre [Hinside [Hts [Hphase Hself]]]].
        destruct Hphase as [[Hlin [Hcnone Hanone]]|Hphase];
          [destruct HIpre as
             (a0 & Hrho0 & Hgraph0 & Hprotocol0 & Hsession0 & Howned0);
           simpl in Hrho0; subst ρ1; simpl in Hanone;
           destruct Hprotocol0 as [Hconcrete0 _];
           pose proof (Hconcrete0 _ N Hcsnap) as Habs;
           rewrite Habs in Hanone; discriminate|].
        destruct Hphase as (N1 & Hlin & Hconcrete & Habstract).
        pose proof HIpre as HIpre0.
        destruct HIpre as (a & Hrho & Hgraph & Hprotocol & Hsession & Howned).
        simpl in Hrho, Hlin, Hconcrete, Habstract, Hts. subst ρ1.
        rewrite Hcsnap in Hconcrete. inversion Hconcrete; subst N1.
        eapply getTop_node_post;
          [exact HIpre0|exact Hinside|exact Hlin|exact Habstract|
           exact Hcvalue|].
        right. left. destruct Hgraph as [_ [HE [_ HG]]].
        unfold lp_top in *. now rewrite <- HE, <- HG.
      - (* garbage *)
        match goal with
        | H : TMap.find _ (lp_snapshots _) = Some _ |- _ =>
            rename H into Hcsnap
        end.
        match goal with
        | H : lp_garbage _ _ |- _ => rename H into Hcgarbage
        end.
        match goal with
        | H : lp_vertices _ _ = Some _ |- _ => rename H into Hcvalue
        end.
        destruct n as [owner loc]. simpl in *.
        destruct Hpre as [HIpre [Hinside [Hts [Hphase Hself]]]].
        destruct Hphase as [[Hlin [Hcnone Hanone]]|Hphase];
          [destruct HIpre as
             (a0 & Hrho0 & Hgraph0 & Hprotocol0 & Hsession0 & Howned0);
           simpl in Hrho0; subst ρ1; simpl in Hanone;
           destruct Hprotocol0 as [Hconcrete0 _];
           pose proof (Hconcrete0 _ N Hcsnap) as Habs;
           rewrite Habs in Hanone; discriminate|].
        destruct Hphase as (N1 & Hlin & Hconcrete & Habstract).
        pose proof HIpre as HIpre0.
        destruct HIpre as (a & Hrho & Hgraph & Hprotocol & Hsession & Howned).
        simpl in Hrho, Hlin, Hconcrete, Habstract, Hts. subst ρ1.
        rewrite Hcsnap in Hconcrete. inversion Hconcrete; subst N1.
        eapply getTop_node_post;
          [exact HIpre0|exact Hinside|exact Hlin|exact Habstract|
           exact Hcvalue|].
        left. destruct Hgraph as [_ [_ [_ HG]]]. now rewrite <- HG.
      - (* elimination candidate *)
        match goal with
        | H : TMap.find _ (lp_snapshots _) = Some _ |- _ =>
            rename H into Hcsnap
        end.
        match goal with
        | H : TMap.find _ (lp_pop_starts _) = Some _ |- _ =>
            rename H into Hcstarts
        end.
        match goal with
        | H : ~ _ |- _ => rename H into Hnot
        end.
        match goal with
        | H : lp_vertices _ _ = Some _ |- _ => rename H into Hcvalue
        end.
        destruct n as [owner loc]. simpl in *.
        destruct Hpre as [HIpre [Hinside [Hts [Hphase Hself]]]].
        destruct Hphase as [[Hlin [Hcnone Hanone]]|Hphase];
          [destruct HIpre as
             (a0 & Hrho0 & Hgraph0 & Hprotocol0 & Hsession0 & Howned0);
           simpl in Hrho0; subst ρ1; simpl in Hanone;
           destruct Hprotocol0 as [Hconcrete0 _];
           pose proof (Hconcrete0 _ N Hcsnap) as Habs;
           rewrite Habs in Hanone; discriminate|].
        destruct Hphase as (N1 & Hlin & Hconcrete & Habstract).
        pose proof HIpre as HIpre0.
        destruct HIpre as (a & Hrho & Hgraph & Hprotocol & Hsession & Howned).
        simpl in Hrho, Hlin, Hconcrete, Habstract, Hts. subst ρ1.
        rewrite Hcsnap in Hconcrete. inversion Hconcrete; subst N1.
        assert (Hastarts : TMap.find actor0 (tsa_pop_starts a) = Some N0).
        { destruct Hsession as [H1 [_ [H3 _]]].
          destruct (H3 _ _ Hts) as [N0' Hfind].
          pose proof (H1 _ _ Hfind) as Hc. simpl in Hc.
          rewrite Hcstarts in Hc. injection Hc as Heq. subst N0'.
          exact Hfind. }
        eapply getTop_node_post;
          [exact HIpre0|exact Hinside|exact Hlin|exact Habstract|
           exact Hcvalue|].
        right. right. exists N0. split; [exact Hastarts|exact Hnot].
      - (* atomic fail *)
        simpl in Hpre.
        destruct Hpre as [HIpre [Hinside [Hts [Hphase Hself]]]].
        specialize (Hself eq_refl).
        destruct Hself as [_ [Htoken [Hcp Has]]].
        pose proof HIpre as HIpre0.
        destruct HIpre as (a & Hrho & Hgraph & Hprotocol & Hsession & Howned).
        simpl in Hrho, Htoken, Has, Hts. subst ρ1.
        exists
          (TSAReady
            (tsa_clear_snapshot actor0 (tsa_start_snapshot actor0 a))),
          (TMap.add actor0 (ls_linr (tsa_trypop start0) TFail)
            (TMap.add actor0 (ls_lini (tsa_trypop start0)) π1)).
        split.
        + eapply rt_trans.
          * apply rt_step. eapply ps_inv.
            -- eapply step_tsa_trypop_snapshot_inv;
                 [exact Has|exact Hts|reflexivity].
            -- exact Htoken.
          * apply rt_step. eapply ps_ret.
            -- eapply step_tsa_trypop_fail with
                 (N := fun n => tsa_is_vertex a n).
               ++ unfold tsa_start_snapshot; simpl. apply TMap.gss.
               ++ reflexivity.
            -- apply TMap.gss.
        + assert (HIpost : source_I
            (@SinglePossState.Build_ProofStateSingle _ _
              (li_lts E) (li_lts F) (LPReady s0)
              (TSAReady
                (tsa_clear_snapshot actor0
                  (tsa_start_snapshot actor0 a)))
              (TMap.add actor0 (ls_linr (tsa_trypop start0) TFail)
                (TMap.add actor0 (ls_lini (tsa_trypop start0)) π1)))).
          { exists
              (tsa_clear_snapshot actor0 (tsa_start_snapshot actor0 a)).
            split; [reflexivity|]. split.
            - now apply graph_represents_atomic_fail.
            - split; [|split].
              + eapply snapshot_protocol_atomic_fail; eauto.
              + eapply session_protocol_keep;
                  [exact Hsession|reflexivity|reflexivity|reflexivity|
                   reflexivity| | |].
                * old_token_neq Htoken.
                * new_token_neq.
                * other_token.
              + exact Howned. }
          split.
          * unfold GetTopPost, Completed. split; [exact HIpost|].
            unfold AssertionsSingle.ALin. simpl. apply TMap.gss.
          * unfold source_G.
            refine (conj _ (conj _ (conj _ (conj _ _)))).
            -- exact HIpre0.
            -- exact HIpost.
            -- apply graph_evol_refl.
            -- intros observer Hneq. unfold actor_local_eq; simpl.
               repeat split; try reflexivity;
                 rewrite ?TMap.gro, ?TMap.gso by congruence; reflexivity.
            -- exact Logic.I.
      - (* atomic empty *)
        match goal with
        | H : all_vertices_garbage _ |- _ => rename H into Hall
        end.
        simpl in Hpre.
        destruct Hpre as [HIpre [Hinside [Hts [Hphase Hself]]]].
        specialize (Hself eq_refl).
        destruct Hself as [_ [Htoken [Hcp Has]]].
        pose proof HIpre as HIpre0.
        destruct HIpre as (a & Hrho & Hgraph & Hprotocol & Hsession & Howned).
        simpl in Hrho, Htoken, Has, Hts. subst ρ1.
        assert (Hempty : tsa_all_vertices_garbage a).
        { eapply all_vertices_garbage_represents;
            [exact Hgraph|exact Hall]. }
        exists (TSAReady (tsa_close_session actor0 a)),
          (TMap.add actor0 (ls_linr (tsa_trypop start0) TSuccEmpty)
            (TMap.add actor0 (ls_lini (tsa_trypop start0)) π1)).
        split.
        + eapply rt_trans.
          * apply rt_step. eapply ps_inv.
            -- eapply step_tsa_trypop_empty_inv;
                 [exact Has|exact Hts|exact Hempty|reflexivity].
            -- exact Htoken.
          * apply rt_step. eapply ps_ret.
            -- eapply step_tsa_trypop_empty_res. reflexivity.
            -- apply TMap.gss.
        + assert (HIpost : source_I
            (@SinglePossState.Build_ProofStateSingle _ _
              (li_lts E) (li_lts F) (LPReady s0)
              (TSAReady (tsa_close_session actor0 a))
              (TMap.add actor0 (ls_linr (tsa_trypop start0) TSuccEmpty)
                (TMap.add actor0 (ls_lini (tsa_trypop start0)) π1)))).
          { exists (tsa_close_session actor0 a).
            split; [reflexivity|]. split.
            - now apply graph_represents_close_session.
            - split; [|split].
              + eapply snapshot_protocol_fields;
                  [eapply snapshot_protocol_atomic_same; eauto|
                   reflexivity|reflexivity|reflexivity|reflexivity].
              + eapply session_protocol_close;
                  [exact Hsession|reflexivity|reflexivity|reflexivity|
                   reflexivity| |].
                * new_token_neq.
                * other_token.
              + exact Howned. }
          split.
          * unfold GetTopPost, Completed. split; [exact HIpost|].
            unfold AssertionsSingle.ALin. simpl. apply TMap.gss.
          * unfold source_G.
            refine (conj _ (conj _ (conj _ (conj _ _)))).
            -- exact HIpre0.
            -- exact HIpost.
            -- apply graph_evol_refl.
            -- intros observer Hneq. unfold actor_local_eq; simpl.
               repeat split; try reflexivity;
                 rewrite ?TMap.gro, ?TMap.gso by congruence; reflexivity.
            -- exact Logic.I.
    Qed.

    Lemma getTop_inv_update actor start :
      AssertionsSingle.PUpdate (source_G actor)
        (Build_ThreadEvent actor (InvEv (lpool_getTop start)))
        (TryPopInside actor start) (GetTopPending actor start).
    Proof.
      pupdate_intros_atomic.
      - (* snapshot branch *)
        destruct Hpre as [[HIpre Htoken] [Hinside Hts]].
        pose proof HIpre as HIpre0.
        destruct HIpre as (a & Hrho & Hgraph & Hprotocol & Hsession & Howned).
        simpl in Hrho. subst ρ1. simpl in Hts.
        assert (Has_none : TMap.find actor0 (tsa_snapshots a) = None).
        { destruct Hprotocol as [_ [Hsnapshot _]].
          destruct (TMap.find actor0 (tsa_snapshots a)) as [N|] eqn:Hfind;
            [|reflexivity].
          destruct (proj1 (Hsnapshot actor0) (ex_intro _ N Hfind))
            as [st Hbad]. unfold AssertionsSingle.ALin in Htoken.
          rewrite Htoken in Hbad. discriminate. }
        exists (TSAReady (tsa_start_snapshot actor0 a)),
          (TMap.add actor0 (ls_lini (tsa_trypop start0)) π1).
        split.
        + apply rt_step. eapply ps_inv.
          * eapply step_tsa_trypop_snapshot_inv;
              [exact Has_none|exact Hts|reflexivity].
          * exact Htoken.
        + assert (HIpost : source_I
            (@SinglePossState.Build_ProofStateSingle _ _
              (li_lts E) (li_lts F)
              (LPReady (start_snapshot actor0 s))
              (TSAReady (tsa_start_snapshot actor0 a))
              (TMap.add actor0 (ls_lini (tsa_trypop start0)) π1))).
          { exists (tsa_start_snapshot actor0 a).
            split; [reflexivity|]. split.
            - now apply graph_represents_start_snapshot.
            - split; [|split].
              + eapply snapshot_protocol_snapshot_inv; eauto.
              + eapply session_protocol_keep;
                  [exact Hsession|reflexivity|reflexivity|reflexivity|
                   reflexivity| | |].
                * old_token_neq Htoken.
                * new_token_neq.
                * other_token.
              + now apply vertices_owned_start_snapshot. }
          split.
          * unfold GetTopPending. split; [exact HIpost|].
            split; [exact Hinside|]. split; [simpl; exact Hts|]. split.
            -- right. exists (fun n => is_vertex s n). split.
               ++ unfold AssertionsSingle.ALin; simpl. apply TMap.gss.
               ++ split.
                  ** simpl. apply TMap.gss.
                  ** simpl. rewrite TMap.gss. f_equal.
                     apply functional_extensionality. intro n.
                     apply propositional_extensionality. symmetry.
                     now apply graph_represents_is_vertex.
            -- exact Logic.I.
          * unfold source_G.
            refine (conj _ (conj _ (conj _ (conj _ _)))).
            -- exact HIpre0.
            -- exact HIpost.
            -- apply graph_evol_start_snapshot.
            -- intros observer Hneq. unfold actor_local_eq; simpl.
               repeat split; try reflexivity;
                 rewrite TMap.gso by congruence; reflexivity.
            -- exact Logic.I.
      - (* atomic branch *)
        destruct Hpre as [[HIpre Htoken] [Hinside Hts]].
        pose proof HIpre as HIpre0.
        destruct HIpre as (a & Hrho & Hgraph & Hprotocol & Hsession & Howned).
        simpl in Hrho. subst ρ1. simpl in Hts.
        assert (Has_none : TMap.find actor0 (tsa_snapshots a) = None).
        { destruct Hprotocol as [_ [Hsnapshot _]].
          destruct (TMap.find actor0 (tsa_snapshots a)) as [N|] eqn:Hfind;
            [|reflexivity].
          destruct (proj1 (Hsnapshot actor0) (ex_intro _ N Hfind))
            as [st Hbad]. unfold AssertionsSingle.ALin in Htoken.
          rewrite Htoken in Hbad. discriminate. }
        assert (Hcp_none : TMap.find actor0 (lp_snapshots s0) = None).
        { destruct Hprotocol as [Hconcrete _].
          destruct (TMap.find actor0 (lp_snapshots s0)) as [N|] eqn:Hfind;
            [|reflexivity].
          specialize (Hconcrete actor0 N Hfind). congruence. }
        exists (TSAReady a), π1. split; [apply rt_refl|].
        assert (HIpost : source_I
          (@SinglePossState.Build_ProofStateSingle _ _
            (li_lts E) (li_lts F)
            (LPAtomicPending s0 actor0 (lpool_getTop start0))
            (TSAReady a) π1)).
        { exists a. simpl. auto. }
        split.
        + unfold GetTopPending. split; [exact HIpost|].
          split; [exact Hinside|]. split; [simpl; exact Hts|].
          assert (Hphase : GetTopAtomicPhase actor0 start0
            (@SinglePossState.Build_ProofStateSingle _ _
              (li_lts E) (li_lts F)
              (LPAtomicPending s0 actor0 (lpool_getTop start0))
              (TSAReady a) π1)).
          { unfold GetTopAtomicPhase. split; [exact Htoken|].
            split; assumption. }
          split; [now left|].
          unfold SelfAtomicGetTop; simpl. intros Hactor_eq. split;
            [reflexivity|exact Hphase].
        + unfold source_G.
          refine (conj _ (conj _ (conj _ (conj _ _)))).
          * exact HIpre0.
          * exact HIpost.
          * apply graph_evol_refl.
          * intros observer Hneq. unfold actor_local_eq; simpl.
            repeat split; reflexivity.
          * reflexivity.
    Qed.

    Definition TryRemovePending actor start (v : A) owner loc : assertion :=
      TryRemoveReady actor start v owner loc.

    Definition TryRemovePost actor start (v : A) owner loc
        (removed : bool) : assertion :=
      Completed actor (tsa_trypop start)
        (if removed then TSuccNode v owner loc else TFail).

    Lemma tryRemove_pending_entails_I actor start v owner loc :
      ⊨ TryRemovePending actor start v owner loc ==>> source_I.
    Proof. apply tryRemove_ready_entails_I. Qed.

    Lemma tryRemove_pending_stable actor start v owner loc :
      AssertionsSingle.A.Stable (source_R actor) source_I
        (TryRemovePending actor start v owner loc).
    Proof. apply tryRemove_ready_stable. Qed.

    Lemma tryRemove_post_entails_I actor start v owner loc removed :
      ⊨ TryRemovePost actor start v owner loc removed ==>> source_I.
    Proof. unfold TryRemovePost. apply completed_entails_I. Qed.

    Lemma tryRemove_post_stable actor start v owner loc removed :
      AssertionsSingle.A.Stable (source_R actor) source_I
        (TryRemovePost actor start v owner loc removed).
    Proof. unfold TryRemovePost. apply completed_stable. Qed.

    Lemma tryRemove_inv_update actor start (v : A) owner loc :
      AssertionsSingle.PUpdate (source_G actor)
        (Build_ThreadEvent actor
          (InvEv (lpool_tryRemove owner loc)))
        (TryRemoveReady actor start v owner loc)
        (TryRemovePending actor start v owner loc).
    Proof.
      pupdate_intros_atomic.
      unfold TryRemoveReady in Hpre.
      destruct Hpre as [HIpre [Hinside Hdata]].
      destruct Hdata as
        (a & N & Hrho & Htoken & Has & Hcs & Hvalue & Hstatus).
      pose proof HIpre as HIpre0.
      destruct HIpre as (a0 & Hrho0 & Hgraph & Hprotocol & Hsession & Howned).
      simpl in Hrho, Hrho0. subst ρ1.
      inversion Hrho; subst a.
      simpl in Hgraph, Hprotocol, Hsession, Howned, Hcs, Htoken.
      exists (TSAReady a0), π1. split; [apply rt_refl|].
      assert (HIpost : source_I
        (@SinglePossState.Build_ProofStateSingle _ _
          (li_lts E) (li_lts F)
          (LPAtomicPending s0 actor0 (lpool_tryRemove owner0 loc0))
          (TSAReady a0) π1)).
      { exists a0. simpl. split; [reflexivity|]. split; [exact Hgraph|].
        split; [exact Hprotocol|]. split; [exact Hsession|exact Howned]. }
      split.
      - unfold TryRemovePending, TryRemoveReady.
        split; [exact HIpost|]. split; [exact Hinside|].
        exists a0, N. simpl. repeat split; assumption.
      - unfold source_G.
        refine (conj _ (conj _ (conj _ (conj _ _)))).
        + exact HIpre0.
        + exact HIpost.
        + apply graph_evol_refl.
        + intros observer Hneq. unfold actor_local_eq; simpl.
          repeat split; reflexivity.
        + reflexivity.
    Qed.

    Lemma tryRemove_ready_no_error actor start (v : A) owner loc :
      ⊨ TryRemoveReady actor start v owner loc ==>>
        AssertionsSingle.A.ANoError
          (Build_ThreadEvent actor
            (InvEv (lpool_tryRemove owner loc))).
    Proof.
      intros [sigma rho pi] Hpre Herror.
      unfold TryRemoveReady in Hpre.
      destruct Hpre as [HI [Hinside Hdata]].
      destruct Hdata as
        (a & N & Hrho & Htoken & Has & Hcs & Hvalue & Hstatus).
      destruct HI as (a0 & Hrho0 & Hgraph & Hprotocol & Hsession & Howned).
      rewrite Hrho in Hrho0. inversion Hrho0; subst a0.
      simpl in Hgraph, Howned.
      assert (Hvertex :
        is_vertex (concrete_payload sigma) (pair owner loc)).
      { destruct Hgraph as [HV _]. unfold is_vertex.
        rewrite HV, Hvalue. discriminate. }
      assert (Howner : ThreadDomain.contains D owner).
      { exact (Howned (pair owner loc) Hvertex). }
      simpl in Herror.
      remember
        (Build_ThreadEvent actor
          (InvEv (lpool_tryRemove owner loc))) as ev eqn:Hev in Herror.
      inversion Herror; subst; try contradiction.
      all: inversion_thread_event_eq; contradiction.
    Qed.

    Lemma tryRemove_res_update actor start (v : A) owner loc removed :
      AssertionsSingle.PUpdate (source_G actor)
        (Build_ThreadEvent actor
          (ResEv (lpool_tryRemove owner loc) removed))
        (TryRemovePending actor start v owner loc)
        (TryRemovePost actor start v owner loc removed).
    Proof.
      pupdate_intros_atomic.
      - (* removed *)
        match goal with
        | H : is_live _ _ |- _ => rename H into Hlive
        end.
        unfold TryRemovePending, TryRemoveReady in Hpre.
        destruct Hpre as [HIpre [Hinside Hdata]].
        destruct Hdata as
          (a & N & Hrho & Htoken & Has & Hcs & Hvalue & Hstatus).
        pose proof HIpre as HIpre0.
        destruct HIpre as
          (a0 & Hrho0 & Hgraph & Hprotocol & Hsession & Howned).
        simpl in Hrho, Hrho0. subst ρ1.
        inversion Hrho; subst a.
        simpl in Hgraph, Hprotocol, Hsession, Howned, Htoken, Has, Hcs.
        assert (Hastep : StepTryStackAux
          (Build_ThreadEvent actor0
            (ResEv (tsa_trypop start) (TSuccNode v owner0 loc0)))
          (TSAReady a0)
          (TSAReady (tsa_remove_node actor0 (pair owner0 loc0) a0))).
        { destruct Hstatus as [Hgarbage|[Htop|Helim]].
          - exfalso. destruct Hlive as [_ Hnotgarbage]. apply Hnotgarbage.
            destruct Hgraph as [_ [_ [_ HG]]]. now rewrite HG.
          - eapply step_tsa_trypop_succ;
              [exact Has|exact Htop|exact Hvalue|reflexivity].
          - destruct Helim as (N0 & Hstarts & Hnot).
            eapply step_tsa_trypop_elim;
              [exact Has|exact Hstarts|exact Hnot| |exact Hvalue|
               reflexivity].
            apply (proj1 (graph_represents_is_live _ _ _ Hgraph)).
            exact Hlive. }
        exists
          (TSAReady (tsa_remove_node actor0 (pair owner0 loc0) a0)),
          (TMap.add actor0
            (ls_linr (tsa_trypop start) (TSuccNode v owner0 loc0)) π1).
        split.
        + apply rt_step. eapply ps_ret; [exact Hastep|exact Htoken].
        + assert (HIpost : source_I
            (@SinglePossState.Build_ProofStateSingle _ _
              (li_lts E) (li_lts F)
              (LPReady (mark_garbage (pair owner0 loc0) s))
              (TSAReady
                (tsa_remove_node actor0 (pair owner0 loc0) a0))
              (TMap.add actor0
                (ls_linr (tsa_trypop start) (TSuccNode v owner0 loc0))
                π1))).
          { exists (tsa_remove_node actor0 (pair owner0 loc0) a0).
            split; [reflexivity|]. split.
            - now apply graph_represents_trypop_succ.
            - split; [|split].
              + eapply snapshot_protocol_trypop_succ; eauto.
              + eapply session_protocol_close;
                  [exact Hsession|reflexivity|reflexivity|reflexivity|
                   reflexivity| |].
                * new_token_neq.
                * other_token.
              + now apply vertices_owned_mark_garbage. }
          split.
          * unfold TryRemovePost, Completed. split; [exact HIpost|].
            unfold AssertionsSingle.ALin. simpl. apply TMap.gss.
          * unfold source_G.
            refine (conj _ (conj _ (conj _ (conj _ _)))).
            -- exact HIpre0.
            -- exact HIpost.
            -- apply graph_evol_mark_garbage.
            -- intros observer Hneq. unfold actor_local_eq; simpl.
               repeat split; try reflexivity;
                 rewrite ?TMap.gro, ?TMap.gso by congruence; reflexivity.
            -- exact Logic.I.
      - (* not removed *)
        unfold TryRemovePending, TryRemoveReady in Hpre.
        destruct Hpre as [HIpre [Hinside Hdata]].
        destruct Hdata as
          (a & N & Hrho & Htoken & Has & Hcs & Hvalue & Hstatus).
        pose proof HIpre as HIpre0.
        destruct HIpre as
          (a0 & Hrho0 & Hgraph & Hprotocol & Hsession & Howned).
        simpl in Hrho, Hrho0. subst ρ1.
        inversion Hrho; subst a.
        simpl in Hgraph, Hprotocol, Hsession, Howned, Htoken, Has, Hcs.
        exists (TSAReady (tsa_clear_snapshot actor0 a0)),
          (TMap.add actor0 (ls_linr (tsa_trypop start) TFail) π1).
        split.
        + apply rt_step. eapply ps_ret.
          * eapply step_tsa_trypop_fail with (N := N);
              [exact Has|reflexivity].
          * exact Htoken.
        + assert (HIpost : source_I
            (@SinglePossState.Build_ProofStateSingle _ _
              (li_lts E) (li_lts F) (LPReady s0)
              (TSAReady (tsa_clear_snapshot actor0 a0))
              (TMap.add actor0 (ls_linr (tsa_trypop start) TFail) π1))).
          { exists (tsa_clear_snapshot actor0 a0).
            split; [reflexivity|]. split.
            - now apply graph_represents_trypop_fail.
            - split; [|split].
              + eapply snapshot_protocol_trypop_fail; eauto.
              + eapply session_protocol_keep;
                  [exact Hsession|reflexivity|reflexivity|reflexivity|
                   reflexivity| | |].
                * old_token_neq Htoken.
                * new_token_neq.
                * other_token.
              + exact Howned. }
          split.
          * unfold TryRemovePost, Completed. split; [exact HIpost|].
            unfold AssertionsSingle.ALin. simpl. apply TMap.gss.
          * unfold source_G.
            refine (conj _ (conj _ (conj _ (conj _ _)))).
            -- exact HIpre0.
            -- exact HIpost.
            -- apply graph_evol_refl.
            -- intros observer Hneq. unfold actor_local_eq; simpl.
               repeat split; try reflexivity;
                 rewrite ?TMap.gro, ?TMap.gso by congruence; reflexivity.
            -- exact Logic.I.
    Qed.

    Lemma tryPop_inside_no_error actor start :
      ⊨ TryPopInside actor start ==>>
        AssertionsSingle.A.ANoError
          (Build_ThreadEvent actor (InvEv (lpool_getTop start))).
    Proof.
      intros [sigma rho pi] [[HI Htoken] [Hinside Hts]] Herror.
      destruct HI as (s & Hrho & Hgraph & Hprotocol & Hsession & Howned).
      simpl in Hrho, Hts. rewrite Hrho in Hts. simpl in Hts.
      assert (Hcts :
        TMap.find actor (lp_pop_ts (concrete_payload sigma)) = Some start).
      { destruct Hsession as [_ [H2 _]]. now apply H2. }
      simpl in Herror.
      remember (Build_ThreadEvent actor (InvEv (lpool_getTop start)))
        as ev eqn:Hev in Herror.
      inversion Herror; subst; try contradiction.
      all: inversion_thread_event_eq; contradiction.
    Qed.

    Lemma trypop_active_or_error actor start w :
      SActive actor (tsa_trypop start) w ->
      lift_assert (TryPopInside actor start) w \/
      AssertionsSet.APError w.
    Proof.
      intros [x [Hview [HI Htoken]]].
      pose proof HI as HI0.
      destruct HI0 as (s & Hrho & _).
      destruct (ThreadDomain.contains_dec D actor) as [Hinside|Houtside].
      - destruct (classic (TMap.find actor (tsa_pop_ts s) = Some start))
          as [Hts|Hts].
        + left. exists x. split; [exact Hview|].
          split; [split; assumption|]. split; [exact Hinside|].
          rewrite Hrho. exact Hts.
        + right. destruct w as [sigma Delta].
          econstructor.
          * eapply singleton_view_member; eauto.
          * apply rt_step. eapply (ps_error actor (tsa_trypop start)).
            -- rewrite Hrho.
               eapply error_tsa_trypop_no_session;
                 [exact Hts|reflexivity].
            -- exact Htoken.
      - right. destruct w as [sigma Delta].
        econstructor.
        + eapply singleton_view_member; eauto.
        + apply rt_step. eapply (ps_error actor (tsa_trypop start)).
          * rewrite Hrho.
            eapply error_tsa_actor_outside;
              [exact Houtside|reflexivity].
          * exact Htoken.
    Qed.

    Lemma tryRemove_call_triple actor start (v : A) owner loc :
      SetLogic.HTripleProvable (R actor) (G actor) SI actor
        (lift_assert (TryRemoveReady actor start v owner loc))
        (lpool_tryRemove owner loc >= removed =>
          Ret (if removed
               then TSuccNode v owner loc
               else TFail))
        (fun ret => SCompleted actor (tsa_trypop start) ret).
    Proof.
      eapply singleton_provable_vis_safe with
        (P' := TryRemovePending actor start v owner loc)
        (Q' := TryRemovePost actor start v owner loc).
      - apply tryRemove_ready_no_error.
      - apply tryRemove_pending_entails_I.
      - intros removed. apply tryRemove_post_entails_I.
      - apply tryRemove_pending_stable.
      - intros removed. apply tryRemove_post_stable.
      - apply tryRemove_inv_update.
      - intros removed. apply tryRemove_res_update.
      - intros removed. eapply singleton_provable_ret_safe.
        + unfold TryRemovePost. apply ImplRefl.
        + apply completed_entails_I.
        + apply completed_stable.
    Qed.

    Lemma trypop_method_triple actor start :
      SetLogic.HTripleProvable (R actor) (G actor) SI actor
        (SActive actor (tsa_trypop start))
        (trypop_impl D start actor)
        (fun ret => SCompleted actor (tsa_trypop start) ret).
    Proof.
      eapply SetLogic.provable_perror with
        (P' := lift_assert (TryPopInside actor start)).
      - intros w Hactive. now apply trypop_active_or_error.
      - unfold trypop_impl.
        eapply singleton_provable_vis_safe with
          (P' := GetTopPending actor start)
          (Q' := GetTopPost actor start).
        + apply tryPop_inside_no_error.
        + apply getTop_pending_entails_I.
        + intros result. apply getTop_post_entails_I.
        + apply getTop_pending_stable.
        + intros result. apply getTop_post_stable.
        + apply getTop_inv_update.
        + intros result. apply getTop_res_update.
        + intros result. destruct result as [v owner loc| |]; simpl.
          * apply tryRemove_call_triple.
          * eapply singleton_provable_ret_safe.
            -- apply ImplRefl.
            -- apply completed_entails_I.
            -- apply completed_stable.
          * eapply singleton_provable_ret_safe.
            -- apply ImplRefl.
            -- apply completed_entails_I.
            -- apply completed_stable.
    Qed.

    Lemma active_closes_invariant actor op :
      ⊨ SActive actor op ==>> SI.
    Proof.
      intros w Hactive.
      eapply lift_impl; [apply active_entails_I|exact Hactive].
    Qed.

    Program Definition MTryStackAuxElim :
        layer_implementation_simulation E F :=
      {| li_impl := try_stack_aux_elim_impl D |}.
    Next Obligation.
      eapply SetLogic.soundness with (R := R) (G := G) (I := SI).
      - exact valid_rg.
      - exact parallel_compatible.
      - intros actor op. destruct op as [v| |start].
        + exists (SActive actor (tsa_push v)).
          exists (fun ret => SCompleted actor (tsa_push v) ret).
          constructor.
          * intros w Hcompose. eapply set_ginv_exposes_active;
              exact Hcompose.
          * apply active_closes_invariant.
          * apply lift_stable. apply active_stable.
          * intros ret w Hcompose. eapply set_gret_closes_completed;
              exact Hcompose.
          * intros ret sigma Delta Hcompleted rho pi Hposs.
            eapply completed_has_return_token; eauto.
          * apply push_method_triple.
        + exists (SActive actor tsa_startPop).
          exists (fun ret => SCompleted actor tsa_startPop ret).
          constructor.
          * intros w Hcompose. eapply set_ginv_exposes_active;
              exact Hcompose.
          * apply active_closes_invariant.
          * apply lift_stable. apply active_stable.
          * intros ret w Hcompose. eapply set_gret_closes_completed;
              exact Hcompose.
          * intros ret sigma Delta Hcompleted rho pi Hposs.
            eapply completed_has_return_token; eauto.
          * apply startPop_method_triple.
        + exists (SActive actor (tsa_trypop start)).
          exists (fun ret => SCompleted actor (tsa_trypop start) ret).
          constructor.
          * intros w Hcompose. eapply set_ginv_exposes_active;
              exact Hcompose.
          * apply active_closes_invariant.
          * apply lift_stable. apply active_stable.
          * intros ret w Hcompose. eapply set_gret_closes_completed;
              exact Hcompose.
          * intros ret sigma Delta Hcompleted rho pi Hposs.
            eapply completed_has_return_token; eauto.
          * apply trypop_method_triple.
      - exact initial_SI.
    Qed.

    Definition MTryStackAuxElimLinearizable :
        layer_implementation_linearizability E F :=
      LISim2LILin MTryStackAuxElim.

    Definition MListPoolTryStackAuxElim :
        layer_implementation_linearizability
          (@ListPoolElimProof.E A D) F :=
      LIVComp (@ListPoolElimProof.MListPoolElimLinearizable A D)
        MTryStackAuxElimLinearizable.

  End Proof.

  Print Assumptions MTryStackAuxElimLinearizable.

End TryStackAuxElimProof.
