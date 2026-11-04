Require Import FMapPositive.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.PArith.PArith.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Program.Equality.
Require Import Coq.Relations.Relation_Operators.
Require Import QArith Qcanon.
Require Import Lia.

Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import Logics.
Require Import Assertion.
Require Import TPSimulationSet.
Require Import RGILogicSet.
Require Import CompLinLayer.

Require Import examples.Common.Heap.
Require Import examples.Common.ThreadDomain.
Require Import examples.TSStack.Shared.TimestampSpec.
Require Import examples.TSStack.Basic.ListPoolSpec.
Require Import examples.TSStack.WithElim.ListPoolElimSpec.
Require Import examples.TSStack.WithElim.TryStackAuxElimSpec.
Require Import examples.TSStack.WithElim.DagStackSpec.
Require Import examples.TSStack.WithElim.DagStack.
Require Import examples.TSStack.WithElim.DagStackHistory.
Require Import examples.TSStack.WithElim.ListPoolElimProof.
Require Import examples.TSStack.WithElim.TryStackAuxElimProof.


(** Correctness proof for the DagStack layer over TryStackAuxElim: the
    plan machinery of the rewritten Appendix A.4 ([I_lag], [I_pop],
    [specS], guarantees) generalized to pop sessions and elimination
    (docs/plans/TSStackEliminationPlan.tex, Section 7.4).

    A plan is a legal history (session-based legality of
    [DagStackHistory]) agreeing with the canonical history on committed
    pops and speculating at most one pop per open session.  There is no
    failing set: the atomic pop has no fail result, so a failed retry
    linearizes nothing and only re-speculates.  The retry loop of the
    implementation is verified with [provable_doloop]; its loop assertion
    is [I] with the actor's session open and no snapshot pending. *)
Module DagStackProof.
  Import Reg LinCCALBase LTSSpec Lang Semantics.
  Import AssertionsSet.
  Import TPSimulationSet.TPSimulation CompLinLayer.
  Import TimestampSpec ListPoolSpec ListPoolElimSpec TryStackAuxElimSpec DagStackSpec DagStackImpl.
  Import DagStackHistory.
  Import (coercions, canonicals, notations) Sig.
  Module SetLogic := RGILogicSet.RGILogic.
  Import SetLogic.

  Open Scope prog_scope.
  Open Scope assertion_scope.
  Open Scope rg_relation_scope.

  Section Proof.
    Context {A : Type} (D : ThreadDomain.t).

    Definition E : layer_interface := @DagStackImpl.E A D.
    Definition F : layer_interface := @DagStackImpl.F A D.

    Definition concrete_state := State (li_lts E).
    Definition abstract_state := State (li_lts F).
    Definition lin_state := @LinState (li_sig F).
    Definition proof_state :=
      @SetPossState.ProofStateSet _ _ (li_lts E) (li_lts F).
    Definition assertion := @Logics.Assertion proof_state.
    Definition rg_relation :=
      @AssertionsSet.A.RGRelation _ _ (li_lts E) (li_lts F).
    Definition config := @AbstractConfig _ (li_lts F).

    Implicit Types (s : @TryStackAuxState A).
    Implicit Types (r : @DagStackState A).
    Implicit Types (π : tmap lin_state).
    Implicit Types (h H : history).

    (** * Concrete payload and tokens *)

    (** The graph seen by the proof.  In the atomic empty branch the
        actor's session is already dead: [tsa_drop_session] removes it, and
        the response is [tsa_tick] of this view
        ([DagStackHistory.close_session_tick]). *)
    Definition payload (c : @TryStackAuxControl A) : @TryStackAuxState A :=
      match c with
      | TSAReady s => s
      | TSAAtomicPending s β _ => tsa_drop_session β s
      end.

    Definition graph_of (w : proof_state) : @TryStackAuxState A :=
      payload (SetPossState.σ w).

    Definition push_inv_token (v : A) : lin_state := ls_inv (dag_push v).
    Definition push_lini_token (v : A) : lin_state := ls_lini (dag_push v).
    Definition push_ret_token (v : A) : lin_state := ls_linr (dag_push v) tt.
    Definition pop_inv_token : lin_state := ls_inv dag_pop.
    Definition pop_lini_token : lin_state := ls_lini dag_pop.
    Definition pop_succ_token (v : A) (n : LPNodeId) : lin_state :=
      ls_linr dag_pop (PNode v (fst n) (snd n)).
    Definition pop_empty_token : lin_state := ls_linr dag_pop PEmpty.

    (** A session of [β] is open when its start set is recorded. *)
    Definition session_open s (β : tid) : Prop :=
      TMap.find β (tsa_pop_starts s) <> None.

    (** * Representation of a plan (paper's [Rep]) *)

    Record rep_state s h r : Prop := {
      rs_vertex_placed : forall x, placed h x -> ds_vertices r x = tsa_vertices s x;
      rs_vertex_unplaced : forall x, ~ placed h x -> ds_vertices r x = None;
      rs_edges : forall x y,
        ds_edges r x y <-> placed h x /\ placed h y /\ above s h x y;
      rs_pending : forall β l,
        TMap.find β (ds_pending_pushes r) = Some l <->
        TMap.find β (tsa_pending_pushes s) = Some l /\ placed h (pair β l);
      rs_garbage : forall x, ds_garbage r x <-> popped h x;
    }.

    Definition spec_pop_of h s (β : tid) : Prop :=
      exists n p, h_pop h n = Some (pair p β) /\ tsa_removals s n = None.

    (** Tokens of a plan's representation: a thread inside a pop (open
        session) holds [•(pop, Succ(v,n))] when the plan speculates its pop
        of [n], and [◦(pop)] otherwise. *)
    Record rep_tokens s h π : Prop := {
      rt_push_unplaced : forall β l v,
        TMap.find β (tsa_pending_pushes s) = Some l ->
        tsa_vertices s (pair β l) = Some v -> ~ placed h (pair β l) ->
        TMap.find β π = Some (push_inv_token v);
      rt_push_placed : forall β l v,
        TMap.find β (tsa_pending_pushes s) = Some l ->
        tsa_vertices s (pair β l) = Some v -> placed h (pair β l) ->
        TMap.find β π = Some (push_lini_token v);
      rt_pop_spec : forall β n p v,
        session_open s β ->
        h_pop h n = Some (pair p β) -> tsa_removals s n = None ->
        tsa_vertices s n = Some v ->
        TMap.find β π = Some (pop_succ_token v n);
      rt_pop_pending : forall β,
        session_open s β -> ~ spec_pop_of h s β ->
        TMap.find β π = Some pop_inv_token;
    }.

    (** * Plans (P1)-(P3) *)

    Record plan s H h : Prop := {
      pl_legal : legal s h;
      pl_committed : forall m, tsa_removals s m <> None -> h_pop h m = h_pop H m;
      pl_later : forall x p, h_inv h x = Some p ->
        exists q, h_inv H x = Some q /\ ple q p;
    }.

    (** * The lag relation and the invariant *)

    Record lag s r π : Prop := {
      lag_vertices : forall x v, ds_vertices r x = Some v -> tsa_vertices s x = Some v;
      lag_unplaced : forall x, tsa_is_vertex s x -> ~ ds_is_vertex r x ->
        tsa_is_pending s x /\
        exists v, tsa_vertices s x = Some v /\
          TMap.find (fst x) π = Some (push_inv_token v);
      lag_placed_pending : forall β l v,
        TMap.find β (tsa_pending_pushes s) = Some l ->
        tsa_vertices s (pair β l) = Some v -> ds_is_vertex r (pair β l) ->
        TMap.find β π = Some (push_lini_token v);
      lag_pending : forall β l,
        TMap.find β (ds_pending_pushes r) = Some l <->
        TMap.find β (tsa_pending_pushes s) = Some l /\ ds_is_vertex r (pair β l);
      lag_edges_in : forall x y, tsa_edges s x y ->
        ds_is_vertex r x -> ds_is_vertex r y -> ds_edges r x y;
      lag_edges_out : forall x y, ds_edges r x y ->
        ds_is_vertex r x /\ ds_is_vertex r y /\
        (tsa_edges s x y \/
         (~ tsa_edges s x y /\ ~ tsa_edges s y x /\ ~ tsa_is_pending s y));
      lag_garbage_in : forall x, tsa_garbage s x -> ds_garbage r x;
      lag_garbage_vertex : forall x, ds_garbage r x -> ds_is_vertex r x;
      lag_spec_justified : forall x, ds_garbage r x -> ~ tsa_garbage s x ->
        exists β v, session_open s β /\
          tsa_vertices s x = Some v /\ TMap.find β π = Some (pop_succ_token v x);
      lag_succ_garbage : forall β v x,
        TMap.find β π = Some (pop_succ_token v x) -> ds_garbage r x;
    }.

    Definition I_lag s (Δ : config) : Prop :=
      forall ρ π, Δ ρ π -> exists r, ρ = DSReady r /\ lag s r π.

    Definition I_pop s H (Δ : config) : Prop :=
      forall h, plan s H h ->
        exists r π, Δ (DSReady r) π /\ rep_state s h r /\ rep_tokens s h π.

    Definition I_state s (Δ : config) : Prop :=
      ghost_wf s /\ I_lag s Δ /\
      exists H, canonical s H /\ I_pop s H Δ.

    Definition I : assertion :=
      fun w => I_state (graph_of w) (SetPossState.Δ w).

    (** * Speculation steps *)

    Variant placeS (σ : concrete_state) :
        abstract_state -> tmap lin_state ->
        abstract_state -> tmap lin_state -> Prop :=
    | place_step r π β l v :
        TMap.find β (tsa_pending_pushes (payload σ)) = Some l ->
        tsa_vertices (payload σ) (pair β l) = Some v ->
        TMap.find β π = Some (push_inv_token v) ->
        TMap.find β (ds_pending_pushes r) = None ->
        ds_fresh_node r (pair β l) ->
        placeS σ (DSReady r) π
          (DSReady (ds_start_push β l v r)) (TMap.add β (push_lini_token v) π).

    (** A speculative pop: a thread with an open session pops a top live
        vertex of the possibility's own graph. *)
    Variant popS (σ : concrete_state) :
        abstract_state -> tmap lin_state ->
        abstract_state -> tmap lin_state -> Prop :=
    | pop_step r π β n v :
        session_open (payload σ) β ->
        TMap.find β π = Some pop_inv_token ->
        tsa_vertices (payload σ) n = Some v ->
        ds_vertices r n = Some v ->
        lp_top (ds_is_live r) (ds_edges r) n ->
        popS σ (DSReady r) π
          (DSReady (ds_mark_garbage n r))
          (TMap.add β (pop_succ_token v n) (TMap.add β pop_lini_token π)).

    Definition spec_step (σ : concrete_state) ρ π ρ' π' : Prop :=
      placeS σ ρ π ρ' π' \/ popS σ ρ π ρ' π'.

    Inductive specS (σ : concrete_state) :
        abstract_state -> tmap lin_state ->
        abstract_state -> tmap lin_state -> Prop :=
    | spec_refl ρ π : specS σ ρ π ρ π
    | spec_trans ρ π ρ' π' ρ'' π'' :
        spec_step σ ρ π ρ' π' -> specS σ ρ' π' ρ'' π'' -> specS σ ρ π ρ'' π''.

    Lemma specS_snoc σ ρ π ρ' π' ρ'' π'' :
      specS σ ρ π ρ' π' -> spec_step σ ρ' π' ρ'' π'' -> specS σ ρ π ρ'' π''.
    Proof.
      intros Hc Hs. induction Hc.
      - eapply spec_trans; [exact Hs|constructor].
      - eapply spec_trans; [exact H|now apply IHHc].
    Qed.

    Lemma specS_app σ ρ π ρ' π' ρ'' π'' :
      specS σ ρ π ρ' π' -> specS σ ρ' π' ρ'' π'' -> specS σ ρ π ρ'' π''.
    Proof.
      intros H1 H2. induction H1; [exact H2|]. eapply spec_trans; eauto.
    Qed.

    (** ** Speculation steps are abstract DagStack steps *)

    Lemma ds_push_inv_step β l (v : A) r :
      TMap.find β (ds_pending_pushes r) = None ->
      ds_fresh_node r (pair β l) ->
      Step (li_lts F) (Build_ThreadEvent β (InvEv (dag_push v)))
        (DSReady r) (DSReady (ds_start_push β l v r)).
    Proof. intros. eapply step_ds_push_inv; eauto. Qed.

    Lemma ds_push_res_step β l (v : A) r :
      TMap.find β (ds_pending_pushes r) = Some l ->
      Step (li_lts F) (Build_ThreadEvent β (ResEv (dag_push v) tt))
        (DSReady r) (DSReady (ds_finish_push β r)).
    Proof. intros. eapply step_ds_push_res; eauto. Qed.

    Lemma ds_pop_inv_step β r :
      Step (li_lts F) (Build_ThreadEvent β (InvEv dag_pop))
        (DSReady r) (DSAtomicPending r β dag_pop).
    Proof. eapply step_ds_pop_inv; eauto. Qed.

    Lemma ds_pop_succ_step β n (v : A) r :
      lp_top (ds_is_live r) (ds_edges r) n ->
      ds_vertices r n = Some v ->
      Step (li_lts F) (Build_ThreadEvent β (ResEv dag_pop (PNode v (fst n) (snd n))))
        (DSAtomicPending r β dag_pop) (DSReady (ds_mark_garbage n r)).
    Proof. intros. eapply step_ds_pop_succ; eauto. Qed.

    Lemma ds_pop_empty_step β r :
      ds_all_vertices_garbage r ->
      Step (li_lts F) (Build_ThreadEvent β (ResEv dag_pop PEmpty))
        (DSAtomicPending r β dag_pop) (DSReady r).
    Proof. intros. eapply step_ds_pop_empty; eauto. Qed.

    Lemma spec_step_poss_steps σ ρ π ρ' π' :
      spec_step σ ρ π ρ' π' -> poss_steps (PossOk ρ π) (PossOk ρ' π').
    Proof.
      intros [Hs|Hs].
      - inversion Hs; subst. apply rt_step.
        eapply (@ps_inv _ (li_lts F) β (dag_push v) (DSReady r)).
        + apply ds_push_inv_step; assumption.
        + exact H1.
      - inversion Hs; subst. eapply rt_trans.
        + apply rt_step.
          eapply (@ps_inv _ (li_lts F) β dag_pop (DSReady r)
            (DSAtomicPending r β dag_pop) π).
          * apply ds_pop_inv_step.
          * exact H0.
        + apply rt_step.
          eapply (@ps_ret _ (li_lts F) β dag_pop (PNode v (fst n) (snd n))
            (DSAtomicPending r β dag_pop) (DSReady (ds_mark_garbage n r))).
          * apply ds_pop_succ_step; assumption.
          * apply TMap.gss.
    Qed.

    Lemma specS_poss_steps σ ρ π ρ' π' :
      specS σ ρ π ρ' π' -> poss_steps (PossOk ρ π) (PossOk ρ' π').
    Proof.
      intros Hc. induction Hc; [apply rt_refl|].
      eapply rt_trans; [eapply spec_step_poss_steps; eauto|exact IHHc].
    Qed.

    Lemma spec_step_ready σ ρ π ρ' π' :
      spec_step σ ρ π ρ' π' -> exists r', ρ' = DSReady r'.
    Proof. intros [Hs|Hs]; inversion Hs; subst; eauto. Qed.

    (** * Generic rule lemmas (plan, departure 9) *)

    (** The paper's [pstep(S) ]: [Δ'] is exactly the [S]-image of [Δ].
        Coq's [PStep S] only bounds [Δ'] from above. *)
    Definition poss_relation : Type :=
      @PossibilityRelation _ _ (li_lts E) (li_lts F).

    Definition PStepExact (S : poss_relation) : rg_relation :=
      fun w w' =>
        SetPossState.σ w = SetPossState.σ w' /\
        forall ρ' π', SetPossState.Δ w' ρ' π' <->
          exists ρ π, SetPossState.Δ w ρ π /\ S (SetPossState.σ w) ρ π ρ' π'.

    Lemma PStepExact_PStep (S : poss_relation) :
      (forall σ ρ π ρ' π', S σ ρ π ρ' π' -> poss_steps (PossOk ρ π) (PossOk ρ' π')) ->
      (PStepExact S ⊆ PStep S)%RGRelation.
    Proof.
      intros Hsteps w w' [Hσ Hiff]. split; [exact Hσ|].
      intros ρ' π' Hposs'. apply Hiff in Hposs'.
      destruct Hposs' as (ρ & π & Hposs & HS). exists ρ, π.
      split; [exact Hposs|]. split; [exact HS|]. eapply Hsteps; eauto.
    Qed.

    Variant ac_image_prop (S : poss_relation)
        (σ : concrete_state) (Δ : config) : @AbstractConfigProp _ (li_lts F) :=
    | ACImage ρ π ρ' π' (Hposs : Δ ρ π) (HS : S σ ρ π ρ' π') :
        ac_image_prop S σ Δ ρ' π'.

    Program Definition ac_image (S : poss_relation) σ (Δ : config)
        (Hsteps : forall ρ π ρ' π', S σ ρ π ρ' π' ->
          poss_steps (PossOk ρ π) (PossOk ρ' π'))
        (Hne : exists ρ π ρ' π', Δ ρ π /\ S σ ρ π ρ' π') : config :=
      {| ac_active := ac_active Δ; ac_prop := ac_image_prop S σ Δ |}.
    Next Obligation.
      destruct Hne as (ρ & π & ρ' & π' & Hposs & HS).
      exists ρ', π'. econstructor; eauto.
    Qed.
    Next Obligation.
      inversion H; subst.
      eapply domain_equiv_trans.
      - apply domain_equiv_symm. eapply poss_steps_domain. eapply Hsteps; eauto.
      - eapply ac_domain; eauto.
    Qed.

    (** Figure 10's [pupd-pstep] in exact-image form. *)
    Lemma PUpdateIdPStepExact (S : poss_relation) (P : assertion) :
      (forall σ ρ π ρ' π', S σ ρ π ρ' π' -> poss_steps (PossOk ρ π) (PossOk ρ' π')) ->
      (forall σ Δ, P (σ, Δ) -> exists ρ π ρ' π', Δ ρ π /\ S σ ρ π ρ' π') ->
      PUpdateId (PStepExact S) P (ComposeA P (PStepExact S)).
    Proof.
      intros Hsteps Hne σ Δ HP.
      exists (ac_image S σ Δ (Hsteps σ) (Hne σ Δ HP)). split.
      - intros ρ' π' Hposs'. inversion Hposs'; subst.
        econstructor; [exact Hposs|]. eapply Hsteps; eauto.
      - assert (Hrel : PStepExact S (σ, Δ)
          (σ, ac_image S σ Δ (Hsteps σ) (Hne σ Δ HP))).
        { split; [reflexivity|]. intros ρ' π'. simpl. split.
          - intros Hp. inversion Hp; subst. eauto.
          - intros (ρ & π & Hposs & HS). econstructor; eauto. }
        split; [|exact Hrel]. exists (σ, Δ). split; assumption.
    Qed.

    (** The underlay event triple: the concrete step with [Δ] unchanged. *)
    Definition EvRel (ev : @ThreadEvent (li_sig E)) : rg_relation :=
      fun w w' =>
        Step (li_lts E) ev (SetPossState.σ w) (SetPossState.σ w') /\
        SetPossState.Δ w' = SetPossState.Δ w.

    Lemma PUpdateEventId ev (P : assertion) :
      PUpdate (EvRel ev) ev P
        (fun w' => exists σ, P (σ, SetPossState.Δ w') /\
          Step (li_lts E) ev σ (SetPossState.σ w')).
    Proof.
      intros σ Δ HP σ' Hstep. exists Δ. split; [apply ac_steps_refl|].
      split; [exists σ; simpl; auto|]. split; simpl; auto.
    Qed.

    (** Figure 10's [pupd-imply], with the relation recording the
        precondition (the paper's guarantees contain the preconditions'
        token facts). *)
    Lemma PUpdateIdImplyPre (P Q : assertion) :
      (⊨ P ==>> Q) -> PUpdateId (ComposeR' P GId) P Q.
    Proof.
      intros Himpl σ Δ HP. exists Δ. split; [apply ac_steps_refl|].
      split; [apply Himpl; exact HP|]. split; [reflexivity|exact HP].
    Qed.

    Lemma pstep_iff_change_σ (S : poss_relation) (Δ Δ' : config) σ σ'' :
      (forall ρ' π', Δ' ρ' π' <-> exists ρ π, Δ ρ π /\ S σ ρ π ρ' π') -> σ = σ'' ->
      (forall ρ' π', Δ' ρ' π' <-> exists ρ π, Δ ρ π /\ S σ'' ρ π ρ' π').
    Proof. intros Hiff <-. exact Hiff. Qed.

    (** A possibility update may record its precondition in the relation. *)
    Lemma PUpdateIdRecordPre (G : rg_relation) (P Q : assertion) :
      PUpdateId G P Q -> PUpdateId (ComposeR' P G) P Q.
    Proof.
      intros Hupd σ Δ HP. destruct (Hupd σ Δ HP) as (Δ' & Hsteps & HQ & HG).
      exists Δ'. split; [exact Hsteps|]. split; [exact HQ|]. split; assumption.
    Qed.

    (** * Shapes of the underlay steps *)

    Lemma tsa_push_inv_shape α (v : A) (σ σ' : concrete_state) :
      Step (li_lts E) (Build_ThreadEvent α (InvEv (tsa_push v))) σ σ' ->
      exists s l,
        σ = TSAReady s /\
        TMap.find α (tsa_pending_pushes s) = None /\
        tsa_fresh_node s (pair α l) /\
        σ' = TSAReady (tsa_start_push α l v s).
    Proof.
      intros Hstep. simpl in Hstep. inversion Hstep; subst;
        match goal with
        | H : Build_ThreadEvent _ _ = Build_ThreadEvent _ _ |- _ =>
            dependent destruction H
        end.
      do 2 eexists. split; [reflexivity|]. split; [eassumption|].
      split; [eassumption|reflexivity].
    Qed.

    Lemma tsa_push_res_shape α (v : A) (σ σ' : concrete_state) :
      Step (li_lts E) (Build_ThreadEvent α (ResEv (tsa_push v) tt)) σ σ' ->
      exists s l,
        σ = TSAReady s /\
        TMap.find α (tsa_pending_pushes s) = Some l /\
        σ' = TSAReady (tsa_finish_push α s).
    Proof.
      intros Hstep. simpl in Hstep. inversion Hstep; subst;
        match goal with
        | H : Build_ThreadEvent _ _ = Build_ThreadEvent _ _ |- _ =>
            pose proof (f_equal te_tid H) as Hact; simpl in Hact; subst;
            pose proof (f_equal te_ev H) as Hev; simpl in Hev;
            first [ apply ResEvInversion in Hev; subst | inversion Hev ]
        end.
      do 2 eexists. split; [reflexivity|]. split; [eassumption|reflexivity].
    Qed.

    Lemma tsa_startPop_inv_shape α (σ σ' : concrete_state) :
      Step (li_lts E) (Build_ThreadEvent α (InvEv tsa_startPop)) σ σ' ->
      exists s, σ = TSAReady s /\ σ' = TSAReady (tsa_start_pop_session α s).
    Proof.
      intros Hstep. simpl in Hstep. inversion Hstep; subst;
        match goal with
        | H : Build_ThreadEvent _ _ = Build_ThreadEvent _ _ |- _ =>
            dependent destruction H
        end.
      eexists. split; reflexivity.
    Qed.

    Lemma tsa_startPop_res_shape α (ts : TS) (σ σ' : concrete_state) :
      Step (li_lts E) (Build_ThreadEvent α (ResEv tsa_startPop ts)) σ σ' ->
      exists s, σ = TSAReady s /\ σ' = TSAReady (tsa_finish_pop_session α ts s).
    Proof.
      intros Hstep. simpl in Hstep. inversion Hstep; subst;
        match goal with
        | H : Build_ThreadEvent _ _ = Build_ThreadEvent _ _ |- _ =>
            pose proof (f_equal te_tid H) as Hact; simpl in Hact; subst;
            pose proof (f_equal te_ev H) as Hev; simpl in Hev;
            first [ apply ResEvInversion in Hev; subst | inversion Hev ]
        end.
      eexists. split; reflexivity.
    Qed.

    Lemma tsa_trypop_inv_shape α (start : TS) (σ σ' : concrete_state) :
      Step (li_lts E) (Build_ThreadEvent α (InvEv (tsa_trypop start))) σ σ' ->
      exists s, σ = TSAReady s /\ TMap.find α (tsa_snapshots s) = None /\
        TMap.find α (tsa_pop_ts s) = Some start /\
        ((tsa_all_vertices_garbage s /\ σ' = TSAAtomicPending s α (tsa_trypop start)) \/
         σ' = TSAReady (tsa_start_snapshot α s)).
    Proof.
      intros Hstep. simpl in Hstep. inversion Hstep; subst;
        match goal with
        | H : Build_ThreadEvent _ _ = Build_ThreadEvent _ _ |- _ =>
            dependent destruction H
        end.
      - eexists. split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. left. auto.
      - eexists. split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. right. reflexivity.
    Qed.

    (** The removal case covers both the snapshot-top and the elimination
        responses; the disjunction is the case hypothesis of
        [DagStackHistory.fs_insertion]. *)
    Definition removal_case s (α : tid) (N : LPNodeSet) (n : LPNodeId) : Prop :=
      lp_top (fun m => N m /\ ~ tsa_garbage s m) (tsa_edges s) n \/
      (tsa_is_live s n /\
       exists N0, TMap.find α (tsa_pop_starts s) = Some N0 /\ ~ N0 n).

    Lemma tsa_trypop_res_shape α (start : TS) (ret : @TResult A) (σ σ' : concrete_state) :
      Step (li_lts E) (Build_ThreadEvent α (ResEv (tsa_trypop start) ret)) σ σ' ->
      (exists s, σ = TSAAtomicPending s α (tsa_trypop start) /\ ret = TSuccEmpty /\
         σ' = TSAReady (tsa_close_session α s)) \/
      (exists s N n v, σ = TSAReady s /\
         TMap.find α (tsa_snapshots s) = Some N /\
         removal_case s α N n /\
         tsa_vertices s n = Some v /\
         ret = TSuccNode v (fst n) (snd n) /\
         σ' = TSAReady (tsa_remove_node α n s)) \/
      (exists s N, σ = TSAReady s /\
         TMap.find α (tsa_snapshots s) = Some N /\ ret = TFail /\
         σ' = TSAReady (tsa_clear_snapshot α s)).
    Proof.
      intros Hstep. simpl in Hstep. inversion Hstep; subst;
        match goal with
        | H : Build_ThreadEvent _ _ = Build_ThreadEvent _ _ |- _ =>
            pose proof (f_equal te_tid H) as Hact; simpl in Hact; subst;
            pose proof (f_equal te_ev H) as Hev; simpl in Hev;
            inversion Hev; subst;
            try match goal with
            | Hx : existT _ _ _ = existT _ _ _ |- _ =>
                apply Eqdep.EqdepTheory.inj_pair2 in Hx; subst
            end;
            try (apply ResEvInversion in Hev; subst)
        end.
      - left. eexists. split; [reflexivity|]. split; reflexivity.
      - right. left. do 4 eexists. split; [reflexivity|]. split; [eassumption|].
        split; [left; eassumption|]. split; [eassumption|]. split; reflexivity.
      - right. left. do 4 eexists. split; [reflexivity|]. split; [eassumption|].
        split; [right; split; [eassumption|eauto]|]. split; [eassumption|]. split; reflexivity.
      - right. right. do 2 eexists. split; [reflexivity|]. split; [eassumption|]. split; reflexivity.
    Qed.


    (** * Facts about the abstract transformers *)

    Lemma ds_sp_vertices r β l (v : A) x :
      x <> pair β l -> ds_vertices (ds_start_push β l v r) x = ds_vertices r x.
    Proof. intros Hneq. unfold ds_start_push. simpl. apply node_update_neq. congruence. Qed.

    Lemma ds_sp_vertex_new r β l (v : A) :
      ds_vertices (ds_start_push β l v r) (pair β l) = Some v.
    Proof. unfold ds_start_push. simpl. apply node_update_eq. Qed.

    Lemma ds_sp_is_vertex r β l (v : A) x :
      ds_is_vertex (ds_start_push β l v r) x <-> ds_is_vertex r x \/ x = pair β l.
    Proof.
      unfold ds_is_vertex. destruct (node_eq_dec x (pair β l)) as [->|Hneq].
      - rewrite ds_sp_vertex_new. split; [auto|discriminate].
      - rewrite ds_sp_vertices by exact Hneq. tauto.
    Qed.

    Lemma ds_sp_pending_find r β l (v : A) β' :
      TMap.find β' (ds_pending_pushes (ds_start_push β l v r)) =
      if Pos.eq_dec β' β then Some l else TMap.find β' (ds_pending_pushes r).
    Proof.
      unfold ds_start_push. simpl. destruct (Pos.eq_dec β' β) as [->|Hneq].
      - apply TMap.gss.
      - apply TMap.gso. congruence.
    Qed.

    Lemma ds_sp_edges r β l (v : A) x y :
      ds_edges (ds_start_push β l v r) x y <->
      ds_edges r x y \/ (x = pair β l /\ ds_is_vertex r y /\ ~ ds_is_pending r y).
    Proof. reflexivity. Qed.

    Lemma tsa_sp_edges s β l (v : A) x y :
      tsa_edges (tsa_start_push β l v s) x y <->
      tsa_edges s x y \/ (x = pair β l /\ tsa_is_vertex s y /\ ~ tsa_is_pending s y).
    Proof. reflexivity. Qed.

    Lemma ds_sp_garbage r β l (v : A) x :
      ds_garbage (ds_start_push β l v r) x <-> ds_garbage r x.
    Proof. reflexivity. Qed.

    Lemma ds_fp_pending_find r β β' :
      TMap.find β' (ds_pending_pushes (ds_finish_push β r)) =
      if Pos.eq_dec β' β then None else TMap.find β' (ds_pending_pushes r).
    Proof.
      unfold ds_finish_push. simpl. destruct (Pos.eq_dec β' β) as [->|Hneq].
      - apply TMap.grs.
      - apply TMap.gro. congruence.
    Qed.

    Lemma ds_mg_garbage r n x :
      ds_garbage (ds_mark_garbage n r) x <-> x = n \/ ds_garbage r x.
    Proof. reflexivity. Qed.

    Lemma ds_mg_live r n x :
      ds_is_live (ds_mark_garbage n r) x <-> ds_is_live r x /\ x <> n.
    Proof.
      unfold ds_is_live, ds_is_vertex. simpl. unfold set_add. split.
      - intros [Hv Hng]. split; [split|].
        + exact Hv.
        + intro Hg. apply Hng. now right.
        + intro Heq. apply Hng. now left.
      - intros [[Hv Hng] Hneq]. split; [exact Hv|].
        intros [Heq|Hg]; [contradiction|now apply Hng].
    Qed.

    Lemma find_add_add (k : tid) (x y : lin_state) π β :
      TMap.find β (TMap.add k x (TMap.add k y π)) = TMap.find β (TMap.add k x π).
    Proof.
      destruct (Pos.eq_dec β k) as [->|Hneq].
      - now rewrite !TMap.gss.
      - now rewrite !TMap.gso by congruence.
    Qed.

    (** * Histories: pointwise extensionality and stripping the current gap *)

    Definition hist_eq h h' : Prop :=
      (forall x, h_inv h x = h_inv h' x) /\ (forall x, h_pop h x = h_pop h' x).

    Lemma placed_eq h h' x : hist_eq h h' -> (placed h x <-> placed h' x).
    Proof. intros [Hi _]. unfold placed. rewrite Hi. reflexivity. Qed.

    Lemma popped_eq h h' x : hist_eq h h' -> (popped h x <-> popped h' x).
    Proof. intros [_ Hp]. unfold popped. rewrite Hp. reflexivity. Qed.

    Lemma above_eq s h h' x y : hist_eq h h' -> (above s h x y <-> above s h' x y).
    Proof. intros [Hi _]. unfold above. rewrite Hi. reflexivity. Qed.

    Lemma spec_pop_of_eq h h' s β :
      hist_eq h h' -> (spec_pop_of h s β <-> spec_pop_of h' s β).
    Proof. intros [_ Hp]. unfold spec_pop_of. split; intros (n & p & Hn & HM); exists n, p; rewrite Hp in *; auto. Qed.

    Lemma rep_state_eq s h h' r :
      hist_eq h h' -> rep_state s h r -> rep_state s h' r.
    Proof.
      intros Heq Hr. constructor.
      - intros x Hx. apply (rs_vertex_placed s h r Hr). apply (placed_eq h h' x Heq). exact Hx.
      - intros x Hx. apply (rs_vertex_unplaced s h r Hr). rewrite (placed_eq h h' x Heq). exact Hx.
      - intros x y. rewrite (rs_edges s h r Hr). rewrite (placed_eq h h' x Heq), (placed_eq h h' y Heq), (above_eq s h h' x y Heq). reflexivity.
      - intros β l. rewrite (rs_pending s h r Hr). rewrite (placed_eq h h' (pair β l) Heq). reflexivity.
      - intros x. rewrite (rs_garbage s h r Hr). apply popped_eq. exact Heq.
    Qed.

    Lemma rep_tokens_eq s h h' π :
      hist_eq h h' -> rep_tokens s h π -> rep_tokens s h' π.
    Proof.
      intros Heq Hπ. pose proof Heq as [Hi Hp]. constructor.
      - intros β l v Hl Hv Hnp. eapply (rt_push_unplaced s h π Hπ); eauto.
        rewrite (placed_eq h h' (pair β l) Heq). exact Hnp.
      - intros β l v Hl Hv Hpl. eapply (rt_push_placed s h π Hπ); eauto.
        apply (placed_eq h h' (pair β l) Heq). exact Hpl.
      - intros β n p v HS Hn HM Hv. eapply (rt_pop_spec s h π Hπ); eauto. rewrite Hp. exact Hn.
      - intros β HS Hns. eapply (rt_pop_pending s h π Hπ); eauto.
        rewrite (spec_pop_of_eq h h' s β Heq). exact Hns.
    Qed.

    Definition strip h (u : nat) : history :=
      {| h_inv := fun x => match h_inv h x with
                           | Some p => if Nat.eq_dec (gap p) u then None else Some p
                           | None => None
                           end;
         h_pop := fun x => match h_pop h x with
                           | Some (pair p β) => if Nat.eq_dec (gap p) u then None else Some (pair p β)
                           | None => None
                           end |}.

    Lemma strip_inv h u x p :
      h_inv (strip h u) x = Some p <-> h_inv h x = Some p /\ gap p <> u.
    Proof.
      simpl. destruct (h_inv h x) as [q|] eqn:Hq.
      - destruct (Nat.eq_dec (gap q) u) as [He|Hne].
        + split; [discriminate|]. intros [Heq Hneq]. injection Heq as <-. contradiction.
        + split; [intros Heq; injection Heq as <-; auto|].
          intros [Heq _]. exact Heq.
      - split; [discriminate|]. intros [Heq _]. discriminate.
    Qed.

    Lemma strip_pop h u x p β :
      h_pop (strip h u) x = Some (pair p β) <-> h_pop h x = Some (pair p β) /\ gap p <> u.
    Proof.
      simpl. destruct (h_pop h x) as [[q β']|] eqn:Hq.
      - destruct (Nat.eq_dec (gap q) u) as [He|Hne].
        + split; [discriminate|]. intros [Heq Hneq]. injection Heq as <- <-. contradiction.
        + split; [intros Heq; injection Heq as <- <-; auto|].
          intros [Heq _]. exact Heq.
      - split; [discriminate|]. intros [Heq _]. discriminate.
    Qed.

    Lemma strip_inv_none h u x :
      h_inv (strip h u) x = None <->
      h_inv h x = None \/ exists p, h_inv h x = Some p /\ gap p = u.
    Proof.
      simpl. destruct (h_inv h x) as [q|] eqn:Hq.
      - destruct (Nat.eq_dec (gap q) u) as [He|Hne].
        + split; [intros _; right; eauto|reflexivity].
        + split; [discriminate|]. intros [Hc| (p & Hp & Hg) ]; [discriminate|].
          injection Hp as <-. contradiction.
      - split; [intros _; left; reflexivity|reflexivity].
    Qed.

    Lemma strip_pop_none h u x :
      h_pop (strip h u) x = None <->
      h_pop h x = None \/ exists p β, h_pop h x = Some (pair p β) /\ gap p = u.
    Proof.
      simpl. destruct (h_pop h x) as [[q β]|] eqn:Hq.
      - destruct (Nat.eq_dec (gap q) u) as [He|Hne].
        + split; [intros _; right; eauto|reflexivity].
        + split; [discriminate|]. intros [Hc| (p & β' & Hp & Hg) ]; [discriminate|].
          injection Hp as <- <-. contradiction.
      - split; [intros _; left; reflexivity|reflexivity].
    Qed.

    (** Positions of the events of [h] in gap [u], over a vertex list. *)
    Definition ev_inv h (u : nat) x : list Pos :=
      match h_inv h x with
      | Some p => if Nat.eq_dec (gap p) u then p :: nil else nil
      | None => nil
      end.

    Definition ev_pop h (u : nat) x : list Pos :=
      match h_pop h x with
      | Some (pair p _) => if Nat.eq_dec (gap p) u then p :: nil else nil
      | None => nil
      end.

    Definition gap_events h (L : list LPNodeId) (u : nat) : list Pos :=
      flat_map (fun x => ev_inv h u x ++ ev_pop h u x) L.

    Lemma gap_events_in h L u p :
      In p (gap_events h L u) <->
      exists x, In x L /\ gap p = u /\
        (h_inv h x = Some p \/ exists β, h_pop h x = Some (pair p β)).
    Proof.
      unfold gap_events. rewrite in_flat_map. split.
      - intros (x & Hx & Hin). apply in_app_or in Hin. exists x. split; [exact Hx|].
        destruct Hin as [Hin|Hin].
        + unfold ev_inv in Hin. destruct (h_inv h x) as [q|] eqn:Hq; [|contradiction].
          destruct (Nat.eq_dec (gap q) u); [|contradiction].
          destruct Hin as [<-|[]]. auto.
        + unfold ev_pop in Hin. destruct (h_pop h x) as [[q β]|] eqn:Hq; [|contradiction].
          destruct (Nat.eq_dec (gap q) u); [|contradiction].
          destruct Hin as [<-|[]]. eauto.
      - intros (x & Hx & Hg & Hev). exists x. split; [exact Hx|]. apply in_or_app.
        destruct Hev as [Hev|[β Hev]].
        + left. unfold ev_inv. rewrite Hev. destruct (Nat.eq_dec (gap p) u); [now left|contradiction].
        + right. unfold ev_pop. rewrite Hev. destruct (Nat.eq_dec (gap p) u); [now left|contradiction].
    Qed.

    Lemma list_max_pos (ps : list Pos) :
      ps <> nil -> exists pm, In pm ps /\ forall p, In p ps -> ple p pm.
    Proof.
      induction ps as [|q ps IH]; intros Hne; [contradiction|].
      destruct ps as [|q' ps'].
      - exists q. split; [now left|]. intros p [->|[]]. apply ple_refl.
      - destruct IH as [pm [Hin Hmax]]; [discriminate|].
        destruct (plt_dec pm q) as [Hlt|Hnlt].
        + exists q. split; [now left|]. intros p [->|Hin']; [apply ple_refl|].
          left. eapply ple_plt_trans; eauto.
        + exists pm. split; [now right|]. intros p [->|Hin']; [|now apply Hmax].
          apply not_plt_ple. exact Hnlt.
    Qed.

    Lemma flat_map_length_lt {X Y : Type} (f g : X -> list Y) (L : list X) (x0 : X) :
      (forall x, x <> x0 -> length (f x) = length (g x)) ->
      In x0 L -> (length (f x0) < length (g x0))%nat ->
      (length (flat_map f L) < length (flat_map g L))%nat.
    Proof.
      intros Hother Hin Hlt. induction L as [|y L IH]; [contradiction|].
      simpl. rewrite !app_length.
      destruct Hin as [->|Hin].
      - assert (Hle : (length (flat_map f L) <= length (flat_map g L))%nat).
        { clear IH. induction L as [|z L IH']; [simpl; lia|].
          simpl. rewrite !app_length.
          destruct (classic (z = x0)) as [->|Hz].
          - lia.
          - rewrite (Hother z Hz). lia. }
        lia.
      - destruct (classic (y = x0)) as [->|Hy].
        + specialize (IH Hin). lia.
        + rewrite (Hother y Hy). specialize (IH Hin). lia.
    Qed.


    (** * Every speculation step preserves the lag relation *)

    Lemma pending_unique_loc s β l l' :
      TMap.find β (tsa_pending_pushes s) = Some l ->
      TMap.find β (tsa_pending_pushes s) = Some l' -> l = l'.
    Proof. intros H1 H2. rewrite H1 in H2. injection H2 as ->. reflexivity. Qed.

    Lemma lag_vertex s r π x :
      lag s r π -> ds_is_vertex r x -> tsa_is_vertex s x.
    Proof.
      intros Hl Hv. unfold ds_is_vertex in Hv. unfold tsa_is_vertex.
      destruct (ds_vertices r x) as [v|] eqn:Hv'; [|contradiction].
      rewrite (lag_vertices s r π Hl x v Hv'). discriminate.
    Qed.


    Definition pop_result (ls : lin_state) : option (@PopResult A) :=
      match ls with
      | ls_linr f ret =>
          (match f return EDagStack_ar f -> option (@PopResult A) with
           | dag_pop => fun res => Some res
           | dag_push _ => fun _ => None
           end) ret
      | _ => None
      end.

    Lemma pop_succ_token_inj (v v' : A) n x :
      pop_succ_token v n = pop_succ_token v' x -> v = v' /\ n = x.
    Proof.
      intros Heq. pose proof (f_equal pop_result Heq) as Hres.
      unfold pop_succ_token, pop_result in Hres.
      injection Hres as <- Hfst Hsnd. split; [reflexivity|].
      destruct n, x. simpl in *. congruence.
    Qed.

    Lemma pop_succ_token_opt_inj (v v' : A) n x :
      Some (pop_succ_token v n) = Some (pop_succ_token v' x) -> v = v' /\ n = x.
    Proof.
      intros Heq.
      pose proof (f_equal (fun o => match o with Some ls => pop_result ls | None => None end) Heq) as Hres.
      unfold pop_succ_token, pop_result in Hres.
      injection Hres as <- Hfst Hsnd. split; [reflexivity|].
      destruct n, x. simpl in *. congruence.
    Qed.

    Lemma placeS_lag s σ r π ρ' π' :
      payload σ = s -> ghost_wf s -> lag s r π ->
      placeS σ (DSReady r) π ρ' π' ->
      exists r', ρ' = DSReady r' /\ lag s r' π'.
    Proof.
      intros Hpay Hwf Hl Hs. inversion Hs; subst. clear Hs.
      rename H0 into Hβ, H1 into Hv, H2 into Hπ, H3 into HPp, H4 into Hfresh.
      set (x0 := pair β l).
      eexists. split; [reflexivity|].
      assert (Hvs : tsa_is_vertex (payload σ) x0) by (unfold tsa_is_vertex, x0; rewrite Hv; discriminate).
      assert (Hpend : tsa_is_pending (payload σ) x0) by exact Hβ.
      assert (Hnot_completed : tsa_node_ret (payload σ) x0 = None).
      { apply (gw_ret_pending _ Hwf x0 Hvs). exact Hpend. }
      assert (Hno_edge_into : forall y, ~ tsa_edges (payload σ) y x0).
      { intros y He. apply (gw_edge _ Hwf) in He. destruct He as (i & ry & _ & Hry & _). congruence. }
      constructor.
      - intros x v' Hx. destruct (node_eq_dec x x0) as [->|Hneq].
        + rewrite ds_sp_vertex_new in Hx. injection Hx as <-. exact Hv.
        + rewrite ds_sp_vertices in Hx by exact Hneq. eapply lag_vertices; eauto.
      - intros x Hvx Hnv.
        assert (Hneq : x <> x0).
        { intro Heq. subst x. apply Hnv. apply ds_sp_is_vertex. now right. }
        assert (Hnv0 : ~ ds_is_vertex r x).
        { intro Hc. apply Hnv. apply ds_sp_is_vertex. now left. }
        destruct (lag_unplaced _ _ _ Hl x Hvx Hnv0) as [Hp (v' & Hv' & Hπ') ].
        split; [exact Hp|]. exists v'. split; [exact Hv'|].
        destruct (Pos.eq_dec (fst x) β) as [Heq|Hne].
        + exfalso. apply Hneq. destruct x as [βx lx]. simpl in Heq. subst βx.
          unfold tsa_is_pending in Hp. simpl in Hp.
          rewrite (pending_unique_loc _ _ _ _ Hp Hβ). reflexivity.
        + rewrite TMap.gso by exact Hne. exact Hπ'.
      - intros β' l' v' Hβ' Hv' Hvx.
        destruct (Pos.eq_dec β' β) as [->|Hne].
        + rewrite (pending_unique_loc _ _ _ _ Hβ' Hβ) in Hv'.
          rewrite Hv in Hv'. injection Hv' as <-. apply TMap.gss.
        + rewrite TMap.gso by exact Hne. eapply lag_placed_pending; eauto.
          apply ds_sp_is_vertex in Hvx. destruct Hvx as [Hvx|Heq]; [exact Hvx|].
          exfalso. injection Heq as -> _. contradiction.
      - intros β' l'. rewrite ds_sp_pending_find.
        destruct (Pos.eq_dec β' β) as [->|Hne].
        + split.
          * intros Heq. injection Heq as <-. split; [exact Hβ|].
            apply ds_sp_is_vertex. now right.
          * intros [Hβ' _]. rewrite (pending_unique_loc _ _ _ _ Hβ' Hβ). reflexivity.
        + rewrite (lag_pending _ _ _ Hl). rewrite ds_sp_is_vertex. split.
          * intros [H1 H2]. split; [exact H1|now left].
          * intros [H1 [H2|H2]]; [split; assumption|].
            exfalso. injection H2 as -> _. contradiction.
      - intros x y He Hvx Hvy. apply ds_sp_edges.
        apply ds_sp_is_vertex in Hvx. apply ds_sp_is_vertex in Hvy.
        assert (Hyx : y <> x0).
        { intro Heq. subst y. exact (Hno_edge_into x He). }
        destruct Hvy as [Hvy|Hvy]; [|contradiction].
        destruct Hvx as [Hvx| ->].
        + left. eapply lag_edges_in; eauto.
        + right. split; [reflexivity|]. split; [exact Hvy|].
          intros Hpy. apply (lag_pending _ _ _ Hl) in Hpy. destruct Hpy as [Hpy _].
          apply (gw_edge _ Hwf) in He. destruct He as (i & ry & _ & Hry & _).
          assert (Hvys : tsa_is_vertex (payload σ) y) by (eapply lag_vertex; eauto).
          apply (gw_ret_pending _ Hwf y Hvys) in Hpy. congruence.
      - intros x y He. apply ds_sp_edges in He.
        destruct He as [He|[Heqx [Hvy Hnpy] ] ]; [|subst x].
        + destruct (lag_edges_out _ _ _ Hl x y He) as (Hvx & Hvy & Hc).
          split; [apply ds_sp_is_vertex; now left|].
          split; [apply ds_sp_is_vertex; now left|exact Hc].
        + split; [apply ds_sp_is_vertex; now right|].
          split; [apply ds_sp_is_vertex; now left|].
          assert (Hvys : tsa_is_vertex (payload σ) y) by (eapply lag_vertex; eauto).
          assert (Hnps : ~ tsa_is_pending (payload σ) y).
          { intro Hp. apply Hnpy. apply (lag_pending _ _ _ Hl).
            split; [exact Hp|destruct y; exact Hvy]. }
          destruct (classic (tsa_edges (payload σ) x0 y)) as [He|Hne]; [now left|].
          right. split; [exact Hne|]. split; [apply Hno_edge_into|exact Hnps].
      - intros x Hg. apply ds_sp_garbage. eapply lag_garbage_in; eauto.
      - intros x Hg. apply ds_sp_garbage in Hg. apply ds_sp_is_vertex. left.
        eapply lag_garbage_vertex; eauto.
      - intros x Hg Hng. apply ds_sp_garbage in Hg.
        destruct (lag_spec_justified _ _ _ Hl x Hg Hng) as (β' & v' & HS & Hv' & Hπ').
        exists β', v'. split; [exact HS|]. split; [exact Hv'|].
        assert (Hne : β' <> β) by (intro; subst; rewrite Hπ in Hπ'; discriminate).
        rewrite TMap.gso by exact Hne. exact Hπ'.
      - intros β' v' x Hπ'. apply ds_sp_garbage.
        destruct (Pos.eq_dec β' β) as [->|Hne].
        + rewrite TMap.gss in Hπ'. discriminate.
        + rewrite TMap.gso in Hπ' by exact Hne. eapply lag_succ_garbage; eauto.
    Qed.

    Lemma popS_lag s σ r π ρ' π' :
      payload σ = s -> ghost_wf s -> lag s r π ->
      popS σ (DSReady r) π ρ' π' ->
      exists r', ρ' = DSReady r' /\ lag s r' π'.
    Proof.
      intros Hpay Hwf Hl Hs. inversion Hs; subst. clear Hs.
      rename H0 into HS, H1 into Hπ, H2 into Hv, H3 into Hvr, H4 into Htop.
      eexists. split; [reflexivity|].
      assert (Hβ_nopush : forall l, TMap.find β (tsa_pending_pushes (payload σ)) = Some l -> False).
      { intros l Hl'.
        assert (Hvs : tsa_is_vertex (payload σ) (pair β l)) by (eapply gw_pending_vertex; eauto).
        destruct (classic (ds_is_vertex r (pair β l))) as [Hvx|Hnv].
        - unfold tsa_is_vertex in Hvs. destruct (tsa_vertices (payload σ) (pair β l)) as [v'|] eqn:Hv'; [|contradiction].
          pose proof (lag_placed_pending _ _ _ Hl β l v' Hl' Hv' Hvx) as Hc. rewrite Hπ in Hc. discriminate.
        - destruct (lag_unplaced _ _ _ Hl (pair β l) Hvs Hnv) as [_ (v' & _ & Hc') ].
          simpl in Hc'. rewrite Hπ in Hc'. discriminate. }
      constructor.
      - intros x v' Hx. simpl in Hx. eapply lag_vertices; eauto.
      - intros x Hvx Hnv. simpl in Hnv.
        destruct (lag_unplaced _ _ _ Hl x Hvx Hnv) as [Hp (v' & Hv' & Hπ') ].
        split; [exact Hp|]. exists v'. split; [exact Hv'|].
        assert (Hne : fst x <> β).
        { intro Heq. apply (Hβ_nopush (snd x)). unfold tsa_is_pending in Hp. rewrite <- Heq. exact Hp. }
        rewrite find_add_add, TMap.gso by exact Hne. exact Hπ'.
      - intros β' l' v' Hβ' Hv' Hvx. simpl in Hvx.
        assert (Hne : β' <> β) by (intro; subst; exact (Hβ_nopush l' Hβ')).
        rewrite find_add_add, TMap.gso by exact Hne. eapply lag_placed_pending; eauto.
      - intros β' l'. simpl. apply (lag_pending _ _ _ Hl).
      - intros x y He Hvx Hvy. exact (lag_edges_in _ _ _ Hl x y He Hvx Hvy).
      - intros x y He. exact (lag_edges_out _ _ _ Hl x y He).
      - intros x Hg. apply ds_mg_garbage. right. eapply lag_garbage_in; eauto.
      - intros x Hg. apply ds_mg_garbage in Hg. destruct Hg as [->|Hg].
        + unfold ds_is_vertex. simpl. rewrite Hvr. discriminate.
        + exact (lag_garbage_vertex _ _ _ Hl x Hg).
      - intros x Hg Hng. apply ds_mg_garbage in Hg. destruct Hg as [->|Hg].
        + exists β, v. split; [exact HS|]. split; [exact Hv|].
          rewrite find_add_add, TMap.gss. reflexivity.
        + destruct (lag_spec_justified _ _ _ Hl x Hg Hng) as (β' & v' & HS' & Hv' & Hπ').
          exists β', v'. split; [exact HS'|]. split; [exact Hv'|].
          assert (Hne : β' <> β) by (intro; subst; rewrite Hπ in Hπ'; discriminate).
          rewrite find_add_add, TMap.gso by exact Hne. exact Hπ'.
      - intros β' v' x Hπ'. apply ds_mg_garbage.
        destruct (Pos.eq_dec β' β) as [->|Hne].
        + rewrite find_add_add, TMap.gss in Hπ'.
          apply pop_succ_token_opt_inj in Hπ'. destruct Hπ' as [_ ->]. now left.
        + rewrite find_add_add, TMap.gso in Hπ' by exact Hne. right.
          eapply lag_succ_garbage; eauto.
    Qed.

    (** * Plans with events in the current gap are reached by speculation *)

    Definition remove_inv h (x0 : LPNodeId) : history :=
      {| h_inv := fun x => if node_eq_dec x x0 then None else h_inv h x;
         h_pop := h_pop h |}.

    Definition remove_pop h (n0 : LPNodeId) : history :=
      {| h_inv := h_inv h;
         h_pop := fun x => if node_eq_dec x n0 then None else h_pop h x |}.

    Lemma remove_inv_other h x0 x : x <> x0 -> h_inv (remove_inv h x0) x = h_inv h x.
    Proof. intros Hne. simpl. destruct (node_eq_dec x x0); congruence. Qed.

    Lemma remove_inv_self h x0 : h_inv (remove_inv h x0) x0 = None.
    Proof. simpl. destruct (node_eq_dec x0 x0); congruence. Qed.

    Lemma remove_pop_other h n0 x : x <> n0 -> h_pop (remove_pop h n0) x = h_pop h x.
    Proof. intros Hne. simpl. destruct (node_eq_dec x n0); congruence. Qed.

    Lemma remove_pop_self h n0 : h_pop (remove_pop h n0) n0 = None.
    Proof. simpl. destruct (node_eq_dec n0 n0); congruence. Qed.

    Lemma placed_remove_inv h x0 x :
      placed (remove_inv h x0) x <-> placed h x /\ x <> x0.
    Proof.
      unfold placed. simpl. destruct (node_eq_dec x x0) as [->|Hne].
      - split; [intros Hc; exfalso; apply Hc; reflexivity|intros [_ Hc]; contradiction].
      - tauto.
    Qed.

    Lemma popped_remove_pop h n0 x :
      popped (remove_pop h n0) x <-> popped h x /\ x <> n0.
    Proof.
      unfold popped. simpl. destruct (node_eq_dec x n0) as [->|Hne].
      - split; [intros Hc; exfalso; apply Hc; reflexivity|intros [_ Hc]; contradiction].
      - tauto.
    Qed.

    Section Replay.
      Variable s : @TryStackAuxState A.
      Variable σ : concrete_state.
      Hypothesis Hpay : payload σ = s.
      Hypothesis Hwf : ghost_wf s.

      Local Notation t := (tsa_now s).

      (** The events of [h] in the current gap. *)
      Definition cur_event h (p : Pos) : Prop :=
        gap p = t /\
        ((exists x, h_inv h x = Some p) \/ (exists x β, h_pop h x = Some (pair p β))).

      Lemma rs_vertex_iff h r z :
        legal s h -> rep_state s h r -> (ds_is_vertex r z <-> placed h z).
      Proof.
        intros Hl Hr. split.
        - intros Hv. destruct (classic (placed h z)) as [Hp|Hnp]; [exact Hp|].
          exfalso. apply Hv. apply (rs_vertex_unplaced s h r Hr z Hnp).
        - intros Hp. unfold ds_is_vertex. rewrite (rs_vertex_placed s h r Hr z Hp).
          apply (legal_placed_vertex s h z Hwf Hl Hp).
      Qed.

      (** A thread with a pending push and an open session cannot carry the
          tokens [Rep] requires. *)
      Lemma rep_tokens_push_not_session h π β l :
        legal s h -> rep_tokens s h π ->
        TMap.find β (tsa_pending_pushes s) = Some l ->
        session_open s β -> False.
      Proof.
        intros Hl Hπ Hβ HS.
        assert (Hv : tsa_is_vertex s (pair β l)) by (eapply gw_pending_vertex; eauto).
        unfold tsa_is_vertex in Hv.
        destruct (tsa_vertices s (pair β l)) as [v|] eqn:Hv'; [|contradiction].
        assert (Hpush : TMap.find β π = Some (push_inv_token v) \/
                        TMap.find β π = Some (push_lini_token v)).
        { destruct (classic (placed h (pair β l))) as [Hp|Hnp].
          - right. eapply rt_push_placed; eauto.
          - left. eapply rt_push_unplaced; eauto. }
        destruct (classic (spec_pop_of h s β)) as [ (n & p & Hn & HM)|Hns].
        - assert (Hvn : tsa_is_vertex s n).
          { apply (legal_placed_vertex s h n Hwf Hl). apply (legal_popped_placed s h n Hl).
            unfold popped. rewrite Hn. discriminate. }
          unfold tsa_is_vertex in Hvn.
          destruct (tsa_vertices s n) as [vn|] eqn:Hvn'; [|contradiction].
          pose proof (rt_pop_spec _ _ _ Hπ β n p vn HS Hn HM Hvn') as Hf.
          destruct Hpush as [Hp|Hp]; rewrite Hp in Hf; discriminate.
        - pose proof (rt_pop_pending _ _ _ Hπ β HS Hns) as Hf.
          destruct Hpush as [Hp|Hp]; rewrite Hp in Hf; discriminate.
      Qed.

      (** ** Removing the last event of the current gap keeps legality *)

      Lemma last_inv_not_popped h x q :
        legal s h -> h_inv h x = Some q -> gap q = t ->
        (forall p, cur_event h p -> ple p q) -> h_pop h x = None.
      Proof.
        intros Hl Hq Hgap Hmax.
        destruct (h_pop h x) as [[p β']|] eqn:Hp; [|reflexivity]. exfalso.
        destruct (lg_pop s h Hl x p β' Hp) as (Hgp & (q' & Hq' & Hlt) & _).
        rewrite Hq in Hq'. injection Hq' as <-.
        assert (Hcur : cur_event h p).
        { split; [apply plt_gap_le in Hlt; lia|]. right. eauto. }
        specialize (Hmax p Hcur). apply (plt_irrefl q). eapply plt_ple_trans; eauto.
      Qed.

      Lemma last_inv_not_completed h x q :
        legal s h -> h_inv h x = Some q -> gap q = t -> tsa_node_ret s x = None.
      Proof.
        intros Hl Hq Hgap.
        destruct (tsa_node_ret s x) as [ry|] eqn:Hry; [|reflexivity]. exfalso.
        destruct (lg_inv s h Hl x q Hq) as (_ & _ & Hret). specialize (Hret ry Hry).
        destruct (gw_ret s Hwf x ry Hry) as (_ & _ & _ & Hlt). lia.
      Qed.

      Lemma above_remove_inv h x y z :
        above s (remove_inv h x) y z <-> y <> x /\ above s h y z.
      Proof.
        unfold above. simpl. destruct (node_eq_dec y x) as [->|Hne].
        - split; [intros (p & rz & Hc & _); discriminate|intros [Hc _]; contradiction].
        - tauto.
      Qed.

      Lemma remove_inv_legal h x q :
        legal s h -> h_inv h x = Some q -> gap q = t ->
        (forall p, cur_event h p -> ple p q) ->
        legal s (remove_inv h x).
      Proof.
        intros Hl Hq Hgap Hmax.
        pose proof (last_inv_not_popped h x q Hl Hq Hgap Hmax) as Hnpop.
        pose proof (last_inv_not_completed h x q Hl Hq Hgap) as Hnc.
        constructor.
        - intros y p Hy. simpl in Hy. destruct (node_eq_dec y x) as [->|Hne]; [discriminate|].
          exact (lg_inv s h Hl y p Hy).
        - intros y Hc. apply placed_remove_inv. split; [exact (lg_inv_all s h Hl y Hc)|].
          intro; subst y. apply Hc. exact Hnc.
        - intros m p β Hm. simpl in Hm.
          destruct (lg_pop s h Hl m p β Hm) as (Hgp & (q' & Hq' & Hlt) & Hcase).
          split; [exact Hgp|]. split; [|exact Hcase].
          exists q'. split; [|exact Hlt]. rewrite remove_inv_other; [exact Hq'|].
          intro; subst m. congruence.
        - intros m HM. exact (lg_pop_all s h Hl m HM).
        - intros m m' p p' β. simpl. apply (lg_spec s h Hl).
        - intros m p β y qy Hm Hy Hlt Hab. simpl in Hm.
          apply above_remove_inv in Hab. destruct Hab as [Hne Hab].
          rewrite remove_inv_other in Hy by exact Hne.
          exact (lg_top s h Hl m p β y qy Hm Hy Hlt Hab).
        - intros y z p Hy Hz. simpl in Hy, Hz.
          destruct (node_eq_dec y x); [discriminate|].
          destruct (node_eq_dec z x); [discriminate|].
          exact (lg_dist_inv s h Hl y z p Hy Hz).
        - intros y z p β β'. simpl. apply (lg_dist_pop s h Hl).
        - intros y z p β Hy Hz. simpl in Hy, Hz.
          destruct (node_eq_dec y x); [discriminate|].
          exact (lg_dist_mix s h Hl y z p β Hy Hz).
      Qed.

      Lemma last_pop_speculative h n q β :
        legal s h -> h_pop h n = Some (pair q β) -> gap q = t ->
        tsa_removals s n = None.
      Proof.
        intros Hl Hn Hgap.
        destruct (lg_pop s h Hl n q β Hn) as (_ & _ & [ (st & rt & HM & _ & Hle)| (HM & _) ]); [|exact HM].
        exfalso. destruct (gw_removal s Hwf n β st rt HM) as (_ & Hlt & _). lia.
      Qed.

      Lemma remove_pop_legal h n q β :
        legal s h -> h_pop h n = Some (pair q β) -> gap q = t ->
        (forall p, cur_event h p -> ple p q) ->
        legal s (remove_pop h n).
      Proof.
        intros Hl Hn Hgap Hmax.
        pose proof (last_pop_speculative h n q β Hl Hn Hgap) as HMn.
        constructor.
        - intros y p Hy. exact (lg_inv s h Hl y p Hy).
        - intros y Hc. exact (lg_inv_all s h Hl y Hc).
        - intros m p β' Hm. simpl in Hm. destruct (node_eq_dec m n); [discriminate|].
          exact (lg_pop s h Hl m p β' Hm).
        - intros m HM. apply popped_remove_pop. split; [exact (lg_pop_all s h Hl m HM)|].
          intro; subst m. contradiction.
        - intros m m' p p' β' Hm Hm'. simpl in Hm, Hm'.
          destruct (node_eq_dec m n); [discriminate|].
          destruct (node_eq_dec m' n); [discriminate|].
          exact (lg_spec s h Hl m m' p p' β' Hm Hm').
        - intros m p β' y qy Hm Hy Hlt Hab. simpl in Hm.
          destruct (node_eq_dec m n) as [|Hne]; [discriminate|].
          destruct (lg_top s h Hl m p β' y qy Hm Hy Hlt Hab) as (p' & β'' & Hp' & Hp'p).
          assert (Hyn : y <> n).
          { intro; subst y. rewrite Hn in Hp'. injection Hp' as <- <-.
            destruct (lg_pop s h Hl m p β' Hm) as (Hgp & _).
            destruct (Nat.eq_dec (gap p) t) as [Heq|Hneq].
            - assert (Hcur : cur_event h p) by (split; [exact Heq|right; eauto]).
              specialize (Hmax p Hcur). apply (plt_irrefl p). eapply ple_plt_trans; eauto.
            - apply plt_gap_le in Hp'p. lia. }
          exists p', β''. split; [|exact Hp'p]. rewrite remove_pop_other by exact Hyn. exact Hp'.
        - intros y z p. simpl. apply (lg_dist_inv s h Hl).
        - intros y z p β' β'' Hy Hz. simpl in Hy, Hz.
          destruct (node_eq_dec y n); [discriminate|].
          destruct (node_eq_dec z n); [discriminate|].
          exact (lg_dist_pop s h Hl y z p β' β'' Hy Hz).
        - intros y z p β' Hy Hz. simpl in Hz. destruct (node_eq_dec z n); [discriminate|].
          exact (lg_dist_mix s h Hl y z p β' Hy Hz).
      Qed.

      (** Replaying the last event of the current gap: a push-inv. *)
      Lemma replay_place h x q r π :
        legal s h ->
        h_inv h x = Some q -> gap q = t ->
        (forall p, cur_event h p -> ple p q) ->
        rep_state s (remove_inv h x) r ->
        rep_tokens s (remove_inv h x) π ->
        exists r' π', placeS σ (DSReady r) π (DSReady r') π' /\
          rep_state s h r' /\ rep_tokens s h π'.
      Proof.
        intros Hl Hq Hgap Hmax Hr Hπ.
        assert (Hl_e : legal s (remove_inv h x)) by (eapply remove_inv_legal; eauto).
        destruct x as [β l]. set (x := pair β l) in *.
        assert (Hplx : placed h x) by (unfold placed; rewrite Hq; discriminate).
        pose proof (legal_placed_vertex s h x Hwf Hl Hplx) as Hvx.
        unfold tsa_is_vertex in Hvx.
        destruct (tsa_vertices s x) as [v|] eqn:Hv; [|contradiction]. clear Hvx.
        assert (Hvx : tsa_is_vertex s x) by (unfold tsa_is_vertex; rewrite Hv; discriminate).
        assert (Hnc : tsa_node_ret s x = None).
        { destruct (tsa_node_ret s x) as [ry|] eqn:Hry; [|reflexivity].
          exfalso. destruct (lg_inv s h Hl x q Hq) as (_ & _ & Hret).
          specialize (Hret ry Hry). destruct (gw_ret s Hwf x ry Hry) as (_ & _ & _ & Hlt). lia. }
        assert (Hpend : tsa_is_pending s x) by (apply (gw_ret_pending s Hwf x Hvx); exact Hnc).
        assert (Hβ : TMap.find β (tsa_pending_pushes s) = Some l) by exact Hpend.
        assert (Hnpop : h_pop h x = None).
        { destruct (h_pop h x) as [[p β']|] eqn:Hp; [|reflexivity]. exfalso.
          destruct (lg_pop s h Hl x p β' Hp) as (Hgp & (q' & Hq' & Hlt) & _).
          rewrite Hq in Hq'. injection Hq' as <-.
          assert (Hcur : cur_event h p).
          { split; [apply plt_gap_le in Hlt; lia|]. right. eauto. }
          specialize (Hmax p Hcur). apply (plt_irrefl q). eapply plt_ple_trans; eauto. }
        assert (Hnpl : ~ placed (remove_inv h x) x).
        { unfold placed. rewrite remove_inv_self. intro Hc. apply Hc. reflexivity. }
        assert (Htok : TMap.find β π = Some (push_inv_token v)).
        { eapply rt_push_unplaced; eauto. }
        assert (HPp : TMap.find β (ds_pending_pushes r) = None).
        { destruct (TMap.find β (ds_pending_pushes r)) as [l'|] eqn:Hl'; [|reflexivity].
          exfalso. apply (rs_pending _ _ _ Hr) in Hl'. destruct Hl' as [Hl' Hpl].
          rewrite (pending_unique_loc _ _ _ _ Hl' Hβ) in Hpl. exact (Hnpl Hpl). }
        assert (Hfresh : ds_fresh_node r x).
        { split.
          - apply (rs_vertex_unplaced _ _ _ Hr). exact Hnpl.
          - intro Hg. apply (rs_garbage _ _ _ Hr) in Hg. exact (Hg Hnpop). }
        assert (Hvert_iff : forall z, ds_is_vertex r z <-> placed h z /\ z <> x).
        { intros z. rewrite <- placed_remove_inv. split.
          - intros Hvz. destruct (classic (placed (remove_inv h x) z)) as [Hp|Hnp]; [exact Hp|].
            exfalso. apply Hvz. apply (rs_vertex_unplaced _ _ _ Hr z Hnp).
          - intros Hp. unfold ds_is_vertex. rewrite (rs_vertex_placed _ _ _ Hr z Hp).
            apply placed_remove_inv in Hp. exact (legal_placed_vertex s h z Hwf Hl (proj1 Hp)). }
        assert (Habove_e : forall y z, above s (remove_inv h x) y z <-> y <> x /\ above s h y z).
        { intros y z. unfold above. simpl. destruct (node_eq_dec y x) as [->|Hne].
          - split; [intros (p & rz & Hc & _); discriminate|intros [Hc _]; contradiction].
          - tauto. }
        assert (Habove_x_gen : forall y z, above s h y z -> z <> x).
        { intros y z (p & rz & _ & Hrz & _) ->. congruence. }
        assert (Habove_x : forall z, above s h x z -> z <> x) by (intros z; apply Habove_x_gen).
        assert (Hcompleted_iff : forall z, placed h z -> z <> x ->
          (~ ds_is_pending r z <-> exists rz, tsa_node_ret s z = Some rz)).
        { intros z Hpz Hnez.
          pose proof (legal_placed_vertex s h z Hwf Hl Hpz) as Hvz.
          unfold ds_is_pending. destruct z as [βz lz]. simpl.
          rewrite (rs_pending _ _ _ Hr), placed_remove_inv.
          pose proof (gw_ret_pending s Hwf (pair βz lz) Hvz) as Hrp. unfold tsa_is_pending in Hrp. simpl in Hrp.
          split.
          - intros Hnp. destruct (tsa_node_ret s (pair βz lz)) as [rz|] eqn:Hrz; [eauto|].
            exfalso. apply Hnp. split; [apply Hrp; reflexivity|]. split; assumption.
          - intros (rz & Hrz) [Hp _]. apply Hrp in Hp. congruence. }
        exists (ds_start_push β l v r), (TMap.add β (push_lini_token v) π).
        split.
        { constructor; rewrite ?Hpay; assumption. }
        split.
        - constructor.
          + intros y Hy. destruct (node_eq_dec y x) as [->|Hne].
            * rewrite ds_sp_vertex_new. symmetry. exact Hv.
            * rewrite ds_sp_vertices by exact Hne. apply (rs_vertex_placed _ _ _ Hr).
              apply placed_remove_inv. auto.
          + intros y Hy. assert (Hne : y <> x) by (intro; subst; contradiction).
            rewrite ds_sp_vertices by exact Hne. apply (rs_vertex_unplaced _ _ _ Hr).
            rewrite placed_remove_inv. tauto.
          + intros y z. rewrite ds_sp_edges, (rs_edges _ _ _ Hr).
            rewrite !placed_remove_inv, Habove_e.
            destruct (node_eq_dec y x) as [->|Hne].
            * split.
              -- intros [ [ [_ Hc] _ ] | [_ [Hvz Hnp] ] ]; [contradiction|].
                 apply Hvert_iff in Hvz. destruct Hvz as [Hpz Hnez].
                 apply (Hcompleted_iff z Hpz Hnez) in Hnp. destruct Hnp as [rz Hrz].
                 split; [exact Hplx|]. split; [exact Hpz|].
                 exists q, rz. split; [exact Hq|]. split; [exact Hrz|].
                 destruct (gw_ret s Hwf z rz Hrz) as (_ & _ & _ & Hlt). lia.
              -- intros (_ & Hpz & Hab). pose proof (Habove_x z Hab) as Hnez.
                 right. split; [reflexivity|]. split; [apply Hvert_iff; auto|].
                 apply (Hcompleted_iff z Hpz Hnez).
                 destruct Hab as (p & rz & _ & Hrz & _). eauto.
            * split.
              -- intros [ [ [Hpy _] [ [Hpz _] [_ Hab] ] ] | [Hc _] ]; [|contradiction].
                 auto.
              -- intros (Hpy & Hpz & Hab). left.
                 split; [split; assumption|]. split; [split; [exact Hpz|exact (Habove_x_gen y z Hab) ]|].
                 split; assumption.
          + intros β' l'. rewrite ds_sp_pending_find.
            destruct (Pos.eq_dec β' β) as [->|Hne].
            * split.
              -- intros Heq. injection Heq as <-. split; [exact Hβ|exact Hplx].
              -- intros [Hβ' _]. rewrite (pending_unique_loc _ _ _ _ Hβ' Hβ). reflexivity.
            * rewrite (rs_pending _ _ _ Hr), placed_remove_inv.
              assert (Hnex : pair β' l' <> x) by (intro Heq; injection Heq as -> _; contradiction).
              tauto.
          + intros y. simpl. apply (rs_garbage _ _ _ Hr).
        - constructor.
          + intros β' l' v' Hβ' Hv' Hnp.
            assert (Hne : β' <> β).
            { intro; subst β'. rewrite (pending_unique_loc _ _ _ _ Hβ' Hβ) in Hnp. contradiction. }
            rewrite TMap.gso by exact Hne. eapply (rt_push_unplaced _ _ _ Hπ); eauto.
            rewrite placed_remove_inv. tauto.
          + intros β' l' v' Hβ' Hv' Hpl.
            destruct (Pos.eq_dec β' β) as [->|Hne].
            * rewrite (pending_unique_loc _ _ _ _ Hβ' Hβ) in Hv'.
              pose proof (eq_trans (eq_sym Hv) Hv') as Hvv. injection Hvv as <-. apply TMap.gss.
            * rewrite TMap.gso by exact Hne. eapply (rt_push_placed _ _ _ Hπ); eauto.
              apply placed_remove_inv. split; [exact Hpl|].
              intro Heq. injection Heq as -> _. contradiction.
          + intros β' n p v' HS Hn HM Hv'.
            assert (Hne : β' <> β).
            { intro; subst β'. exact (rep_tokens_push_not_session _ _ _ _ Hl_e Hπ Hβ HS). }
            rewrite TMap.gso by exact Hne. eapply (rt_pop_spec _ _ _ Hπ); eauto.
          + intros β' HS Hns.
            assert (Hne : β' <> β).
            { intro; subst β'. exact (rep_tokens_push_not_session _ _ _ _ Hl_e Hπ Hβ HS). }
            rewrite TMap.gso by exact Hne. eapply (rt_pop_pending _ _ _ Hπ); eauto.
      Qed.

      (** Replaying the last event of the current gap: a speculative pop. *)
      Lemma replay_pop h n q β r π :
        legal s h ->
        h_pop h n = Some (pair q β) -> gap q = t ->
        (forall p, cur_event h p -> ple p q) ->
        rep_state s (remove_pop h n) r ->
        rep_tokens s (remove_pop h n) π ->
        exists r' π', popS σ (DSReady r) π (DSReady r') π' /\
          rep_state s h r' /\ rep_tokens s h π'.
      Proof.
        intros Hl Hn Hgap Hmax Hr Hπ.
        assert (Hl_e : legal s (remove_pop h n)) by (eapply remove_pop_legal; eauto).
        destruct (lg_pop s h Hl n q β Hn) as (Hgq & (q0 & Hq0 & Hq0q) & Hcase).
        destruct Hcase as [ (st & rt & HM & _ & Hle)| (HM & σs & Hσs & _) ].
        { exfalso. destruct (gw_removal s Hwf n β st rt HM) as (_ & Hlt & _). lia. }
        assert (Hpln : placed h n) by (unfold placed; rewrite Hq0; discriminate).
        pose proof (legal_placed_vertex s h n Hwf Hl Hpln) as Hvn.
        unfold tsa_is_vertex in Hvn.
        destruct (tsa_vertices s n) as [v|] eqn:Hv; [|contradiction]. clear Hvn.
        assert (HSne : session_open s β).
        { destruct (gw_session_time s Hwf β σs Hσs) as (N0 & HN0). unfold session_open. congruence. }
        assert (Hnospec : ~ spec_pop_of (remove_pop h n) s β).
        { intros (n' & p' & Hn' & HM').
          destruct (node_eq_dec n' n) as [->|Hne].
          - rewrite remove_pop_self in Hn'. discriminate.
          - rewrite remove_pop_other in Hn' by exact Hne.
            apply Hne. eapply (lg_spec s h Hl n' n p' q β); eauto. }
        assert (Htok : TMap.find β π = Some pop_inv_token).
        { eapply (rt_pop_pending _ _ _ Hπ); eauto. }
        assert (Hplaced_e : forall z, placed (remove_pop h n) z <-> placed h z) by (intros z; reflexivity).
        assert (Hvr : ds_vertices r n = Some v).
        { rewrite (rs_vertex_placed _ _ _ Hr n Hpln). exact Hv. }
        assert (Htop : lp_top (ds_is_live r) (ds_edges r) n).
        { split.
          - split; [unfold ds_is_vertex; congruence|].
            intro Hg. apply (rs_garbage _ _ _ Hr) in Hg. apply popped_remove_pop in Hg.
            destruct Hg as [_ Hc]. apply Hc. reflexivity.
          - intros y [Hvy Hngy] He. apply (rs_edges _ _ _ Hr) in He.
            destruct He as (Hpy & _ & Hab). simpl in Hab.
            unfold placed in Hpy. destruct (h_inv h y) as [qy|] eqn:Hqy; [|contradiction].
            assert (Hlt : plt qy q).
            { destruct (plt_trichotomy qy q) as [Hlt|[Heq|Hgt]]; [exact Hlt| |].
              - subst qy. exfalso. exact (lg_dist_mix s h Hl y n q β Hqy Hn).
              - exfalso. assert (Hcur : cur_event h qy).
                { split; [|left; eauto].
                  destruct (lg_inv s h Hl y qy Hqy) as (Hle' & _).
                  apply plt_gap_le in Hgt. lia. }
                specialize (Hmax qy Hcur). apply (plt_irrefl q). eapply plt_ple_trans; eauto. }
            destruct (lg_top s h Hl n q β y qy Hn Hqy Hlt Hab) as (p' & β' & Hp' & Hp'q).
            assert (Hne : y <> n).
            { intro; subst y. rewrite Hn in Hp'. injection Hp' as <- _. exact (plt_irrefl q Hp'q). }
            apply Hngy. apply (rs_garbage _ _ _ Hr). apply popped_remove_pop.
            split; [unfold popped; congruence|exact Hne]. }
        exists (ds_mark_garbage n r),
          (TMap.add β (pop_succ_token v n) (TMap.add β pop_lini_token π)).
        split.
        { apply (pop_step σ r π β n v); rewrite ?Hpay; assumption. }
        split.
        - constructor.
          + intros y Hy. simpl. apply (rs_vertex_placed _ _ _ Hr). exact Hy.
          + intros y Hy. simpl. apply (rs_vertex_unplaced _ _ _ Hr). exact Hy.
          + intros y z. simpl. rewrite (rs_edges _ _ _ Hr). reflexivity.
          + intros β' l'. simpl. apply (rs_pending _ _ _ Hr).
          + intros y. rewrite ds_mg_garbage, (rs_garbage _ _ _ Hr), popped_remove_pop.
            split.
            * intros [->|[Hp _]]; [unfold popped; congruence|exact Hp].
            * intros Hp. destruct (node_eq_dec y n) as [->|Hne]; [now left|right; auto].
        - assert (Hβ_nopush : forall l, TMap.find β (tsa_pending_pushes s) = Some l -> False).
          { intros l Hl'. exact (rep_tokens_push_not_session _ _ _ _ Hl_e Hπ Hl' HSne). }
          constructor.
          + intros β' l' v' Hβ' Hv' Hnp.
            assert (Hne : β' <> β) by (intro; subst; eapply Hβ_nopush; eauto).
            rewrite find_add_add, TMap.gso by exact Hne. eapply (rt_push_unplaced _ _ _ Hπ); eauto.
          + intros β' l' v' Hβ' Hv' Hpl.
            assert (Hne : β' <> β) by (intro; subst; eapply Hβ_nopush; eauto).
            rewrite find_add_add, TMap.gso by exact Hne. eapply (rt_push_placed _ _ _ Hπ); eauto.
          + intros β' n' p' v' HS' Hn' HM' Hv'.
            destruct (Pos.eq_dec β' β) as [->|Hne].
            * assert (Heq : n' = n) by (eapply (lg_spec s h Hl n' n p' q β); eauto).
              subst n'. rewrite Hv in Hv'. injection Hv' as <-.
              rewrite find_add_add, TMap.gss. reflexivity.
            * rewrite find_add_add, TMap.gso by exact Hne.
              assert (Hnen : n' <> n) by (intro; subst n'; rewrite Hn in Hn'; injection Hn' as _ ->; contradiction).
              eapply (rt_pop_spec _ _ _ Hπ); eauto. rewrite remove_pop_other by exact Hnen. exact Hn'.
          + intros β' HS' Hns.
            assert (Hne : β' <> β).
            { intro; subst β'. apply Hns. exists n, q. auto. }
            rewrite find_add_add, TMap.gso by exact Hne. eapply (rt_pop_pending _ _ _ Hπ); eauto.
            intros (n' & p' & Hn' & HM'). apply Hns. exists n', p'. split; [|exact HM'].
            destruct (node_eq_dec n' n) as [->|Hnen].
            * rewrite remove_pop_self in Hn'. discriminate.
            * rewrite remove_pop_other in Hn' by exact Hnen. exact Hn'.
      Qed.

      (** ** Stripping the current gap *)

      Lemma hist_eq_sym h h' : hist_eq h h' -> hist_eq h' h.
      Proof. intros [Hi Hp]. split; intros x; symmetry; auto. Qed.

      Lemma strip_remove_inv h x q :
        h_inv h x = Some q -> gap q = t ->
        hist_eq (strip (remove_inv h x) t) (strip h t).
      Proof.
        intros Hq Hgap. split; intros y.
        - simpl. destruct (node_eq_dec y x) as [->|Hne].
          + rewrite Hq. destruct (Nat.eq_dec (gap q) t); [reflexivity|contradiction].
          + reflexivity.
        - reflexivity.
      Qed.

      Lemma strip_remove_pop h n q β :
        h_pop h n = Some (pair q β) -> gap q = t ->
        hist_eq (strip (remove_pop h n) t) (strip h t).
      Proof.
        intros Hq Hgap. split; intros y.
        - reflexivity.
        - simpl. destruct (node_eq_dec y n) as [->|Hne].
          + rewrite Hq. destruct (Nat.eq_dec (gap q) t); [reflexivity|contradiction].
          + reflexivity.
      Qed.

      Lemma strip_no_cur h :
        (forall p, ~ cur_event h p) -> hist_eq (strip h t) h.
      Proof.
        intros Hno. split; intros x; simpl.
        - destruct (h_inv h x) as [p|] eqn:Hp; [|reflexivity].
          destruct (Nat.eq_dec (gap p) t) as [Heq|]; [|reflexivity].
          exfalso. apply (Hno p). split; [exact Heq|left; eauto].
        - destruct (h_pop h x) as [[p β]|] eqn:Hp; [|reflexivity].
          destruct (Nat.eq_dec (gap p) t) as [Heq|]; [|reflexivity].
          exfalso. apply (Hno p). split; [exact Heq|right; eauto].
      Qed.

      Lemma cur_event_in_gap_events h L p :
        (forall x, In x L <-> tsa_is_vertex s x) -> legal s h ->
        cur_event h p -> In p (gap_events h L t).
      Proof.
        intros HL Hl [Hgap Hev]. apply gap_events_in.
        destruct Hev as [[x Hx]|[x [β Hx]]]; exists x; (split; [apply HL| split; [exact Hgap|eauto]]).
        - apply (legal_placed_vertex s h x Hwf Hl). unfold placed. rewrite Hx. discriminate.
        - apply (legal_placed_vertex s h x Hwf Hl). apply (legal_popped_placed s h x Hl).
          unfold popped. rewrite Hx. discriminate.
      Qed.

      Lemma gap_events_remove_inv_lt h L x q :
        In x L -> h_inv h x = Some q -> gap q = t ->
        (length (gap_events (remove_inv h x) L t) < length (gap_events h L t))%nat.
      Proof.
        intros Hin Hq Hgap. unfold gap_events. apply (flat_map_length_lt _ _ L x).
        - intros y Hne. unfold ev_inv, ev_pop. simpl.
          destruct (node_eq_dec y x); [contradiction|reflexivity].
        - exact Hin.
        - unfold ev_inv, ev_pop. simpl. destruct (node_eq_dec x x); [|contradiction].
          rewrite Hq. destruct (Nat.eq_dec (gap q) t); [|contradiction]. simpl. lia.
      Qed.

      Lemma gap_events_remove_pop_lt h L n q β :
        In n L -> h_pop h n = Some (pair q β) -> gap q = t ->
        (length (gap_events (remove_pop h n) L t) < length (gap_events h L t))%nat.
      Proof.
        intros Hin Hq Hgap. unfold gap_events. apply (flat_map_length_lt _ _ L n).
        - intros y Hne. unfold ev_inv, ev_pop. simpl.
          destruct (node_eq_dec y n); [contradiction|reflexivity].
        - exact Hin.
        - unfold ev_inv, ev_pop. simpl. destruct (node_eq_dec n n); [|contradiction].
          rewrite Hq. destruct (Nat.eq_dec (gap q) t); [|contradiction].
          rewrite !app_length. simpl. lia.
      Qed.

      (** ** The replay, by induction on the number of current-gap events *)

      Lemma replay_induction (L : list LPNodeId) :
        (forall x, In x L <-> tsa_is_vertex s x) ->
        forall k h, length (gap_events h L t) = k -> legal s h ->
        forall r π, rep_state s (strip h t) r ->
          rep_tokens s (strip h t) π ->
          exists r' π', specS σ (DSReady r) π (DSReady r') π' /\
            rep_state s h r' /\ rep_tokens s h π'.
      Proof.
        intros HL k. induction k as [k IH] using (well_founded_induction lt_wf).
        intros h Hk Hl r π Hr Hπ.
        destruct (gap_events h L t) as [|p0 ps] eqn:Hev.
        - (* no event in the current gap *)
          assert (Hno : forall p, ~ cur_event h p).
          { intros p Hc. pose proof (cur_event_in_gap_events h L p HL Hl Hc) as Hin.
            rewrite Hev in Hin. exact Hin. }
          pose proof (strip_no_cur h Hno) as Heq.
          exists r, π. split; [constructor|]. split.
          + eapply rep_state_eq; eauto.
          + eapply rep_tokens_eq; [exact Heq|exact Hπ].
        - destruct (list_max_pos (p0 :: ps)) as (pm & Hin & Hmaxl); [discriminate|].
          rewrite <- Hev in Hin. apply gap_events_in in Hin.
          destruct Hin as (x & HxL & Hgap & Hevx).
          assert (Hmax : forall p, cur_event h p -> ple p pm).
          { intros p Hc. apply Hmaxl. rewrite <- Hev.
            apply cur_event_in_gap_events; assumption. }
          destruct Hevx as [Hx|[β Hx]].
          + (* the last event is a push-inv *)
            pose proof (remove_inv_legal h x pm Hl Hx Hgap Hmax) as Hl'.
            pose proof (gap_events_remove_inv_lt h L x pm HxL Hx Hgap) as Hlt.
            assert (Hlt' : (length (gap_events (remove_inv h x) L t) < k)%nat).
            { rewrite <- Hk, <- Hev. exact Hlt. }
            pose proof (strip_remove_inv h x pm Hx Hgap) as Heq.
            destruct (IH _ Hlt' (remove_inv h x) eq_refl Hl' r π)
              as (r1 & π1 & Hspec & Hr1 & Hπ1).
            { eapply rep_state_eq; [apply hist_eq_sym; exact Heq|exact Hr]. }
            { eapply rep_tokens_eq; [apply hist_eq_sym; exact Heq|exact Hπ]. }
            destruct (replay_place h x pm r1 π1 Hl Hx Hgap Hmax Hr1 Hπ1)
              as (r' & π' & Hstep & Hr' & Hπ').
            exists r', π'. split; [|split; assumption].
            eapply specS_snoc; [exact Hspec|]. left. exact Hstep.
          + (* the last event is a speculative pop *)
            pose proof (remove_pop_legal h x pm β Hl Hx Hgap Hmax) as Hl'.
            pose proof (gap_events_remove_pop_lt h L x pm β HxL Hx Hgap) as Hlt.
            assert (Hlt' : (length (gap_events (remove_pop h x) L t) < k)%nat).
            { rewrite <- Hk, <- Hev. exact Hlt. }
            pose proof (strip_remove_pop h x pm β Hx Hgap) as Heq.
            destruct (IH _ Hlt' (remove_pop h x) eq_refl Hl' r π)
              as (r1 & π1 & Hspec & Hr1 & Hπ1).
            { eapply rep_state_eq; [apply hist_eq_sym; exact Heq|exact Hr]. }
            { eapply rep_tokens_eq; [apply hist_eq_sym; exact Heq|exact Hπ]. }
            destruct (replay_pop h x pm β r1 π1 Hl Hx Hgap Hmax Hr1 Hπ1)
              as (r' & π' & Hstep & Hr' & Hπ').
            exists r', π'. split; [|split; assumption].
            eapply specS_snoc; [exact Hspec|]. right. exact Hstep.
      Qed.

      (** ** Stripping a plan gives a plan without speculation *)

      Lemma strip_plan H h : plan s H h -> plan s H (strip h t).
      Proof.
        intros Hpl. pose proof (pl_legal _ _ _ Hpl) as Hl.
        assert (Hlegal : legal s (strip h t)).
        { constructor.
          - intros x p Hx. apply strip_inv in Hx. destruct Hx as [Hx _]. exact (lg_inv s h Hl x p Hx).
          - intros x Hc. pose proof (lg_inv_all s h Hl x Hc) as Hp. unfold placed in *.
            destruct (h_inv h x) as [p|] eqn:Hx; [|contradiction].
            destruct (lg_inv s h Hl x p Hx) as (_ & _ & Hret).
            unfold completed in Hc. destruct (tsa_node_ret s x) as [rx|] eqn:Hrx; [|contradiction].
            specialize (Hret rx eq_refl). destruct (gw_ret s Hwf x rx Hrx) as (_ & _ & _ & Hlt).
            intro Hnone. apply strip_inv_none in Hnone.
            destruct Hnone as [Hc'| (p' & Hp' & Hg) ]; [congruence|].
            rewrite Hx in Hp'. injection Hp' as <-. lia.
          - intros n p β Hn. apply strip_pop in Hn. destruct Hn as [Hn Hne].
            destruct (lg_pop s h Hl n p β Hn) as (Hgp & (q & Hq & Hlt) & Hcase).
            split; [exact Hgp|]. split; [|exact Hcase].
            exists q. split; [|exact Hlt]. apply strip_inv. split; [exact Hq|].
            apply plt_gap_le in Hlt. lia.
          - intros n HM. pose proof (lg_pop_all s h Hl n HM) as Hp. unfold popped in *.
            destruct (h_pop h n) as [[p β]|] eqn:Hn; [|contradiction].
            destruct (lg_pop s h Hl n p β Hn) as (_ & _ & [ (st & rt & HM' & _ & Hle)| (HM' & _) ]); [|contradiction].
            destruct (gw_removal s Hwf n β st rt HM') as (_ & Hlt & _).
            intro Hnone. apply strip_pop_none in Hnone.
            destruct Hnone as [Hc| (p' & β' & Hp' & Hg) ]; [congruence|].
            rewrite Hn in Hp'. injection Hp' as <- <-. lia.
          - intros n m p q β Hn Hm HMn HMm. apply strip_pop in Hn. apply strip_pop in Hm.
            exact (lg_spec s h Hl n m p q β (proj1 Hn) (proj1 Hm) HMn HMm).
          - intros n p β x q Hn Hx Hlt Hab. apply strip_pop in Hn. destruct Hn as [Hn Hne].
            apply strip_inv in Hx. destruct Hx as [Hx _].
            assert (Hab' : above s h x n).
            { destruct Hab as (p' & rn & Hp' & Hrn & Hlt'). apply strip_inv in Hp'.
              exists p', rn. split; [exact (proj1 Hp')|auto]. }
            destruct (lg_top s h Hl n p β x q Hn Hx Hlt Hab') as (p' & β' & Hp' & Hp'p).
            exists p', β'. split; [|exact Hp'p]. apply strip_pop. split; [exact Hp'|].
            destruct (lg_pop s h Hl n p β Hn) as (Hgp & _).
            apply plt_gap_le in Hp'p. lia.
          - intros x y p Hx Hy. apply strip_inv in Hx. apply strip_inv in Hy.
            exact (lg_dist_inv s h Hl x y p (proj1 Hx) (proj1 Hy)).
          - intros x y p β β' Hx Hy. apply strip_pop in Hx. apply strip_pop in Hy.
            exact (lg_dist_pop s h Hl x y p β β' (proj1 Hx) (proj1 Hy)).
          - intros x y p β Hx Hy. apply strip_inv in Hx. apply strip_pop in Hy.
            exact (lg_dist_mix s h Hl x y p β (proj1 Hx) (proj1 Hy)). }
        constructor.
        - exact Hlegal.
        - intros m HM. rewrite <- (pl_committed _ _ _ Hpl m HM).
          pose proof (lg_pop_all s h Hl m HM) as Hp. unfold popped in Hp.
          destruct (h_pop h m) as [[p β]|] eqn:Hm; [|contradiction].
          apply strip_pop. split; [exact Hm|].
          destruct (lg_pop s h Hl m p β Hm) as (_ & _ & [ (st & rt & HM' & _ & Hle)| (HM' & _) ]); [|contradiction].
          destruct (gw_removal s Hwf m β st rt HM') as (_ & Hlt & _). lia.
        - intros x p Hx. apply strip_inv in Hx. exact (pl_later _ _ _ Hpl x p (proj1 Hx)).
      Qed.

      (** The paper's "plans with events in the current gap are reached by
          speculation". *)
      Theorem plans_reached H h :
        plan s H h ->
        forall r π, rep_state s (strip h t) r ->
          rep_tokens s (strip h t) π ->
          exists r' π', specS σ (DSReady r) π (DSReady r') π' /\
            rep_state s h r' /\ rep_tokens s h π'.
      Proof.
        intros Hpl r π Hr Hπ. destruct (gw_finite s Hwf) as [L HL].
        exact (replay_induction L HL _ h eq_refl (pl_legal _ _ _ Hpl) r π Hr Hπ).
      Qed.

    End Replay.

    (** * Speculation preserves [I_lag] *)

    Lemma spec_step_lag s σ r π ρ' π' :
      payload σ = s -> ghost_wf s -> lag s r π ->
      spec_step σ (DSReady r) π ρ' π' ->
      exists r', ρ' = DSReady r' /\ lag s r' π'.
    Proof.
      intros Hpay Hwf Hl [Hs|Hs].
      - eapply placeS_lag; eauto.
      - eapply popS_lag; eauto.
    Qed.

    Lemma specS_lag s σ ρ π ρ' π' :
      payload σ = s -> ghost_wf s ->
      (exists r, ρ = DSReady r /\ lag s r π) ->
      specS σ ρ π ρ' π' ->
      exists r', ρ' = DSReady r' /\ lag s r' π'.
    Proof.
      intros Hpay Hwf Hl Hc. induction Hc as [ρ π|ρ π ρ1 π1 ρ2 π2 Hstep Hc IH]; [exact Hl|].
      apply IH. destruct Hl as (r & -> & Hl). eapply spec_step_lag; eauto.
    Qed.

    (** [I_lag] is preserved by the exact speculation image. *)
    Lemma I_lag_specS s σ (Δ Δ' : config) :
      payload σ = s -> ghost_wf s -> I_lag s Δ ->
      (forall ρ' π', Δ' ρ' π' <-> exists ρ π, Δ ρ π /\ specS σ ρ π ρ' π') ->
      I_lag s Δ'.
    Proof.
      intros Hpay Hwf Hlag HΔ' ρ' π' Hposs'. apply HΔ' in Hposs'.
      destruct Hposs' as (ρ & π & Hposs & Hspec).
      eapply specS_lag; eauto.
    Qed.


    (** * Generic transport facts *)

    Definition extend_inv H (x : LPNodeId) (p : Pos) : history :=
      {| h_inv := fun y => if node_eq_dec y x then Some p else h_inv H y;
         h_pop := h_pop H |}.

    Lemma extend_inv_self H x p : h_inv (extend_inv H x p) x = Some p.
    Proof. simpl. destruct (node_eq_dec x x); congruence. Qed.

    Lemma extend_inv_other H x p y : y <> x -> h_inv (extend_inv H x p) y = h_inv H y.
    Proof. intros Hne. simpl. destruct (node_eq_dec y x); congruence. Qed.

    (** A history whose events all lie in gaps [<= u]. *)
    Definition bounded h (u : nat) : Prop :=
      (forall x p, h_inv h x = Some p -> (gap p <= u)%nat) /\
      (forall x p β, h_pop h x = Some (pair p β) -> (gap p <= u)%nat).

    Lemma strip_bounded h u :
      (forall x p, h_inv h x = Some p -> (gap p <= u)%nat) ->
      (forall x p β, h_pop h x = Some (pair p β) -> (gap p <= u)%nat) ->
      bounded (strip h u) (u - 1).
    Proof.
      intros Hi Hp. split.
      - intros x p Hx. apply strip_inv in Hx. destruct Hx as [Hx Hne].
        specialize (Hi x p Hx). lia.
      - intros x p β Hx. apply strip_pop in Hx. destruct Hx as [Hx Hne].
        specialize (Hp x p β Hx). lia.
    Qed.

    Lemma legal_bounded s h : legal s h -> bounded h (tsa_now s).
    Proof.
      intros Hl. split.
      - intros x p Hx. exact (proj1 (lg_inv s h Hl x p Hx)).
      - intros x p β Hx. exact (proj1 (lg_pop s h Hl x p β Hx)).
    Qed.

    (** * [⊨ I ∘ G_push-inv ⇒ I] *)

    Section PushInv.
      Variable s : @TryStackAuxState A.
      Variables (α : tid) (l : Addr) (v : A).
      Variable H : history.
      Variable Δ Δ' : config.
      Hypothesis Hwf : ghost_wf s.
      Hypothesis Hlag : I_lag s Δ.
      Hypothesis Hcan : canonical s H.
      Hypothesis Hpop : I_pop s H Δ.
      Hypothesis Hnone : TMap.find α (tsa_pending_pushes s) = None.
      Hypothesis Hfresh : tsa_fresh_node s (pair α l).
      Hypothesis Htok : forall ρ π, Δ ρ π -> TMap.find α π = Some (push_inv_token v).
      Hypothesis HΔ' : forall ρ' π', Δ' ρ' π' <->
        exists ρ π, Δ ρ π /\ specS (TSAReady (tsa_start_push α l v s)) ρ π ρ' π'.

      Local Notation s' := (tsa_start_push α l v s).
      Local Notation x := (pair α l).
      Local Notation t := (tsa_now s).

      Let Hwf' : ghost_wf s' := ghost_wf_start_push s α l v Hwf Hnone Hfresh.

      Lemma pi_x_not_vertex : ~ tsa_is_vertex s x.
      Proof. pose proof Hfresh as [Hv _]. unfold tsa_is_vertex. rewrite Hv. intro Hc. apply Hc. reflexivity. Qed.

      Lemma pi_x_ret : tsa_node_ret s x = None.
      Proof. apply (not_vertex_no_ret s x Hwf pi_x_not_vertex). Qed.

      Lemma pi_vertices y : y <> x -> tsa_vertices s' y = tsa_vertices s y.
      Proof. intros Hne. simpl. apply node_update_neq. congruence. Qed.

      Lemma pi_vertex_new : tsa_vertices s' x = Some v.
      Proof. simpl. apply node_update_eq. Qed.

      Lemma pi_pending_find β :
        TMap.find β (tsa_pending_pushes s') =
        if Pos.eq_dec β α then Some l else TMap.find β (tsa_pending_pushes s).
      Proof.
        simpl. destruct (Pos.eq_dec β α) as [->|Hne]; [apply TMap.gss|apply TMap.gso; congruence].
      Qed.

      Lemma pi_inv y : y <> x -> tsa_node_inv s' y = tsa_node_inv s y.
      Proof. intros Hne. simpl. apply node_update_neq. congruence. Qed.

      (** [lag] for the new concrete state. *)
      Lemma pi_lag r π :
        lag s r π -> TMap.find α π = Some (push_inv_token v) -> lag s' r π.
      Proof.
        intros Hl Hπ.
        assert (Hnvr : ~ ds_is_vertex r x).
        { intro Hv. apply pi_x_not_vertex. eapply lag_vertex; eauto. }
        constructor.
        - intros y v' Hy.
          assert (Hne : y <> x) by (intro; subst y; apply Hnvr; unfold ds_is_vertex; congruence).
          rewrite pi_vertices by exact Hne. eapply lag_vertices; eauto.
        - intros y Hvy Hnv. apply tsa_sp_is_vertex in Hvy. destruct Hvy as [Hvy| ->].
          + destruct (lag_unplaced _ _ _ Hl y Hvy Hnv) as [Hp Hrest].
            assert (Hne : y <> x) by (intro; subst y; exact (pi_x_not_vertex Hvy)).
            split; [apply tsa_sp_pending; [exact Hnone|now left]|].
            rewrite pi_vertices by exact Hne. exact Hrest.
          + split; [apply tsa_sp_pending; [exact Hnone|now right]|].
            exists v. split; [apply pi_vertex_new|exact Hπ].
        - intros β l' v' Hβ Hv' Hvr. rewrite pi_pending_find in Hβ.
          destruct (Pos.eq_dec β α) as [->|Hne].
          + injection Hβ as <-. contradiction.
          + assert (Hnex : pair β l' <> x) by (intro Heq; injection Heq as -> _; contradiction).
            rewrite pi_vertices in Hv' by exact Hnex. eapply lag_placed_pending; eauto.
        - intros β l'. rewrite pi_pending_find, (lag_pending _ _ _ Hl).
          destruct (Pos.eq_dec β α) as [->|Hne].
          + rewrite Hnone. split.
            * intros [Hc _]. discriminate.
            * intros [Heq Hvr]. injection Heq as <-. contradiction.
          + reflexivity.
        - intros y z He Hvy Hvz. apply tsa_sp_edges in He.
          destruct He as [He|[Heq _] ]; [eapply lag_edges_in; eauto|].
          rewrite Heq in Hvy. contradiction.
        - intros y z He. destruct (lag_edges_out _ _ _ Hl y z He) as (Hvy & Hvz & Hc).
          split; [exact Hvy|]. split; [exact Hvz|].
          assert (Hney : y <> x) by (intro; subst y; contradiction).
          assert (Hnez : z <> x) by (intro; subst z; contradiction).
          destruct Hc as [He'| (Hn1 & Hn2 & Hnp) ].
          + left. apply tsa_sp_edges. now left.
          + right. split; [|split].
            * intro Hc. apply tsa_sp_edges in Hc. destruct Hc as [Hc|[Hc _] ]; [contradiction|congruence].
            * intro Hc. apply tsa_sp_edges in Hc. destruct Hc as [Hc|[Hc _] ]; [contradiction|congruence].
            * intro Hc. apply tsa_sp_pending in Hc; [|exact Hnone]. destruct Hc; [contradiction|congruence].
        - intros y Hg. eapply lag_garbage_in; eauto.
        - intros y Hg. eapply lag_garbage_vertex; eauto.
        - intros y Hg Hng. destruct (lag_spec_justified _ _ _ Hl y Hg Hng) as (β & v' & HS & Hv' & Hπ').
          exists β, v'. split; [exact HS|]. split; [|exact Hπ'].
          assert (Hne : y <> x).
          { intro; subst y. apply pi_x_not_vertex. unfold tsa_is_vertex. congruence. }
          rewrite pi_vertices by exact Hne. exact Hv'.
        - intros β v' y Hπ'. eapply lag_succ_garbage; eauto.
      Qed.

      Lemma pi_I_lag : I_lag s' Δ'.
      Proof.
        eapply I_lag_specS with (σ := TSAReady s') (Δ := Δ); [reflexivity|exact Hwf'| |exact HΔ'].
        intros ρ π Hposs. destruct (Hlag ρ π Hposs) as (r & -> & Hl).
        exists r. split; [reflexivity|]. apply pi_lag; [exact Hl|]. eapply Htok; eauto.
      Qed.

      (** The canonical history places the new vertex lock-step. *)
      Definition H' : history := extend_inv H x (pair (S t) (Q2Qc (Qmake 0%Z 1%positive))).

      Lemma pi_H'_inv_other y : y <> x -> h_inv H' y = h_inv H y.
      Proof. intros Hne. unfold H'. apply extend_inv_other. exact Hne. Qed.

      Lemma pi_H'_pop y : h_pop H' y = h_pop H y.
      Proof. reflexivity. Qed.

      Lemma pi_H_x_unplaced : h_inv H x = None.
      Proof.
        destruct (h_inv H x) as [p|] eqn:Hp; [|reflexivity]. exfalso.
        apply pi_x_not_vertex. eapply legal_placed_vertex; [exact Hwf|exact (proj1 Hcan)|].
        unfold placed. congruence.
      Qed.

      Lemma pi_H_x_unpopped : h_pop H x = None.
      Proof.
        destruct (h_pop H x) as [p|] eqn:Hp; [|reflexivity]. exfalso.
        pose proof (legal_popped_placed s H x (proj1 Hcan)) as Hpl.
        unfold popped, placed in Hpl. rewrite pi_H_x_unplaced in Hpl. apply Hpl; congruence.
      Qed.

      Lemma pi_H'_canonical : canonical s' H'.
      Proof.
        pose proof Hcan as (Hleg & Hall & Hnospec & Hnnd).
        pose proof pi_H_x_unplaced as Hxu. pose proof pi_H_x_unpopped as Hxp.
        pose proof pi_x_ret as Hxr.
        assert (Hnow' : tsa_now s' = S t) by reflexivity.
        split; [|split; [|split] ].
        - constructor.
          + intros y p Hy. simpl in Hy. destruct (node_eq_dec y x) as [->|Hne].
            * injection Hy as <-. split; [simpl; lia|]. split.
              -- exists t. split; [simpl; apply node_update_eq|simpl; lia].
              -- intros ry Hry. simpl in Hry. congruence.
            * destruct (lg_inv s H Hleg y p Hy) as (Hgp & (i & Hi & Hig) & Hret).
              split; [simpl; lia|]. split; [|exact Hret].
              exists i. split; [|exact Hig]. rewrite pi_inv by exact Hne. exact Hi.
          + intros y Hc. unfold completed in Hc. simpl in Hc.
            assert (Hne : y <> x) by (intro; subst y; congruence).
            unfold placed. rewrite pi_H'_inv_other by exact Hne.
            apply (lg_inv_all s H Hleg y Hc).
          + intros n p β Hn. simpl in Hn.
            destruct (lg_pop s H Hleg n p β Hn) as (Hgp & (q & Hq & Hlt) & Hcase).
            split; [simpl; lia|]. split; [|exact Hcase].
            assert (Hne : n <> x) by (intro; subst n; congruence).
            exists q. split; [|exact Hlt]. rewrite pi_H'_inv_other by exact Hne. exact Hq.
          + intros n HM. simpl in HM. exact (lg_pop_all s H Hleg n HM).
          + intros n m p q β. simpl. apply (lg_spec s H Hleg).
          + intros n p β y q Hn Hy Hlt Hab. simpl in Hn, Hy.
            destruct (node_eq_dec y x) as [->|Hne].
            * injection Hy as <-. exfalso. destruct (lg_pop s H Hleg n p β Hn) as (Hgp & _).
              apply plt_gap_le in Hlt. simpl in Hlt. lia.
            * assert (Hab' : above s H y n).
              { destruct Hab as (p' & rn & Hp' & Hrn & Hlt'). simpl in Hrn.
                rewrite pi_H'_inv_other in Hp' by exact Hne. exists p', rn. auto. }
              exact (lg_top s H Hleg n p β y q Hn Hy Hlt Hab').
          + intros y z p Hy Hz. simpl in Hy, Hz.
            destruct (node_eq_dec y x) as [->|Hney]; destruct (node_eq_dec z x) as [->|Hnez].
            * reflexivity.
            * injection Hy as <-. destruct (lg_inv s H Hleg z _ Hz) as (Hgp & _). simpl in Hgp. lia.
            * injection Hz as <-. destruct (lg_inv s H Hleg y _ Hy) as (Hgp & _). simpl in Hgp. lia.
            * exact (lg_dist_inv s H Hleg y z p Hy Hz).
          + intros y z p β β'. simpl. apply (lg_dist_pop s H Hleg).
          + intros y z p β Hy Hz. simpl in Hy, Hz. destruct (node_eq_dec y x) as [->|Hne].
            * injection Hy as <-. destruct (lg_pop s H Hleg z _ _ Hz) as (Hgp & _). simpl in Hgp. lia.
            * exact (lg_dist_mix s H Hleg y z p β Hy Hz).
        - intros y Hv. apply tsa_sp_is_vertex in Hv. unfold placed. simpl.
          destruct (node_eq_dec y x) as [->|Hne]; [discriminate|].
          destruct Hv as [Hv|Hv]; [|contradiction]. exact (Hall y Hv).
        - intros n Hp. simpl in Hp. exact (Hnospec n Hp).
        - intros y m Hy Hab Hne. simpl in Hy.
          destruct (node_eq_dec y x) as [->|Hney].
          + exfalso. destruct Hab as (p & rm & Hp & Hrm & Hlt). simpl in Hrm.
            apply Hne. apply tsa_sp_edges. right. split; [reflexivity|].
            assert (Hvm : tsa_is_vertex s m) by (eapply gw_ret_vertex; eauto).
            split; [exact Hvm|]. intro Hpm. apply (gw_ret_pending s Hwf m Hvm) in Hpm. congruence.
          + assert (Hab' : above s H y m).
            { destruct Hab as (p & rm & Hp & Hrm & Hlt). simpl in Hrm.
              rewrite pi_H'_inv_other in Hp by exact Hney. exists p, rm. auto. }
            assert (Hne' : ~ tsa_edges s y m).
            { intro Hc. apply Hne. apply tsa_sp_edges. now left. }
            destruct (Hnnd y m Hy Hab' Hne') as (p & β & q & Hm & Hq & Hlt).
            exists p, β, q. split; [exact Hm|]. split; [|exact Hlt].
            rewrite pi_H'_inv_other by exact Hney. exact Hq.
      Qed.

      (** A plan of the new state, stripped of the new current gap, is a
          plan of the old state (with no speculative failures). *)
      Lemma pi_strip_x_unplaced h : legal s' h -> h_inv (strip h (S t)) x = None.
      Proof.
        intros Hl. apply strip_inv_none.
        destruct (h_inv h x) as [p|] eqn:Hp; [|now left]. right. exists p. split; [reflexivity|].
        destruct (lg_inv s' h Hl x p Hp) as (Hgp & (i & Hi & Hig) & _).
        simpl in Hgp, Hi. rewrite node_update_eq in Hi. injection Hi as <-. lia.
      Qed.

      Lemma pi_plan_back h :
        plan s' H' h -> plan s H (strip h (S t)).
      Proof.
        intros Hpl.
        pose proof (strip_plan s' Hwf' H' h Hpl) as Hpl'.
        pose proof (pl_legal _ _ _ Hpl') as Hl'.
        pose proof (pi_strip_x_unplaced h (pl_legal _ _ _ Hpl)) as Hxu.
        set (h0 := strip h (S t)) in *.
        assert (Hgap : forall y p, h_inv h0 y = Some p -> (gap p <= t)%nat).
        { intros y p Hy. apply strip_inv in Hy. destruct Hy as [Hy Hne].
          destruct (lg_inv s' h (pl_legal _ _ _ Hpl) y p Hy) as (Hgp & _). simpl in Hgp. lia. }
        assert (Hgapp : forall y p β, h_pop h0 y = Some (pair p β) -> (gap p <= t)%nat).
        { intros y p β Hy. apply strip_pop in Hy. destruct Hy as [Hy Hne].
          destruct (lg_pop s' h (pl_legal _ _ _ Hpl) y p β Hy) as (Hgp & _). simpl in Hgp. lia. }
        assert (Hnex : forall y, placed h0 y -> y <> x).
        { intros y Hy ->. unfold placed in Hy. congruence. }
        constructor.
        - constructor.
          + intros y p Hy. destruct (lg_inv s' h0 Hl' y p Hy) as (_ & (i & Hi & Hig) & Hret).
            assert (Hne : y <> x) by (apply Hnex; unfold placed; congruence).
            split; [eauto|]. split; [|exact Hret].
            exists i. split; [|exact Hig]. rewrite <- pi_inv by exact Hne. exact Hi.
          + intros y Hc. apply (lg_inv_all s' h0 Hl' y Hc).
          + intros n p β Hn. destruct (lg_pop s' h0 Hl' n p β Hn) as (_ & Hq & Hcase).
            split; [eauto|]. split; [exact Hq|exact Hcase].
          + intros n HM. apply (lg_pop_all s' h0 Hl' n HM).
          + apply (lg_spec s' h0 Hl').
          + intros n p β y q Hn Hy Hlt Hab. apply (lg_top s' h0 Hl' n p β y q Hn Hy Hlt Hab).
          + apply (lg_dist_inv s' h0 Hl').
          + apply (lg_dist_pop s' h0 Hl').
          + apply (lg_dist_mix s' h0 Hl').
        - intros m HM. exact (pl_committed _ _ _ Hpl' m HM).
        - intros y p Hy. destruct (pl_later _ _ _ Hpl' y p Hy) as (q & Hq & Hle).
          assert (Hne : y <> x) by (apply Hnex; unfold placed; congruence).
          exists q. split; [|exact Hle]. rewrite pi_H'_inv_other in Hq by exact Hne. exact Hq.
      Qed.

      Lemma pi_rep_state_fwd h r :
        h_inv h x = None -> rep_state s h r -> rep_state s' h r.
      Proof.
        intros Hxu Hr.
        assert (Hnex : forall y, placed h y -> y <> x) by (intros y Hy ->; unfold placed in Hy; congruence).
        constructor.
        - intros y Hy. rewrite pi_vertices by (apply Hnex; exact Hy). apply (rs_vertex_placed _ _ _ Hr). exact Hy.
        - intros y Hy. apply (rs_vertex_unplaced _ _ _ Hr). exact Hy.
        - intros y z. rewrite (rs_edges _ _ _ Hr). reflexivity.
        - intros β l'. rewrite (rs_pending _ _ _ Hr), pi_pending_find.
          destruct (Pos.eq_dec β α) as [->|Hne].
          + rewrite Hnone. split.
            * intros [Hc _]. discriminate.
            * intros [Heq Hpl]. injection Heq as <-. unfold placed in Hpl. congruence.
          + reflexivity.
        - intros y. apply (rs_garbage _ _ _ Hr).
      Qed.

      Lemma pi_rep_tokens_fwd h π :
        legal s h -> h_inv h x = None ->
        TMap.find α π = Some (push_inv_token v) ->
        rep_tokens s h π -> rep_tokens s' h π.
      Proof.
        intros Hl Hxu Hπα Hπ. constructor.
        - intros β l' v' Hβ Hv' Hnp. rewrite pi_pending_find in Hβ.
          destruct (Pos.eq_dec β α) as [->|Hne].
          + injection Hβ as <-. rewrite pi_vertex_new in Hv'. injection Hv' as <-. exact Hπα.
          + assert (Hnex : pair β l' <> x) by (intro Heq; injection Heq as -> _; contradiction).
            rewrite pi_vertices in Hv' by exact Hnex. eapply (rt_push_unplaced _ _ _ Hπ); eauto.
        - intros β l' v' Hβ Hv' Hpl. rewrite pi_pending_find in Hβ.
          destruct (Pos.eq_dec β α) as [->|Hne].
          + injection Hβ as <-. unfold placed in Hpl. congruence.
          + assert (Hnex : pair β l' <> x) by (intro Heq; injection Heq as -> _; contradiction).
            rewrite pi_vertices in Hv' by exact Hnex. eapply (rt_push_placed _ _ _ Hπ); eauto.
        - intros β n p v' HS Hn HM Hv'. simpl in HS, HM.
          assert (Hne : n <> x).
          { intro; subst n. pose proof (legal_popped_placed s h x Hl) as Hpl.
            unfold popped, placed in Hpl. rewrite Hxu in Hpl. apply Hpl; congruence. }
          rewrite pi_vertices in Hv' by exact Hne. eapply (rt_pop_spec _ _ _ Hπ); eauto.
        - intros β HS Hns. simpl in HS. eapply (rt_pop_pending _ _ _ Hπ); eauto.
      Qed.

      Lemma pi_I_pop : I_pop s' H' Δ'.
      Proof.
        intros h Hpl.
        pose proof (pi_plan_back h Hpl) as Hpl0.
        destruct (Hpop _ Hpl0) as (r & π & Hposs & Hr & Hπ).
        pose proof (pi_strip_x_unplaced h (pl_legal _ _ _ Hpl)) as Hxu.
        pose proof (pi_rep_state_fwd _ r Hxu Hr) as Hr'.
        pose proof (pi_rep_tokens_fwd _ π (pl_legal _ _ _ Hpl0) Hxu (Htok _ _ Hposs) Hπ) as Hπ'.
        destruct (plans_reached s' (TSAReady s') eq_refl Hwf' H' h Hpl r π Hr' Hπ')
          as (r' & π' & Hspec & Hr'' & Hπ'').
        exists r', π'. split; [|split; assumption].
        apply HΔ'. exists (DSReady r), π. split; assumption.
      Qed.

      Lemma pi_I_state : I_state s' Δ'.
      Proof.
        split; [exact Hwf'|]. split; [exact pi_I_lag|].
        exists H'. split; [exact pi_H'_canonical|exact pi_I_pop].
      Qed.

    End PushInv.

    (** * [⊨ I ∘ G_push-ret ⇒ I] *)

    Section PushRet.
      Variable s : @TryStackAuxState A.
      Variables (α : tid) (l : Addr) (v : A).
      Variable H : history.
      Variable Δ Δ'' Δ3 Δ' : config.
      Hypothesis Hwf : ghost_wf s.
      Hypothesis Hlag : I_lag s Δ.
      Hypothesis Hcan : canonical s H.
      Hypothesis Hpop : I_pop s H Δ.
      Hypothesis Hl : TMap.find α (tsa_pending_pushes s) = Some l.
      Hypothesis Hv : tsa_vertices s (pair α l) = Some v.
      Hypothesis HΔ'' : forall ρ' π', Δ'' ρ' π' <->
        exists ρ π, Δ ρ π /\ specS (TSAReady s) ρ π ρ' π'.
      Hypothesis HΔ3 : forall ρ' π', Δ3 ρ' π' <->
        exists r π, Δ'' (DSReady r) π /\ TMap.find α π = Some (push_lini_token v) /\
          ρ' = DSReady (ds_finish_push α r) /\ π' = TMap.add α (push_ret_token v) π.
      Hypothesis HΔ' : forall ρ' π', Δ' ρ' π' <->
        exists ρ π, Δ3 ρ π /\ specS (TSAReady (tsa_finish_push α s)) ρ π ρ' π'.

      Local Notation s' := (tsa_finish_push α s).
      Local Notation x := (pair α l).
      Local Notation t := (tsa_now s).

      Let Hwf' : ghost_wf s' := ghost_wf_finish_push s α l Hwf Hl.
      Let Hleg : legal s H := proj1 Hcan.

      Lemma pr_x_vertex : tsa_is_vertex s x.
      Proof. unfold tsa_is_vertex. rewrite Hv. discriminate. Qed.

      Lemma pr_x_ret : tsa_node_ret s x = None.
      Proof. apply (gw_ret_pending s Hwf x pr_x_vertex). exact Hl. Qed.

      Lemma pr_ret' y :
        tsa_node_ret s' y = if node_eq_dec x y then Some t else tsa_node_ret s y.
      Proof. simpl. rewrite Hl. reflexivity. Qed.

      Lemma pr_pending_find β :
        TMap.find β (tsa_pending_pushes s') =
        if Pos.eq_dec β α then None else TMap.find β (tsa_pending_pushes s).
      Proof.
        simpl. destruct (Pos.eq_dec β α) as [->|Hne]; [apply TMap.grs|apply TMap.gro; congruence].
      Qed.

      Lemma pr_pending_not_session β :
        TMap.find β (tsa_pending_pushes s) <> None ->
        session_open s β -> False.
      Proof.
        intros HP HS. destruct (TMap.find β (tsa_pending_pushes s)) as [l'|] eqn:Hl'; [|congruence].
        assert (Hpl : plan s H H).
        { constructor; [exact Hleg| |intros y p Hy; exists p; split; [exact Hy|apply ple_refl] ].
          intros m _. reflexivity. }
        destruct (Hpop H Hpl) as (r & π & _ & _ & Hπ).
        exact (rep_tokens_push_not_session s Hwf H π β l' Hleg Hπ Hl' HS).
      Qed.

      Lemma pr_lag r π :
        lag s r π -> TMap.find α π = Some (push_lini_token v) ->
        ds_is_vertex r x /\ TMap.find α (ds_pending_pushes r) = Some l /\
        lag s' (ds_finish_push α r) (TMap.add α (push_ret_token v) π).
      Proof.
        intros Hlg Hπ.
        assert (Hvr : ds_is_vertex r x).
        { destruct (classic (ds_is_vertex r x)) as [Hvr|Hnv]; [exact Hvr|]. exfalso.
          destruct (lag_unplaced _ _ _ Hlg x pr_x_vertex Hnv) as [_ (v' & _ & Hc) ].
          simpl in Hc. rewrite Hπ in Hc. discriminate. }
        split; [exact Hvr|]. split.
        { apply (lag_pending _ _ _ Hlg). split; assumption. }
        constructor.
        - intros y v' Hy. exact (lag_vertices _ _ _ Hlg y v' Hy).
        - intros y Hvy Hnv. simpl in Hvy, Hnv.
          destruct (lag_unplaced _ _ _ Hlg y Hvy Hnv) as [Hp (v' & Hv' & Hπ') ].
          assert (Hne : fst y <> α).
          { intro Heq. destruct y as [βy ly]. simpl in Heq. subst βy.
            unfold tsa_is_pending in Hp. simpl in Hp. rewrite (pending_unique_loc _ _ _ _ Hp Hl) in Hnv.
            contradiction. }
          split.
          + apply tsa_fp_pending. split; assumption.
          + exists v'. split; [exact Hv'|]. rewrite TMap.gso by exact Hne. exact Hπ'.
        - intros β l' v' Hβ Hv' Hvy. rewrite pr_pending_find in Hβ.
          destruct (Pos.eq_dec β α) as [->|Hne]; [discriminate|].
          rewrite TMap.gso by exact Hne. simpl in Hvy. eapply lag_placed_pending; eauto.
        - intros β l'. rewrite pr_pending_find, ds_fp_pending_find.
          destruct (Pos.eq_dec β α) as [->|Hne].
          + split; [discriminate|intros [Hc _]; discriminate].
          + simpl. apply (lag_pending _ _ _ Hlg).
        - intros y z He Hvy Hvz. exact (lag_edges_in _ _ _ Hlg y z He Hvy Hvz).
        - intros y z He. simpl in He.
          destruct (lag_edges_out _ _ _ Hlg y z He) as (Hvy & Hvz & Hc).
          split; [exact Hvy|]. split; [exact Hvz|].
          destruct Hc as [He'| (Hn1 & Hn2 & Hnp) ]; [now left|].
          right. split; [exact Hn1|]. split; [exact Hn2|].
          intro Hc. apply tsa_fp_pending in Hc. apply Hnp. exact (proj1 Hc).
        - intros y Hg. exact (lag_garbage_in _ _ _ Hlg y Hg).
        - intros y Hg. exact (lag_garbage_vertex _ _ _ Hlg y Hg).
        - intros y Hg Hng. simpl in Hg, Hng.
          destruct (lag_spec_justified _ _ _ Hlg y Hg Hng) as (β & v' & HS & Hv' & Hπ').
          exists β, v'. split; [exact HS|]. split; [exact Hv'|].
          assert (Hne : β <> α) by (intro; subst; rewrite Hπ in Hπ'; discriminate).
          rewrite TMap.gso by exact Hne. exact Hπ'.
        - intros β v' y Hπ'. simpl.
          destruct (Pos.eq_dec β α) as [->|Hne].
          + rewrite TMap.gss in Hπ'. discriminate.
          + rewrite TMap.gso in Hπ' by exact Hne. eapply lag_succ_garbage; eauto.
      Qed.

      Lemma pr_I_lag_Δ'' : I_lag s Δ''.
      Proof. eapply I_lag_specS with (σ := TSAReady s) (Δ := Δ); [reflexivity|exact Hwf|exact Hlag|exact HΔ'']. Qed.

      (** The abstract response is enabled in every filtered possibility, so
          the enabledness side condition can be dropped from the paper's set
          comprehension. *)
      Lemma pr_Δ3_paper_form (Δ3' : config) :
        (forall ρ' π', Δ3' ρ' π' <->
          exists r l' π, Δ'' (DSReady r) π /\
            TMap.find α (ds_pending_pushes r) = Some l' /\
            TMap.find α π = Some (push_lini_token v) /\
            ρ' = DSReady (ds_finish_push α r) /\ π' = TMap.add α (push_ret_token v) π) ->
        (forall ρ' π', Δ3' ρ' π' <->
          exists r π, Δ'' (DSReady r) π /\ TMap.find α π = Some (push_lini_token v) /\
            ρ' = DSReady (ds_finish_push α r) /\ π' = TMap.add α (push_ret_token v) π).
      Proof.
        intros Hiff ρ' π'. rewrite Hiff. split.
        - intros (r & l' & π & Hposs & _ & Hπ & -> & ->). eauto 8.
        - intros (r & π & Hposs & Hπ & -> & ->).
          destruct (pr_I_lag_Δ'' _ _ Hposs) as (r0 & Heq & Hlg). injection Heq as <-.
          destruct (pr_lag _ _ Hlg Hπ) as (_ & HP & _).
          exists r, l, π. auto.
      Qed.

      Lemma pr_I_lag : I_lag s' Δ'.
      Proof.
        eapply I_lag_specS with (σ := TSAReady s') (Δ := Δ3); [reflexivity|exact Hwf'| |exact HΔ'].
        intros ρ π Hposs. apply HΔ3 in Hposs. destruct Hposs as (r & π0 & Hposs & Hπ0 & -> & ->).
        destruct (pr_I_lag_Δ'' _ _ Hposs) as (r0 & Heq & Hlg). injection Heq as <-.
        destruct (pr_lag _ π0 Hlg Hπ0) as (_ & _ & Hlg'). eauto.
      Qed.

      Lemma pr_H_canonical : canonical s' H.
      Proof.
        pose proof Hcan as (Hleg0 & Hall & Hnospec & Hnnd).
        assert (Hnow' : tsa_now s' = S t) by reflexivity.
        pose proof (legal_bounded s H Hleg0) as [Hbi Hbp].
        split; [|split; [|split] ].
        - constructor.
          + intros y p Hy. destruct (lg_inv s H Hleg0 y p Hy) as (Hgp & Hi & Hret).
            split; [rewrite Hnow'; lia|]. split; [simpl; exact Hi|].
            intros ry Hry. rewrite pr_ret' in Hry. destruct (node_eq_dec x y) as [<-|Hne].
            * injection Hry as <-. exact Hgp.
            * exact (Hret ry Hry).
          + intros y Hc. unfold completed in Hc. rewrite pr_ret' in Hc.
            destruct (node_eq_dec x y) as [<-|Hne]; [apply Hall; exact pr_x_vertex|].
            apply (lg_inv_all s H Hleg0 y Hc).
          + intros n p β Hn. destruct (lg_pop s H Hleg0 n p β Hn) as (Hgp & Hq & Hcase).
            split; [rewrite Hnow'; lia|]. split; [exact Hq|exact Hcase].
          + intros n HM. exact (lg_pop_all s H Hleg0 n HM).
          + apply (lg_spec s H Hleg0).
          + intros n p β y q Hn Hy Hlt Hab.
            assert (Hab' : above s H y n).
            { destruct Hab as (p' & rn & Hp' & Hrn & Hlt'). rewrite pr_ret' in Hrn.
              destruct (node_eq_dec x n) as [<-|Hne].
              - exfalso. injection Hrn as <-. specialize (Hbi y p' Hp'). lia.
              - exists p', rn. auto. }
            exact (lg_top s H Hleg0 n p β y q Hn Hy Hlt Hab').
          + apply (lg_dist_inv s H Hleg0).
          + apply (lg_dist_pop s H Hleg0).
          + apply (lg_dist_mix s H Hleg0).
        - intros y Hvy. apply Hall. exact Hvy.
        - intros n Hp. apply Hnospec. exact Hp.
        - intros y m Hy Hab Hne.
          assert (Hab' : above s H y m).
          { destruct Hab as (p & rm & Hp & Hrm & Hlt). rewrite pr_ret' in Hrm.
            destruct (node_eq_dec x m) as [<-|Hnex].
            - exfalso. injection Hrm as <-. specialize (Hbi y p Hp). lia.
            - exists p, rm. auto. }
          exact (Hnnd y m Hy Hab' Hne).
      Qed.

      (** Plans of the new state (stripped) are plans of the old one, and
          place the completed vertex. *)
      Lemma pr_plan_back h :
        plan s' H h ->
        plan s H (strip h (S t)) /\ placed (strip h (S t)) x.
      Proof.
        intros Hpl.
        pose proof (strip_plan s' Hwf' H h Hpl) as Hpl'.
        pose proof (pl_legal _ _ _ Hpl') as Hl'.
        set (h0 := strip h (S t)) in *.
        assert (Hgap : forall y p, h_inv h0 y = Some p -> (gap p <= t)%nat).
        { intros y p Hy. apply strip_inv in Hy. destruct Hy as [Hy Hne].
          destruct (lg_inv s' h (pl_legal _ _ _ Hpl) y p Hy) as (Hgp & _). simpl in Hgp. lia. }
        assert (Hgapp : forall y p β, h_pop h0 y = Some (pair p β) -> (gap p <= t)%nat).
        { intros y p β Hy. apply strip_pop in Hy. destruct Hy as [Hy Hne].
          destruct (lg_pop s' h (pl_legal _ _ _ Hpl) y p β Hy) as (Hgp & _). simpl in Hgp. lia. }
        split.
        - constructor.
          + constructor.
            * intros y p Hy. destruct (lg_inv s' h0 Hl' y p Hy) as (_ & Hi & Hret).
              split; [eauto|]. split; [exact Hi|].
              intros ry Hry. apply Hret. rewrite pr_ret'. destruct (node_eq_dec x y) as [<-|Hne]; [|exact Hry].
              rewrite pr_x_ret in Hry. discriminate.
            * intros y Hc. apply (lg_inv_all s' h0 Hl' y). unfold completed in *.
              rewrite pr_ret'. destruct (node_eq_dec x y); [discriminate|exact Hc].
            * intros n p β Hn. destruct (lg_pop s' h0 Hl' n p β Hn) as (_ & Hq & Hcase).
              split; [eauto|]. split; [exact Hq|exact Hcase].
            * intros n HM. apply (lg_pop_all s' h0 Hl' n HM).
            * apply (lg_spec s' h0 Hl').
            * intros n p β y q Hn Hy Hlt Hab. apply (lg_top s' h0 Hl' n p β y q Hn Hy Hlt).
              destruct Hab as (p' & rn & Hp' & Hrn & Hlt'). exists p', rn. split; [exact Hp'|].
              split; [|exact Hlt']. rewrite pr_ret'. destruct (node_eq_dec x n) as [<-|Hne]; [|exact Hrn].
              rewrite pr_x_ret in Hrn. discriminate.
            * apply (lg_dist_inv s' h0 Hl').
            * apply (lg_dist_pop s' h0 Hl').
            * apply (lg_dist_mix s' h0 Hl').
          + intros m HM. exact (pl_committed _ _ _ Hpl' m HM).
          + intros y p Hy. exact (pl_later _ _ _ Hpl' y p Hy).
        - apply (lg_inv_all s' h0 Hl' x). unfold completed. rewrite pr_ret'.
          destruct (node_eq_dec x x); [discriminate|contradiction].
      Qed.

      Lemma pr_rep_state_fwd h r :
        bounded h t -> rep_state s h r -> placed h x ->
        rep_state s' h (ds_finish_push α r).
      Proof.
        intros [Hbi _] Hr Hpx. constructor.
        - intros y Hy. simpl. apply (rs_vertex_placed _ _ _ Hr y Hy).
        - intros y Hy. simpl. apply (rs_vertex_unplaced _ _ _ Hr y Hy).
        - intros y z. simpl. rewrite (rs_edges _ _ _ Hr).
          assert (Hab : above s' h y z <-> above s h y z).
          { unfold above. split; intros (p & rz & Hp & Hrz & Hlt); exists p, rz.
            - rewrite pr_ret' in Hrz. destruct (node_eq_dec x z) as [<-|Hne]; [|auto].
              injection Hrz as <-. specialize (Hbi y p Hp). lia.
            - rewrite pr_ret'. destruct (node_eq_dec x z) as [<-|Hne]; [|auto].
              rewrite pr_x_ret in Hrz. discriminate. }
          rewrite Hab. reflexivity.
        - intros β l'. rewrite ds_fp_pending_find, pr_pending_find.
          destruct (Pos.eq_dec β α) as [->|Hne].
          + split; [discriminate|intros [Hc _]; discriminate].
          + apply (rs_pending _ _ _ Hr).
        - intros y. simpl. apply (rs_garbage _ _ _ Hr).
      Qed.

      Lemma pr_rep_tokens_fwd h π :
        rep_tokens s h π ->
        rep_tokens s' h (TMap.add α (push_ret_token v) π).
      Proof.
        intros Hπ. constructor.
        - intros β l' v' Hβ Hv' Hnp. rewrite pr_pending_find in Hβ.
          destruct (Pos.eq_dec β α) as [->|Hne]; [discriminate|].
          rewrite TMap.gso by exact Hne. simpl in Hv'. eapply (rt_push_unplaced _ _ _ Hπ); eauto.
        - intros β l' v' Hβ Hv' Hpl. rewrite pr_pending_find in Hβ.
          destruct (Pos.eq_dec β α) as [->|Hne]; [discriminate|].
          rewrite TMap.gso by exact Hne. simpl in Hv'. eapply (rt_push_placed _ _ _ Hπ); eauto.
        - intros β n p v' HS Hn HM Hv'. simpl in HS, HM, Hv'.
          assert (Hne : β <> α) by (intro; subst; apply (pr_pending_not_session α); [congruence|exact HS]).
          rewrite TMap.gso by exact Hne. eapply (rt_pop_spec _ _ _ Hπ); eauto.
        - intros β HS Hns. simpl in HS.
          assert (Hne : β <> α) by (intro; subst; apply (pr_pending_not_session α); [congruence|exact HS]).
          rewrite TMap.gso by exact Hne. eapply (rt_pop_pending _ _ _ Hπ); eauto.
      Qed.

      (** Every plan of the old state that places [x] yields an element of
          the filtered set; used for nonemptiness and for [I_pop]. *)
      Lemma pr_plan_to_Δ3 h :
        plan s H h -> placed h x ->
        exists r π, Δ'' (DSReady r) π /\ TMap.find α π = Some (push_lini_token v) /\
          rep_state s h r /\ rep_tokens s h π.
      Proof.
        intros Hpl Hpx. destruct (Hpop h Hpl) as (r & π & Hposs & Hr & Hπ).
        exists r, π. split; [apply HΔ''; exists (DSReady r), π; split; [exact Hposs|constructor]|].
        split; [|split; assumption].
        eapply (rt_push_placed _ _ _ Hπ); eauto.
      Qed.

      Lemma pr_nonempty :
        exists r π, Δ'' (DSReady r) π /\ TMap.find α π = Some (push_lini_token v).
      Proof.
        assert (Hpl : plan s H H).
        { constructor; [exact Hleg| |intros y p Hy; exists p; split; [exact Hy|apply ple_refl] ].
          intros m _. reflexivity. }
        destruct (pr_plan_to_Δ3 H Hpl (proj1 (proj2 Hcan) x pr_x_vertex)) as (r & π & Hposs & Hπα & _).
        eauto.
      Qed.

      Lemma pr_I_pop : I_pop s' H Δ'.
      Proof.
        intros h Hpl.
        destruct (pr_plan_back h Hpl) as [Hpl0 Hpx].
        destruct (pr_plan_to_Δ3 _ Hpl0 Hpx) as (r & π & Hposs & Hπα & Hr & Hπ).
        assert (Hb : bounded (strip h (S t)) t).
        { pose proof (legal_bounded s _ (pl_legal _ _ _ Hpl0)) as Hb. exact Hb. }
        pose proof (pr_rep_state_fwd _ r Hb Hr Hpx) as Hr'.
        pose proof (pr_rep_tokens_fwd _ π Hπ) as Hπ'.
        destruct (plans_reached s' (TSAReady s') eq_refl Hwf' H h Hpl _ _ Hr' Hπ')
          as (r' & π' & Hspec & Hr'' & Hπ'').
        exists r', π'. split; [|split; assumption].
        apply HΔ'. eexists _, _. split; [|exact Hspec].
        apply HΔ3. exists r, π. auto.
      Qed.

      Lemma pr_I_state : I_state s' Δ'.
      Proof.
        split; [exact Hwf'|]. split; [exact pr_I_lag|].
        exists H. split; [exact pr_H_canonical|exact pr_I_pop].
      Qed.

    End PushRet.

    (** * [⊨ I ∘ G_snap ⇒ I] *)

    Section Snap.
      Variable s : @TryStackAuxState A.
      Variable α : tid.
      Variable H : history.
      Variable Δ Δ' : config.
      Hypothesis Hwf : ghost_wf s.
      Hypothesis Hlag : I_lag s Δ.
      Hypothesis Hcan : canonical s H.
      Hypothesis Hpop : I_pop s H Δ.
      Variable start : TS.
      Hypothesis HSnone : TMap.find α (tsa_snapshots s) = None.
      Hypothesis Hts : TMap.find α (tsa_pop_ts s) = Some start.
      Hypothesis HΔ' : forall ρ' π', Δ' ρ' π' <->
        exists ρ π, Δ ρ π /\ specS (TSAReady (tsa_start_snapshot α s)) ρ π ρ' π'.

      Local Notation s' := (tsa_start_snapshot α s).
      Local Notation t := (tsa_now s).

      Let Hwf' : ghost_wf s' := ghost_wf_start_snapshot s α start Hwf HSnone Hts.

      Lemma sn_snap_find β :
        TMap.find β (tsa_snapshots s') =
        if Pos.eq_dec β α then Some (fun n => tsa_is_vertex s n) else TMap.find β (tsa_snapshots s).
      Proof.
        simpl. destruct (Pos.eq_dec β α) as [->|Hne]; [apply TMap.gss|apply TMap.gso; congruence].
      Qed.

      Lemma sn_time_find β :
        TMap.find β (tsa_snap_time s') =
        if Pos.eq_dec β α then Some t else TMap.find β (tsa_snap_time s).
      Proof.
        simpl. destruct (Pos.eq_dec β α) as [->|Hne]; [apply TMap.gss|apply TMap.gso; congruence].
      Qed.

      Lemma sn_lag r π : lag s r π -> lag s' r π.
      Proof.
        intros Hlg. constructor.
        - intros y v' Hy. exact (lag_vertices _ _ _ Hlg y v' Hy).
        - intros y Hvy Hnv. exact (lag_unplaced _ _ _ Hlg y Hvy Hnv).
        - intros β l' v' Hβ Hv' Hvy. exact (lag_placed_pending _ _ _ Hlg β l' v' Hβ Hv' Hvy).
        - intros β l'. exact (lag_pending _ _ _ Hlg β l').
        - intros y z He Hvy Hvz. exact (lag_edges_in _ _ _ Hlg y z He Hvy Hvz).
        - intros y z He. exact (lag_edges_out _ _ _ Hlg y z He).
        - intros y Hg. exact (lag_garbage_in _ _ _ Hlg y Hg).
        - intros y Hg. exact (lag_garbage_vertex _ _ _ Hlg y Hg).
        - intros y Hg Hng.
          destruct (lag_spec_justified _ _ _ Hlg y Hg Hng) as (β & v' & HS & Hv' & Hπ').
          exists β, v'. split; [exact HS|auto].
        - intros β v' y Hπ'. exact (lag_succ_garbage _ _ _ Hlg β v' y Hπ').
      Qed.

      Lemma sn_I_lag : I_lag s' Δ'.
      Proof.
        eapply I_lag_specS with (σ := TSAReady s') (Δ := Δ); [reflexivity|exact Hwf'| |exact HΔ'].
        intros ρ π Hposs. destruct (Hlag ρ π Hposs) as (r & -> & Hl). exists r. split; [reflexivity|].
        apply sn_lag. exact Hl.
      Qed.

      Lemma sn_H_canonical : canonical s' H.
      Proof.
        pose proof Hcan as (Hleg & Hall & Hnospec & Hnnd).
        split; [|split; [|split] ].
        - constructor.
          + intros y p Hy. destruct (lg_inv s H Hleg y p Hy) as (Hgp & Hi & Hret).
            split; [simpl; lia|]. split; [exact Hi|exact Hret].
          + intros y Hc. exact (lg_inv_all s H Hleg y Hc).
          + intros n p β Hn. destruct (lg_pop s H Hleg n p β Hn) as (Hgp & Hq & Hcase).
            split; [simpl; lia|]. split; [exact Hq|exact Hcase].
          + intros n HM. exact (lg_pop_all s H Hleg n HM).
          + apply (lg_spec s H Hleg).
          + intros n p β y q Hn Hy Hlt Hab. exact (lg_top s H Hleg n p β y q Hn Hy Hlt Hab).
          + apply (lg_dist_inv s H Hleg).
          + apply (lg_dist_pop s H Hleg).
          + apply (lg_dist_mix s H Hleg).
        - exact Hall.
        - exact Hnospec.
        - exact Hnnd.
      Qed.

      Lemma sn_plan_back h :
        plan s' H h -> plan s H (strip h (S t)).
      Proof.
        intros Hpl.
        pose proof (strip_plan s' Hwf' H h Hpl) as Hpl'.
        pose proof (pl_legal _ _ _ Hpl') as Hl'.
        set (h0 := strip h (S t)) in *.
        assert (Hgap : forall y p, h_inv h0 y = Some p -> (gap p <= t)%nat).
        { intros y p Hy. apply strip_inv in Hy. destruct Hy as [Hy Hne].
          destruct (lg_inv s' h (pl_legal _ _ _ Hpl) y p Hy) as (Hgp & _). simpl in Hgp. lia. }
        assert (Hgapp : forall y p β, h_pop h0 y = Some (pair p β) -> (gap p <= t)%nat).
        { intros y p β Hy. apply strip_pop in Hy. destruct Hy as [Hy Hne].
          destruct (lg_pop s' h (pl_legal _ _ _ Hpl) y p β Hy) as (Hgp & _). simpl in Hgp. lia. }
        constructor.
        - constructor.
          + intros y p Hy. destruct (lg_inv s' h0 Hl' y p Hy) as (_ & Hi & Hret).
            split; [eauto|]. split; [exact Hi|exact Hret].
          + intros y Hc. exact (lg_inv_all s' h0 Hl' y Hc).
          + intros n p β Hn. destruct (lg_pop s' h0 Hl' n p β Hn) as (_ & Hq & Hcase).
            split; [eauto|]. split; [exact Hq|exact Hcase].
          + intros n HM. exact (lg_pop_all s' h0 Hl' n HM).
          + apply (lg_spec s' h0 Hl').
          + intros n p β y q Hn Hy Hlt Hab. exact (lg_top s' h0 Hl' n p β y q Hn Hy Hlt Hab).
          + apply (lg_dist_inv s' h0 Hl').
          + apply (lg_dist_pop s' h0 Hl').
          + apply (lg_dist_mix s' h0 Hl').
        - intros m HM. exact (pl_committed _ _ _ Hpl' m HM).
        - intros y p Hy. exact (pl_later _ _ _ Hpl' y p Hy).
      Qed.

      Lemma sn_rep_state_fwd h r : rep_state s h r -> rep_state s' h r.
      Proof.
        intros Hr. constructor.
        - intros y Hy. exact (rs_vertex_placed _ _ _ Hr y Hy).
        - intros y Hy. exact (rs_vertex_unplaced _ _ _ Hr y Hy).
        - intros y z. exact (rs_edges _ _ _ Hr y z).
        - intros β l'. exact (rs_pending _ _ _ Hr β l').
        - intros y. exact (rs_garbage _ _ _ Hr y).
      Qed.

      Lemma sn_rep_tokens_fwd h π :
        rep_tokens s h π -> rep_tokens s' h π.
      Proof.
        intros Hπ. constructor.
        - intros β l' v' Hβ Hv' Hnp. exact (rt_push_unplaced _ _ _ Hπ β l' v' Hβ Hv' Hnp).
        - intros β l' v' Hβ Hv' Hpl. exact (rt_push_placed _ _ _ Hπ β l' v' Hβ Hv' Hpl).
        - intros β n p v' HS Hn HM Hv'. exact (rt_pop_spec _ _ _ Hπ β n p v' HS Hn HM Hv').
        - intros β HS Hns. exact (rt_pop_pending _ _ _ Hπ β HS Hns).
      Qed.

      Lemma sn_I_pop : I_pop s' H Δ'.
      Proof.
        intros h Hpl.
        pose proof (sn_plan_back h Hpl) as Hpl0.
        destruct (Hpop _ Hpl0) as (r & π & Hposs & Hr & Hπ).
        pose proof (sn_rep_state_fwd _ r Hr) as Hr'.
        pose proof (sn_rep_tokens_fwd _ π Hπ) as Hπ'.
        destruct (plans_reached s' (TSAReady s') eq_refl Hwf' H h Hpl r π Hr' Hπ')
          as (r' & π' & Hspec & Hr'' & Hπ'').
        exists r', π'. split; [|split; assumption].
        apply HΔ'. exists (DSReady r), π. split; assumption.
      Qed.

      Lemma sn_I_state : I_state s' Δ'.
      Proof.
        split; [exact Hwf'|]. split; [exact sn_I_lag|].
        exists H. split; [exact sn_H_canonical|exact sn_I_pop].
      Qed.

    End Snap.

    (** * [⊨ I ∘ G_fail ⇒ I] *)

    Section Fail.
      Variable s : @TryStackAuxState A.
      Variable α : tid.
      Variable N : LPNodeSet.
      Variable H : history.
      Variable Δ Δ'' Δ' : config.
      Hypothesis Hwf : ghost_wf s.
      Hypothesis Hlag : I_lag s Δ.
      Hypothesis Hcan : canonical s H.
      Hypothesis Hpop : I_pop s H Δ.
      Hypothesis HS : TMap.find α (tsa_snapshots s) = Some N.
      Hypothesis HΔ'' : forall ρ' π', Δ'' ρ' π' <->
        exists ρ π, Δ ρ π /\ specS (TSAReady s) ρ π ρ' π'.
      Hypothesis HΔ' : forall ρ' π', Δ' ρ' π' <->
        exists ρ π, Δ'' ρ π /\ specS (TSAReady (tsa_clear_snapshot α s)) ρ π ρ' π'.

      Local Notation s' := (tsa_clear_snapshot α s).
      Local Notation t := (tsa_now s).

      Let Hwf' : ghost_wf s' := ghost_wf_clear_snapshot s α Hwf.
      Let Hleg : legal s H := proj1 Hcan.

      Lemma fl_snap_find β :
        TMap.find β (tsa_snapshots s') =
        if Pos.eq_dec β α then None else TMap.find β (tsa_snapshots s).
      Proof.
        simpl. destruct (Pos.eq_dec β α) as [->|Hne]; [apply TMap.grs|apply TMap.gro; congruence].
      Qed.

      Lemma fl_time_find β :
        TMap.find β (tsa_snap_time s') =
        if Pos.eq_dec β α then None else TMap.find β (tsa_snap_time s).
      Proof.
        simpl. destruct (Pos.eq_dec β α) as [->|Hne]; [apply TMap.grs|apply TMap.gro; congruence].
      Qed.

      (** Clearing a snapshot changes nothing the lag relation sees. *)
      Lemma fl_lag r π : lag s r π -> lag s' r π.
      Proof.
        intros Hlg. constructor.
        - intros y v' Hy. exact (lag_vertices _ _ _ Hlg y v' Hy).
        - intros y Hvy Hnv. exact (lag_unplaced _ _ _ Hlg y Hvy Hnv).
        - intros β l' v' Hβ Hv' Hvy. exact (lag_placed_pending _ _ _ Hlg β l' v' Hβ Hv' Hvy).
        - intros β l'. exact (lag_pending _ _ _ Hlg β l').
        - intros y z He Hvy Hvz. exact (lag_edges_in _ _ _ Hlg y z He Hvy Hvz).
        - intros y z He. exact (lag_edges_out _ _ _ Hlg y z He).
        - intros y Hg. exact (lag_garbage_in _ _ _ Hlg y Hg).
        - intros y Hg. exact (lag_garbage_vertex _ _ _ Hlg y Hg).
        - intros y Hg Hng.
          destruct (lag_spec_justified _ _ _ Hlg y Hg Hng) as (β & v' & HS' & Hv' & Hπ').
          exists β, v'. split; [exact HS'|auto].
        - intros β v' y Hπ'. exact (lag_succ_garbage _ _ _ Hlg β v' y Hπ').
      Qed.

      Lemma fl_I_lag : I_lag s' Δ'.
      Proof.
        eapply I_lag_specS with (σ := TSAReady s') (Δ := Δ''); [reflexivity|exact Hwf'| |exact HΔ'].
        intros ρ π Hposs. apply HΔ'' in Hposs. destruct Hposs as (ρ0 & π0 & Hposs0 & Hspec).
        destruct (specS_lag s (TSAReady s) ρ0 π0 ρ π eq_refl Hwf (Hlag _ _ Hposs0) Hspec) as (r & -> & Hlg).
        exists r. split; [reflexivity|]. apply fl_lag; assumption.
      Qed.

      Lemma fl_H_canonical : canonical s' H.
      Proof.
        pose proof Hcan as (Hleg0 & Hall & Hnospec & Hnnd).
        split; [|split; [|split] ].
        - constructor.
          + intros y p Hy. destruct (lg_inv s H Hleg0 y p Hy) as (Hgp & Hi & Hret).
            split; [simpl; lia|]. split; [exact Hi|exact Hret].
          + intros y Hc. exact (lg_inv_all s H Hleg0 y Hc).
          + intros m p β Hm. destruct (lg_pop s H Hleg0 m p β Hm) as (Hgp & Hq & Hcase).
            split; [simpl; lia|]. split; [exact Hq|exact Hcase].
          + intros m HM. exact (lg_pop_all s H Hleg0 m HM).
          + apply (lg_spec s H Hleg0).
          + intros m p β y q Hm Hy Hlt Hab. exact (lg_top s H Hleg0 m p β y q Hm Hy Hlt Hab).
          + apply (lg_dist_inv s H Hleg0).
          + apply (lg_dist_pop s H Hleg0).
          + apply (lg_dist_mix s H Hleg0).
        - exact Hall.
        - exact Hnospec.
        - exact Hnnd.
      Qed.

      Lemma fl_plan_back h :
        plan s' H h -> plan s H (strip h (S t)).
      Proof.
        intros Hpl.
        pose proof (strip_plan s' Hwf' H h Hpl) as Hpl'.
        pose proof (pl_legal _ _ _ Hpl') as Hl'.
        set (h0 := strip h (S t)) in *.
        assert (Hgap : forall y p, h_inv h0 y = Some p -> (gap p <= t)%nat).
        { intros y p Hy. apply strip_inv in Hy. destruct Hy as [Hy Hne].
          destruct (lg_inv s' h (pl_legal _ _ _ Hpl) y p Hy) as (Hgp & _). simpl in Hgp. lia. }
        assert (Hgapp : forall y p β, h_pop h0 y = Some (pair p β) -> (gap p <= t)%nat).
        { intros y p β Hy. apply strip_pop in Hy. destruct Hy as [Hy Hne].
          destruct (lg_pop s' h (pl_legal _ _ _ Hpl) y p β Hy) as (Hgp & _). simpl in Hgp. lia. }
        constructor.
        - constructor.
          + intros y p Hy. destruct (lg_inv s' h0 Hl' y p Hy) as (_ & Hi & Hret).
            split; [eauto|]. split; [exact Hi|exact Hret].
          + intros y Hc. exact (lg_inv_all s' h0 Hl' y Hc).
          + intros m p β Hm. destruct (lg_pop s' h0 Hl' m p β Hm) as (_ & Hq & Hcase).
            split; [eauto|]. split; [exact Hq|exact Hcase].
          + intros m HM. exact (lg_pop_all s' h0 Hl' m HM).
          + apply (lg_spec s' h0 Hl').
          + intros m p β y q Hm Hy Hlt Hab. exact (lg_top s' h0 Hl' m p β y q Hm Hy Hlt Hab).
          + apply (lg_dist_inv s' h0 Hl').
          + apply (lg_dist_pop s' h0 Hl').
          + apply (lg_dist_mix s' h0 Hl').
        - intros m HM. exact (pl_committed _ _ _ Hpl' m HM).
        - intros y p Hy. exact (pl_later _ _ _ Hpl' y p Hy).
      Qed.

      Lemma fl_rep_state_fwd h r : rep_state s h r -> rep_state s' h r.
      Proof.
        intros Hr. constructor.
        - intros y Hy. exact (rs_vertex_placed _ _ _ Hr y Hy).
        - intros y Hy. exact (rs_vertex_unplaced _ _ _ Hr y Hy).
        - intros y z. exact (rs_edges _ _ _ Hr y z).
        - intros β l'. exact (rs_pending _ _ _ Hr β l').
        - intros y. exact (rs_garbage _ _ _ Hr y).
      Qed.

      Lemma fl_rep_tokens_fwd h π :
        rep_tokens s h π -> rep_tokens s' h π.
      Proof.
        intros Hπ. constructor.
        - intros β l' v' Hβ Hv' Hnp. exact (rt_push_unplaced _ _ _ Hπ β l' v' Hβ Hv' Hnp).
        - intros β l' v' Hβ Hv' Hpl. exact (rt_push_placed _ _ _ Hπ β l' v' Hβ Hv' Hpl).
        - intros β m p v' HS' Hm HM Hv'. exact (rt_pop_spec _ _ _ Hπ β m p v' HS' Hm HM Hv').
        - intros β HS' Hns. exact (rt_pop_pending _ _ _ Hπ β HS' Hns).
      Qed.

      Lemma fl_I_pop : I_pop s' H Δ'.
      Proof.
        intros h Hpl.
        pose proof (fl_plan_back h Hpl) as Hpl0.
        destruct (Hpop _ Hpl0) as (r & π & Hposs & Hr & Hπ).
        pose proof (fl_rep_state_fwd _ r Hr) as Hr'.
        pose proof (fl_rep_tokens_fwd _ π Hπ) as Hπ'.
        destruct (plans_reached s' (TSAReady s') eq_refl Hwf' H h Hpl _ _ Hr' Hπ')
          as (r' & π' & Hspec & Hr'' & Hπ'').
        exists r', π'. split; [|split; assumption].
        apply HΔ'. exists (DSReady r), π. split; [|exact Hspec].
        apply HΔ''. exists (DSReady r), π. split; [exact Hposs|constructor].
      Qed.

      Lemma fl_I_state : I_state s' Δ'.
      Proof.
        split; [exact Hwf'|]. split; [exact fl_I_lag|].
        exists H. split; [exact fl_H_canonical|exact fl_I_pop].
      Qed.

    End Fail.

    (** * [⊨ I ∘ G_emp ⇒ I]: the atomic empty invocation *)

    (** Between the two events of the empty branch the actor's session is
        already dead ([payload] drops it); the response only advances the
        clock (Section [Tick]). *)
    Section Emp.
      Variable s : @TryStackAuxState A.
      Variable α : tid.
      Variable start : TS.
      Variable H : history.
      Variable Δ Δ' : config.
      Hypothesis Hwf : ghost_wf s.
      Hypothesis Hlag : I_lag s Δ.
      Hypothesis Hcan : canonical s H.
      Hypothesis Hpop : I_pop s H Δ.
      Hypothesis HSnone : TMap.find α (tsa_snapshots s) = None.
      Hypothesis Hts : TMap.find α (tsa_pop_ts s) = Some start.
      Hypothesis Hall : tsa_all_vertices_garbage s.
      Hypothesis HΔ' : forall ρ' π', Δ' ρ' π' <->
        exists r π, Δ (DSReady r) π /\ TMap.find α π = Some pop_inv_token /\
          ρ' = DSReady r /\
          π' = TMap.add α pop_empty_token (TMap.add α pop_lini_token π).

      Local Notation s0 := (tsa_drop_session α s).

      Let Hwf0 : ghost_wf s0 := ghost_wf_drop_session s α Hwf HSnone.
      Let Hleg : legal s H := proj1 Hcan.

      Lemma em_session : session_open s α.
      Proof.
        destruct (gw_pop_ts s Hwf α start Hts) as (N0 & HN0). unfold session_open. congruence.
      Qed.

      Lemma em_session0 β : session_open s0 β <-> session_open s β /\ β <> α.
      Proof.
        unfold session_open. simpl. destruct (Pos.eq_dec β α) as [->|Hne].
        - rewrite TMap.grs. split; [intros Hc; exfalso; apply Hc; reflexivity|intros [_ Hc]; contradiction].
        - rewrite TMap.gro by exact Hne. tauto.
      Qed.

      Lemma em_enabled r π : lag s r π -> ds_all_vertices_garbage r.
      Proof.
        intros Hlg y. split.
        - intros Hvy. apply (lag_garbage_in _ _ _ Hlg). apply Hall. eapply lag_vertex; eauto.
        - intros Hg. exact (lag_garbage_vertex _ _ _ Hlg y Hg).
      Qed.

      Lemma em_no_push r π l :
        lag s r π -> TMap.find α π = Some pop_inv_token ->
        TMap.find α (tsa_pending_pushes s) = Some l -> False.
      Proof.
        intros Hlg Hπ Hl.
        assert (Hvs : tsa_is_vertex s (pair α l)) by (eapply gw_pending_vertex; eauto).
        destruct (classic (ds_is_vertex r (pair α l))) as [Hvx|Hnv].
        - unfold tsa_is_vertex in Hvs. destruct (tsa_vertices s (pair α l)) as [v'|] eqn:Hv'; [|contradiction].
          pose proof (lag_placed_pending _ _ _ Hlg α l v' Hl Hv' Hvx) as Hc. rewrite Hπ in Hc. discriminate.
        - destruct (lag_unplaced _ _ _ Hlg (pair α l) Hvs Hnv) as [_ (v' & _ & Hc') ].
          simpl in Hc'. rewrite Hπ in Hc'. discriminate.
      Qed.

      (** With every vertex removed, no plan speculates a pop. *)
      Lemma em_no_spec h β : legal s h -> ~ spec_pop_of h s β.
      Proof.
        intros Hl (n & p & Hn & HM).
        assert (Hv : tsa_is_vertex s n).
        { apply (legal_placed_vertex s h n Hwf Hl). apply (legal_popped_placed s h n Hl).
          unfold popped. rewrite Hn. discriminate. }
        apply Hall in Hv. apply (gw_garbage s Hwf) in Hv. exact (Hv HM).
      Qed.

      Lemma em_lag r π :
        lag s r π -> TMap.find α π = Some pop_inv_token ->
        lag s0 r (TMap.add α pop_empty_token (TMap.add α pop_lini_token π)).
      Proof.
        intros Hlg Hπ. constructor.
        - intros y v' Hy. exact (lag_vertices _ _ _ Hlg y v' Hy).
        - intros y Hvy Hnv. destruct (lag_unplaced _ _ _ Hlg y Hvy Hnv) as [Hp (v' & Hv' & Hπ') ].
          split; [exact Hp|]. exists v'. split; [exact Hv'|].
          assert (Hne : fst y <> α).
          { intro Heq. apply (em_no_push r π (snd y) Hlg Hπ). unfold tsa_is_pending in Hp. rewrite <- Heq. exact Hp. }
          rewrite find_add_add, TMap.gso by exact Hne. exact Hπ'.
        - intros β l' v' Hβ Hv' Hvy.
          assert (Hne : β <> α) by (intro; subst; exact (em_no_push r π l' Hlg Hπ Hβ)).
          rewrite find_add_add, TMap.gso by exact Hne. exact (lag_placed_pending _ _ _ Hlg β l' v' Hβ Hv' Hvy).
        - intros β l'. exact (lag_pending _ _ _ Hlg β l').
        - intros y z He Hvy Hvz. exact (lag_edges_in _ _ _ Hlg y z He Hvy Hvz).
        - intros y z He. exact (lag_edges_out _ _ _ Hlg y z He).
        - intros y Hg. exact (lag_garbage_in _ _ _ Hlg y Hg).
        - intros y Hg. exact (lag_garbage_vertex _ _ _ Hlg y Hg).
        - intros y Hg Hng.
          destruct (lag_spec_justified _ _ _ Hlg y Hg Hng) as (β & v' & HS' & Hv' & Hπ').
          assert (Hne : β <> α) by (intro; subst; rewrite Hπ in Hπ'; discriminate).
          exists β, v'. split; [apply em_session0; auto|]. split; [exact Hv'|].
          rewrite find_add_add, TMap.gso by exact Hne. exact Hπ'.
        - intros β v' y Hπ'. destruct (Pos.eq_dec β α) as [->|Hne].
          + rewrite find_add_add, TMap.gss in Hπ'.
            apply (f_equal (fun o => match o with Some ls => pop_result ls | None => None end)) in Hπ'.
            simpl in Hπ'. discriminate.
          + rewrite find_add_add, TMap.gso in Hπ' by exact Hne. exact (lag_succ_garbage _ _ _ Hlg β v' y Hπ').
      Qed.

      (** The abstract response is enabled in every retained possibility,
          so the enabledness side condition can be dropped from the
          paper's set comprehension. *)
      Lemma em_Δ'_paper_form (Δ0 : config) :
        (forall ρ' π', Δ0 ρ' π' <->
          exists r π, Δ (DSReady r) π /\ ds_all_vertices_garbage r /\
            TMap.find α π = Some pop_inv_token /\ ρ' = DSReady r /\
            π' = TMap.add α pop_empty_token (TMap.add α pop_lini_token π)) ->
        (forall ρ' π', Δ0 ρ' π' <->
          exists r π, Δ (DSReady r) π /\ TMap.find α π = Some pop_inv_token /\
            ρ' = DSReady r /\
            π' = TMap.add α pop_empty_token (TMap.add α pop_lini_token π)).
      Proof.
        intros Hiff ρ' π'. rewrite Hiff. split.
        - intros (r & π & Hposs & _ & Hπ & -> & ->). exists r, π. auto.
        - intros (r & π & Hposs & Hπ & -> & ->).
          destruct (Hlag _ _ Hposs) as (r0 & Heq & Hlg). injection Heq as <-.
          exists r, π. split; [exact Hposs|]. split; [eapply em_enabled; eauto|auto].
      Qed.

      Lemma em_I_lag : I_lag s0 Δ'.
      Proof.
        intros ρ' π' Hposs'. apply HΔ' in Hposs'. destruct Hposs' as (r & π & Hposs & Hπ & -> & ->).
        destruct (Hlag _ _ Hposs) as (r0 & Heq & Hlg). injection Heq as <-.
        exists r. split; [reflexivity|]. apply em_lag; assumption.
      Qed.

      Lemma em_H_canonical : canonical s0 H.
      Proof.
        pose proof Hcan as (Hleg0 & Hall0 & Hnospec & Hnnd).
        split; [|split; [|split] ].
        - constructor.
          + intros y p Hy. exact (lg_inv s H Hleg0 y p Hy).
          + intros y Hc. exact (lg_inv_all s H Hleg0 y Hc).
          + intros m p β Hm. destruct (lg_pop s H Hleg0 m p β Hm) as (Hgp & Hq & Hcase).
            split; [exact Hgp|]. split; [exact Hq|].
            destruct Hcase as [Hc| (HM & _) ]; [now left|].
            exfalso. apply (Hnospec m); [unfold popped; congruence|exact HM].
          + intros m HM. exact (lg_pop_all s H Hleg0 m HM).
          + apply (lg_spec s H Hleg0).
          + intros m p β y q Hm Hy Hlt Hab. exact (lg_top s H Hleg0 m p β y q Hm Hy Hlt Hab).
          + apply (lg_dist_inv s H Hleg0).
          + apply (lg_dist_pop s H Hleg0).
          + apply (lg_dist_mix s H Hleg0).
        - exact Hall0.
        - exact Hnospec.
        - exact Hnnd.
      Qed.

      Lemma em_plan_back h : plan s0 H h -> plan s H h.
      Proof.
        intros Hpl. pose proof (pl_legal _ _ _ Hpl) as Hl0.
        constructor.
        - constructor.
          + intros y p Hy. exact (lg_inv s0 h Hl0 y p Hy).
          + intros y Hc. exact (lg_inv_all s0 h Hl0 y Hc).
          + intros m p β Hm. destruct (lg_pop s0 h Hl0 m p β Hm) as (Hgp & Hq & Hcase).
            split; [exact Hgp|]. split; [exact Hq|].
            destruct Hcase as [Hc| (HM & σ & Hσ & Hlt) ]; [now left|].
            right. split; [exact HM|]. exists σ. split; [|exact Hlt].
            simpl in Hσ. destruct (Pos.eq_dec β α) as [->|Hne].
            * rewrite TMap.grs in Hσ. discriminate.
            * rewrite TMap.gro in Hσ by exact Hne. exact Hσ.
          + intros m HM. exact (lg_pop_all s0 h Hl0 m HM).
          + apply (lg_spec s0 h Hl0).
          + intros m p β y q Hm Hy Hlt Hab. exact (lg_top s0 h Hl0 m p β y q Hm Hy Hlt Hab).
          + apply (lg_dist_inv s0 h Hl0).
          + apply (lg_dist_pop s0 h Hl0).
          + apply (lg_dist_mix s0 h Hl0).
        - intros m HM. exact (pl_committed _ _ _ Hpl m HM).
        - intros y p Hy. exact (pl_later _ _ _ Hpl y p Hy).
      Qed.

      Lemma em_rep_state_fwd h r : rep_state s h r -> rep_state s0 h r.
      Proof.
        intros Hr. constructor.
        - intros y Hy. exact (rs_vertex_placed _ _ _ Hr y Hy).
        - intros y Hy. exact (rs_vertex_unplaced _ _ _ Hr y Hy).
        - intros y z. exact (rs_edges _ _ _ Hr y z).
        - intros β l'. exact (rs_pending _ _ _ Hr β l').
        - intros y. exact (rs_garbage _ _ _ Hr y).
      Qed.

      Lemma em_I_pop : I_pop s0 H Δ'.
      Proof.
        intros h Hpl. pose proof (em_plan_back h Hpl) as Hpl0.
        destruct (Hpop h Hpl0) as (r & π & Hposs & Hr & Hπ).
        destruct (Hlag _ _ Hposs) as (r0 & Heq & Hlg). injection Heq as <-.
        assert (Hπα : TMap.find α π = Some pop_inv_token).
        { apply (rt_pop_pending _ _ _ Hπ α em_session).
          apply em_no_spec. exact (pl_legal _ _ _ Hpl0). }
        exists r, (TMap.add α pop_empty_token (TMap.add α pop_lini_token π)).
        split; [apply HΔ'; exists r, π; auto|]. split; [apply em_rep_state_fwd; exact Hr|].
        constructor.
        - intros β l' v' Hβ Hv' Hnp.
          assert (Hne : β <> α) by (intro; subst; exact (em_no_push r π l' Hlg Hπα Hβ)).
          rewrite find_add_add, TMap.gso by exact Hne. exact (rt_push_unplaced _ _ _ Hπ β l' v' Hβ Hv' Hnp).
        - intros β l' v' Hβ Hv' Hpl'.
          assert (Hne : β <> α) by (intro; subst; exact (em_no_push r π l' Hlg Hπα Hβ)).
          rewrite find_add_add, TMap.gso by exact Hne. exact (rt_push_placed _ _ _ Hπ β l' v' Hβ Hv' Hpl').
        - intros β m p v' HS Hm HM Hv'. apply em_session0 in HS. destruct HS as [HS Hne].
          rewrite find_add_add, TMap.gso by exact Hne. exact (rt_pop_spec _ _ _ Hπ β m p v' HS Hm HM Hv').
        - intros β HS Hns. apply em_session0 in HS. destruct HS as [HS Hne].
          rewrite find_add_add, TMap.gso by exact Hne. exact (rt_pop_pending _ _ _ Hπ β HS Hns).
      Qed.

      Lemma em_I_state : I_state s0 Δ'.
      Proof.
        split; [exact Hwf0|]. split; [exact em_I_lag|].
        exists H. split; [exact em_H_canonical|exact em_I_pop].
      Qed.

    End Emp.

    (** * [⊨ I ∘ G_start-inv ⇒ I]: opening a session *)

    Section StartInv.
      Variable s : @TryStackAuxState A.
      Variable α : tid.
      Variable H : history.
      Variable Δ Δ' : config.
      Hypothesis Hwf : ghost_wf s.
      Hypothesis Hlag : I_lag s Δ.
      Hypothesis Hcan : canonical s H.
      Hypothesis Hpop : I_pop s H Δ.
      Hypothesis Hnosess : TMap.find α (tsa_session_time s) = None.
      Hypothesis Htok : forall ρ π, Δ ρ π -> TMap.find α π = Some pop_inv_token.
      Hypothesis HΔ' : forall ρ' π', Δ' ρ' π' <->
        exists ρ π, Δ ρ π /\ specS (TSAReady (tsa_start_pop_session α s)) ρ π ρ' π'.

      Local Notation s' := (tsa_start_pop_session α s).
      Local Notation t := (tsa_now s).

      Let Hwf' : ghost_wf s' := ghost_wf_start_pop_session s α Hwf Hnosess.
      Let Hleg : legal s H := proj1 Hcan.

      Lemma si_not_open : ~ session_open s α.
      Proof.
        intros Hopen. unfold session_open in Hopen.
        destruct (TMap.find α (tsa_pop_starts s)) as [N0|] eqn:HN0; [|congruence].
        destruct (gw_session s Hwf α N0 HN0) as (σ & Hσ & _). congruence.
      Qed.

      Lemma si_session_open β : session_open s β -> session_open s' β.
      Proof.
        unfold session_open. simpl. destruct (Pos.eq_dec β α) as [->|Hne].
        - rewrite TMap.gss. discriminate.
        - rewrite TMap.gso by exact Hne. tauto.
      Qed.

      Lemma si_session_time β σ :
        TMap.find β (tsa_session_time s') = Some σ ->
        (β = α /\ σ = t) \/ (β <> α /\ TMap.find β (tsa_session_time s) = Some σ).
      Proof.
        simpl. destruct (Pos.eq_dec β α) as [->|Hne].
        - rewrite TMap.gss. intros Heq. injection Heq as <-. now left.
        - rewrite TMap.gso by exact Hne. intros Hσ. now right.
      Qed.

      Lemma si_lag r π : lag s r π -> lag s' r π.
      Proof.
        intros Hlg. constructor.
        - intros y v' Hy. exact (lag_vertices _ _ _ Hlg y v' Hy).
        - intros y Hvy Hnv. exact (lag_unplaced _ _ _ Hlg y Hvy Hnv).
        - intros β l' v' Hβ Hv' Hvy. exact (lag_placed_pending _ _ _ Hlg β l' v' Hβ Hv' Hvy).
        - intros β l'. exact (lag_pending _ _ _ Hlg β l').
        - intros y z He Hvy Hvz. exact (lag_edges_in _ _ _ Hlg y z He Hvy Hvz).
        - intros y z He. exact (lag_edges_out _ _ _ Hlg y z He).
        - intros y Hg. exact (lag_garbage_in _ _ _ Hlg y Hg).
        - intros y Hg. exact (lag_garbage_vertex _ _ _ Hlg y Hg).
        - intros y Hg Hng.
          destruct (lag_spec_justified _ _ _ Hlg y Hg Hng) as (β & v' & HS' & Hv' & Hπ').
          exists β, v'. split; [apply si_session_open; exact HS'|auto].
        - intros β v' y Hπ'. exact (lag_succ_garbage _ _ _ Hlg β v' y Hπ').
      Qed.

      Lemma si_I_lag : I_lag s' Δ'.
      Proof.
        eapply I_lag_specS with (σ := TSAReady s') (Δ := Δ); [reflexivity|exact Hwf'| |exact HΔ'].
        intros ρ π Hposs. destruct (Hlag ρ π Hposs) as (r & -> & Hl). exists r. split; [reflexivity|].
        apply si_lag. exact Hl.
      Qed.

      Lemma si_H_canonical : canonical s' H.
      Proof.
        pose proof Hcan as (Hleg0 & Hall & Hnospec & Hnnd).
        split; [|split; [|split] ].
        - constructor.
          + intros y p Hy. destruct (lg_inv s H Hleg0 y p Hy) as (Hgp & Hi & Hret).
            split; [simpl; lia|]. split; [exact Hi|exact Hret].
          + intros y Hc. exact (lg_inv_all s H Hleg0 y Hc).
          + intros m p β Hm. destruct (lg_pop s H Hleg0 m p β Hm) as (Hgp & Hq & Hcase).
            split; [simpl; lia|]. split; [exact Hq|].
            destruct Hcase as [Hc| (HM & _) ]; [now left|].
            exfalso. apply (Hnospec m); [unfold popped; congruence|exact HM].
          + intros m HM. exact (lg_pop_all s H Hleg0 m HM).
          + apply (lg_spec s H Hleg0).
          + intros m p β y q Hm Hy Hlt Hab. exact (lg_top s H Hleg0 m p β y q Hm Hy Hlt Hab).
          + apply (lg_dist_inv s H Hleg0).
          + apply (lg_dist_pop s H Hleg0).
          + apply (lg_dist_mix s H Hleg0).
        - exact Hall.
        - exact Hnospec.
        - exact Hnnd.
      Qed.

      (** A plan of the new state, stripped of the new current gap, is a
          plan of the old state: the new session's speculated pops all lie
          in the new current gap. *)
      Lemma si_plan_back h :
        plan s' H h -> plan s H (strip h (S t)).
      Proof.
        intros Hpl.
        pose proof (strip_plan s' Hwf' H h Hpl) as Hpl'.
        pose proof (pl_legal _ _ _ Hpl') as Hl'.
        set (h0 := strip h (S t)) in *.
        assert (Hgap : forall y p, h_inv h0 y = Some p -> (gap p <= t)%nat).
        { intros y p Hy. apply strip_inv in Hy. destruct Hy as [Hy Hne].
          destruct (lg_inv s' h (pl_legal _ _ _ Hpl) y p Hy) as (Hgp & _). simpl in Hgp. lia. }
        assert (Hgapp : forall y p β, h_pop h0 y = Some (pair p β) -> (gap p <= t)%nat).
        { intros y p β Hy. apply strip_pop in Hy. destruct Hy as [Hy Hne].
          destruct (lg_pop s' h (pl_legal _ _ _ Hpl) y p β Hy) as (Hgp & _). simpl in Hgp. lia. }
        constructor.
        - constructor.
          + intros y p Hy. destruct (lg_inv s' h0 Hl' y p Hy) as (_ & Hi & Hret).
            split; [eauto|]. split; [exact Hi|exact Hret].
          + intros y Hc. exact (lg_inv_all s' h0 Hl' y Hc).
          + intros m p β Hm. destruct (lg_pop s' h0 Hl' m p β Hm) as (_ & Hq & Hcase).
            split; [eauto|]. split; [exact Hq|].
            destruct Hcase as [Hc| (HM & σ & Hσ & Hlt) ]; [now left|].
            right. split; [exact HM|].
            destruct (si_session_time β σ Hσ) as [ [-> ->]|[Hne Hσ0] ].
            * exfalso. specialize (Hgapp m p α Hm). lia.
            * exists σ. auto.
          + intros m HM. exact (lg_pop_all s' h0 Hl' m HM).
          + apply (lg_spec s' h0 Hl').
          + intros m p β y q Hm Hy Hlt Hab. exact (lg_top s' h0 Hl' m p β y q Hm Hy Hlt Hab).
          + apply (lg_dist_inv s' h0 Hl').
          + apply (lg_dist_pop s' h0 Hl').
          + apply (lg_dist_mix s' h0 Hl').
        - intros m HM. exact (pl_committed _ _ _ Hpl' m HM).
        - intros y p Hy. exact (pl_later _ _ _ Hpl' y p Hy).
      Qed.

      Lemma si_rep_state_fwd h r : rep_state s h r -> rep_state s' h r.
      Proof.
        intros Hr. constructor.
        - intros y Hy. exact (rs_vertex_placed _ _ _ Hr y Hy).
        - intros y Hy. exact (rs_vertex_unplaced _ _ _ Hr y Hy).
        - intros y z. exact (rs_edges _ _ _ Hr y z).
        - intros β l'. exact (rs_pending _ _ _ Hr β l').
        - intros y. exact (rs_garbage _ _ _ Hr y).
      Qed.

      (** No plan of the old state speculates a pop by [α]. *)
      Lemma si_no_spec h : legal s h -> ~ spec_pop_of h s α.
      Proof.
        intros Hl (n & p & Hn & HM).
        destruct (lg_pop s h Hl n p α Hn) as (_ & _ & [ (σ & rt & HM' & _)| (_ & σ & Hσ & _) ]).
        - congruence.
        - congruence.
      Qed.

      Lemma si_rep_tokens_fwd h π :
        legal s h -> TMap.find α π = Some pop_inv_token ->
        rep_tokens s h π -> rep_tokens s' h π.
      Proof.
        intros Hl Hπα Hπ. constructor.
        - intros β l' v' Hβ Hv' Hnp. exact (rt_push_unplaced _ _ _ Hπ β l' v' Hβ Hv' Hnp).
        - intros β l' v' Hβ Hv' Hpl. exact (rt_push_placed _ _ _ Hπ β l' v' Hβ Hv' Hpl).
        - intros β n p v' HS Hn HM Hv'.
          destruct (Pos.eq_dec β α) as [->|Hne].
          + exfalso. apply (si_no_spec h Hl). exists n, p. auto.
          + apply (rt_pop_spec _ _ _ Hπ β n p v'); [|exact Hn|exact HM|exact Hv'].
            unfold session_open in *. simpl in HS. rewrite TMap.gso in HS by exact Hne. exact HS.
        - intros β HS Hns.
          destruct (Pos.eq_dec β α) as [->|Hne]; [exact Hπα|].
          apply (rt_pop_pending _ _ _ Hπ β); [|exact Hns].
          unfold session_open in *. simpl in HS. rewrite TMap.gso in HS by exact Hne. exact HS.
      Qed.

      Lemma si_I_pop : I_pop s' H Δ'.
      Proof.
        intros h Hpl.
        pose proof (si_plan_back h Hpl) as Hpl0.
        destruct (Hpop _ Hpl0) as (r & π & Hposs & Hr & Hπ).
        pose proof (si_rep_state_fwd _ r Hr) as Hr'.
        pose proof (si_rep_tokens_fwd _ π (pl_legal _ _ _ Hpl0) (Htok _ _ Hposs) Hπ) as Hπ'.
        destruct (plans_reached s' (TSAReady s') eq_refl Hwf' H h Hpl r π Hr' Hπ')
          as (r' & π' & Hspec & Hr'' & Hπ'').
        exists r', π'. split; [|split; assumption].
        apply HΔ'. exists (DSReady r), π. split; assumption.
      Qed.

      Lemma si_I_state : I_state s' Δ'.
      Proof.
        split; [exact Hwf'|]. split; [exact si_I_lag|].
        exists H. split; [exact si_H_canonical|exact si_I_pop].
      Qed.

    End StartInv.

    (** * [⊨ I ∘ G_start-ret ⇒ I]: recording the token *)

    Section StartRet.
      Variable s : @TryStackAuxState A.
      Variables (α : tid) (ts : TS).
      Variable H : history.
      Variable Δ Δ'' Δ' : config.
      Hypothesis Hwf : ghost_wf s.
      Hypothesis Hlag : I_lag s Δ.
      Hypothesis Hcan : canonical s H.
      Hypothesis Hpop : I_pop s H Δ.
      Hypothesis Hopen : TMap.find α (tsa_pop_starts s) <> None.
      Hypothesis HΔ'' : forall ρ' π', Δ'' ρ' π' <->
        exists ρ π, Δ ρ π /\ specS (TSAReady s) ρ π ρ' π'.
      Hypothesis HΔ' : forall ρ' π', Δ' ρ' π' <->
        exists ρ π, Δ'' ρ π /\ specS (TSAReady (tsa_finish_pop_session α ts s)) ρ π ρ' π'.

      Local Notation s' := (tsa_finish_pop_session α ts s).
      Local Notation t := (tsa_now s).

      Let Hwf' : ghost_wf s' := ghost_wf_finish_pop_session s α ts Hwf Hopen.
      Let Hleg : legal s H := proj1 Hcan.

      (** Recording the token changes nothing the lag relation sees. *)
      Lemma sr_lag r π : lag s r π -> lag s' r π.
      Proof.
        intros Hlg. constructor.
        - intros y v' Hy. exact (lag_vertices _ _ _ Hlg y v' Hy).
        - intros y Hvy Hnv. exact (lag_unplaced _ _ _ Hlg y Hvy Hnv).
        - intros β l' v' Hβ Hv' Hvy. exact (lag_placed_pending _ _ _ Hlg β l' v' Hβ Hv' Hvy).
        - intros β l'. exact (lag_pending _ _ _ Hlg β l').
        - intros y z He Hvy Hvz. exact (lag_edges_in _ _ _ Hlg y z He Hvy Hvz).
        - intros y z He. exact (lag_edges_out _ _ _ Hlg y z He).
        - intros y Hg. exact (lag_garbage_in _ _ _ Hlg y Hg).
        - intros y Hg. exact (lag_garbage_vertex _ _ _ Hlg y Hg).
        - intros y Hg Hng.
          destruct (lag_spec_justified _ _ _ Hlg y Hg Hng) as (β & v' & HS' & Hv' & Hπ').
          exists β, v'. split; [exact HS'|auto].
        - intros β v' y Hπ'. exact (lag_succ_garbage _ _ _ Hlg β v' y Hπ').
      Qed.

      Lemma sr_I_lag : I_lag s' Δ'.
      Proof.
        eapply I_lag_specS with (σ := TSAReady s') (Δ := Δ''); [reflexivity|exact Hwf'| |exact HΔ'].
        intros ρ π Hposs. apply HΔ'' in Hposs. destruct Hposs as (ρ0 & π0 & Hposs0 & Hspec).
        destruct (specS_lag s (TSAReady s) ρ0 π0 ρ π eq_refl Hwf (Hlag _ _ Hposs0) Hspec) as (r & -> & Hlg).
        exists r. split; [reflexivity|]. apply sr_lag; assumption.
      Qed.

      Lemma sr_H_canonical : canonical s' H.
      Proof.
        pose proof Hcan as (Hleg0 & Hall & Hnospec & Hnnd).
        split; [|split; [|split] ].
        - constructor.
          + intros y p Hy. destruct (lg_inv s H Hleg0 y p Hy) as (Hgp & Hi & Hret).
            split; [simpl; lia|]. split; [exact Hi|exact Hret].
          + intros y Hc. exact (lg_inv_all s H Hleg0 y Hc).
          + intros m p β Hm. destruct (lg_pop s H Hleg0 m p β Hm) as (Hgp & Hq & Hcase).
            split; [simpl; lia|]. split; [exact Hq|exact Hcase].
          + intros m HM. exact (lg_pop_all s H Hleg0 m HM).
          + apply (lg_spec s H Hleg0).
          + intros m p β y q Hm Hy Hlt Hab. exact (lg_top s H Hleg0 m p β y q Hm Hy Hlt Hab).
          + apply (lg_dist_inv s H Hleg0).
          + apply (lg_dist_pop s H Hleg0).
          + apply (lg_dist_mix s H Hleg0).
        - exact Hall.
        - exact Hnospec.
        - exact Hnnd.
      Qed.

      Lemma sr_plan_back h :
        plan s' H h -> plan s H (strip h (S t)).
      Proof.
        intros Hpl.
        pose proof (strip_plan s' Hwf' H h Hpl) as Hpl'.
        pose proof (pl_legal _ _ _ Hpl') as Hl'.
        set (h0 := strip h (S t)) in *.
        assert (Hgap : forall y p, h_inv h0 y = Some p -> (gap p <= t)%nat).
        { intros y p Hy. apply strip_inv in Hy. destruct Hy as [Hy Hne].
          destruct (lg_inv s' h (pl_legal _ _ _ Hpl) y p Hy) as (Hgp & _). simpl in Hgp. lia. }
        assert (Hgapp : forall y p β, h_pop h0 y = Some (pair p β) -> (gap p <= t)%nat).
        { intros y p β Hy. apply strip_pop in Hy. destruct Hy as [Hy Hne].
          destruct (lg_pop s' h (pl_legal _ _ _ Hpl) y p β Hy) as (Hgp & _). simpl in Hgp. lia. }
        constructor.
        - constructor.
          + intros y p Hy. destruct (lg_inv s' h0 Hl' y p Hy) as (_ & Hi & Hret).
            split; [eauto|]. split; [exact Hi|exact Hret].
          + intros y Hc. exact (lg_inv_all s' h0 Hl' y Hc).
          + intros m p β Hm. destruct (lg_pop s' h0 Hl' m p β Hm) as (_ & Hq & Hcase).
            split; [eauto|]. split; [exact Hq|exact Hcase].
          + intros m HM. exact (lg_pop_all s' h0 Hl' m HM).
          + apply (lg_spec s' h0 Hl').
          + intros m p β y q Hm Hy Hlt Hab. exact (lg_top s' h0 Hl' m p β y q Hm Hy Hlt Hab).
          + apply (lg_dist_inv s' h0 Hl').
          + apply (lg_dist_pop s' h0 Hl').
          + apply (lg_dist_mix s' h0 Hl').
        - intros m HM. exact (pl_committed _ _ _ Hpl' m HM).
        - intros y p Hy. exact (pl_later _ _ _ Hpl' y p Hy).
      Qed.

      Lemma sr_rep_state_fwd h r : rep_state s h r -> rep_state s' h r.
      Proof.
        intros Hr. constructor.
        - intros y Hy. exact (rs_vertex_placed _ _ _ Hr y Hy).
        - intros y Hy. exact (rs_vertex_unplaced _ _ _ Hr y Hy).
        - intros y z. exact (rs_edges _ _ _ Hr y z).
        - intros β l'. exact (rs_pending _ _ _ Hr β l').
        - intros y. exact (rs_garbage _ _ _ Hr y).
      Qed.

      Lemma sr_rep_tokens_fwd h π :
        rep_tokens s h π -> rep_tokens s' h π.
      Proof.
        intros Hπ. constructor.
        - intros β l' v' Hβ Hv' Hnp. exact (rt_push_unplaced _ _ _ Hπ β l' v' Hβ Hv' Hnp).
        - intros β l' v' Hβ Hv' Hpl. exact (rt_push_placed _ _ _ Hπ β l' v' Hβ Hv' Hpl).
        - intros β m p v' HS' Hm HM Hv'. exact (rt_pop_spec _ _ _ Hπ β m p v' HS' Hm HM Hv').
        - intros β HS' Hns. exact (rt_pop_pending _ _ _ Hπ β HS' Hns).
      Qed.

      Lemma sr_I_pop : I_pop s' H Δ'.
      Proof.
        intros h Hpl.
        pose proof (sr_plan_back h Hpl) as Hpl0.
        destruct (Hpop _ Hpl0) as (r & π & Hposs & Hr & Hπ).
        pose proof (sr_rep_state_fwd _ r Hr) as Hr'.
        pose proof (sr_rep_tokens_fwd _ π Hπ) as Hπ'.
        destruct (plans_reached s' (TSAReady s') eq_refl Hwf' H h Hpl _ _ Hr' Hπ')
          as (r' & π' & Hspec & Hr'' & Hπ'').
        exists r', π'. split; [|split; assumption].
        apply HΔ'. exists (DSReady r), π. split; [|exact Hspec].
        apply HΔ''. exists (DSReady r), π. split; [exact Hposs|constructor].
      Qed.

      Lemma sr_I_state : I_state s' Δ'.
      Proof.
        split; [exact Hwf'|]. split; [exact sr_I_lag|].
        exists H. split; [exact sr_H_canonical|exact sr_I_pop].
      Qed.

    End StartRet.

    (** * [⊨ I ∘ G_emp-ret ⇒ I]: the clock advances *)

    Section Tick.
      Variable s : @TryStackAuxState A.
      Variable H : history.
      Variable Δ Δ' : config.
      Hypothesis Hwf : ghost_wf s.
      Hypothesis Hlag : I_lag s Δ.
      Hypothesis Hcan : canonical s H.
      Hypothesis Hpop : I_pop s H Δ.
      Hypothesis HΔ' : forall ρ' π', Δ' ρ' π' <->
        exists ρ π, Δ ρ π /\ specS (TSAReady (tsa_tick s)) ρ π ρ' π'.

      Local Notation s' := (tsa_tick s).
      Local Notation t := (tsa_now s).

      Let Hwf' : ghost_wf s' := ghost_wf_tick s Hwf.
      Let Hleg : legal s H := proj1 Hcan.

      (** Advancing the clock changes nothing the lag relation sees. *)
      Lemma tk_lag r π : lag s r π -> lag s' r π.
      Proof.
        intros Hlg. constructor.
        - intros y v' Hy. exact (lag_vertices _ _ _ Hlg y v' Hy).
        - intros y Hvy Hnv. exact (lag_unplaced _ _ _ Hlg y Hvy Hnv).
        - intros β l' v' Hβ Hv' Hvy. exact (lag_placed_pending _ _ _ Hlg β l' v' Hβ Hv' Hvy).
        - intros β l'. exact (lag_pending _ _ _ Hlg β l').
        - intros y z He Hvy Hvz. exact (lag_edges_in _ _ _ Hlg y z He Hvy Hvz).
        - intros y z He. exact (lag_edges_out _ _ _ Hlg y z He).
        - intros y Hg. exact (lag_garbage_in _ _ _ Hlg y Hg).
        - intros y Hg. exact (lag_garbage_vertex _ _ _ Hlg y Hg).
        - intros y Hg Hng.
          destruct (lag_spec_justified _ _ _ Hlg y Hg Hng) as (β & v' & HS' & Hv' & Hπ').
          exists β, v'. split; [exact HS'|auto].
        - intros β v' y Hπ'. exact (lag_succ_garbage _ _ _ Hlg β v' y Hπ').
      Qed.

      Lemma tk_I_lag : I_lag s' Δ'.
      Proof.
        eapply I_lag_specS with (σ := TSAReady s') (Δ := Δ); [reflexivity|exact Hwf'| |exact HΔ'].
        intros ρ π Hposs. destruct (Hlag _ _ Hposs) as (r & -> & Hlg).
        exists r. split; [reflexivity|]. apply tk_lag; assumption.
      Qed.

      Lemma tk_H_canonical : canonical s' H.
      Proof.
        pose proof Hcan as (Hleg0 & Hall & Hnospec & Hnnd).
        split; [|split; [|split] ].
        - constructor.
          + intros y p Hy. destruct (lg_inv s H Hleg0 y p Hy) as (Hgp & Hi & Hret).
            split; [simpl; lia|]. split; [exact Hi|exact Hret].
          + intros y Hc. exact (lg_inv_all s H Hleg0 y Hc).
          + intros m p β Hm. destruct (lg_pop s H Hleg0 m p β Hm) as (Hgp & Hq & Hcase).
            split; [simpl; lia|]. split; [exact Hq|exact Hcase].
          + intros m HM. exact (lg_pop_all s H Hleg0 m HM).
          + apply (lg_spec s H Hleg0).
          + intros m p β y q Hm Hy Hlt Hab. exact (lg_top s H Hleg0 m p β y q Hm Hy Hlt Hab).
          + apply (lg_dist_inv s H Hleg0).
          + apply (lg_dist_pop s H Hleg0).
          + apply (lg_dist_mix s H Hleg0).
        - exact Hall.
        - exact Hnospec.
        - exact Hnnd.
      Qed.

      Lemma tk_plan_back h :
        plan s' H h -> plan s H (strip h (S t)).
      Proof.
        intros Hpl.
        pose proof (strip_plan s' Hwf' H h Hpl) as Hpl'.
        pose proof (pl_legal _ _ _ Hpl') as Hl'.
        set (h0 := strip h (S t)) in *.
        assert (Hgap : forall y p, h_inv h0 y = Some p -> (gap p <= t)%nat).
        { intros y p Hy. apply strip_inv in Hy. destruct Hy as [Hy Hne].
          destruct (lg_inv s' h (pl_legal _ _ _ Hpl) y p Hy) as (Hgp & _). simpl in Hgp. lia. }
        assert (Hgapp : forall y p β, h_pop h0 y = Some (pair p β) -> (gap p <= t)%nat).
        { intros y p β Hy. apply strip_pop in Hy. destruct Hy as [Hy Hne].
          destruct (lg_pop s' h (pl_legal _ _ _ Hpl) y p β Hy) as (Hgp & _). simpl in Hgp. lia. }
        constructor.
        - constructor.
          + intros y p Hy. destruct (lg_inv s' h0 Hl' y p Hy) as (_ & Hi & Hret).
            split; [eauto|]. split; [exact Hi|exact Hret].
          + intros y Hc. exact (lg_inv_all s' h0 Hl' y Hc).
          + intros m p β Hm. destruct (lg_pop s' h0 Hl' m p β Hm) as (_ & Hq & Hcase).
            split; [eauto|]. split; [exact Hq|exact Hcase].
          + intros m HM. exact (lg_pop_all s' h0 Hl' m HM).
          + apply (lg_spec s' h0 Hl').
          + intros m p β y q Hm Hy Hlt Hab. exact (lg_top s' h0 Hl' m p β y q Hm Hy Hlt Hab).
          + apply (lg_dist_inv s' h0 Hl').
          + apply (lg_dist_pop s' h0 Hl').
          + apply (lg_dist_mix s' h0 Hl').
        - intros m HM. exact (pl_committed _ _ _ Hpl' m HM).
        - intros y p Hy. exact (pl_later _ _ _ Hpl' y p Hy).
      Qed.

      Lemma tk_rep_state_fwd h r : rep_state s h r -> rep_state s' h r.
      Proof.
        intros Hr. constructor.
        - intros y Hy. exact (rs_vertex_placed _ _ _ Hr y Hy).
        - intros y Hy. exact (rs_vertex_unplaced _ _ _ Hr y Hy).
        - intros y z. exact (rs_edges _ _ _ Hr y z).
        - intros β l'. exact (rs_pending _ _ _ Hr β l').
        - intros y. exact (rs_garbage _ _ _ Hr y).
      Qed.

      Lemma tk_rep_tokens_fwd h π :
        rep_tokens s h π -> rep_tokens s' h π.
      Proof.
        intros Hπ. constructor.
        - intros β l' v' Hβ Hv' Hnp. exact (rt_push_unplaced _ _ _ Hπ β l' v' Hβ Hv' Hnp).
        - intros β l' v' Hβ Hv' Hpl. exact (rt_push_placed _ _ _ Hπ β l' v' Hβ Hv' Hpl).
        - intros β m p v' HS' Hm HM Hv'. exact (rt_pop_spec _ _ _ Hπ β m p v' HS' Hm HM Hv').
        - intros β HS' Hns. exact (rt_pop_pending _ _ _ Hπ β HS' Hns).
      Qed.

      Lemma tk_I_pop : I_pop s' H Δ'.
      Proof.
        intros h Hpl.
        pose proof (tk_plan_back h Hpl) as Hpl0.
        destruct (Hpop _ Hpl0) as (r & π & Hposs & Hr & Hπ).
        pose proof (tk_rep_state_fwd _ r Hr) as Hr'.
        pose proof (tk_rep_tokens_fwd _ π Hπ) as Hπ'.
        destruct (plans_reached s' (TSAReady s') eq_refl Hwf' H h Hpl _ _ Hr' Hπ')
          as (r' & π' & Hspec & Hr'' & Hπ'').
        exists r', π'. split; [|split; assumption].
        apply HΔ'. exists (DSReady r), π. split; [exact Hposs|exact Hspec].
      Qed.

      Lemma tk_I_state : I_state s' Δ'.
      Proof.
        split; [exact Hwf'|]. split; [exact tk_I_lag|].
        exists H. split; [exact tk_H_canonical|exact tk_I_pop].
      Qed.

    End Tick.

    (** * [⊨ I ∘ G_rmv ⇒ I] *)

    Section Rmv.
      Variable s : @TryStackAuxState A.
      Variables (α : tid) (N : LPNodeSet) (σ : nat) (n : LPNodeId) (v : A).
      Variable H H' : history.
      Variable P : Pos.
      Variable Δ Δ'' Δ3 Δ' : config.
      Hypothesis Hwf : ghost_wf s.
      Hypothesis Hlag : I_lag s Δ.
      Hypothesis Hcan : canonical s H.
      Hypothesis Hpop : I_pop s H Δ.
      Hypothesis HS : TMap.find α (tsa_snapshots s) = Some N.
      Hypothesis Hσ : TMap.find α (tsa_session_time s) = Some σ.
      Hypothesis Hcase : removal_case s α N n.
      Hypothesis Hv : tsa_vertices s n = Some v.
      (** The output of Lemma A.1. *)
      Hypothesis HcanH' : canonical (tsa_remove_node α n s) H'.
      Hypothesis Hc : forall m, tsa_removals s m <> None -> h_pop H' m = h_pop H m.
      Hypothesis Hd : forall x p, h_inv H x = Some p -> exists p', h_inv H' x = Some p' /\ ple p p'.
      Hypothesis HPn : h_pop H' n = Some (pair P α).
      Hypothesis HPσ : (σ < gap P)%nat.
      Hypothesis HPt : (gap P <= tsa_now s)%nat.
      Hypothesis HΔ'' : forall ρ' π', Δ'' ρ' π' <->
        exists ρ π, Δ ρ π /\ specS (TSAReady s) ρ π ρ' π'.
      Hypothesis HΔ3 : forall ρ' π', Δ3 ρ' π' <->
        Δ'' ρ' π' /\ TMap.find α π' = Some (pop_succ_token v n).
      Hypothesis HΔ' : forall ρ' π', Δ' ρ' π' <->
        exists ρ π, Δ3 ρ π /\ specS (TSAReady (tsa_remove_node α n s)) ρ π ρ' π'.

      Local Notation s' := (tsa_remove_node α n s).
      Local Notation t := (tsa_now s).

      Lemma rm_n_vertex : tsa_is_vertex s n.
      Proof.
        destruct Hcase as [Htop| [Hlive _] ]; [|exact (proj1 Hlive) ].
        eapply gw_snapshot_vertex; eauto. exact (proj1 (proj1 Htop)).
      Qed.

      Lemma rm_n_not_garbage : ~ tsa_garbage s n.
      Proof.
        destruct Hcase as [Htop| [Hlive _] ]; [exact (proj2 (proj1 Htop))|exact (proj2 Hlive) ].
      Qed.

      Let Hwf' : ghost_wf s' :=
        ghost_wf_remove_node s α N n Hwf HS rm_n_vertex rm_n_not_garbage.
      Let Hleg : legal s H := proj1 Hcan.

      Lemma rm_session : session_open s α.
      Proof.
        destruct (gw_session_time s Hwf α σ Hσ) as (N0 & HN0). unfold session_open. congruence.
      Qed.

      Lemma rm_n_no_removal : tsa_removals s n = None.
      Proof.
        destruct (tsa_removals s n) eqn:HM; [|reflexivity]. exfalso.
        apply rm_n_not_garbage. apply (gw_garbage s Hwf). congruence.
      Qed.

      Lemma rm_rem_find m :
        tsa_removals s' m =
        if node_eq_dec n m then Some (pair (pair α σ) t) else tsa_removals s m.
      Proof. unfold tsa_remove_node. simpl. rewrite Hσ. reflexivity. Qed.

      Lemma rm_session_find β :
        TMap.find β (tsa_session_time s') =
        if Pos.eq_dec β α then None else TMap.find β (tsa_session_time s).
      Proof.
        simpl. destruct (Pos.eq_dec β α) as [->|Hne]; [apply TMap.grs|apply TMap.gro; congruence].
      Qed.

      Lemma rm_session_open β : session_open s' β <-> session_open s β /\ β <> α.
      Proof.
        unfold session_open. simpl. destruct (Pos.eq_dec β α) as [->|Hne].
        - rewrite TMap.grs. split; [intros Hx; exfalso; apply Hx; reflexivity|intros [_ Hx]; contradiction].
        - rewrite TMap.gro by exact Hne. tauto.
      Qed.

      Lemma rm_snap_find β :
        TMap.find β (tsa_snapshots s') =
        if Pos.eq_dec β α then None else TMap.find β (tsa_snapshots s).
      Proof.
        simpl. destruct (Pos.eq_dec β α) as [->|Hne]; [apply TMap.grs|apply TMap.gro; congruence].
      Qed.

      Lemma rm_time_find β :
        TMap.find β (tsa_snap_time s') =
        if Pos.eq_dec β α then None else TMap.find β (tsa_snap_time s).
      Proof.
        simpl. destruct (Pos.eq_dec β α) as [->|Hne]; [apply TMap.grs|apply TMap.gro; congruence].
      Qed.

      Lemma rm_garbage m : tsa_garbage s' m <-> m = n \/ tsa_garbage s m.
      Proof. reflexivity. Qed.

      Lemma rm_lag r π :
        lag s r π -> TMap.find α π = Some (pop_succ_token v n) -> lag s' r π.
      Proof.
        intros Hlg Hπ. constructor.
        - intros y v' Hy. exact (lag_vertices _ _ _ Hlg y v' Hy).
        - intros y Hvy Hnv. exact (lag_unplaced _ _ _ Hlg y Hvy Hnv).
        - intros β l' v' Hβ Hv' Hvy. exact (lag_placed_pending _ _ _ Hlg β l' v' Hβ Hv' Hvy).
        - intros β l'. exact (lag_pending _ _ _ Hlg β l').
        - intros y z He Hvy Hvz. exact (lag_edges_in _ _ _ Hlg y z He Hvy Hvz).
        - intros y z He. exact (lag_edges_out _ _ _ Hlg y z He).
        - intros y Hg. apply rm_garbage in Hg. destruct Hg as [->|Hg].
          + exact (lag_succ_garbage _ _ _ Hlg α v n Hπ).
          + exact (lag_garbage_in _ _ _ Hlg y Hg).
        - intros y Hg. exact (lag_garbage_vertex _ _ _ Hlg y Hg).
        - intros y Hg Hng.
          assert (Hng0 : ~ tsa_garbage s y) by (intro Hc0; apply Hng; apply rm_garbage; now right).
          assert (Hyn : y <> n) by (intro; subst y; apply Hng; apply rm_garbage; now left).
          destruct (lag_spec_justified _ _ _ Hlg y Hg Hng0) as (β & v' & HS' & Hv' & Hπ').
          exists β, v'. split; [|auto].
          assert (Hne : β <> α).
          { intro; subst β. rewrite Hπ in Hπ'. apply pop_succ_token_opt_inj in Hπ'.
            destruct Hπ' as [_ Heq]. exact (Hyn (eq_sym Heq)). }
          unfold session_open in *. simpl. rewrite TMap.gro by exact Hne. exact HS'.
        - intros β v' y Hπ'. exact (lag_succ_garbage _ _ _ Hlg β v' y Hπ').
      Qed.

      Lemma rm_I_lag : I_lag s' Δ'.
      Proof.
        eapply I_lag_specS with (σ := TSAReady s') (Δ := Δ3); [reflexivity|exact Hwf'| |exact HΔ'].
        intros ρ π Hposs. apply HΔ3 in Hposs. destruct Hposs as [Hposs Hπ].
        apply HΔ'' in Hposs. destruct Hposs as (ρ0 & π0 & Hposs0 & Hspec).
        destruct (specS_lag s (TSAReady s) ρ0 π0 ρ π eq_refl Hwf (Hlag _ _ Hposs0) Hspec) as (r & -> & Hlg).
        exists r. split; [reflexivity|]. apply rm_lag; assumption.
      Qed.

      (** Plans of the new state, stripped, are plans of the old state in
          which the pop of [n] is speculative. *)
      Lemma rm_plan_back h :
        plan s' H' h ->
        plan s H (strip h (S t)) /\
        h_pop (strip h (S t)) n = Some (pair P α).
      Proof.
        intros Hpl.
        pose proof (strip_plan s' Hwf' H' h Hpl) as Hpl'.
        pose proof (pl_legal _ _ _ Hpl') as Hl'.
        set (h0 := strip h (S t)) in *.
        assert (Hgap : forall y p, h_inv h0 y = Some p -> (gap p <= t)%nat).
        { intros y p Hy. apply strip_inv in Hy. destruct Hy as [Hy Hne].
          destruct (lg_inv s' h (pl_legal _ _ _ Hpl) y p Hy) as (Hgp & _). simpl in Hgp. lia. }
        assert (Hgapp : forall y p β, h_pop h0 y = Some (pair p β) -> (gap p <= t)%nat).
        { intros y p β Hy. apply strip_pop in Hy. destruct Hy as [Hy Hne].
          destruct (lg_pop s' h (pl_legal _ _ _ Hpl) y p β Hy) as (Hgp & _). simpl in Hgp. lia. }
        assert (HMn' : tsa_removals s' n <> None).
        { rewrite rm_rem_find. destruct (node_eq_dec n n); [discriminate|contradiction]. }
        assert (Hn0 : h_pop h0 n = Some (pair P α)).
        { exact (eq_trans (pl_committed _ _ _ Hpl' n HMn') HPn). }
        (* a speculative pop by [α] in [s] is the pop of [n] *)
        assert (Hspecα : forall m p, h_pop h0 m = Some (pair p α) ->
          tsa_removals s m = None -> m = n).
        { intros m p Hm HM. destruct (node_eq_dec m n) as [->|Hne]; [reflexivity|]. exfalso.
          destruct (lg_pop s' h0 Hl' m p α Hm) as (_ & _ & [ (st' & rt' & HM' & _)| (_ & σ' & Hσ' & _) ]).
          - rewrite rm_rem_find in HM'. destruct (node_eq_dec n m); [congruence|congruence].
          - rewrite rm_session_find in Hσ'. destruct (Pos.eq_dec α α); [discriminate|contradiction]. }
        split; [|exact Hn0].
        constructor.
        - constructor.
          + intros y p Hy. destruct (lg_inv s' h0 Hl' y p Hy) as (_ & Hi & Hret).
            split; [eauto|]. split; [exact Hi|exact Hret].
          + intros y Hcomp. exact (lg_inv_all s' h0 Hl' y Hcomp).
          + intros m p β Hm. destruct (lg_pop s' h0 Hl' m p β Hm) as (_ & Hq & Hpc).
            split; [eauto|]. split; [exact Hq|].
            destruct Hpc as [ (st' & rt' & HM' & Hlt & Hle)| (HM' & σ' & Hσ' & Hlt) ].
            * rewrite rm_rem_find in HM'. destruct (node_eq_dec n m) as [<-|Hne].
              -- injection HM' as <- <- <-. right. split; [exact rm_n_no_removal|].
                 exists σ. split; [exact Hσ|exact Hlt].
              -- left. exists st', rt'. auto.
            * rewrite rm_rem_find in HM'. destruct (node_eq_dec n m) as [<-|Hne]; [discriminate|].
              rewrite rm_session_find in Hσ'.
              destruct (Pos.eq_dec β α) as [->|Hne']; [discriminate|].
              right. split; [exact HM'|]. exists σ'. auto.
          + intros m HM. apply (lg_pop_all s' h0 Hl' m). rewrite rm_rem_find.
            destruct (node_eq_dec n m); [discriminate|exact HM].
          + intros m m' p q β Hm Hm' HM HM'.
            destruct (node_eq_dec m n) as [->|Hmn].
            * rewrite Hn0 in Hm. injection Hm as <- <-. symmetry. exact (Hspecα m' q Hm' HM').
            * destruct (node_eq_dec m' n) as [->|Hm'n].
              -- rewrite Hn0 in Hm'. injection Hm' as <- <-. exact (Hspecα m p Hm HM).
              -- apply (lg_spec s' h0 Hl' m m' p q β Hm Hm');
                   rewrite rm_rem_find; destruct (node_eq_dec n m); destruct (node_eq_dec n m'); congruence.
          + intros m p β y q Hm Hy Hlt Hab. exact (lg_top s' h0 Hl' m p β y q Hm Hy Hlt Hab).
          + apply (lg_dist_inv s' h0 Hl').
          + apply (lg_dist_pop s' h0 Hl').
          + apply (lg_dist_mix s' h0 Hl').
        - intros m HM. rewrite <- (Hc m HM). apply (pl_committed _ _ _ Hpl' m).
          rewrite rm_rem_find. destruct (node_eq_dec n m); [discriminate|exact HM].
        - intros y p Hy. destruct (pl_later _ _ _ Hpl' y p Hy) as (q & Hq & Hle).
          assert (Hvy : tsa_is_vertex s y).
          { pose proof (legal_placed_vertex s' H' y Hwf' (proj1 HcanH')) as Hvy.
            apply Hvy. unfold placed. congruence. }
          pose proof (proj1 (proj2 Hcan) y Hvy) as Hpl0. unfold placed in Hpl0.
          destruct (h_inv H y) as [q0|] eqn:Hq0; [|contradiction].
          destruct (Hd y q0 Hq0) as (q' & Hq' & Hle'). rewrite Hq in Hq'. injection Hq' as <-.
          exists q0. split; [reflexivity|]. eapply ple_trans; eauto.
      Qed.

      Lemma rm_rep_state_fwd h r : rep_state s h r -> rep_state s' h r.
      Proof.
        intros Hr. constructor.
        - intros y Hy. exact (rs_vertex_placed _ _ _ Hr y Hy).
        - intros y Hy. exact (rs_vertex_unplaced _ _ _ Hr y Hy).
        - intros y z. exact (rs_edges _ _ _ Hr y z).
        - intros β l'. exact (rs_pending _ _ _ Hr β l').
        - intros y. exact (rs_garbage _ _ _ Hr y).
      Qed.

      Lemma rm_rep_tokens_fwd h π :
        h_pop h n = Some (pair P α) ->
        rep_tokens s h π -> rep_tokens s' h π.
      Proof.
        intros Hn Hπ. constructor.
        - intros β l' v' Hβ Hv' Hnp. exact (rt_push_unplaced _ _ _ Hπ β l' v' Hβ Hv' Hnp).
        - intros β l' v' Hβ Hv' Hpl. exact (rt_push_placed _ _ _ Hπ β l' v' Hβ Hv' Hpl).
        - intros β m p v' HS' Hm HM Hv'. apply rm_session_open in HS'. destruct HS' as [HS' Hne].
          rewrite rm_rem_find in HM. destruct (node_eq_dec n m) as [<-|Hnm]; [discriminate|].
          exact (rt_pop_spec _ _ _ Hπ β m p v' HS' Hm HM Hv').
        - intros β HS' Hns. apply rm_session_open in HS'. destruct HS' as [HS' Hne].
          apply (rt_pop_pending _ _ _ Hπ β HS').
          intros (m & p & Hm & HM). apply Hns. exists m, p. split; [exact Hm|].
          rewrite rm_rem_find. destruct (node_eq_dec n m) as [<-|Hnm]; [|exact HM].
          rewrite Hn in Hm. injection Hm as _ Heq. congruence.
      Qed.

      Lemma rm_plan_to_Δ3 h :
        plan s H h -> h_pop h n = Some (pair P α) ->
        exists r π, Δ3 (DSReady r) π /\ rep_state s h r /\ rep_tokens s h π.
      Proof.
        intros Hpl Hn.
        pose proof (strip_plan s Hwf H h Hpl) as Hpl0.
        destruct (Hpop _ Hpl0) as (r0 & π0 & Hposs0 & Hr0 & Hπ0).
        destruct (plans_reached s (TSAReady s) eq_refl Hwf H h Hpl r0 π0 Hr0 Hπ0)
          as (r & π & Hspec & Hr & Hπ).
        exists r, π. split; [|split; assumption].
        apply HΔ3. split.
        - apply HΔ''. exists (DSReady r0), π0. split; assumption.
        - apply (rt_pop_spec _ _ _ Hπ α n P v); [exact rm_session|exact Hn|exact rm_n_no_removal|exact Hv].
      Qed.

      Lemma rm_filter_nonempty :
        exists r π, Δ'' (DSReady r) π /\ TMap.find α π = Some (pop_succ_token v n).
      Proof.
        assert (Hpl : plan s' H' H').
        { constructor; [exact (proj1 HcanH')|intros m _; reflexivity|].
          intros y p Hy. exists p. split; [exact Hy|apply ple_refl]. }
        destruct (rm_plan_back H' Hpl) as [Hpl0 Hn0].
        pose proof (strip_plan s Hwf H _ Hpl0) as Hpl1.
        destruct (Hpop _ Hpl1) as (r0 & π0 & Hposs0 & Hr0 & Hπ0).
        destruct (plans_reached s (TSAReady s) eq_refl Hwf H _ Hpl0 r0 π0 Hr0 Hπ0)
          as (r & π & Hspec & Hr & Hπ).
        exists r, π. split.
        - apply HΔ''. exists (DSReady r0), π0. split; assumption.
        - apply (rt_pop_spec _ _ _ Hπ α n P v); [exact rm_session|exact Hn0|exact rm_n_no_removal|exact Hv].
      Qed.

      Lemma rm_nonempty : exists r π, Δ3 (DSReady r) π.
      Proof.
        assert (Hpl : plan s' H' H').
        { constructor; [exact (proj1 HcanH')|intros m _; reflexivity|].
          intros y p Hy. exists p. split; [exact Hy|apply ple_refl]. }
        destruct (rm_plan_back H' Hpl) as [Hpl0 Hn0].
        destruct (rm_plan_to_Δ3 _ Hpl0 Hn0) as (r & π & Hposs & _). eauto.
      Qed.

      Lemma rm_I_pop : I_pop s' H' Δ'.
      Proof.
        intros h Hpl.
        destruct (rm_plan_back h Hpl) as [Hpl0 Hn0].
        destruct (rm_plan_to_Δ3 _ Hpl0 Hn0) as (r & π & Hposs & Hr & Hπ).
        pose proof (rm_rep_state_fwd _ r Hr) as Hr'.
        pose proof (rm_rep_tokens_fwd _ π Hn0 Hπ) as Hπ'.
        destruct (plans_reached s' (TSAReady s') eq_refl Hwf' H' h Hpl _ _ Hr' Hπ')
          as (r' & π' & Hspec & Hr'' & Hπ'').
        exists r', π'. split; [|split; assumption].
        apply HΔ'. exists (DSReady r), π. split; assumption.
      Qed.

      Lemma rm_I_state : I_state s' Δ'.
      Proof.
        split; [exact Hwf'|]. split; [exact rm_I_lag|].
        exists H'. split; [exact HcanH'|exact rm_I_pop].
      Qed.

    End Rmv.

    (** * The framework's invocation and return steps *)

    Lemma I_state_equiv s (Δ Δ' : config) :
      (forall ρ π, Δ ρ π <-> Δ' ρ π) -> I_state s Δ -> I_state s Δ'.
    Proof.
      intros Heq (Hwf & Hlag & H & Hcan & Hpop). split; [exact Hwf|]. split.
      - intros ρ π Hposs. apply Heq in Hposs. exact (Hlag ρ π Hposs).
      - exists H. split; [exact Hcan|]. intros h Hpl.
        destruct (Hpop h Hpl) as (r & π & Hposs & Hr & Hπ).
        exists r, π. split; [apply Heq; exact Hposs|auto].
    Qed.

    (** A thread without a token has neither a pending push nor an open
        session (hence no pending snapshot). *)
    Lemma tokenless_idle s (Δ : config) t :
      I_state s Δ ->
      (forall ρ π, Δ ρ π -> TMap.find t π = None) ->
      TMap.find t (tsa_pending_pushes s) = None /\ TMap.find t (tsa_pop_starts s) = None.
    Proof.
      intros (Hwf & Hlag & H & Hcan & Hpop) Hnone.
      assert (Hpl : plan s H H).
      { constructor; [exact (proj1 Hcan)|intros m _; reflexivity|].
        intros y p Hy. exists p. split; [exact Hy|apply ple_refl]. }
      destruct (Hpop H Hpl) as (r & π & Hposs & Hr & Hπ).
      pose proof (Hnone _ _ Hposs) as Ht.
      split.
      - destruct (TMap.find t (tsa_pending_pushes s)) as [l|] eqn:Hl; [|reflexivity]. exfalso.
        assert (Hv : tsa_is_vertex s (pair t l)) by (eapply gw_pending_vertex; eauto).
        unfold tsa_is_vertex in Hv. destruct (tsa_vertices s (pair t l)) as [v|] eqn:Hv'; [|contradiction].
        destruct (classic (placed H (pair t l))) as [Hp|Hnp].
        + rewrite (rt_push_placed _ _ _ Hπ t l v Hl Hv' Hp) in Ht. discriminate.
        + rewrite (rt_push_unplaced _ _ _ Hπ t l v Hl Hv' Hnp) in Ht. discriminate.
      - destruct (TMap.find t (tsa_pop_starts s)) as [N|] eqn:HS; [|reflexivity]. exfalso.
        assert (HS' : session_open s t) by (unfold session_open; congruence).
        destruct (classic (spec_pop_of H s t)) as [ (n & p & Hn & HM)|Hns].
        + exfalso. apply (proj1 (proj2 (proj2 Hcan)) n); [unfold popped; congruence|exact HM].
        + rewrite (rt_pop_pending _ _ _ Hπ t HS' Hns) in Ht. discriminate.
    Qed.

    Lemma no_session_no_snapshot s t :
      ghost_wf s -> TMap.find t (tsa_pop_starts s) = None ->
      TMap.find t (tsa_snapshots s) = None.
    Proof.
      intros Hwf HS. destruct (TMap.find t (tsa_snapshots s)) as [N|] eqn:HN; [|reflexivity].
      exfalso. destruct (gw_snap s Hwf t N HN) as (st & Hst & _).
      destruct (gw_snap_session s Hwf t st Hst) as (σ & Hσ & _).
      destruct (gw_session_time s Hwf t σ Hσ) as (N0 & HN0). congruence.
    Qed.

    Lemma lag_add_other s r π t ls :
      lag s r π ->
      TMap.find t (tsa_pending_pushes s) = None ->
      TMap.find t (tsa_pop_starts s) = None ->
      (forall v n, ls <> pop_succ_token v n) ->
      lag s r (TMap.add t ls π).
    Proof.
      intros Hlg HP HS Hls. constructor.
      - intros y v' Hy. exact (lag_vertices _ _ _ Hlg y v' Hy).
      - intros y Hvy Hnv. destruct (lag_unplaced _ _ _ Hlg y Hvy Hnv) as [Hp (v' & Hv' & Hπ') ].
        split; [exact Hp|]. exists v'. split; [exact Hv'|].
        assert (Hne : fst y <> t).
        { intro Heq. unfold tsa_is_pending in Hp. rewrite Heq, HP in Hp. discriminate. }
        rewrite TMap.gso by exact Hne. exact Hπ'.
      - intros β l' v' Hβ Hv' Hvy.
        assert (Hne : β <> t) by (intro; subst; congruence).
        rewrite TMap.gso by exact Hne. exact (lag_placed_pending _ _ _ Hlg β l' v' Hβ Hv' Hvy).
      - intros β l'. exact (lag_pending _ _ _ Hlg β l').
      - intros y z He Hvy Hvz. exact (lag_edges_in _ _ _ Hlg y z He Hvy Hvz).
      - intros y z He. exact (lag_edges_out _ _ _ Hlg y z He).
      - intros y Hg. exact (lag_garbage_in _ _ _ Hlg y Hg).
      - intros y Hg. exact (lag_garbage_vertex _ _ _ Hlg y Hg).
      - intros y Hg Hng.
        destruct (lag_spec_justified _ _ _ Hlg y Hg Hng) as (β & v' & HS' & Hv' & Hπ').
        exists β, v'. split; [exact HS'|]. split; [exact Hv'|].
        assert (Hne : β <> t) by (intro; subst; unfold session_open in HS'; congruence).
        rewrite TMap.gso by exact Hne. exact Hπ'.
      - intros β v' y Hπ'. destruct (Pos.eq_dec β t) as [->|Hne].
        + rewrite TMap.gss in Hπ'. injection Hπ' as Heq. exfalso. exact (Hls v' y Heq).
        + rewrite TMap.gso in Hπ' by exact Hne. exact (lag_succ_garbage _ _ _ Hlg β v' y Hπ').
    Qed.

    Lemma lag_remove_other s r π t :
      lag s r π ->
      TMap.find t (tsa_pending_pushes s) = None ->
      TMap.find t (tsa_pop_starts s) = None ->
      lag s r (TMap.remove t π).
    Proof.
      intros Hlg HP HS. constructor.
      - intros y v' Hy. exact (lag_vertices _ _ _ Hlg y v' Hy).
      - intros y Hvy Hnv. destruct (lag_unplaced _ _ _ Hlg y Hvy Hnv) as [Hp (v' & Hv' & Hπ') ].
        split; [exact Hp|]. exists v'. split; [exact Hv'|].
        assert (Hne : fst y <> t).
        { intro Heq. unfold tsa_is_pending in Hp. rewrite Heq, HP in Hp. discriminate. }
        rewrite TMap.gro by exact Hne. exact Hπ'.
      - intros β l' v' Hβ Hv' Hvy.
        assert (Hne : β <> t) by (intro; subst; congruence).
        rewrite TMap.gro by exact Hne. exact (lag_placed_pending _ _ _ Hlg β l' v' Hβ Hv' Hvy).
      - intros β l'. exact (lag_pending _ _ _ Hlg β l').
      - intros y z He Hvy Hvz. exact (lag_edges_in _ _ _ Hlg y z He Hvy Hvz).
      - intros y z He. exact (lag_edges_out _ _ _ Hlg y z He).
      - intros y Hg. exact (lag_garbage_in _ _ _ Hlg y Hg).
      - intros y Hg. exact (lag_garbage_vertex _ _ _ Hlg y Hg).
      - intros y Hg Hng.
        destruct (lag_spec_justified _ _ _ Hlg y Hg Hng) as (β & v' & HS' & Hv' & Hπ').
        exists β, v'. split; [exact HS'|]. split; [exact Hv'|].
        assert (Hne : β <> t) by (intro; subst; unfold session_open in HS'; congruence).
        rewrite TMap.gro by exact Hne. exact Hπ'.
      - intros β v' y Hπ'. destruct (Pos.eq_dec β t) as [->|Hne].
        + rewrite TMap.grs in Hπ'. discriminate.
        + rewrite TMap.gro in Hπ' by exact Hne. exact (lag_succ_garbage _ _ _ Hlg β v' y Hπ').
    Qed.

    Lemma rep_tokens_add_other s h π t ls :
      rep_tokens s h π ->
      TMap.find t (tsa_pending_pushes s) = None ->
      TMap.find t (tsa_pop_starts s) = None ->
      rep_tokens s h (TMap.add t ls π).
    Proof.
      intros Hπ HP HS. constructor.
      - intros β l' v' Hβ Hv' Hnp. assert (Hne : β <> t) by (intro; subst; congruence).
        rewrite TMap.gso by exact Hne. exact (rt_push_unplaced _ _ _ Hπ β l' v' Hβ Hv' Hnp).
      - intros β l' v' Hβ Hv' Hpl. assert (Hne : β <> t) by (intro; subst; congruence).
        rewrite TMap.gso by exact Hne. exact (rt_push_placed _ _ _ Hπ β l' v' Hβ Hv' Hpl).
      - intros β m p v' HS' Hm HM Hv'.
        assert (Hne : β <> t) by (intro; subst; unfold session_open in HS'; congruence).
        rewrite TMap.gso by exact Hne. exact (rt_pop_spec _ _ _ Hπ β m p v' HS' Hm HM Hv').
      - intros β HS' Hns.
        assert (Hne : β <> t) by (intro; subst; unfold session_open in HS'; congruence).
        rewrite TMap.gso by exact Hne. exact (rt_pop_pending _ _ _ Hπ β HS' Hns).
    Qed.

    Lemma rep_tokens_remove_other s h π t :
      rep_tokens s h π ->
      TMap.find t (tsa_pending_pushes s) = None ->
      TMap.find t (tsa_pop_starts s) = None ->
      rep_tokens s h (TMap.remove t π).
    Proof.
      intros Hπ HP HS. constructor.
      - intros β l' v' Hβ Hv' Hnp. assert (Hne : β <> t) by (intro; subst; congruence).
        rewrite TMap.gro by exact Hne. exact (rt_push_unplaced _ _ _ Hπ β l' v' Hβ Hv' Hnp).
      - intros β l' v' Hβ Hv' Hpl. assert (Hne : β <> t) by (intro; subst; congruence).
        rewrite TMap.gro by exact Hne. exact (rt_push_placed _ _ _ Hπ β l' v' Hβ Hv' Hpl).
      - intros β m p v' HS' Hm HM Hv'.
        assert (Hne : β <> t) by (intro; subst; unfold session_open in HS'; congruence).
        rewrite TMap.gro by exact Hne. exact (rt_pop_spec _ _ _ Hπ β m p v' HS' Hm HM Hv').
      - intros β HS' Hns.
        assert (Hne : β <> t) by (intro; subst; unfold session_open in HS'; congruence).
        rewrite TMap.gro by exact Hne. exact (rt_pop_pending _ _ _ Hπ β HS' Hns).
    Qed.

    Lemma ginv_I_state s (Δ : config) t (f : Sig.op (li_sig F)) :
      I_state s Δ ->
      (forall ρ π, Δ ρ π -> TMap.find t π = None) ->
      I_state s (ac_inv Δ t f).
    Proof.
      intros HI Hnone. destruct (tokenless_idle s Δ t HI Hnone) as [HP HS].
      destruct HI as (Hwf & Hlag & H & Hcan & Hpop). split; [exact Hwf|]. split.
      - intros ρ π Hposs. inversion Hposs; subst. destruct (Hlag _ _ Hposs0) as (r & -> & Hlg).
        exists r. split; [reflexivity|]. apply lag_add_other; auto. intros v n Hc. discriminate.
      - exists H. split; [exact Hcan|]. intros h Hpl.
        destruct (Hpop h Hpl) as (r & π & Hposs & Hr & Hπ).
        exists r, (TMap.add t (ls_inv f) π). split; [constructor; exact Hposs|]. split; [exact Hr|].
        apply rep_tokens_add_other; auto.
    Qed.

    Lemma gret_I_state s (Δ : config) t :
      I_state s Δ ->
      TMap.find t (tsa_pending_pushes s) = None ->
      TMap.find t (tsa_pop_starts s) = None ->
      I_state s (ac_res Δ t).
    Proof.
      intros (Hwf & Hlag & H & Hcan & Hpop) HP HS. split; [exact Hwf|]. split.
      - intros ρ π Hposs. inversion Hposs; subst. destruct (Hlag _ _ Hposs0) as (r & -> & Hlg).
        exists r. split; [reflexivity|]. apply lag_remove_other; auto.
      - exists H. split; [exact Hcan|]. intros h Hpl.
        destruct (Hpop h Hpl) as (r & π & Hposs & Hr & Hπ).
        exists r, (TMap.remove t π). split; [constructor; exact Hposs|]. split; [exact Hr|].
        apply rep_tokens_remove_other; auto.
    Qed.

    (** * Guarantees (the paper's relations with sessions, plus the
        framework steps) *)

    Definition spec_image (σ : concrete_state) (Δ Δ' : config) : Prop :=
      forall ρ' π', Δ' ρ' π' <-> exists ρ π, Δ ρ π /\ specS σ ρ π ρ' π'.

    Variant G_push_inv (α : tid) : rg_relation :=
    | g_push_inv s l v (w w' : proof_state) :
        SetPossState.σ w = TSAReady s ->
        TMap.find α (tsa_pending_pushes s) = None ->
        tsa_fresh_node s (pair α l) ->
        (forall ρ π, SetPossState.Δ w ρ π -> TMap.find α π = Some (push_inv_token v)) ->
        SetPossState.σ w' = TSAReady (tsa_start_push α l v s) ->
        spec_image (TSAReady (tsa_start_push α l v s)) (SetPossState.Δ w) (SetPossState.Δ w') ->
        G_push_inv α w w'.

    Variant G_push_ret (α : tid) : rg_relation :=
    | g_push_ret s l v (Δ'' Δ3 : config) (w w' : proof_state) :
        SetPossState.σ w = TSAReady s ->
        TMap.find α (tsa_pending_pushes s) = Some l ->
        tsa_vertices s (pair α l) = Some v ->
        SetPossState.σ w' = TSAReady (tsa_finish_push α s) ->
        spec_image (TSAReady s) (SetPossState.Δ w) Δ'' ->
        (forall ρ' π', Δ3 ρ' π' <->
          exists r l' π, Δ'' (DSReady r) π /\
            TMap.find α (ds_pending_pushes r) = Some l' /\
            TMap.find α π = Some (push_lini_token v) /\
            ρ' = DSReady (ds_finish_push α r) /\ π' = TMap.add α (push_ret_token v) π) ->
        spec_image (TSAReady (tsa_finish_push α s)) Δ3 (SetPossState.Δ w') ->
        G_push_ret α w w'.

    (** Opening a session: the actor has no session and holds [◦(pop)]
        everywhere. *)
    Variant G_start_inv (α : tid) : rg_relation :=
    | g_start_inv s (w w' : proof_state) :
        SetPossState.σ w = TSAReady s ->
        TMap.find α (tsa_session_time s) = None ->
        (forall ρ π, SetPossState.Δ w ρ π -> TMap.find α π = Some pop_inv_token) ->
        SetPossState.σ w' = TSAReady (tsa_start_pop_session α s) ->
        spec_image (TSAReady (tsa_start_pop_session α s)) (SetPossState.Δ w) (SetPossState.Δ w') ->
        G_start_inv α w w'.

    Variant G_start_ret (α : tid) : rg_relation :=
    | g_start_ret s ts (Δ'' : config) (w w' : proof_state) :
        SetPossState.σ w = TSAReady s ->
        TMap.find α (tsa_pop_starts s) <> None ->
        SetPossState.σ w' = TSAReady (tsa_finish_pop_session α ts s) ->
        spec_image (TSAReady s) (SetPossState.Δ w) Δ'' ->
        spec_image (TSAReady (tsa_finish_pop_session α ts s)) Δ'' (SetPossState.Δ w') ->
        G_start_ret α w w'.

    Variant G_snap (α : tid) : rg_relation :=
    | g_snap s start (w w' : proof_state) :
        SetPossState.σ w = TSAReady s ->
        TMap.find α (tsa_snapshots s) = None ->
        TMap.find α (tsa_pop_ts s) = Some start ->
        SetPossState.σ w' = TSAReady (tsa_start_snapshot α s) ->
        spec_image (TSAReady (tsa_start_snapshot α s)) (SetPossState.Δ w) (SetPossState.Δ w') ->
        G_snap α w w'.

    Variant G_rmv (α : tid) : rg_relation :=
    | g_rmv s N n v (Δ'' Δ3 : config) (w w' : proof_state) :
        SetPossState.σ w = TSAReady s ->
        TMap.find α (tsa_snapshots s) = Some N ->
        removal_case s α N n ->
        tsa_vertices s n = Some v ->
        SetPossState.σ w' = TSAReady (tsa_remove_node α n s) ->
        spec_image (TSAReady s) (SetPossState.Δ w) Δ'' ->
        (forall ρ' π', Δ3 ρ' π' <-> Δ'' ρ' π' /\ TMap.find α π' = Some (pop_succ_token v n)) ->
        spec_image (TSAReady (tsa_remove_node α n s)) Δ3 (SetPossState.Δ w') ->
        G_rmv α w w'.

    (** A failed retry linearizes nothing: no filter. *)
    Variant G_fail (α : tid) : rg_relation :=
    | g_fail s N (Δ'' : config) (w w' : proof_state) :
        SetPossState.σ w = TSAReady s ->
        TMap.find α (tsa_snapshots s) = Some N ->
        SetPossState.σ w' = TSAReady (tsa_clear_snapshot α s) ->
        spec_image (TSAReady s) (SetPossState.Δ w) Δ'' ->
        spec_image (TSAReady (tsa_clear_snapshot α s)) Δ'' (SetPossState.Δ w') ->
        G_fail α w w'.

    Variant G_emp (α : tid) : rg_relation :=
    | g_emp s start (w w' : proof_state) :
        SetPossState.σ w = TSAReady s ->
        TMap.find α (tsa_snapshots s) = None ->
        TMap.find α (tsa_pop_ts s) = Some start ->
        tsa_all_vertices_garbage s ->
        SetPossState.σ w' = TSAAtomicPending s α (tsa_trypop start) ->
        (forall ρ' π', SetPossState.Δ w' ρ' π' <->
          exists r π, SetPossState.Δ w (DSReady r) π /\ ds_all_vertices_garbage r /\
            TMap.find α π = Some pop_inv_token /\
            ρ' = DSReady r /\
            π' = TMap.add α pop_empty_token (TMap.add α pop_lini_token π)) ->
        G_emp α w w'
    | g_emp_ret s start (w w' : proof_state) :
        SetPossState.σ w = TSAAtomicPending s α (tsa_trypop start) ->
        SetPossState.σ w' = TSAReady (tsa_close_session α s) ->
        spec_image (TSAReady (tsa_close_session α s)) (SetPossState.Δ w) (SetPossState.Δ w') ->
        G_emp α w w'.

    Definition G (α : tid) : rg_relation :=
      fun w w' =>
        G_push_inv α w w' \/ G_push_ret α w w' \/
        G_start_inv α w w' \/ G_start_ret α w w' \/ G_snap α w w' \/
        G_rmv α w w' \/ G_fail α w w' \/ G_emp α w w'.

    Definition R (observer : tid) : rg_relation :=
      fun w w' =>
        (exists actor, actor <> observer /\ G actor w w') \/
        (exists actor, actor <> observer /\ GINV actor w w') \/
        (exists actor, actor <> observer /\ GRET actor w w') \/
        w = w'.

    (** * [⊨ I ∘ G ⇒ I] *)

    Lemma I_payload (w : proof_state) s : SetPossState.σ w = TSAReady s -> I w -> I_state s (SetPossState.Δ w).
    Proof. intros Hσ HI. unfold I, graph_of in HI. rewrite Hσ in HI. exact HI. Qed.

    Lemma I_payload_atomic (w : proof_state) s α op :
      SetPossState.σ w = TSAAtomicPending s α op -> I w ->
      I_state (tsa_drop_session α s) (SetPossState.Δ w).
    Proof. intros Hσ HI. unfold I, graph_of in HI. rewrite Hσ in HI. exact HI. Qed.

    Lemma no_session_no_time s t :
      ghost_wf s -> TMap.find t (tsa_pop_starts s) = None ->
      TMap.find t (tsa_session_time s) = None.
    Proof.
      intros Hwf HS. destruct (TMap.find t (tsa_session_time s)) as [σ|] eqn:Hσ; [|reflexivity].
      exfalso. destruct (gw_session_time s Hwf t σ Hσ) as (N0 & HN0). congruence.
    Qed.

    Lemma G_preserves_I α (w w' : proof_state) : G α w w' -> I w -> I w'.
    Proof.
      intros HG HI. unfold I, graph_of.
      destruct HG as [HG|[HG|[HG|[HG|[HG|[HG|[HG|HG] ] ] ] ] ] ].
      - destruct HG as [s l v w w' Hσ Hnone Hfresh Htok Hσ' HΔ'].
        pose proof (I_payload w s Hσ HI) as (Hwf & Hlag & H & Hcan & Hpop).
        rewrite Hσ'. simpl.
        exact (pi_I_state s α l v H _ _ Hwf Hlag Hcan Hpop Hnone Hfresh Htok HΔ').
      - destruct HG as [s l v Δ'' Δ3 w w' Hσ Hl Hv Hσ' HΔ'' HΔ3 HΔ'].
        pose proof (I_payload w s Hσ HI) as (Hwf & Hlag & H & Hcan & Hpop).
        rewrite Hσ'. simpl.
        assert (HΔ3' : forall ρ' π', Δ3 ρ' π' <->
          exists r π, Δ'' (DSReady r) π /\ TMap.find α π = Some (push_lini_token v) /\
            ρ' = DSReady (ds_finish_push α r) /\ π' = TMap.add α (push_ret_token v) π).
        { eapply pr_Δ3_paper_form; eauto. }
        exact (pr_I_state s α l v H _ Δ'' Δ3 _ Hwf Hlag Hcan Hpop Hl Hv HΔ'' HΔ3' HΔ').
      - destruct HG as [s w w' Hσ Hnosess Htok Hσ' HΔ'].
        pose proof (I_payload w s Hσ HI) as (Hwf & Hlag & H & Hcan & Hpop).
        rewrite Hσ'. simpl.
        exact (si_I_state s α H _ _ Hwf Hlag Hcan Hpop Hnosess Htok HΔ').
      - destruct HG as [s ts Δ'' w w' Hσ Hopen Hσ' HΔ'' HΔ'].
        pose proof (I_payload w s Hσ HI) as (Hwf & Hlag & H & Hcan & Hpop).
        rewrite Hσ'. simpl.
        exact (sr_I_state s α ts H _ Δ'' _ Hwf Hlag Hcan Hpop Hopen HΔ'' HΔ').
      - destruct HG as [s start w w' Hσ HSnone Hts Hσ' HΔ'].
        pose proof (I_payload w s Hσ HI) as (Hwf & Hlag & H & Hcan & Hpop).
        rewrite Hσ'. simpl.
        exact (sn_I_state s α H _ _ Hwf Hlag Hcan Hpop start HSnone Hts HΔ').
      - destruct HG as [s N n v Δ'' Δ3 w w' Hσ HS Hcase Hv Hσ' HΔ'' HΔ3 HΔ'].
        pose proof (I_payload w s Hσ HI) as (Hwf & Hlag & H & Hcan & Hpop).
        rewrite Hσ'. simpl.
        destruct (gw_snap s Hwf α N HS) as (st & Hst & _ & _).
        destruct (gw_snap_session s Hwf α st Hst) as (σ & Hσs & _).
        destruct (fs_insertion s H α N st σ n Hwf Hcan HS Hst Hσs Hcase)
          as (H' & P & HcanH' & Hc & Hd & HPn & HPσ & HPt).
        exact (rm_I_state s α N σ n v H H' P _ Δ'' Δ3 _ Hwf Hlag Hcan Hpop HS Hσs Hcase Hv
                 HcanH' Hc Hd HPn HPσ HPt HΔ'' HΔ3 HΔ').
      - destruct HG as [s N Δ'' w w' Hσ HS Hσ' HΔ'' HΔ'].
        pose proof (I_payload w s Hσ HI) as (Hwf & Hlag & H & Hcan & Hpop).
        rewrite Hσ'. simpl.
        exact (fl_I_state s α H _ Δ'' _ Hwf Hlag Hcan Hpop HΔ'' HΔ').
      - destruct HG as [s start w w' Hσ HSnone Hts Hall Hσ' HΔ'|s start w w' Hσ Hσ' HΔ'].
        + pose proof (I_payload w s Hσ HI) as (Hwf & Hlag & H & Hcan & Hpop).
          rewrite Hσ'. simpl.
          assert (HΔ'' : forall ρ' π', SetPossState.Δ w' ρ' π' <->
            exists r π, SetPossState.Δ w (DSReady r) π /\ TMap.find α π = Some pop_inv_token /\
              ρ' = DSReady r /\
              π' = TMap.add α pop_empty_token (TMap.add α pop_lini_token π)).
          { eapply em_Δ'_paper_form; eauto. }
          exact (em_I_state s α start H _ _ Hwf Hlag Hcan Hpop HSnone Hts Hall HΔ'').
        + pose proof (I_payload_atomic w s α (tsa_trypop start) Hσ HI) as (Hwf & Hlag & H & Hcan & Hpop).
          rewrite Hσ'. simpl. rewrite close_session_tick.
          exact (tk_I_state (tsa_drop_session α s) H _ _ Hwf Hlag Hcan Hpop HΔ').
    Qed.

    (** * What other threads' steps preserve *)

    (** A speculation step touches the token of [obs] only by placing its
        pending push or by speculating a pop in its open session; the
        latter turns [◦(pop)] into a success token and happens at most
        once along a chain. *)
    Lemma spec_step_find_other σ ρ π ρ' π' (obs : tid) :
      spec_step σ ρ π ρ' π' ->
      TMap.find obs (tsa_pending_pushes (payload σ)) = None ->
      TMap.find obs π' = TMap.find obs π \/
      (session_open (payload σ) obs /\ TMap.find obs π = Some pop_inv_token).
    Proof.
      intros [Hs|Hs] HP; inversion Hs; subst.
      - assert (Hne : obs <> β) by (intro; subst; congruence). left.
        rewrite TMap.gso by exact Hne. reflexivity.
      - destruct (Pos.eq_dec obs β) as [->|Hne].
        + right. split; assumption.
        + left. rewrite find_add_add, TMap.gso by exact Hne. reflexivity.
    Qed.

    Lemma specS_find_other σ ρ π ρ' π' (obs : tid) :
      specS σ ρ π ρ' π' ->
      TMap.find obs (tsa_pending_pushes (payload σ)) = None ->
      TMap.find obs π' = TMap.find obs π \/
      (session_open (payload σ) obs /\ TMap.find obs π = Some pop_inv_token).
    Proof.
      intros Hc HP. induction Hc as [|ρ π ρ1 π1 ρ2 π2 Hstep Hc IH]; [now left|].
      destruct (spec_step_find_other _ _ _ _ _ obs Hstep HP) as [Heq|[Hopen Htok]].
      - destruct IH as [Heq'|[Hopen Htok]].
        + left. congruence.
        + right. split; [exact Hopen|congruence].
      - right. split; assumption.
    Qed.

    Lemma specS_find_other_closed σ ρ π ρ' π' (obs : tid) :
      specS σ ρ π ρ' π' ->
      TMap.find obs (tsa_pending_pushes (payload σ)) = None ->
      TMap.find obs (tsa_pop_starts (payload σ)) = None ->
      TMap.find obs π' = TMap.find obs π.
    Proof.
      intros Hc HP HS. destruct (specS_find_other _ _ _ _ _ obs Hc HP) as [Heq|[Hopen _]].
      - exact Heq.
      - unfold session_open in Hopen. contradiction.
    Qed.

    Lemma spec_step_none_iff σ ρ π ρ' π' (obs : tid) :
      spec_step σ ρ π ρ' π' ->
      (TMap.find obs π = None <-> TMap.find obs π' = None).
    Proof.
      intros [Hs|Hs]; inversion Hs; subst.
      - destruct (Pos.eq_dec obs β) as [->|Hne].
        + rewrite TMap.gss. split; congruence.
        + rewrite TMap.gso by exact Hne. reflexivity.
      - destruct (Pos.eq_dec obs β) as [->|Hne].
        + rewrite find_add_add, TMap.gss. split; congruence.
        + rewrite find_add_add, TMap.gso by exact Hne. reflexivity.
    Qed.

    Lemma specS_none_iff σ ρ π ρ' π' (obs : tid) :
      specS σ ρ π ρ' π' ->
      (TMap.find obs π = None <-> TMap.find obs π' = None).
    Proof.
      intros Hc. induction Hc as [|ρ π ρ1 π1 ρ2 π2 Hstep Hc IH]; [reflexivity|].
      rewrite <- IH. eapply spec_step_none_iff; eauto.
    Qed.

    (** The facts about [obs] that every step of another thread preserves:
        its pending push, snapshot and session entries, the vertices, the
        atomic control it owns, and its tokens (which another thread can
        only change by speculating a pop of an open session). *)
    Definition other_facts (obs : tid) (w w' : proof_state) : Prop :=
      TMap.find obs (tsa_pending_pushes (graph_of w)) =
        TMap.find obs (tsa_pending_pushes (graph_of w')) /\
      TMap.find obs (tsa_snapshots (graph_of w)) =
        TMap.find obs (tsa_snapshots (graph_of w')) /\
      TMap.find obs (tsa_pop_starts (graph_of w)) =
        TMap.find obs (tsa_pop_starts (graph_of w')) /\
      TMap.find obs (tsa_pop_ts (graph_of w)) =
        TMap.find obs (tsa_pop_ts (graph_of w')) /\
      (forall n v, tsa_vertices (graph_of w) n = Some v ->
        tsa_vertices (graph_of w') n = Some v) /\
      ((exists s0 op, SetPossState.σ w = TSAAtomicPending s0 obs op) ->
        SetPossState.σ w' = SetPossState.σ w) /\
      (TMap.find obs (tsa_pending_pushes (graph_of w)) = None ->
        forall ρ' π', SetPossState.Δ w' ρ' π' ->
          exists ρ π, SetPossState.Δ w ρ π /\
            (TMap.find obs π' = TMap.find obs π \/
             (TMap.find obs (tsa_pop_starts (graph_of w)) <> None /\
              TMap.find obs π = Some pop_inv_token))) /\
      (exists ρ' π' ρ π,
        SetPossState.Δ w' ρ' π' /\ SetPossState.Δ w ρ π /\
        (TMap.find obs π = None <-> TMap.find obs π' = None)).

    Lemma some_none_iff (x y : lin_state) : Some x = None <-> Some y = None.
    Proof. split; discriminate. Qed.

    (** The token clause of [other_facts] for a configuration that is a
        speculation image, possibly after a filter and image step whose
        [obs]-token is untouched. *)
    Lemma spec_image_other_tokens (σ σ' : concrete_state) (Δ Δ' : config) obs :
      spec_image σ' Δ Δ' ->
      TMap.find obs (tsa_pending_pushes (payload σ')) = TMap.find obs (tsa_pending_pushes (payload σ)) ->
      TMap.find obs (tsa_pop_starts (payload σ')) = TMap.find obs (tsa_pop_starts (payload σ)) ->
      TMap.find obs (tsa_pending_pushes (payload σ)) = None ->
      forall ρ' π', Δ' ρ' π' ->
        exists ρ π, Δ ρ π /\
          (TMap.find obs π' = TMap.find obs π \/
           (TMap.find obs (tsa_pop_starts (payload σ)) <> None /\
            TMap.find obs π = Some pop_inv_token)).
    Proof.
      intros HΔ' HP Hsess HPnone ρ' π' Hposs'. apply HΔ' in Hposs'.
      destruct Hposs' as (ρ & π & Hposs & Hspec). exists ρ, π. split; [exact Hposs|].
      destruct (specS_find_other _ _ _ _ _ obs Hspec) as [Heq|[Hopen Htok]].
      - rewrite HP. exact HPnone.
      - now left.
      - right. unfold session_open in Hopen. rewrite Hsess in Hopen. auto.
    Qed.

    Lemma G_other_facts actor (w w' : proof_state) obs :
      obs <> actor -> G actor w w' -> other_facts obs w w'.
    Proof.
      intros Hneq HG.
      destruct HG as [HG|[HG|[HG|[HG|[HG|[HG|[HG|HG] ] ] ] ] ] ].
      - (* push-inv *)
        destruct HG as [s l v w w' Hσ Hnone Hfresh Htok Hσ' HΔ'].
        unfold other_facts, graph_of. rewrite Hσ, Hσ'. cbn [payload].
        assert (HP' : TMap.find obs (tsa_pending_pushes (tsa_start_push actor l v s)) =
          TMap.find obs (tsa_pending_pushes s)).
        { simpl. rewrite TMap.gso by congruence. reflexivity. }
        split; [symmetry; exact HP'|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split.
        { intros n v0 Hv0. simpl. rewrite node_update_neq; [exact Hv0|].
          intro Heq. subst n. destruct Hfresh as [Hn _]. congruence. }
        split; [intros [s0 [op Heq] ]; discriminate|]. split.
        + intros HP. eapply (spec_image_other_tokens (TSAReady s) (TSAReady (tsa_start_push actor l v s))); [exact HΔ'| | |exact HP].
          * simpl. rewrite TMap.gso by congruence. reflexivity.
          * reflexivity.
        + destruct (ac_nonempty (SetPossState.Δ w')) as (ρ' & π' & Hposs').
          pose proof Hposs' as Hposs''. apply HΔ' in Hposs''. destruct Hposs'' as (ρ & π & Hposs & Hspec).
          exists ρ', π', ρ, π. split; [exact Hposs'|]. split; [exact Hposs|].
          eapply specS_none_iff; eauto.
      - (* push-ret *)
        destruct HG as [s l v Δ'' Δ3 w w' Hσ Hl Hv Hσ' HΔ'' HΔ3 HΔ'].
        unfold other_facts, graph_of. rewrite Hσ, Hσ'. cbn [payload].
        assert (HP' : TMap.find obs (tsa_pending_pushes (tsa_finish_push actor s)) =
          TMap.find obs (tsa_pending_pushes s)).
        { simpl. rewrite TMap.gro by congruence. reflexivity. }
        split; [symmetry; exact HP'|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [intros n v0 Hv0; exact Hv0|].
        split; [intros [s0 [op Heq] ]; discriminate|]. split.
        + intros HP ρ' π' Hposs'. apply HΔ' in Hposs'. destruct Hposs' as (ρ3 & π3 & Hposs3 & Hspec3).
          apply HΔ3 in Hposs3. destruct Hposs3 as (r & l' & π2 & Hposs2 & _ & _ & -> & ->).
          apply HΔ'' in Hposs2. destruct Hposs2 as (ρ & π & Hposs & Hspec).
          exists ρ, π. split; [exact Hposs|].
          destruct (specS_find_other _ _ _ _ _ obs Hspec3) as [Heq3|[Hopen3 Htok3] ].
          { simpl. rewrite TMap.gro by congruence. exact HP. }
          * rewrite Heq3, TMap.gso by congruence.
            destruct (specS_find_other _ _ _ _ _ obs Hspec HP) as [Heq|[Hopen Htok] ].
            -- now left.
            -- right. split; [exact Hopen|exact Htok].
          * unfold session_open in Hopen3. simpl in Hopen3.
            rewrite TMap.gso in Htok3 by congruence.
            destruct (specS_find_other _ _ _ _ _ obs Hspec HP) as [Heq|[Hopen Htok] ].
            -- right. split; [exact Hopen3|congruence].
            -- right. split; [exact Hopen|exact Htok].
        + destruct (ac_nonempty (SetPossState.Δ w')) as (ρ' & π' & Hposs').
          pose proof Hposs' as Hposs''. apply HΔ' in Hposs''. destruct Hposs'' as (ρ3 & π3 & Hposs3 & Hspec3).
          apply HΔ3 in Hposs3. destruct Hposs3 as (r & l' & π2 & Hposs2 & _ & _ & -> & ->).
          apply HΔ'' in Hposs2. destruct Hposs2 as (ρ & π & Hposs & Hspec).
          exists ρ', π', ρ, π. split; [exact Hposs'|]. split; [exact Hposs|].
          rewrite <- (specS_none_iff _ _ _ _ _ obs Hspec3). rewrite TMap.gso by congruence.
          eapply specS_none_iff; eauto.
      - (* start-inv *)
        destruct HG as [s w w' Hσ Hnosess Htok Hσ' HΔ'].
        unfold other_facts, graph_of. rewrite Hσ, Hσ'. cbn [payload].
        split; [reflexivity|]. split; [reflexivity|].
        split; [simpl; rewrite TMap.gso by congruence; reflexivity|].
        split; [simpl; rewrite TMap.gro by congruence; reflexivity|].
        split; [intros n v0 Hv0; exact Hv0|].
        split; [intros [s0 [op Heq] ]; discriminate|]. split.
        + intros HP. eapply (spec_image_other_tokens (TSAReady s) (TSAReady (tsa_start_pop_session actor s))); [exact HΔ'| | |exact HP].
          * reflexivity.
          * simpl. rewrite TMap.gso by congruence. reflexivity.
        + destruct (ac_nonempty (SetPossState.Δ w')) as (ρ' & π' & Hposs').
          pose proof Hposs' as Hposs''. apply HΔ' in Hposs''. destruct Hposs'' as (ρ & π & Hposs & Hspec).
          exists ρ', π', ρ, π. split; [exact Hposs'|]. split; [exact Hposs|].
          eapply specS_none_iff; eauto.
      - (* start-ret *)
        destruct HG as [s ts Δ'' w w' Hσ Hopen0 Hσ' HΔ'' HΔ'].
        unfold other_facts, graph_of. rewrite Hσ, Hσ'. cbn [payload].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [simpl; rewrite TMap.gso by congruence; reflexivity|].
        split; [intros n v0 Hv0; exact Hv0|].
        split; [intros [s0 [op Heq] ]; discriminate|]. split.
        + intros HP ρ' π' Hposs'. apply HΔ' in Hposs'. destruct Hposs' as (ρ2 & π2 & Hposs2 & Hspec2).
          apply HΔ'' in Hposs2. destruct Hposs2 as (ρ & π & Hposs & Hspec).
          exists ρ, π. split; [exact Hposs|].
          destruct (specS_find_other _ _ _ _ _ obs Hspec2 HP) as [Heq2|[Hopen2 Htok2] ].
          * rewrite Heq2. exact (specS_find_other _ _ _ _ _ obs Hspec HP).
          * unfold session_open in Hopen2. simpl in Hopen2.
            destruct (specS_find_other _ _ _ _ _ obs Hspec HP) as [Heq|[Hopen Htok] ].
            -- right. split; [exact Hopen2|congruence].
            -- right. split; [exact Hopen|exact Htok].
        + destruct (ac_nonempty (SetPossState.Δ w')) as (ρ' & π' & Hposs').
          pose proof Hposs' as Hposs''. apply HΔ' in Hposs''. destruct Hposs'' as (ρ2 & π2 & Hposs2 & Hspec2).
          apply HΔ'' in Hposs2. destruct Hposs2 as (ρ & π & Hposs & Hspec).
          exists ρ', π', ρ, π. split; [exact Hposs'|]. split; [exact Hposs|].
          rewrite <- (specS_none_iff _ _ _ _ _ obs Hspec2). eapply specS_none_iff; eauto.
      - (* snap *)
        destruct HG as [s start w w' Hσ HSnone Hts Hσ' HΔ'].
        unfold other_facts, graph_of. rewrite Hσ, Hσ'. cbn [payload].
        assert (HS' : TMap.find obs (tsa_snapshots (tsa_start_snapshot actor s)) =
          TMap.find obs (tsa_snapshots s)).
        { simpl. rewrite TMap.gso by congruence. reflexivity. }
        split; [reflexivity|]. split; [symmetry; exact HS'|]. split; [reflexivity|]. split; [reflexivity|].
        split; [intros n v0 Hv0; exact Hv0|].
        split; [intros [s0 [op Heq] ]; discriminate|]. split.
        + intros HP. eapply (spec_image_other_tokens (TSAReady s) (TSAReady (tsa_start_snapshot actor s))); [exact HΔ'| | |exact HP]; reflexivity.
        + destruct (ac_nonempty (SetPossState.Δ w')) as (ρ' & π' & Hposs').
          pose proof Hposs' as Hposs''. apply HΔ' in Hposs''. destruct Hposs'' as (ρ & π & Hposs & Hspec).
          exists ρ', π', ρ, π. split; [exact Hposs'|]. split; [exact Hposs|].
          eapply specS_none_iff; eauto.
      - (* rmv *)
        destruct HG as [s N n v Δ'' Δ3 w w' Hσ HS Hcase Hv Hσ' HΔ'' HΔ3 HΔ'].
        unfold other_facts, graph_of. rewrite Hσ, Hσ'. cbn [payload].
        split; [reflexivity|].
        split; [simpl; rewrite TMap.gro by congruence; reflexivity|].
        split; [simpl; rewrite TMap.gro by congruence; reflexivity|].
        split; [simpl; rewrite TMap.gro by congruence; reflexivity|].
        split; [intros m v0 Hv0; exact Hv0|].
        split; [intros [s0 [op Heq] ]; discriminate|]. split.
        + intros HP ρ' π' Hposs'. apply HΔ' in Hposs'. destruct Hposs' as (ρ3 & π3 & Hposs3 & Hspec3).
          apply HΔ3 in Hposs3. destruct Hposs3 as [Hposs2 _].
          apply HΔ'' in Hposs2. destruct Hposs2 as (ρ & π & Hposs & Hspec).
          exists ρ, π. split; [exact Hposs|].
          destruct (specS_find_other _ _ _ _ _ obs Hspec3 HP) as [Heq3|[Hopen3 Htok3] ].
          * rewrite Heq3. exact (specS_find_other _ _ _ _ _ obs Hspec HP).
          * unfold session_open in Hopen3. simpl in Hopen3. rewrite TMap.gro in Hopen3 by congruence.
            destruct (specS_find_other _ _ _ _ _ obs Hspec HP) as [Heq|[Hopen Htok] ].
            -- right. split; [exact Hopen3|congruence].
            -- right. split; [exact Hopen|exact Htok].
        + destruct (ac_nonempty (SetPossState.Δ w')) as (ρ' & π' & Hposs').
          pose proof Hposs' as Hposs''. apply HΔ' in Hposs''. destruct Hposs'' as (ρ3 & π3 & Hposs3 & Hspec3).
          apply HΔ3 in Hposs3. destruct Hposs3 as [Hposs2 _].
          apply HΔ'' in Hposs2. destruct Hposs2 as (ρ & π & Hposs & Hspec).
          exists ρ', π', ρ, π. split; [exact Hposs'|]. split; [exact Hposs|].
          rewrite <- (specS_none_iff _ _ _ _ _ obs Hspec3). eapply specS_none_iff; eauto.
      - (* fail *)
        destruct HG as [s N Δ'' w w' Hσ HS Hσ' HΔ'' HΔ'].
        unfold other_facts, graph_of. rewrite Hσ, Hσ'. cbn [payload].
        split; [reflexivity|].
        split; [simpl; rewrite TMap.gro by congruence; reflexivity|].
        split; [reflexivity|]. split; [reflexivity|].
        split; [intros m v0 Hv0; exact Hv0|].
        split; [intros [s0 [op Heq] ]; discriminate|]. split.
        + intros HP ρ' π' Hposs'. apply HΔ' in Hposs'. destruct Hposs' as (ρ2 & π2 & Hposs2 & Hspec2).
          apply HΔ'' in Hposs2. destruct Hposs2 as (ρ & π & Hposs & Hspec).
          exists ρ, π. split; [exact Hposs|].
          destruct (specS_find_other _ _ _ _ _ obs Hspec2 HP) as [Heq2|[Hopen2 Htok2] ].
          * rewrite Heq2. exact (specS_find_other _ _ _ _ _ obs Hspec HP).
          * unfold session_open in Hopen2. simpl in Hopen2.
            destruct (specS_find_other _ _ _ _ _ obs Hspec HP) as [Heq|[Hopen Htok] ].
            -- right. split; [exact Hopen2|congruence].
            -- right. split; [exact Hopen|exact Htok].
        + destruct (ac_nonempty (SetPossState.Δ w')) as (ρ' & π' & Hposs').
          pose proof Hposs' as Hposs''. apply HΔ' in Hposs''. destruct Hposs'' as (ρ2 & π2 & Hposs2 & Hspec2).
          apply HΔ'' in Hposs2. destruct Hposs2 as (ρ & π & Hposs & Hspec).
          exists ρ', π', ρ, π. split; [exact Hposs'|]. split; [exact Hposs|].
          rewrite <- (specS_none_iff _ _ _ _ _ obs Hspec2). eapply specS_none_iff; eauto.
      - (* emp *)
        destruct HG as [s start w w' Hσ HSnone Hts Hall Hσ' HΔ'|s start w w' Hσ Hσ' HΔ'].
        + unfold other_facts, graph_of. rewrite Hσ, Hσ'. cbn [payload].
          split; [reflexivity|]. split; [reflexivity|].
          split; [simpl; rewrite TMap.gro by congruence; reflexivity|].
          split; [simpl; rewrite TMap.gro by congruence; reflexivity|].
          split; [intros m v0 Hv0; exact Hv0|].
          split; [intros [s0 [op Heq] ]; discriminate|]. split.
          * intros _ ρ' π' Hposs'. apply HΔ' in Hposs'. destruct Hposs' as (r & π & Hposs & _ & _ & -> & ->).
            exists (DSReady r), π. split; [exact Hposs|]. left. rewrite find_add_add, TMap.gso by congruence. reflexivity.
          * destruct (ac_nonempty (SetPossState.Δ w')) as (ρ' & π' & Hposs').
            pose proof Hposs' as Hposs''. apply HΔ' in Hposs''. destruct Hposs'' as (r & π & Hposs & _ & _ & -> & ->).
            eexists _, _, (DSReady r), π. split; [exact Hposs'|]. split; [exact Hposs|].
            rewrite find_add_add, TMap.gso by congruence. reflexivity.
        + unfold other_facts, graph_of. rewrite Hσ, Hσ'. cbn [payload].
          split; [reflexivity|]. split; [reflexivity|].
          split; [simpl; rewrite !TMap.gro by congruence; reflexivity|].
          split; [simpl; rewrite !TMap.gro by congruence; reflexivity|].
          split; [intros m v0 Hv0; exact Hv0|].
          split; [intros [s0 [op Heq] ]; injection Heq as _ Heq _; congruence|]. split.
          * intros HP. eapply (spec_image_other_tokens (TSAAtomicPending s actor (tsa_trypop start)) (TSAReady (tsa_close_session actor s))); [exact HΔ'| | |exact HP].
            -- reflexivity.
            -- simpl. rewrite !TMap.gro by congruence. reflexivity.
          * destruct (ac_nonempty (SetPossState.Δ w')) as (ρ' & π' & Hposs').
            pose proof Hposs' as Hposs''. apply HΔ' in Hposs''. destruct Hposs'' as (ρ & π & Hposs & Hspec).
            exists ρ', π', ρ, π. split; [exact Hposs'|]. split; [exact Hposs|].
            eapply specS_none_iff; eauto.
    Qed.

    Lemma GINV_other_facts actor (w w' : proof_state) obs :
      obs <> actor -> GINV actor w w' -> other_facts obs w w'.
    Proof.
      intros Hneq [f [Hσ [Hnone Hequiv] ] ].
      unfold other_facts, graph_of. rewrite Hσ.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [intros; assumption|].
      split; [intros; reflexivity|]. split.
      - intros _ ρ' π' Hposs'. apply Hequiv in Hposs'. inversion Hposs'; subst.
        exists ρ', π. split; [exact Hposs|]. left. rewrite TMap.gso by congruence. reflexivity.
      - destruct (ac_nonempty (SetPossState.Δ w)) as (ρ & π & Hposs).
        exists ρ, (TMap.add actor (ls_inv f) π), ρ, π. split.
        + apply Hequiv. constructor. exact Hposs.
        + split; [exact Hposs|]. rewrite TMap.gso by congruence. reflexivity.
    Qed.

    Lemma GRET_other_facts actor (w w' : proof_state) obs :
      obs <> actor -> GRET actor w w' -> other_facts obs w w'.
    Proof.
      intros Hneq [f [ret [Hσ [Hall Hequiv] ] ] ].
      unfold other_facts, graph_of. rewrite Hσ.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [intros; assumption|].
      split; [intros; reflexivity|]. split.
      - intros _ ρ' π' Hposs'. apply Hequiv in Hposs'. inversion Hposs'; subst.
        exists ρ', π. split; [exact Hposs|]. left. rewrite TMap.gro by congruence. reflexivity.
      - destruct (ac_nonempty (SetPossState.Δ w)) as (ρ & π & Hposs).
        exists ρ, (TMap.remove actor π), ρ, π. split.
        + apply Hequiv. constructor. exact Hposs.
        + split; [exact Hposs|]. rewrite TMap.gro by congruence. reflexivity.
    Qed.

    Lemma R_other_facts obs (w w' : proof_state) : R obs w w' -> other_facts obs w w'.
    Proof.
      intros [ [actor [Hneq HG] ]|[ [actor [Hneq Hinv] ]|[ [actor [Hneq Hret] ]|Heq] ] ].
      - eapply G_other_facts; eauto.
      - eapply GINV_other_facts; eauto.
      - eapply GRET_other_facts; eauto.
      - subst w'. unfold other_facts.
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [intros; assumption|].
        split; [intros; reflexivity|]. split.
        + intros _ ρ' π' Hposs'. exists ρ', π'. split; [exact Hposs'|now left].
        + destruct (ac_nonempty (SetPossState.Δ w)) as (ρ & π & Hposs).
          exists ρ, π, ρ, π. repeat split; auto.
    Qed.

    (** * Assertions of the proof outlines *)

    Definition NoPending (actor : tid) : assertion :=
      fun w => TMap.find actor (tsa_pending_pushes (graph_of w)) = None.

    Definition NoSnapshot (actor : tid) : assertion :=
      fun w => TMap.find actor (tsa_snapshots (graph_of w)) = None.

    Definition NoSession (actor : tid) : assertion :=
      fun w => TMap.find actor (tsa_pop_starts (graph_of w)) = None.

    Definition SessionOpen (actor : tid) : assertion :=
      fun w => TMap.find actor (tsa_pop_starts (graph_of w)) <> None.

    Definition HasToken (actor : tid) (start : TS) : assertion :=
      fun w => TMap.find actor (tsa_pop_ts (graph_of w)) = Some start.

    (** A thread at its invocation has no open session (it holds no token
        before the invocation); this is what keeps its [◦] token stable. *)
    Definition Active (actor : tid) (op : Sig.op (li_sig F)) : assertion :=
      I //\\ ALin actor (ls_inv op) //\\ NoSession actor.

    Definition Completed (actor : tid) (op : Sig.op (li_sig F)) (ret : Sig.ar op) : assertion :=
      I //\\ ALin actor (ls_linr op ret) //\\ NoPending actor //\\ NoSession actor.

    Definition Inside (actor : tid) (op : Sig.op (li_sig F)) : assertion :=
      Active actor op //\\ ⌜ThreadDomain.contains D actor⌝.

    (** [I ∧ α ↦∀ ◦(push v) ∧ P[α] = ⊥]. *)
    Definition PushPre (actor : tid) (v : A) : assertion :=
      Inside actor (dag_push v) //\\ NoPending actor.

    (** [I ∧ ∃l. P[α] = l ∧ V[α,l] = v]. *)
    Definition PushPending (actor : tid) (v : A) : assertion :=
      I //\\ ⌜ThreadDomain.contains D actor⌝ //\\ NoSession actor //\\
      (fun w => exists l,
        TMap.find actor (tsa_pending_pushes (graph_of w)) = Some l /\
        tsa_vertices (graph_of w) (pair actor l) = Some v).

    (** [I ∧ α ↦∀ ◦(pop) ∧ no session]. *)
    Definition PopPre (actor : tid) : assertion :=
      Inside actor dag_pop //\\ NoPending actor.

    (** Between the [startPop] invocation and response: the session is
        open, no snapshot. *)
    Definition StartPending (actor : tid) : assertion :=
      I //\\ ⌜ThreadDomain.contains D actor⌝ //\\ NoPending actor //\\
      SessionOpen actor //\\ NoSnapshot actor.

    (** The loop assertion: the session is open with token [start] and
        no snapshot is pending. *)
    Definition LoopInv (actor : tid) (start : TS) : assertion :=
      I //\\ ⌜ThreadDomain.contains D actor⌝ //\\ NoPending actor //\\
      NoSnapshot actor //\\ HasToken actor start.

    (** The intermediate assertion of a retry: either the snapshot is
        pending, or the atomic empty branch has been taken (and the
        session is already dead in the proof's view of the state). *)
    Definition PopMid (actor : tid) (start : TS) : assertion :=
      (I //\\ ⌜ThreadDomain.contains D actor⌝ //\\ NoPending actor //\\
        HasToken actor start //\\
        (fun w => TMap.find actor (tsa_snapshots (graph_of w)) <> None) //\\
        (fun w : proof_state => forall s0 op, SetPossState.σ w <> TSAAtomicPending s0 actor op))
      \\//
      (I //\\ ⌜ThreadDomain.contains D actor⌝ //\\ NoPending actor //\\ NoSession actor //\\
        ALin actor pop_empty_token //\\
        (fun w : proof_state => exists s, SetPossState.σ w = TSAAtomicPending s actor (tsa_trypop start))).

    Definition PopPost (actor : tid) (start : TS) (ret : @TResult A) : assertion :=
      match ret with
      | TSuccNode v o l => Completed actor dag_pop (PNode v o l)
      | TSuccEmpty => Completed actor dag_pop PEmpty
      | TFail => LoopInv actor start
      end.

    (** * Stability *)

    (** Tokens of a thread with no pending push are preserved by other
        threads unless the thread has an open session and the token is
        [◦(pop)]. *)
    Lemma alin_stable_core t (ls : lin_state) (w w' : proof_state) :
      R t w w' ->
      TMap.find t (tsa_pending_pushes (graph_of w)) = None ->
      (TMap.find t (tsa_pop_starts (graph_of w)) = None \/ ls <> pop_inv_token) ->
      (forall ρ π, SetPossState.Δ w ρ π -> TMap.find t π = Some ls) ->
      forall ρ' π', SetPossState.Δ w' ρ' π' -> TMap.find t π' = Some ls.
    Proof.
      intros HR HP Hcase Hall ρ' π' Hposs'.
      destruct (R_other_facts t w w' HR) as (_ & _ & _ & _ & _ & _ & Htok & _).
      destruct (Htok HP _ _ Hposs') as (ρ & π & Hposs & [Heq|[Hopen Hinv] ]).
      - rewrite Heq. now apply Hall with ρ.
      - exfalso. pose proof (Hall _ _ Hposs) as Hls. rewrite Hinv in Hls. injection Hls as <-.
        destruct Hcase as [Hc|Hc]; [contradiction|apply Hc; reflexivity].
    Qed.

    Lemma nopending_stable t (w w' : proof_state) :
      R t w w' -> NoPending t w -> NoPending t w'.
    Proof.
      intros HR HP. destruct (R_other_facts t w w' HR) as (Hpend & _).
      unfold NoPending in *. rewrite <- Hpend. exact HP.
    Qed.

    Lemma nosnapshot_stable t (w w' : proof_state) :
      R t w w' -> NoSnapshot t w -> NoSnapshot t w'.
    Proof.
      intros HR HS. destruct (R_other_facts t w w' HR) as (_ & Hsnap & _).
      unfold NoSnapshot in *. rewrite <- Hsnap. exact HS.
    Qed.

    Lemma nosession_stable t (w w' : proof_state) :
      R t w w' -> NoSession t w -> NoSession t w'.
    Proof.
      intros HR HS. destruct (R_other_facts t w w' HR) as (_ & _ & Hsess & _).
      unfold NoSession in *. rewrite <- Hsess. exact HS.
    Qed.

    Lemma sessionopen_stable t (w w' : proof_state) :
      R t w w' -> SessionOpen t w -> SessionOpen t w'.
    Proof.
      intros HR HS. destruct (R_other_facts t w w' HR) as (_ & _ & Hsess & _).
      unfold SessionOpen in *. rewrite <- Hsess. exact HS.
    Qed.

    Lemma hastoken_stable t start (w w' : proof_state) :
      R t w w' -> HasToken t start w -> HasToken t start w'.
    Proof.
      intros HR HS. destruct (R_other_facts t w w' HR) as (_ & _ & _ & Hts & _).
      unfold HasToken in *. rewrite <- Hts. exact HS.
    Qed.

    (** A thread whose token is [◦(f)] in every possibility has no pending
        push: the canonical plan places every vertex. *)
    Lemma active_nopending (w : proof_state) t (op : Sig.op (li_sig F)) :
      I w -> (forall ρ π, SetPossState.Δ w ρ π -> TMap.find t π = Some (ls_inv op)) ->
      NoPending t w.
    Proof.
      intros HI Hall. unfold I in HI. destruct HI as (Hwf & Hlag & H & Hcan & Hpop).
      unfold NoPending. set (s := graph_of w) in *.
      assert (Hpl : plan s H H).
      { constructor; [exact (proj1 Hcan)|intros m _; reflexivity|].
        intros y p Hy. exists p. split; [exact Hy|apply ple_refl]. }
      destruct (Hpop H Hpl) as (r & π & Hposs & Hr & Hπ).
      pose proof (Hall _ _ Hposs) as Ht.
      destruct (TMap.find t (tsa_pending_pushes s)) as [l|] eqn:Hl; [|reflexivity]. exfalso.
      assert (Hv : tsa_is_vertex s (pair t l)) by (eapply gw_pending_vertex; eauto).
      pose proof (proj1 (proj2 Hcan) _ Hv) as Hp.
      unfold tsa_is_vertex in Hv. destruct (tsa_vertices s (pair t l)) as [v|] eqn:Hv'; [|contradiction].
      rewrite (rt_push_placed _ _ _ Hπ t l v Hl Hv' Hp) in Ht. discriminate.
    Qed.

    Lemma active_stable t op : AssertionsSet.A.Stable (R t) I (Active t op).
    Proof.
      intros w' [ [w [ [HI [Hlin HS] ] HR] ] HI'].
      split; [exact HI'|]. split.
      - intros ρ' π' Hposs'.
        pose proof (active_nopending w t op HI Hlin) as HP.
        eapply alin_stable_core; eauto.
      - eapply nosession_stable; eauto.
    Qed.

    Lemma pushpre_stable t v : AssertionsSet.A.Stable (R t) I (PushPre t v).
    Proof.
      intros w' [ [w [ [ [ [HI [Hlin HS] ] Hin] HP] HR] ] HI'].
      split; [split; [split; [exact HI'|split]|exact Hin]|].
      - intros ρ' π' Hposs'. eapply alin_stable_core; eauto.
      - eapply nosession_stable; eauto.
      - eapply nopending_stable; eauto.
    Qed.

    Lemma pushpending_stable t v : AssertionsSet.A.Stable (R t) I (PushPending t v).
    Proof.
      intros w' [ [w [ [HI [Hin [HS [l [Hl Hv] ] ] ] ] HR] ] HI'].
      destruct (R_other_facts t w w' HR) as (Hpend & _ & _ & _ & Hvert & _).
      split; [exact HI'|]. split; [exact Hin|]. split; [eapply nosession_stable; eauto|].
      exists l. split; [rewrite <- Hpend; exact Hl|apply Hvert; exact Hv].
    Qed.

    Lemma completed_stable t op ret : AssertionsSet.A.Stable (R t) I (Completed t op ret).
    Proof.
      intros w' [ [w [ [HI [Hlin [HP HS] ] ] HR] ] HI'].
      split; [exact HI'|]. split.
      - intros ρ' π' Hposs'. eapply alin_stable_core; eauto.
      - split; [eapply nopending_stable; eauto|eapply nosession_stable; eauto].
    Qed.

    Lemma poppre_stable t : AssertionsSet.A.Stable (R t) I (PopPre t).
    Proof.
      intros w' [ [w [ [ [ [HI [Hlin HS] ] Hin] HP] HR] ] HI'].
      split; [split; [split; [exact HI'|split]|exact Hin]|].
      - intros ρ' π' Hposs'. eapply alin_stable_core; eauto.
      - eapply nosession_stable; eauto.
      - eapply nopending_stable; eauto.
    Qed.

    Lemma startpending_stable t : AssertionsSet.A.Stable (R t) I (StartPending t).
    Proof.
      intros w' [ [w [ [HI [Hin [HP [HS HN] ] ] ] HR] ] HI'].
      split; [exact HI'|]. split; [exact Hin|]. split; [eapply nopending_stable; eauto|].
      split; [eapply sessionopen_stable; eauto|eapply nosnapshot_stable; eauto].
    Qed.

    Lemma loopinv_stable t start : AssertionsSet.A.Stable (R t) I (LoopInv t start).
    Proof.
      intros w' [ [w [ [HI [Hin [HP [HN Hts] ] ] ] HR] ] HI'].
      split; [exact HI'|]. split; [exact Hin|]. split; [eapply nopending_stable; eauto|].
      split; [eapply nosnapshot_stable; eauto|eapply hastoken_stable; eauto].
    Qed.

    (** Other threads never hand the atomic control to [t]. *)
    Lemma other_control_not_mine t (w w' : proof_state) s0 op :
      R t w w' ->
      (forall s1 op1, SetPossState.σ w <> TSAAtomicPending s1 t op1) ->
      SetPossState.σ w' = TSAAtomicPending s0 t op -> False.
    Proof.
      intros [ [actor [Hneq HG] ]|[ [actor [Hneq Hinv] ]|[ [actor [Hneq Hret] ]|Heq] ] ] Hnot Hσ'.
      - destruct HG as [HG|[HG|[HG|[HG|[HG|[HG|[HG|HG] ] ] ] ] ] ].
        + destruct HG as [? ? ? ? ? ? ? ? ? Hσ1 ?]. rewrite Hσ1 in Hσ'. discriminate.
        + destruct HG as [? ? ? ? ? ? ? ? ? ? Hσ1 ? ? ?]. rewrite Hσ1 in Hσ'. discriminate.
        + destruct HG as [? ? ? ? ? ? Hσ1 ?]. rewrite Hσ1 in Hσ'. discriminate.
        + destruct HG as [? ? ? ? ? ? ? Hσ1 ? ?]. rewrite Hσ1 in Hσ'. discriminate.
        + destruct HG as [? ? ? ? ? ? ? Hσ1 ?]. rewrite Hσ1 in Hσ'. discriminate.
        + destruct HG as [? ? ? ? ? ? ? ? ? ? ? ? Hσ1 ? ? ?]. rewrite Hσ1 in Hσ'. discriminate.
        + destruct HG as [? ? ? ? ? ? ? Hσ1 ? ?]. rewrite Hσ1 in Hσ'. discriminate.
        + destruct HG as [? ? ? ? ? ? ? ? Hσ1 ?|? ? ? ? ? Hσ1 ?].
          * rewrite Hσ1 in Hσ'. injection Hσ' as _ Heq _. congruence.
          * rewrite Hσ1 in Hσ'. discriminate.
      - destruct Hinv as [f [Hσ _] ]. rewrite <- Hσ in Hσ'. exact (Hnot _ _ Hσ').
      - destruct Hret as [f [ret [Hσ _] ] ]. rewrite <- Hσ in Hσ'. exact (Hnot _ _ Hσ').
      - subst w'. exact (Hnot _ _ Hσ').
    Qed.

    Lemma popmid_stable t start : AssertionsSet.A.Stable (R t) I (PopMid t start).
    Proof.
      intros w' [ [w [Hmid HR] ] HI'].
      destruct (R_other_facts t w w' HR) as (Hpend & Hsnap & _ & _ & _ & Hctl & _).
      destruct Hmid as [ [HI [Hin [HP [Hts [HS Hctl'] ] ] ] ] | [HI [Hin [HP [HN [Hlin [s Hσ] ] ] ] ] ] ].
      - left. split; [exact HI'|]. split; [exact Hin|].
        split; [eapply nopending_stable; eauto|]. split; [eapply hastoken_stable; eauto|]. split.
        + rewrite <- Hsnap. exact HS.
        + intros s0 op Heq. eapply other_control_not_mine; eauto.
      - right. split; [exact HI'|]. split; [exact Hin|].
        split; [eapply nopending_stable; eauto|]. split; [eapply nosession_stable; eauto|].
        split.
        + intros ρ' π' Hposs'. eapply alin_stable_core; eauto.
        + exists s. rewrite Hctl; [exact Hσ|]. exists s, (tsa_trypop start). exact Hσ.
    Qed.

    Lemma poppost_stable t start ret : AssertionsSet.A.Stable (R t) I (PopPost t start ret).
    Proof.
      destruct ret as [v o l| |]; simpl.
      - apply completed_stable.
      - apply completed_stable.
      - apply loopinv_stable.
    Qed.

    Lemma pushpre_entails_I t v : ⊨ PushPre t v ==>> I.
    Proof. intros w [ [ [HI _] _] _]. exact HI. Qed.
    Lemma pushpending_entails_I t v : ⊨ PushPending t v ==>> I.
    Proof. intros w [HI _]. exact HI. Qed.
    Lemma completed_entails_I t op ret : ⊨ Completed t op ret ==>> I.
    Proof. intros w [HI _]. exact HI. Qed.
    Lemma poppre_entails_I t : ⊨ PopPre t ==>> I.
    Proof. intros w [ [ [HI _] _] _]. exact HI. Qed.
    Lemma startpending_entails_I t : ⊨ StartPending t ==>> I.
    Proof. intros w [HI _]. exact HI. Qed.
    Lemma loopinv_entails_I t start : ⊨ LoopInv t start ==>> I.
    Proof. intros w [HI _]. exact HI. Qed.
    Lemma popmid_entails_I t start : ⊨ PopMid t start ==>> I.
    Proof. intros w [ [HI _]|[HI _] ]; exact HI. Qed.
    Lemma poppost_entails_I t start ret : ⊨ PopPost t start ret ==>> I.
    Proof. destruct ret; intros w [HI _]; exact HI. Qed.
    Lemma active_entails_I t op : ⊨ Active t op ==>> I.
    Proof. intros w [HI _]. exact HI. Qed.

    (** * Rely/guarantee validity and parallel compatibility *)

    Lemma valid_rg t :
      RGISimulationSet.RGISimulation.ValidRGI (R t) (G t) I t.
    Proof.
      constructor. intros w w' HR HI'.
      destruct (R_other_facts t w w' HR)
        as (_ & _ & _ & _ & _ & _ & _ & (ρ' & π' & ρ & π & Hposs' & Hposs & Hiff)).
      split; intros Hall.
      - intros ρ0 π0 Hposs0.
        eapply ac_find_none_same; [exact Hposs'|exact Hposs0|].
        apply Hiff. now apply Hall with ρ.
      - intros ρ0 π0 Hposs0.
        eapply ac_find_none_same; [exact Hposs|exact Hposs0|].
        apply Hiff. now apply Hall with ρ'.
    Qed.

    Lemma parallel_compatible t1 t2 :
      t1 <> t2 ->
      (I ⊓ (G t1 ∪ (GINV t1 ∪ GRET t1 ∪ GId)) ⊆ R t2)%RGRelation.
    Proof.
      intros Hneq w w' [Hrel _].
      destruct Hrel as [HG | [ [Hinv | Hret] | Hid] ].
      - left. exists t1. split; [congruence|exact HG].
      - right. left. exists t1. split; [congruence|exact Hinv].
      - right. right. left. exists t1. split; [congruence|exact Hret].
      - right. right. right. exact Hid.
    Qed.

    (** * The event updates, derived with the rules of Fig. 10 *)

    Lemma specS_image_nonempty (P : assertion) σ (Δ : config) :
      P (σ, Δ) -> exists ρ π ρ' π', Δ ρ π /\ specS σ ρ π ρ' π'.
    Proof.
      intros _. destruct (ac_nonempty Δ) as (ρ & π & Hposs). exists ρ, π, ρ, π.
      split; [exact Hposs|constructor].
    Qed.

    (** The identity relation and the per-event abstract steps. *)
    Definition idS : poss_relation := fun _ ρ π ρ' π' => ρ' = ρ /\ π' = π.

    Lemma idS_steps σ ρ π ρ' π' : idS σ ρ π ρ' π' -> poss_steps (PossOk ρ π) (PossOk ρ' π').
    Proof. intros [-> ->]. apply rt_refl. Qed.

    Definition S_pushret (β : tid) (v : A) : poss_relation :=
      fun _ ρ π ρ' π' =>
        exists r l', ρ = DSReady r /\
          TMap.find β (ds_pending_pushes r) = Some l' /\
          TMap.find β π = Some (push_lini_token v) /\
          ρ' = DSReady (ds_finish_push β r) /\ π' = TMap.add β (push_ret_token v) π.

    Lemma S_pushret_steps β v σ ρ π ρ' π' :
      S_pushret β v σ ρ π ρ' π' -> poss_steps (PossOk ρ π) (PossOk ρ' π').
    Proof.
      intros (r & l' & -> & HP & Hπ & -> & ->). apply rt_step.
      eapply (@ps_ret _ (li_lts F) β (dag_push v) tt (DSReady r) (DSReady (ds_finish_push β r))).
      - exact (ds_push_res_step β l' v r HP).
      - exact Hπ.
    Qed.

    (** ** The push invocation: [G_push-inv] *)

    Lemma push_inv_update α v :
      PUpdate (G α) (Build_ThreadEvent α (InvEv (tsa_push v)))
        (PushPre α v) (PushPending α v).
    Proof.
      set (ev := Build_ThreadEvent α (InvEv (tsa_push v))).
      set (P2 := fun w' : proof_state => exists σ, PushPre α v (σ, SetPossState.Δ w') /\
        Step (li_lts E) ev σ (SetPossState.σ w')).
      pose proof (PUpdateIdImplyPre (PushPre α v) (PushPre α v) ImplRefl) as H1.
      pose proof (PUpdateEventId ev (PushPre α v)) as H2.
      pose proof (PUpdateIdPStepExact specS P2 specS_poss_steps (specS_image_nonempty P2)) as H3.
      pose proof (PUpdateConseqUpdates _ _ _ _ _ _ _ ev H1 H2 H3) as Hupd.
      eapply PUpdateGuaranteeWeaken; [|eapply PUpdateConseq; [apply ImplRefl| |exact Hupd] ].
      - (* the composed relation is [G_push-inv] *)
        intros w w'' (w1 & (w0 & [Heq0 HP] & [Hstep HΔ1]) & Hσ & Hiff).
        unfold GId in Heq0. subst w0.
        destruct (tsa_push_inv_shape α v _ _ Hstep) as (s & l & Hσw & Hnone & Hfresh & Hσ1).
        left. apply (g_push_inv α s l v w w''); try assumption.
        + intros ρ π Hposs. destruct HP as [ [ [HI [Hlin HS] ] Hin] _]. exact (Hlin ρ π Hposs).
        + exact (eq_trans (eq_sym Hσ) Hσ1).
        + intros ρ' π'. rewrite HΔ1 in Hiff. exact (pstep_iff_change_σ _ _ _ _ _ Hiff Hσ1 ρ' π').
      - (* the postcondition *)
        intros w'' (w1 & (σ0 & HP & Hstep) & Hσ & Hiff).
        destruct (tsa_push_inv_shape α v _ _ Hstep) as (s & l & -> & Hnone & Hfresh & Hσ1).
        destruct HP as [ [ [HI [Hlin HS] ] Hin] HP].
        unfold I, graph_of in HI. simpl in HI. destruct HI as (Hwf & Hlag & H & Hcan & Hpop).
        unfold NoPending, NoSession, graph_of in HP, HS. simpl in HP, HS.
        assert (Hσ'' : SetPossState.σ w'' = TSAReady (tsa_start_push α l v s)) by (exact (eq_trans (eq_sym Hσ) Hσ1)).
        pose proof (pstep_iff_change_σ _ _ _ _ _ Hiff Hσ1) as Hiff2. clear Hiff. rename Hiff2 into Hiff.
        split; [|split; [exact Hin|split] ].
        + unfold I, graph_of. rewrite Hσ''. simpl.
          exact (pi_I_state s α l v H _ _ Hwf Hlag Hcan Hpop Hnone Hfresh (fun ρ π Hposs => Hlin ρ π Hposs) Hiff).
        + unfold NoSession, graph_of. rewrite Hσ''. exact HS.
        + unfold graph_of. rewrite Hσ''. exists l. simpl. split; [apply TMap.gss|apply node_update_eq].
    Qed.

    (** ** The push response: [G_push-ret] *)

    Lemma push_res_update α v :
      PUpdate (G α) (Build_ThreadEvent α (ResEv (tsa_push v) tt))
        (PushPending α v) (Completed α (dag_push v) tt).
    Proof.
      set (ev := Build_ThreadEvent α (ResEv (tsa_push v) tt)).
      set (P1 := ComposeA (PushPending α v) (PStepExact specS)).
      set (P2 := fun w' : proof_state => exists σ, P1 (σ, SetPossState.Δ w') /\
        Step (li_lts E) ev σ (SetPossState.σ w')).
      pose proof (PUpdateIdRecordPre _ _ _ (PUpdateIdPStepExact specS (PushPending α v) specS_poss_steps
        (specS_image_nonempty (PushPending α v)))) as H1.
      pose proof (PUpdateEventId ev P1) as H2.
      (* the filtered abstract response is enabled and nonempty *)
      assert (Hne : forall σ Δ, P2 (σ, Δ) -> exists ρ π ρ' π', Δ ρ π /\ S_pushret α v σ ρ π ρ' π').
      { intros σ Δ (σ0 & (w0 & HP & Hσ0 & Hiff) & Hstep).
        destruct w0 as [σw0 Δw0]. simpl in Hσ0, Hiff, Hstep. subst σw0.
        destruct (tsa_push_res_shape α v _ _ Hstep) as (s & l & -> & Hl & Hσ').
        destruct HP as [HI [Hin [HS [l0 [Hl0 Hv] ] ] ] ].
        unfold I, graph_of in HI. simpl in HI.
        unfold graph_of in Hl0, Hv. simpl in Hl0, Hv.
        rewrite Hl in Hl0. injection Hl0 as <-.
        destruct HI as (Hwf & Hlag & H & Hcan & Hpop).
        edestruct (pr_nonempty s α l v H) as (r & π & Hposs & Hπ); eauto.
        assert (Hlag'' : I_lag s Δ) by (eapply pr_I_lag_Δ''; eauto).
        destruct (Hlag'' _ _ Hposs) as (r0 & Heq & Hlg). injection Heq as <-.
        assert (Hpr : ds_is_vertex r (pair α l) /\ TMap.find α (ds_pending_pushes r) = Some l /\
          lag (tsa_finish_push α s) (ds_finish_push α r) (TMap.add α (push_ret_token v) π)).
        { eapply pr_lag; eauto. }
        destruct Hpr as (_ & HP' & _).
        exists (DSReady r), π, (DSReady (ds_finish_push α r)), (TMap.add α (push_ret_token v) π).
        split; [exact Hposs|]. exists r, l. auto. }
      pose proof (PUpdateIdPStepExact (S_pushret α v) P2 (S_pushret_steps α v) Hne) as H3a.
      pose proof (PUpdateIdPStepExact specS (ComposeA P2 (PStepExact (S_pushret α v)))
        specS_poss_steps (specS_image_nonempty _)) as H3b.
      pose proof (PUpdateIdCompose _ _ _ _ _ H3a H3b) as H3.
      pose proof (PUpdateConseqUpdates _ _ _ _ _ _ _ ev H1 H2 H3) as Hupd.
      eapply PUpdateGuaranteeWeaken; [|eapply PUpdateConseq; [apply ImplRefl| |exact Hupd] ].
      - intros w w'' (w1 & (w0 & [ [Hσ0 Hiff0] HP] & [Hstep HΔ1]) & w3 & [Hσ3 Hiff3] & [Hσ'' Hiff'']).
        destruct (tsa_push_res_shape α v _ _ Hstep) as (s & l & Hσw0 & Hl & Hσ1).
        destruct HP as [HI [Hin [HS [l0 [Hl0 Hv] ] ] ] ].
        unfold graph_of in Hl0, Hv. rewrite Hσ0, Hσw0 in Hl0, Hv. simpl in Hl0, Hv.
        rewrite Hl in Hl0. injection Hl0 as <-.
        right. left.
        apply (g_push_ret α s l v (SetPossState.Δ w0) (SetPossState.Δ w3) w w'').
        + rewrite Hσ0. exact Hσw0.
        + exact Hl.
        + exact Hv.
        + exact (eq_trans (eq_sym Hσ'') (eq_trans (eq_sym Hσ3) Hσ1)).
        + intros ρ' π'. rewrite Hiff0, Hσ0, Hσw0. reflexivity.
        + intros ρ' π'. rewrite Hiff3, HΔ1. split.
          * intros (ρ & π & Hposs & r & l' & -> & HP & Hπ & -> & ->). eauto 9.
          * intros (r & l' & π & Hposs & HP & Hπ & -> & ->). exists (DSReady r), π. split; [exact Hposs|].
            exists r, l'. auto.
        + intros ρ' π'. rewrite Hiff'', <- Hσ3, Hσ1. reflexivity.
      - intros w'' (w3 & (w2 & (σ1 & (w0 & HP & Hσ0 & Hiff0) & Hstep) & Hσ3 & Hiff3) & Hσ'' & Hiff'').
        destruct w0 as [σw0 Δw0]. simpl in Hσ0, Hiff0, Hstep. subst σw0.
        destruct (tsa_push_res_shape α v _ _ Hstep) as (s & l & -> & Hl & Hσ2).
        destruct HP as [HI [Hin [HS [l0 [Hl0 Hv] ] ] ] ].
        unfold I, graph_of in HI. simpl in HI.
        unfold graph_of in Hl0, Hv. simpl in Hl0, Hv.
        unfold NoSession, graph_of in HS. simpl in HS.
        rewrite Hl in Hl0. injection Hl0 as <-.
        destruct HI as (Hwf & Hlag & H & Hcan & Hpop).
        assert (Hσw'' : SetPossState.σ w'' = TSAReady (tsa_finish_push α s))
          by (exact (eq_trans (eq_sym Hσ'') (eq_trans (eq_sym Hσ3) Hσ2))).
        pose proof (pstep_iff_change_σ _ _ _ _ _ Hiff'' (eq_trans (eq_sym Hσ3) Hσ2)) as Hiff''2.
        clear Hiff''. rename Hiff''2 into Hiff''.
        assert (Hiff3' : forall ρ' π', SetPossState.Δ w3 ρ' π' <->
          exists r l' π, SetPossState.Δ w2 (DSReady r) π /\
            TMap.find α (ds_pending_pushes r) = Some l' /\
            TMap.find α π = Some (push_lini_token v) /\
            ρ' = DSReady (ds_finish_push α r) /\ π' = TMap.add α (push_ret_token v) π).
        { intros ρ' π'. rewrite Hiff3. split.
          - intros (ρ & π & Hposs & r & l' & -> & HP & Hπ & -> & ->). eauto 9.
          - intros (r & l' & π & Hposs & HP & Hπ & -> & ->). exists (DSReady r), π. split; [exact Hposs|].
            exists r, l'. auto. }
        assert (Hiff3'' : forall ρ' π', SetPossState.Δ w3 ρ' π' <->
          exists r π, SetPossState.Δ w2 (DSReady r) π /\ TMap.find α π = Some (push_lini_token v) /\
            ρ' = DSReady (ds_finish_push α r) /\ π' = TMap.add α (push_ret_token v) π).
        { eapply pr_Δ3_paper_form; eauto. }
        split; [|split; [|split] ].
        + unfold I, graph_of. rewrite Hσw''. simpl.
          exact (pr_I_state s α l v H _ _ _ _ Hwf Hlag Hcan Hpop Hl Hv Hiff0 Hiff3'' Hiff'').
        + intros ρ' π' Hposs'. apply Hiff'' in Hposs'. destruct Hposs' as (ρ & π & Hposs & Hspec).
          apply Hiff3'' in Hposs. destruct Hposs as (r & π0 & _ & _ & -> & ->).
          refine (eq_trans (specS_find_other_closed _ _ _ _ _ α Hspec _ _) _);
            [simpl; apply TMap.grs|exact HS|apply TMap.gss].
        + unfold NoPending, graph_of. rewrite Hσw''. simpl. apply TMap.grs.
        + unfold NoSession, graph_of. rewrite Hσw''. exact HS.
    Qed.

    (** ** The startPop invocation: [G_start-inv] *)

    Lemma startPop_inv_update α :
      PUpdate (G α) (Build_ThreadEvent α (InvEv tsa_startPop))
        (PopPre α) (StartPending α).
    Proof.
      set (ev := Build_ThreadEvent α (InvEv tsa_startPop)).
      set (P2 := fun w' : proof_state => exists σ, PopPre α (σ, SetPossState.Δ w') /\
        Step (li_lts E) ev σ (SetPossState.σ w')).
      pose proof (PUpdateIdImplyPre (PopPre α) (PopPre α) ImplRefl) as H1.
      pose proof (PUpdateEventId ev (PopPre α)) as H2.
      pose proof (PUpdateIdPStepExact specS P2 specS_poss_steps (specS_image_nonempty P2)) as H3.
      pose proof (PUpdateConseqUpdates _ _ _ _ _ _ _ ev H1 H2 H3) as Hupd.
      eapply PUpdateGuaranteeWeaken; [|eapply PUpdateConseq; [apply ImplRefl| |exact Hupd] ].
      - intros w w'' (w1 & (w0 & [Heq0 HP] & [Hstep HΔ1]) & Hσ & Hiff).
        unfold GId in Heq0. subst w0.
        destruct (tsa_startPop_inv_shape α _ _ Hstep) as (s & Hσw & Hσ1).
        destruct HP as [ [ [HI [Hlin HS] ] Hin] HP].
        right. right. left. apply (g_start_inv α s w w''); try assumption.
        + unfold I, graph_of in HI. rewrite Hσw in HI. destruct HI as (Hwf & _).
          unfold NoSession, graph_of in HS. rewrite Hσw in HS.
          apply no_session_no_time; assumption.
        + exact (eq_trans (eq_sym Hσ) Hσ1).
        + intros ρ' π'. rewrite HΔ1 in Hiff. exact (pstep_iff_change_σ _ _ _ _ _ Hiff Hσ1 ρ' π').
      - intros w'' (w1 & (σ0 & HP & Hstep) & Hσ & Hiff).
        destruct (tsa_startPop_inv_shape α _ _ Hstep) as (s & -> & Hσ1).
        destruct HP as [ [ [HI [Hlin HS] ] Hin] HP].
        unfold I, graph_of in HI. simpl in HI. destruct HI as (Hwf & Hlag & H & Hcan & Hpop).
        unfold NoPending, NoSession, graph_of in HP, HS. simpl in HP, HS.
        assert (Hσ'' : SetPossState.σ w'' = TSAReady (tsa_start_pop_session α s)) by (exact (eq_trans (eq_sym Hσ) Hσ1)).
        pose proof (pstep_iff_change_σ _ _ _ _ _ Hiff Hσ1) as Hiff2. clear Hiff. rename Hiff2 into Hiff.
        pose proof (no_session_no_time s α Hwf HS) as Hnosess.
        pose proof (no_session_no_snapshot s α Hwf HS) as Hnosnap.
        split; [|split; [exact Hin|split; [|split] ] ].
        + unfold I, graph_of. rewrite Hσ''. simpl.
          exact (si_I_state s α H _ _ Hwf Hlag Hcan Hpop Hnosess (fun ρ π Hposs => Hlin ρ π Hposs) Hiff).
        + unfold NoPending, graph_of. rewrite Hσ''. exact HP.
        + unfold SessionOpen, graph_of. rewrite Hσ''. simpl. rewrite TMap.gss. discriminate.
        + unfold NoSnapshot, graph_of. rewrite Hσ''. exact Hnosnap.
    Qed.

    (** ** The startPop response: [G_start-ret] *)

    Lemma startPop_res_update α ts :
      PUpdate (G α) (Build_ThreadEvent α (ResEv tsa_startPop ts))
        (StartPending α) (LoopInv α ts).
    Proof.
      set (ev := Build_ThreadEvent α (ResEv tsa_startPop ts)).
      set (P1 := ComposeA (StartPending α) (PStepExact specS)).
      set (P2 := fun w' : proof_state => exists σ, P1 (σ, SetPossState.Δ w') /\
        Step (li_lts E) ev σ (SetPossState.σ w')).
      pose proof (PUpdateIdRecordPre _ _ _ (PUpdateIdPStepExact specS (StartPending α) specS_poss_steps
        (specS_image_nonempty (StartPending α)))) as H1.
      pose proof (PUpdateEventId ev P1) as H2.
      pose proof (PUpdateIdPStepExact specS P2 specS_poss_steps (specS_image_nonempty P2)) as H3.
      pose proof (PUpdateConseqUpdates _ _ _ _ _ _ _ ev H1 H2 H3) as Hupd.
      eapply PUpdateGuaranteeWeaken; [|eapply PUpdateConseq; [apply ImplRefl| |exact Hupd] ].
      - intros w w'' (w1 & (w0 & [ [Hσ0 Hiff0] HP] & [Hstep HΔ1]) & Hσ'' & Hiff'').
        destruct (tsa_startPop_res_shape α ts _ _ Hstep) as (s & Hσw0 & Hσ1).
        destruct HP as [HI [Hin [HP [HS HN] ] ] ].
        unfold SessionOpen, graph_of in HS. rewrite Hσ0, Hσw0 in HS. simpl in HS.
        right. right. right. left.
        apply (g_start_ret α s ts (SetPossState.Δ w0) w w'').
        + rewrite Hσ0. exact Hσw0.
        + exact HS.
        + exact (eq_trans (eq_sym Hσ'') Hσ1).
        + intros ρ' π'. rewrite Hiff0, Hσ0, Hσw0. reflexivity.
        + intros ρ' π'. rewrite Hiff'', HΔ1, Hσ1. reflexivity.
      - intros w'' (w1 & (σ1 & (w0 & HP & Hσ0 & Hiff0) & Hstep) & Hσ'' & Hiff'').
        destruct w0 as [σw0 Δw0]. simpl in Hσ0, Hiff0, Hstep. subst σw0.
        destruct (tsa_startPop_res_shape α ts _ _ Hstep) as (s & -> & Hσ2).
        destruct HP as [HI [Hin [HP [HS HN] ] ] ].
        unfold I, graph_of in HI. simpl in HI. destruct HI as (Hwf & Hlag & H & Hcan & Hpop).
        unfold NoPending, SessionOpen, NoSnapshot, graph_of in HP, HS, HN. simpl in HP, HS, HN.
        assert (Hσw'' : SetPossState.σ w'' = TSAReady (tsa_finish_pop_session α ts s))
          by (exact (eq_trans (eq_sym Hσ'') Hσ2)).
        pose proof (pstep_iff_change_σ _ _ _ _ _ Hiff'' Hσ2) as Hiff''2.
        clear Hiff''. rename Hiff''2 into Hiff''.
        split; [|split; [exact Hin|split; [|split] ] ].
        + unfold I, graph_of. rewrite Hσw''. simpl.
          exact (sr_I_state s α ts H _ _ _ Hwf Hlag Hcan Hpop HS Hiff0 Hiff'').
        + unfold NoPending, graph_of. rewrite Hσw''. exact HP.
        + unfold NoSnapshot, graph_of. rewrite Hσw''. exact HN.
        + unfold HasToken, graph_of. rewrite Hσw''. simpl. apply TMap.gss.
    Qed.

    (** ** The trypop invocation: [G_snap] or [G_emp] *)

    Lemma lag_all_garbage s r π :
      tsa_all_vertices_garbage s -> lag s r π -> ds_all_vertices_garbage r.
    Proof.
      intros Hall Hlg y. split.
      - intros Hvy. apply (lag_garbage_in _ _ _ Hlg). apply Hall. eapply lag_vertex; eauto.
      - intros Hg. exact (lag_garbage_vertex _ _ _ Hlg y Hg).
    Qed.

    Definition empS (β : tid) : poss_relation :=
      fun _ ρ π ρ' π' =>
        exists r, ρ = DSReady r /\ ds_all_vertices_garbage r /\
          TMap.find β π = Some pop_inv_token /\
          ρ' = DSReady r /\ π' = TMap.add β pop_empty_token (TMap.add β pop_lini_token π).

    Lemma empS_steps β σ ρ π ρ' π' :
      empS β σ ρ π ρ' π' -> poss_steps (PossOk ρ π) (PossOk ρ' π').
    Proof.
      intros (r & -> & Hall & Hπ & -> & ->). eapply rt_trans.
      - apply rt_step.
        eapply (@ps_inv _ (li_lts F) β dag_pop (DSReady r) (DSAtomicPending r β dag_pop) π).
        + apply ds_pop_inv_step.
        + exact Hπ.
      - apply rt_step.
        eapply (@ps_ret _ (li_lts F) β dag_pop PEmpty (DSAtomicPending r β dag_pop) (DSReady r)).
        + apply ds_pop_empty_step. exact Hall.
        + apply TMap.gss.
    Qed.

    (** After the invocation the control decides which abstract update
        applies: speculation after a snapshot, the atomic empty pop
        otherwise. *)
    Definition S_trypop_inv (β : tid) : poss_relation :=
      fun σ => match σ with
               | TSAReady _ => specS σ
               | TSAAtomicPending _ _ _ => empS β σ
               end.

    Lemma S_trypop_inv_steps β σ ρ π ρ' π' :
      S_trypop_inv β σ ρ π ρ' π' -> poss_steps (PossOk ρ π) (PossOk ρ' π').
    Proof.
      destruct σ; simpl; [apply specS_poss_steps|apply empS_steps].
    Qed.

    (** With every vertex removed, the canonical plan is represented with
        [◦(pop)] for the actor: the possibility the empty branch keeps. *)
    Lemma emp_witness s (Δ : config) α start :
      I_state s Δ ->
      TMap.find α (tsa_pop_ts s) = Some start ->
      tsa_all_vertices_garbage s ->
      exists r π, Δ (DSReady r) π /\ ds_all_vertices_garbage r /\
        TMap.find α π = Some pop_inv_token.
    Proof.
      intros (Hwf & Hlag & H & Hcan & Hpop) Hts Hall.
      assert (Hpl : plan s H H).
      { constructor; [exact (proj1 Hcan)|intros m _; reflexivity|].
        intros y p Hy. exists p. split; [exact Hy|apply ple_refl]. }
      destruct (Hpop H Hpl) as (r & π & Hposs & Hr & Hπ).
      destruct (Hlag _ _ Hposs) as (r0 & Heq & Hlg). injection Heq as <-.
      exists r, π. split; [exact Hposs|]. split; [eapply lag_all_garbage; eauto|].
      apply (rt_pop_pending _ _ _ Hπ α).
      - destruct (gw_pop_ts s Hwf α start Hts) as (N0 & HN0). unfold session_open. congruence.
      - intros (n & p & Hn & HM).
        assert (Hv : tsa_is_vertex s n).
        { apply (legal_placed_vertex s H n Hwf (proj1 Hcan)). apply (legal_popped_placed s H n (proj1 Hcan)).
          unfold popped. rewrite Hn. discriminate. }
        apply Hall in Hv. apply (gw_garbage s Hwf) in Hv. exact (Hv HM).
    Qed.

    Lemma trypop_inv_update α start :
      PUpdate (G α) (Build_ThreadEvent α (InvEv (tsa_trypop start))) (LoopInv α start) (PopMid α start).
    Proof.
      set (ev := Build_ThreadEvent α (InvEv (tsa_trypop start))).
      set (P2 := fun w' : proof_state => exists σ, LoopInv α start (σ, SetPossState.Δ w') /\
        Step (li_lts E) ev σ (SetPossState.σ w')).
      pose proof (PUpdateIdImplyPre (LoopInv α start) (LoopInv α start) ImplRefl) as H1.
      pose proof (PUpdateEventId ev (LoopInv α start)) as H2.
      assert (Hne : forall σ Δ, P2 (σ, Δ) -> exists ρ π ρ' π', Δ ρ π /\ S_trypop_inv α σ ρ π ρ' π').
      { intros σ Δ (σ0 & HP & Hstep). simpl in *.
        destruct (tsa_trypop_inv_shape α start _ _ Hstep) as (s & -> & HSnone & Hts & [ [Hall ->]| -> ]).
        - destruct HP as [HI _]. unfold I, graph_of in HI. simpl in HI.
          destruct (emp_witness s Δ α start HI Hts Hall) as (r & π & Hposs & Hallr & Hπ).
          exists (DSReady r), π, (DSReady r), (TMap.add α pop_empty_token (TMap.add α pop_lini_token π)).
          split; [exact Hposs|]. simpl. exists r. split; [reflexivity|].
          split; [exact Hallr|]. split; [exact Hπ|auto].
        - destruct (ac_nonempty Δ) as (ρ & π & Hposs). exists ρ, π, ρ, π. split; [exact Hposs|]. simpl. constructor. }
      pose proof (PUpdateIdPStepExact (S_trypop_inv α) P2 (S_trypop_inv_steps α) Hne) as H3.
      pose proof (PUpdateConseqUpdates _ _ _ _ _ _ _ ev H1 H2 H3) as Hupd.
      eapply PUpdateGuaranteeWeaken; [|eapply PUpdateConseq; [apply ImplRefl| |exact Hupd] ].
      - intros w w'' (w1 & (w0 & [Heq0 HP] & [Hstep HΔ1]) & Hσ & Hiff).
        unfold GId in Heq0. subst w0.
        destruct HP as [HI [Hin [HP [HN Hts0] ] ] ].
        destruct (tsa_trypop_inv_shape α start _ _ Hstep) as (s & Hσw & HSnone & Hts & [ [Hall Hσ1]| Hσ1 ]).
        + (* the empty branch *)
          do 7 right.
          apply (g_emp α s start w w''); try assumption.
          * exact (eq_trans (eq_sym Hσ) Hσ1).
          * intros ρ' π'. rewrite HΔ1 in Hiff. rewrite (pstep_iff_change_σ _ _ _ _ _ Hiff Hσ1). simpl. split.
            -- intros (ρ & π & Hposs & r & -> & Hallr & Hπ & -> & ->). eauto 8.
            -- intros (r & π & Hposs & Hallr & Hπ & -> & ->). exists (DSReady r), π. split; [exact Hposs|].
               exists r. split; [reflexivity|]. split; [exact Hallr|].
               split; [exact Hπ|]. split; reflexivity.
        + (* the snapshot branch *)
          do 4 right. left.
          apply (g_snap α s start w w''); try assumption.
          * exact (eq_trans (eq_sym Hσ) Hσ1).
          * intros ρ' π'. rewrite HΔ1 in Hiff. exact (pstep_iff_change_σ _ _ _ _ _ Hiff Hσ1 ρ' π').
      - intros w'' (w1 & (σ0 & HP & Hstep) & Hσ & Hiff).
        destruct HP as [HI [Hin [HP [HN Hts0] ] ] ].
        destruct (tsa_trypop_inv_shape α start _ _ Hstep) as (s & -> & HSnone & Hts & [ [Hall Hσ1]| Hσ1 ]).
        + (* the empty branch: the second disjunct *)
          unfold I, graph_of in HI. simpl in HI. destruct HI as (Hwf & Hlag & H & Hcan & Hpop).
          unfold NoPending, NoSnapshot, graph_of in HP, HN. simpl in HP, HN.
          assert (Hσ'' : SetPossState.σ w'' = TSAAtomicPending s α (tsa_trypop start)) by (exact (eq_trans (eq_sym Hσ) Hσ1)).
          pose proof (pstep_iff_change_σ _ _ _ _ _ Hiff Hσ1) as Hiff2. clear Hiff. rename Hiff2 into Hiff. simpl in Hiff.
          assert (Hiff' : forall ρ' π', SetPossState.Δ w'' ρ' π' <->
            exists r π, SetPossState.Δ w1 (DSReady r) π /\ TMap.find α π = Some pop_inv_token /\
              ρ' = DSReady r /\
              π' = TMap.add α pop_empty_token (TMap.add α pop_lini_token π)).
          { intros ρ' π'. rewrite Hiff. split.
            - intros (ρ & π & Hposs & r & -> & _ & Hπ & -> & ->). exists r, π. auto.
            - intros (r & π & Hposs & Hπ & -> & ->). exists (DSReady r), π. split; [exact Hposs|].
              destruct (Hlag _ _ Hposs) as (r0 & Heq & Hlg). injection Heq as <-.
              exists r. split; [reflexivity|]. split; [eapply lag_all_garbage; eauto|].
              split; [exact Hπ|]. split; reflexivity. }
          right. split; [|split; [exact Hin|split; [|split; [|split] ] ] ].
          * unfold I, graph_of. rewrite Hσ''. simpl.
            exact (em_I_state s α start H _ _ Hwf Hlag Hcan Hpop HSnone Hts Hall Hiff').
          * unfold NoPending, graph_of. rewrite Hσ''. exact HP.
          * unfold NoSession, graph_of. rewrite Hσ''. simpl. apply TMap.grs.
          * intros ρ' π' Hposs'. apply Hiff' in Hposs'. destruct Hposs' as (r & π & _ & _ & -> & ->).
            rewrite find_add_add. apply TMap.gss.
          * exists s. exact Hσ''.
        + (* the snapshot branch: the first disjunct *)
          unfold I, graph_of in HI. simpl in HI. destruct HI as (Hwf & Hlag & H & Hcan & Hpop).
          unfold NoPending, NoSnapshot, HasToken, graph_of in HP, HN, Hts0. simpl in HP, HN, Hts0.
          assert (Hσ'' : SetPossState.σ w'' = TSAReady (tsa_start_snapshot α s)) by (exact (eq_trans (eq_sym Hσ) Hσ1)).
          pose proof (pstep_iff_change_σ _ _ _ _ _ Hiff Hσ1) as Hiff2. clear Hiff. rename Hiff2 into Hiff. simpl in Hiff.
          left. split; [|split; [exact Hin|split; [|split; [|split] ] ] ].
          * unfold I, graph_of. rewrite Hσ''. simpl.
            exact (sn_I_state s α H _ _ Hwf Hlag Hcan Hpop start HSnone Hts Hiff).
          * unfold NoPending, graph_of. rewrite Hσ''. exact HP.
          * unfold HasToken, graph_of. rewrite Hσ''. exact Hts0.
          * unfold graph_of. rewrite Hσ''. simpl. rewrite TMap.gss. discriminate.
          * intros s0 op Heq. rewrite Hσ'' in Heq. discriminate.
    Qed.

    (** ** The trypop response: [G_rmv], [G_fail], or the empty response *)

    Definition S_pre : poss_relation :=
      fun σ => match σ with TSAReady _ => specS σ | TSAAtomicPending _ _ _ => idS σ end.

    Lemma S_pre_steps σ ρ π ρ' π' : S_pre σ ρ π ρ' π' -> poss_steps (PossOk ρ π) (PossOk ρ' π').
    Proof. destruct σ; simpl; [apply specS_poss_steps|apply idS_steps]. Qed.

    Lemma S_pre_image_nonempty (P : assertion) σ (Δ : config) :
      P (σ, Δ) -> exists ρ π ρ' π', Δ ρ π /\ S_pre σ ρ π ρ' π'.
    Proof.
      intros _. destruct (ac_nonempty Δ) as (ρ & π & Hposs). exists ρ, π, ρ, π.
      split; [exact Hposs|]. destruct σ; simpl; [constructor|split; reflexivity].
    Qed.

    Definition S_filter (β : tid) (ret : @TResult A) : poss_relation :=
      fun _ ρ π ρ' π' => ρ' = ρ /\ π' = π /\
        match ret with
        | TSuccNode v o l => TMap.find β π = Some (pop_succ_token v (pair o l))
        | TSuccEmpty => True
        | TFail => True
        end.

    Lemma S_filter_steps β ret σ ρ π ρ' π' :
      S_filter β ret σ ρ π ρ' π' -> poss_steps (PossOk ρ π) (PossOk ρ' π').
    Proof. intros (-> & -> & _). apply rt_refl. Qed.

    Lemma trypop_res_update α start ret :
      PUpdate (G α) (Build_ThreadEvent α (ResEv (tsa_trypop start) ret)) (PopMid α start) (PopPost α start ret).
    Proof.
      set (ev := Build_ThreadEvent α (ResEv (tsa_trypop start) ret)).
      set (P1 := ComposeA (PopMid α start) (PStepExact S_pre)).
      set (P2 := fun w' : proof_state => exists σ, P1 (σ, SetPossState.Δ w') /\
        Step (li_lts E) ev σ (SetPossState.σ w')).
      pose proof (PUpdateIdRecordPre _ _ _ (PUpdateIdPStepExact S_pre (PopMid α start) S_pre_steps
        (S_pre_image_nonempty (PopMid α start)))) as H1.
      pose proof (PUpdateEventId ev P1) as H2.
      assert (Hne : forall σ Δ, P2 (σ, Δ) -> exists ρ π ρ' π', Δ ρ π /\ S_filter α ret σ ρ π ρ' π').
      { intros σ Δ (σ0 & (w0 & HP & Hσ0 & Hiff) & Hstep).
        destruct w0 as [σw0 Δw0]. simpl in Hσ0, Hiff, Hstep. subst σw0.
        destruct (tsa_trypop_res_shape α start ret _ _ Hstep)
          as [ (s & -> & -> & ->) | [ (s & N & n & v & -> & HS & Hcase & Hv & -> & ->) | (s & N & -> & HS & -> & ->) ] ].
        - destruct (ac_nonempty Δ) as (ρ & π & Hposs). exists ρ, π, ρ, π. split; [exact Hposs|].
          split; [reflexivity|split; [reflexivity|exact Logic.I] ].
        - destruct HP as [ [HI [Hin [HP [Hts [HSne Hctl] ] ] ] ] | [HI [Hin [HP [HSn [Hlin [s0 Hc] ] ] ] ] ] ]; [|discriminate].
          unfold I, graph_of in HI. simpl in HI. destruct HI as (Hwf & Hlag & H & Hcan & Hpop).
          simpl in Hiff.
          destruct (gw_snap s Hwf α N HS) as (st & Hst & _ & _).
          destruct (gw_snap_session s Hwf α st Hst) as (σs & Hσs & _).
          destruct (fs_insertion s H α N st σs n Hwf Hcan HS Hst Hσs Hcase)
            as (H' & P & HcanH' & Hc & Hd & HPn & HPσ & HPt).
          edestruct (rm_filter_nonempty s α N σs n v H H' P) as (r & π & Hposs & Hπ); eauto.
          exists (DSReady r), π, (DSReady r), π. split; [exact Hposs|].
          split; [reflexivity|split; [reflexivity|] ].
          simpl. rewrite <- surjective_pairing. exact Hπ.
        - destruct (ac_nonempty Δ) as (ρ & π & Hposs). exists ρ, π, ρ, π. split; [exact Hposs|].
          split; [reflexivity|split; [reflexivity|exact Logic.I] ]. }
      pose proof (PUpdateIdPStepExact (S_filter α ret) P2 (S_filter_steps α ret) Hne) as H3a.
      pose proof (PUpdateIdPStepExact specS (ComposeA P2 (PStepExact (S_filter α ret)))
        specS_poss_steps (specS_image_nonempty _)) as H3b.
      pose proof (PUpdateIdCompose _ _ _ _ _ H3a H3b) as H3.
      pose proof (PUpdateConseqUpdates _ _ _ _ _ _ _ ev H1 H2 H3) as Hupd.
      eapply PUpdateGuaranteeWeaken; [|eapply PUpdateConseq; [apply ImplRefl| |exact Hupd] ].
      - intros w w'' (w1 & (w0 & [ [Hσ0 Hiff0] HP] & [Hstep HΔ1]) & w3 & [Hσ3 Hiff3] & [Hσ'' Hiff'']).
        destruct (tsa_trypop_res_shape α start ret _ _ Hstep)
          as [ (s & Hσw0 & -> & Hσ1) | [ (s & N & n & v & Hσw0 & HS & Hcase & Hv & -> & Hσ1) | (s & N & Hσw0 & HS & -> & Hσ1) ] ].
        + (* the empty response *)
          do 7 right.
          apply (g_emp_ret α s start w w'').
          * exact (eq_trans Hσ0 Hσw0).
          * exact (eq_trans (eq_sym Hσ'') (eq_trans (eq_sym Hσ3) Hσ1)).
          * intros ρ' π'. rewrite (pstep_iff_change_σ _ _ _ _ _ Hiff'' (eq_trans (eq_sym Hσ3) Hσ1)). split.
            -- intros (ρ0 & π0 & Hposs & Hspec). apply Hiff3 in Hposs.
               destruct Hposs as (ρ1 & π1 & Hposs & -> & -> & _). rewrite HΔ1 in Hposs.
               apply Hiff0 in Hposs. destruct Hposs as (ρ2 & π2 & Hposs & Hpre).
               rewrite Hσ0, Hσw0 in Hpre. simpl in Hpre. destruct Hpre as [-> ->].
               exists ρ2, π2. split; [exact Hposs|exact Hspec].
            -- intros (ρ0 & π0 & Hposs & Hspec). exists ρ0, π0. split; [|exact Hspec].
               apply Hiff3. exists ρ0, π0. split; [|split; [reflexivity|split; [reflexivity|exact Logic.I] ] ].
               rewrite HΔ1. apply Hiff0. exists ρ0, π0. split; [exact Hposs|].
               rewrite Hσ0, Hσw0. simpl. split; reflexivity.
        + (* a successful removal: [G_rmv] *)
          do 5 right. left.
          apply (g_rmv α s N n v (SetPossState.Δ w0) (SetPossState.Δ w3) w w'').
          * exact (eq_trans Hσ0 Hσw0).
          * exact HS.
          * exact Hcase.
          * exact Hv.
          * exact (eq_trans (eq_sym Hσ'') (eq_trans (eq_sym Hσ3) Hσ1)).
          * intros ρ' π'. rewrite Hiff0, Hσ0, Hσw0. reflexivity.
          * intros ρ' π'. rewrite Hiff3, HΔ1. split.
            -- intros (ρ & π & Hposs & -> & -> & Htok). split; [exact Hposs|].
               simpl in Htok. rewrite <- surjective_pairing in Htok. exact Htok.
            -- intros [Hposs Htok]. exists ρ', π'. split; [exact Hposs|]. split; [reflexivity|].
               split; [reflexivity|]. simpl. rewrite <- surjective_pairing. exact Htok.
          * exact (pstep_iff_change_σ _ _ _ _ _ Hiff'' (eq_trans (eq_sym Hσ3) Hσ1)).
        + (* a failure: [G_fail] *)
          do 6 right. left.
          apply (g_fail α s N (SetPossState.Δ w0) w w'').
          * exact (eq_trans Hσ0 Hσw0).
          * exact HS.
          * exact (eq_trans (eq_sym Hσ'') (eq_trans (eq_sym Hσ3) Hσ1)).
          * intros ρ' π'. rewrite Hiff0, Hσ0, Hσw0. reflexivity.
          * intros ρ' π'. rewrite (pstep_iff_change_σ _ _ _ _ _ Hiff'' (eq_trans (eq_sym Hσ3) Hσ1)). split.
            -- intros (ρ0 & π0 & Hposs & Hspec). apply Hiff3 in Hposs.
               destruct Hposs as (ρ1 & π1 & Hposs & -> & -> & _). rewrite HΔ1 in Hposs.
               exists ρ1, π1. split; [exact Hposs|exact Hspec].
            -- intros (ρ0 & π0 & Hposs & Hspec). exists ρ0, π0. split; [|exact Hspec].
               apply Hiff3. exists ρ0, π0. split; [|split; [reflexivity|split; [reflexivity|exact Logic.I] ] ].
               rewrite HΔ1. exact Hposs.
      - intros w'' (w3 & (w2 & (σ1 & (w0 & HP & Hσ0 & Hiff0) & Hstep) & Hσ3 & Hiff3) & Hσ'' & Hiff'').
        destruct w0 as [σw0 Δw0]. simpl in Hσ0, Hiff0, Hstep. subst σw0.
        destruct (tsa_trypop_res_shape α start ret _ _ Hstep)
          as [ (s & -> & -> & Hσ2) | [ (s & N & n & v & -> & HS & Hcase & Hv & -> & Hσ2) | (s & N & -> & HS & -> & Hσ2) ] ].
        + (* the empty response: the session closes, the clock advances *)
          destruct HP as [ [HI [Hin [HP [Hts [HSne Hctl] ] ] ] ] | [HI [Hin [HP [HSn [Hlin [s0 Hc] ] ] ] ] ] ].
          { exfalso. exact (Hctl s (tsa_trypop start) eq_refl). }
          unfold I, graph_of in HI. simpl in HI.
          unfold NoPending, NoSession, graph_of in HP, HSn. simpl in HP, HSn.
          simpl in Hiff0.
          assert (Hσw'' : SetPossState.σ w'' = TSAReady (tsa_close_session α s))
            by (exact (eq_trans (eq_sym Hσ'') (eq_trans (eq_sym Hσ3) Hσ2))).
          pose proof (pstep_iff_change_σ _ _ _ _ _ Hiff'' (eq_trans (eq_sym Hσ3) Hσ2)) as Hiff''2.
          clear Hiff''. rename Hiff''2 into Hiff''. simpl in Hiff''.
          assert (Hchain : forall ρ π, SetPossState.Δ w3 ρ π <-> Δw0 ρ π).
          { intros ρ π. rewrite Hiff3. split.
            - intros (ρ1 & π1 & Hposs & -> & -> & _). apply Hiff0 in Hposs.
              destruct Hposs as (ρ2 & π2 & Hposs & -> & ->). exact Hposs.
            - intros Hposs. exists ρ, π. split; [|split; [reflexivity|split; [reflexivity|exact Logic.I] ] ].
              apply Hiff0. exists ρ, π. split; [exact Hposs|split; reflexivity]. }
          assert (Hiffc : forall ρ' π', SetPossState.Δ w'' ρ' π' <->
            exists ρ π, Δw0 ρ π /\ specS (TSAReady (tsa_close_session α s)) ρ π ρ' π').
          { intros ρ' π'. rewrite Hiff''. split.
            - intros (ρ & π & Hposs & Hspec). exists ρ, π. split; [apply Hchain; exact Hposs|exact Hspec].
            - intros (ρ & π & Hposs & Hspec). exists ρ, π. split; [apply Hchain; exact Hposs|exact Hspec]. }
          destruct HI as (Hwf & Hlag & H & Hcan & Hpop).
          split; [|split; [|split] ].
          * unfold I, graph_of. rewrite Hσw''. simpl. rewrite close_session_tick.
            exact (tk_I_state (tsa_drop_session α s) H _ _ Hwf Hlag Hcan Hpop Hiffc).
          * intros ρ' π' Hposs'. apply Hiffc in Hposs'. destruct Hposs' as (ρ & π & Hposs & Hspec).
            refine (eq_trans (specS_find_other_closed _ _ _ _ _ α Hspec _ _) _);
              [exact HP|simpl; rewrite TMap.grs; reflexivity|exact (Hlin _ _ Hposs) ].
          * unfold NoPending, graph_of. rewrite Hσw''. exact HP.
          * unfold NoSession, graph_of. rewrite Hσw''. simpl. apply TMap.grs.
        + (* a successful removal *)
          destruct HP as [ [HI [Hin [HP [Hts [HSne Hctl] ] ] ] ] | [HI [Hin [HP [HSn [Hlin [s0 Hc] ] ] ] ] ] ]; [|discriminate].
          unfold I, graph_of in HI. simpl in HI. destruct HI as (Hwf & Hlag & H & Hcan & Hpop).
          unfold NoPending, graph_of in HP. simpl in HP.
          simpl in Hiff0.
          destruct (gw_snap s Hwf α N HS) as (st & Hst & _ & _).
          destruct (gw_snap_session s Hwf α st Hst) as (σs & Hσs & _).
          destruct (fs_insertion s H α N st σs n Hwf Hcan HS Hst Hσs Hcase)
            as (H' & P & HcanH' & Hc & Hd & HPn & HPσ & HPt).
          assert (Hσw'' : SetPossState.σ w'' = TSAReady (tsa_remove_node α n s))
            by (exact (eq_trans (eq_sym Hσ'') (eq_trans (eq_sym Hσ3) Hσ2))).
          pose proof (pstep_iff_change_σ _ _ _ _ _ Hiff'' (eq_trans (eq_sym Hσ3) Hσ2)) as Hiff''2.
          clear Hiff''. rename Hiff''2 into Hiff''. simpl in Hiff''.
          assert (Hiff3' : forall ρ' π', SetPossState.Δ w3 ρ' π' <->
            SetPossState.Δ w2 ρ' π' /\ TMap.find α π' = Some (pop_succ_token v n)).
          { intros ρ' π'. rewrite Hiff3. split.
            - intros (ρ & π & Hposs & -> & -> & Htok). split; [exact Hposs|].
              simpl in Htok. rewrite <- surjective_pairing in Htok. exact Htok.
            - intros [Hposs Htok]. exists ρ', π'. split; [exact Hposs|]. split; [reflexivity|].
              split; [reflexivity|]. simpl. rewrite <- surjective_pairing. exact Htok. }
          split; [|split; [|split] ].
          * unfold I, graph_of. rewrite Hσw''. simpl.
            exact (rm_I_state s α N σs n v H H' P _ _ _ _ Hwf Hlag Hcan Hpop HS Hσs Hcase Hv
                     HcanH' Hc Hd HPn HPσ HPt Hiff0 Hiff3' Hiff'').
          * intros ρ' π' Hposs'. apply Hiff'' in Hposs'. destruct Hposs' as (ρ & π & Hposs & Hspec).
            apply Hiff3' in Hposs. destruct Hposs as [_ Htok].
            refine (eq_trans (specS_find_other_closed _ _ _ _ _ α Hspec _ _) _);
              [exact HP|simpl; apply TMap.grs|exact Htok].
          * unfold NoPending, graph_of. rewrite Hσw''. exact HP.
          * unfold NoSession, graph_of. rewrite Hσw''. simpl. apply TMap.grs.
        + (* a failure: back to the loop assertion *)
          destruct HP as [ [HI [Hin [HP [Hts [HSne Hctl] ] ] ] ] | [HI [Hin [HP [HSn [Hlin [s0 Hc] ] ] ] ] ] ]; [|discriminate].
          unfold I, graph_of in HI. simpl in HI. destruct HI as (Hwf & Hlag & H & Hcan & Hpop).
          unfold NoPending, HasToken, graph_of in HP, Hts. simpl in HP, Hts.
          simpl in Hiff0.
          assert (Hσw'' : SetPossState.σ w'' = TSAReady (tsa_clear_snapshot α s))
            by (exact (eq_trans (eq_sym Hσ'') (eq_trans (eq_sym Hσ3) Hσ2))).
          pose proof (pstep_iff_change_σ _ _ _ _ _ Hiff'' (eq_trans (eq_sym Hσ3) Hσ2)) as Hiff''2.
          clear Hiff''. rename Hiff''2 into Hiff''. simpl in Hiff''.
          assert (Hiff3' : forall ρ' π', SetPossState.Δ w3 ρ' π' <-> SetPossState.Δ w2 ρ' π').
          { intros ρ' π'. rewrite Hiff3. split.
            - intros (ρ & π & Hposs & -> & -> & _). exact Hposs.
            - intros Hposs. exists ρ', π'. split; [exact Hposs|split; [reflexivity|split; [reflexivity|exact Logic.I] ] ]. }
          assert (Hiff'3 : forall ρ' π', SetPossState.Δ w'' ρ' π' <->
            exists ρ π, SetPossState.Δ w2 ρ π /\ specS (TSAReady (tsa_clear_snapshot α s)) ρ π ρ' π').
          { intros ρ' π'. rewrite Hiff''. split.
            - intros (ρ & π & Hposs & Hspec). exists ρ, π. split; [apply Hiff3'; exact Hposs|exact Hspec].
            - intros (ρ & π & Hposs & Hspec). exists ρ, π. split; [apply Hiff3'; exact Hposs|exact Hspec]. }
          split; [|split; [exact Hin|split; [|split] ] ].
          * unfold I, graph_of. rewrite Hσw''. simpl.
            exact (fl_I_state s α H _ _ _ Hwf Hlag Hcan Hpop Hiff0 Hiff'3).
          * unfold NoPending, graph_of. rewrite Hσw''. exact HP.
          * unfold NoSnapshot, graph_of. rewrite Hσw''. simpl. apply TMap.grs.
          * unfold HasToken, graph_of. rewrite Hσw''. exact Hts.
    Qed.

    (** * Overlay invocation and return; errors *)

    Lemma set_ginv_exposes_active t op :
      ⊨ AssertionsSet.A.ComposeA I (AssertionsSet.Ginv t op) ==>> Active t op.
    Proof.
      intros w [pre [HIpre [Hσ [Hnone Hequiv] ] ] ].
      destruct pre as [σ0 Δ0], w as [σ1 Δ1]; simpl in *. subst σ1.
      unfold I, graph_of in HIpre. simpl in HIpre.
      destruct (tokenless_idle _ _ t HIpre Hnone) as [HP HS].
      split; [|split].
      - unfold I, graph_of. simpl.
        eapply I_state_equiv; [intros ρ π; symmetry; apply Hequiv|].
        apply ginv_I_state; assumption.
      - intros ρ π Hposs. apply Hequiv in Hposs. eapply ac_inv_find_eq. exact Hposs.
      - unfold NoSession, graph_of. simpl. exact HS.
    Qed.

    Lemma set_gret_closes_completed t op ret :
      ⊨ AssertionsSet.A.ComposeA (Completed t op ret) (AssertionsSet.Gret t op ret) ==>> I.
    Proof.
      intros w [pre [ [HIpre [Hlin [HnoP HnoS] ] ] [Hσ [Hall Hequiv] ] ] ].
      destruct pre as [σ0 Δ0], w as [σ1 Δ1]; simpl in *. subst σ1.
      unfold I, graph_of, NoPending, NoSession in *. simpl in *.
      eapply I_state_equiv; [intros ρ π; symmetry; apply Hequiv|].
      apply gret_I_state; assumption.
    Qed.

    Lemma completed_has_return_token t op ret (σ : concrete_state) (Δ : config) :
      Completed t op ret (SetPossState.Build_ProofStateSet _ _ _ _ σ Δ) ->
      forall ρ π, Δ ρ π -> TMap.find t π = Some (ls_linr op ret).
    Proof. intros [_ [Hlin _] ]. exact Hlin. Qed.

    Lemma active_error t (op : Sig.op (li_sig F)) (w : proof_state) :
      I w -> ALin t (ls_inv op) w -> ~ ThreadDomain.contains D t -> AssertionsSet.APError w.
    Proof.
      intros HI Hlin Hout. destruct w as [σ Δ]. destruct (ac_nonempty Δ) as (ρ & π & Hposs).
      unfold I, graph_of in HI. destruct HI as (_ & Hlag & _).
      destruct (Hlag _ _ Hposs) as (r & -> & _).
      econstructor; [exact Hposs|].
      apply rt_step. eapply (@ps_error _ (li_lts F) t op (DSReady r) π).
      - eapply error_ds_actor_outside; [exact Hout|reflexivity].
      - exact (Hlin (DSReady r) π Hposs).
    Qed.

    Lemma active_or_error_push t v :
      ⊨ Active t (dag_push v) ==>> PushPre t v \\// AssertionsSet.APError.
    Proof.
      intros w [HI [Hlin HS] ].
      destruct (ThreadDomain.contains_dec D t) as [Hin|Hout].
      - left. pose proof (active_nopending w t (dag_push v) HI Hlin) as HP.
        split; [split; [split; [exact HI|split; assumption]|exact Hin]|exact HP].
      - right. eapply active_error; eauto.
    Qed.

    Lemma active_or_error_pop t :
      ⊨ Active t dag_pop ==>> PopPre t \\// AssertionsSet.APError.
    Proof.
      intros w [HI [Hlin HS] ].
      destruct (ThreadDomain.contains_dec D t) as [Hin|Hout].
      - left. pose proof (active_nopending w t dag_pop HI Hlin) as HP.
        split; [split; [split; [exact HI|split; assumption]|exact Hin]|exact HP].
      - right. eapply active_error; eauto.
    Qed.

    (** The underlay errors: an actor outside the domain, or a [trypop]
        with a token that is not the actor's session token. *)
    Lemma inside_no_error_push t v (w : proof_state) :
      ThreadDomain.contains D t ->
      AssertionsSet.A.ANoError (Build_ThreadEvent t (InvEv (tsa_push v))) w.
    Proof.
      intros Hin Herr. simpl in Herr. inversion Herr; subst.
      - match goal with
        | H : Build_ThreadEvent _ _ = Build_ThreadEvent _ _ |- _ => inversion H; subst
        end.
        contradiction.
      - match goal with
        | H : Build_ThreadEvent _ _ = Build_ThreadEvent _ _ |- _ => inversion H
        end.
    Qed.

    Lemma inside_no_error_start t (w : proof_state) :
      ThreadDomain.contains D t ->
      AssertionsSet.A.ANoError (Build_ThreadEvent t (InvEv tsa_startPop)) w.
    Proof.
      intros Hin Herr. simpl in Herr. inversion Herr; subst.
      - match goal with
        | H : Build_ThreadEvent _ _ = Build_ThreadEvent _ _ |- _ => inversion H; subst
        end.
        contradiction.
      - match goal with
        | H : Build_ThreadEvent _ _ = Build_ThreadEvent _ _ |- _ => inversion H
        end.
    Qed.

    Lemma inside_no_error_trypop t start (w : proof_state) :
      ThreadDomain.contains D t -> HasToken t start w ->
      AssertionsSet.A.ANoError (Build_ThreadEvent t (InvEv (tsa_trypop start))) w.
    Proof.
      intros Hin Hts Herr. unfold HasToken, graph_of in Hts.
      destruct w as [σw Δw]. simpl in Hts, Herr.
      inversion Herr; subst.
      - match goal with
        | H : Build_ThreadEvent _ _ = Build_ThreadEvent _ _ |- _ => inversion H; subst
        end.
        contradiction.
      - match goal with
        | H : Build_ThreadEvent _ _ = Build_ThreadEvent _ _ |- _ => inversion H; subst
        end.
        simpl in Hts. contradiction.
    Qed.

    Lemma pushpre_no_error t v :
      ⊨ PushPre t v ==>> AssertionsSet.A.ANoError (Build_ThreadEvent t (InvEv (tsa_push v))).
    Proof. intros w [ [_ Hin] _]. apply inside_no_error_push. exact Hin. Qed.

    Lemma poppre_no_error t :
      ⊨ PopPre t ==>> AssertionsSet.A.ANoError (Build_ThreadEvent t (InvEv tsa_startPop)).
    Proof. intros w [ [_ Hin] _]. apply inside_no_error_start. exact Hin. Qed.

    Lemma loopinv_no_error t start :
      ⊨ LoopInv t start ==>> AssertionsSet.A.ANoError (Build_ThreadEvent t (InvEv (tsa_trypop start))).
    Proof.
      intros w [_ [Hin [_ [_ Hts] ] ] ]. apply inside_no_error_trypop; assumption.
    Qed.

    (** * Method outlines *)

    Lemma push_triple t v :
      [li_lts E, li_lts F, R t, G t, I, t] ⊢
        {{ Active t (dag_push v) }} push_impl D v t
        {{ fun _ => Completed t (dag_push v) tt }}.
    Proof.
      eapply SetLogic.provable_perror with (P' := PushPre t v).
      - apply active_or_error_push.
      - unfold push_impl.
        eapply SetLogic.provable_vis_safe with
          (P' := PushPending t v)
          (Q' := fun _ => Completed t (dag_push v) tt).
        + apply pushpre_no_error.
        + apply pushpending_entails_I.
        + intros _. apply completed_entails_I.
        + apply pushpending_stable.
        + intros _. apply completed_stable.
        + apply push_inv_update.
        + intros []. apply push_res_update.
        + intros []. eapply SetLogic.provable_ret_safe.
          * apply ImplRefl.
          * apply completed_entails_I.
          * apply completed_stable.
    Qed.

    (** One retry: the [trypop] with the session token, mapped to the
        loop's [Continue]/[Break]. *)
    Lemma retry_triple t start :
      [li_lts E, li_lts F, R t, G t, I, t] ⊢
        {{ LoopInv t start }} retry_body D start
        {{ fun r : unit + @PopResult A =>
             match r with
             | inl _ => LoopInv t start
             | inr v => Completed t dag_pop v
             end }}.
    Proof.
      unfold retry_body.
      eapply SetLogic.provable_vis_safe with (P' := PopMid t start) (Q' := PopPost t start).
      - apply loopinv_no_error.
      - apply popmid_entails_I.
      - intros ret. apply poppost_entails_I.
      - apply popmid_stable.
      - intros ret. apply poppost_stable.
      - apply trypop_inv_update.
      - intros ret. apply trypop_res_update.
      - intros ret. destruct ret as [v o l| |]; simpl; eapply SetLogic.provable_ret_safe.
        + apply ImplRefl.
        + apply completed_entails_I.
        + apply completed_stable.
        + apply ImplRefl.
        + apply completed_entails_I.
        + apply completed_stable.
        + apply ImplRefl.
        + apply loopinv_entails_I.
        + apply loopinv_stable.
    Qed.

    Lemma pop_triple t :
      [li_lts E, li_lts F, R t, G t, I, t] ⊢
        {{ Active t dag_pop }} pop_impl D t
        {{ fun ret => Completed t dag_pop ret }}.
    Proof.
      eapply SetLogic.provable_perror with (P' := PopPre t).
      - apply active_or_error_pop.
      - unfold pop_impl.
        eapply SetLogic.provable_vis_safe with
          (P' := StartPending t)
          (Q' := fun start => LoopInv t start).
        + apply poppre_no_error.
        + apply startpending_entails_I.
        + intros start. apply loopinv_entails_I.
        + apply startpending_stable.
        + intros start. apply loopinv_stable.
        + apply startPop_inv_update.
        + intros start. apply startPop_res_update.
        + intros start. eapply SetLogic.provable_doloop.
          * intros ret. apply completed_entails_I.
          * intros ret. apply completed_stable.
          * apply retry_triple.
    Qed.

    (** * Packaging *)

    Definition H0 : history := {| h_inv := fun _ => None; h_pop := fun _ => None |}.

    Lemma initial_I :
      I (SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          (li_init E) (ac_singleton (li_init F) (@TMap.empty lin_state))).
    Proof.
      unfold I, graph_of. simpl.
      pose proof (@ghost_wf_empty A) as Hwf.
      assert (Hnov : forall x, ~ tsa_is_vertex (@empty_try_stack_aux_state A) x).
      { intros x Hv. apply Hv. reflexivity. }
      split; [exact Hwf|]. split.
      - intros ρ π Hposs. inversion Hposs; subst. exists empty_dag_stack_state. split; [reflexivity|].
        constructor.
        + intros x v Hx. discriminate.
        + intros x Hv. exfalso. exact (Hnov x Hv).
        + intros β l v Hβ. rewrite TMap.gempty in Hβ. discriminate.
        + intros β l. rewrite !TMap.gempty. split; [discriminate|intros [Hc _]; discriminate].
        + intros x y He. contradiction.
        + intros x y He. contradiction.
        + intros x Hg. contradiction.
        + intros x Hg. contradiction.
        + intros x Hg. contradiction.
        + intros β v x Hπ. rewrite TMap.gempty in Hπ. discriminate.
      - exists H0. split.
        + split; [|split; [|split] ].
          * constructor; simpl.
            -- intros x p Hx. discriminate.
            -- intros x Hc. exfalso. apply Hc. reflexivity.
            -- intros n p β Hn. discriminate.
            -- intros n HM. exfalso. apply HM. reflexivity.
            -- intros n m p q β Hn. discriminate.
            -- intros n p β x q Hn. discriminate.
            -- intros x y p Hx. discriminate.
            -- intros x y p β β' Hx. discriminate.
            -- intros x y p β Hx. discriminate.
          * intros x Hv. exfalso. exact (Hnov x Hv).
          * intros n Hp. exfalso. apply Hp. reflexivity.
          * intros x m Hx (p & rm & Hp & _). discriminate.
        + intros h Hpl. pose proof (pl_legal _ _ _ Hpl) as Hl.
          assert (Hnop : forall x, ~ placed h x).
          { intros x Hp. exact (Hnov x (legal_placed_vertex _ _ x Hwf Hl Hp)). }
          assert (Hnopop : forall x, ~ popped h x).
          { intros x Hp. exact (Hnop x (legal_popped_placed _ _ x Hl Hp)). }
          exists empty_dag_stack_state, (@TMap.empty lin_state). split; [constructor|]. split.
          * constructor.
            -- intros x Hp. exfalso. exact (Hnop x Hp).
            -- intros x _. reflexivity.
            -- intros x y. simpl. split; [contradiction|]. intros [Hp _]. exfalso. exact (Hnop x Hp).
            -- intros β l. simpl. rewrite !TMap.gempty. split; [discriminate|intros [Hc _]; discriminate].
            -- intros x. simpl. split; [contradiction|]. intros Hp. exfalso. exact (Hnopop x Hp).
          * constructor.
            -- intros β l v Hβ. simpl in Hβ. rewrite TMap.gempty in Hβ. discriminate.
            -- intros β l v Hβ. simpl in Hβ. rewrite TMap.gempty in Hβ. discriminate.
            -- intros β n p v HS. unfold session_open in HS. simpl in HS. rewrite TMap.gempty in HS.
               exfalso. apply HS. reflexivity.
            -- intros β HS. unfold session_open in HS. simpl in HS. rewrite TMap.gempty in HS.
               exfalso. apply HS. reflexivity.
    Qed.

    Program Definition MDagStack : layer_implementation_simulation E F :=
      {| li_impl := dag_stack_impl D |}.
    Next Obligation.
      eapply SetLogic.soundness with (R := R) (G := G) (I := I).
      - exact valid_rg.
      - exact parallel_compatible.
      - intros t op. destruct op as [v|].
        + exists (Active t (dag_push v)).
          exists (fun _ => Completed t (dag_push v) tt).
          constructor.
          * intros w Hcompose. eapply set_ginv_exposes_active. exact Hcompose.
          * apply active_entails_I.
          * apply active_stable.
          * intros [] w Hcompose. eapply set_gret_closes_completed. exact Hcompose.
          * intros [] σ Δ Hcompleted ρ π Hposs. eapply completed_has_return_token; eauto.
          * apply push_triple.
        + exists (Active t dag_pop).
          exists (fun ret => Completed t dag_pop ret).
          constructor.
          * intros w Hcompose. eapply set_ginv_exposes_active. exact Hcompose.
          * apply active_entails_I.
          * apply active_stable.
          * intros ret w Hcompose. eapply set_gret_closes_completed. exact Hcompose.
          * intros ret σ Δ Hcompleted ρ π Hposs. eapply completed_has_return_token; eauto.
          * apply pop_triple.
      - exact initial_I.
    Qed.

    Definition MDagStackLinearizable :
        layer_implementation_linearizability E F :=
      LISim2LILin MDagStack.

    Definition MListPoolDagStack :
        layer_implementation_linearizability (@ListPoolElimProof.E A D) F :=
      LIVComp (@TryStackAuxElimProof.MListPoolTryStackAuxElim A D) MDagStackLinearizable.

  End Proof.

  Print Assumptions MDagStackLinearizable.
End DagStackProof.
