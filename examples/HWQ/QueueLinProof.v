Require Import FMapPositive.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.PArith.PArith.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Eqdep.
Require Import Coq.Relations.Relation_Operators.
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

Require Import examples.Common.AtomicLTS.
Require Import examples.HWQ.POQueueSpec.
Require Import examples.HWQ.QueueSpec.
Require Import examples.HWQ.QueueLin.


(** Layer 2 of the Herlihy--Wing queue: the partial-order queue linearizes
    to the FIFO queue (docs/proof-details/HWQueueProofDetails.tex,
    Section 6).

    The abstract configuration is a set of FIFO linearizations of the
    concrete DAG.  Following the paper, the invariant is a completeness
    property [I_graph] (the paper's (J1)): for every choice [P'] of pending
    enqueues that are still unlinearized, and every topological order [N]
    of the remaining live vertices, some possibility is justified by [N]
    and its tokens record the choice.  Token soundness (J2) is split into
    [I_pending] for other threads and the thread-local assertions of the
    method proofs.

    Three possibility updates carry the future-dependent choice:
    [enq-inv] adds every linearization of the new vertex together with any
    omitted pending vertices ([ac_lin]), [enq-ret] filters the
    possibilities that linearized the vertex, and [deq] selects the
    possibilities justified by an order headed by the removed vertex
    ([ac_select]).  The structure mirrors [TSStackProof] with "top"
    replaced by "minimal" and the stack by a list with insertion at the
    tail. *)
Module QueueLinProof.
  Import Reg LinCCALBase LTSSpec Lang Semantics.
  Import AssertionsSet.
  Import TPSimulationSet.TPSimulation CompLinLayer.
  Import AtomicLTS.
  Import POQueueSpec QueueSpec QueueLinImpl.
  Import (coercions, canonicals, notations) Sig.
  Module SetLogic := RGILogicSet.RGILogic.
  Import SetLogic.

  Open Scope prog_scope.
  Open Scope assertion_scope.
  Open Scope rg_relation_scope.

  Section Proof.
    Context {A : Type}.

    Definition E : layer_interface := @QueueLinImpl.E A.
    Definition F : layer_interface := @QueueLinImpl.F A.

    Definition concrete_state := State (li_lts E).
    Definition abstract_state := State (li_lts F).
    Definition lin_state := @LinState (li_sig F).
    Definition proof_state :=
      @SetPossState.ProofStateSet _ _ (li_lts E) (li_lts F).
    Definition assertion := @Logics.Assertion proof_state.
    Definition rg_relation :=
      @AssertionsSet.A.RGRelation _ _ (li_lts E) (li_lts F).
    Definition config := @AbstractConfig _ (li_lts F).

    Definition q_enq (v : A) : Sig.op (li_sig F) := enq v.
    Definition q_deq : Sig.op (li_sig F) := deq.

    Implicit Types (s : @POQueueState A).
    Implicit Types (π : tmap lin_state).
    Implicit Types (N ms : list VertexId).
    Implicit Types (q vals : list A).

    Definition enq_inv_token (v : A) : lin_state := ls_inv (q_enq v).
    Definition enq_lini_token (v : A) : lin_state := ls_lini (q_enq v).
    Definition enq_ret_token (v : A) : lin_state := ls_linr (q_enq v) tt.
    Definition deq_inv_token : lin_state := ls_inv q_deq.
    Definition deq_lini_token : lin_state := ls_lini q_deq.
    Definition deq_ret_token (v : A) : lin_state := ls_linr q_deq v.

    (** * Concrete payload *)

    Definition graph_of (w : proof_state) : @POQueueState A :=
      poq_payload (SetPossState.σ w).

    (** * Orders and justified possibilities (Section 6.2) *)

    Definition live s (n : VertexId) : Prop := poq_live s n.

    (** The paper's [omitted(s, π, n)]: a pending vertex whose thread has
        not linearized its enqueue in [π]. *)
    Definition omitted s π (n : VertexId) : Prop :=
      exists β v, TMap.find β (poq_pending s) = Some n /\
        TMap.find β π = Some (enq_inv_token v).

    (** Oldest-first lists compatible with the edge relation: no element
        has an edge to a later one, i.e. [(n, m) ∈ E] puts [m] before [n]. *)
    Fixpoint ecompat (Ed : Edges) N : Prop :=
      match N with
      | nil => True
      | n :: N' => (forall m, In m N' -> ~ Ed n m) /\ ecompat Ed N'
      end.

    (** The paper's [topo(s, Y, N)]. *)
    Definition topo s (Y : VertexSet) N : Prop :=
      NoDup N /\ ecompat (poq_edges s) N /\ forall n, In n N <-> Y n.

    (** [vals(s, N)] as a relation. *)
    Definition values_of s N q : Prop :=
      Forall2 (fun n v => poq_vertices s n = Some v) N q.

    (** The linearized set [X(s, π)]. *)
    Definition lin_set s π : VertexSet :=
      fun n => live s n /\ ~ omitted s π n.

    Definition justified s (ρ : abstract_state) π N : Prop :=
      topo s (lin_set s π) N /\
      exists q, values_of s N q /\ ρ = Idle q.

    (** * The invariant (Invariant 6.1) *)

    Definition pending_set s (P' : VertexSet) : Prop :=
      forall n, P' n -> poq_pending_vertex s n.

    (** The token clauses of (J1): threads whose pending vertex is outside
        [P'] have linearized, those inside have not. *)
    Definition graph_tokens s (P' : VertexSet) π : Prop :=
      forall β n, TMap.find β (poq_pending s) = Some n ->
        exists v, poq_vertices s n = Some v /\
          (~ P' n -> TMap.find β π = Some (enq_ret_token v)) /\
          (P' n -> TMap.find β π = Some (enq_inv_token v)).

    (** (J1), with [Y = live \ P'] for a set [P'] of pending vertices. *)
    Definition I_graph s (Δ : config) : Prop :=
      forall P', pending_set s P' ->
      forall N, topo s (fun n => live s n /\ ~ P' n) N ->
      forall q, values_of s N q ->
      exists π, Δ (Idle q) π /\ graph_tokens s P' π.

    (** (J2) for the threads between [enq-inv] and [enq-ret]. *)
    Definition I_pending s (Δ : config) : Prop :=
      forall β n, TMap.find β (poq_pending s) = Some n ->
        exists v, poq_vertices s n = Some v /\
          forall ρ π, Δ ρ π ->
            TMap.find β π = Some (enq_inv_token v) \/
            TMap.find β π = Some (enq_ret_token v).

    Definition I_state s (Δ : config) : Prop :=
      poq_wf s /\ I_graph s Δ /\ I_pending s Δ.

    Definition I : assertion :=
      fun w => I_state (graph_of w) (SetPossState.Δ w).

    (** * Linearizing pending enqueues inside a possibility *)

    (** One omitted pending enqueue is linearized by an atomic FIFO
        enqueue at the tail. *)
    Variant lin_step s :
        abstract_state -> tmap lin_state ->
        abstract_state -> tmap lin_state -> Prop :=
    | lin_enq β n v q π :
        TMap.find β (poq_pending s) = Some n ->
        poq_vertices s n = Some v ->
        TMap.find β π = Some (enq_inv_token v) ->
        lin_step s (Idle q) π
          (Idle (q ++ v :: nil))
          (TMap.add β (enq_ret_token v) (TMap.add β (enq_lini_token v) π)).

    Inductive lin_closure s :
        abstract_state -> tmap lin_state ->
        abstract_state -> tmap lin_state -> Prop :=
    | lin_refl ρ π : lin_closure s ρ π ρ π
    | lin_trans ρ π ρ' π' ρ'' π'' :
        lin_step s ρ π ρ' π' ->
        lin_closure s ρ' π' ρ'' π'' ->
        lin_closure s ρ π ρ'' π''.

    (** * Guarantees (Section 6.4) *)

    (** [enq-inv]: branches (a) and (b) of Lemma 6.3 together are the
        image of [Δ] under the closure. *)
    Variant G_enq_inv (α : tid) : rg_relation :=
    | g_enq_inv s v (w w' : proof_state) :
        SetPossState.σ w = POQReady s ->
        TMap.find α (poq_pending s) = None ->
        (forall ρ π, SetPossState.Δ w ρ π ->
          TMap.find α π = Some (enq_inv_token v)) ->
        SetPossState.σ w' = POQReady (poq_start_enq α v s) ->
        (forall ρ' π', SetPossState.Δ w' ρ' π' <->
          exists ρ π, SetPossState.Δ w ρ π /\
            lin_closure (poq_start_enq α v s) ρ π ρ' π') ->
        G_enq_inv α w w'.

    (** [enq-ret]: keep the possibilities that linearized the vertex. *)
    Variant G_enq_ret (α : tid) : rg_relation :=
    | g_enq_ret s n v (w w' : proof_state) :
        SetPossState.σ w = POQReady s ->
        TMap.find α (poq_pending s) = Some n ->
        poq_vertices s n = Some v ->
        SetPossState.σ w' = POQReady (poq_finish_enq α s) ->
        (forall ρ π, SetPossState.Δ w' ρ π <->
          SetPossState.Δ w ρ π /\ TMap.find α π = Some (enq_ret_token v)) ->
        G_enq_ret α w w'.

    (** [deq]: keep the possibilities justified by an order headed by the
        removed vertex, and take the atomic FIFO dequeue in each. *)
    Variant G_deq (α : tid) : rg_relation :=
    | g_deq s n v (w w' : proof_state) :
        SetPossState.σ w = POQAtomic s α poq_deq ->
        poq_minimal s n ->
        poq_complete s n ->
        poq_vertices s n = Some v ->
        (forall ρ π, SetPossState.Δ w ρ π ->
          TMap.find α π = Some deq_inv_token) ->
        SetPossState.σ w' = POQReady (poq_mark_garbage n s) ->
        (forall ρ' π', SetPossState.Δ w' ρ' π' <->
          exists q π,
            SetPossState.Δ w (Idle (v :: q)) π /\
            (exists N', justified s (Idle (v :: q)) π (n :: N')) /\
            ρ' = Idle q /\
            π' = TMap.add α (deq_ret_token v)
                   (TMap.add α deq_lini_token π)) ->
        G_deq α w w'.

    (** The Coq two-event encoding of the atomic dequeue: entering the
        actor-owned atomic control state without an abstract step. *)
    Variant G_control (α : tid) : rg_relation :=
    | g_control_enter s (w w' : proof_state) :
        SetPossState.σ w = POQReady s ->
        SetPossState.σ w' = POQAtomic s α poq_deq ->
        SetPossState.Δ w' = SetPossState.Δ w ->
        G_control α w w'.

    Definition G (α : tid) : rg_relation :=
      fun w w' =>
        G_enq_inv α w w' \/ G_enq_ret α w w' \/
        G_deq α w w' \/ G_control α w w'.

    Definition R (observer : tid) : rg_relation :=
      fun w w' =>
        (exists actor, actor <> observer /\ G actor w w') \/
        (exists actor, actor <> observer /\ GINV actor w w') \/
        (exists actor, actor <> observer /\ GRET actor w w') \/
        w = w'.

    (** * Assertions of the method proofs (the phases of (J2)) *)

    Definition Active (actor : tid) (op : Sig.op (li_sig F)) : assertion :=
      I //\\ ALin actor (ls_inv op).

    Definition NoPending (actor : tid) : assertion :=
      fun w => TMap.find actor (poq_pending (graph_of w)) = None.

    Definition Completed (actor : tid) (op : Sig.op (li_sig F))
        (ret : Sig.ar op) : assertion :=
      I //\\ ALin actor (ls_linr op ret) //\\ NoPending actor.

    (** Between [enq-inv] and [enq-ret]: the vertex is pending with the
        right value; the token is [◦] or [•] by [I_pending]. *)
    Definition EnqPending (actor : tid) (v : A) : assertion :=
      I //\\
      (fun w => exists n,
        TMap.find actor (poq_pending (graph_of w)) = Some n /\
        poq_vertices (graph_of w) n = Some v).

    Definition DeqAtomic (actor : tid) : assertion :=
      Active actor q_deq //\\
      (fun w => exists s,
        SetPossState.σ w = POQAtomic s actor poq_deq).

    (** * List utilities *)

    Lemma ecompat_mono (E1 E2 : Edges) N :
      (forall x y, E1 x y -> E2 x y) ->
      ecompat E2 N -> ecompat E1 N.
    Proof.
      intros Hsub. induction N as [|n N IH]; simpl.
      - trivial.
      - intros [Hhead Htail]. split; [|now apply IH].
        intros m Hin HE. apply (Hhead m Hin). now apply Hsub.
    Qed.

    Lemma ecompat_app_inv_r Ed N1 N2 :
      ecompat Ed (N1 ++ N2) -> ecompat Ed N2.
    Proof.
      induction N1 as [|n N1 IH]; simpl; intros H.
      - exact H.
      - apply IH. exact (proj2 H).
    Qed.

    Lemma ecompat_app_inv_l Ed N1 N2 :
      ecompat Ed (N1 ++ N2) -> ecompat Ed N1.
    Proof.
      induction N1 as [|n N1 IH]; simpl; intros H.
      - trivial.
      - destruct H as [Hhead Htail]. split; [|now apply IH].
        intros m Hin. apply Hhead. apply in_or_app. now left.
    Qed.

    (** Elements after [n] in a compatible order are not targets of an
        edge from [n]. *)
    Lemma ecompat_app_after Ed N1 n N2 :
      ecompat Ed (N1 ++ n :: N2) ->
      forall m, In m N2 -> ~ Ed n m.
    Proof.
      intros H. apply ecompat_app_inv_r in H. exact (proj1 H).
    Qed.

    Lemma ecompat_edges_ext (E1 E2 : Edges) N :
      (forall x y, In x N -> In y N -> (E1 x y <-> E2 x y)) ->
      ecompat E1 N -> ecompat E2 N.
    Proof.
      induction N as [|n N IH]; simpl; intros Hext.
      - trivial.
      - intros [Hhead Htail]. split.
        + intros m Hin HE. apply (Hhead m Hin). apply Hext; auto.
        + apply IH; [|exact Htail]. intros x y Hx Hy. apply Hext; auto.
    Qed.

    (** Selecting a sublist by an arbitrary (classically decided)
        predicate preserves duplicate-freeness and compatibility. *)
    Lemma select_sublist (Keep : VertexId -> Prop) Ed order :
      NoDup order -> ecompat Ed order ->
      exists N, NoDup N /\ ecompat Ed N /\
        forall n, In n N <-> (In n order /\ Keep n).
    Proof.
      induction order as [|h order IH]; intros Hnodup Hcompat.
      - exists nil. repeat split; try constructor; simpl; tauto.
      - apply NoDup_cons_iff in Hnodup; destruct Hnodup as [Hnotin Hnodup'].
        destruct Hcompat as [Hhead Hcompat'].
        destruct (IH Hnodup' Hcompat') as [N [HnodupN [HcompatN Hmem]]].
        destruct (classic (Keep h)) as [Hkeep|Hdrop].
        + exists (h :: N). split; [|split].
          * constructor; [|exact HnodupN].
            intro Hin. apply Hmem in Hin as [Hin _]. contradiction.
          * split; [|exact HcompatN].
            intros m Hin. apply Hmem in Hin as [Hin _]. now apply Hhead.
          * intros n. simpl. rewrite Hmem. split.
            -- intros [->|[Hin Hk]]; tauto.
            -- intros [[->|Hin] Hk]; tauto.
        + exists N. split; [exact HnodupN|]. split; [exact HcompatN|].
          intros n. simpl. rewrite Hmem. split.
          * intros [Hin Hk]; tauto.
          * intros [[->|Hin] Hk]; [contradiction|tauto].
    Qed.

    Lemma NoDup_app_left (l1 l2 : list VertexId) :
      NoDup (l1 ++ l2) -> NoDup l1.
    Proof.
      induction l1 as [|x l1 IH]; intros H; simpl in *; [constructor|].
      apply NoDup_cons_iff in H. destruct H as [Hnotin H].
      constructor; [|now apply IH].
      intro Hin. apply Hnotin. apply in_or_app. now left.
    Qed.

    Lemma NoDup_app_right (l1 l2 : list VertexId) :
      NoDup (l1 ++ l2) -> NoDup l2.
    Proof.
      induction l1 as [|x l1 IH]; intros H; simpl in *; [exact H|].
      apply NoDup_cons_iff in H. now apply IH.
    Qed.

    Lemma NoDup_app_disjoint (l1 l2 : list VertexId) x :
      NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
    Proof.
      induction l1 as [|y l1 IH]; intros H Hin1 Hin2; simpl in *; [contradiction|].
      apply NoDup_cons_iff in H. destruct H as [Hnotin H].
      destruct Hin1 as [Heq|Hin1].
      - subst y. apply Hnotin. apply in_or_app. now right.
      - now apply IH.
    Qed.

    Lemma values_exist s N :
      (forall n, In n N -> poq_is_vertex s n) ->
      exists q, values_of s N q.
    Proof.
      induction N as [|n N IH]; intros Hvertex.
      - exists nil. constructor.
      - destruct (IH (fun m Hm => Hvertex m (or_intror Hm))) as [q Hq].
        assert (Hn : poq_is_vertex s n) by (apply Hvertex; now left).
        unfold poq_is_vertex in Hn.
        destruct (poq_vertices s n) as [v|] eqn:Hv; [|congruence].
        exists (v :: q). constructor; assumption.
    Qed.

    Lemma values_of_vertex s N q n :
      values_of s N q -> In n N -> poq_is_vertex s n.
    Proof.
      intros Hvals Hin. induction Hvals as [|m v N q Hm Hvals IH].
      - contradiction.
      - destruct Hin as [->|Hin].
        + unfold poq_is_vertex. congruence.
        + now apply IH.
    Qed.

    Lemma values_of_same_vertices s s' N q :
      (forall n, In n N -> poq_vertices s n = poq_vertices s' n) ->
      values_of s N q -> values_of s' N q.
    Proof.
      intros Hsame Hvals. induction Hvals as [|n v N q Hn Hvals IH].
      - constructor.
      - constructor.
        + rewrite <- Hsame; [exact Hn|now left].
        + apply IH. intros m Hm. apply Hsame. now right.
    Qed.

    (** * Token-map utilities *)

    Lemma find_add_add k x y π β :
      TMap.find β (TMap.add k x (TMap.add k y π)) =
      TMap.find β (TMap.add k x π).
    Proof.
      destruct (Pos.eq_dec β k) as [->|Hneq].
      - now rewrite !TMap.gss.
      - now rewrite !TMap.gso by congruence.
    Qed.

    Lemma enq_tokens_distinct (v v' : A) :
      enq_inv_token v <> enq_ret_token v'.
    Proof. discriminate. Qed.

    (** * Topological orders exist: list the vertices in increasing order *)

    Lemma seq_ecompat s :
      poq_wf s -> ecompat (poq_edges s) (seq O (poq_next s)).
    Proof.
      intros Hwf.
      assert (Hgen : forall k start, ecompat (poq_edges s) (seq start k)).
      { induction k as [|k IH]; intros start; simpl; [trivial|].
        split; [|apply IH].
        intros m Hin Hedge. apply in_seq in Hin.
        pose proof (wf_edge_lt s Hwf start m Hedge). lia. }
      apply Hgen.
    Qed.

    Lemma topo_exists s (Y : VertexSet) :
      poq_wf s -> (forall n, Y n -> poq_is_vertex s n) ->
      exists N, topo s Y N.
    Proof.
      intros Hwf Hsub.
      destruct (select_sublist Y (poq_edges s) (seq O (poq_next s))
        (seq_NoDup _ _) (seq_ecompat s Hwf)) as [N [HnodupN [HcompatN Hmem]]].
      exists N. split; [exact HnodupN|]. split; [exact HcompatN|].
      intros n. rewrite Hmem. split.
      - intros [_ Hk]. exact Hk.
      - intros Hk. split; [|exact Hk]. apply in_seq.
        pose proof (poq_vertex_lt s n Hwf (Hsub n Hk)). lia.
    Qed.

    Lemma topo_vertices s (Y : VertexSet) N n :
      (forall m, Y m -> poq_is_vertex s m) ->
      topo s Y N -> In n N -> poq_is_vertex s n.
    Proof.
      intros Hsub [_ [_ Hmem]] Hin. apply Hsub. now apply Hmem.
    Qed.

    Lemma topo_ext s (Y Y' : VertexSet) N :
      (forall n, Y n <-> Y' n) -> topo s Y N -> topo s Y' N.
    Proof.
      intros Hext [Hnodup [Hcompat Hmem]].
      split; [exact Hnodup|]. split; [exact Hcompat|].
      intros n. rewrite Hmem. apply Hext.
    Qed.

    Lemma topo_edges_ext s s' (Y : VertexSet) N :
      poq_edges s = poq_edges s' -> topo s Y N -> topo s' Y N.
    Proof.
      intros Heq [Hnodup [Hcompat Hmem]].
      split; [exact Hnodup|]. split; [|exact Hmem]. now rewrite <- Heq.
    Qed.

    Lemma live_vertex s n : live s n -> poq_is_vertex s n.
    Proof. intros [Hv _]. exact Hv. Qed.

    (** * The closure as possibility steps *)

    Lemma lin_closure_snoc s ρ π ρ' π' ρ'' π'' :
      lin_closure s ρ π ρ' π' ->
      lin_step s ρ' π' ρ'' π'' ->
      lin_closure s ρ π ρ'' π''.
    Proof.
      intros Hclos Hstep. induction Hclos.
      - eapply lin_trans; [exact Hstep|constructor].
      - eapply lin_trans; [exact H|now apply IHHclos].
    Qed.

    Lemma queue_enq_inv_step β (v : A) q :
      Step (li_lts F) (Build_ThreadEvent β (InvEv (q_enq v)))
        (Idle q) (Pending q β (q_enq v)).
    Proof.
      eapply AtomicLTS.step_inv. apply (QueueSpec.step_enq_inv β q v). reflexivity.
    Qed.

    Lemma queue_enq_res_step β (v : A) q :
      Step (li_lts F) (Build_ThreadEvent β (ResEv (q_enq v) tt))
        (Pending q β (q_enq v)) (Idle (q ++ v :: nil)).
    Proof.
      eapply AtomicLTS.step_res. apply (QueueSpec.step_enq_res β q v). reflexivity.
    Qed.

    Lemma queue_deq_inv_step β q :
      Step (li_lts F) (Build_ThreadEvent β (InvEv q_deq))
        (Idle q) (Pending q β q_deq).
    Proof.
      eapply AtomicLTS.step_inv. apply (QueueSpec.step_deq_inv β q). reflexivity.
    Qed.

    Lemma queue_deq_res_step β (v : A) q :
      Step (li_lts F) (Build_ThreadEvent β (ResEv q_deq v))
        (Pending (v :: q) β q_deq) (Idle q).
    Proof.
      eapply AtomicLTS.step_res. apply (QueueSpec.step_deq_res β q v). reflexivity.
    Qed.

    Lemma lin_step_poss_steps s ρ π ρ' π' :
      lin_step s ρ π ρ' π' ->
      poss_steps (PossOk ρ π) (PossOk ρ' π').
    Proof.
      intros Hstep. inversion Hstep; subst.
      eapply rt_trans.
      - apply rt_step.
        eapply (@ps_inv _ (li_lts F) β (q_enq v) (Idle q)
          (Pending q β (q_enq v)) π).
        + apply queue_enq_inv_step.
        + exact H1.
      - apply rt_step.
        eapply (@ps_ret _ (li_lts F) β (q_enq v) tt (Pending q β (q_enq v))
          (Idle (q ++ v :: nil))).
        + apply queue_enq_res_step.
        + apply TMap.gss.
    Qed.

    Lemma lin_closure_poss_steps s ρ π ρ' π' :
      lin_closure s ρ π ρ' π' ->
      poss_steps (PossOk ρ π) (PossOk ρ' π').
    Proof.
      intros Hclos. induction Hclos.
      - apply rt_refl.
      - eapply rt_trans; [eapply lin_step_poss_steps; eauto|exact IHHclos].
    Qed.

    (** * Token bookkeeping for the closure *)

    Lemma lin_step_find s ρ π ρ' π' γ :
      lin_step s ρ π ρ' π' ->
      TMap.find γ π' = TMap.find γ π \/
      (exists n v, TMap.find γ (poq_pending s) = Some n /\
        poq_vertices s n = Some v /\
        TMap.find γ π = Some (enq_inv_token v) /\
        TMap.find γ π' = Some (enq_ret_token v)).
    Proof.
      intros Hstep. inversion Hstep; subst.
      destruct (Pos.eq_dec γ β) as [->|Hneq].
      - right. exists n, v. rewrite find_add_add, TMap.gss. auto.
      - left. rewrite find_add_add, TMap.gso by congruence. reflexivity.
    Qed.

    Lemma lin_closure_find s ρ π ρ' π' γ :
      lin_closure s ρ π ρ' π' ->
      TMap.find γ π' = TMap.find γ π \/
      (exists n v, TMap.find γ (poq_pending s) = Some n /\
        poq_vertices s n = Some v /\
        TMap.find γ π' = Some (enq_ret_token v)).
    Proof.
      intros Hclos. induction Hclos as [ρ π|ρ π ρ' π' ρ'' π'' Hstep Hclos IH].
      - now left.
      - destruct (lin_step_find _ _ _ _ _ γ Hstep)
          as [Hsame|[n [v [Hn [Hv [Hinv0 Hret]]]]]].
        + destruct IH as [Hsame'|Hlin].
          * left. congruence.
          * right. exact Hlin.
        + destruct IH as [Hsame'|Hlin].
          * right. exists n, v. rewrite Hsame'. auto.
          * right. exact Hlin.
    Qed.

    Lemma lin_closure_find_noninv s ρ π ρ' π' γ :
      lin_closure s ρ π ρ' π' ->
      (forall v, TMap.find γ π <> Some (enq_inv_token v)) ->
      TMap.find γ π' = TMap.find γ π.
    Proof.
      intros Hclos. induction Hclos as [ρ π|ρ π ρ' π' ρ'' π'' Hstep Hclos IH];
        intros Hnot.
      - reflexivity.
      - destruct (lin_step_find _ _ _ _ _ γ Hstep)
          as [Hsame|[n [v [Hn0 [Hv0 [Hinv Hret0]]]]]].
        + rewrite <- Hsame. apply IH. now rewrite Hsame.
        + exfalso. exact (Hnot v Hinv).
    Qed.

    Lemma lin_closure_find_nopending s ρ π ρ' π' γ :
      lin_closure s ρ π ρ' π' ->
      TMap.find γ (poq_pending s) = None ->
      TMap.find γ π' = TMap.find γ π.
    Proof.
      intros Hclos Hnone.
      destruct (lin_closure_find _ _ _ _ _ γ Hclos) as [Hsame|[n [v0 [Hn Hrest]]]].
      - exact Hsame.
      - congruence.
    Qed.

    (** Linearizing a list of omitted pending vertices in order appends
        their values at the tail and completes their threads' tokens. *)
    Lemma lin_all s ms vals q π :
      poq_wf s ->
      values_of s ms vals ->
      NoDup ms ->
      (forall m, In m ms -> exists β v,
        TMap.find β (poq_pending s) = Some m /\
        poq_vertices s m = Some v /\
        TMap.find β π = Some (enq_inv_token v)) ->
      exists π',
        lin_closure s (Idle q) π (Idle (q ++ vals)) π' /\
        (forall β, (forall m, In m ms -> TMap.find β (poq_pending s) <> Some m) ->
          TMap.find β π' = TMap.find β π) /\
        (forall β m, In m ms -> TMap.find β (poq_pending s) = Some m ->
          exists v, poq_vertices s m = Some v /\
            TMap.find β π' = Some (enq_ret_token v)).
    Proof.
      intros Hwf Hvals. revert q π.
      induction Hvals as [|m v ms vals Hv Hvals IH]; intros q π Hnodup Hall.
      - exists π. split; [rewrite app_nil_r; constructor|]. split.
        + intros β _. reflexivity.
        + intros β m [].
      - apply NoDup_cons_iff in Hnodup. destruct Hnodup as [Hnotin Hnodup'].
        destruct (Hall m (or_introl eq_refl)) as (β & v' & Hβ & Hv' & Htok).
        rewrite Hv in Hv'. injection Hv' as <-.
        set (π1 := TMap.add β (enq_ret_token v) (TMap.add β (enq_lini_token v) π)).
        assert (Hstep : lin_step s (Idle q) π (Idle (q ++ v :: nil)) π1).
        { apply (lin_enq s β m v q π); assumption. }
        assert (Hother : forall γ, γ <> β -> TMap.find γ π1 = TMap.find γ π).
        { intros γ Hne. unfold π1. rewrite find_add_add, TMap.gso by congruence. reflexivity. }
        assert (Hall' : forall m', In m' ms -> exists β' v',
          TMap.find β' (poq_pending s) = Some m' /\
          poq_vertices s m' = Some v' /\
          TMap.find β' π1 = Some (enq_inv_token v')).
        { intros m' Hm'. destruct (Hall m' (or_intror Hm')) as (β' & v' & Hβ' & Hv'' & Htok').
          exists β', v'. split; [exact Hβ'|]. split; [exact Hv''|].
          rewrite Hother; [exact Htok'|].
          intros ->. rewrite Hβ in Hβ'. injection Hβ' as ->. exact (Hnotin Hm'). }
        destruct (IH (q ++ v :: nil) π1 Hnodup' Hall') as (π' & Hclos & Hunch & Hlin).
        exists π'. split; [|split].
        + rewrite <- app_assoc in Hclos. simpl in Hclos.
          eapply lin_trans; [exact Hstep|exact Hclos].
        + intros γ Hnone. rewrite Hunch.
          * apply Hother. intros ->. exact (Hnone m (or_introl eq_refl) Hβ).
          * intros m' Hm'. apply Hnone. now right.
        + intros γ m' [->|Hm'] Hγ.
          * (* [γ = β] by uniqueness of pending entries *)
            assert (γ = β) by (eapply poq_pending_vertex_unique; eauto). subst γ.
            exists v. split; [exact Hv|]. rewrite Hunch.
            -- unfold π1. apply TMap.gss.
            -- intros m'' Hm'' Hβ''. rewrite Hβ in Hβ''. injection Hβ'' as ->.
               exact (Hnotin Hm'').
          * exact (Hlin γ m' Hm' Hγ).
    Qed.

    (** * Consequences of the invariant *)

    Lemma I_state_wf s Δ : I_state s Δ -> poq_wf s.
    Proof. intros [H _]. exact H. Qed.

    Lemma I_state_graph s Δ : I_state s Δ -> I_graph s Δ.
    Proof. intros [_ [H _]]. exact H. Qed.

    Lemma I_state_pending s Δ : I_state s Δ -> I_pending s Δ.
    Proof. intros [_ [_ H]]. exact H. Qed.

    Lemma pending_vertex_of s β n :
      TMap.find β (poq_pending s) = Some n -> poq_pending_vertex s n.
    Proof. intros H. exists β. exact H. Qed.

    (** [live ∧ complete ⊆ Y ⊆ live] with [Y = live \ P']: a topological
        order of [live \ P'] exists for every [P' ⊆ pending]. *)
    Lemma topo_live_exists s (P' : VertexSet) :
      poq_wf s -> exists N, topo s (fun n => live s n /\ ~ P' n) N.
    Proof.
      intros Hwf. apply topo_exists; [exact Hwf|].
      intros n [Hl _]. apply live_vertex. exact Hl.
    Qed.

    (** The paper's "[α ↦ ◦ ⊕ α ↦ •]" for a pending enqueue follows from
        [I_graph]: both tokens occur in some possibility. *)
    Lemma pending_both_tokens s Δ β n v :
      I_state s Δ ->
      TMap.find β (poq_pending s) = Some n ->
      poq_vertices s n = Some v ->
      (exists ρ π, Δ ρ π /\ TMap.find β π = Some (enq_inv_token v)) /\
      (exists ρ π, Δ ρ π /\ TMap.find β π = Some (enq_ret_token v)).
    Proof.
      intros HI Hn Hv.
      pose proof (I_state_wf _ _ HI) as Hwf.
      pose proof (I_state_graph _ _ HI) as Hgraph.
      split.
      - set (P' := fun m : VertexId => m = n).
        assert (Hpset : pending_set s P').
        { intros m Hm. unfold P' in Hm. subst m. exists β. exact Hn. }
        destruct (topo_live_exists s P' Hwf) as [N Htopo].
        destruct (values_exist s N) as [q Hq].
        { intros m Hm. eapply topo_vertices; [|exact Htopo|exact Hm].
          intros m' [Hm' _]. apply live_vertex. exact Hm'. }
        destruct (Hgraph P' Hpset N Htopo q Hq) as [π [Hposs Htok]].
        destruct (Htok β n Hn) as (v' & Hv' & _ & Hinv).
        rewrite Hv in Hv'. injection Hv' as <-.
        exists (Idle q), π. split; [exact Hposs|]. apply Hinv. reflexivity.
      - set (P' := fun _ : VertexId => False).
        assert (Hpset : pending_set s P') by (intros m Hm; contradiction).
        destruct (topo_live_exists s P' Hwf) as [N Htopo].
        destruct (values_exist s N) as [q Hq].
        { intros m Hm. eapply topo_vertices; [|exact Htopo|exact Hm].
          intros m' [Hm' _]. apply live_vertex. exact Hm'. }
        destruct (Hgraph P' Hpset N Htopo q Hq) as [π [Hposs Htok]].
        destruct (Htok β n Hn) as (v' & Hv' & Hret & _).
        rewrite Hv in Hv'. injection Hv' as <-.
        exists (Idle q), π. split; [exact Hposs|]. apply Hret. intro Hbad. exact Hbad.
    Qed.

    (** A thread whose token is fixed across all possibilities, and is not
        a completed enqueue, has no pending entry. *)
    Lemma alin_no_pending s Δ α (ls : lin_state) :
      I_state s Δ ->
      (forall ρ π, Δ ρ π -> TMap.find α π = Some ls) ->
      (forall v, ls <> enq_ret_token v) ->
      TMap.find α (poq_pending s) = None.
    Proof.
      intros HI Hall Hnotret.
      destruct (TMap.find α (poq_pending s)) as [n|] eqn:Hn; [|reflexivity].
      exfalso.
      destruct (I_state_pending _ _ HI α n Hn) as (v & Hv & _).
      destruct (pending_both_tokens _ _ _ _ _ HI Hn Hv)
        as ((ρ1 & π1 & Hposs1 & Hinv) & (ρ2 & π2 & Hposs2 & Hret)).
      rewrite (Hall _ _ Hposs2) in Hret. injection Hret as Heq.
      exact (Hnotret v Heq).
    Qed.

    Lemma alin_inv_no_pending s Δ α (op : Sig.op (li_sig F)) :
      I_state s Δ ->
      (forall ρ π, Δ ρ π -> TMap.find α π = Some (ls_inv op)) ->
      TMap.find α (poq_pending s) = None.
    Proof.
      intros HI Hall. eapply alin_no_pending; eauto. discriminate.
    Qed.

    Lemma alin_deq_no_pending s Δ α (v : A) :
      I_state s Δ ->
      (forall ρ π, Δ ρ π -> TMap.find α π = Some (deq_ret_token v)) ->
      TMap.find α (poq_pending s) = None.
    Proof.
      intros HI Hall. eapply alin_no_pending; eauto. discriminate.
    Qed.

    (** A thread with a pending entry has a token in every possibility. *)
    Lemma pending_has_token s (Δ : config) t n ρ π :
      I_state s Δ -> TMap.find t (poq_pending s) = Some n ->
      Δ ρ π -> exists ls, TMap.find t π = Some ls.
    Proof.
      intros HI Hn Hposs.
      destruct (I_state_pending _ _ HI t n Hn) as (v & Hv & Htok).
      destruct (Htok _ _ Hposs) as [H|H]; eauto.
    Qed.

    Lemma I_state_equiv s (Δ Δ' : config) :
      (forall ρ π, Δ ρ π <-> Δ' ρ π) -> I_state s Δ -> I_state s Δ'.
    Proof.
      intros Heq [Hwf [Hgraph Hpend]]. split; [exact Hwf|]. split.
      - intros P' Hpset N Htopo q Hq.
        destruct (Hgraph P' Hpset N Htopo q Hq) as [π [Hposs Htok]].
        exists π. split; [apply Heq; exact Hposs|exact Htok].
      - intros β n Hn. destruct (Hpend β n Hn) as (v & Hv & Htok).
        exists v. split; [exact Hv|].
        intros ρ π Hposs. apply Heq in Hposs. exact (Htok ρ π Hposs).
    Qed.

    (** * [I ∘ G_enq-inv ⇒ I] (Lemma 6.3) *)

    Section EnqInv.
      Variable s : @POQueueState A.
      Variables (α : tid) (v : A).
      Variable Δ Δ' : config.
      Hypothesis HI : I_state s Δ.
      Hypothesis Hnone : TMap.find α (poq_pending s) = None.
      Hypothesis Htoken : forall ρ π, Δ ρ π ->
        TMap.find α π = Some (enq_inv_token v).
      Hypothesis HΔ' : forall ρ' π', Δ' ρ' π' <->
        exists ρ π, Δ ρ π /\ lin_closure (poq_start_enq α v s) ρ π ρ' π'.

      Local Notation s' := (poq_start_enq α v s).
      Local Notation n := (poq_next s).

      Let Hwf : poq_wf s := I_state_wf _ _ HI.
      Let Hwf' : poq_wf (poq_start_enq α v s) :=
        poq_start_enq_wf α v s Hwf Hnone.

      Lemma ei_new_not_vertex : ~ poq_is_vertex s n.
      Proof. apply poq_next_not_vertex. exact Hwf. Qed.

      Lemma ei_find_pending_new : TMap.find α (poq_pending s') = Some n.
      Proof. simpl. apply TMap.gss. Qed.

      Lemma ei_find_pending_other β :
        β <> α ->
        TMap.find β (poq_pending s') = TMap.find β (poq_pending s).
      Proof. intros Hne. simpl. rewrite TMap.gso by congruence. reflexivity. Qed.

      Lemma ei_pending_other m :
        m <> n ->
        (poq_pending_vertex s' m <-> poq_pending_vertex s m).
      Proof.
        intros Hneq. rewrite (poq_start_enq_pending_vertex α v s m Hnone). tauto.
      Qed.

      Lemma ei_pending_old_not_alpha β m :
        TMap.find β (poq_pending s) = Some m -> β <> α.
      Proof. intros Hβ ->. congruence. Qed.

      Lemma ei_vertex_not_new m : poq_is_vertex s m -> m <> n.
      Proof. intros Hv ->. exact (ei_new_not_vertex Hv). Qed.

      Lemma ei_live_old m : live s' m -> m <> n -> live s m.
      Proof.
        intros Hl Hne. apply (poq_start_enq_live α v s m Hwf) in Hl.
        destruct Hl as [Heq | Hl]; [congruence | exact Hl].
      Qed.

      Lemma ei_live_new m : live s m -> live s' m.
      Proof. intros Hl. apply (poq_start_enq_live α v s m Hwf). right. exact Hl. Qed.

      (** Elements placed after the new vertex in a compatible order are
          pending vertices of the old graph: the new vertex has an edge to
          every complete one. *)
      Lemma ei_after_new_pending N1 N2 :
        ecompat (poq_edges s') (N1 ++ n :: N2) ->
        (forall m, In m N2 -> poq_is_vertex s m) ->
        forall m, In m N2 -> poq_pending_vertex s m.
      Proof.
        intros Hcompat Hvertex m Hin.
        pose proof (ecompat_app_after _ _ _ _ Hcompat m Hin) as Hnoedge.
        destruct (classic (poq_pending_vertex s m)) as [Hp|Hnp]; [exact Hp|].
        exfalso. apply Hnoedge. apply poq_start_enq_edges. right.
        split; [reflexivity|]. split; [now apply Hvertex|exact Hnp].
      Qed.

      Lemma ei_I_graph : I_graph s' Δ'.
      Proof.
        intros P' Hpset N Htopo q Hq.
        pose proof (I_state_graph _ _ HI) as Hgraph.
        destruct (classic (In n N)) as [Hin|Hnotin].
        - (* the new vertex is linearized: N = N1 ++ n :: N2 *)
          destruct (in_split _ _ Hin) as [N1 [N2 ->]].
          destruct Htopo as [Hnodup [Hcompat Hmem]].
          pose proof (NoDup_remove _ _ _ Hnodup) as [Hnodup12 Hnotin12].
          assert (HN1live : forall m, In m N1 -> live s m).
          { intros m Hm.
            assert (Hm' : In m (N1 ++ n :: N2)) by (apply in_or_app; now left).
            apply Hmem in Hm'. destruct Hm' as [Hlive _].
            apply ei_live_old; [exact Hlive|].
            intros ->. apply Hnotin12. apply in_or_app. now left. }
          assert (HN2live : forall m, In m N2 -> live s m).
          { intros m Hm.
            assert (Hm' : In m (N1 ++ n :: N2)) by (apply in_or_app; right; now right).
            apply Hmem in Hm'. destruct Hm' as [Hlive _].
            apply ei_live_old; [exact Hlive|].
            intros ->. apply Hnotin12. apply in_or_app. now right. }
          assert (HN2vertex : forall m, In m N2 -> poq_is_vertex s m).
          { intros m Hm. apply live_vertex. now apply HN2live. }
          assert (HN2pending : forall m, In m N2 -> poq_pending_vertex s m).
          { apply (ei_after_new_pending N1 N2); assumption. }
          assert (HN2notP : forall m, In m N2 -> ~ P' m).
          { intros m Hm.
            assert (Hm' : In m (N1 ++ n :: N2)) by (apply in_or_app; right; now right).
            apply Hmem in Hm'. exact (proj2 Hm'). }
          assert (HnewnotP : ~ P' n).
          { apply Hmem in Hin. exact (proj2 Hin). }
          (* the old choice of unlinearized enqueues *)
          set (P'' := fun m => (P' m /\ m <> n) \/ In m N2).
          assert (Hpset'' : pending_set s P'').
          { intros m [[Hm Hneq]|Hm].
            - apply Hpset in Hm. apply ei_pending_other in Hm; assumption.
            - now apply HN2pending. }
          assert (Htopo1 : topo s (fun m => live s m /\ ~ P'' m) N1).
          { split; [|split].
            - apply NoDup_app_left in Hnodup12. exact Hnodup12.
            - eapply ecompat_mono;
                [|eapply ecompat_app_inv_l with (N2 := n :: N2); exact Hcompat].
              intros x y Hxy. apply poq_start_enq_edges. left. exact Hxy.
            - intros m. split.
              + intros Hm.
                assert (Hm' : In m (N1 ++ n :: N2)) by (apply in_or_app; now left).
                apply Hmem in Hm'. destruct Hm' as [Hlive HnotP].
                split; [now apply HN1live|].
                intros [[HP _]|HinN2]; [contradiction|].
                exact (NoDup_app_disjoint _ _ _ Hnodup12 Hm HinN2).
              + intros [Hlive HnotP''].
                assert (Hneq : m <> n) by (apply ei_vertex_not_new; apply live_vertex; exact Hlive).
                assert (Hm' : In m (N1 ++ n :: N2)).
                { apply Hmem. split.
                  - now apply ei_live_new.
                  - intro HP. apply HnotP''. left. split; assumption. }
                apply in_app_or in Hm'. destruct Hm' as [Hm'|[Heq|Hm']].
                * exact Hm'.
                * symmetry in Heq. contradiction.
                * exfalso. apply HnotP''. now right. }
          (* split the values *)
          apply Forall2_app_inv_l in Hq.
          destruct Hq as (vals1 & q2' & Hvals1 & Hq2' & ->).
          inversion Hq2' as [|n' v' N2' q2 Hnew Hvals2]; subst.
          rewrite poq_start_enq_vertex_new in Hnew. injection Hnew as <-.
          assert (Hvals1s : values_of s N1 vals1).
          { eapply values_of_same_vertices; [|exact Hvals1].
            intros m Hm. apply poq_start_enq_vertices.
            intros ->. apply Hnotin12. apply in_or_app. now left. }
          assert (Hvals2s : values_of s N2 q2).
          { eapply values_of_same_vertices; [|exact Hvals2].
            intros m Hm. apply poq_start_enq_vertices.
            intros ->. apply Hnotin12. apply in_or_app. now right. }
          destruct (Hgraph P'' Hpset'' N1 Htopo1 vals1 Hvals1s) as [π [Hposs Htok]].
          (* linearize the new vertex, then N2 in order *)
          set (π1 := TMap.add α (enq_ret_token v) (TMap.add α (enq_lini_token v) π)).
          assert (Hstep1 : lin_step s' (Idle vals1) π (Idle (vals1 ++ v :: nil)) π1).
          { apply (lin_enq s' α n v vals1 π).
            - apply ei_find_pending_new.
            - apply poq_start_enq_vertex_new.
            - now apply Htoken with (Idle vals1). }
          assert (Hvals2s' : values_of s' N2 q2) by exact Hvals2.
          assert (HN2nodup : NoDup N2) by (apply NoDup_app_right in Hnodup12; exact Hnodup12).
          assert (Hall2 : forall m, In m N2 -> exists β vm,
            TMap.find β (poq_pending s') = Some m /\
            poq_vertices s' m = Some vm /\
            TMap.find β π1 = Some (enq_inv_token vm)).
          { intros m Hm.
            destruct (HN2pending m Hm) as [β Hβ].
            pose proof (ei_pending_old_not_alpha β m Hβ) as Hβα.
            destruct (Htok β m Hβ) as (vm & Hvm & _ & Hinv).
            exists β, vm. split; [rewrite ei_find_pending_other by exact Hβα; exact Hβ|].
            split.
            - rewrite poq_start_enq_vertices; [exact Hvm|].
              apply ei_vertex_not_new. now apply HN2vertex.
            - unfold π1. rewrite find_add_add, TMap.gso by congruence.
              apply Hinv. now right. }
          destruct (lin_all s' N2 q2 (vals1 ++ v :: nil) π1 Hwf' Hvals2s' HN2nodup Hall2)
            as (π' & Hclos & Hunch & Hlin).
          exists π'. split.
          + apply HΔ'. exists (Idle vals1), π. split; [exact Hposs|].
            rewrite <- app_assoc in Hclos. simpl in Hclos.
            eapply lin_trans; [exact Hstep1|exact Hclos].
          + (* the token clauses *)
            intros β m Hβm.
            destruct (Pos.eq_dec β α) as [->|Hneq].
            * rewrite ei_find_pending_new in Hβm. injection Hβm as <-.
              exists v. split; [apply poq_start_enq_vertex_new|]. split.
              -- intros _. rewrite Hunch.
                 ++ unfold π1. apply TMap.gss.
                 ++ intros m' Hm' Hbad. rewrite ei_find_pending_new in Hbad.
                    injection Hbad as <-. apply Hnotin12. apply in_or_app. now right.
              -- intros HP. contradiction.
            * rewrite ei_find_pending_other in Hβm by exact Hneq.
              destruct (Htok β m Hβm) as (vβ & Hvβ & Hret & Hinv).
              assert (Hmn : m <> n).
              { apply ei_vertex_not_new. unfold poq_is_vertex. congruence. }
              exists vβ. split; [rewrite poq_start_enq_vertices; assumption|].
              destruct (classic (In m N2)) as [HinN2|HnotinN2].
              -- split.
                 ++ intros _.
                    destruct (Hlin β m HinN2) as (vm & Hvm & Hret').
                    { rewrite ei_find_pending_other by exact Hneq. exact Hβm. }
                    rewrite poq_start_enq_vertices in Hvm by exact Hmn.
                    rewrite Hvβ in Hvm. injection Hvm as <-. exact Hret'.
                 ++ intros HP. exfalso. exact (HN2notP _ HinN2 HP).
              -- assert (Hother : TMap.find β π' = TMap.find β π).
                 { rewrite Hunch.
                   - unfold π1. rewrite find_add_add, TMap.gso by congruence. reflexivity.
                   - intros m' Hm' Hbad. rewrite ei_find_pending_other in Hbad by exact Hneq.
                     rewrite Hβm in Hbad. injection Hbad as <-. exact (HnotinN2 Hm'). }
                 rewrite Hother. split.
                 ++ intros HnotP. apply Hret. intros [[HP _]|HinN2']; contradiction.
                 ++ intros HP. apply Hinv. left. split; assumption.
        - (* the new vertex is not linearized: it is in P' *)
          assert (HnewP : P' n).
          { destruct (classic (P' n)) as [HP|HnP]; [exact HP|].
            exfalso. apply Hnotin. destruct Htopo as [_ [_ Hmem]]. apply Hmem.
            split; [|exact HnP].
            apply (poq_start_enq_live α v s n Hwf). left. reflexivity. }
          set (P'' := fun m => P' m /\ m <> n).
          assert (Hpset'' : pending_set s P'').
          { intros m [Hm Hneq]. apply Hpset in Hm. apply ei_pending_other in Hm; assumption. }
          assert (Htopo' : topo s (fun m => live s m /\ ~ P'' m) N).
          { destruct Htopo as [Hnodup [Hcompat Hmem]]. split; [exact Hnodup|]. split.
            - eapply ecompat_mono; [|exact Hcompat].
              intros x y Hxy. apply poq_start_enq_edges. left. exact Hxy.
            - intros m. rewrite Hmem. unfold P''. split.
              + intros [Hlive HnP].
                assert (Hneq : m <> n) by (intros ->; exact (Hnotin (proj2 (Hmem n) (conj Hlive HnP)))).
                split; [apply ei_live_old; assumption|]. tauto.
              + intros [Hlive HnP''].
                assert (Hneq : m <> n) by (apply ei_vertex_not_new; apply live_vertex; exact Hlive).
                split; [now apply ei_live_new|]. tauto. }
          assert (Hqs : values_of s N q).
          { eapply values_of_same_vertices; [|exact Hq].
            intros m Hm. apply poq_start_enq_vertices. intros ->. contradiction. }
          destruct (Hgraph P'' Hpset'' N Htopo' q Hqs) as [π [Hposs Htok]].
          exists π. split.
          + apply HΔ'. exists (Idle q), π. split; [exact Hposs|constructor].
          + intros β m Hβm.
            destruct (Pos.eq_dec β α) as [->|Hneq].
            * rewrite ei_find_pending_new in Hβm. injection Hβm as <-.
              exists v. split; [apply poq_start_enq_vertex_new|]. split.
              -- intros HnP. contradiction.
              -- intros _. now apply Htoken with (Idle q).
            * rewrite ei_find_pending_other in Hβm by exact Hneq.
              destruct (Htok β m Hβm) as (vβ & Hvβ & Hret & Hinv).
              assert (Hmn : m <> n).
              { apply ei_vertex_not_new. unfold poq_is_vertex. congruence. }
              exists vβ. split; [rewrite poq_start_enq_vertices; assumption|]. split.
              -- intros HnP. apply Hret. intros [HP _]. contradiction.
              -- intros HP. apply Hinv. split; assumption.
      Qed.

      Lemma ei_I_pending : I_pending s' Δ'.
      Proof.
        intros β m Hβm.
        destruct (Pos.eq_dec β α) as [->|Hneq].
        - rewrite ei_find_pending_new in Hβm. injection Hβm as <-.
          exists v. split; [apply poq_start_enq_vertex_new|].
          intros ρ' π' Hposs'. apply HΔ' in Hposs'.
          destruct Hposs' as (ρ & π & Hposs & Hclos).
          destruct (lin_closure_find _ _ _ _ _ α Hclos)
            as [Hsame|[n' [v' [Hn' [Hv' Hret]]]]].
          + left. rewrite Hsame. now apply Htoken with ρ.
          + right. rewrite ei_find_pending_new in Hn'. injection Hn' as <-.
            rewrite poq_start_enq_vertex_new in Hv'. injection Hv' as <-.
            exact Hret.
        - rewrite ei_find_pending_other in Hβm by exact Hneq.
          destruct (I_state_pending _ _ HI β m Hβm) as (vβ & Hvβ & Htok).
          assert (Hmn : m <> n).
          { apply ei_vertex_not_new. unfold poq_is_vertex. congruence. }
          exists vβ. split; [rewrite poq_start_enq_vertices; assumption|].
          intros ρ' π' Hposs'. apply HΔ' in Hposs'.
          destruct Hposs' as (ρ & π & Hposs & Hclos).
          destruct (lin_closure_find _ _ _ _ _ β Hclos)
            as [Hsame|[n' [v' [Hn' [Hv' Hret]]]]].
          + rewrite Hsame. exact (Htok _ _ Hposs).
          + right. rewrite ei_find_pending_other in Hn' by exact Hneq.
            rewrite Hβm in Hn'. injection Hn' as <-.
            rewrite poq_start_enq_vertices in Hv' by exact Hmn.
            rewrite Hvβ in Hv'. injection Hv' as <-. exact Hret.
      Qed.

      Lemma ei_I_state : I_state s' Δ'.
      Proof. split; [exact Hwf'|]. split; [apply ei_I_graph|apply ei_I_pending]. Qed.
    End EnqInv.

    (** * [I ∘ G_enq-ret ⇒ I] (Lemma 6.4) *)

    Section EnqRet.
      Variable s : @POQueueState A.
      Variables (α : tid) (n : VertexId) (v : A).
      Variable Δ Δ' : config.
      Hypothesis HI : I_state s Δ.
      Hypothesis Hn : TMap.find α (poq_pending s) = Some n.
      Hypothesis Hv : poq_vertices s n = Some v.
      Hypothesis HΔ' : forall ρ π, Δ' ρ π <->
        Δ ρ π /\ TMap.find α π = Some (enq_ret_token v).

      Local Notation s' := (poq_finish_enq α s).

      Let Hwf : poq_wf s := I_state_wf _ _ HI.

      Lemma er_pending_not_alpha β m :
        TMap.find β (poq_pending s') = Some m ->
        TMap.find β (poq_pending s) = Some m /\ β <> α.
      Proof.
        intros H. simpl in H. apply find_remove_inv in H. tauto.
      Qed.

      (** [n] is complete in [s'], so every admissible [P'] excludes it. *)
      Lemma er_not_in_pset P' : pending_set s' P' -> ~ P' n.
      Proof.
        intros Hpset HP. apply Hpset in HP.
        apply (poq_finish_enq_pending_vertex_iff α s n n Hwf Hn) in HP.
        exact (proj2 HP eq_refl).
      Qed.

      Lemma er_I_graph : I_graph s' Δ'.
      Proof.
        intros P' Hpset N Htopo q Hq.
        assert (Hpset0 : pending_set s P').
        { intros m Hm. apply Hpset in Hm.
          exact (poq_finish_enq_pending_vertex α s m Hm). }
        (* vertices, edges and garbage are unchanged *)
        assert (Htopo0 : topo s (fun m => live s m /\ ~ P' m) N) by exact Htopo.
        assert (Hq0 : values_of s N q) by exact Hq.
        destruct (I_state_graph _ _ HI P' Hpset0 N Htopo0 q Hq0) as [π [Hposs Htok]].
        exists π. split.
        - apply HΔ'. split; [exact Hposs|].
          destruct (Htok α n Hn) as (v' & Hv' & Hret & _).
          rewrite Hv in Hv'. injection Hv' as <-.
          apply Hret. apply er_not_in_pset. exact Hpset.
        - intros β m Hβm. destruct (er_pending_not_alpha β m Hβm) as [Hβm0 _].
          exact (Htok β m Hβm0).
      Qed.

      Lemma er_I_pending : I_pending s' Δ'.
      Proof.
        intros β m Hβm. destruct (er_pending_not_alpha β m Hβm) as [Hβm0 _].
        destruct (I_state_pending _ _ HI β m Hβm0) as (vβ & Hvβ & Htok).
        exists vβ. split; [exact Hvβ|].
        intros ρ π Hposs'. apply HΔ' in Hposs'. exact (Htok _ _ (proj1 Hposs')).
      Qed.

      Lemma er_I_state : I_state s' Δ'.
      Proof.
        split; [apply poq_finish_enq_wf; exact Hwf|].
        split; [apply er_I_graph|apply er_I_pending].
      Qed.

      Lemma er_nonempty :
        exists ρ π, Δ ρ π /\ TMap.find α π = Some (enq_ret_token v).
      Proof. exact (proj2 (pending_both_tokens _ _ _ _ _ HI Hn Hv)). Qed.
    End EnqRet.

    (** * [I ∘ G_deq ⇒ I] (Lemma 6.5) *)

    Section Deq.
      Variable s : @POQueueState A.
      Variables (α : tid) (n : VertexId) (v : A).
      Variable Δ Δ' : config.
      Hypothesis HI : I_state s Δ.
      Hypothesis Hmin : poq_minimal s n.
      Hypothesis Hcomp : poq_complete s n.
      Hypothesis Hv : poq_vertices s n = Some v.
      Hypothesis Hα : forall ρ π, Δ ρ π -> TMap.find α π = Some deq_inv_token.

      Local Notation s' := (poq_mark_garbage n s).
      Local Notation πf π :=
        (TMap.add α (deq_ret_token v) (TMap.add α deq_lini_token π)).

      Let Hwf : poq_wf s := I_state_wf _ _ HI.
      Let Hαnone : TMap.find α (poq_pending s) = None :=
        alin_inv_no_pending s Δ α q_deq HI Hα.

      Lemma deq_pending_not_alpha β m :
        TMap.find β (poq_pending s) = Some m -> β <> α.
      Proof. intros Hβ ->. congruence. Qed.

      Lemma deq_find_other π β :
        β <> α -> TMap.find β (πf π) = TMap.find β π.
      Proof. intros Hneq. rewrite find_add_add, TMap.gso by congruence. reflexivity. Qed.

      Lemma deq_live_n : live s n.
      Proof. exact (proj1 Hmin). Qed.

      (** The paper's argument for (J1): extend a post-state order by the
          removed minimal vertex and read off the possibility delivered by
          the old (J1). *)
      Lemma deq_witness P' N' q' :
        pending_set s' P' ->
        topo s' (fun m => live s' m /\ ~ P' m) N' ->
        values_of s' N' q' ->
        exists π,
          Δ (Idle (v :: q')) π /\
          (exists N, justified s (Idle (v :: q')) π (n :: N)) /\
          graph_tokens s' P' (πf π).
      Proof.
        intros Hpset Htopo Hq.
        assert (Hpset0 : pending_set s P') by exact Hpset.
        assert (HnotinN' : ~ In n N').
        { intro Hin. destruct Htopo as [_ [_ Hmem]]. apply Hmem in Hin.
          destruct Hin as [Hlive _]. apply poq_mark_garbage_live in Hlive.
          exact (proj2 Hlive eq_refl). }
        assert (Htopo0 : topo s (fun m => live s m /\ ~ P' m) (n :: N')).
        { destruct Htopo as [Hnodup [Hcompat Hmem]]. split; [|split].
          - constructor; assumption.
          - split; [|exact Hcompat].
            intros m Hin Hedge. apply Hmem in Hin. destruct Hin as [Hlive _].
            apply poq_mark_garbage_live in Hlive. destruct Hlive as [Hlive _].
            exact (proj2 Hmin m Hedge Hlive).
          - intros m. simpl. rewrite Hmem. split.
            + intros [Heq|[Hlive HnP]].
              * subst m. split; [exact deq_live_n|].
                intro HP. apply Hpset0 in HP. exact (proj2 Hcomp HP).
              * apply poq_mark_garbage_live in Hlive. split; [exact (proj1 Hlive)|exact HnP].
            + intros [Hlive HnP].
              destruct (Nat.eq_dec n m) as [Heq|Hneq]; [now left|].
              right. split; [|exact HnP].
              apply poq_mark_garbage_live. split; [exact Hlive|congruence]. }
        assert (Hq0 : values_of s (n :: N') (v :: q')).
        { constructor; [exact Hv|exact Hq]. }
        destruct (I_state_graph _ _ HI P' Hpset0 (n :: N') Htopo0 (v :: q') Hq0)
          as [π [Hposs Htok]].
        exists π. split; [exact Hposs|]. split.
        - exists N'. split; [|exists (v :: q'); split; [exact Hq0|reflexivity]].
          eapply topo_ext; [|exact Htopo0].
          intros m. unfold lin_set. split.
          + intros [Hlive HnP]. split; [exact Hlive|].
            intros (β & v' & Hβ & Hinv).
            destruct (Htok β m Hβ) as (v'' & Hv'' & Hret & _).
            rewrite Hret in Hinv; [discriminate|exact HnP].
          + intros [Hlive Hnot]. split; [exact Hlive|]. intros HP.
            destruct (Hpset0 m HP) as [β Hβ].
            destruct (Htok β m Hβ) as (v' & Hv' & _ & Hinv).
            apply Hnot. exists β, v'. split; [exact Hβ|]. apply Hinv. exact HP.
        - intros β m Hβm.
          pose proof (deq_pending_not_alpha β m Hβm) as Hneq.
          destruct (Htok β m Hβm) as (vβ & Hvβ & Hret & Hinv).
          exists vβ. split; [exact Hvβ|]. rewrite deq_find_other by exact Hneq.
          split; [exact Hret|exact Hinv].
      Qed.

      Lemma deq_nonempty :
        exists q π,
          Δ (Idle (v :: q)) π /\
          (exists N', justified s (Idle (v :: q)) π (n :: N')).
      Proof.
        assert (Hwf' : poq_wf s') by (apply poq_mark_garbage_wf; assumption).
        assert (Hpset : pending_set s' (fun _ : VertexId => False)) by (intros m Hm; contradiction).
        destruct (topo_live_exists s' (fun _ => False) Hwf') as [N' Htopo].
        destruct (values_exist s' N') as [q' Hq].
        { intros m Hm. eapply topo_vertices; [|exact Htopo|exact Hm].
          intros m' [Hm' _]. apply live_vertex. exact Hm'. }
        destruct (deq_witness _ N' q' Hpset Htopo Hq) as (π & Hposs & Hjust & _).
        exists q', π. auto.
      Qed.

      Hypothesis HΔ' : forall ρ' π', Δ' ρ' π' <->
        exists q π,
          Δ (Idle (v :: q)) π /\
          (exists N', justified s (Idle (v :: q)) π (n :: N')) /\
          ρ' = Idle q /\
          π' = πf π.

      Lemma deq_I_graph : I_graph s' Δ'.
      Proof.
        intros P' Hpset N' Htopo q' Hq.
        destruct (deq_witness P' N' q' Hpset Htopo Hq) as (π & Hposs & Hjust & Htok).
        eexists. split; [|exact Htok].
        apply HΔ'. exists q', π. repeat split; auto.
      Qed.

      Lemma deq_I_pending : I_pending s' Δ'.
      Proof.
        intros β m Hβm.
        pose proof (deq_pending_not_alpha β m Hβm) as Hneq.
        destruct (I_state_pending _ _ HI β m Hβm) as (vβ & Hvβ & Htok).
        exists vβ. split; [exact Hvβ|].
        intros ρ' π' Hposs'. apply HΔ' in Hposs'.
        destruct Hposs' as (q & π & Hposs & _ & -> & ->).
        rewrite deq_find_other by exact Hneq. exact (Htok _ _ Hposs).
      Qed.

      Lemma deq_I_state : I_state s' Δ'.
      Proof.
        split; [apply poq_mark_garbage_wf; assumption|].
        split; [apply deq_I_graph|apply deq_I_pending].
      Qed.
    End Deq.

    (** * The framework's token steps preserve [I] *)

    Lemma ginv_I_state s (Δ : config) t (f : Sig.op (li_sig F)) :
      I_state s Δ ->
      (forall ρ π, Δ ρ π -> TMap.find t π = None) ->
      I_state s (ac_inv Δ t f).
    Proof.
      intros HI Hnone.
      assert (Htnone : TMap.find t (poq_pending s) = None).
      { destruct (TMap.find t (poq_pending s)) as [n|] eqn:Hn; [|reflexivity].
        exfalso. destruct (ac_nonempty Δ) as (ρ & π & Hposs).
        destruct (pending_has_token _ _ _ _ _ _ HI Hn Hposs) as [ls Hls].
        rewrite (Hnone _ _ Hposs) in Hls. discriminate. }
      destruct HI as [Hwf [Hgraph Hpend]].
      split; [exact Hwf|]. split.
      - intros P' Hpset N Htopo q Hq.
        destruct (Hgraph P' Hpset N Htopo q Hq) as [π [Hposs Htok]].
        exists (TMap.add t (ls_inv f) π). split; [constructor; exact Hposs|].
        intros β m Hβm. destruct (Htok β m Hβm) as (vβ & Hvβ & Hret & Hinv).
        exists vβ. split; [exact Hvβ|].
        rewrite TMap.gso by (intro; subst; congruence). auto.
      - intros β m Hβm. destruct (Hpend β m Hβm) as (vβ & Hvβ & Htok).
        exists vβ. split; [exact Hvβ|].
        intros ρ π Hposs. inversion Hposs; subst.
        rewrite TMap.gso by (intro; subst; congruence). exact (Htok _ _ Hposs0).
    Qed.

    Lemma gret_I_state s (Δ : config) t :
      I_state s Δ ->
      TMap.find t (poq_pending s) = None ->
      I_state s (ac_res Δ t).
    Proof.
      intros HI Htnone.
      destruct HI as [Hwf [Hgraph Hpend]].
      split; [exact Hwf|]. split.
      - intros P' Hpset N Htopo q Hq.
        destruct (Hgraph P' Hpset N Htopo q Hq) as [π [Hposs Htok]].
        exists (TMap.remove t π). split; [constructor; exact Hposs|].
        intros β m Hβm. destruct (Htok β m Hβm) as (vβ & Hvβ & Hret & Hinv).
        exists vβ. split; [exact Hvβ|].
        rewrite TMap.gro by (intro; subst; congruence). auto.
      - intros β m Hβm. destruct (Hpend β m Hβm) as (vβ & Hvβ & Htok).
        exists vβ. split; [exact Hvβ|].
        intros ρ π Hposs. inversion Hposs; subst.
        rewrite TMap.gro by (intro; subst; congruence). exact (Htok _ _ Hposs0).
    Qed.

    (** * Abstract-configuration constructors for the updates *)

    (** The image of [Δc] under the closure (branches (a) and (b)). *)
    Variant ac_lin_prop s (Δc : config) : @AbstractConfigProp _ (li_lts F) :=
    | ACLin ρ π ρ' π' (Hposs : Δc ρ π) (Hlin : lin_closure s ρ π ρ' π') :
        ac_lin_prop s Δc ρ' π'.

    Program Definition ac_lin s (Δc : config) : config :=
      {| ac_active := ac_active Δc; ac_prop := ac_lin_prop s Δc |}.
    Next Obligation.
      destruct (ac_nonempty Δc) as (ρ & π & Hposs).
      exists ρ, π. econstructor; [exact Hposs|constructor].
    Qed.
    Next Obligation.
      inversion H; subst.
      eapply domain_equiv_trans.
      - apply domain_equiv_symm. eapply poss_steps_domain.
        eapply lin_closure_poss_steps. exact Hlin.
      - eapply ac_domain. exact Hposs.
    Qed.

    Lemma ac_lin_subset_steps s Δc :
      ac_subset (ac_lin s Δc) (ac_steps Δc).
    Proof.
      intros ρ' π' Hposs'. inversion Hposs'; subst.
      econstructor; [exact Hposs|]. eapply lin_closure_poss_steps. exact Hlin.
    Qed.

    Lemma ac_lin_iff s Δc ρ' π' :
      ac_lin s Δc ρ' π' <-> exists ρ π, Δc ρ π /\ lin_closure s ρ π ρ' π'.
    Proof.
      split.
      - intros H. inversion H; subst. eauto.
      - intros (ρ & π & Hposs & Hlin). econstructor; eauto.
    Qed.

    (** Selecting possibilities and stepping each of them. *)
    Variant ac_select_prop (Δc : config)
        (sel : abstract_state -> tmap lin_state -> Prop)
        (ρf : abstract_state -> abstract_state)
        (πf : tmap lin_state -> tmap lin_state) :
        @AbstractConfigProp _ (li_lts F) :=
    | ACSelect ρ π (Hposs : Δc ρ π) (Hsel : sel ρ π) :
        ac_select_prop Δc sel ρf πf (ρf ρ) (πf π).

    Program Definition ac_select (Δc : config)
        (sel : abstract_state -> tmap lin_state -> Prop)
        (ρf : abstract_state -> abstract_state)
        (πf : tmap lin_state -> tmap lin_state)
        (Hsteps : forall ρ π, Δc ρ π -> sel ρ π ->
          poss_steps (PossOk ρ π) (PossOk (ρf ρ) (πf π)))
        (Hne : exists ρ π, Δc ρ π /\ sel ρ π) : config :=
      {| ac_active := ac_active Δc; ac_prop := ac_select_prop Δc sel ρf πf |}.
    Next Obligation.
      destruct Hne as (ρ & π & Hposs & Hsel).
      exists (ρf ρ), (πf π). constructor; assumption.
    Qed.
    Next Obligation.
      inversion H; subst.
      eapply domain_equiv_trans.
      - apply domain_equiv_symm. eapply poss_steps_domain. eapply Hsteps; eassumption.
      - eapply ac_domain. eassumption.
    Qed.

    Lemma ac_select_subset_steps Δc sel ρf πf Hsteps Hne :
      ac_subset (ac_select Δc sel ρf πf Hsteps Hne) (ac_steps Δc).
    Proof.
      intros ρ' π' Hposs'. inversion Hposs'; subst.
      econstructor; [exact Hposs|]. apply Hsteps; assumption.
    Qed.

    Lemma ac_select_iff Δc sel ρf πf Hsteps Hne ρ' π' :
      ac_select Δc sel ρf πf Hsteps Hne ρ' π' <->
      exists ρ π, Δc ρ π /\ sel ρ π /\ ρ' = ρf ρ /\ π' = πf π.
    Proof.
      split.
      - intros H. inversion H; subst. do 2 eexists.
        repeat split; first [eassumption|reflexivity].
      - intros (ρ & π & Hposs & Hsel & -> & ->). constructor; assumption.
    Qed.

    (** * Shapes of the underlay steps *)

    (** Thread events carry dependent results; the value of a response is
        read back through a projection rather than by [injection]. *)
    Definition enq_res_value (ev : @Event (li_sig E)) : option A :=
      match ev with
      | ResEv op r =>
          match op return (Sig.ar op -> option A) with
          | poq_enq v => fun _ => Some v
          | poq_deq => fun _ => None
          end r
      | InvEv _ => None
      end.

    Definition deq_res_value (ev : @Event (li_sig E)) : option A :=
      match ev with
      | ResEv op r =>
          match op return (Sig.ar op -> option A) with
          | poq_deq => fun x => Some x
          | poq_enq _ => fun _ => None
          end r
      | InvEv _ => None
      end.

    Ltac invert_poq_step Hstep :=
      simpl in Hstep;
      inversion Hstep; subst;
      match goal with
      | H : Build_ThreadEvent _ _ = Build_ThreadEvent _ _ |- _ =>
          first [ discriminate H
                | pose proof (f_equal te_tid H) as Hact; simpl in Hact; subst;
                  pose proof (f_equal te_ev H) as Hev; simpl in Hev; clear H;
                  first [ pose proof (f_equal enq_res_value Hev) as Hval; simpl in Hval;
                          first [ discriminate Hval | injection Hval as Hval; subst ]
                        | pose proof (f_equal deq_res_value Hev) as Hval; simpl in Hval;
                          first [ discriminate Hval | injection Hval as Hval; subst ]
                        | try (injection Hev; clear Hev; intros);
                          repeat match goal with
                          | Hx : poq_enq _ = poq_enq _ |- _ =>
                              injection Hx; clear Hx; intros
                          | Hx : ?x = ?y |- _ => is_var y; subst y
                          | Hx : ?x = ?y |- _ => is_var x; subst x
                          end ] ]
      end.

    Lemma poq_enq_inv_shape α (v : A) (σ σ' : concrete_state) :
      Step (li_lts E) (Build_ThreadEvent α (InvEv (poq_enq v))) σ σ' ->
      exists s,
        σ = POQReady s /\
        TMap.find α (poq_pending s) = None /\
        σ' = POQReady (poq_start_enq α v s).
    Proof.
      intros Hstep. invert_poq_step Hstep.
      eexists. split; [reflexivity|]. split; [eassumption|reflexivity].
    Qed.

    Lemma poq_enq_res_shape α (v : A) (σ σ' : concrete_state) :
      Step (li_lts E) (Build_ThreadEvent α (ResEv (poq_enq v) tt)) σ σ' ->
      exists s n,
        σ = POQReady s /\
        TMap.find α (poq_pending s) = Some n /\
        σ' = POQReady (poq_finish_enq α s).
    Proof.
      intros Hstep. invert_poq_step Hstep.
      do 2 eexists. split; [reflexivity|]. split; [eassumption|reflexivity].
    Qed.

    Lemma poq_deq_inv_shape α (σ σ' : concrete_state) :
      Step (li_lts E) (Build_ThreadEvent α (InvEv poq_deq)) σ σ' ->
      exists s, σ = POQReady s /\ σ' = POQAtomic s α poq_deq.
    Proof.
      intros Hstep. invert_poq_step Hstep. eexists. split; reflexivity.
    Qed.

    Lemma poq_deq_res_shape α (v : A) (σ σ' : concrete_state) :
      Step (li_lts E) (Build_ThreadEvent α (ResEv poq_deq v)) σ σ' ->
      exists s n,
        σ = POQAtomic s α poq_deq /\
        poq_minimal s n /\ poq_complete s n /\ poq_vertices s n = Some v /\
        σ' = POQReady (poq_mark_garbage n s).
    Proof.
      intros Hstep. invert_poq_step Hstep.
      do 2 eexists. split; [reflexivity|]. split; [eassumption|].
      split; [eassumption|]. split; [eassumption|reflexivity].
    Qed.

    (** * What other threads' steps preserve *)

    Definition other_facts (obs : tid) (w w' : proof_state) : Prop :=
      TMap.find obs (poq_pending (graph_of w)) =
        TMap.find obs (poq_pending (graph_of w')) /\
      (poq_wf (graph_of w) ->
        forall n v, poq_vertices (graph_of w) n = Some v ->
          poq_vertices (graph_of w') n = Some v) /\
      ((exists s0 op, SetPossState.σ w = POQAtomic s0 obs op) ->
        SetPossState.σ w' = SetPossState.σ w) /\
      (TMap.find obs (poq_pending (graph_of w)) = None ->
        forall ρ' π', SetPossState.Δ w' ρ' π' ->
          exists ρ π, SetPossState.Δ w ρ π /\
            TMap.find obs π' = TMap.find obs π) /\
      (exists ρ' π' ρ π,
        SetPossState.Δ w' ρ' π' /\ SetPossState.Δ w ρ π /\
        (TMap.find obs π = None <-> TMap.find obs π' = None)).

    Lemma some_none_iff (x y : lin_state) :
      Some x = None <-> Some y = None.
    Proof. split; discriminate. Qed.

    Lemma G_other_facts actor w w' obs :
      obs <> actor -> G actor w w' -> other_facts obs w w'.
    Proof.
      intros Hneq HG.
      destruct HG as [HG|[HG|[HG|HG]]].
      - destruct HG as [s v w w' Hσ Hnone Htok Hσ' HΔ'].
        unfold other_facts, graph_of. rewrite Hσ, Hσ'. cbn [poq_payload].
        split; [|split; [|split; [|split]]].
        + change (poq_pending (poq_start_enq actor v s))
            with (TMap.add actor (poq_next s) (poq_pending s)).
          rewrite TMap.gso by congruence. reflexivity.
        + intros Hwf n v0 Hv0. rewrite poq_start_enq_vertices; [exact Hv0|].
          intros ->. apply (poq_next_not_vertex s Hwf). unfold poq_is_vertex. congruence.
        + intros [s0 [op Heq]]. discriminate.
        + intros Hobs ρ' π' Hposs'. apply HΔ' in Hposs'.
          destruct Hposs' as (ρ & π & Hposs & Hclos).
          exists ρ, π. split; [exact Hposs|].
          eapply lin_closure_find_nopending; [exact Hclos|].
          change (poq_pending (poq_start_enq actor v s))
            with (TMap.add actor (poq_next s) (poq_pending s)).
          rewrite TMap.gso by congruence. exact Hobs.
        + destruct (ac_nonempty (SetPossState.Δ w')) as (ρ' & π' & Hposs').
          pose proof Hposs' as Hposs''. apply HΔ' in Hposs''.
          destruct Hposs'' as (ρ & π & Hposs & Hclos).
          exists ρ', π', ρ, π. split; [exact Hposs'|]. split; [exact Hposs|].
          destruct (lin_closure_find _ _ _ _ _ obs Hclos)
            as [Hsame|[n0 [v0 [Hn0 [Hv0 Hret]]]]].
          * rewrite Hsame. reflexivity.
          * rewrite Hret.
            destruct (TMap.find obs π) as [x|] eqn:Hx.
            -- apply some_none_iff.
            -- exfalso.
               pose proof (lin_closure_find_noninv _ _ _ _ _ obs Hclos) as Hkeep.
               assert (Hnoinv : forall v1, TMap.find obs π <> Some (enq_inv_token v1)).
               { intros v1 Hbad. pose proof (eq_trans (eq_sym Hx) Hbad) as Habs.
                 discriminate Habs. }
               pose proof (eq_trans (eq_sym Hret) (eq_trans (Hkeep Hnoinv) Hx)) as Habs.
               discriminate Habs.
      - destruct HG as [s n v w w' Hσ Hn Hv Hσ' HΔ'].
        unfold other_facts, graph_of. rewrite Hσ, Hσ'. cbn [poq_payload].
        split; [|split; [|split; [|split]]].
        + change (poq_pending (poq_finish_enq actor s))
            with (TMap.remove actor (poq_pending s)).
          rewrite TMap.gro by congruence. reflexivity.
        + intros _ n0 v0 Hv0. exact Hv0.
        + intros [s0 [op Heq]]. discriminate.
        + intros _ ρ' π' Hposs'. apply HΔ' in Hposs'. destruct Hposs' as [Hposs _].
          exists ρ', π'. split; [exact Hposs|reflexivity].
        + destruct (ac_nonempty (SetPossState.Δ w')) as (ρ' & π' & Hposs').
          pose proof Hposs' as Hposs''. apply HΔ' in Hposs''. destruct Hposs'' as [Hposs _].
          exists ρ', π', ρ', π'. repeat split; auto.
      - destruct HG as [s n v w w' Hσ Hmin Hcomp Hv Hα Hσ' HΔ'].
        unfold other_facts, graph_of. rewrite Hσ, Hσ'. cbn [poq_payload].
        split; [|split; [|split; [|split]]].
        + reflexivity.
        + intros _ n0 v0 Hv0. exact Hv0.
        + intros [s0 [op Heq]]. injection Heq as _ Heq _. congruence.
        + intros _ ρ' π' Hposs'. apply HΔ' in Hposs'.
          destruct Hposs' as (q & π & Hposs & _ & -> & ->).
          exists (Idle (v :: q)), π. split; [exact Hposs|].
          rewrite find_add_add, TMap.gso by congruence. reflexivity.
        + destruct (ac_nonempty (SetPossState.Δ w')) as (ρ' & π' & Hposs').
          pose proof Hposs' as Hposs''. apply HΔ' in Hposs''.
          destruct Hposs'' as (q & π & Hposs & _ & -> & ->).
          exists (Idle q), (TMap.add actor (deq_ret_token v) (TMap.add actor deq_lini_token π)),
            (Idle (v :: q)), π.
          split; [exact Hposs'|]. split; [exact Hposs|].
          rewrite find_add_add, TMap.gso by congruence. reflexivity.
      - destruct HG as [s w w' Hσ Hσ' HΔ'].
        unfold other_facts, graph_of. rewrite Hσ, Hσ', HΔ'. cbn [poq_payload].
        split; [reflexivity|]. split; [intros; assumption|]. split.
        + intros [s0 [op Heq]]. discriminate.
        + split.
          * intros _ ρ' π' Hposs'. exists ρ', π'. split; [exact Hposs'|reflexivity].
          * destruct (ac_nonempty (SetPossState.Δ w)) as (ρ & π & Hposs).
            exists ρ, π, ρ, π. repeat split; auto.
    Qed.

    Lemma GINV_other_facts actor w w' obs :
      obs <> actor -> GINV actor w w' -> other_facts obs w w'.
    Proof.
      intros Hneq [f [Hσ [Hnone Hequiv]]].
      unfold other_facts, graph_of. rewrite Hσ.
      split; [reflexivity|]. split; [intros; assumption|]. split; [intros; reflexivity|].
      split.
      - intros _ ρ' π' Hposs'. apply Hequiv in Hposs'. inversion Hposs'; subst.
        exists ρ', π. split; [exact Hposs|]. rewrite TMap.gso by congruence. reflexivity.
      - destruct (ac_nonempty (SetPossState.Δ w)) as (ρ & π & Hposs).
        exists ρ, (TMap.add actor (ls_inv f) π), ρ, π. split.
        + apply Hequiv. constructor. exact Hposs.
        + split; [exact Hposs|]. rewrite TMap.gso by congruence. reflexivity.
    Qed.

    Lemma GRET_other_facts actor w w' obs :
      obs <> actor -> GRET actor w w' -> other_facts obs w w'.
    Proof.
      intros Hneq [f [ret [Hσ [Hall Hequiv]]]].
      unfold other_facts, graph_of. rewrite Hσ.
      split; [reflexivity|]. split; [intros; assumption|]. split; [intros; reflexivity|].
      split.
      - intros _ ρ' π' Hposs'. apply Hequiv in Hposs'. inversion Hposs'; subst.
        exists ρ', π. split; [exact Hposs|]. rewrite TMap.gro by congruence. reflexivity.
      - destruct (ac_nonempty (SetPossState.Δ w)) as (ρ & π & Hposs).
        exists ρ, (TMap.remove actor π), ρ, π. split.
        + apply Hequiv. constructor. exact Hposs.
        + split; [exact Hposs|]. rewrite TMap.gro by congruence. reflexivity.
    Qed.

    Lemma R_other_facts obs w w' :
      R obs w w' -> other_facts obs w w'.
    Proof.
      intros [[actor [Hneq HG]]|[[actor [Hneq Hinv]]|[[actor [Hneq Hret]]|Heq]]].
      - eapply G_other_facts; eauto.
      - eapply GINV_other_facts; eauto.
      - eapply GRET_other_facts; eauto.
      - subst w'. unfold other_facts.
        split; [reflexivity|]. split; [intros; assumption|]. split; [intros; reflexivity|].
        split.
        + intros _ ρ' π' Hposs'. exists ρ', π'. split; [exact Hposs'|reflexivity].
        + destruct (ac_nonempty (SetPossState.Δ w)) as (ρ & π & Hposs).
          exists ρ, π, ρ, π. repeat split; auto.
    Qed.

    (** * Stability *)

    Lemma I_stable t : AssertionsSet.A.Stable (R t) I I.
    Proof. apply AssertionsSet.A.Stable_invariant. Qed.

    Lemma alin_stable_core t (ls : lin_state) w w' :
      R t w w' ->
      TMap.find t (poq_pending (graph_of w)) = None ->
      (forall ρ π, SetPossState.Δ w ρ π -> TMap.find t π = Some ls) ->
      forall ρ' π', SetPossState.Δ w' ρ' π' -> TMap.find t π' = Some ls.
    Proof.
      intros HR Hnone Hall ρ' π' Hposs'.
      destruct (R_other_facts t w w' HR) as (_ & _ & _ & Htok & _).
      destruct (Htok Hnone _ _ Hposs') as (ρ & π & Hposs & Heq).
      rewrite Heq. now apply Hall with ρ.
    Qed.

    Lemma active_stable t op :
      AssertionsSet.A.Stable (R t) I (Active t op).
    Proof.
      intros w' [[w [[HI Hlin] HR]] HI']. split; [exact HI'|].
      intros ρ' π' Hposs'.
      eapply alin_stable_core; [exact HR| |exact Hlin|exact Hposs'].
      eapply alin_inv_no_pending; [exact HI|exact Hlin].
    Qed.

    Lemma completed_stable t op ret :
      AssertionsSet.A.Stable (R t) I (Completed t op ret).
    Proof.
      intros w' [[w [[HI [Hlin HnoP]] HR]] HI']. split; [exact HI'|].
      destruct (R_other_facts t w w' HR) as (Hpend & _ & _ & _ & _).
      split.
      - intros ρ' π' Hposs'.
        eapply alin_stable_core; [exact HR|exact HnoP|exact Hlin|exact Hposs'].
      - unfold NoPending. rewrite <- Hpend. exact HnoP.
    Qed.

    Lemma enq_pending_stable t v :
      AssertionsSet.A.Stable (R t) I (EnqPending t v).
    Proof.
      intros w' [[w [[HI [n [Hn Hv]]] HR]] HI']. split; [exact HI'|].
      destruct (R_other_facts t w w' HR) as (Hpend & Hvert & _ & _ & _).
      exists n. split.
      - rewrite <- Hpend. exact Hn.
      - apply Hvert; [exact (I_state_wf _ _ HI)|exact Hv].
    Qed.

    Lemma deq_atomic_stable t :
      AssertionsSet.A.Stable (R t) I (DeqAtomic t).
    Proof.
      intros w' [[w [[Hactive [s Hσ]] HR]] HI']. split.
      - apply (active_stable t q_deq). split; [|exact HI']. exists w. split; assumption.
      - destruct (R_other_facts t w w' HR) as (_ & _ & Hctl & _ & _).
        exists s. rewrite Hctl; [exact Hσ|]. exists s, poq_deq. exact Hσ.
    Qed.

    Lemma active_entails_I t op : ⊨ Active t op ==>> I.
    Proof. intros w [HI _]. exact HI. Qed.

    Lemma completed_entails_I t op ret : ⊨ Completed t op ret ==>> I.
    Proof. intros w [HI _]. exact HI. Qed.

    Lemma enq_pending_entails_I t v : ⊨ EnqPending t v ==>> I.
    Proof. intros w [HI _]. exact HI. Qed.

    Lemma deq_atomic_entails_I t : ⊨ DeqAtomic t ==>> I.
    Proof. intros w [[HI _] _]. exact HI. Qed.

    (** * Rely/guarantee validity and parallel compatibility *)

    Lemma valid_rg t :
      RGISimulationSet.RGISimulation.ValidRGI (R t) (G t) I t.
    Proof.
      constructor. intros w w' HR HI'.
      destruct (R_other_facts t w w' HR)
        as (_ & _ & _ & _ & (ρ' & π' & ρ & π & Hposs' & Hposs & Hiff)).
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
      destruct Hrel as [HG | [[Hinv | Hret] | Hid]].
      - left. exists t1. split; [congruence|exact HG].
      - right. left. exists t1. split; [congruence|exact Hinv].
      - right. right. left. exists t1. split; [congruence|exact Hret].
      - right. right. right. exact Hid.
    Qed.

    (** * Overlay invocation and return *)

    Lemma set_ginv_exposes_active t op :
      ⊨ AssertionsSet.A.ComposeA I (AssertionsSet.Ginv t op) ==>> Active t op.
    Proof.
      intros w [pre [HIpre [Hσ [Hnone Hequiv]]]].
      destruct pre as [σ0 Δ0], w as [σ1 Δ1]; simpl in *. subst σ1.
      split.
      - unfold I, graph_of in *. simpl in *.
        eapply I_state_equiv; [intros ρ π; symmetry; apply Hequiv|].
        apply ginv_I_state; assumption.
      - intros ρ π Hposs. apply Hequiv in Hposs. eapply ac_inv_find_eq. exact Hposs.
    Qed.

    Lemma set_gret_closes_completed t op ret :
      ⊨ AssertionsSet.A.ComposeA (Completed t op ret)
          (AssertionsSet.Gret t op ret) ==>> I.
    Proof.
      intros w [pre [[HIpre [Hlin HnoP]] [Hσ [Hall Hequiv]]]].
      destruct pre as [σ0 Δ0], w as [σ1 Δ1]; simpl in *. subst σ1.
      unfold I, graph_of, NoPending in *. simpl in *.
      eapply I_state_equiv; [intros ρ π; symmetry; apply Hequiv|].
      apply gret_I_state; assumption.
    Qed.

    Lemma completed_has_return_token t op ret (σ : concrete_state) (Δ : config) :
      Completed t op ret (SetPossState.Build_ProofStateSet _ _ _ _ σ Δ) ->
      forall ρ π, Δ ρ π -> TMap.find t π = Some (ls_linr op ret).
    Proof. intros [_ [Hlin _]]. exact Hlin. Qed.

    (** The partial-order queue is error-free. *)
    Lemma no_error (P : assertion) (m : Sig.op (li_sig E)) t :
      ⊨ P ==>> AssertionsSet.A.ANoError (Build_ThreadEvent t (InvEv m)).
    Proof. intros w _ Herr. simpl in Herr. exact Herr. Qed.

    (** * The four event updates *)

    Lemma enq_inv_update α v :
      AssertionsSet.PUpdate (G α)
        (Build_ThreadEvent α (InvEv (poq_enq v)))
        (Active α (q_enq v)) (EnqPending α v).
    Proof.
      intros σ Δ [HI Hlin] σ' Hstep.
      destruct (poq_enq_inv_shape α v σ σ' Hstep) as (s & -> & Hnone & ->).
      unfold I, graph_of in HI. simpl in HI.
      assert (Htok : forall ρ π, Δ ρ π -> TMap.find α π = Some (enq_inv_token v)).
      { intros ρ π Hposs. exact (Hlin ρ π Hposs). }
      assert (HΔ' : forall ρ' π', ac_lin (poq_start_enq α v s) Δ ρ' π' <->
        exists ρ π, Δ ρ π /\ lin_closure (poq_start_enq α v s) ρ π ρ' π').
      { intros ρ' π'. apply ac_lin_iff. }
      pose proof (ei_I_state s α v Δ _ HI Hnone Htok HΔ') as HI'.
      exists (ac_lin (poq_start_enq α v s) Δ). split; [apply ac_lin_subset_steps|].
      split.
      - split; [exact HI'|].
        exists (poq_next s). unfold graph_of. cbn [SetPossState.σ poq_payload].
        split; [apply TMap.gss|apply poq_start_enq_vertex_new].
      - left. apply (g_enq_inv α s v); simpl; auto.
    Qed.

    Lemma enq_res_update α v :
      AssertionsSet.PUpdate (G α)
        (Build_ThreadEvent α (ResEv (poq_enq v) tt))
        (EnqPending α v) (Completed α (q_enq v) tt).
    Proof.
      intros σ Δ [HI [n [Hn Hv]]] σ' Hstep.
      destruct (poq_enq_res_shape α v σ σ' Hstep) as (s & n0 & -> & Hn0 & ->).
      unfold I, graph_of in HI, Hn, Hv. simpl in HI, Hn, Hv.
      rewrite Hn in Hn0. injection Hn0 as <-.
      pose proof (er_nonempty s α n v Δ HI Hn Hv) as Hne.
      set (sel := fun (_ : abstract_state) π => TMap.find α π = Some (enq_ret_token v)).
      assert (Hsteps : forall ρ π, Δ ρ π -> sel ρ π ->
        poss_steps (PossOk ρ π) (PossOk ((fun ρ => ρ) ρ) ((fun π => π) π))).
      { intros ρ π _ _. apply rt_refl. }
      assert (Hne' : exists ρ π, Δ ρ π /\ sel ρ π).
      { destruct Hne as (ρ & π & Hposs & Hret). exists ρ, π. split; assumption. }
      set (Δ' := ac_select Δ sel (fun ρ => ρ) (fun π => π) Hsteps Hne').
      assert (HΔ' : forall ρ π, Δ' ρ π <-> Δ ρ π /\ TMap.find α π = Some (enq_ret_token v)).
      { intros ρ π. unfold Δ'. rewrite ac_select_iff. split.
        - intros (ρ0 & π0 & Hposs & Hsel & -> & ->). split; assumption.
        - intros [Hposs Hret]. exists ρ, π. repeat split; assumption. }
      pose proof (er_I_state s α n v Δ Δ' HI Hn Hv HΔ') as HI'.
      exists Δ'. split; [apply ac_select_subset_steps|].
      split.
      - split; [exact HI'|]. split.
        + intros ρ π Hposs. apply HΔ' in Hposs. exact (proj2 Hposs).
        + unfold NoPending, graph_of. simpl. apply TMap.grs.
      - right. left. apply (g_enq_ret α s n v); simpl; auto.
    Qed.

    Lemma deq_inv_update α :
      AssertionsSet.PUpdate (G α)
        (Build_ThreadEvent α (InvEv poq_deq))
        (Active α q_deq) (DeqAtomic α).
    Proof.
      intros σ Δ Hactive σ' Hstep.
      destruct (poq_deq_inv_shape α σ σ' Hstep) as (s & -> & ->).
      exists Δ. split; [apply ac_steps_refl|].
      split.
      - split; [exact Hactive|]. exists s. reflexivity.
      - right. right. right. apply (g_control_enter α s); reflexivity.
    Qed.

    Lemma deq_res_update α v :
      AssertionsSet.PUpdate (G α)
        (Build_ThreadEvent α (ResEv poq_deq v))
        (DeqAtomic α) (Completed α q_deq v).
    Proof.
      intros σ Δ [[HI Hlin] [s0 Hσ]] σ' Hstep.
      destruct (poq_deq_res_shape α v σ σ' Hstep)
        as (s & n & Hσs & Hmin & Hcomp & Hv & Hσ'). subst σ σ'.
      unfold I, graph_of in HI. simpl in HI.
      assert (Hα : forall ρ π, Δ ρ π -> TMap.find α π = Some deq_inv_token).
      { intros ρ π Hposs. exact (Hlin ρ π Hposs). }
      set (sel := fun ρ π =>
        exists q, ρ = Idle q /\ (exists q', q = v :: q') /\
          (exists N', justified s ρ π (n :: N'))).
      set (ρf := fun ρ : abstract_state =>
        match ρ with Idle (_ :: q) => Idle q | _ => ρ end).
      set (πf := fun π => TMap.add α (deq_ret_token v) (TMap.add α deq_lini_token π)).
      assert (Hsteps : forall ρ π, Δ ρ π -> sel ρ π ->
        poss_steps (PossOk ρ π) (PossOk (ρf ρ) (πf π))).
      { intros ρ π Hposs (q & Hρ & [q' Hq'] & _). subst ρ q. unfold ρf, πf. simpl.
        eapply rt_trans.
        - apply rt_step.
          eapply (@ps_inv _ (li_lts F) α q_deq (Idle (v :: q'))
            (Pending (v :: q') α q_deq) π).
          + apply queue_deq_inv_step.
          + exact (Hα _ _ Hposs).
        - apply rt_step.
          eapply (@ps_ret _ (li_lts F) α q_deq v (Pending (v :: q') α q_deq)
            (Idle q')).
          + apply queue_deq_res_step.
          + apply TMap.gss. }
      assert (Hne : exists ρ π, Δ ρ π /\ sel ρ π).
      { destruct (deq_nonempty s α n v Δ HI Hmin Hcomp Hv Hα) as (q & π & Hposs & Hjust).
        exists (Idle (v :: q)), π. split; [exact Hposs|].
        exists (v :: q). split; [reflexivity|]. split; [eauto|exact Hjust]. }
      set (Δ' := ac_select Δ sel ρf πf Hsteps Hne).
      assert (HΔ' : forall ρ' π', Δ' ρ' π' <->
        exists q π,
          Δ (Idle (v :: q)) π /\
          (exists N', justified s (Idle (v :: q)) π (n :: N')) /\
          ρ' = Idle q /\
          π' = TMap.add α (deq_ret_token v) (TMap.add α deq_lini_token π)).
      { intros ρ' π'. unfold Δ'. rewrite ac_select_iff. split.
        - intros (ρ & π & Hposs & (q & Hρ & [q' Hq'] & Hjust) & -> & ->).
          subst ρ q. exists q', π. repeat split; assumption.
        - intros (q & π & Hposs & Hjust & -> & ->).
          exists (Idle (v :: q)), π. split; [exact Hposs|]. split; [|split; reflexivity].
          exists (v :: q). split; [reflexivity|]. split; [eauto|exact Hjust]. }
      pose proof (deq_I_state s α n v Δ Δ' HI Hmin Hcomp Hv Hα HΔ') as HI'.
      exists Δ'. split; [apply ac_select_subset_steps|].
      split.
      - simpl. split; [exact HI'|]. split.
        + intros ρ' π' Hposs'. apply HΔ' in Hposs'.
          destruct Hposs' as (q & π & _ & _ & -> & ->). apply TMap.gss.
        + unfold NoPending, graph_of. simpl.
          eapply alin_inv_no_pending; [exact HI|exact Hα].
      - right. right. left. apply (g_deq α s n v); simpl; auto.
    Qed.

    (** * Method outlines *)

    Lemma enq_triple t v :
      [li_lts E, li_lts F, R t, G t, I, t] ⊢
        {{ Active t (q_enq v) }} enq_impl v t
        {{ fun _ => Completed t (q_enq v) tt }}.
    Proof.
      unfold enq_impl.
      eapply SetLogic.provable_vis_safe with
        (P' := EnqPending t v)
        (Q' := fun _ => Completed t (q_enq v) tt).
      - apply no_error.
      - apply enq_pending_entails_I.
      - intros _. apply completed_entails_I.
      - apply enq_pending_stable.
      - intros _. apply completed_stable.
      - apply enq_inv_update.
      - intros []. apply enq_res_update.
      - intros []. eapply SetLogic.provable_ret_safe.
        + apply ImplRefl.
        + apply completed_entails_I.
        + apply completed_stable.
    Qed.

    Lemma deq_triple t :
      [li_lts E, li_lts F, R t, G t, I, t] ⊢
        {{ Active t q_deq }} deq_impl t
        {{ fun v => Completed t q_deq v }}.
    Proof.
      unfold deq_impl.
      eapply SetLogic.provable_vis_safe with
        (P' := DeqAtomic t)
        (Q' := fun v => Completed t q_deq v).
      - apply no_error.
      - apply deq_atomic_entails_I.
      - intros v. apply completed_entails_I.
      - apply deq_atomic_stable.
      - intros v. apply completed_stable.
      - apply deq_inv_update.
      - intros v. apply deq_res_update.
      - intros v. eapply SetLogic.provable_ret_safe.
        + apply ImplRefl.
        + apply completed_entails_I.
        + apply completed_stable.
    Qed.

    (** * Packaging (Theorem 6.7) *)

    Lemma initial_I :
      I (SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          (li_init E) (ac_singleton (li_init F) (@TMap.empty lin_state))).
    Proof.
      unfold I, graph_of. simpl.
      split; [apply empty_poqueue_state_wf|]. split.
      - intros P' Hpset N Htopo q Hq.
        assert (HN : N = nil).
        { destruct N as [|m N]; [reflexivity|]. exfalso.
          destruct Htopo as [_ [_ Hmem]].
          assert (Hm : In m (m :: N)) by (left; reflexivity).
          apply Hmem in Hm. destruct Hm as [[Hv _] _]. apply Hv. reflexivity. }
        subst N. inversion Hq; subst.
        exists (@TMap.empty lin_state). split; [constructor|].
        intros β n Hn. simpl in Hn. rewrite TMap.gempty in Hn. discriminate.
      - intros β n Hn. simpl in Hn. rewrite TMap.gempty in Hn. discriminate.
    Qed.

    Program Definition MQueueLin : layer_implementation_simulation E F :=
      {| li_impl := queue_lin_impl |}.
    Next Obligation.
      eapply SetLogic.soundness with (R := R) (G := G) (I := I).
      - exact valid_rg.
      - exact parallel_compatible.
      - intros t op. destruct op as [v|].
        + exists (Active t (q_enq v)).
          exists (fun _ => Completed t (q_enq v) tt).
          constructor.
          * intros w Hcompose. eapply set_ginv_exposes_active. exact Hcompose.
          * apply active_entails_I.
          * apply active_stable.
          * intros [] w Hcompose. eapply set_gret_closes_completed. exact Hcompose.
          * intros [] σ Δ Hcompleted ρ π Hposs.
            eapply completed_has_return_token; eauto.
          * apply enq_triple.
        + exists (Active t q_deq).
          exists (fun v => Completed t q_deq v).
          constructor.
          * intros w Hcompose. eapply set_ginv_exposes_active. exact Hcompose.
          * apply active_entails_I.
          * apply active_stable.
          * intros v w Hcompose. eapply set_gret_closes_completed. exact Hcompose.
          * intros v σ Δ Hcompleted ρ π Hposs.
            eapply completed_has_return_token; eauto.
          * apply deq_triple.
      - exact initial_I.
    Qed.

    Definition MQueueLinLinearizable :
        layer_implementation_linearizability E F :=
      LISim2LILin MQueueLin.

  End Proof.

  Print Assumptions MQueueLin.

End QueueLinProof.
