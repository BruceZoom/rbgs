Require Import FMapPositive.
Require Import Coq.Lists.List.
Require Import Coq.PArith.PArith.
Require Import Coq.Arith.PeanoNat.
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
Require Import SingletonPossibility.
Require Import CompLinLayer.

Require Import examples.Common.AtomicLTS.
Require Import examples.Common.SwapSpec.
Require Import examples.HWQ.CounterSpec.
Require Import examples.HWQ.POQueueSpec.
Require Import examples.HWQ.HWQueue.


(** Layer 1 of the Herlihy--Wing queue: the implementation over
    [Counter ⊗ SwapArray] refines the partial-order queue
    (docs/proof-details/HWQueueProofDetails.tex, Section 5).

    The proof keeps a single abstract possibility.  Every concrete step
    has at most one abstract counterpart and no choice is ever revised:

      inc returns i          enq-inv with vertex i
      store(i, x)            enq-ret
      swap(i, null) = x      deq-inv then deq-res with value x
      read, swap = null      no abstract step

    The global invariant [I] is the paper's (I1)--(I3): the abstract state
    is well formed, the counter equals the next vertex identifier, and a
    cell holds [x] exactly when its vertex is live, complete and carries
    [x].  One clause is added, [pending_tokens]: a thread with a pending
    enqueue holds the token [⋆enq]; the paper leaves it implicit, but it is
    what makes the precondition [EnqStart] follow from [I] at the concrete
    invocation.

    The thread-local assertions are the paper's [EnqStart], [EnqSlot],
    [EnqDone] and [Scan(α, i, r)]; [Scan] is the loop invariant of the
    inner [for] loop and the heart of the proof.  Stability of [Scan] is
    the state-based replacement of the paper's temporal argument. *)
Module HWQueueProof.
  Import Reg LinCCALBase LTSSpec Lang Semantics.
  Import AssertionsSingle SingletonPossibility.
  Import TPSimulationSet.TPSimulation CompLinLayer.
  Import AtomicLTS CounterSpec SwapSpec POQueueSpec HWQueueImpl.
  Import (coercions, canonicals, notations) Sig.
  Import (canonicals) Sig.Plus.
  Import (notations) LinCCAL.
  Module SetLogic := RGILogicSet.RGILogic.
  Import SetLogic.

  Open Scope prog_scope.
  Open Scope assertion_scope.
  Open Scope rg_relation_scope.

  Section Proof.
    Context {A : Type}.

    Definition E : layer_interface := @HWQueueImpl.E A.
    Definition F : layer_interface := @HWQueueImpl.F A.

    Definition concrete_state := State (li_lts E).
    Definition abstract_state := State (li_lts F).
    Definition lin_state := @LinState (li_sig F).
    Definition single_state :=
      @SinglePossState.ProofStateSingle _ _ (li_lts E) (li_lts F).
    Definition assertion := @Logics.Assertion single_state.
    Definition rg_relation :=
      @AssertionsSingle.A.RGRelation _ _ (li_lts E) (li_lts F).

    Definition counter_control := @AState ECounter nat.
    Definition cells_control := @AState (@ESwapArray A) (@Cells A).

    (** Explicitly typed proof-state builder. *)
    Definition mk (σ : concrete_state) (ρ : abstract_state) (π : tmap lin_state) :
        single_state :=
      @SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F) σ ρ π.

    Implicit Types (s : @POQueueState A).
    Implicit Types (π : tmap lin_state).

    Definition op_enq (x : A) : Sig.op (li_sig F) := poq_enq x.
    Definition op_deq : Sig.op (li_sig F) := poq_deq.

    (** The paper's tokens [◦ enq(x)], [⋆ enq(x)], [• (enq(x), ok)],
        [◦ deq], [⋆ deq], [• (deq, x)]. *)
    Definition enq_inv_token (x : A) : lin_state := ls_inv (op_enq x).
    Definition enq_lini_token (x : A) : lin_state := ls_lini (op_enq x).
    Definition enq_ret_token (x : A) : lin_state := ls_linr (op_enq x) tt.
    Definition deq_inv_token : lin_state := ls_inv op_deq.
    Definition deq_lini_token : lin_state := ls_lini op_deq.
    Definition deq_ret_token (x : A) : lin_state := ls_linr op_deq x.

    (** * Views of the proof state *)

    (** [c] and [cells] of the paper: the values of the two hardware
        objects, ignoring their atomic control. *)
    Definition counter_of (σ : concrete_state) : nat :=
      AtomicLTS.state (fst σ).
    Definition cells_of (σ : concrete_state) : @Cells A :=
      AtomicLTS.state (snd σ).

    (** [s = (V, E, P, g, nxt)]: the payload of the abstract control. *)
    Definition graph_of (w : single_state) : @POQueueState A :=
      poq_payload (ρ w).

    (** * The global invariant (Invariant 5.1) *)

    (** (I2) *)
    Definition I_cells s (c : @Cells A) : Prop :=
      forall i x,
        c i = Some x <->
        (poq_live s i /\ poq_complete s i /\ poq_vertices s i = Some x).

    (** The added clause: a pending enqueue of [β] for vertex [n] holds the
        token [⋆ enq(x)] with [V(n) = x]. *)
    Definition pending_tokens s π : Prop :=
      forall β n, TMap.find β (poq_pending s) = Some n ->
        exists x, poq_vertices s n = Some x /\
          TMap.find β π = Some (enq_lini_token x).

    Definition I_state (σ : concrete_state) (ρ : abstract_state) π : Prop :=
      exists s,
        ρ = POQReady s /\                      (* (I3) *)
        poq_wf s /\ counter_of σ = poq_next s /\ (* (I1) *)
        I_cells s (cells_of σ) /\               (* (I2) *)
        pending_tokens s π.

    Definition I : assertion := fun w => I_state (σ w) (ρ w) (π w).

    (** * Guarantee and rely (Section 5.3) *)

    (** [G α] records which abstract transition, if any, a step of [α]
        takes, together with the token it moves.  The concrete state is
        not constrained: the program logic supplies [I] at the post-state
        of every stability obligation. *)
    Variant G (α : tid) : rg_relation :=
    | g_silent (w w' : single_state) :
        ρ w' = ρ w -> π w' = π w ->
        G α w w'
    | g_enq_inv (w w' : single_state) s x :
        ρ w = POQReady s ->
        TMap.find α (poq_pending s) = None ->
        TMap.find α (π w) = Some (enq_inv_token x) ->
        ρ w' = POQReady (poq_start_enq α x s) ->
        π w' = TMap.add α (enq_lini_token x) (π w) ->
        G α w w'
    | g_enq_ret (w w' : single_state) s x n :
        ρ w = POQReady s ->
        TMap.find α (poq_pending s) = Some n ->
        TMap.find α (π w) = Some (enq_lini_token x) ->
        ρ w' = POQReady (poq_finish_enq α s) ->
        π w' = TMap.add α (enq_ret_token x) (π w) ->
        G α w w'
    | g_deq (w w' : single_state) s n x :
        ρ w = POQReady s ->
        poq_minimal s n ->
        poq_complete s n ->
        poq_vertices s n = Some x ->
        TMap.find α (π w) = Some deq_inv_token ->
        ρ w' = POQReady (poq_mark_garbage n s) ->
        π w' = TMap.add α (deq_ret_token x) (TMap.add α deq_lini_token (π w)) ->
        G α w w'.

    (** [R α = ⋃_{β ≠ α} G β], plus the framework's token steps. *)
    Definition R (α : tid) : rg_relation :=
      fun w w' =>
        (exists β, β <> α /\ G β w w') \/
        (exists β, β <> α /\ GINV β w w') \/
        (exists β, β <> α /\ GRET β w w') \/
        w = w'.

    (** * Thread-local assertions (Definition 5.2) *)

    Definition EnqStart (α : tid) (x : A) : assertion :=
      fun w => I w /\
        TMap.find α (π w) = Some (enq_inv_token x) /\
        TMap.find α (poq_pending (graph_of w)) = None.

    Definition EnqSlot (α : tid) (x : A) (i : nat) : assertion :=
      fun w => I w /\
        TMap.find α (π w) = Some (enq_lini_token x) /\
        TMap.find α (poq_pending (graph_of w)) = Some i /\
        poq_vertices (graph_of w) i = Some x.

    Definition EnqDone (α : tid) (x : A) : assertion :=
      fun w => I w /\
        TMap.find α (π w) = Some (enq_ret_token x) /\
        TMap.find α (poq_pending (graph_of w)) = None.

    Definition DeqStart (α : tid) : assertion :=
      fun w => I w /\ TMap.find α (π w) = Some deq_inv_token.

    (** The universally quantified clause of [Scan]: among the slots
        below [i], a live complete element is preceded in the DAG only by
        vertices created at or after [r]. *)
    Definition scan_clause s (i r : nat) : Prop :=
      forall m, m < i -> poq_live s m -> poq_complete s m ->
        forall n, poq_edges s n m -> r <= n.

    Definition Scan (α : tid) (i r : nat) : assertion :=
      fun w => I w /\
        TMap.find α (π w) = Some deq_inv_token /\
        i <= r /\ r <= poq_next (graph_of w) /\
        scan_clause (graph_of w) i r.

    Definition Found (α : tid) (x : A) : assertion :=
      fun w => I w /\ TMap.find α (π w) = Some (deq_ret_token x).

    (** Loop invariant of the [ForEach] over [seq 0 r]: while nothing has
        been found, the remaining slots are [i, ..., r-1] and [Scan(α, i, r)]
        holds; once [x] is found, the loop idles with [• (deq, x)]. *)
    Definition ScanInv (α : tid) (r : nat) (items : list nat)
        (acc : option A) : assertion :=
      match acc with
      | None => fun w => exists i, items = seq i (r - i) /\ Scan α i r w
      | Some x => Found α x
      end.

    (** * Elementary consequences *)

    Lemma I_graph_wf w : I w -> poq_wf (graph_of w).
    Proof.
      intros (s & Hρ & Hwf & _). unfold graph_of. rewrite Hρ. exact Hwf.
    Qed.

    Lemma I_ready w : I w -> ρ w = POQReady (graph_of w).
    Proof. intros (s & Hρ & _). unfold graph_of. rewrite Hρ. reflexivity. Qed.

    Lemma I_counter w : I w -> counter_of (σ w) = poq_next (graph_of w).
    Proof.
      intros (s & Hρ & _ & Hc & _). unfold graph_of. rewrite Hρ. exact Hc.
    Qed.

    Lemma I_cells_of w : I w -> I_cells (graph_of w) (cells_of (σ w)).
    Proof.
      intros (s & Hρ & _ & _ & Hcells & _). unfold graph_of. rewrite Hρ. exact Hcells.
    Qed.

    Lemma I_pending_tokens w : I w -> pending_tokens (graph_of w) (π w).
    Proof.
      intros (s & Hρ & _ & _ & _ & Hpt). unfold graph_of. rewrite Hρ. exact Hpt.
    Qed.

    Lemma enq_start_entails_I α x : ⊨ EnqStart α x ==>> I.
    Proof. intros w [HI _]. exact HI. Qed.
    Lemma enq_slot_entails_I α x i : ⊨ EnqSlot α x i ==>> I.
    Proof. intros w [HI _]. exact HI. Qed.
    Lemma enq_done_entails_I α x : ⊨ EnqDone α x ==>> I.
    Proof. intros w [HI _]. exact HI. Qed.
    Lemma deq_start_entails_I α : ⊨ DeqStart α ==>> I.
    Proof. intros w [HI _]. exact HI. Qed.
    Lemma scan_entails_I α i r : ⊨ Scan α i r ==>> I.
    Proof. intros w [HI _]. exact HI. Qed.
    Lemma found_entails_I α x : ⊨ Found α x ==>> I.
    Proof. intros w [HI _]. exact HI. Qed.
    Lemma scan_inv_entails_I α r items acc : ⊨ ScanInv α r items acc ==>> I.
    Proof.
      destruct acc as [x|]; simpl.
      - apply found_entails_I.
      - intros w [i [_ HScan]]. exact (scan_entails_I α i r w HScan).
    Qed.

    (** A cell is empty when its vertex is not live and complete. *)
    Lemma I_cells_none s c i :
      I_cells s c ->
      ~ (poq_live s i /\ poq_complete s i) ->
      c i = None.
    Proof.
      intros Hcells Hnot. destruct (c i) as [x|] eqn:Hc; [|reflexivity].
      exfalso. apply Hnot. apply Hcells in Hc. tauto.
    Qed.

    Lemma I_cells_next s c :
      poq_wf s -> I_cells s c -> c (poq_next s) = None.
    Proof.
      intros Hwf Hcells. apply (I_cells_none s c _ Hcells).
      intros [[Hv _] _]. exact (poq_next_not_vertex s Hwf Hv).
    Qed.

    (** * Preservation of (I2) by the three abstract transitions
        (the (I2) cases of Lemma 5.3) *)

    Lemma I_cells_start_enq β x s c :
      poq_wf s ->
      TMap.find β (poq_pending s) = None ->
      I_cells s c ->
      I_cells (poq_start_enq β x s) c.
    Proof.
      intros Hwf Hidle Hcells i y.
      destruct (Nat.eq_dec i (poq_next s)) as [-> | Hne].
      - (* the new vertex: its cell is empty and it is pending *)
        rewrite (I_cells_next s c Hwf Hcells). split; [discriminate |].
        intros [_ [Hc _]]. exfalso.
        exact (poq_start_enq_new_not_complete β x s Hidle Hc).
      - rewrite (poq_start_enq_vertices β x s i Hne). split.
        + intros Hc. apply Hcells in Hc. destruct Hc as [Hl [Hcomp Hv]].
          split; [apply (poq_start_enq_live β x s i Hwf); right; exact Hl |].
          split; [apply (poq_start_enq_complete β x s i Hidle Hne); exact Hcomp | exact Hv].
        + intros [Hl [Hcomp Hv]]. apply Hcells.
          apply (poq_start_enq_live β x s i Hwf) in Hl.
          destruct Hl as [Heq | Hl]; [congruence |].
          apply (poq_start_enq_complete β x s i Hidle Hne) in Hcomp.
          split; [exact Hl |]. split; [exact Hcomp | exact Hv].
    Qed.

    Lemma I_cells_finish_enq β x n s c :
      poq_wf s ->
      TMap.find β (poq_pending s) = Some n ->
      poq_vertices s n = Some x ->
      I_cells s c ->
      I_cells (poq_finish_enq β s) (cell_update n (Some x) c).
    Proof.
      intros Hwf Hfind Hv Hcells i y.
      change (poq_live (poq_finish_enq β s) i) with (poq_live s i).
      change (poq_vertices (poq_finish_enq β s) i) with (poq_vertices s i).
      destruct (Nat.eq_dec n i) as [<- | Hne].
      - (* the completed vertex: live by (W4), complete now, value [x] *)
        rewrite cell_update_same. split.
        + intros Hy. injection Hy as <-. split.
          * apply poq_pending_live; [exact Hwf |]. exists β. exact Hfind.
          * split; [| exact Hv].
            apply (poq_finish_enq_complete β s n n Hwf Hfind). right. reflexivity.
        + intros [_ [_ Hv']]. rewrite Hv in Hv'. exact Hv'.
      - rewrite cell_update_other by exact Hne. split.
        + intros Hc. apply Hcells in Hc. destruct Hc as [Hl [Hcomp Hv']].
          split; [exact Hl |]. split; [| exact Hv'].
          apply (poq_finish_enq_complete β s n i Hwf Hfind). left. exact Hcomp.
        + intros [Hl [Hcomp Hv']]. apply Hcells.
          apply (poq_finish_enq_complete β s n i Hwf Hfind) in Hcomp.
          destruct Hcomp as [Hcomp | Heq]; [| congruence].
          split; [exact Hl |]. split; [exact Hcomp | exact Hv'].
    Qed.

    Lemma I_cells_mark_garbage n s c :
      I_cells s c ->
      I_cells (poq_mark_garbage n s) (cell_update n None c).
    Proof.
      intros Hcells i y.
      change (poq_vertices (poq_mark_garbage n s) i) with (poq_vertices s i).
      destruct (Nat.eq_dec n i) as [-> | Hne].
      - (* the removed vertex: its cell is empty and it is garbage *)
        rewrite cell_update_same. split; [discriminate |].
        intros [Hl _]. apply poq_mark_garbage_live in Hl.
        destruct Hl as [_ Hne]. exact (False_ind _ (Hne eq_refl)).
      - rewrite cell_update_other by exact Hne. split.
        + intros Hc. apply Hcells in Hc. destruct Hc as [Hl [Hcomp Hv]].
          split; [apply poq_mark_garbage_live; split; auto |].
          split; [apply poq_mark_garbage_complete; exact Hcomp | exact Hv].
        + intros [Hl [Hcomp Hv]]. apply Hcells.
          apply poq_mark_garbage_live in Hl. destruct Hl as [Hl _].
          apply poq_mark_garbage_complete in Hcomp.
          split; [exact Hl |]. split; [exact Hcomp | exact Hv].
    Qed.

    (** * Preservation of [scan_clause] by other threads' transitions
        (the [Scan] cases of Lemma 5.3) *)

    Lemma scan_clause_start_enq β x s i r :
      poq_wf s ->
      TMap.find β (poq_pending s) = None ->
      r <= poq_next s ->
      scan_clause s i r ->
      scan_clause (poq_start_enq β x s) i r.
    Proof.
      intros Hwf Hidle Hr Hscan m Hm Hl Hc n Hedge.
      destruct (Nat.eq_dec m (poq_next s)) as [-> | Hne].
      - exfalso. exact (poq_start_enq_new_not_complete β x s Hidle Hc).
      - apply (poq_start_enq_live β x s m Hwf) in Hl.
        destruct Hl as [Heq | Hl]; [congruence |].
        apply (poq_start_enq_complete β x s m Hidle Hne) in Hc.
        apply poq_start_enq_edges in Hedge.
        destruct Hedge as [Hedge | [-> _]].
        + exact (Hscan m Hm Hl Hc n Hedge).
        + exact Hr.
    Qed.

    Lemma scan_clause_finish_enq β n s i r :
      poq_wf s ->
      TMap.find β (poq_pending s) = Some n ->
      scan_clause s i r ->
      scan_clause (poq_finish_enq β s) i r.
    Proof.
      intros Hwf Hfind Hscan m Hm Hl Hc n' Hedge.
      change (poq_edges (poq_finish_enq β s) n' m) with (poq_edges s n' m) in Hedge.
      change (poq_live (poq_finish_enq β s) m) with (poq_live s m) in Hl.
      apply (poq_finish_enq_complete β s n m Hwf Hfind) in Hc.
      destruct Hc as [Hc | ->].
      - exact (Hscan m Hm Hl Hc n' Hedge).
      - (* [n] was pending, so by (W3) it has no incoming edge. *)
        exfalso. apply (wf_pending_no_incoming s Hwf n' n); [| exact Hedge].
        exists β. exact Hfind.
    Qed.

    Lemma scan_clause_mark_garbage n s i r :
      scan_clause s i r ->
      scan_clause (poq_mark_garbage n s) i r.
    Proof.
      intros Hscan m Hm Hl Hc n' Hedge.
      apply poq_mark_garbage_live in Hl. destruct Hl as [Hl _].
      exact (Hscan m Hm Hl Hc n' Hedge).
    Qed.

    (** * Lemma 5.5: a dequeue takes a minimal element *)

    Lemma deq_takes_minimal s c i r x :
      poq_wf s ->
      I_cells s c ->
      scan_clause s i r ->
      i < r ->
      c i = Some x ->
      poq_live s i /\ poq_complete s i /\ poq_vertices s i = Some x /\
      poq_minimal s i.
    Proof.
      intros Hwf Hcells Hscan Hir Hc.
      apply Hcells in Hc. destruct Hc as [Hl [Hcomp Hv]].
      split; [exact Hl |]. split; [exact Hcomp |]. split; [exact Hv |].
      split; [exact Hl |].
      intros m Hedge Hlm.
      (* (W2): m < i.  (W3): m is not pending, so complete.  Then [Scan]. *)
      pose proof (wf_edge_lt s Hwf i m Hedge) as Hmi.
      assert (Hcm : poq_complete s m).
      { split; [exact (proj1 Hlm) |].
        intro Hp. exact (wf_pending_no_incoming s Hwf i m Hp Hedge). }
      pose proof (Hscan m Hmi Hlm Hcm i Hedge). lia.
    Qed.

    (** * What the rely preserves *)

    (** The abstract transitions other threads may take. *)
    Variant abs_step s : @POQueueState A -> Prop :=
    | abs_same : abs_step s s
    | abs_start_enq β x :
        TMap.find β (poq_pending s) = None ->
        abs_step s (poq_start_enq β x s)
    | abs_finish_enq β n :
        TMap.find β (poq_pending s) = Some n ->
        abs_step s (poq_finish_enq β s)
    | abs_mark_garbage n :
        poq_complete s n ->
        abs_step s (poq_mark_garbage n s).

    Lemma graph_of_ready (w : single_state) s :
      ρ w = POQReady s -> graph_of w = s.
    Proof. intros H. unfold graph_of. rewrite H. reflexivity. Qed.

    Lemma R_facts obs w w' :
      R obs w w' -> I w ->
      TMap.find obs (π w') = TMap.find obs (π w) /\
      TMap.find obs (poq_pending (graph_of w')) =
        TMap.find obs (poq_pending (graph_of w)) /\
      (forall n v, poq_vertices (graph_of w) n = Some v ->
        poq_vertices (graph_of w') n = Some v) /\
      poq_next (graph_of w) <= poq_next (graph_of w') /\
      abs_step (graph_of w) (graph_of w').
    Proof.
      intros HR HI. pose proof (I_graph_wf w HI) as Hwf.
      destruct HR as [[β [Hne HG]] | [[β [Hne [f [Hσ [Hρ [Hnone Hπ]]]]]]
        | [[β [Hne [f [ret [Hσ [Hρ [Hsome Hπ]]]]]]] | Heq]]].
      - destruct HG as [w w' Hρ Hπ | w w' s x Hρ Hidle Htok Hρ' Hπ'
          | w w' s x n Hρ Hfind Htok Hρ' Hπ' | w w' s n x Hρ Hmin Hcomp Hv Htok Hρ' Hπ'].
        + unfold graph_of. rewrite Hρ, Hπ.
          repeat split; auto. constructor.
        + rewrite (graph_of_ready w s Hρ) in Hwf.
          rewrite Hπ', (graph_of_ready w s Hρ), (graph_of_ready w' _ Hρ').
          rewrite TMap.gso by congruence.
          split; [reflexivity |]. split.
          { change (poq_pending (poq_start_enq β x s)) with
              (TMap.add β (poq_next s) (poq_pending s)).
            rewrite TMap.gso by congruence. reflexivity. }
          split.
          { intros n v Hv. rewrite poq_start_enq_vertices; [exact Hv |].
            intros ->. apply (poq_next_not_vertex s Hwf). unfold poq_is_vertex. congruence. }
          split; [change (poq_next (poq_start_enq β x s)) with (S (poq_next s)); lia |].
          constructor. exact Hidle.
        + rewrite Hπ', (graph_of_ready w s Hρ), (graph_of_ready w' _ Hρ').
          rewrite TMap.gso by congruence.
          split; [reflexivity |]. split.
          { change (poq_pending (poq_finish_enq β s)) with
              (TMap.remove β (poq_pending s)).
            rewrite TMap.gro by congruence. reflexivity. }
          split; [intros n' v Hv; exact Hv |].
          split; [change (poq_next (poq_finish_enq β s)) with (poq_next s); lia |].
          econstructor. exact Hfind.
        + rewrite Hπ', (graph_of_ready w s Hρ), (graph_of_ready w' _ Hρ').
          rewrite TMap.gso by congruence. rewrite TMap.gso by congruence.
          split; [reflexivity |]. split; [reflexivity |].
          split; [intros n' v Hv'; exact Hv' |].
          split; [change (poq_next (poq_mark_garbage n s)) with (poq_next s); lia |].
          constructor. exact Hcomp.
      - unfold graph_of. rewrite Hρ, Hπ. rewrite TMap.gso by congruence.
        repeat split; auto. constructor.
      - unfold graph_of. rewrite Hρ, Hπ. rewrite TMap.gro by congruence.
        repeat split; auto. constructor.
      - subst w'. repeat split; auto. constructor.
    Qed.

    (** * Stability (Lemma 5.3) *)

    Lemma I_stable α : Stable (R α) I I.
    Proof. apply Stable_invariant. Qed.

    Lemma enq_start_stable α x : Stable (R α) I (EnqStart α x).
    Proof.
      intros w' [[w [[HI [Htok Hpend]] HR]] HI'].
      destruct (R_facts α w w' HR HI) as (Hπ & HP & _ & _ & _).
      split; [exact HI' |]. split; [rewrite Hπ; exact Htok | rewrite HP; exact Hpend].
    Qed.

    Lemma enq_slot_stable α x i : Stable (R α) I (EnqSlot α x i).
    Proof.
      intros w' [[w [[HI [Htok [Hpend Hv]]] HR]] HI'].
      destruct (R_facts α w w' HR HI) as (Hπ & HP & HV & _ & _).
      split; [exact HI' |]. split; [rewrite Hπ; exact Htok |].
      split; [rewrite HP; exact Hpend | apply HV; exact Hv].
    Qed.

    Lemma enq_done_stable α x : Stable (R α) I (EnqDone α x).
    Proof.
      intros w' [[w [[HI [Htok Hpend]] HR]] HI'].
      destruct (R_facts α w w' HR HI) as (Hπ & HP & _ & _ & _).
      split; [exact HI' |]. split; [rewrite Hπ; exact Htok | rewrite HP; exact Hpend].
    Qed.

    Lemma deq_start_stable α : Stable (R α) I (DeqStart α).
    Proof.
      intros w' [[w [[HI Htok] HR]] HI'].
      destruct (R_facts α w w' HR HI) as (Hπ & _ & _ & _ & _).
      split; [exact HI' | rewrite Hπ; exact Htok].
    Qed.

    Lemma found_stable α x : Stable (R α) I (Found α x).
    Proof.
      intros w' [[w [[HI Htok] HR]] HI'].
      destruct (R_facts α w w' HR HI) as (Hπ & _ & _ & _ & _).
      split; [exact HI' | rewrite Hπ; exact Htok].
    Qed.

    Lemma scan_stable α i r : Stable (R α) I (Scan α i r).
    Proof.
      intros w' [[w [[HI [Htok [Hir [Hr Hscan]]]] HR]] HI'].
      pose proof (I_graph_wf w HI) as Hwf.
      destruct (R_facts α w w' HR HI) as (Hπ & _ & _ & Hnext & Hstep).
      split; [exact HI' |]. split; [rewrite Hπ; exact Htok |].
      split; [exact Hir |]. split; [lia |].
      destruct Hstep as [| β x Hidle | β n Hfind | n Hcomp].
      - exact Hscan.
      - apply scan_clause_start_enq; assumption.
      - eapply scan_clause_finish_enq; eassumption.
      - apply scan_clause_mark_garbage; assumption.
    Qed.

    Lemma scan_inv_stable α r items acc : Stable (R α) I (ScanInv α r items acc).
    Proof.
      destruct acc as [x|]; simpl; [apply found_stable |].
      intros w' [[w [[i [Hitems HScan]] HR]] HI'].
      exists i. split; [exact Hitems |].
      apply (scan_stable α i r). split; [| exact HI']. exists w. split; assumption.
    Qed.

    (** * Rely/guarantee side conditions *)

    Lemma source_valid_rg α : forall w w', R α w w' -> I w' ->
      TMap.find α (π w) = None <-> TMap.find α (π w') = None.
    Proof.
      intros w w' HR _.
      destruct HR as [[β [Hne HG]] | [[β [Hne [f [Hσ [Hρ [Hnone Hπ]]]]]]
        | [[β [Hne [f [ret [Hσ [Hρ [Hsome Hπ]]]]]]] | Heq]]].
      - destruct HG as [w w' Hρ Hπ | w w' s x Hρ Hidle Htok Hρ' Hπ'
          | w w' s x n Hρ Hfind Htok Hρ' Hπ' | w w' s n x Hρ Hmin Hcomp Hv Htok Hρ' Hπ'].
        + rewrite Hπ. tauto.
        + rewrite Hπ', TMap.gso by congruence. tauto.
        + rewrite Hπ', TMap.gso by congruence. tauto.
        + rewrite Hπ', TMap.gso, TMap.gso by congruence. tauto.
      - rewrite Hπ, TMap.gso by congruence. tauto.
      - rewrite Hπ, TMap.gro by congruence. tauto.
      - subst w'. tauto.
    Qed.

    Lemma source_rg_compatible t1 t2 : t1 <> t2 -> forall w w',
      (G t1 w w' \/ (GINV t1 w w' \/ GRET t1 w w') \/ GId w w') ->
      R t2 w w'.
    Proof.
      intros Hneq w w' [HG | [[Hinv | Hret] | Hid]].
      - left. exists t1. split; [congruence | exact HG].
      - right. left. exists t1. split; [congruence | exact Hinv].
      - right. right. left. exists t1. split; [congruence | exact Hret].
      - right. right. right. exact Hid.
    Qed.

    (** * Steps of the hardware objects *)

    Lemma no_error ev (P : assertion) : ⊨ P ==>> ANoError ev.
    Proof.
      intros w _ Herr. unfold ANoError in Herr.
      destruct (σ w) as [ca sa]. destruct ev as [t [[op | op] | [op | op] r]];
        simpl in Herr; exact Herr.
    Qed.

    Ltac crush_event :=
      repeat match goal with
      | H : {| te_tid := _; te_ev := _ |} = {| te_tid := _; te_ev := _ |} |- _ =>
          injection H; clear H; intros
      | H : InvEv _ = ResEv _ _ |- _ => discriminate H
      | H : ResEv _ _ = InvEv _ |- _ => discriminate H
      | H : InvEv _ = InvEv _ |- _ => injection H; clear H; intros
      | H : ResEv _ _ = ResEv _ _ |- _ => injection H; clear H; intros
      | H : sa_swap _ _ = sa_swap _ _ |- _ => injection H; clear H; intros
      | H : sa_store _ _ = sa_store _ _ |- _ => injection H; clear H; intros
      | H : existT _ _ _ = existT _ _ _ |- _ => apply inj_pair2 in H
      | H : ?x = ?x |- _ => clear H
      | H : ?x = ?y |- _ => is_var y; subst y
      | H : ?x = ?y |- _ => is_var x; subst x
      end;
      try discriminate; try congruence.

    Lemma ctr_inv_shape α op (σ σ' : concrete_state) :
      Step (li_lts E) {| te_tid := α; te_ev := InvEv (inl op) |} σ σ' ->
      exists c sa, σ = pair (Idle c) sa /\ σ' = pair (Pending c α op) sa.
    Proof.
      destruct σ as [ca sa], σ' as [ca' sa']. simpl. intros [Hstep ->].
      inversion Hstep; subst; crush_event.
      inversion Hstep0; subst; crush_event; eauto.
    Qed.

    Lemma ctr_inc_res_shape α i (σ σ' : concrete_state) :
      Step (li_lts E) {| te_tid := α; te_ev := ResEv (inl ctr_inc) i |} σ σ' ->
      exists sa, σ = pair (Pending i α ctr_inc) sa /\ σ' = pair (Idle (S i)) sa.
    Proof.
      destruct σ as [ca sa], σ' as [ca' sa']. simpl. intros [Hstep ->].
      inversion Hstep; subst; crush_event.
      inversion Hstep0; subst; crush_event; eauto.
    Qed.

    Lemma ctr_read_res_shape α r (σ σ' : concrete_state) :
      Step (li_lts E) {| te_tid := α; te_ev := ResEv (inl ctr_read) r |} σ σ' ->
      exists sa, σ = pair (Pending r α ctr_read) sa /\ σ' = pair (Idle r) sa.
    Proof.
      destruct σ as [ca sa], σ' as [ca' sa']. simpl. intros [Hstep ->].
      inversion Hstep; subst; crush_event.
      inversion Hstep0; subst; crush_event; eauto.
    Qed.

    Lemma sa_inv_shape α op (σ σ' : concrete_state) :
      Step (li_lts E) {| te_tid := α; te_ev := InvEv (inr op) |} σ σ' ->
      exists ca c, σ = pair ca (Idle c) /\ σ' = pair ca (Pending c α op).
    Proof.
      destruct σ as [ca sa], σ' as [ca' sa']. simpl. intros [Hstep ->].
      inversion Hstep; subst; crush_event.
      inversion Hstep0; subst; crush_event; eauto.
    Qed.

    Lemma sa_swap_res_shape α i w x (σ σ' : concrete_state) :
      Step (li_lts E) {| te_tid := α; te_ev := ResEv (inr (sa_swap i w)) x |} σ σ' ->
      exists ca c, σ = pair ca (Pending c α (sa_swap i w)) /\
        x = c i /\ σ' = pair ca (Idle (cell_update i w c)).
    Proof.
      destruct σ as [ca sa], σ' as [ca' sa']. simpl. intros [Hstep ->].
      inversion Hstep; subst; crush_event.
      inversion Hstep0; subst; crush_event; eauto.
    Qed.

    Lemma sa_store_res_shape α i w (σ σ' : concrete_state) :
      Step (li_lts E) {| te_tid := α; te_ev := ResEv (inr (sa_store i w)) tt |} σ σ' ->
      exists ca c, σ = pair ca (Pending c α (sa_store i w)) /\
        σ' = pair ca (Idle (cell_update i w c)).
    Proof.
      destruct σ as [ca sa], σ' as [ca' sa']. simpl. intros [Hstep ->].
      inversion Hstep; subst; crush_event.
      inversion Hstep0; subst; crush_event; eauto.
    Qed.

    (** * Steps of the partial-order queue *)

    Lemma poq_enq_inv_step α x s :
      TMap.find α (poq_pending s) = None ->
      Step (li_lts F) {| te_tid := α; te_ev := InvEv (op_enq x) |}
        (POQReady s) (POQReady (poq_start_enq α x s)).
    Proof. intros Hidle. apply (step_poq_enq_inv α s x); auto. Qed.

    Lemma poq_enq_res_step α x s n :
      TMap.find α (poq_pending s) = Some n ->
      Step (li_lts F) {| te_tid := α; te_ev := ResEv (op_enq x) tt |}
        (POQReady s) (POQReady (poq_finish_enq α s)).
    Proof. intros Hfind. apply (step_poq_enq_res α s x n); auto. Qed.

    Lemma poq_deq_inv_step α s :
      Step (li_lts F) {| te_tid := α; te_ev := InvEv op_deq |}
        (POQReady s) (POQAtomic s α poq_deq).
    Proof. apply (step_poq_deq_inv α s); auto. Qed.

    Lemma poq_deq_res_step α s n x :
      poq_minimal s n -> poq_complete s n -> poq_vertices s n = Some x ->
      Step (li_lts F) {| te_tid := α; te_ev := ResEv op_deq x |}
        (POQAtomic s α poq_deq) (POQReady (poq_mark_garbage n s)).
    Proof. intros. apply (step_poq_deq_res α s n x); auto. Qed.

    (** * The possibility updates of the method proofs *)

    Lemma enq_lini_not_deq_inv y : enq_lini_token y <> deq_inv_token.
    Proof. discriminate. Qed.
    Lemma enq_lini_not_deq_ret y x : enq_lini_token y <> deq_ret_token x.
    Proof. discriminate. Qed.

    (** Silent concrete steps: the abstract possibility is unchanged and
        [I] only looks at the values of the hardware objects. *)
    Lemma silent_inv_counter α (op : ECounter_op) (P : assertion) :
      (forall w, P w -> forall (c : nat) (sa : cells_control),
        σ w = pair (Idle c) sa ->
        P (mk (pair (Pending c α op) sa) (ρ w) (π w))) ->
      PUpdate (G α) {| te_tid := α; te_ev := InvEv (inl op) |} P P.
    Proof.
      intros Hkeep σ1 ρ1 π1 Hpre σ2 Hstep.
      destruct (ctr_inv_shape _ _ _ _ Hstep) as (c & sa & -> & ->).
      exists ρ1, π1. split; [apply rt_refl |]. split.
      - exact (Hkeep _ Hpre c sa eq_refl).
      - apply g_silent; reflexivity.
    Qed.

    Lemma silent_inv_cells α (op : @ESwapArray_op A) (P : assertion) :
      (forall w, P w -> forall (ca : counter_control) (c : @Cells A),
        σ w = pair ca (Idle c) ->
        P (mk (pair ca (Pending c α op)) (ρ w) (π w))) ->
      PUpdate (G α) {| te_tid := α; te_ev := InvEv (inr op) |} P P.
    Proof.
      intros Hkeep σ1 ρ1 π1 Hpre σ2 Hstep.
      destruct (sa_inv_shape _ _ _ _ Hstep) as (ca & c & -> & ->).
      exists ρ1, π1. split; [apply rt_refl |]. split.
      - exact (Hkeep _ Hpre ca c eq_refl).
      - apply g_silent; reflexivity.
    Qed.

    (** Every assertion of the proof depends on the concrete state only
        through [counter_of] and [cells_of], which ignore the control. *)
    Lemma I_control_counter (ca ca' : counter_control) (sa : cells_control)
        (ρ : abstract_state) π :
      AtomicLTS.state ca' = AtomicLTS.state ca ->
      I (mk (pair ca sa) ρ π) -> I (mk (pair ca' sa) ρ π).
    Proof.
      intros Heq (s & Hρ & Hwf & Hc & Hcells & Hpt). exists s.
      unfold counter_of, cells_of in *. simpl in *. rewrite Heq. auto.
    Qed.

    Lemma I_control_cells (ca : counter_control) (sa sa' : cells_control)
        (ρ : abstract_state) π :
      AtomicLTS.state sa' = AtomicLTS.state sa ->
      I (mk (pair ca sa) ρ π) -> I (mk (pair ca sa') ρ π).
    Proof.
      intros Heq (s & Hρ & Hwf & Hc & Hcells & Hpt). exists s.
      unfold counter_of, cells_of in *. simpl in *. rewrite Heq. auto.
    Qed.

    (** The invocation of a counter operation keeps an assertion of the
        form [I ∧ facts about ρ and π]. *)
    Lemma keep_counter_inv α (op : ECounter_op) (X : single_state -> Prop) :
      (forall (w : single_state) (ca : counter_control), X w ->
        X (mk (pair ca (snd (σ w))) (ρ w) (π w))) ->
      forall w, (I w /\ X w) -> forall (c : nat) (sa : cells_control),
        σ w = pair (Idle c) sa ->
        (I (mk (pair (Pending c α op) sa) (ρ w) (π w)) /\
         X (mk (pair (Pending c α op) sa) (ρ w) (π w))).
    Proof.
      intros HX w [HI Hx] c sa Hσ.
      pose proof (HX w (Pending c α op) Hx) as Hx'.
      destruct w as [σw ρw πw]. simpl in Hσ. subst σw. simpl in Hx'.
      split; [| exact Hx'].
      eapply I_control_counter with (ca := Idle c); [reflexivity | exact HI].
    Qed.

    Lemma keep_cells_inv α (op : @ESwapArray_op A) (X : single_state -> Prop) :
      (forall (w : single_state) (sa : cells_control), X w ->
        X (mk (pair (fst (σ w)) sa) (ρ w) (π w))) ->
      forall w, (I w /\ X w) -> forall (ca : counter_control) (c : @Cells A),
        σ w = pair ca (Idle c) ->
        (I (mk (pair ca (Pending c α op)) (ρ w) (π w)) /\
         X (mk (pair ca (Pending c α op)) (ρ w) (π w))).
    Proof.
      intros HX w [HI Hx] ca c Hσ.
      pose proof (HX w (Pending c α op) Hx) as Hx'.
      destruct w as [σw ρw πw]. simpl in Hσ. subst σw. simpl in Hx'.
      split; [| exact Hx'].
      eapply I_control_cells with (sa := Idle c); [reflexivity | exact HI].
    Qed.

    (** [inc] returns [i = nxt]: take [enq-inv] with vertex [i]
        (Lemma 5.4, "inc"). *)
    Lemma enq_inc_update α x :
      forall i,
        PUpdate (G α) {| te_tid := α; te_ev := ResEv (inl ctr_inc) i |}
          (EnqStart α x) (EnqSlot α x i).
    Proof.
      intros i σ1 ρ1 π1 [HI [Htok Hidle]] σ2 Hstep.
      destruct (ctr_inc_res_shape _ _ _ _ Hstep) as (sa & -> & ->).
      destruct HI as (s & Hρ & Hwf & Hc & Hcells & Hpt). simpl in Hρ. subst ρ1.
      unfold graph_of in Hidle. simpl in Hidle.
      unfold counter_of in Hc. simpl in Hc. subst i.
      exists (POQReady (poq_start_enq α x s)), (TMap.add α (enq_lini_token x) π1).
      split.
      { apply rt_step. apply (ps_inv α (op_enq x)); [| exact Htok].
        apply poq_enq_inv_step. exact Hidle. }
      split.
      - split; [| split; [| split]].
        + exists (poq_start_enq α x s). split; [reflexivity |].
          split; [apply poq_start_enq_wf; assumption |].
          split; [reflexivity |].
          split; [apply I_cells_start_enq; assumption |].
          (* pending tokens: the new entry is [α]'s, the rest are unchanged *)
          intros β n Hβ. simpl in Hβ. cbn [SinglePossState.π]. apply find_add_inv in Hβ.
          destruct Hβ as [[-> ->] | [Hne Hβ]].
          * exists x. split; [apply poq_start_enq_vertex_new | apply TMap.gss].
          * destruct (Hpt β n Hβ) as [y [Hy Hty]]. exists y. split.
            -- rewrite poq_start_enq_vertices; [exact Hy |].
               intros ->. apply (poq_next_not_vertex s Hwf). unfold poq_is_vertex. congruence.
            -- rewrite TMap.gso by congruence. exact Hty.
        + cbn [SinglePossState.π]. apply TMap.gss.
        + unfold graph_of. cbn [SinglePossState.ρ poq_payload]. apply TMap.gss.
        + unfold graph_of. cbn [SinglePossState.ρ poq_payload].
          apply poq_start_enq_vertex_new.
      - apply (g_enq_inv α _ _ s x); simpl; auto.
    Qed.

    (** [store(i, x)]: take [enq-ret] (Lemma 5.4, "store"). *)
    Lemma enq_store_update α x i :
      PUpdate (G α) {| te_tid := α; te_ev := ResEv (inr (sa_store i (Some x))) tt |}
        (EnqSlot α x i) (EnqDone α x).
    Proof.
      intros σ1 ρ1 π1 [HI [Htok [Hpend Hv]]] σ2 Hstep.
      destruct (sa_store_res_shape _ _ _ _ _ Hstep) as (ca & c & -> & ->).
      destruct HI as (s & Hρ & Hwf & Hc & Hcells & Hpt). simpl in Hρ. subst ρ1.
      unfold graph_of in Hpend, Hv. simpl in Hpend, Hv.
      unfold cells_of in Hcells. simpl in Hcells.
      exists (POQReady (poq_finish_enq α s)), (TMap.add α (enq_ret_token x) π1).
      split.
      { apply rt_step. apply (ps_ret α (op_enq x) tt); [| exact Htok].
        apply (poq_enq_res_step α x s i). exact Hpend. }
      split.
      - split; [| split].
        + exists (poq_finish_enq α s). split; [reflexivity |].
          split; [apply poq_finish_enq_wf; assumption |].
          split; [exact Hc |].
          split; [apply (I_cells_finish_enq α x i s c); assumption |].
          intros β n Hβ. simpl in Hβ. cbn [SinglePossState.π]. apply find_remove_inv in Hβ.
          destruct Hβ as [Hne Hβ]. destruct (Hpt β n Hβ) as [y [Hy Hty]].
          exists y. split; [exact Hy | rewrite TMap.gso by congruence; exact Hty].
        + cbn [SinglePossState.π]. apply TMap.gss.
        + unfold graph_of. cbn [SinglePossState.ρ poq_payload]. apply TMap.grs.
      - apply (g_enq_ret α _ _ s x i); simpl; auto.
    Qed.

    (** [read] returns [r = nxt]: establish [Scan(α, 0, r)]
        (Lemma 5.6, "read"). *)
    Lemma deq_read_update α :
      forall r,
        PUpdate (G α) {| te_tid := α; te_ev := ResEv (inl ctr_read) r |}
          (DeqStart α) (ScanInv α r (seq O r) None).
    Proof.
      intros r σ1 ρ1 π1 [HI Htok] σ2 Hstep.
      destruct (ctr_read_res_shape _ _ _ _ Hstep) as (sa & -> & ->).
      pose proof (I_counter _ HI) as Hc. unfold counter_of, graph_of in Hc. simpl in Hc.
      exists ρ1, π1. split; [apply rt_refl |]. split.
      - exists O. split; [f_equal; lia |].
        split; [eapply I_control_counter with (ca := Pending r α ctr_read);
                [reflexivity | exact HI] |].
        split; [exact Htok |]. unfold graph_of. cbn [SinglePossState.ρ].
        split; [lia |]. split; [lia |].
        intros m Hm. lia.
      - apply g_silent; reflexivity.
    Qed.

    (** The slots remaining in the [ForEach] are [seq i (r - i)]. *)
    Lemma seq_cons_inv i r item items :
      item :: items = seq i (r - i) ->
      item = i /\ i < r /\ items = seq (S i) (r - S i).
    Proof.
      intros Heq. destruct (r - i) as [|k] eqn:Hk; simpl in Heq; [discriminate |].
      injection Heq as Hitem Hitems. subst item.
      split; [reflexivity |]. split; [lia |].
      rewrite Hitems. f_equal. lia.
    Qed.

    (** The precondition of the swap at slot [i]: [Scan(α, i, r)] with
        [i < r], and the remaining slots are [i+1, ..., r-1]. *)
    Definition ScanAt (α : tid) (i r : nat) (items : list nat) : assertion :=
      Scan α i r //\\ ⌜i < r⌝ //\\ ⌜items = seq (S i) (r - S i)⌝.

    Lemma scan_at_entails_I α i r items : ⊨ ScanAt α i r items ==>> I.
    Proof. intros w [HScan _]. exact (scan_entails_I _ _ _ _ HScan). Qed.

    Lemma scan_at_stable α i r items : Stable (R α) I (ScanAt α i r items).
    Proof.
      apply ConjStable; [apply scan_stable |].
      apply ConjStable; apply APureStable.
    Qed.

    Lemma keep_cells_scan_at α (op : @ESwapArray_op A) i r items :
      forall w, ScanAt α i r items w ->
      forall (ca : counter_control) (c : @Cells A),
        σ w = pair ca (Idle c) ->
        ScanAt α i r items (mk (pair ca (Pending c α op)) (ρ w) (π w)).
    Proof.
      intros w [[HI Hrest] Hpure] ca c Hσ.
      destruct w as [σw ρw πw]. simpl in Hσ. subst σw.
      split; [split; [| exact Hrest] | exact Hpure].
      eapply I_control_cells with (sa := Idle c); [reflexivity | exact HI].
    Qed.

    (** [swap(i, null)] inside the scan (Lemma 5.6, "for loop"):
        [null] keeps scanning, a value [x] takes [deq-inv] and [deq-res]. *)
    Lemma deq_swap_update α r i items :
      forall x,
        PUpdate (G α) {| te_tid := α; te_ev := ResEv (inr (sa_swap i None)) x |}
          (ScanAt α i r items) (ScanInv α r items x).
    Proof.
      intros x σ1 ρ1 π1 [[HI [Htok [Hir [Hr Hscan]]]] [Hlt Hitems]] σ2 Hstep.
      unfold APure in Hlt, Hitems. subst items.
      destruct (sa_swap_res_shape _ _ _ _ _ _ Hstep) as (ca & c & -> & -> & ->).
      destruct HI as (s & Hρ & Hwf & Hc & Hcells & Hpt). simpl in Hρ. subst ρ1.
      unfold graph_of in Hr, Hscan. simpl in Hr, Hscan.
      unfold cells_of in Hcells. simpl in Hcells.
      destruct (c i) as [x|] eqn:Hci.
      - (* The slot held [x]: by Lemma 5.5 vertex [i] is minimal. *)
        destruct (deq_takes_minimal s c i r x Hwf Hcells Hscan Hlt Hci)
          as (Hl & Hcomp & Hv & Hmin).
        exists (POQReady (poq_mark_garbage i s)),
          (TMap.add α (deq_ret_token x) (TMap.add α deq_lini_token π1)).
        split.
        { eapply rt_trans.
          - apply rt_step. apply (ps_inv α op_deq); [| exact Htok].
            apply poq_deq_inv_step.
          - apply rt_step. apply (ps_ret α op_deq x); [| apply TMap.gss].
            apply (poq_deq_res_step α s i x); assumption. }
        split.
        + split; [| cbn [SinglePossState.π]; apply TMap.gss].
          exists (poq_mark_garbage i s). split; [reflexivity |].
          split; [apply poq_mark_garbage_wf; assumption |].
          split; [exact Hc |].
          split; [apply I_cells_mark_garbage; exact Hcells |].
          intros β n Hβ. simpl in Hβ. cbn [SinglePossState.π].
          destruct (Hpt β n Hβ) as [y [Hy Hty]].
          exists y. split; [exact Hy |].
          (* [β ≠ α]: [α] holds the dequeue token, not an enqueue token *)
          assert (Hne : β <> α).
          { intros ->. pose proof (eq_trans (eq_sym Hty) Htok) as Habs.
            injection Habs as Habs. exact (enq_lini_not_deq_inv y Habs). }
          rewrite TMap.gso by exact Hne. rewrite TMap.gso by exact Hne. exact Hty.
        + apply (g_deq α _ _ s i x); simpl; auto.
      - (* The slot was empty: no abstract step, [i] joins the scanned slots. *)
        exists (POQReady s), π1. split; [apply rt_refl |]. split.
        + exists (S i). split; [reflexivity |].
          split; [| split; [exact Htok |]].
          * exists s. split; [reflexivity |]. split; [exact Hwf |]. split; [exact Hc |].
            split; [| exact Hpt]. unfold cells_of. simpl.
            intros j y. destruct (Nat.eq_dec i j) as [-> | Hne].
            -- rewrite cell_update_same. rewrite <- Hci. apply Hcells.
            -- rewrite cell_update_other by exact Hne. apply Hcells.
          * unfold graph_of. cbn [SinglePossState.ρ poq_payload].
            split; [lia |]. split; [exact Hr |].
            intros m Hm Hl Hcomp n Hedge.
            destruct (Nat.eq_dec m i) as [-> | Hne].
            -- (* (I2): an empty slot is not live and complete *)
               exfalso. destruct (poq_vertex_some s i (proj1 Hl)) as [y Hy].
               assert (Hsome : c i = Some y) by (apply Hcells; auto). congruence.
            -- apply (Hscan m); auto; lia.
        + apply g_silent; reflexivity.
    Qed.

    (** * The method proofs *)

    Lemma lift_entails (P Q : assertion) :
      (⊨ P ==>> Q) -> ⊨ lift_assert P ==>> lift_assert Q.
    Proof. intros H s Hs. eapply lift_impl; [exact H | exact Hs]. Qed.

    (** Lemma 5.4. *)
    Lemma enq_triple α x :
      SetLogic.HTripleProvable (lift_relation (R α)) (lift_relation (G α))
        (lift_assert I) α (lift_assert (EnqStart α x)) (enq_impl x α)
        (fun _ => lift_assert (EnqDone α x)).
    Proof.
      unfold enq_impl.
      (* i <- inc(back) *)
      singleton_vis_safe (EnqStart α x) (fun i => EnqSlot α x i).
      - apply no_error.
      - apply enq_start_entails_I.
      - intros i. apply enq_slot_entails_I.
      - apply enq_start_stable.
      - intros i. apply enq_slot_stable.
      - apply silent_inv_counter. apply keep_counter_inv.
        intros w ca Hx. exact Hx.
      - apply enq_inc_update.
      - intros i.
        (* store(items[i], x) *)
        singleton_vis_safe (EnqSlot α x i) (fun _ : unit => EnqDone α x).
        + apply no_error.
        + apply enq_slot_entails_I.
        + intros _. apply enq_done_entails_I.
        + apply enq_slot_stable.
        + intros _. apply enq_done_stable.
        + apply silent_inv_cells. apply keep_cells_inv.
          intros w sa Hx. exact Hx.
        + intros []. apply enq_store_update.
        + intros []. singleton_ret_safe.
          * apply ImplRefl.
          * apply enq_done_entails_I.
          * apply enq_done_stable.
    Qed.

    (** One iteration of the inner loop: the step function of the
        [ForEach] either idles on a found value or swaps the next slot. *)
    Lemma deq_scan_step_triple α r item items acc :
      SetLogic.HTripleProvable (lift_relation (R α)) (lift_relation (G α))
        (lift_assert I) α
        (lift_assert (ScanInv α r (item :: items) acc))
        (match acc with
         | Some v => Ret (Some v)
         | None => inr (sa_swap item None) >= x => Ret x
         end)
        (fun acc' => lift_assert (ScanInv α r items acc')).
    Proof.
      destruct acc as [v|].
      - singleton_ret_safe.
        + apply ImplRefl.
        + apply found_entails_I.
        + apply found_stable.
      - (* The remaining slots are [item = i, ..., r-1]. *)
        eapply singleton_provable_linstep with (P' := ScanAt α item r items).
        + apply scan_at_entails_I.
        + apply scan_at_stable.
        + intros σ1 ρ1 π1 [i [Hitems HScan]].
          destruct (seq_cons_inv _ _ _ _ Hitems) as (-> & Hlt & ->).
          exists ρ1, π1. split; [apply rt_refl |]. split.
          * split; [exact HScan |]. split; [exact Hlt | reflexivity].
          * apply g_silent; reflexivity.
        + (* x <- swap(items[i], null) *)
          singleton_vis_safe (ScanAt α item r items)
            (fun x => ScanInv α r items x).
          * apply no_error.
          * apply scan_at_entails_I.
          * intros x. apply scan_inv_entails_I.
          * apply scan_at_stable.
          * intros x. apply scan_inv_stable.
          * apply silent_inv_cells. apply keep_cells_scan_at.
          * intros x. apply deq_swap_update.
          * intros x. singleton_ret_safe.
            -- apply ImplRefl.
            -- apply scan_inv_entails_I.
            -- apply scan_inv_stable.
    Qed.

    (** The whole scan: [ForEach] over the slots that existed when the
        counter was read. *)
    Lemma deq_scan_triple α r :
      SetLogic.HTripleProvable (lift_relation (R α)) (lift_relation (G α))
        (lift_assert I) α
        (lift_assert (ScanInv α r (seq O r) None))
        (ForEach seq O r From None Using (fun found i =>
           match found with
           | Some v => Ret (Some v)
           | None => inr (sa_swap i None) >= x => Ret x
           end))
        (fun found => lift_assert (ScanInv α r nil found)).
    Proof.
      eapply SetLogic.provable_foreach
        with (Inv := fun items acc => lift_assert (ScanInv α r items acc)).
      - intros acc. singleton_ret_safe.
        + apply ImplRefl.
        + apply scan_inv_entails_I.
        + apply scan_inv_stable.
      - intros item items acc. apply deq_scan_step_triple.
    Qed.

    (** After a full scan without success the thread is back where the
        outer loop started. *)
    Lemma scan_done_entails_deq_start α r :
      ⊨ ScanInv α r nil None ==>> DeqStart α.
    Proof.
      intros w [i [Hnil [HI [Htok _]]]]. split; assumption.
    Qed.

    (** Lemma 5.6. *)
    Lemma deq_triple α :
      SetLogic.HTripleProvable (lift_relation (R α)) (lift_relation (G α))
        (lift_assert I) α (lift_assert (DeqStart α)) (deq_impl α)
        (fun x => lift_assert (Found α x)).
    Proof.
      unfold deq_impl.
      (* while true *)
      eapply SetLogic.provable_doloop.
      - intros x. apply lift_entails. apply found_entails_I.
      - intros x. apply lift_stable. apply found_stable.
      - eapply SetLogic.provable_conseq_weak_post
          with (Q' := fun res => lift_assert
            (match res with inl _ => DeqStart α | inr x => Found α x end)).
        + intros [u | x]; simpl; apply lift_entails;
            [apply deq_start_entails_I | apply found_entails_I].
        + intros [u | x]; simpl; apply lift_stable;
            [apply deq_start_stable | apply found_stable].
        + intros [u | x]; simpl; intros w Hw; exact Hw.
        + (* r <- read(back) *)
          singleton_vis_safe (DeqStart α) (fun r => ScanInv α r (seq O r) None).
          * apply no_error.
          * apply deq_start_entails_I.
          * intros r. apply scan_inv_entails_I.
          * apply deq_start_stable.
          * intros r. apply scan_inv_stable.
          * apply silent_inv_counter. apply keep_counter_inv.
            intros w ca Hx. exact Hx.
          * apply deq_read_update.
          * intros r.
            (* for i in 0 .. r-1 *)
            eapply SetLogic.provable_seq
              with (Q' := fun found => lift_assert (ScanInv α r nil found)).
            -- apply deq_scan_triple.
            -- intros [x|].
               ++ (* return x *)
                  singleton_ret_safe.
                  ** apply ImplRefl.
                  ** apply found_entails_I.
                  ** apply found_stable.
               ++ (* next round *)
                  singleton_ret_safe.
                  ** apply scan_done_entails_deq_start.
                  ** apply deq_start_entails_I.
                  ** apply deq_start_stable.
    Qed.

    (** * Packaging (Theorem 5.7) *)

    Lemma ginv_enq_start α x :
      forall w, ComposeA I (Ginv α (op_enq x)) w -> EnqStart α x w.
    Proof.
      intros w [pre [HI [Hσ [Hρ [Hnone Hπ]]]]].
      destruct pre as [σp ρp πp], w as [σo ρo πo]. simpl in *. subst.
      destruct HI as (s & Hρ & Hwf & Hc & Hcells & Hpt).
      cbn [SinglePossState.ρ] in Hρ. subst ρo.
      split; [| split].
      - exists s. split; [reflexivity |]. split; [exact Hwf |]. split; [exact Hc |].
        split; [exact Hcells |].
        intros β n Hβ. cbn [SinglePossState.π].
        destruct (Hpt β n Hβ) as [y [Hy Hty]]. exists y.
        split; [exact Hy |]. rewrite TMap.gso; [exact Hty |].
        intros ->. pose proof (eq_trans (eq_sym Hnone) Hty) as Habs. discriminate Habs.
      - cbn [SinglePossState.π]. apply TMap.gss.
      - (* no token, hence no pending entry by [pending_tokens] *)
        unfold graph_of. cbn [SinglePossState.ρ poq_payload].
        destruct (TMap.find α (poq_pending s)) as [n|] eqn:Hn; [| reflexivity].
        destruct (Hpt α n Hn) as [y [_ Hty]].
        pose proof (eq_trans (eq_sym Hnone) Hty) as Habs. discriminate Habs.
    Qed.

    Lemma ginv_deq_start α :
      forall w, ComposeA I (Ginv α op_deq) w -> DeqStart α w.
    Proof.
      intros w [pre [HI [Hσ [Hρ [Hnone Hπ]]]]].
      destruct pre as [σp ρp πp], w as [σo ρo πo]. simpl in *. subst.
      destruct HI as (s & Hρ & Hwf & Hc & Hcells & Hpt).
      cbn [SinglePossState.ρ] in Hρ. subst ρo.
      split; [| cbn [SinglePossState.π]; apply TMap.gss].
      exists s. split; [reflexivity |]. split; [exact Hwf |]. split; [exact Hc |].
      split; [exact Hcells |].
      intros β n Hβ. cbn [SinglePossState.π].
      destruct (Hpt β n Hβ) as [y [Hy Hty]]. exists y.
      split; [exact Hy |]. rewrite TMap.gso; [exact Hty |].
      intros ->. pose proof (eq_trans (eq_sym Hnone) Hty) as Habs. discriminate Habs.
    Qed.

    Lemma gret_enq_done α x :
      forall w, ComposeA (EnqDone α x) (Gret α (op_enq x) tt) w -> I w.
    Proof.
      intros w [pre [[HI [Htok Hpend]] [Hσ [Hρ [Hsome Hπ]]]]].
      destruct pre as [σp ρp πp], w as [σo ρo πo]. simpl in *. subst.
      destruct HI as (s & Hρ & Hwf & Hc & Hcells & Hpt).
      cbn [SinglePossState.ρ] in Hρ. subst ρo.
      unfold graph_of in Hpend. cbn [SinglePossState.ρ poq_payload] in Hpend.
      exists s. split; [reflexivity |]. split; [exact Hwf |]. split; [exact Hc |].
      split; [exact Hcells |].
      intros β n Hβ. cbn [SinglePossState.π].
      destruct (Hpt β n Hβ) as [y [Hy Hty]]. exists y.
      split; [exact Hy |]. rewrite TMap.gro; [exact Hty |].
      intros ->. pose proof (eq_trans (eq_sym Hpend) Hβ) as Habs. discriminate Habs.
    Qed.

    Lemma gret_found α x :
      forall w, ComposeA (Found α x) (Gret α op_deq x) w -> I w.
    Proof.
      intros w [pre [[HI Htok] [Hσ [Hρ [Hsome Hπ]]]]].
      destruct pre as [σp ρp πp], w as [σo ρo πo]. simpl in *. subst.
      destruct HI as (s & Hρ & Hwf & Hc & Hcells & Hpt).
      cbn [SinglePossState.ρ] in Hρ. subst ρo.
      exists s. split; [reflexivity |]. split; [exact Hwf |]. split; [exact Hc |].
      split; [exact Hcells |].
      intros β n Hβ. cbn [SinglePossState.π].
      destruct (Hpt β n Hβ) as [y [Hy Hty]]. exists y.
      split; [exact Hy |]. rewrite TMap.gro; [exact Hty |].
      (* [α] holds a dequeue token, so it has no pending enqueue *)
      intros ->. pose proof (eq_trans (eq_sym Hty) Htok) as Habs.
      injection Habs as Habs. exact (enq_lini_not_deq_ret y x Habs).
    Qed.

    Lemma initial_I :
      I (mk (li_init E) (li_init F) (@TMap.empty lin_state)).
    Proof.
      exists empty_poqueue_state. split; [reflexivity |].
      split; [apply empty_poqueue_state_wf |].
      split; [reflexivity |]. split.
      - intros i x. simpl. split; [discriminate |].
        intros [[Hv _] _]. exfalso. apply Hv. reflexivity.
      - intros β n Hβ. simpl in Hβ. rewrite TMap.gempty in Hβ. discriminate.
    Qed.

    Program Definition MHWQueue : layer_implementation_simulation E F :=
    {| li_impl := hw_queue_impl |}.
    Next Obligation.
      eapply SetLogic.soundness
        with (R := fun t => lift_relation (R t))
             (G := fun t => lift_relation (G t))
             (I := lift_assert I).
      (* valid RG *)
      { intros t. eapply lift_valid_rgi. apply source_valid_rg. }
      (* cross-thread compatibility *)
      { intros t1 t2 Hneq s s' Hrel.
        eapply lift_parallel_compat; [exact Hneq | | exact Hrel].
        apply source_rg_compatible; exact Hneq. }
      (* method provable *)
      { intros t f. destruct f as [x|].
        - exists (lift_assert (EnqStart t x)).
          exists (fun _ => lift_assert (EnqDone t x)).
          constructor.
          + intros w Hcompose.
            eapply (lift_ginv_compose t (op_enq x) I (EnqStart t x));
              [apply ginv_enq_start | exact Hcompose].
          + apply lift_entails. apply enq_start_entails_I.
          + apply lift_stable. apply enq_start_stable.
          + intros [] w Hcompose.
            eapply (lift_gret_compose t (op_enq x) tt (EnqDone t x) I);
              [apply gret_enq_done | exact Hcompose].
          + intros [] σ0 Δ0 Hpost ρ0 π0 Hposs.
            eapply (lift_post_lin (EnqDone t x) t (enq_ret_token x));
              [| exact Hpost | exact Hposs].
            intros w [_ [Htok _]]. exact Htok.
          + apply enq_triple.
        - exists (lift_assert (DeqStart t)).
          exists (fun x => lift_assert (Found t x)).
          constructor.
          + intros w Hcompose.
            eapply (lift_ginv_compose t op_deq I (DeqStart t));
              [apply ginv_deq_start | exact Hcompose].
          + apply lift_entails. apply deq_start_entails_I.
          + apply lift_stable. apply deq_start_stable.
          + intros x w Hcompose.
            eapply (lift_gret_compose t op_deq x (Found t x) I);
              [apply gret_found | exact Hcompose].
          + intros x σ0 Δ0 Hpost ρ0 π0 Hposs.
            eapply (lift_post_lin (Found t x) t (deq_ret_token x));
              [| exact Hpost | exact Hposs].
            intros w [_ Htok]. exact Htok.
          + apply deq_triple. }
      (* initial singleton *)
      { apply lift_initial. apply initial_I. }
    Defined.

    Definition MHWQueueLinearizable : layer_implementation_linearizability E F :=
      LISim2LILin MHWQueue.

  End Proof.

  Print Assumptions MHWQueue.

End HWQueueProof.
