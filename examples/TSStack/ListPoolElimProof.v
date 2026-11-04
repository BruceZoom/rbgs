Require Import FMapPositive.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.
Require Import Coq.Relations.Relation_Operators.
Require Import Lia.

Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import Logics.
Require Import Assertion.
Require Import RGILogicSet.
Require Import CompLinLayer.

Require Import examples.Common.Heap.
Require Import examples.Common.ThreadDomain.
Require Import examples.TSStack.TimestampSpec.
Require Import examples.TSStack.SPListSpec.
Require Import examples.TSStack.SPListArraySpec.
Require Import examples.TSStack.ListPoolSpec.
Require Import examples.TSStack.SPListArrayProof.
Require Import examples.TSStack.ListPool.
Require Import examples.TSStack.ListPoolElimSpec.
Require Import examples.TSStack.ListPoolElim.


(** Set-based correctness proof for ListPool with elimination
    (docs/plans/TSStackEliminationPlan.tex, Section 7.1).  It is the proof
    of [ListPoolProof] extended with the pop sessions: [startPop] records
    the start set and the session token, the invariant [session_represents]
    (Lemma 4.3 of the plan) ties every start-set member to an interval
    below the session's clock bound, and the scan of [getTop start] may
    exit early on a node stamped after [start], which is reported through
    the specification's elimination response.  This layer needs genuine
    possibility families: no singleton assertion adapter is imported. *)
Module ListPoolElimProof.
  Import Reg LinCCALBase LTSSpec Lang Semantics.
  Import AssertionsSet.
  Import TimestampSpec SPListSpec SPListArraySpec ListPoolSpec ListPoolImpl.
  Import ListPoolElimSpec ListPoolElimImpl.
  Module SetLogic := RGILogicSet.RGILogic.
  Import TPSimulationSet.TPSimulation CompLinLayer.
  Import ListNotations.
  Import (coercions, canonicals, notations) Sig.
  Import (canonicals) Sig.Plus.

  Open Scope assertion_scope.
  Open Scope rg_relation_scope.

  (** Paper notation: circle is an unlinearized invocation, a bare bullet is
      an interval invocation, and a bullet carrying a result is a response. *)
  Notation "a '↦∀◦(' op ')'" := (a ↦∀ (ls_inv op))
    (at level 35, op at level 0) : assertion_scope.
  Notation "a '↦∃◦(' op ')'" := (a ↦∃ (ls_inv op))
    (at level 35, op at level 0) : assertion_scope.
  Notation "a '↦∀•(' op ')'" := (a ↦∀ (ls_lini op))
    (at level 35, op at level 0) : assertion_scope.
  Notation "a '↦∃•(' op ')'" := (a ↦∃ (ls_lini op))
    (at level 35, op at level 0) : assertion_scope.
  Notation "a '↦∀•(' op ',' ret ')'" := (a ↦∀ (ls_linr op ret))
    (at level 35, op at level 0, ret at level 0) : assertion_scope.
  Notation "a '↦∃•(' op ',' ret ')'" := (a ↦∃ (ls_linr op ret))
    (at level 35, op at level 0, ret at level 0) : assertion_scope.

  Section Proof.
    Context {A : Type} (D : ThreadDomain.t).

    Definition E : layer_interface :=
      @ListPoolElimImpl.E A D.
    Definition F : layer_interface :=
      @ListPoolElimImpl.F A D.

    Definition concrete_state := State (li_lts E).
    Definition abstract_state := State (li_lts F).
    Definition assertion :=
      @Logics.Assertion
        (@SetPossState.ProofStateSet _ _ (li_lts E) (li_lts F)).
    Definition rg_relation :=
      @AssertionsSet.A.RGRelation _ _ (li_lts E) (li_lts F).

    Definition array_payload (c : @SPListArrayControl A) :
        @SPListArrayState A :=
      match c with
      | ArrayReady a => a
      | ArrayAtomicPending a _ _ => a
      end.

    Definition concrete_array (s : concrete_state) : @SPListArrayState A :=
      array_payload (fst s).

    Definition concrete_timestamp (s : concrete_state) : TimestampState :=
      snd s.

    Definition stamped_before_clock
        (a : @SPListArrayState A) (tss : TimestampState) : Prop :=
      forall n lower upper,
        as_timestamps a n = Some (TSInterval lower upper) ->
        S upper <= ts_clock tss.

    Definition timestamp_defined (a : @SPListArrayState A) : Prop :=
      (forall n v,
        as_values a n = Some v ->
        exists ts, as_timestamps a n = Some ts /\ timestamp_wf ts) /\
      (forall n ts,
        as_timestamps a n = Some ts ->
        exists v, as_values a n = Some v) /\
      (forall n, as_garbage a n -> array_vertex a n).

    (** The concrete array order contains exactly the live nodes, and every
        allocated row belongs to the finite thread domain.  These facts are
        implicit in the paper's vertex/garbage and iterator assertions. *)
    Definition array_structural_wf (a : @SPListArrayState A) : Prop :=
      (forall owner loc,
        array_live a (pair owner loc) <->
        In loc (order_at owner a)) /\
      (forall n, array_vertex a n ->
        ThreadDomain.contains D (fst n)) /\
      (forall owner, NoDup (order_at owner a)).

    Lemma NoDup_remove_nat removed order :
      NoDup order -> NoDup (List.remove Nat.eq_dec removed order).
    Proof.
      induction order as [|head tail IH]; intro Hnodup; simpl; [constructor|].
      inversion Hnodup as [|? ? Hnotin Htail]; subst.
      destruct (Nat.eq_dec removed head) as [->|Hneq].
      - now apply IH.
      - constructor.
        + intro Hin. apply Hnotin.
          exact (proj1 (in_remove Nat.eq_dec _ _ _ Hin)).
        + now apply IH.
    Qed.

    Definition list_before (newer older : Addr) (order : list Addr) : Prop :=
      exists prefix middle suffix,
        order = prefix ++ newer :: middle ++ older :: suffix.

    Lemma list_before_cons address newer older order :
      list_before newer older order ->
      list_before newer older (address :: order).
    Proof.
      intros (prefix & middle & suffix & ->).
      exists (address :: prefix), middle, suffix. reflexivity.
    Qed.

    Lemma list_before_head newer older order :
      newer <> older -> In older order ->
      list_before newer older (newer :: order).
    Proof.
      intros Hneq Hin. destruct (in_split _ _ Hin) as (prefix & suffix & ->).
      exists nil, prefix, suffix. reflexivity.
    Qed.

    Lemma list_before_remove removed newer older order :
      removed <> newer -> removed <> older ->
      list_before newer older order ->
      list_before newer older (List.remove Nat.eq_dec removed order).
    Proof.
      intros Hnewer Holder (prefix & middle & suffix & ->).
      repeat rewrite remove_app. simpl.
      destruct (Nat.eq_dec removed newer) as [Heq|Hneq]; [contradiction|].
      rewrite remove_app. simpl.
      destruct (Nat.eq_dec removed older) as [Heq|Hneq']; [contradiction|].
      exists (List.remove Nat.eq_dec removed prefix),
        (List.remove Nat.eq_dec removed middle),
        (List.remove Nat.eq_dec removed suffix).
      reflexivity.
    Qed.

    (** Within one concrete row, live pool vertices retain allocation order,
        and distinct live vertices are comparable by a pool edge.  This is
        the graph/list bridge used by the row-top argument. *)
    Definition pool_rows_ordered
        (a : @SPListArrayState A) (p : @ListPoolState A) : Prop :=
      (forall owner newer older,
        lp_edges p (pair owner newer) (pair owner older) ->
        is_live p (pair owner newer) ->
        is_live p (pair owner older) ->
        list_before newer older (order_at owner a)) /\
      (forall owner first second,
        first <> second ->
        is_live p (pair owner first) ->
        is_live p (pair owner second) ->
        lp_edges p (pair owner first) (pair owner second) \/
        lp_edges p (pair owner second) (pair owner first)).

    Definition concrete_wf (s : concrete_state) : Prop :=
      timestamp_state_valid (concrete_timestamp s) /\
      stamped_before_clock (concrete_array s) (concrete_timestamp s) /\
      timestamp_defined (concrete_array s) /\
      array_structural_wf (concrete_array s).

    Definition outgoing_before
        (a : @SPListArrayState A) (p : @ListPoolState A)
        (newer : LPNodeId) (lower : nat) : Prop :=
      forall older, lp_edges p newer older ->
        exists old_lower old_upper,
          as_timestamps a older = Some (TSInterval old_lower old_upper) /\
          old_upper < lower.

    Definition pool_represents
        (a : @SPListArrayState A) (p : @ListPoolState A) : Prop :=
      (forall n, lp_vertices p n = as_values a n) /\
      (forall newer older,
        lp_edges p newer older -> array_edge a newer older) /\
      (forall newer older,
        lp_edges p newer older -> is_vertex p newer /\ is_vertex p older) /\
      (forall n, lp_garbage p n <-> as_garbage a n) /\
      (forall n, is_pending p n <-> as_timestamps a n = Some TSTop) /\
      (forall actor N,
        TMap.find actor (lp_snapshots p) = Some N ->
        forall n, N n -> array_vertex a n) /\
      pool_rows_ordered a p.

    Definition pool_protocol
        (p : @ListPoolState A) (pi : tmap (@LinState (li_sig F))) : Prop :=
      (forall actor loc,
        TMap.find actor (lp_pending_pushes p) = Some loc ->
        exists v, TMap.find actor pi = Some (ls_lini (lpool_push v))) /\
      (forall actor N,
        TMap.find actor (lp_snapshots p) = Some N ->
        exists start,
          TMap.find actor pi = Some (ls_lini (lpool_getTop start))) /\
      (forall actor v,
        TMap.find actor pi = Some (ls_lini (lpool_push v)) ->
        exists loc,
          TMap.find actor (lp_pending_pushes p) = Some loc) /\
      (forall actor N0,
        TMap.find actor (lp_pop_starts p) = Some N0 ->
        TMap.find actor (lp_pop_ts p) = None ->
        TMap.find actor pi = Some (ls_lini lpool_startPop)) /\
      (forall actor,
        TMap.find actor pi = Some (ls_lini lpool_startPop) ->
        TMap.find actor (lp_pop_ts p) = None /\
        exists N0, TMap.find actor (lp_pop_starts p) = Some N0) /\
      (forall actor start,
        TMap.find actor pi = Some (ls_lini (lpool_getTop start)) ->
        TMap.find actor (lp_pop_ts p) = Some start).

    (** The timestamp invocation saves the clock at which all completed
        predecessors of the pending push were already stamped.  Keeping
        this fact in the global branch invariant makes it stable across
        arbitrary interference between [newTS]'s invocation and response.
        A pending [newTS] may also belong to a [startPop] session. *)
    Definition timestamp_pending_edges
        (s : concrete_state) (p : @ListPoolState A) : Prop :=
      (forall actor lower,
        TMap.find actor (ts_pending (concrete_timestamp s)) = Some lower ->
        (exists loc, TMap.find actor (lp_pending_pushes p) = Some loc) \/
        (TMap.find actor (lp_pop_ts p) = None /\
         exists N0, TMap.find actor (lp_pop_starts p) = Some N0)) /\
      (forall actor lower loc,
        TMap.find actor (ts_pending (concrete_timestamp s)) = Some lower ->
        TMap.find actor (lp_pending_pushes p) = Some loc ->
        outgoing_before (concrete_array s) p (pair actor loc) lower).

    (** The start-set invariant (Lemma 4.3 of the elimination plan): every
        member of a recorded start set carries an interval whose upper
        endpoint lies below the session's clock bound [c].  While the
        session's [newTS] is pending, [c] is the clock it recorded; once the
        token is known, [c] is its lower endpoint. *)
    Definition session_represents
        (a : @SPListArrayState A) (tss : TimestampState)
        (p : @ListPoolState A) : Prop :=
      (forall actor N0,
        TMap.find actor (lp_pop_starts p) = Some N0 ->
        exists c,
          (forall ts, TMap.find actor (lp_pop_ts p) = Some ts ->
            exists u, ts = TSInterval c u /\ c <= u) /\
          (TMap.find actor (lp_pop_ts p) = None ->
            TMap.find actor (ts_pending tss) = Some c) /\
          (forall n, N0 n ->
            exists lower upper,
              as_timestamps a n = Some (TSInterval lower upper) /\
              upper < c)) /\
      (forall actor ts,
        TMap.find actor (lp_pop_ts p) = Some ts ->
        exists N0, TMap.find actor (lp_pop_starts p) = Some N0).

    Definition branch_represents
        (s : concrete_state) (rho : abstract_state)
        (pi : tmap (@LinState (li_sig F))) : Prop :=
      exists p,
        rho = LPReady p /\
        pool_represents (concrete_array s) p /\
        pool_protocol p pi /\
        timestamp_pending_edges s p /\
        session_represents (concrete_array s) (concrete_timestamp s) p.

    (** Possibilities differ in per-thread snapshot and linearization-map
        choices, but not in the shared ListPool graph.  Moreover those
        per-thread choices form the Cartesian family required by the
        paper's independent-snapshot connective.  This is the semantic
        fact that makes a final [getTop] commit compositional: we may select
        the acting thread's legal snapshot without discarding another
        thread's speculative choice.  The session maps are determined by
        the concrete history and are therefore shared as well. *)
    Definition pool_shared_eq
        (p q : @ListPoolState A) : Prop :=
      lp_vertices p = lp_vertices q /\
      lp_edges p = lp_edges q /\
      lp_pending_pushes p = lp_pending_pushes q /\
      lp_garbage p = lp_garbage q /\
      lp_pop_starts p = lp_pop_starts q /\
      lp_pop_ts p = lp_pop_ts q.

    Lemma pool_shared_eq_refl (p : @ListPoolState A) :
      pool_shared_eq p p.
    Proof. repeat split; reflexivity. Qed.

    Lemma pool_shared_eq_sym (p q : @ListPoolState A) :
      pool_shared_eq p q -> pool_shared_eq q p.
    Proof. unfold pool_shared_eq; intuition congruence. Qed.

    Lemma pool_shared_eq_trans (p q r : @ListPoolState A) :
      pool_shared_eq p q -> pool_shared_eq q r -> pool_shared_eq p r.
    Proof. unfold pool_shared_eq; intuition congruence. Qed.

    Lemma pool_shared_eq_start_snapshot scan (p : @ListPoolState A) :
      pool_shared_eq (start_snapshot scan p) p.
    Proof. unfold pool_shared_eq, start_snapshot; simpl; repeat split. Qed.

    Lemma pool_shared_eq_start_snapshot_compat scan
        (p q : @ListPoolState A) :
      pool_shared_eq p q ->
      pool_shared_eq (start_snapshot scan p) (start_snapshot scan q).
    Proof. unfold pool_shared_eq, start_snapshot; simpl; tauto. Qed.

    Lemma shared_is_vertex_ext (p q : @ListPoolState A) :
      pool_shared_eq p q ->
      (fun n => is_vertex p n) = (fun n => is_vertex q n).
    Proof.
      intros [Hvertices _]. apply functional_extensionality. intro n.
      unfold is_vertex. now rewrite Hvertices.
    Qed.

    Definition branch_merge (actor : tid)
        (donor_p : @ListPoolState A)
        (donor_pi : tmap (@LinState (li_sig F)))
        (receiver_p : @ListPoolState A)
        (receiver_pi : tmap (@LinState (li_sig F)))
        (merged_p : @ListPoolState A)
        (merged_pi : tmap (@LinState (li_sig F))) : Prop :=
      pool_shared_eq merged_p receiver_p /\
      TMap.find actor (lp_snapshots merged_p) =
        TMap.find actor (lp_snapshots donor_p) /\
      TMap.find actor merged_pi = TMap.find actor donor_pi /\
      (forall observer, actor <> observer ->
        TMap.find observer (lp_snapshots merged_p) =
          TMap.find observer (lp_snapshots receiver_p)) /\
      (forall observer, actor <> observer ->
        TMap.find observer merged_pi = TMap.find observer receiver_pi).

    Definition possibility_rectangular
        (Delta : @AbstractConfig _ (li_lts F)) : Prop :=
      (forall p1 pi1 p2 pi2,
        Delta (LPReady p1) pi1 -> Delta (LPReady p2) pi2 ->
        pool_shared_eq p1 p2) /\
      (forall actor p1 pi1 p2 pi2,
        Delta (LPReady p1) pi1 -> Delta (LPReady p2) pi2 ->
        exists p pi,
          Delta (LPReady p) pi /\
          branch_merge actor p1 pi1 p2 pi2 p pi).

    (** The array's aggregate-counter call is internal to [getTop].  While
        such a call is pending, every abstract possibility has already
        crossed the interval invocation of that same [getTop].  In
        particular, an idle actor or an actor at an external invocation
        cannot have a stale pending counter. *)
    Definition pending_counter_protocol
        (sigma : concrete_state)
        (Delta : @AbstractConfig _ (li_lts F)) : Prop :=
      forall actor saved,
        TMap.find actor
          (as_pending_counters (concrete_array sigma)) = Some saved ->
        exists rho pi start, Delta rho pi /\
          TMap.find actor pi = Some (ls_lini (lpool_getTop start)).

    Lemma singleton_ready_rectangular p pi :
      possibility_rectangular
        (@ac_singleton _ (li_lts F) (LPReady p) pi).
    Proof.
      split.
      - intros p1 pi1 p2 pi2 H1 H2.
        inversion H1; inversion H2; subst. repeat split; reflexivity.
      - intros actor p1 pi1 p2 pi2 H1 H2.
        inversion H1; inversion H2; subst.
        eexists; eexists. split; [constructor|].
        unfold branch_merge. repeat split; try reflexivity.
    Qed.

    Definition I : assertion :=
      fun w =>
        concrete_wf (SetPossState.σ w) /\
        (forall rho pi, SetPossState.Δ w rho pi ->
          branch_represents (SetPossState.σ w) rho pi) /\
        possibility_rectangular (SetPossState.Δ w) /\
        pending_counter_protocol
          (SetPossState.σ w) (SetPossState.Δ w).

    Lemma initial_concrete_wf : concrete_wf (li_init E).
    Proof.
      unfold concrete_wf, array_structural_wf, concrete_timestamp,
        concrete_array, array_payload,
        E, ListPoolElimImpl.E, ListPoolElimImpl.EArray,
        ListPoolElimImpl.ETimestampLayer.
      simpl. split.
      - apply initial_timestamp_state_valid.
      - split.
        + intros n lower upper Hfind. discriminate.
        + split.
          * split.
            -- intros n v Hfind. discriminate.
            -- split.
               ++ intros n ts Hfind. discriminate.
               ++ intros n Hgarbage. contradiction.
          * split.
            -- intros owner loc. split.
               ++ unfold array_live, array_vertex, empty_array_state,
                    empty_node_map. simpl. tauto.
               ++ intro Hin.
                  assert (Horder :
                    order_at owner (@empty_array_state A D) = nil).
                  { change
                      ((match TMap.find owner
                         (initial_orders (ThreadDomain.threads D)) with
                       | Some order => order
                       | None => nil
                       end) = nil).
                    destruct (ThreadDomain.contains_dec D owner)
                      as [Hinside|Houtside].
                    - rewrite SPListArrayProof.initial_orders_find_in
                        by exact Hinside. reflexivity.
                    - rewrite SPListArrayProof.initial_orders_find_out
                        by exact Houtside. reflexivity. }
                  rewrite Horder in Hin. contradiction.
            -- split.
               ++ intros n Hvertex. contradiction.
               ++ intro owner.
                  assert (Horder :
                    order_at owner (@empty_array_state A D) = nil).
                  { change
                      ((match TMap.find owner
                         (initial_orders (ThreadDomain.threads D)) with
                       | Some order => order
                       | None => nil
                       end) = nil).
                    destruct (ThreadDomain.contains_dec D owner)
                      as [Hinside|Houtside].
                    - rewrite SPListArrayProof.initial_orders_find_in
                        by exact Hinside. reflexivity.
                    - rewrite SPListArrayProof.initial_orders_find_out
                        by exact Houtside. reflexivity. }
                  rewrite Horder. constructor.
    Qed.

    Lemma initial_pool_represents :
      pool_represents (@empty_array_state A D)
        (@empty_list_pool_state A).
    Proof.
      unfold pool_represents. split.
      - intro n. reflexivity.
      - split.
        + intros newer older Hedge. contradiction.
        + split.
          * intros newer older Hedge. contradiction.
          * split.
            -- intro n. reflexivity.
            -- split.
               ++ intro n. unfold is_pending, empty_list_pool_state. simpl.
                  rewrite TMap.gempty. split; discriminate.
               ++ split.
                  ** intros actor N Hfind.
                     unfold empty_list_pool_state in Hfind. simpl in Hfind.
                     rewrite TMap.gempty in Hfind. discriminate.
                  ** split.
                     --- intros owner newer older Hedge. contradiction.
                     --- intros owner first second Hneq Hfirst.
                         unfold is_live, is_vertex, empty_list_pool_state
                           in Hfirst. simpl in Hfirst.
                         destruct Hfirst as [Hvertex _].
                         unfold empty_node_map in Hvertex. contradiction.
    Qed.

    Lemma initial_I :
      I (SetPossState.Build_ProofStateSet _ _ _ _
          (li_init E) (ac_init (li_init F))).
    Proof.
      split; [apply initial_concrete_wf|]. split.
      - intros rho pi Hposs. inversion Hposs; subst.
        exists (@empty_list_pool_state A). split; [reflexivity|].
        split; [apply initial_pool_represents|].
        split.
        + unfold pool_protocol, empty_list_pool_state. simpl.
          repeat match goal with |- _ /\ _ => split end.
          * intros actor loc Hfind. rewrite TMap.gempty in Hfind.
            discriminate.
          * intros actor N Hfind. rewrite TMap.gempty in Hfind.
            discriminate.
          * intros actor v Hfind. rewrite TMap.gempty in Hfind.
            discriminate.
          * intros actor N0 Hfind. rewrite TMap.gempty in Hfind.
            discriminate.
          * intros actor Hfind. rewrite TMap.gempty in Hfind.
            discriminate.
          * intros actor start Hfind. rewrite TMap.gempty in Hfind.
            discriminate.
        + split.
          * unfold timestamp_pending_edges, concrete_timestamp, E,
              ListPoolElimImpl.E, ListPoolElimImpl.ETimestampLayer. simpl.
            split.
            -- intros actor lower Hfind. rewrite TMap.gempty in Hfind.
               discriminate.
            -- intros actor lower loc Hfind. rewrite TMap.gempty in Hfind.
               discriminate.
          * unfold session_represents, empty_list_pool_state. simpl. split.
            -- intros actor N0 Hfind. rewrite TMap.gempty in Hfind.
               discriminate.
            -- intros actor ts Hfind. rewrite TMap.gempty in Hfind.
               discriminate.
      - split.
        + apply singleton_ready_rectangular.
        + intros actor saved Hpending.
          unfold concrete_array, array_payload, E, ListPoolElimImpl.E,
            ListPoolElimImpl.EArray in Hpending. simpl in Hpending.
          rewrite TMap.gempty in Hpending. discriminate.
    Qed.

    (** Pointwise abstract evolution.  Unlike [ac_steps], this remembers
        exactly one chosen descendant for every old possibility.  It is the
        workhorse for ordinary implementation steps: no possibility is
        accidentally collapsed merely because the concrete action is
        deterministic. *)
    Variant ac_image_prop
        (Delta : @AbstractConfig _ (li_lts F))
        (rhof : abstract_state -> abstract_state)
        (pif : tmap (@LinState (li_sig F)) ->
               tmap (@LinState (li_sig F)))
        (Hsteps : forall rho pi, Delta rho pi ->
          poss_steps (PossOk rho pi) (PossOk (rhof rho) (pif pi))) :
        @AbstractConfigProp _ (li_lts F) :=
    | ACImage rho pi (Hposs : Delta rho pi) :
        ac_image_prop Delta rhof pif Hsteps (rhof rho) (pif pi).

    Program Definition ac_image
        (Delta : @AbstractConfig _ (li_lts F))
        (rhof : abstract_state -> abstract_state)
        (pif : tmap (@LinState (li_sig F)) ->
               tmap (@LinState (li_sig F)))
        (Hsteps : forall rho pi, Delta rho pi ->
          poss_steps (PossOk rho pi) (PossOk (rhof rho) (pif pi))) :
        @AbstractConfig _ (li_lts F) :=
      {| ac_active := ac_active Delta;
         ac_prop := ac_image_prop Delta rhof pif Hsteps |}.
    Next Obligation.
      destruct (ac_nonempty Delta) as [rho [pi Hposs]].
      exists (rhof rho), (pif pi). constructor. exact Hposs.
    Qed.
    Next Obligation.
      inversion H; subst.
      eapply domain_equiv_trans.
      - apply domain_equiv_symm. eapply poss_steps_domain. apply Hsteps.
        exact Hposs.
      - eapply ac_domain. exact Hposs.
    Qed.

    Lemma ac_image_subset_steps Delta rhof pif Hsteps :
      ac_subset (ac_image Delta rhof pif Hsteps) (ac_steps Delta).
    Proof.
      intros rho pi Himage. inversion Himage; subst.
      econstructor; eauto.
    Qed.

    Lemma ac_image_elim Delta rhof pif Hsteps rho' pi' :
      ac_image Delta rhof pif Hsteps rho' pi' ->
      exists rho pi, Delta rho pi /\ rho' = rhof rho /\ pi' = pif pi.
    Proof. inversion 1; subst. eauto. Qed.

    Definition token_view
        (observer : tid) (Delta : @AbstractConfig _ (li_lts F))
        (token : option (@LinState (li_sig F))) : Prop :=
      exists rho pi, Delta rho pi /\ TMap.find observer pi = token.

    Definition token_equiv
        (observer : tid) (Delta Delta' : @AbstractConfig _ (li_lts F)) : Prop :=
      forall token,
        token_view observer Delta token <->
        token_view observer Delta' token.

    Lemma token_equiv_refl observer Delta :
      token_equiv observer Delta Delta.
    Proof. firstorder. Qed.

    Lemma token_equiv_sym observer Delta Delta' :
      token_equiv observer Delta Delta' ->
      token_equiv observer Delta' Delta.
    Proof. unfold token_equiv. firstorder. Qed.

    Lemma token_equiv_trans observer Delta1 Delta2 Delta3 :
      token_equiv observer Delta1 Delta2 ->
      token_equiv observer Delta2 Delta3 ->
      token_equiv observer Delta1 Delta3.
    Proof.
      intros H12 H23 token. split; intro Hview.
      - apply (proj1 (H23 token)), (proj1 (H12 token)); exact Hview.
      - apply (proj2 (H12 token)), (proj2 (H23 token)); exact Hview.
    Qed.

    (** Interference may add speculative branches in which a pending
        [getTop] invocation has taken its interval invocation.  Every old
        token view is retained; the only genuinely new token view is that
        [getTop] linearizing state, justified by an old invocation view. *)
    Definition token_rely
        (observer : tid) (Delta Delta' : @AbstractConfig _ (li_lts F)) : Prop :=
      (forall token,
        token_view observer Delta token ->
        token_view observer Delta' token) /\
      (forall token,
        token_view observer Delta' token ->
        token_view observer Delta token \/
        (exists start,
          token = Some (ls_lini (lpool_getTop start)) /\
          token_view observer Delta (Some (ls_inv (lpool_getTop start))))).

    Lemma token_equiv_rely observer Delta Delta' :
      token_equiv observer Delta Delta' ->
      token_rely observer Delta Delta'.
    Proof. unfold token_equiv, token_rely. firstorder. Qed.

    Lemma token_rely_refl observer Delta :
      token_rely observer Delta Delta.
    Proof. apply token_equiv_rely, token_equiv_refl. Qed.

    Lemma token_rely_trans observer Delta1 Delta2 Delta3 :
      token_rely observer Delta1 Delta2 ->
      token_rely observer Delta2 Delta3 ->
      token_rely observer Delta1 Delta3.
    Proof.
      intros [H12keep H12new] [H23keep H23new]. split.
      - intros token Hview. now apply H23keep, H12keep.
      - intros token Hview.
        destruct (H23new token Hview) as [Hview2| (start & Htok & Hinv2) ].
        + destruct (H12new token Hview2) as [Hview1|Hnew]; auto.
        + subst token. right. exists start. split; [reflexivity|].
          destruct (H12new _ Hinv2) as [Hinv1| (start' & Heq & Hbad) ];
            [exact Hinv1|discriminate Heq].
    Qed.

    Lemma token_view_ALinExists sigma observer Delta ls :
      token_view observer Delta (Some ls) <->
      ALinExists observer ls
        (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          sigma Delta).
    Proof.
      split.
      - intros (rho & pi & Hposs & Hfind).
        pose (single := @ac_singleton _ (li_lts F) rho pi).
        assert (Hactive :
          domain_equiv (ac_active single) (ac_active Delta)).
        { unfold single. eapply domain_equiv_trans.
          - apply ac_singleton_active.
          - exact (ac_domain Delta _ _ Hposs). }
        pose (joined := @ac_union _ (li_lts F) single Delta Hactive).
        assert (Hequiv : ac_equiv joined Delta).
        { intros rho' pi'. split.
          - intro Hjoined. destruct (ac_union_cases _ _ _ _ _ Hjoined)
              as [Hsingle|HDelta]; [|exact HDelta].
            inversion Hsingle; subst. exact Hposs.
          - intro HDelta. apply ac_union_right. exact HDelta. }
        assert (Heq : joined = Delta) by
          (apply AbstractConfig_ext; exact Hequiv).
        unfold ALinExists, SpecUnion. exists
          (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
            sigma single),
          (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
            sigma Delta).
        split.
        + unfold ALin. intros rho' pi' Hsingle.
          change (ac_singleton_prop rho pi rho' pi') in Hsingle.
          destruct Hsingle. exact Hfind.
        + split; [constructor|].
          assert (Hunion : spec_union
            (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
              sigma single)
            (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
              sigma Delta)
            (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
              sigma joined)) by constructor.
          rewrite Heq in Hunion. exact Hunion.
      - intros (w1 & w2 & Hlin & HT & Hunion).
        destruct w1 as [sigma1 Delta1].
        destruct w2 as [sigma2 Delta2].
        inversion Hunion; subst.
        destruct (ac_nonempty Delta1)
          as (rho & pi & Hposs).
        exists rho, pi. split.
        + apply ac_union_left. exact Hposs.
        + exact (Hlin _ _ Hposs).
    Qed.

    Lemma token_equiv_ALinExists observer Delta Delta' ls :
      token_equiv observer Delta Delta' ->
      forall sigma sigma',
        ALinExists observer ls
          (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
            sigma Delta) ->
        ALinExists observer ls
          (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
            sigma' Delta').
    Proof.
      intros Hequiv sigma sigma' Hexists.
      apply (proj1 (token_view_ALinExists sigma' observer Delta' ls)).
      apply (proj1 (Hequiv (Some ls))).
      apply (proj2 (token_view_ALinExists sigma observer Delta ls)).
      exact Hexists.
    Qed.

    Lemma token_rely_ALinExists observer Delta Delta' ls :
      token_rely observer Delta Delta' ->
      forall sigma sigma',
        ALinExists observer ls
          (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
            sigma Delta) ->
        ALinExists observer ls
          (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
            sigma' Delta').
    Proof.
      intros [Hkeep Hnew] sigma sigma' Hexists.
      apply (proj1 (token_view_ALinExists sigma' observer Delta' ls)).
      apply Hkeep.
      now apply (proj2 (token_view_ALinExists sigma observer Delta ls)).
    Qed.

    Lemma token_equiv_image_other actor observer Delta rhof pi Hsteps :
      actor <> observer ->
      token_equiv observer Delta
        (ac_image Delta rhof (fun tokens => TMap.add actor pi tokens) Hsteps).
    Proof.
      intros Hneq token. split.
      - intros (rho & tokens & Hposs & Hfind).
        exists (rhof rho), (TMap.add actor pi tokens). split.
        + constructor. exact Hposs.
        + rewrite TMap.gso by congruence. exact Hfind.
      - intros (rho' & tokens' & Himage & Hfind).
        inversion Himage; subst. exists rho, pi0. split; [exact Hposs|].
        rewrite TMap.gso by congruence. reflexivity.
    Qed.

    Lemma token_equiv_image_foreign observer Delta rhof pif Hsteps :
      (forall pi, TMap.find observer (pif pi) =
        TMap.find observer pi) ->
      token_equiv observer Delta (ac_image Delta rhof pif Hsteps).
    Proof.
      intros Hforeign token. split.
      - intros (rho & pi & Hposs & Hfind). exists (rhof rho), (pif pi).
        split; [constructor; exact Hposs|]. rewrite Hforeign. exact Hfind.
      - intros (rho' & pi' & Himage & Hfind).
        destruct (ac_image_elim _ _ _ _ _ _ Himage) as
          (rho & pi & Hposs & -> & ->).
        exists rho, pi. split; [exact Hposs|].
        rewrite Hforeign in Hfind. exact Hfind.
    Qed.

    Definition pool_local_state (observer : tid) (rho : abstract_state) :
        prod (option Addr) (option LPNodeSet) :=
      match rho with
      | LPReady p | LPAtomicPending p _ _ =>
          pair (TMap.find observer (lp_pending_pushes p))
            (TMap.find observer (lp_snapshots p))
      end.

    Definition pool_local_view observer
        (Delta : @AbstractConfig _ (li_lts F)) local : Prop :=
      exists rho pi, Delta rho pi /\ pool_local_state observer rho = local.

    (** Existing snapshot alternatives may be retained and new alternatives
        may be added by a concurrent push.  The pending-push component is
        observationally fixed: every new local view has the same pending
        component as some old one.  This is the set-level form of the
        paper's monotone [gettingT] family. *)
    Definition pool_local_equiv observer
        (Delta Delta' : @AbstractConfig _ (li_lts F)) : Prop :=
      (forall local,
        pool_local_view observer Delta local ->
        pool_local_view observer Delta' local) /\
      (forall local',
        pool_local_view observer Delta' local' ->
        exists local,
          pool_local_view observer Delta local /\
          fst local = fst local').

    Lemma pool_local_equiv_refl observer Delta :
      pool_local_equiv observer Delta Delta.
    Proof.
      split; [firstorder|]. intros local Hview.
      exists local. auto.
    Qed.

    Lemma pool_local_equiv_image_foreign observer Delta rhof pif Hsteps :
      (forall rho, pool_local_state observer (rhof rho) =
        pool_local_state observer rho) ->
      pool_local_equiv observer Delta (ac_image Delta rhof pif Hsteps).
    Proof.
      intro Hlocal. split.
      - intros local (rho & pi & Hposs & Hview).
        exists (rhof rho), (pif pi). split; [constructor; exact Hposs|].
        rewrite Hlocal. exact Hview.
      - intros local' (rho' & pi' & Himage & Hview).
        destruct (ac_image_elim _ _ _ _ _ _ Himage) as
          (rho & pi & Hposs & -> & ->).
        exists (pool_local_state observer rho). split.
        + exists rho, pi. split; [exact Hposs|reflexivity].
        + rewrite Hlocal in Hview. exact (f_equal fst Hview).
    Qed.

    (** The per-thread pop-session view: the recorded start set and the
        session token.  Both are determined by the concrete history, so
        every possibility agrees on them; interference by other threads
        preserves the set of session views of an observer. *)
    Definition session_state (observer : tid) (rho : abstract_state) :
        prod (option LPNodeSet) (option TS) :=
      match rho with
      | LPReady p | LPAtomicPending p _ _ =>
          pair (TMap.find observer (lp_pop_starts p))
            (TMap.find observer (lp_pop_ts p))
      end.

    Definition session_ts (observer : tid) (rho : abstract_state) :
        option TS :=
      snd (session_state observer rho).

    Definition session_starts (observer : tid) (rho : abstract_state) :
        option LPNodeSet :=
      fst (session_state observer rho).

    Definition session_view observer
        (Delta : @AbstractConfig _ (li_lts F)) sess : Prop :=
      exists rho pi, Delta rho pi /\ session_state observer rho = sess.

    Definition session_equiv observer
        (Delta Delta' : @AbstractConfig _ (li_lts F)) : Prop :=
      forall sess,
        session_view observer Delta sess <->
        session_view observer Delta' sess.

    Lemma session_equiv_refl observer Delta :
      session_equiv observer Delta Delta.
    Proof. firstorder. Qed.

    Lemma session_equiv_sym observer Delta Delta' :
      session_equiv observer Delta Delta' ->
      session_equiv observer Delta' Delta.
    Proof. unfold session_equiv. firstorder. Qed.

    Lemma session_equiv_trans observer Delta1 Delta2 Delta3 :
      session_equiv observer Delta1 Delta2 ->
      session_equiv observer Delta2 Delta3 ->
      session_equiv observer Delta1 Delta3.
    Proof.
      intros H12 H23 sess. split; intro Hview.
      - apply (proj1 (H23 sess)), (proj1 (H12 sess)); exact Hview.
      - apply (proj2 (H12 sess)), (proj2 (H23 sess)); exact Hview.
    Qed.

    Lemma session_equiv_image_foreign observer Delta rhof pif Hsteps :
      (forall rho, session_state observer (rhof rho) =
        session_state observer rho) ->
      session_equiv observer Delta (ac_image Delta rhof pif Hsteps).
    Proof.
      intro Hlocal. intro sess. split.
      - intros (rho & pi & Hposs & Hview).
        exists (rhof rho), (pif pi). split; [constructor; exact Hposs|].
        rewrite Hlocal. exact Hview.
      - intros (rho' & pi' & Himage & Hview).
        destruct (ac_image_elim _ _ _ _ _ _ Himage) as
          (rho & pi & Hposs & -> & ->).
        exists rho, pi. split; [exact Hposs|].
        rewrite Hlocal in Hview. exact Hview.
    Qed.

    (** A view-preserving map between configurations preserves the
        session views. *)
    Lemma session_equiv_of_covers observer
        (Delta Delta' : @AbstractConfig _ (li_lts F)) :
      (forall rho pi, Delta rho pi ->
        exists rho' pi', Delta' rho' pi' /\
          session_state observer rho' = session_state observer rho) ->
      (forall rho' pi', Delta' rho' pi' ->
        exists rho pi, Delta rho pi /\
          session_state observer rho = session_state observer rho') ->
      session_equiv observer Delta Delta'.
    Proof.
      intros Hforward Hback sess. split.
      - intros (rho & pi & Hposs & Hview).
        destruct (Hforward _ _ Hposs) as (rho' & pi' & Hposs' & Heq).
        exists rho', pi'. split; [exact Hposs'|congruence].
      - intros (rho' & pi' & Hposs' & Hview).
        destruct (Hback _ _ Hposs') as (rho & pi & Hposs & Heq).
        exists rho, pi. split; [exact Hposs|congruence].
    Qed.

    Lemma session_state_shared observer p q :
      pool_shared_eq p q ->
      session_state observer (LPReady p) = session_state observer (LPReady q).
    Proof.
      intros (_ & _ & _ & _ & Hstarts & Hts). simpl.
      rewrite Hstarts, Hts. reflexivity.
    Qed.

    (** Uniform session facts of a thread, used by its own [getTop]. *)
    Definition SessionToken (actor : tid) (start : TS) : assertion :=
      fun w => forall rho pi, SetPossState.Δ w rho pi ->
        session_ts actor rho = Some start.

    Definition StartSet (actor : tid) (N0 : LPNodeSet) : assertion :=
      fun w => forall rho pi, SetPossState.Δ w rho pi ->
        session_starts actor rho = Some N0.

    Lemma session_token_equiv actor start Delta Delta' :
      session_equiv actor Delta Delta' ->
      (forall rho pi, Delta rho pi -> session_ts actor rho = Some start) ->
      forall rho pi, Delta' rho pi -> session_ts actor rho = Some start.
    Proof.
      intros Hequiv Hall rho pi Hposs.
      destruct (proj2 (Hequiv (session_state actor rho))
        (ex_intro _ rho (ex_intro _ pi (conj Hposs eq_refl)))) as
        (rho0 & pi0 & Hposs0 & Heq).
      unfold session_ts. rewrite <- Heq. now apply Hall with pi0.
    Qed.

    Lemma start_set_equiv actor N0 Delta Delta' :
      session_equiv actor Delta Delta' ->
      (forall rho pi, Delta rho pi -> session_starts actor rho = Some N0) ->
      forall rho pi, Delta' rho pi -> session_starts actor rho = Some N0.
    Proof.
      intros Hequiv Hall rho pi Hposs.
      destruct (proj2 (Hequiv (session_state actor rho))
        (ex_intro _ rho (ex_intro _ pi (conj Hposs eq_refl)))) as
        (rho0 & pi0 & Hposs0 & Heq).
      unfold session_starts. rewrite <- Heq. now apply Hall with pi0.
    Qed.

    Lemma session_mismatch_equiv actor start Delta Delta' :
      session_equiv actor Delta Delta' ->
      (forall rho pi, Delta rho pi -> session_ts actor rho <> Some start) ->
      forall rho pi, Delta' rho pi -> session_ts actor rho <> Some start.
    Proof.
      intros Hequiv Hall rho pi Hposs.
      destruct (proj2 (Hequiv (session_state actor rho))
        (ex_intro _ rho (ex_intro _ pi (conj Hposs eq_refl)))) as
        (rho0 & pi0 & Hposs0 & Heq).
      unfold session_ts. rewrite <- Heq. now apply Hall with pi0.
    Qed.

    Lemma session_token_stable actor start sigma sigma'
        (Delta Delta' : @AbstractConfig _ (li_lts F)) :
      session_equiv actor Delta Delta' ->
      SessionToken actor start
        (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          sigma Delta) ->
      SessionToken actor start
        (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          sigma' Delta').
    Proof.
      intros Hequiv Hall rho pi Hposs.
      eapply session_token_equiv; [exact Hequiv|exact Hall|exact Hposs].
    Qed.

    Lemma start_set_stable actor N0 sigma sigma'
        (Delta Delta' : @AbstractConfig _ (li_lts F)) :
      session_equiv actor Delta Delta' ->
      StartSet actor N0
        (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          sigma Delta) ->
      StartSet actor N0
        (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          sigma' Delta').
    Proof.
      intros Hequiv Hall rho pi Hposs.
      eapply start_set_equiv; [exact Hequiv|exact Hall|exact Hposs].
    Qed.

    Definition push_causal actor loc lower : assertion :=
      fun w => forall rho pi, SetPossState.Δ w rho pi ->
        exists p,
          rho = LPReady p /\
          TMap.find actor (lp_pending_pushes p) = Some loc /\
          outgoing_before (concrete_array (SetPossState.σ w)) p
            (pair actor loc) lower.

    Definition visited_top (done : list tid) (p : @ListPoolState A)
        (N : LPNodeSet) (n : LPNodeId) : Prop :=
      N n /\
      ~ lp_garbage p n /\
      forall newer,
        N newer -> In (fst newer) done -> ~ lp_garbage p newer ->
        ~ lp_edges p newer n.

    Definition candidate_tstop_safe (candidate : @Candidate A)
        (p : @ListPoolState A) (N : LPNodeSet) : Prop :=
      match candidate_timestamp candidate with
      | TSTop =>
          forall newer, N newer -> ~ lp_garbage p newer ->
            ~ lp_edges p newer
              (pair (candidate_owner candidate) (candidate_loc candidate))
      | TSInterval _ _ => True
      end.

    Definition candidate_interval_valid (candidate : @Candidate A)
        (a : @SPListArrayState A) : Prop :=
      match candidate_timestamp candidate with
      | TSTop => True
      | TSInterval lower upper =>
          as_timestamps a
            (pair (candidate_owner candidate) (candidate_loc candidate)) =
          Some (TSInterval lower upper)
      end.

    (** A candidate witness is an actual [gettingT] branch.  Its candidate
        is either already garbage (the paper's garbage alternative), or is
        top among the rows visited so far. *)
    Definition candidate_view (observer : tid) (done : list tid)
        (candidate : @Candidate A)
        (Delta : @AbstractConfig _ (li_lts F)) : Prop :=
      let n := pair (candidate_owner candidate) (candidate_loc candidate) in
      exists p pi N,
        Delta (LPReady p) pi /\
        (exists start,
          TMap.find observer pi = Some (ls_lini (lpool_getTop start))) /\
        TMap.find observer (lp_snapshots p) = Some N /\
        lp_vertices p n = Some (candidate_value candidate) /\
        In (candidate_owner candidate) done /\
        (lp_garbage p n \/ visited_top done p N n) /\
        candidate_tstop_safe candidate p N.

    Definition candidate_views_preserved observer
        (Delta Delta' : @AbstractConfig _ (li_lts F)) : Prop :=
      forall done candidate,
        candidate_view observer done candidate Delta ->
        candidate_view observer done candidate Delta'.

    Lemma candidate_views_preserved_refl observer Delta :
      candidate_views_preserved observer Delta Delta.
    Proof. intros done candidate Hview. exact Hview. Qed.

    Definition row_snapshot_view (observer owner : tid)
        (saved : list Addr) (Delta : @AbstractConfig _ (li_lts F)) : Prop :=
      exists p pi N,
        Delta (LPReady p) pi /\
        (exists start,
          TMap.find observer pi = Some (ls_lini (lpool_getTop start))) /\
        TMap.find observer (lp_snapshots p) = Some N /\
        (forall loc, In loc saved -> N (pair owner loc)) /\
        (forall loc, N (pair owner loc) ->
          ~ lp_garbage p (pair owner loc) -> In loc saved) /\
        (forall newer older,
          N (pair owner newer) -> N (pair owner older) ->
          ~ lp_garbage p (pair owner newer) ->
          ~ lp_garbage p (pair owner older) ->
          lp_edges p (pair owner newer) (pair owner older) ->
          list_before newer older saved).

    Definition row_snapshot_views_preserved observer
        (Delta Delta' : @AbstractConfig _ (li_lts F)) : Prop :=
      forall owner saved,
        row_snapshot_view observer owner saved Delta ->
        row_snapshot_view observer owner saved Delta'.

    Lemma row_snapshot_views_preserved_refl observer Delta :
      row_snapshot_views_preserved observer Delta Delta.
    Proof. firstorder. Qed.

    (** During one concrete row call, an already selected candidate and the
        coverage facts for the row being scanned must refer to the same
        speculative ListPool snapshot.  Keeping these facts in one
        existential avoids combining unrelated [↦∃] branches. *)
    Definition candidate_row_view (observer : tid) (done : list tid)
        (candidate : @Candidate A) (owner : tid) (saved : list Addr)
        (Delta : @AbstractConfig _ (li_lts F)) : Prop :=
      let n := pair (candidate_owner candidate) (candidate_loc candidate) in
      exists p pi N,
        Delta (LPReady p) pi /\
        (exists start,
          TMap.find observer pi = Some (ls_lini (lpool_getTop start))) /\
        TMap.find observer (lp_snapshots p) = Some N /\
        lp_vertices p n = Some (candidate_value candidate) /\
        In (candidate_owner candidate) done /\
        (lp_garbage p n \/ visited_top done p N n) /\
        (forall loc, N (pair owner loc) ->
          ~ lp_garbage p (pair owner loc) -> In loc saved) /\
        (forall newer older,
          N (pair owner newer) -> N (pair owner older) ->
          ~ lp_garbage p (pair owner newer) ->
          ~ lp_garbage p (pair owner older) ->
          lp_edges p (pair owner newer) (pair owner older) ->
          list_before newer older saved) /\
        candidate_tstop_safe candidate p N.

    Definition candidate_row_views_preserved observer
        (Delta Delta' : @AbstractConfig _ (li_lts F)) : Prop :=
      forall done candidate owner saved,
        candidate_row_view observer done candidate owner saved Delta ->
        candidate_row_view observer done candidate owner saved Delta'.

    Lemma candidate_row_views_preserved_refl observer Delta :
      candidate_row_views_preserved observer Delta Delta.
    Proof. intros done candidate owner saved Hview. exact Hview. Qed.

    Lemma candidate_row_views_preserved_mono observer
        (Delta Delta' : @AbstractConfig _ (li_lts F)) :
      (forall rho pi, Delta rho pi -> Delta' rho pi) ->
      candidate_row_views_preserved observer Delta Delta'.
    Proof.
      intros Hmono done candidate owner saved Hview.
      unfold candidate_row_view in *.
      destruct Hview as
        (p & pi & N & Hposs & Htoken & Hsnapshot & Hvalue & Hdone &
          Hstatus & Hcovered & Horder & Hsafe).
      exists p, pi, N. repeat split; try assumption. now apply Hmono.
    Qed.

    Lemma candidate_row_views_preserved_trans observer Delta1 Delta2 Delta3 :
      candidate_row_views_preserved observer Delta1 Delta2 ->
      candidate_row_views_preserved observer Delta2 Delta3 ->
      candidate_row_views_preserved observer Delta1 Delta3.
    Proof.
      intros H12 H23 done candidate owner saved Hview.
      apply H23. now apply H12.
    Qed.

    (** Direct, proof-relevant replacement for the paper's finite
        [I_ignore] elimination.  A node cut is a real snapshot possibility
        containing [n] in which no live incoming predecessor of [n] is
        classified [Ignored] by the concrete iterator.  Old cuts are retained
        across later ignored pushes; a nonignored new push receives a fresh
        cut at its own insertion. *)
    Definition node_cut_view (observer : tid) (progress : ScanProgress)
        (n : LPNodeId) (value : A)
        (Delta : @AbstractConfig _ (li_lts F)) : Prop :=
      exists p pi N,
        Delta (LPReady p) pi /\
        (exists start,
          TMap.find observer pi = Some (ls_lini (lpool_getTop start))) /\
        TMap.find observer (lp_snapshots p) = Some N /\
        lp_vertices p n = Some value /\
        N n /\
        forall newer,
          N newer -> ~ lp_garbage p newer -> lp_edges p newer n ->
          ~ scan_status progress newer Ignored.

    Definition node_cuts_available (observer : tid)
        (progress : ScanProgress) (a : @SPListArrayState A)
        (Delta : @AbstractConfig _ (li_lts F)) : Prop :=
      forall n value,
        array_live a n ->
        as_values a n = Some value ->
        ~ scan_status progress n Ignored ->
        node_cut_view observer progress n value Delta.

    Lemma empty_scan_not_ignored n :
      ~ scan_status empty_scan n Ignored.
    Proof.
      intro Hstatus. inversion Hstatus; subst; simpl in *;
        try contradiction; discriminate.
    Qed.

    Definition node_cuts_preserved observer
        (s s' : concrete_state)
        (Delta Delta' : @AbstractConfig _ (li_lts F)) : Prop :=
      forall progress start,
        ThreadDomain.contains D observer ->
        token_view observer Delta (Some (ls_inv (lpool_getTop start))) ->
        (forall rho pi, Delta rho pi -> session_ts observer rho = Some start) ->
        node_cuts_available observer progress (concrete_array s) Delta ->
        node_cuts_available observer progress (concrete_array s') Delta'.

    Lemma node_cuts_preserved_refl observer s Delta :
      node_cuts_preserved observer s s Delta Delta.
    Proof. firstorder. Qed.

    Lemma node_cuts_preserved_same_array observer s s' Delta :
      concrete_array s = concrete_array s' ->
      node_cuts_preserved observer s s' Delta Delta.
    Proof.
      intros Hsame progress start Hinside Hfallback Hsession Hcuts.
      rewrite <- Hsame. exact Hcuts.
    Qed.

    Definition garbage_evolves (s s' : concrete_state) : Prop :=
      forall n, as_garbage (concrete_array s) n ->
        as_garbage (concrete_array s') n.

    Lemma garbage_evolves_refl s : garbage_evolves s s.
    Proof. firstorder. Qed.

    Lemma garbage_evolves_same_array s s' :
      concrete_array s = concrete_array s' -> garbage_evolves s s'.
    Proof. unfold garbage_evolves. intros Hsame. now rewrite Hsame. Qed.

    Definition intervals_evolve (s s' : concrete_state) : Prop :=
      (forall n ts,
        as_timestamps (concrete_array s) n = Some ts ->
        exists ts', as_timestamps (concrete_array s') n = Some ts') /\
      (forall n lower upper,
        as_timestamps (concrete_array s) n =
          Some (TSInterval lower upper) ->
        as_timestamps (concrete_array s') n =
          Some (TSInterval lower upper)) /\
      (forall n v,
        as_values (concrete_array s) n = Some v ->
        as_values (concrete_array s') n = Some v).

    Lemma intervals_evolve_refl s : intervals_evolve s s.
    Proof. split; [firstorder|]. split; firstorder. Qed.

    Lemma intervals_evolve_same_array s s' :
      concrete_array s = concrete_array s' -> intervals_evolve s s'.
    Proof.
      unfold intervals_evolve. intros Hsame. rewrite Hsame.
      split; [firstorder|]. split; firstorder.
    Qed.

    Lemma candidate_status_mark_garbage done p N n removed :
      lp_garbage p n \/ visited_top done p N n ->
      lp_garbage (mark_garbage removed p) n \/
        visited_top done (mark_garbage removed p) N n.
    Proof.
      intros [Hgarbage|[Hmember [Hlive Htop]]].
      - left. simpl. unfold set_add. right. exact Hgarbage.
      - destruct (node_eq_dec n removed) as [->|Hneq].
        + left. simpl. unfold set_add. left. reflexivity.
        + right. split; [exact Hmember|]. split.
          * simpl. unfold set_add. intros [Heq|Hgarbage]; auto.
          * intros newer Hnewer Hdone Hnewer_live.
            apply Htop; try assumption. intro Hgarbage.
            apply Hnewer_live. simpl. unfold set_add. right. exact Hgarbage.
    Qed.

    Lemma candidate_tstop_safe_mark_garbage candidate p (N : LPNodeSet) removed :
      candidate_tstop_safe candidate p N ->
      candidate_tstop_safe candidate (mark_garbage removed p) N.
    Proof.
      unfold candidate_tstop_safe. destruct (candidate_timestamp candidate);
        simpl; auto.
      intros Hsafe newer Hmember Hlive Hedge.
      eapply Hsafe; [exact Hmember| |exact Hedge].
      intro Hgarbage. apply Hlive. unfold set_add. now right.
    Qed.

    Lemma candidate_status_start_push done p (N : LPNodeSet) n actor loc (v : A) :
      fresh_node p (pair actor loc) ->
      (forall node, N node -> is_vertex p node) ->
      (lp_garbage p n \/ visited_top done p N n) ->
      lp_garbage (start_push actor loc v p) n \/
        visited_top done (start_push actor loc v p) N n.
    Proof.
      intros Hfresh Hsnapshot [Hgarbage|[Hmember [Hlive Htop]]].
      - left. exact Hgarbage.
      - right. split; [exact Hmember|]. split; [exact Hlive|].
        intros newer Hnewer Hdone Hnewer_live Hedge.
        simpl in Hedge. destruct Hedge as [Hedge|[Heq [Hold_live Hstable]]].
        + eapply Htop; eauto.
        + subst newer. destruct Hfresh as [Hfresh_value _].
          apply (Hsnapshot (pair actor loc) Hnewer).
          unfold is_vertex. rewrite Hfresh_value. reflexivity.
    Qed.

    Lemma candidate_tstop_safe_start_push candidate p (N : LPNodeSet)
        actor loc (v : A) :
      fresh_node p (pair actor loc) ->
      (forall node, N node -> is_vertex p node) ->
      candidate_tstop_safe candidate p N ->
      candidate_tstop_safe candidate (start_push actor loc v p) N.
    Proof.
      intros Hfresh Hsnapshot.
      unfold candidate_tstop_safe.
      destruct (candidate_timestamp candidate); simpl; auto.
      intros Hsafe newer Hmember Hlive Hedge.
      simpl in Hedge. destruct Hedge as [Hold|[Heq Hgenerated]].
      - eapply Hsafe; eauto.
      - subst newer. exfalso. apply (Hsnapshot _ Hmember).
        exact (proj1 Hfresh).
    Qed.

    Lemma candidate_tstop_safe_finish_push candidate p (N : LPNodeSet) actor :
      candidate_tstop_safe candidate p N ->
      candidate_tstop_safe candidate (finish_push actor p) N.
    Proof. unfold candidate_tstop_safe; destruct (candidate_timestamp candidate);
      simpl; auto. Qed.

    Definition array_local_state (observer : tid) (s : concrete_state) :
        prod (option ScanProgress) (option nat) :=
      pair (TMap.find observer (as_scans (concrete_array s)))
        (TMap.find observer
          (as_pending_counters (concrete_array s))).

    (** Counters never decrease.  If a row counter is unchanged, its live
        order can only shrink.  This is the rely fact used by the paper's
        accumulated-counter empty-pool argument. *)
    Definition array_evolves (s s' : concrete_state) : Prop :=
      forall owner,
        counter_at owner (concrete_array s) <=
          counter_at owner (concrete_array s') /\
        (counter_at owner (concrete_array s) =
           counter_at owner (concrete_array s') ->
         incl (order_at owner (concrete_array s'))
           (order_at owner (concrete_array s))).

    Lemma array_evolves_refl s : array_evolves s s.
    Proof.
      intro owner. split; [lia|]. intros Heq address Hin. exact Hin.
    Qed.

    Lemma array_evolves_same_array s s' :
      concrete_array s = concrete_array s' ->
      array_evolves s s'.
    Proof.
      intro Hsame. unfold array_evolves. intro owner.
      rewrite Hsame. split; [lia|]. intros Heq address Hin. exact Hin.
    Qed.

    Lemma array_evolves_of_counter_order s s' :
      (forall owner,
        counter_at owner (concrete_array s) =
        counter_at owner (concrete_array s')) ->
      (forall owner,
        order_at owner (concrete_array s) =
        order_at owner (concrete_array s')) ->
      array_evolves s s'.
    Proof.
      intros Hcounter Horder owner. rewrite <- Hcounter, <- Horder.
      split; [lia|]. intros Heq address Hin. exact Hin.
    Qed.

    Lemma array_evolves_insert (a : @SPListArrayState A)
        tss actor loc (v : A) :
      array_evolves (pair (ArrayReady a) tss)
        (pair (ArrayReady (insert_node actor loc v a)) tss).
    Proof.
      intro owner. unfold concrete_array, array_payload. simpl.
      destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
      - assert (Hcounter :
          counter_at actor (insert_node actor loc v a) =
          S (counter_at actor a)).
        { unfold counter_at, insert_node. simpl. rewrite TMap.gss.
          reflexivity. }
        rewrite Hcounter. split; [lia|]. intro Heq. exfalso. lia.
      - assert (Hcounter :
          counter_at owner (insert_node actor loc v a) =
          counter_at owner a).
        { unfold counter_at, insert_node. simpl.
          rewrite TMap.gso by congruence. reflexivity. }
        assert (Horder :
          order_at owner (insert_node actor loc v a) = order_at owner a).
        { unfold order_at, insert_node. simpl.
          rewrite TMap.gso by congruence. reflexivity. }
        rewrite Hcounter, Horder. split; [lia|].
        intros Heq address Hin. exact Hin.
    Qed.

    Lemma array_evolves_remove (a : @SPListArrayState A)
        tss (n : LPNodeId) :
      array_evolves (pair (ArrayReady a) tss)
        (pair (ArrayReady (remove_node n a)) tss).
    Proof.
      destruct n as [target_owner target_loc]. intro owner.
      unfold concrete_array, array_payload. simpl.
      unfold counter_at. simpl. split; [lia|]. intro Heq.
      unfold order_at, remove_node. simpl.
      destruct (PositiveMap.E.eq_dec owner target_owner) as [->|Hneq].
      - rewrite TMap.gss. intros address Hin.
        exact (proj1 (in_remove Nat.eq_dec _ _ _ Hin)).
      - rewrite TMap.gso by congruence. intros address Hin. exact Hin.
    Qed.

    Definition G (actor : tid) : rg_relation :=
      fun w w' =>
        (forall observer, actor <> observer ->
          token_rely observer (SetPossState.Δ w) (SetPossState.Δ w')) /\
        (forall observer, actor <> observer ->
          pool_local_equiv observer
            (SetPossState.Δ w) (SetPossState.Δ w')) /\
        (forall observer loc lower, actor <> observer ->
          push_causal observer loc lower w ->
          push_causal observer loc lower w') /\
        (forall observer, actor <> observer ->
          array_local_state observer (SetPossState.σ w) =
          array_local_state observer (SetPossState.σ w')) /\
        (forall observer, actor <> observer ->
          TMap.find observer
            (ts_pending (concrete_timestamp (SetPossState.σ w))) =
          TMap.find observer
            (ts_pending (concrete_timestamp (SetPossState.σ w')))) /\
        (forall observer, actor <> observer ->
          candidate_views_preserved observer
            (SetPossState.Δ w) (SetPossState.Δ w')) /\
        (forall observer, actor <> observer ->
          row_snapshot_views_preserved observer
            (SetPossState.Δ w) (SetPossState.Δ w')) /\
        array_evolves (SetPossState.σ w) (SetPossState.σ w') /\
        ts_clock (concrete_timestamp (SetPossState.σ w)) <=
          ts_clock (concrete_timestamp (SetPossState.σ w')) /\
        (forall observer, actor <> observer ->
          candidate_row_views_preserved observer
            (SetPossState.Δ w) (SetPossState.Δ w')) /\
        (forall observer, actor <> observer ->
          node_cuts_preserved observer
            (SetPossState.σ w) (SetPossState.σ w')
            (SetPossState.Δ w) (SetPossState.Δ w')) /\
        garbage_evolves (SetPossState.σ w) (SetPossState.σ w') /\
        intervals_evolve (SetPossState.σ w) (SetPossState.σ w') /\
        (forall observer, actor <> observer ->
          session_equiv observer
            (SetPossState.Δ w) (SetPossState.Δ w')).

    Definition R (observer : tid) : rg_relation :=
      fun w w' =>
        token_rely observer (SetPossState.Δ w) (SetPossState.Δ w') /\
        pool_local_equiv observer
          (SetPossState.Δ w) (SetPossState.Δ w') /\
        (forall loc lower,
          push_causal observer loc lower w ->
          push_causal observer loc lower w') /\
        array_local_state observer (SetPossState.σ w) =
          array_local_state observer (SetPossState.σ w') /\
        TMap.find observer
          (ts_pending (concrete_timestamp (SetPossState.σ w))) =
        TMap.find observer
          (ts_pending (concrete_timestamp (SetPossState.σ w'))) /\
        candidate_views_preserved observer
          (SetPossState.Δ w) (SetPossState.Δ w') /\
        row_snapshot_views_preserved observer
          (SetPossState.Δ w) (SetPossState.Δ w') /\
        array_evolves (SetPossState.σ w) (SetPossState.σ w') /\
        ts_clock (concrete_timestamp (SetPossState.σ w)) <=
          ts_clock (concrete_timestamp (SetPossState.σ w')) /\
        candidate_row_views_preserved observer
          (SetPossState.Δ w) (SetPossState.Δ w') /\
        node_cuts_preserved observer
          (SetPossState.σ w) (SetPossState.σ w')
          (SetPossState.Δ w) (SetPossState.Δ w') /\
        garbage_evolves (SetPossState.σ w) (SetPossState.σ w') /\
        intervals_evolve (SetPossState.σ w) (SetPossState.σ w') /\
        session_equiv observer (SetPossState.Δ w) (SetPossState.Δ w').

    Definition Active (actor : tid) (op : Sig.op (li_sig F)) : assertion :=
      I //\\ actor ↦∀◦(op).

    Definition Completed (actor : tid) (op : Sig.op (li_sig F))
        (ret : Sig.ar op) : assertion :=
      I //\\ actor ↦∀•(op, ret).

    Lemma token_equiv_ALin observer Delta Delta' ls :
      token_equiv observer Delta Delta' ->
      (forall rho pi, Delta rho pi -> TMap.find observer pi = Some ls) ->
      forall rho pi, Delta' rho pi -> TMap.find observer pi = Some ls.
    Proof.
      intros Hequiv Hall rho pi Hposs.
      pose proof (proj2 (Hequiv (TMap.find observer pi))) as Hback.
      destruct (Hback (ex_intro _ rho (ex_intro _ pi
        (conj Hposs eq_refl)))) as (rho0 & pi0 & Hposs0 & Hfind).
      rewrite <- Hfind. now apply Hall with rho0.
    Qed.

    Lemma token_rely_ALin_non_getTop_inv observer Delta Delta' ls :
      token_rely observer Delta Delta' ->
      (forall start, ls <> ls_inv (lpool_getTop start)) ->
      (forall rho pi, Delta rho pi ->
        TMap.find observer pi = Some ls) ->
      forall rho pi, Delta' rho pi ->
        TMap.find observer pi = Some ls.
    Proof.
      intros [Hkeep Hnew] Hneq Hall rho pi Hposs.
      destruct (Hnew (TMap.find observer pi)) as
        [Hold| (start & Htoken & Hinv) ].
      - exists rho, pi. split; [exact Hposs|reflexivity].
      - destruct Hold as (rho0 & pi0 & Hposs0 & Hfind).
        rewrite <- Hfind. now apply Hall with rho0.
      - destruct Hinv as (rho0 & pi0 & Hposs0 & Hfind).
        specialize (Hall _ _ Hposs0). rewrite Hfind in Hall.
        injection Hall as Heq. exfalso. apply (Hneq start). symmetry.
        exact Heq.
    Qed.

    Lemma token_equiv_all observer Delta Delta' token :
      token_equiv observer Delta Delta' ->
      (forall rho pi, Delta rho pi -> TMap.find observer pi = token) <->
      (forall rho pi, Delta' rho pi -> TMap.find observer pi = token).
    Proof.
      intro Hequiv. split.
      - intros Hall rho pi Hposs.
        pose proof (proj2 (Hequiv (TMap.find observer pi))) as Hback.
        destruct (Hback (ex_intro _ rho (ex_intro _ pi
          (conj Hposs eq_refl)))) as (rho0 & pi0 & Hposs0 & Hfind).
        rewrite <- Hfind. now apply Hall with rho0.
      - intros Hall rho pi Hposs.
        pose proof (proj1 (Hequiv (TMap.find observer pi))) as Hforward.
        destruct (Hforward (ex_intro _ rho (ex_intro _ pi
          (conj Hposs eq_refl)))) as (rho0 & pi0 & Hposs0 & Hfind).
        rewrite <- Hfind. now apply Hall with rho0.
    Qed.

    Lemma token_rely_all_none observer Delta Delta' :
      token_rely observer Delta Delta' ->
      (forall rho pi, Delta rho pi -> TMap.find observer pi = None) <->
      (forall rho pi, Delta' rho pi -> TMap.find observer pi = None).
    Proof.
      intros [Hkeep Hnew]. split.
      - intros Hall rho pi Hposs.
        destruct (Hnew (TMap.find observer pi)) as
          [Hold| (start & Htoken & Hinv) ].
        + exists rho, pi. split; [exact Hposs|reflexivity].
        + destruct Hold as (rho0 & pi0 & Hposs0 & Hfind).
          rewrite <- Hfind. now apply Hall with rho0.
        + destruct Hinv as (rho0 & pi0 & Hposs0 & Hfind).
          specialize (Hall _ _ Hposs0). congruence.
      - intros Hall rho pi Hposs.
        specialize (Hkeep (TMap.find observer pi)).
        assert (Hview : token_view observer Delta
          (TMap.find observer pi)).
        { exists rho, pi. auto. }
        destruct (Hkeep Hview) as (rho' & pi' & Hposs' & Hfind).
        rewrite <- Hfind. now apply Hall with rho'.
    Qed.

    Lemma active_entails_I actor op :
      ⊨ Active actor op ==>> I.
    Proof. firstorder. Qed.

    Lemma completed_entails_I actor op ret :
      ⊨ Completed actor op ret ==>> I.
    Proof. firstorder. Qed.

    Lemma active_stable actor op :
      (forall start, ls_inv op <> ls_inv (lpool_getTop start)) ->
      AssertionsSet.A.Stable (R actor) I (Active actor op).
    Proof.
      intro Hnot.
      unfold AssertionsSet.A.Stable, AssertionsSet.A.ComposeA,
        Active, R. intros w [[pre [[HI Hlin] Hequiv]] HI'].
      destruct Hequiv as
        [Hequiv [Hlocal [Hcausal [Harray_local [Hpending
          [Hcandidate [Hrow [Hevolve Hclock]]]]]]]].
      split; [exact HI'|].
      unfold ALin in *.
      eapply token_rely_ALin_non_getTop_inv; eauto.
    Qed.

    Lemma completed_stable actor op ret :
      AssertionsSet.A.Stable (R actor) I (Completed actor op ret).
    Proof.
      unfold AssertionsSet.A.Stable, AssertionsSet.A.ComposeA,
        Completed, R. intros w [[pre [[HI Hlin] Hequiv]] HI'].
      destruct Hequiv as
        [Hequiv [Hlocal [Hcausal [Harray_local [Hpending
          [Hcandidate [Hrow [Hevolve Hclock]]]]]]]].
      split; [exact HI'|].
      unfold ALin in *.
      eapply token_rely_ALin_non_getTop_inv; eauto; intros ?; discriminate.
    Qed.

    Lemma GINV_token_equiv actor observer :
      actor <> observer ->
      (AssertionsSet.GINV actor ⊆ R observer)%RGRelation.
    Proof.
      intros Hneq w w' [op [Hsigma [Hnone Heq]]]. split.
      - apply token_equiv_rely. intro token. split.
        + intros (rho & pi & Hposs & Hfind).
          exists rho, (TMap.add actor (ls_inv op) pi). split.
          * apply (proj2 (Heq _ _)). constructor. exact Hposs.
          * rewrite TMap.gso by congruence. exact Hfind.
        + intros (rho' & pi' & Hposs' & Hfind).
          apply (proj1 (Heq _ _)) in Hposs'.
          destruct (@ac_inv_find_neq _ (li_lts F) (SetPossState.Δ w)
            actor op rho' pi' observer Hposs' (not_eq_sym Hneq))
            as (pi0 & Hsource & Hsame).
          exists rho', pi0. split; [exact Hsource|]. congruence.
      - split.
        + split.
          * intros local (rho & pi & Hposs & Hlocal).
            exists rho, (TMap.add actor (ls_inv op) pi). split.
            -- apply (proj2 (Heq _ _)). constructor. exact Hposs.
            -- exact Hlocal.
          * intros local' (rho & pi & Hposs & Hlocal).
            apply (proj1 (Heq _ _)) in Hposs.
            destruct (@ac_inv_find_neq _ (li_lts F) (SetPossState.Δ w)
              actor op rho pi observer Hposs (not_eq_sym Hneq))
              as (pi0 & Hsource & Hsame).
            exists local'. split.
            -- exists rho, pi0. split; assumption.
            -- reflexivity.
        + split.
          * intros loc lower Hcausal rho pi Hposs.
            apply (proj1 (Heq _ _)) in Hposs.
            destruct (@ac_inv_find_neq _ (li_lts F) (SetPossState.Δ w)
              actor op rho pi observer Hposs (not_eq_sym Hneq))
              as (pi0 & Hsource & Hsame).
            destruct (Hcausal _ _ Hsource) as
              (p & -> & Hpending_pool & Hbefore).
            exists p. repeat split; auto.
            rewrite <- Hsigma. exact Hbefore.
          * split.
            -- rewrite Hsigma. reflexivity.
            -- split.
               ++ rewrite Hsigma. reflexivity.
               ++ split.
                  ** intros done candidate Hview.
                     unfold candidate_view in *.
                     destruct Hview as
                       (p & pi & N & Hposs & Htoken & Hsnapshot & Hvalue &
                        Hdone & Hwitness & Hsafe).
                     exists p, (TMap.add actor (ls_inv op) pi), N.
                     split.
                     --- apply (proj2 (Heq _ _)). constructor. exact Hposs.
                     --- split.
                         +++ rewrite TMap.gso by congruence. exact Htoken.
                         +++ split; [exact Hsnapshot|]. split; [exact Hvalue|].
                             repeat split; assumption.
                  ** split.
                     --- intros owner saved Hview.
                         unfold row_snapshot_view in *.
                         destruct Hview as
                           (p & pi & N & Hposs & Htoken & Hsnapshot &
                             Hsaved & Hlive & Horder).
                         exists p, (TMap.add actor (ls_inv op) pi), N.
                         repeat split; try assumption.
                         +++ apply (proj2 (Heq _ _)). constructor. exact Hposs.
                         +++ rewrite TMap.gso by congruence. exact Htoken.
                     --- split.
                         +++ apply array_evolves_same_array. now rewrite Hsigma.
                         +++ split; [rewrite Hsigma; lia|].
                             split.
                             *** intros done candidate owner saved Hview.
                             unfold candidate_row_view in *.
                             destruct Hview as
                               (p & pi & N & Hposs & Htoken & Hsnapshot &
                                 Hvalue & Hdone & Hstatus & Hcovered & Horder &
                                 Hsafe).
                             exists p, (TMap.add actor (ls_inv op) pi), N.
                             repeat split; try assumption.
                             ++++ apply (proj2 (Heq _ _)). constructor.
                                 exact Hposs.
                             ++++ rewrite TMap.gso by congruence. exact Htoken.
                             *** split.
                                 ++++ intros progress start0 Hinside Hfallback Hsession_all Hcuts n
                                   value Hlive Hvalue Hnotignored.
                                 rewrite <- Hsigma in Hlive, Hvalue.
                                 destruct (Hcuts n value Hlive Hvalue Hnotignored)
                                   as (p & pi & N & Hposs & Htoken & Hsnapshot &
                                     Hnode_value & Hmember & Hcut).
                                 exists p, (TMap.add actor (ls_inv op) pi), N.
                                 repeat split; try assumption.
                                 +++++ apply (proj2 (Heq _ _)). constructor.
                                      exact Hposs.
                                 +++++ rewrite TMap.gso by congruence.
                                      exact Htoken.
                                 ++++ split.
                                      ***** unfold garbage_evolves.
                                            now rewrite Hsigma.
                                      ***** split.
                                            ------ apply intervals_evolve_same_array.
                                                   now rewrite Hsigma.
                                            ------ apply session_equiv_of_covers.
                                                   { intros rho pi Hposs.
                                                     exists rho,
                                                       (TMap.add actor (ls_inv op) pi).
                                                     split; [|reflexivity].
                                                     apply (proj2 (Heq _ _)).
                                                     constructor. exact Hposs. }
                                                   { intros rho pi Hposs.
                                                     apply (proj1 (Heq _ _)) in Hposs.
                                                     destruct (@ac_inv_find_neq _
                                                       (li_lts F) (SetPossState.Δ w)
                                                       actor op rho pi observer Hposs
                                                       (not_eq_sym Hneq))
                                                       as (pi0 & Hsource & Hsame).
                                                     exists rho, pi0.
                                                     split; [exact Hsource|].
                                                     reflexivity. }
    Qed.

    Lemma GRET_token_equiv actor observer :
      actor <> observer ->
      (AssertionsSet.GRET actor ⊆ R observer)%RGRelation.
    Proof.
      intros Hneq w w' [op [ret [Hsigma [Hlin Heq]]]]. split.
      - apply token_equiv_rely. intro token. split.
        + intros (rho & pi & Hposs & Hfind).
          exists rho, (TMap.remove actor pi). split.
          * apply (proj2 (Heq _ _)). constructor. exact Hposs.
          * rewrite TMap.gro by congruence. exact Hfind.
        + intros (rho' & pi' & Hposs' & Hfind).
          apply (proj1 (Heq _ _)) in Hposs'.
          destruct (@ac_res_find_neq _ (li_lts F) (SetPossState.Δ w)
            actor rho' pi' observer Hposs' (not_eq_sym Hneq))
            as (pi0 & Hsource & Hsame).
          exists rho', pi0. split; [exact Hsource|]. congruence.
      - split.
        + split.
          * intros local (rho & pi & Hposs & Hlocal).
            exists rho, (TMap.remove actor pi). split.
            -- apply (proj2 (Heq _ _)). constructor. exact Hposs.
            -- exact Hlocal.
          * intros local' (rho & pi & Hposs & Hlocal).
            apply (proj1 (Heq _ _)) in Hposs.
            destruct (@ac_res_find_neq _ (li_lts F) (SetPossState.Δ w)
              actor rho pi observer Hposs (not_eq_sym Hneq))
              as (pi0 & Hsource & Hsame).
            exists local'. split.
            -- exists rho, pi0. split; assumption.
            -- reflexivity.
        + split.
          * intros loc lower Hcausal rho pi Hposs.
            apply (proj1 (Heq _ _)) in Hposs.
            destruct (@ac_res_find_neq _ (li_lts F) (SetPossState.Δ w)
              actor rho pi observer Hposs (not_eq_sym Hneq))
              as (pi0 & Hsource & Hsame).
            destruct (Hcausal _ _ Hsource) as
              (p & -> & Hpending_pool & Hbefore).
            exists p. repeat split; auto.
            rewrite <- Hsigma. exact Hbefore.
          * split.
            -- rewrite Hsigma. reflexivity.
            -- split.
               ++ rewrite Hsigma. reflexivity.
               ++ split.
                  ** intros done candidate Hview.
                     unfold candidate_view in *.
                     destruct Hview as
                       (p & pi & N & Hposs & Htoken & Hsnapshot & Hvalue &
                        Hdone & Hwitness & Hsafe).
                     exists p, (TMap.remove actor pi), N. split.
                     --- apply (proj2 (Heq _ _)). constructor. exact Hposs.
                     --- split.
                         +++ rewrite TMap.gro by congruence. exact Htoken.
                         +++ split; [exact Hsnapshot|]. split; [exact Hvalue|].
                             repeat split; assumption.
                  ** split.
                     --- intros owner saved Hview.
                         unfold row_snapshot_view in *.
                         destruct Hview as
                           (p & pi & N & Hposs & Htoken & Hsnapshot &
                             Hsaved & Hlive & Horder).
                         exists p, (TMap.remove actor pi), N.
                         repeat split; try assumption.
                         +++ apply (proj2 (Heq _ _)). constructor. exact Hposs.
                         +++ rewrite TMap.gro by congruence. exact Htoken.
                     --- split.
                         +++ apply array_evolves_same_array. now rewrite Hsigma.
                         +++ split; [rewrite Hsigma; lia|].
                             split.
                             *** intros done candidate owner saved Hview.
                             unfold candidate_row_view in *.
                             destruct Hview as
                               (p & pi & N & Hposs & Htoken & Hsnapshot &
                                 Hvalue & Hdone & Hstatus & Hcovered & Horder &
                                 Hsafe).
                             exists p, (TMap.remove actor pi), N.
                             repeat split; try assumption.
                             ++++ apply (proj2 (Heq _ _)). constructor.
                                 exact Hposs.
                             ++++ rewrite TMap.gro by congruence. exact Htoken.
                             *** split.
                                 ++++ intros progress start0 Hinside Hfallback Hsession_all Hcuts n
                                   value Hlive Hvalue Hnotignored.
                                 rewrite <- Hsigma in Hlive, Hvalue.
                                 destruct (Hcuts n value Hlive Hvalue Hnotignored)
                                   as (p & pi & N & Hposs & Htoken & Hsnapshot &
                                     Hnode_value & Hmember & Hcut).
                                 exists p, (TMap.remove actor pi), N.
                                 repeat split; try assumption.
                                 +++++ apply (proj2 (Heq _ _)). constructor.
                                      exact Hposs.
                                 +++++ rewrite TMap.gro by congruence.
                                      exact Htoken.
                                 ++++ split.
                                      ***** unfold garbage_evolves.
                                            now rewrite Hsigma.
                                      ***** split.
                                            ------ apply intervals_evolve_same_array.
                                                   now rewrite Hsigma.
                                            ------ apply session_equiv_of_covers.
                                                   { intros rho pi Hposs.
                                                     exists rho, (TMap.remove actor pi).
                                                     split; [|reflexivity].
                                                     apply (proj2 (Heq _ _)).
                                                     constructor. exact Hposs. }
                                                   { intros rho pi Hposs.
                                                     apply (proj1 (Heq _ _)) in Hposs.
                                                     destruct (@ac_res_find_neq _
                                                       (li_lts F) (SetPossState.Δ w)
                                                       actor rho pi observer Hposs
                                                       (not_eq_sym Hneq))
                                                       as (pi0 & Hsource & Hsame).
                                                     exists rho, pi0.
                                                     split; [exact Hsource|].
                                                     reflexivity. }
    Qed.

    Lemma valid_rg observer :
      RGISimulationSet.RGISimulation.ValidRGI
        (R observer) (G observer) I observer.
    Proof.
      constructor. intros w w' HR HI'.
      apply token_rely_all_none. exact (proj1 HR).
    Qed.

    Lemma parallel_compatible actor observer :
      actor <> observer -> forall w w',
      (G actor w w' \/
       (AssertionsSet.GINV actor w w' \/
        AssertionsSet.GRET actor w w') \/
       AssertionsSet.A.GId w w') /\ I w ->
      R observer w w'.
    Proof.
      intros Hneq w w' [Hstep HI]. destruct Hstep as [HG | [[Hinv|Hret]|Hid]].
      - destruct HG as
          [HGtoken [HGlocal [HGcausal [HGarray [HGpending
            [HGcandidate [HGrow [HGevolve [HGclock
              [HGcandidate_row [HGcuts [HGgarbage
                [HGintervals HGsession]]]]]]]]]]]]].
        split; [exact (HGtoken observer Hneq)|].
        split; [exact (HGlocal observer Hneq)|].
        split.
        + intros loc lower Hcausal. eapply HGcausal; eauto.
        + split; [exact (HGarray observer Hneq)|].
          split; [exact (HGpending observer Hneq)|].
          split; [exact (HGcandidate observer Hneq)|].
          split; [exact (HGrow observer Hneq)|].
          split; [exact HGevolve|].
          split; [exact HGclock|].
          split; [exact (HGcandidate_row observer Hneq)|].
          split; [exact (HGcuts observer Hneq)|].
          split; [exact HGgarbage|]. split; [exact HGintervals|].
          exact (HGsession observer Hneq).
      - eapply GINV_token_equiv; eauto.
      - eapply GRET_token_equiv; eauto.
      - unfold AssertionsSet.A.GId in Hid. subst.
        split; [apply token_rely_refl|]. split.
        + apply pool_local_equiv_refl.
        + split.
          * intros loc lower Hcausal. exact Hcausal.
          * split; [reflexivity|]. split; [reflexivity|].
            split; [apply candidate_views_preserved_refl|].
            split; [apply row_snapshot_views_preserved_refl|].
            split; [apply array_evolves_refl|].
            split; [lia|]. split.
            -- apply candidate_row_views_preserved_refl.
            -- split; [apply node_cuts_preserved_same_array; reflexivity|].
               split.
               ++ apply garbage_evolves_same_array. reflexivity.
               ++ split.
                  ** apply intervals_evolve_same_array. reflexivity.
                  ** apply session_equiv_refl.
    Qed.

    Lemma timestamp_update_eq n ts timestamps :
      timestamp_update n ts timestamps n = Some ts.
    Proof.
      unfold timestamp_update. destruct (node_eq_dec n n); congruence.
    Qed.

    Lemma timestamp_update_neq n n' ts timestamps :
      n <> n' -> timestamp_update n ts timestamps n' = timestamps n'.
    Proof.
      intro Hneq. unfold timestamp_update.
      destruct (node_eq_dec n n'); congruence.
    Qed.

    Lemma vertex_value (a : @SPListArrayState A) (n : LPNodeId) :
      array_vertex a n -> exists v, as_values a n = Some v.
    Proof.
      unfold array_vertex. destruct (as_values a n); eauto; contradiction.
    Qed.

    Lemma pool_vertex_value (a : @SPListArrayState A)
        (p : @ListPoolState A) (n : LPNodeId) :
      pool_represents a p -> is_vertex p n ->
      exists v, lp_vertices p n = Some v.
    Proof.
      intros Hrep. unfold is_vertex. destruct (lp_vertices p n); eauto.
      contradiction.
    Qed.

    Lemma pool_fresh_of_array_fresh (a : @SPListArrayState A)
        (p : @ListPoolState A) (n : LPNodeId) :
      pool_represents a p -> array_fresh a n -> fresh_node p n.
    Proof.
      intros (Hvertices & Hedges & Hedgevertices & Hgarbage &
        Hpending & Hsnapshots & Hrows) [Hvalue Hgarbage0].
      split; [rewrite Hvertices; exact Hvalue|].
      rewrite Hgarbage. exact Hgarbage0.
    Qed.

    Lemma timestamp_defined_vertex (a : @SPListArrayState A) (n : LPNodeId) :
      timestamp_defined a -> array_vertex a n ->
      exists ts, as_timestamps a n = Some ts /\ timestamp_wf ts.
    Proof.
      intros [Hdefined _] Hvertex.
      destruct (vertex_value _ _ Hvertex) as [v Hvalue]. eauto.
    Qed.

    Lemma timestamp_defined_timestamp (a : @SPListArrayState A)
        (n : LPNodeId) ts :
      timestamp_defined a -> as_timestamps a n = Some ts ->
      array_vertex a n.
    Proof.
      intros [_ [Hreverse _]] Htimestamp.
      destruct (Hreverse _ _ Htimestamp) as [v Hvalue].
      unfold array_vertex. congruence.
    Qed.

    Lemma timestamp_defined_wf (a : @SPListArrayState A)
        (n : LPNodeId) ts :
      timestamp_defined a -> as_timestamps a n = Some ts -> timestamp_wf ts.
    Proof.
      intros Hdefined Htimestamp.
      pose proof (timestamp_defined_timestamp a n ts Hdefined Htimestamp)
        as Hvertex.
      destruct (timestamp_defined_vertex a n Hdefined Hvertex) as
        (current & Hcurrent & Hwf).
      rewrite Htimestamp in Hcurrent. inversion Hcurrent; subst. exact Hwf.
    Qed.

    Lemma insert_preserves_old_timestamp (actor : tid) (loc : Addr) (v : A)
        (a : @SPListArrayState A) (n : LPNodeId) :
      n <> pair actor loc ->
      as_timestamps (insert_node actor loc v a) n = as_timestamps a n.
    Proof. intro Hneq. simpl. apply timestamp_update_neq. congruence. Qed.

    Lemma insert_preserves_old_value (actor : tid) (loc : Addr) (v : A)
        (a : @SPListArrayState A) (n : LPNodeId) :
      n <> pair actor loc ->
      as_values (insert_node actor loc v a) n = as_values a n.
    Proof. intro Hneq. simpl. apply node_update_neq. congruence. Qed.

    Lemma insert_preserves_garbage (actor : tid) (loc : Addr) (v : A)
        (a : @SPListArrayState A) (n : LPNodeId) :
      as_garbage (insert_node actor loc v a) n = as_garbage a n.
    Proof. reflexivity. Qed.

    Lemma insert_timestamp_top (actor : tid) (loc : Addr) (v : A)
        (a : @SPListArrayState A) :
      as_timestamps (insert_node actor loc v a) (pair actor loc) = Some TSTop.
    Proof. simpl. apply timestamp_update_eq. Qed.

    Lemma insert_value (actor : tid) (loc : Addr) (v : A)
        (a : @SPListArrayState A) :
      as_values (insert_node actor loc v a) (pair actor loc) = Some v.
    Proof. simpl. apply node_update_eq. Qed.

    Lemma timestamp_defined_insert (actor : tid) (loc : Addr) (v : A)
        (a : @SPListArrayState A) :
      timestamp_defined a -> array_fresh a (pair actor loc) ->
      timestamp_defined (insert_node actor loc v a).
    Proof.
      intros [Hforward [Hreverse Hgarbage]] [Hfresh _]. split.
      - intros n value Hvalue.
        destruct (node_eq_dec (pair actor loc) n) as [<-|Hneq].
        + exists TSTop. split; [apply insert_timestamp_top|simpl; trivial].
        + rewrite insert_preserves_old_value in Hvalue by congruence.
          destruct (Hforward _ _ Hvalue) as (ts & Hts & Hwf).
          exists ts. split; [rewrite insert_preserves_old_timestamp by congruence;
            exact Hts|exact Hwf].
      - split.
        + intros n ts Htimestamp.
          destruct (node_eq_dec (pair actor loc) n) as [<-|Hneq].
          * exists v. apply insert_value.
          * rewrite insert_preserves_old_timestamp in Htimestamp by congruence.
            destruct (Hreverse _ _ Htimestamp) as [value Hvalue].
            exists value. rewrite insert_preserves_old_value by congruence.
            exact Hvalue.
        + intros n Hgarbage'.
          destruct (node_eq_dec (pair actor loc) n) as [<-|Hneq].
          * unfold array_vertex. simpl. rewrite node_update_eq. discriminate.
          * specialize (Hgarbage n Hgarbage').
            unfold array_vertex in *. simpl.
            rewrite node_update_neq by exact Hneq. exact Hgarbage.
    Qed.

    Lemma stamped_before_clock_insert (actor : tid) (loc : Addr) (v : A)
        (a : @SPListArrayState A) (tss : TimestampState) :
      stamped_before_clock a tss ->
      stamped_before_clock (insert_node actor loc v a) tss.
    Proof.
      intros Hstamped n lower upper Htimestamp.
      destruct (node_eq_dec (pair actor loc) n) as [<-|Hneq].
      - rewrite insert_timestamp_top in Htimestamp. discriminate.
      - rewrite insert_preserves_old_timestamp in Htimestamp by congruence.
        eauto.
    Qed.

    Lemma interval_timestamps_preserved_insert
        (actor : tid) (loc : Addr) (v : A)
        (a : @SPListArrayState A) :
      timestamp_defined a -> array_fresh a (pair actor loc) ->
      forall n lower upper,
        as_timestamps a n = Some (TSInterval lower upper) ->
        as_timestamps (insert_node actor loc v a) n =
          Some (TSInterval lower upper).
    Proof.
      intros Hdefined [Hfresh_value _] n lower upper Htimestamp.
      destruct (node_eq_dec n (pair actor loc)) as [->|Hneq].
      - exfalso.
        pose proof (timestamp_defined_timestamp _ _ _ Hdefined Htimestamp)
          as Hvertex.
        unfold array_vertex in Hvertex. rewrite Hfresh_value in Hvertex.
        contradiction.
      - rewrite insert_preserves_old_timestamp by exact Hneq.
        exact Htimestamp.
    Qed.

    Lemma timestamp_domain_preserved_insert
        (actor : tid) (loc : Addr) (v : A)
        (a : @SPListArrayState A) :
      timestamp_defined a -> array_fresh a (pair actor loc) ->
      forall n ts,
        as_timestamps a n = Some ts ->
        exists ts', as_timestamps (insert_node actor loc v a) n = Some ts'.
    Proof.
      intros Hdefined [Hfresh_value _] n ts Htimestamp.
      destruct (node_eq_dec n (pair actor loc)) as [->|Hneq].
      - exfalso.
        pose proof (timestamp_defined_timestamp _ _ _ Hdefined Htimestamp)
          as Hvertex.
        unfold array_vertex in Hvertex. rewrite Hfresh_value in Hvertex.
        contradiction.
      - exists ts. rewrite insert_preserves_old_timestamp by exact Hneq.
        exact Htimestamp.
    Qed.

    Lemma pool_represents_start_push
        (a : @SPListArrayState A) (p : @ListPoolState A)
        (actor : tid) (loc : Addr) (v : A) :
      pool_represents a p ->
      timestamp_defined a ->
      array_structural_wf a ->
      TMap.find actor (lp_pending_pushes p) = None ->
      array_fresh a (pair actor loc) ->
      pool_represents (insert_node actor loc v a)
        (start_push actor loc v p).
    Proof.
      intros Hrep Hdefined Hstructural Hnone Hfresh.
      destruct Hrep as (Hvertices & Hedges & Hedgevertices & Hgarbage &
        Hpending & Hsnapshots & Hrows).
      assert (Hpoolfresh : fresh_node p (pair actor loc)).
      { split.
        - rewrite Hvertices. exact (proj1 Hfresh).
        - rewrite Hgarbage. exact (proj2 Hfresh). }
      unfold pool_represents.
      repeat match goal with |- _ /\ _ => split end.
      - intro n. simpl. unfold node_update.
        destruct (node_eq_dec (pair actor loc) n); auto using Hvertices.
      - intros newer older Hedge. simpl in Hedge.
        destruct Hedge as [Hold | [Hnew [Holder_vertex Hcompleted]]].
        + destruct (Hedges _ _ Hold) as
            (newer_ts & older_ts & Hnewer_ts & Holder_ts & Hlt).
          destruct (Hedgevertices _ _ Hold) as [Hnewer_vertex Holder_vertex].
          assert (Hnewer_neq : newer <> pair actor loc).
          { intro Heq. subst newer.
            destruct (pool_vertex_value a p _
              (conj Hvertices (conj Hedges (conj Hedgevertices
                (conj Hgarbage (conj Hpending (conj Hsnapshots Hrows))))))
              Hnewer_vertex) as [value Hvalue].
            rewrite Hvertices, (proj1 Hfresh) in Hvalue. discriminate. }
          assert (Holder_neq : older <> pair actor loc).
          { intro Heq. subst older.
            destruct (pool_vertex_value a p _
              (conj Hvertices (conj Hedges (conj Hedgevertices
                (conj Hgarbage (conj Hpending (conj Hsnapshots Hrows))))))
              Holder_vertex) as [value Hvalue].
            rewrite Hvertices, (proj1 Hfresh) in Hvalue. discriminate. }
          exists newer_ts, older_ts. repeat split; auto.
          * simpl. rewrite timestamp_update_neq by congruence. exact Hnewer_ts.
          * simpl. rewrite timestamp_update_neq by congruence. exact Holder_ts.
        + subst newer.
          assert (Holder_array : array_vertex a older).
          { unfold array_vertex, is_vertex in *.
            rewrite <- Hvertices. exact Holder_vertex. }
          destruct (timestamp_defined_vertex a older Hdefined Holder_array)
            as (older_ts & Holder_ts & Holder_wf).
          assert (Holder_not_top : older_ts <> TSTop).
          { intro Heq. subst older_ts. apply Hcompleted.
            apply (proj2 (Hpending older)). exact Holder_ts. }
          destruct older_ts as [|lower upper]; [contradiction|].
          assert (Holder_neq : older <> pair actor loc).
          { intro Heq. subst older.
            exact (Holder_vertex (proj1 Hpoolfresh)). }
          exists TSTop, (TSInterval lower upper). split.
          * simpl. apply timestamp_update_eq.
          * split.
            -- simpl. rewrite timestamp_update_neq by congruence.
               exact Holder_ts.
            -- simpl. trivial.
      - intros newer2 older2 Hedge. simpl in Hedge.
        destruct Hedge as [Hold | [-> [Holder Hcompleted]]].
        + destruct (Hedgevertices _ _ Hold) as [Hnewer_vertex Holder_vertex].
          split; unfold is_vertex in *; simpl.
          * rewrite node_update_neq.
            -- exact Hnewer_vertex.
            -- intro Heq. subst newer2.
               exact (Hnewer_vertex (proj1 Hpoolfresh)).
          * rewrite node_update_neq.
            -- exact Holder_vertex.
            -- intro Heq. subst older2.
               exact (Holder_vertex (proj1 Hpoolfresh)).
        + split.
          * unfold is_vertex. simpl. rewrite node_update_eq. discriminate.
          * unfold is_vertex in *. simpl.
            destruct (node_eq_dec (pair actor loc) older2).
            -- subst. exfalso. exact (Holder (proj1 Hpoolfresh)).
            -- rewrite node_update_neq by congruence. exact Holder.
      - intro n. simpl. apply Hgarbage.
      - destruct n as [owner address]. unfold is_pending. simpl.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Howner].
        + rewrite TMap.gss. destruct (Nat.eq_dec address loc) as [->|Hloc].
          * rewrite timestamp_update_eq. split; congruence.
          * rewrite timestamp_update_neq by (intro Hpair; inversion Hpair; auto).
            specialize (Hpending (pair actor address)).
            unfold is_pending in Hpending. cbn in Hpending.
            rewrite Hnone in Hpending. split; intro Hbad.
            -- inversion Hbad. congruence.
            -- apply (proj2 Hpending) in Hbad. discriminate.
        + rewrite TMap.gso by congruence.
          rewrite timestamp_update_neq by
            (intro Hpair; inversion Hpair; congruence).
          exact (Hpending (pair owner address)).
      - intros scan N Hfind n Hmember. simpl in Hfind.
        specialize (Hsnapshots _ _ Hfind _ Hmember).
        unfold array_vertex in *. simpl.
        destruct (node_eq_dec (pair actor loc) n) as [<-|Hneq].
        + rewrite node_update_eq. discriminate.
        + rewrite node_update_neq by congruence. exact Hsnapshots.
      - destruct Hrows as [Hedgeorder Htotal]. split.
        + intros owner newer older Hedge Hnewer_live Holder_live.
          simpl in Hedge.
          destruct Hedge as [Hold|[Hnew [Holder_old Hcompleted]]].
          * assert (Hnewer_neq : pair owner newer <> pair actor loc).
            { intro Heq. subst.
              destruct (Hedgevertices _ _ Hold) as [Hvertex _].
              unfold is_vertex in Hvertex.
              rewrite Heq in Hvertex. exact (Hvertex (proj1 Hpoolfresh)). }
            assert (Holder_neq : pair owner older <> pair actor loc).
            { intro Heq. subst.
              destruct (Hedgevertices _ _ Hold) as [_ Hvertex].
              unfold is_vertex in Hvertex.
              rewrite Heq in Hvertex. exact (Hvertex (proj1 Hpoolfresh)). }
            assert (Hnewer_old : is_live p (pair owner newer)).
            { destruct Hnewer_live as [Hvertex Hlive]. split; [|exact Hlive].
              unfold is_vertex in *. simpl in Hvertex.
              rewrite node_update_neq in Hvertex by congruence. exact Hvertex. }
            assert (Holder_old' : is_live p (pair owner older)).
            { destruct Holder_live as [Hvertex Hlive]. split; [|exact Hlive].
              unfold is_vertex in *. simpl in Hvertex.
              rewrite node_update_neq in Hvertex by congruence. exact Hvertex. }
            specialize (Hedgeorder owner newer older Hold
              Hnewer_old Holder_old').
            unfold order_at. simpl.
            destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
            -- rewrite TMap.gss. now apply list_before_cons.
            -- rewrite TMap.gso by congruence. exact Hedgeorder.
          * inversion Hnew; subst owner newer.
            unfold order_at. simpl. rewrite TMap.gss.
            apply list_before_head.
            -- intro Heq. subst older.
               exact (Holder_old (proj1 Hpoolfresh)).
            -- apply (proj1 Hstructural actor older).
               destruct Holder_live as [_ Hlive]. split.
               ++ unfold array_vertex, is_vertex in *.
                  rewrite <- Hvertices. exact Holder_old.
               ++ intro Hgarbage_a. apply Hlive.
                  apply (proj2 (Hgarbage _)). exact Hgarbage_a.
        + intros owner first second Hneq Hfirst Hsecond.
          destruct (Nat.eq_dec first loc) as [Hfirstloc|Hfirstloc];
          destruct (PositiveMap.E.eq_dec owner actor) as [Howner|Howner].
          * subst owner first. left. simpl. right. split; [reflexivity|].
            split.
            -- destruct Hsecond as [Hv _].
               unfold is_vertex in *. simpl in Hv.
               rewrite node_update_neq in Hv by
                 (intro Heq; inversion Heq; congruence). exact Hv.
            -- unfold is_pending. cbn. rewrite Hnone. discriminate.
          * subst first. assert (Hpair : pair actor loc <> pair owner loc)
                by (intro Heq; inversion Heq; congruence).
            assert (Hfirst_old : is_live p (pair owner loc)).
            { destruct Hfirst as [Hv Hg]. split; [|exact Hg].
              unfold is_vertex in *. simpl in Hv.
              rewrite node_update_neq in Hv by exact Hpair. exact Hv. }
            assert (Hsecond_pair : pair actor loc <> pair owner second)
                by (intro Heq; inversion Heq; congruence).
            assert (Hsecond_old : is_live p (pair owner second)).
            { destruct Hsecond as [Hv Hg]. split; [|exact Hg].
              unfold is_vertex in *. simpl in Hv.
              rewrite node_update_neq in Hv by exact Hsecond_pair. exact Hv. }
            destruct (Htotal owner loc second Hneq Hfirst_old Hsecond_old);
              [left|right]; simpl; auto.
          * subst owner.
            destruct (Nat.eq_dec second loc) as [->|Hsecondloc].
            -- right. simpl. right. split; [reflexivity|]. split.
               ++ destruct Hfirst as [Hv _].
                  unfold is_vertex in *. simpl in Hv.
                  rewrite node_update_neq in Hv by
                    (intro Heq; inversion Heq; congruence). exact Hv.
               ++ unfold is_pending. cbn. rewrite Hnone. discriminate.
            -- assert (Hfirst_old : is_live p (pair actor first)).
               { destruct Hfirst as [Hv Hg]. split; [|exact Hg].
                 unfold is_vertex in *. simpl in Hv.
                 rewrite node_update_neq in Hv by
                   (intro Heq; inversion Heq; congruence). exact Hv. }
               assert (Hsecond_old : is_live p (pair actor second)).
               { destruct Hsecond as [Hv Hg]. split; [|exact Hg].
                 unfold is_vertex in *. simpl in Hv.
                 rewrite node_update_neq in Hv by
                   (intro Heq; inversion Heq; congruence). exact Hv. }
               destruct (Htotal actor first second Hneq
                 Hfirst_old Hsecond_old); [left|right]; simpl; auto.
          * assert (Hfirst_pair : pair actor loc <> pair owner first)
                by (intro Heq; inversion Heq; congruence).
            assert (Hsecond_pair : pair actor loc <> pair owner second)
                by (intro Heq; inversion Heq; congruence).
            assert (Hfirst_old : is_live p (pair owner first)).
            { destruct Hfirst as [Hv Hg]. split; [|exact Hg].
              unfold is_vertex in *. simpl in Hv.
              rewrite node_update_neq in Hv by exact Hfirst_pair. exact Hv. }
            assert (Hsecond_old : is_live p (pair owner second)).
            { destruct Hsecond as [Hv Hg]. split; [|exact Hg].
              unfold is_vertex in *. simpl in Hv.
              rewrite node_update_neq in Hv by exact Hsecond_pair. exact Hv. }
            destruct (Htotal owner first second Hneq
              Hfirst_old Hsecond_old); [left|right]; simpl; auto.
    Qed.

    (** The causal fact used when a saved [TSTop] is later replaced by an
        interval.  It talks about the abstract outgoing edges, not about a
        candidate's current concrete timestamp, so it remains valid across
        the stale-observation execution identified in the plan. *)
    Lemma start_push_outgoing_before
        (a : @SPListArrayState A) (p : @ListPoolState A)
        (tss : TimestampState) (actor : tid) (loc : Addr) (v : A) :
      pool_represents a p -> timestamp_defined a ->
      stamped_before_clock a tss ->
      array_fresh a (pair actor loc) ->
      outgoing_before (insert_node actor loc v a)
        (start_push actor loc v p) (pair actor loc) (ts_clock tss).
    Proof.
      intros Hrep Hdefined Hstamped Hfresh older Hedge.
      destruct Hrep as (Hvertices & Hedges & Hedgevertices & Hgarbage &
        Hpending & Hsnapshots & Hrows).
      simpl in Hedge. destruct Hedge as [Hold | [_ [Holder_vertex Hcompleted]]].
      - destruct (Hedgevertices _ _ Hold) as [Hnewvertex _].
        unfold is_vertex in Hnewvertex.
        rewrite Hvertices, (proj1 Hfresh) in Hnewvertex. contradiction.
      - assert (Holder_array : array_vertex a older).
        { unfold array_vertex, is_vertex in *.
          rewrite <- Hvertices. exact Holder_vertex. }
        destruct (timestamp_defined_vertex a older Hdefined Holder_array)
          as (old_ts & Hold_ts & Hwf).
        assert (Hnot_top : old_ts <> TSTop).
        { intro Heq. subst old_ts. apply Hcompleted.
          apply (proj2 (Hpending older)). exact Hold_ts. }
        destruct old_ts as [|old_lower old_upper]; [contradiction|].
        exists old_lower, old_upper. split.
        + rewrite insert_preserves_old_timestamp by
            (intro Heq; subst; unfold array_vertex in Holder_array;
              rewrite (proj1 Hfresh) in Holder_array; contradiction).
          exact Hold_ts.
        + specialize (Hstamped older old_lower old_upper Hold_ts). lia.
    Qed.

    Lemma pending_push_outgoing_before
        (a : @SPListArrayState A) (p : @ListPoolState A)
        (tss : TimestampState) actor loc :
      pool_represents a p -> stamped_before_clock a tss ->
      TMap.find actor (lp_pending_pushes p) = Some loc ->
      outgoing_before a p (pair actor loc) (ts_clock tss).
    Proof.
      intros (Hvertices & Hedges & Hedgevertices & Hgarbage & Hpending &
        Hsnapshots & Hrows) Hstamped Hpending_actor older Hedge.
      destruct (Hedges _ _ Hedge) as
        (newer_ts & older_ts & Hnewer & Holder & Hlt).
      assert (Htop : as_timestamps a (pair actor loc) = Some TSTop).
      { apply (proj1 (Hpending (pair actor loc))).
        unfold is_pending. exact Hpending_actor. }
      rewrite Htop in Hnewer. inversion Hnewer; subst newer_ts.
      destruct older_ts as [|old_lower old_upper].
      - unfold timestamp_above in Hlt. contradiction.
      - exists old_lower, old_upper. split; [exact Holder|].
        specialize (Hstamped older old_lower old_upper Holder). lia.
    Qed.

    Lemma outgoing_before_stamped_edge
        (a : @SPListArrayState A) (p : @ListPoolState A)
        (actor : tid) (loc : Addr) lower upper :
      as_timestamps a (pair actor loc) = Some TSTop ->
      outgoing_before a p (pair actor loc) lower ->
      forall older, lp_edges p (pair actor loc) older ->
        array_edge
          (set_node_timestamp actor loc (TSInterval lower upper) a)
          (pair actor loc) older.
    Proof.
      intros Htop Hbefore older Hedge.
      destruct (Hbefore _ Hedge) as
        (old_lower & old_upper & Hold & Hlt).
      assert (Hneq : older <> pair actor loc).
      { intro Heq. subst older. rewrite Htop in Hold. discriminate. }
      exists (TSInterval lower upper), (TSInterval old_lower old_upper).
      unfold set_node_timestamp. simpl. rewrite Htop. split.
      - apply timestamp_update_eq.
      - split.
        + rewrite timestamp_update_neq by congruence. exact Hold.
        + exact Hlt.
    Qed.

    Lemma set_timestamp_at_top (a : @SPListArrayState A)
        (actor : tid) (loc : Addr) ts :
      as_timestamps a (pair actor loc) = Some TSTop ->
      as_timestamps (set_node_timestamp actor loc ts a)
        (pair actor loc) = Some ts.
    Proof.
      intro Htop. unfold set_node_timestamp. simpl. rewrite Htop.
      apply timestamp_update_eq.
    Qed.

    Lemma set_timestamp_other (a : @SPListArrayState A)
        (actor : tid) (loc : Addr) ts n :
      n <> pair actor loc ->
      as_timestamps (set_node_timestamp actor loc ts a) n =
      as_timestamps a n.
    Proof.
      intro Hneq. unfold set_node_timestamp. simpl.
      destruct (as_timestamps a (pair actor loc)) as [current|].
      - destruct current.
        + apply timestamp_update_neq. congruence.
        + reflexivity.
      - reflexivity.
    Qed.

    Lemma interval_timestamps_preserved_set_at_top
        (a : @SPListArrayState A) (actor : tid) (loc : Addr) ts :
      as_timestamps a (pair actor loc) = Some TSTop ->
      forall n lower upper,
        as_timestamps a n = Some (TSInterval lower upper) ->
        as_timestamps (set_node_timestamp actor loc ts a) n =
          Some (TSInterval lower upper).
    Proof.
      intros Htop n lower upper Hinterval.
      destruct (node_eq_dec n (pair actor loc)) as [->|Hneq].
      - rewrite Htop in Hinterval. discriminate.
      - rewrite set_timestamp_other by exact Hneq. exact Hinterval.
    Qed.

    Lemma timestamp_domain_preserved_set_at_top
        (a : @SPListArrayState A) (actor : tid) (loc : Addr) ts :
      as_timestamps a (pair actor loc) = Some TSTop ->
      forall n old,
        as_timestamps a n = Some old ->
        exists current,
          as_timestamps (set_node_timestamp actor loc ts a) n = Some current.
    Proof.
      intros Htop n old Htimestamp.
      destruct (node_eq_dec n (pair actor loc)) as [->|Hneq].
      - exists ts. now apply set_timestamp_at_top.
      - exists old. rewrite set_timestamp_other by exact Hneq.
        exact Htimestamp.
    Qed.

    Lemma timestamp_defined_set (a : @SPListArrayState A)
        (actor : tid) (loc : Addr) ts :
      timestamp_defined a -> timestamp_wf ts ->
      as_timestamps a (pair actor loc) = Some TSTop ->
      timestamp_defined (set_node_timestamp actor loc ts a).
    Proof.
      intros [Hforward [Hreverse Hgarbage]] Hwf Htop. split.
      - intros n v Hvalue. simpl in Hvalue.
        destruct (node_eq_dec (pair actor loc) n) as [<-|Hneq].
        + exists ts. split; [now apply set_timestamp_at_top|exact Hwf].
        + destruct (Hforward _ _ Hvalue) as (old & Hold & Holdwf).
          exists old. split; [rewrite set_timestamp_other by congruence;
            exact Hold|exact Holdwf].
      - split.
        + intros n current Htimestamp. simpl.
          destruct (node_eq_dec (pair actor loc) n) as [<-|Hneq].
          * destruct (Hreverse _ _ Htop) as [value Hvalue].
            exists value. exact Hvalue.
          * rewrite set_timestamp_other in Htimestamp by congruence.
            eapply Hreverse. exact Htimestamp.
        + exact Hgarbage.
    Qed.

    Lemma stamped_before_clock_set (a : @SPListArrayState A)
        (tss : TimestampState) (actor : tid) (loc : Addr) lower upper :
      stamped_before_clock a tss -> S upper <= ts_clock tss ->
      as_timestamps a (pair actor loc) = Some TSTop ->
      stamped_before_clock
        (set_node_timestamp actor loc (TSInterval lower upper) a) tss.
    Proof.
      intros Hstamped Hbound Htop n lower' upper' Htimestamp.
      destruct (node_eq_dec (pair actor loc) n) as [<-|Hneq].
      - rewrite set_timestamp_at_top in Htimestamp by exact Htop.
        inversion Htimestamp; subst. exact Hbound.
      - rewrite set_timestamp_other in Htimestamp by congruence.
        eauto.
    Qed.

    Lemma pending_node_has_no_incoming
        (a : @SPListArrayState A) (p : @ListPoolState A) n :
      pool_represents a p -> is_pending p n ->
      forall newer, ~ lp_edges p newer n.
    Proof.
      intros (Hvertices & Hedges & Hedgevertices & Hgarbage &
        Hpending & Hsnapshots & Hrows) Hpending_n newer Hedge.
      destruct (Hedges _ _ Hedge) as
        (newer_ts & node_ts & Hnewer & Hnode & Hlt).
      rewrite (proj1 (Hpending n) Hpending_n) in Hnode.
      inversion Hnode; subst. destruct newer_ts; contradiction.
    Qed.

    Lemma pool_represents_finish_push
        (a : @SPListArrayState A) (p : @ListPoolState A)
        (actor : tid) (loc : Addr) lower upper :
      pool_represents a p ->
      TMap.find actor (lp_pending_pushes p) = Some loc ->
      as_timestamps a (pair actor loc) = Some TSTop ->
      (forall older, lp_edges p (pair actor loc) older ->
        array_edge
          (set_node_timestamp actor loc (TSInterval lower upper) a)
          (pair actor loc) older) ->
      pool_represents
        (set_node_timestamp actor loc (TSInterval lower upper) a)
        (finish_push actor p).
    Proof.
      intros Hrep Hpending_actor Htop Houtgoing.
      destruct Hrep as (Hvertices & Hedges & Hedgevertices & Hgarbage &
        Hpending & Hsnapshots & Hrows).
      assert (Hnoincoming : forall newer,
        ~ lp_edges p newer (pair actor loc)).
      { eapply pending_node_has_no_incoming.
        - exact (conj Hvertices (conj Hedges (conj Hedgevertices
            (conj Hgarbage (conj Hpending (conj Hsnapshots Hrows)))))).
        - unfold is_pending. exact Hpending_actor. }
      unfold pool_represents.
      repeat match goal with |- _ /\ _ => split end.
      - exact Hvertices.
      - intros newer older Hedge. simpl in Hedge.
        destruct (node_eq_dec newer (pair actor loc)) as [->|Hnewer].
        + apply Houtgoing. exact Hedge.
        + assert (Holder : older <> pair actor loc).
          { intro Heq. subst. exact (Hnoincoming newer Hedge). }
          destruct (Hedges _ _ Hedge) as
            (newer_ts & older_ts & Hnewer_ts & Holder_ts & Hlt).
          exists newer_ts, older_ts. repeat split; auto.
          * rewrite set_timestamp_other by congruence. exact Hnewer_ts.
          * rewrite set_timestamp_other by congruence. exact Holder_ts.
      - exact Hedgevertices.
      - exact Hgarbage.
      - destruct n as [owner address].
        unfold is_pending, set_node_timestamp. simpl. rewrite Htop.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Howner].
        + rewrite TMap.grs.
          destruct (Nat.eq_dec address loc) as [->|Hloc].
          * rewrite timestamp_update_eq. split; intro Hbad.
            -- discriminate.
            -- inversion Hbad.
          * rewrite timestamp_update_neq by
              (intro Hpair; inversion Hpair; auto).
            specialize (Hpending (pair actor address)).
            unfold is_pending in Hpending. cbn in Hpending.
            rewrite Hpending_actor in Hpending. split; intro Hbad.
            -- discriminate.
            -- apply (proj2 Hpending) in Hbad. inversion Hbad. congruence.
        + rewrite TMap.gro by congruence.
          rewrite timestamp_update_neq by
            (intro Hpair; inversion Hpair; congruence).
          exact (Hpending (pair owner address)).
      - exact Hsnapshots.
      - exact Hrows.
    Qed.

    Lemma pool_represents_mark_garbage
        (a : @SPListArrayState A) (p : @ListPoolState A) n :
      pool_represents a p ->
      pool_represents (remove_node n a) (mark_garbage n p).
    Proof.
      destruct n as [target_owner target_loc].
      intros (Hvertices & Hedges & Hedgevertices & Hgarbage &
        Hpending & Hsnapshots & Hrows).
      unfold pool_represents. simpl.
      refine (conj Hvertices (conj Hedges (conj Hedgevertices
        (conj _ (conj Hpending (conj Hsnapshots _)))))).
      - intro node. unfold set_add. specialize (Hgarbage node). tauto.
      - destruct Hrows as [Hedgeorder Htotal]. split.
        + intros owner newer older Hedge Hnewer Holder.
          assert (Hnewer_old : is_live p (pair owner newer)).
          { destruct Hnewer as [Hv Hg]. split; [exact Hv|].
            intro Hgarbage0. apply Hg. unfold set_add. now right. }
          assert (Holder_old : is_live p (pair owner older)).
          { destruct Holder as [Hv Hg]. split; [exact Hv|].
            intro Hgarbage0. apply Hg. unfold set_add. now right. }
          specialize (Hedgeorder owner newer older Hedge
            Hnewer_old Holder_old).
          destruct (PositiveMap.E.eq_dec owner target_owner) as [->|Hneq].
          * unfold order_at, remove_node. simpl. rewrite TMap.gss.
            apply list_before_remove; [| |exact Hedgeorder].
            -- intro Heq. apply (proj2 Hnewer). unfold set_add. left.
               now subst newer.
            -- intro Heq. apply (proj2 Holder). unfold set_add. left.
               now subst older.
          * unfold order_at, remove_node. simpl.
            rewrite TMap.gso by congruence. exact Hedgeorder.
        + intros owner first second Hneq Hfirst Hsecond.
          apply Htotal; [exact Hneq| |].
          * destruct Hfirst as [Hv Hg]. split; [exact Hv|].
            intro Hgarbage0. apply Hg. unfold set_add. now right.
          * destruct Hsecond as [Hv Hg]. split; [exact Hv|].
            intro Hgarbage0. apply Hg. unfold set_add. now right.
    Qed.

    Lemma pool_represents_start_snapshot
        (a : @SPListArrayState A) (p : @ListPoolState A) actor :
      pool_represents a p ->
      pool_represents a (start_snapshot actor p).
    Proof.
      intros (Hvertices & Hedges & Hedgevertices & Hgarbage &
        Hpending & Hsnapshots & Hrows).
      unfold pool_represents. simpl.
      refine (conj Hvertices (conj Hedges (conj Hedgevertices
        (conj Hgarbage (conj Hpending (conj _ Hrows)))))).
      intros scan N Hfind n Hmember.
      destruct (PositiveMap.E.eq_dec scan actor) as [->|Hneq].
      - rewrite TMap.gss in Hfind. inversion Hfind; subst N.
        unfold is_vertex in Hmember. unfold array_vertex.
        rewrite <- Hvertices. exact Hmember.
      - rewrite TMap.gso in Hfind by exact Hneq. eauto.
    Qed.

    Lemma pool_represents_clear_snapshot
        (a : @SPListArrayState A) (p : @ListPoolState A) actor :
      pool_represents a p ->
      pool_represents a (clear_snapshot actor p).
    Proof.
      intros (Hvertices & Hedges & Hedgevertices & Hgarbage &
        Hpending & Hsnapshots & Hrows).
      unfold pool_represents. simpl.
      refine (conj Hvertices (conj Hedges (conj Hedgevertices
        (conj Hgarbage (conj Hpending (conj _ Hrows)))))).
      intros scan N Hfind n Hmember.
      destruct (PositiveMap.E.eq_dec scan actor) as [->|Hneq].
      - rewrite TMap.grs in Hfind. discriminate.
      - rewrite TMap.gro in Hfind by exact Hneq. eauto.
    Qed.

    Lemma array_structural_wf_insert
        (a : @SPListArrayState A) actor loc (v : A) :
      array_structural_wf a ->
      ThreadDomain.contains D actor ->
      array_fresh a (pair actor loc) ->
      array_structural_wf (insert_node actor loc v a).
    Proof.
      intros [Hlive [Hdomain Hnodup]] Hactor [Hfresh Hnotgarbage]. split.
      - intros owner address.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Howner].
        + destruct (Nat.eq_dec address loc) as [->|Haddress].
          * split.
            -- intro H. unfold order_at. simpl.
               rewrite TMap.gss. now left.
            -- intro H. split.
               ++ unfold array_vertex. simpl. rewrite node_update_eq.
                  discriminate.
               ++ simpl. exact Hnotgarbage.
          * assert (Hnode : pair actor loc <> pair actor address)
              by (intro Heq; inversion Heq; congruence).
            assert (Hold :
              array_live (insert_node actor loc v a) (pair actor address) <->
              array_live a (pair actor address)).
            { unfold array_live, array_vertex. simpl.
              rewrite node_update_neq by exact Hnode. tauto. }
            rewrite Hold, Hlive. unfold order_at. simpl.
            rewrite TMap.gss. simpl. assert (loc <> address) by congruence.
            tauto.
        + assert (Hnode : pair actor loc <> pair owner address)
            by (intro Heq; inversion Heq; congruence).
          assert (Hold :
            array_live (insert_node actor loc v a) (pair owner address) <->
            array_live a (pair owner address)).
          { unfold array_live, array_vertex. simpl.
            rewrite node_update_neq by exact Hnode. tauto. }
          rewrite Hold, Hlive. unfold order_at. simpl.
          rewrite TMap.gso by congruence. reflexivity.
      - split.
        + intros [owner address] Hvertex.
          destruct (node_eq_dec (pair actor loc) (pair owner address))
            as [Heq|Hneq].
          * inversion Heq; subst. exact Hactor.
          * apply Hdomain. unfold array_vertex in *. simpl in Hvertex.
            rewrite node_update_neq in Hvertex by exact Hneq. exact Hvertex.
        + intro owner. unfold order_at, insert_node. simpl.
          destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
          * rewrite TMap.gss. constructor; [|apply Hnodup].
            intro Hin.
            pose proof (proj1 (proj2 (Hlive actor loc) Hin)) as Hvertex.
            unfold array_vertex in Hvertex. rewrite Hfresh in Hvertex.
            contradiction.
          * rewrite TMap.gso by congruence. apply Hnodup.
    Qed.

    Lemma array_structural_wf_remove
        (a : @SPListArrayState A) (n : LPNodeId) :
      array_structural_wf a ->
      array_structural_wf (remove_node n a).
    Proof.
      destruct n as [target_owner target_loc].
      intros [Hlive [Hdomain Hnodup]].
      assert (Hremoved : forall owner address,
        array_live (remove_node (pair target_owner target_loc) a)
          (pair owner address) <->
        array_live a (pair owner address) /\
          pair owner address <> pair target_owner target_loc).
      { intros owner address. unfold array_live, array_vertex, remove_node.
        simpl. unfold set_add. tauto. }
      split.
      - intros owner address.
        destruct (PositiveMap.E.eq_dec owner target_owner)
          as [->|Howner].
        + rewrite Hremoved, Hlive. unfold order_at. simpl.
          rewrite TMap.gss.
          split.
          * intros [Hold Hneq]. apply in_in_remove; [|exact Hold].
            intro Heq. apply Hneq. now subst.
          * intro Hin. destruct (in_remove Nat.eq_dec _ _ _ Hin)
              as [Hold Hneqloc]. split; [exact Hold|].
            intro Heq. inversion Heq. congruence.
        + rewrite Hremoved, Hlive. unfold order_at. simpl.
          rewrite TMap.gso by congruence. split.
          * intros [Hin Hneq]. exact Hin.
          * intro Hin. split; [exact Hin|]. intro Heq.
            inversion Heq. congruence.
      - split.
        + intros node Hvertex. apply Hdomain. exact Hvertex.
        + intro owner. unfold order_at, remove_node. simpl.
          destruct (PositiveMap.E.eq_dec owner target_owner) as [->|Hneq].
          * rewrite TMap.gss. apply NoDup_remove_nat, Hnodup.
          * rewrite TMap.gso by congruence. apply Hnodup.
    Qed.

    Lemma concrete_wf_remove (a : @SPListArrayState A)
        (tss : TimestampState) n :
      concrete_wf (pair (ArrayReady a) tss) ->
      array_vertex a n ->
      concrete_wf (pair (ArrayReady (remove_node n a)) tss).
    Proof.
      unfold concrete_wf, concrete_array, concrete_timestamp, array_payload.
      simpl. intros (Hvalid & Hstamped & Hdefined & Hstructural) Hvertex.
      split; [exact Hvalid|]. split.
      - intros node lower upper Hfind. eauto.
      - split.
        + destruct Hdefined as [Hforward [Hreverse Hgarbage]]. split;
            [exact Hforward|]. split; [exact Hreverse|].
          intros node [Heq|Hgarbage']; [subst node; exact Hvertex|].
          now apply Hgarbage.
        + now apply array_structural_wf_remove.
    Qed.

    Lemma I_config_equiv sigma Delta Delta' :
      ac_equiv Delta Delta' ->
      I (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          sigma Delta) ->
      I (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          sigma Delta').
    Proof.
      intros Hequiv [Hwf [Hrep [Hrect Hcounter]]].
      split; [exact Hwf|]. split.
      - intros rho pi Hposs.
        exact (Hrep rho pi ((proj2 (Hequiv rho pi)) Hposs)).
      - split.
        + destruct Hrect as [Hshared Hsplice]. split.
          * intros p1 pi1 p2 pi2 H1 H2. eapply Hshared.
            -- exact ((proj2 (Hequiv (LPReady p1) pi1)) H1).
            -- exact ((proj2 (Hequiv (LPReady p2) pi2)) H2).
          * intros actor p1 pi1 p2 pi2 H1 H2.
            destruct (Hsplice actor p1 pi1 p2 pi2
              ((proj2 (Hequiv (LPReady p1) pi1)) H1)
              ((proj2 (Hequiv (LPReady p2) pi2)) H2)) as
              (p & pi & Hposs & Hmerge).
            exists p, pi. split; [|exact Hmerge].
            exact ((proj1 (Hequiv (LPReady p) pi)) Hposs).
        + intros actor saved Hpending.
          destruct (Hcounter actor saved Hpending) as
            (rho & pi & start & Hposs & Hfind).
          exists rho, pi, start. split; [|exact Hfind].
          exact ((proj1 (Hequiv rho pi)) Hposs).
    Qed.

    (** The session-token clauses of [pool_protocol] are closed under
        every token update that does not touch the [startPop]/[getTop]
        session tokens of the acting thread. *)
    Lemma pool_protocol_add_inv p pi actor op :
      pool_protocol p pi -> TMap.find actor pi = None ->
      pool_protocol p (TMap.add actor (ls_inv op) pi).
    Proof.
      intros (Hpush & Hsnapshot & Hpushback & Hstartpop & Hstartpopback &
        Hgettop) Hnone.
      unfold pool_protocol.
      repeat match goal with |- _ /\ _ => split end.
      - intros owner loc Hpending.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + destruct (Hpush _ _ Hpending) as [v Htoken]. congruence.
        + destruct (Hpush _ _ Hpending) as [v Htoken]. exists v.
          rewrite TMap.gso by exact Hneq. exact Htoken.
      - intros owner N Hsnapshot_find.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + destruct (Hsnapshot _ _ Hsnapshot_find) as [start Htoken].
          congruence.
        + rewrite TMap.gso by exact Hneq. eauto.
      - intros owner v Htoken.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite TMap.gss in Htoken. discriminate.
        + rewrite TMap.gso in Htoken by exact Hneq. eapply Hpushback; eauto.
      - intros owner N0 Hstarts Hts.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + specialize (Hstartpop _ _ Hstarts Hts). congruence.
        + rewrite TMap.gso by exact Hneq. eauto.
      - intros owner Htoken.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite TMap.gss in Htoken. discriminate.
        + rewrite TMap.gso in Htoken by exact Hneq. eauto.
      - intros owner start Htoken.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite TMap.gss in Htoken. discriminate.
        + rewrite TMap.gso in Htoken by exact Hneq. eauto.
    Qed.

    Lemma pool_protocol_remove_completed p pi actor op ret :
      pool_protocol p pi ->
      TMap.find actor pi = Some (ls_linr op ret) ->
      pool_protocol p (TMap.remove actor pi).
    Proof.
      intros (Hpush & Hsnapshot & Hpushback & Hstartpop & Hstartpopback &
        Hgettop) Hcompleted.
      unfold pool_protocol.
      repeat match goal with |- _ /\ _ => split end.
      - intros owner loc Hpending.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + destruct (Hpush _ _ Hpending) as [v Htoken].
          rewrite Hcompleted in Htoken. dependent destruction Htoken.
        + destruct (Hpush _ _ Hpending) as [v Htoken]. exists v.
          rewrite TMap.gro by exact Hneq. exact Htoken.
      - intros owner N Hsnapshot_find.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + destruct (Hsnapshot _ _ Hsnapshot_find) as [start Htoken].
          rewrite Hcompleted in Htoken. dependent destruction Htoken.
        + rewrite TMap.gro by exact Hneq. eauto.
      - intros owner v Htoken.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite TMap.grs in Htoken. discriminate.
        + rewrite TMap.gro in Htoken by exact Hneq. eapply Hpushback; eauto.
      - intros owner N0 Hstarts Hts.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + specialize (Hstartpop _ _ Hstarts Hts).
          rewrite Hcompleted in Hstartpop. dependent destruction Hstartpop.
        + rewrite TMap.gro by exact Hneq. eauto.
      - intros owner Htoken.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite TMap.grs in Htoken. discriminate.
        + rewrite TMap.gro in Htoken by exact Hneq. eauto.
      - intros owner start Htoken.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite TMap.grs in Htoken. discriminate.
        + rewrite TMap.gro in Htoken by exact Hneq. eauto.
    Qed.

    Lemma pool_protocol_start_push p pi actor loc v :
      pool_protocol p pi ->
      TMap.find actor pi = Some (ls_inv (lpool_push v)) ->
      TMap.find actor (lp_pending_pushes p) = None ->
      pool_protocol (start_push actor loc v p)
        (TMap.add actor (ls_lini (lpool_push v)) pi).
    Proof.
      intros (Hpush & Hsnapshot & Hpushback & Hstartpop & Hstartpopback &
        Hgettop) Hactive Hnone.
      unfold pool_protocol.
      repeat match goal with |- _ /\ _ => split end.
      - intros owner address Hfind. simpl in Hfind.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite TMap.gss in Hfind. inversion Hfind; subst address.
          exists v. apply TMap.gss.
        + rewrite TMap.gso in Hfind by exact Hneq.
          destruct (Hpush _ _ Hfind) as [value Htoken]. exists value.
          rewrite TMap.gso by exact Hneq. exact Htoken.
      - intros owner N Hfind. simpl in Hfind.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + destruct (Hsnapshot _ _ Hfind) as [start Htoken].
          rewrite Hactive in Htoken. discriminate.
        + rewrite TMap.gso by exact Hneq. eauto.
      - intros owner value Htoken. simpl.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + exists loc. apply TMap.gss.
        + rewrite TMap.gso in Htoken by exact Hneq.
          destruct (Hpushback _ _ Htoken) as [old_loc Hold].
          exists old_loc. rewrite TMap.gso by exact Hneq. exact Hold.
      - intros owner N0 Hstarts Hts. simpl in Hstarts, Hts.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + specialize (Hstartpop _ _ Hstarts Hts).
          rewrite Hactive in Hstartpop. discriminate.
        + rewrite TMap.gso by exact Hneq. eauto.
      - intros owner Htoken. simpl.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite TMap.gss in Htoken. discriminate.
        + rewrite TMap.gso in Htoken by exact Hneq. eauto.
      - intros owner start Htoken. simpl.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite TMap.gss in Htoken. discriminate.
        + rewrite TMap.gso in Htoken by exact Hneq. eauto.
    Qed.

    Lemma pool_protocol_start_snapshot p pi actor start :
      pool_protocol p pi ->
      TMap.find actor pi = Some (ls_inv (lpool_getTop start)) ->
      TMap.find actor (lp_pop_ts p) = Some start ->
      TMap.find actor (lp_snapshots p) = None ->
      pool_protocol (start_snapshot actor p)
        (TMap.add actor (ls_lini (lpool_getTop start)) pi).
    Proof.
      intros (Hpush & Hsnapshot & Hpushback & Hstartpop & Hstartpopback &
        Hgettop) Hlin Hsession Hnone.
      unfold pool_protocol.
      repeat match goal with |- _ /\ _ => split end.
      - intros owner loc Hpending. simpl in Hpending.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + destruct (Hpush _ _ Hpending) as [v Htoken]. congruence.
        + destruct (Hpush _ _ Hpending) as [v Htoken]. exists v.
          rewrite TMap.gso by exact Hneq. exact Htoken.
      - intros owner N Hfind. simpl in Hfind.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + exists start. rewrite TMap.gss. reflexivity.
        + rewrite TMap.gso by exact Hneq. eapply Hsnapshot.
          rewrite TMap.gso in Hfind by exact Hneq. exact Hfind.
      - intros owner v Htoken. simpl.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite TMap.gss in Htoken. discriminate.
        + rewrite TMap.gso in Htoken by exact Hneq. eauto.
      - intros owner N0 Hstarts Hts. simpl in Hstarts, Hts.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + specialize (Hstartpop _ _ Hstarts Hts). congruence.
        + rewrite TMap.gso by exact Hneq. eauto.
      - intros owner Htoken. simpl.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite TMap.gss in Htoken. discriminate.
        + rewrite TMap.gso in Htoken by exact Hneq. eauto.
      - intros owner start0 Htoken. simpl.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite TMap.gss in Htoken. inversion Htoken; subst start0.
          exact Hsession.
        + rewrite TMap.gso in Htoken by exact Hneq. eauto.
    Qed.

    Lemma pool_protocol_finish_push p pi actor v loc :
      pool_protocol p pi ->
      TMap.find actor pi = Some (ls_lini (lpool_push v)) ->
      TMap.find actor (lp_pending_pushes p) = Some loc ->
      pool_protocol (finish_push actor p)
        (TMap.add actor (ls_linr (lpool_push v) tt) pi).
    Proof.
      intros (Hpush & Hsnapshot & Hpushback & Hstartpop & Hstartpopback &
        Hgettop) Hactive Hpending_actor.
      unfold pool_protocol.
      repeat match goal with |- _ /\ _ => split end.
      - intros owner address Hfind. simpl in Hfind.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite TMap.grs in Hfind. discriminate.
        + rewrite TMap.gro in Hfind by exact Hneq.
          destruct (Hpush _ _ Hfind) as [value Htoken]. exists value.
          rewrite TMap.gso by exact Hneq. exact Htoken.
      - intros owner N Hfind. simpl in Hfind.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + destruct (Hsnapshot _ _ Hfind) as [start Htoken].
          rewrite Hactive in Htoken. discriminate.
        + rewrite TMap.gso by exact Hneq. eauto.
      - intros owner value Htoken. simpl.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite TMap.gss in Htoken. discriminate.
        + rewrite TMap.gso in Htoken by exact Hneq.
          destruct (Hpushback _ _ Htoken) as [old_loc Hold].
          exists old_loc. rewrite TMap.gro by exact Hneq. exact Hold.
      - intros owner N0 Hstarts Hts. simpl in Hstarts, Hts.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + specialize (Hstartpop _ _ Hstarts Hts).
          rewrite Hactive in Hstartpop. discriminate.
        + rewrite TMap.gso by exact Hneq. eauto.
      - intros owner Htoken. simpl.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite TMap.gss in Htoken. discriminate.
        + rewrite TMap.gso in Htoken by exact Hneq. eauto.
      - intros owner start Htoken. simpl.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite TMap.gss in Htoken. discriminate.
        + rewrite TMap.gso in Htoken by exact Hneq. eauto.
    Qed.

    Lemma pool_protocol_atomic p pi actor op ret :
      pool_protocol p pi -> TMap.find actor pi = Some (ls_inv op) ->
      pool_protocol p
        (TMap.add actor (ls_linr op ret)
          (TMap.add actor (ls_lini op) pi)).
    Proof.
      intros (Hpush & Hsnapshot & Hpushback & Hstartpop & Hstartpopback &
        Hgettop) Hactive.
      unfold pool_protocol.
      repeat match goal with |- _ /\ _ => split end.
      - intros owner address Hfind.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + destruct (Hpush _ _ Hfind) as [value Htoken].
          rewrite Hactive in Htoken. discriminate.
        + destruct (Hpush _ _ Hfind) as [value Htoken]. exists value.
          repeat rewrite TMap.gso by exact Hneq. exact Htoken.
      - intros owner N Hfind.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + destruct (Hsnapshot _ _ Hfind) as [start Htoken].
          rewrite Hactive in Htoken. discriminate.
        + repeat rewrite TMap.gso by exact Hneq. eauto.
      - intros owner value Htoken.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite TMap.gss in Htoken. discriminate.
        + repeat rewrite TMap.gso in Htoken by exact Hneq.
          eapply Hpushback; eauto.
      - intros owner N0 Hstarts Hts.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + specialize (Hstartpop _ _ Hstarts Hts).
          rewrite Hactive in Hstartpop. discriminate.
        + repeat rewrite TMap.gso by exact Hneq. eauto.
      - intros owner Htoken.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite TMap.gss in Htoken. discriminate.
        + repeat rewrite TMap.gso in Htoken by exact Hneq. eauto.
      - intros owner start Htoken.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite TMap.gss in Htoken. discriminate.
        + repeat rewrite TMap.gso in Htoken by exact Hneq. eauto.
    Qed.

    Lemma pool_protocol_start_pop_session p pi actor :
      pool_protocol p pi ->
      TMap.find actor pi = Some (ls_inv lpool_startPop) ->
      pool_protocol (start_pop_session actor p)
        (TMap.add actor (ls_lini lpool_startPop) pi).
    Proof.
      intros (Hpush & Hsnapshot & Hpushback & Hstartpop & Hstartpopback &
        Hgettop) Hactive.
      unfold pool_protocol.
      repeat match goal with |- _ /\ _ => split end.
      - intros owner address Hfind. simpl in Hfind.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + destruct (Hpush _ _ Hfind) as [value Htoken].
          rewrite Hactive in Htoken. discriminate.
        + destruct (Hpush _ _ Hfind) as [value Htoken]. exists value.
          rewrite TMap.gso by exact Hneq. exact Htoken.
      - intros owner N Hfind. simpl in Hfind.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + destruct (Hsnapshot _ _ Hfind) as [start Htoken].
          rewrite Hactive in Htoken. discriminate.
        + rewrite TMap.gso by exact Hneq. eauto.
      - intros owner value Htoken. simpl.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite TMap.gss in Htoken. discriminate.
        + rewrite TMap.gso in Htoken by exact Hneq. eauto.
      - intros owner N0 Hstarts Hts. simpl in Hstarts, Hts.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + apply TMap.gss.
        + rewrite TMap.gso in Hstarts by exact Hneq.
          rewrite TMap.gro in Hts by exact Hneq.
          rewrite TMap.gso by exact Hneq. eauto.
      - intros owner Htoken. simpl.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + split; [apply TMap.grs|]. exists (completed_set p). apply TMap.gss.
        + rewrite TMap.gso in Htoken by exact Hneq.
          rewrite TMap.gro, TMap.gso by exact Hneq. eauto.
      - intros owner start Htoken. simpl.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite TMap.gss in Htoken. discriminate.
        + rewrite TMap.gso in Htoken by exact Hneq.
          rewrite TMap.gro by exact Hneq. eauto.
    Qed.

    Lemma pool_protocol_finish_pop_session p pi actor ts :
      pool_protocol p pi ->
      TMap.find actor pi = Some (ls_lini lpool_startPop) ->
      pool_protocol (finish_pop_session actor ts p)
        (TMap.add actor (ls_linr lpool_startPop ts) pi).
    Proof.
      intros (Hpush & Hsnapshot & Hpushback & Hstartpop & Hstartpopback &
        Hgettop) Hactive.
      unfold pool_protocol.
      repeat match goal with |- _ /\ _ => split end.
      - intros owner address Hfind. simpl in Hfind.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + destruct (Hpush _ _ Hfind) as [value Htoken].
          rewrite Hactive in Htoken. discriminate.
        + destruct (Hpush _ _ Hfind) as [value Htoken]. exists value.
          rewrite TMap.gso by exact Hneq. exact Htoken.
      - intros owner N Hfind. simpl in Hfind.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + destruct (Hsnapshot _ _ Hfind) as [start Htoken].
          rewrite Hactive in Htoken. discriminate.
        + rewrite TMap.gso by exact Hneq. eauto.
      - intros owner value Htoken. simpl.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite TMap.gss in Htoken. discriminate.
        + rewrite TMap.gso in Htoken by exact Hneq. eauto.
      - intros owner N0 Hstarts Hts. simpl in Hstarts, Hts.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite TMap.gss in Hts. discriminate.
        + rewrite TMap.gso in Hts by exact Hneq.
          rewrite TMap.gso by exact Hneq. eauto.
      - intros owner Htoken. simpl.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite TMap.gss in Htoken. discriminate.
        + rewrite TMap.gso in Htoken by exact Hneq.
          rewrite TMap.gso by exact Hneq. eauto.
      - intros owner start Htoken. simpl.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite TMap.gss in Htoken. discriminate.
        + rewrite TMap.gso in Htoken by exact Hneq.
          rewrite TMap.gso by exact Hneq. eauto.
    Qed.

    (** Session invariant: closure under array and clock evolution. *)
    Lemma session_represents_evolve
        (a a' : @SPListArrayState A) (tss tss' : TimestampState)
        (p : @ListPoolState A) :
      (forall n lower upper,
        as_timestamps a n = Some (TSInterval lower upper) ->
        as_timestamps a' n = Some (TSInterval lower upper)) ->
      (forall actor N0,
        TMap.find actor (lp_pop_starts p) = Some N0 ->
        TMap.find actor (lp_pop_ts p) = None ->
        TMap.find actor (ts_pending tss') = TMap.find actor (ts_pending tss)) ->
      session_represents a tss p -> session_represents a' tss' p.
    Proof.
      intros Hintervals Hpending [Hstarts Hts]. split; [|exact Hts].
      intros actor N0 Hfind.
      destruct (Hstarts _ _ Hfind) as (c & Htoken & Hclock & Hmembers).
      exists c. split; [exact Htoken|]. split.
      - intro Hnone. rewrite (Hpending actor N0 Hfind Hnone). now apply Hclock.
      - intros n Hmember.
        destruct (Hmembers n Hmember) as (lower & upper & Hts_n & Hlt).
        exists lower, upper. split; [now apply Hintervals|exact Hlt].
    Qed.

    (** A thread holding a push or [getTop] token has no pending
        [startPop] session, so its clock entry is irrelevant. *)
    Lemma no_pending_session_of_token p pi actor ls :
      pool_protocol p pi ->
      TMap.find actor pi = Some ls ->
      ls <> ls_lini lpool_startPop ->
      forall N0, TMap.find actor (lp_pop_starts p) = Some N0 ->
        TMap.find actor (lp_pop_ts p) <> None.
    Proof.
      intros (_ & _ & _ & Hstartpop & _) Htoken Hneq N0 Hstarts Hts.
      specialize (Hstartpop _ _ Hstarts Hts). rewrite Htoken in Hstartpop.
      injection Hstartpop as Heq. apply Hneq. exact Heq.
    Qed.

    Lemma session_represents_start_pop_session
        (a : @SPListArrayState A) (tss : TimestampState)
        (p : @ListPoolState A) actor :
      timestamp_defined a -> stamped_before_clock a tss ->
      pool_represents a p ->
      session_represents a tss p ->
      session_represents a (start_newTS actor tss) (start_pop_session actor p).
    Proof.
      intros Hdefined Hstamped Hpool [Hstarts Hts]. split.
      - intros owner N0 Hfind. simpl in Hfind.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite TMap.gss in Hfind. inversion Hfind; subst N0.
          exists (ts_clock tss). split; [|split].
          * intros ts Hbad. simpl in Hbad. rewrite TMap.grs in Hbad.
            discriminate.
          * intros _. simpl. apply TMap.gss.
          * intros n [Hvertex Hcompleted].
            destruct (pool_vertex_value a p n Hpool Hvertex) as [v Hvalue].
            rewrite (proj1 Hpool) in Hvalue.
            destruct (proj1 Hdefined _ _ Hvalue) as (ts & Hts_n & Hwf).
            destruct ts as [|lower upper].
            -- exfalso. apply Hcompleted.
               apply (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 Hpool)))) n)).
               exact Hts_n.
            -- exists lower, upper. split; [exact Hts_n|].
               specialize (Hstamped _ _ _ Hts_n). lia.
        + rewrite TMap.gso in Hfind by exact Hneq.
          destruct (Hstarts _ _ Hfind) as (c & Htoken & Hclock & Hmembers).
          exists c. split; [|split].
          * intros ts Hts_find. simpl in Hts_find.
            rewrite TMap.gro in Hts_find by exact Hneq. now apply Htoken.
          * intros Hnone. simpl in Hnone. rewrite TMap.gro in Hnone by exact Hneq.
            simpl. rewrite TMap.gso by exact Hneq. now apply Hclock.
          * exact Hmembers.
      - intros owner ts Hfind. simpl in Hfind. simpl.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite TMap.grs in Hfind. discriminate.
        + rewrite TMap.gro in Hfind by exact Hneq.
          rewrite TMap.gso by exact Hneq. eauto.
    Qed.

    Lemma session_represents_finish_pop_session
        (a : @SPListArrayState A) (tss : TimestampState)
        (p : @ListPoolState A) actor lower upper :
      TMap.find actor (ts_pending tss) = Some lower ->
      lower <= upper ->
      TMap.find actor (lp_pop_ts p) = None ->
      (exists N0, TMap.find actor (lp_pop_starts p) = Some N0) ->
      session_represents a tss p ->
      session_represents a (finish_newTS actor upper tss)
        (finish_pop_session actor (TSInterval lower upper) p).
    Proof.
      intros Hpending Hle Hnone Hstarts_actor [Hstarts Hts]. split.
      - intros owner N0 Hfind. simpl in Hfind.
        destruct (Hstarts _ _ Hfind) as (c & Htoken & Hclock & Hmembers).
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + specialize (Hclock Hnone). rewrite Hpending in Hclock.
          inversion Hclock; subst c.
          exists lower. split; [|split].
          * intros ts Hts_find. simpl in Hts_find.
            rewrite TMap.gss in Hts_find. inversion Hts_find; subst ts.
            exists upper. split; [reflexivity|exact Hle].
          * intros Hbad. simpl in Hbad. rewrite TMap.gss in Hbad. discriminate.
          * exact Hmembers.
        + exists c. split; [|split].
          * intros ts Hts_find. simpl in Hts_find.
            rewrite TMap.gso in Hts_find by exact Hneq. now apply Htoken.
          * intros Hnone'. simpl in Hnone'.
            rewrite TMap.gso in Hnone' by exact Hneq.
            simpl. rewrite TMap.gro by exact Hneq. now apply Hclock.
          * exact Hmembers.
      - intros owner ts Hfind. simpl in Hfind. simpl.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + exact Hstarts_actor.
        + rewrite TMap.gso in Hfind by exact Hneq. eauto.
    Qed.

    (** Every completed array insertion exposes a paper-style [⊕] choice to
        each active scan: retain the old possibility, or place that scan's
        abstract invocation immediately after this push.  Folding over the
        finite thread domain materializes all independent combinations.
        The fork is parametrized by a predicate on the session token so
        that it also serves the scanning thread itself. *)
    Definition snapshot_tokens actor (start : TS)
        (pi : tmap (@LinState (li_sig F))) :=
      TMap.add actor (ls_lini (lpool_getTop start)) pi.

    Lemma snapshot_poss_step actor start p pi :
      TMap.find actor pi = Some (ls_inv (lpool_getTop start)) ->
      TMap.find actor (lp_pop_ts p) = Some start ->
      TMap.find actor (lp_snapshots p) = None ->
      @poss_steps (li_sig F) (li_lts F)
        (@PossOk (li_sig F) (li_lts F) (LPReady p) pi)
        (@PossOk (li_sig F) (li_lts F)
          (LPReady (start_snapshot actor p))
          (snapshot_tokens actor start pi)).
    Proof.
      intros Htoken Hsession Hnone. apply rt_step. eapply ps_inv.
      - eapply step_getTop_snapshot_inv; [exact Hnone|exact Hsession|].
        reflexivity.
      - exact Htoken.
    Qed.

    Variant ac_fork_snapshot_prop
        (Delta : @AbstractConfig _ (li_lts F)) (actor : tid)
        (ok : TS -> Prop) :
        @AbstractConfigProp _ (li_lts F) :=
    | ACForkSnapshotKeep rho pi (Hposs : Delta rho pi) :
        ac_fork_snapshot_prop Delta actor ok rho pi
    | ACForkSnapshotTake p pi start
        (Hposs : Delta (LPReady p) pi)
        (Hok : ok start)
        (Htoken : TMap.find actor pi = Some (ls_inv (lpool_getTop start)))
        (Hsession : TMap.find actor (lp_pop_ts p) = Some start)
        (Hnone : TMap.find actor (lp_snapshots p) = None) :
        ac_fork_snapshot_prop Delta actor ok
          (LPReady (start_snapshot actor p)) (snapshot_tokens actor start pi).

    Program Definition ac_fork_snapshot
        (Delta : @AbstractConfig _ (li_lts F)) (actor : tid)
        (ok : TS -> Prop) :
        @AbstractConfig _ (li_lts F) :=
      {| ac_active := ac_active Delta;
         ac_prop := ac_fork_snapshot_prop Delta actor ok |}.
    Next Obligation.
      destruct (ac_nonempty Delta) as (rho & pi & Hposs).
      exists rho, pi. now constructor.
    Qed.
    Next Obligation.
      dependent destruction H.
      - eapply ac_domain; eauto.
      - eapply domain_equiv_trans.
        + apply domain_equiv_symm. eapply poss_steps_domain.
          eapply (snapshot_poss_step actor); eassumption.
        + eapply ac_domain; eauto.
    Qed.

    Definition ac_push_snapshot
        (Delta : @AbstractConfig _ (li_lts F)) (actor : tid) :
        @AbstractConfig _ (li_lts F) :=
      ac_fork_snapshot Delta actor (fun _ => True).

    Lemma ac_fork_snapshot_keep
        (Delta : @AbstractConfig _ (li_lts F)) actor (ok : TS -> Prop) rho pi :
      Delta rho pi -> ac_fork_snapshot Delta actor ok rho pi.
    Proof. now constructor. Qed.

    Lemma ac_push_snapshot_keep
        (Delta : @AbstractConfig _ (li_lts F)) actor rho pi :
      Delta rho pi -> ac_push_snapshot Delta actor rho pi.
    Proof. now constructor. Qed.

    Lemma ac_fork_snapshot_take
        (Delta : @AbstractConfig _ (li_lts F)) actor (ok : TS -> Prop) start
        (p : @ListPoolState A) (pi : tmap (@LinState (li_sig F))) :
      Delta (LPReady p) pi ->
      ok start ->
      TMap.find actor pi = Some (ls_inv (lpool_getTop start)) ->
      TMap.find actor (lp_pop_ts p) = Some start ->
      TMap.find actor (lp_snapshots p) = None ->
      ac_fork_snapshot Delta actor ok
        (LPReady (start_snapshot actor p)) (snapshot_tokens actor start pi).
    Proof. intros. now constructor. Qed.

    Lemma ac_fork_snapshot_cases
        (Delta : @AbstractConfig _ (li_lts F)) actor (ok : TS -> Prop) rho pi :
      ac_fork_snapshot Delta actor ok rho pi ->
      Delta rho pi \/
      exists p pi0 start,
        Delta (LPReady p) pi0 /\
        ok start /\
        TMap.find actor pi0 = Some (ls_inv (lpool_getTop start)) /\
        TMap.find actor (lp_pop_ts p) = Some start /\
        TMap.find actor (lp_snapshots p) = None /\
        rho = LPReady (start_snapshot actor p) /\
        pi = snapshot_tokens actor start pi0.
    Proof.
      intro Hfork. change (ac_fork_snapshot_prop Delta actor ok rho pi) in Hfork.
      dependent destruction Hfork.
      - left. exact Hposs.
      - right. exists p, pi, start. repeat split; auto.
    Qed.

    Lemma ac_push_snapshot_cases
        (Delta : @AbstractConfig _ (li_lts F)) actor rho pi :
      ac_push_snapshot Delta actor rho pi ->
      Delta rho pi \/
      exists p pi0 start,
        Delta (LPReady p) pi0 /\
        TMap.find actor pi0 = Some (ls_inv (lpool_getTop start)) /\
        TMap.find actor (lp_pop_ts p) = Some start /\
        TMap.find actor (lp_snapshots p) = None /\
        rho = LPReady (start_snapshot actor p) /\
        pi = snapshot_tokens actor start pi0.
    Proof.
      intro Hfork. destruct (ac_fork_snapshot_cases _ _ _ _ _ Hfork)
        as [Hkeep|Htake]; [now left|right].
      destruct Htake as
        (p & pi0 & start & Hposs & _ & Htoken & Hsession & Hnone & Hrho & Hpi).
      exists p, pi0, start. repeat split; auto.
    Qed.

    Lemma ac_fork_snapshot_subset_steps
        (Delta : @AbstractConfig _ (li_lts F)) (actor : tid) (ok : TS -> Prop) :
      ac_subset (ac_fork_snapshot Delta actor ok) (ac_steps Delta).
    Proof.
      intros rho pi Hfork.
      destruct (ac_fork_snapshot_cases _ _ _ _ _ Hfork) as [Hkeep|Htake].
      - now apply ac_steps_refl.
      - destruct Htake as
          (p & pi0 & start & Hposs & Hok & Htoken & Hsession & Hnone & Hrho &
            Hpi).
        subst rho pi. econstructor; [exact Hposs|].
        now apply snapshot_poss_step.
    Qed.

    Lemma ac_push_snapshot_subset_steps
        (Delta : @AbstractConfig _ (li_lts F)) (actor : tid) :
      ac_subset (ac_push_snapshot Delta actor) (ac_steps Delta).
    Proof. apply ac_fork_snapshot_subset_steps. Qed.

    Variant snapshot_choice (scan : tid) (ok : TS -> Prop)
        (p : @ListPoolState A)
        (pi : tmap (@LinState (li_sig F))) :
        @ListPoolState A -> tmap (@LinState (li_sig F)) -> Prop :=
    | SnapshotChoiceKeep : snapshot_choice scan ok p pi p pi
    | SnapshotChoiceTake start
        (Hok : ok start)
        (Htoken : TMap.find scan pi = Some (ls_inv (lpool_getTop start)))
        (Hsession : TMap.find scan (lp_pop_ts p) = Some start)
        (Hnone : TMap.find scan (lp_snapshots p) = None) :
        snapshot_choice scan ok p pi (start_snapshot scan p)
          (snapshot_tokens scan start pi).

    Lemma ac_fork_snapshot_choice
        (Delta : @AbstractConfig _ (li_lts F)) scan (ok : TS -> Prop) p' pi' :
      ac_fork_snapshot Delta scan ok (LPReady p') pi' ->
      exists p pi,
        Delta (LPReady p) pi /\ snapshot_choice scan ok p pi p' pi'.
    Proof.
      intro Hfork. destruct (ac_fork_snapshot_cases _ _ _ _ _ Hfork)
        as [Hkeep|Htake].
      - exists p', pi'. split; [exact Hkeep|constructor].
      - destruct Htake as
          (p & pi & start & Hposs & Hok & Htoken & Hsession & Hnone & Hrho &
            Hpi).
        inversion Hrho; subst p'. subst pi'.
        exists p, pi. split; [exact Hposs|]. now constructor.
    Qed.

    Lemma snapshot_choice_shared scan (ok : TS -> Prop) p pi p' pi' :
      snapshot_choice scan ok p pi p' pi' -> pool_shared_eq p' p.
    Proof.
      intro Hchoice. inversion Hchoice; subst.
      - apply pool_shared_eq_refl.
      - apply pool_shared_eq_start_snapshot.
    Qed.

    Lemma snapshot_choice_foreign scan (ok : TS -> Prop) p pi p' pi' :
      snapshot_choice scan ok p pi p' pi' ->
      forall observer, scan <> observer ->
        TMap.find observer (lp_snapshots p') =
          TMap.find observer (lp_snapshots p) /\
        TMap.find observer pi' = TMap.find observer pi.
    Proof.
      intros Hchoice observer Hneq. inversion Hchoice; subst; simpl.
      - auto.
      - unfold start_snapshot, snapshot_tokens; simpl.
        rewrite !TMap.gso by congruence. auto.
    Qed.

    Lemma snapshot_choice_replay scan (ok : TS -> Prop) p pi p' pi' q qi :
      snapshot_choice scan ok p pi p' pi' ->
      pool_shared_eq p q ->
      TMap.find scan (lp_snapshots q) =
        TMap.find scan (lp_snapshots p) ->
      TMap.find scan qi = TMap.find scan pi ->
      exists q' qi',
        snapshot_choice scan ok q qi q' qi' /\
        branch_merge scan p' pi' q qi q' qi'.
    Proof.
      intros Hchoice Hshared Hsnapshot Htoken.
      inversion Hchoice; subst.
      - exists q, qi. split; [constructor|].
        unfold branch_merge. repeat split; try assumption;
          try apply pool_shared_eq_refl; reflexivity.
      - assert (Htoken_q :
          TMap.find scan qi = Some (ls_inv (lpool_getTop start)))
          by congruence.
        assert (Hsession_q : TMap.find scan (lp_pop_ts q) = Some start).
        { destruct Hshared as (_ & _ & _ & _ & _ & Hts). congruence. }
        assert (Hnone_q : TMap.find scan (lp_snapshots q) = None)
          by congruence.
        exists (start_snapshot scan q), (snapshot_tokens scan start qi).
        split; [now constructor|]. unfold branch_merge.
        split; [apply pool_shared_eq_start_snapshot|]. repeat split.
        + unfold start_snapshot; simpl. rewrite !TMap.gss.
          f_equal. symmetry. now apply shared_is_vertex_ext.
        + unfold snapshot_tokens. rewrite !TMap.gss. reflexivity.
        + intros observer Hneq. unfold start_snapshot; simpl.
          now rewrite TMap.gso by congruence.
        + intros observer Hneq. unfold snapshot_tokens.
          now rewrite TMap.gso by congruence.
    Qed.

    Lemma possibility_rectangular_fork_snapshot
        (Delta : @AbstractConfig _ (li_lts F)) scan (ok : TS -> Prop) :
      possibility_rectangular Delta ->
      possibility_rectangular (ac_fork_snapshot Delta scan ok).
    Proof.
      intros [Hshared Hmerge]. split.
      - intros p1 pi1 p2 pi2 H1 H2.
        destruct (ac_fork_snapshot_choice _ _ _ _ _ H1) as
          (q1 & qi1 & Hq1 & Hchoice1).
        destruct (ac_fork_snapshot_choice _ _ _ _ _ H2) as
          (q2 & qi2 & Hq2 & Hchoice2).
        eapply pool_shared_eq_trans.
        + apply snapshot_choice_shared in Hchoice1. exact Hchoice1.
        + eapply pool_shared_eq_trans; [eapply Hshared; eassumption|].
          apply pool_shared_eq_sym. now apply snapshot_choice_shared in
            Hchoice2.
      - intros actor p1 pi1 p2 pi2 H1 H2.
        destruct (ac_fork_snapshot_choice _ _ _ _ _ H1) as
          (q1 & qi1 & Hq1 & Hchoice1).
        destruct (ac_fork_snapshot_choice _ _ _ _ _ H2) as
          (q2 & qi2 & Hq2 & Hchoice2).
        destruct (Hmerge actor q1 qi1 q2 qi2 Hq1 Hq2) as
          (q & qi & Hq & Hmerged).
        destruct Hmerged as
          (Hqshared & Hactor_snapshot & Hactor_token & Hforeign_snapshot &
            Hforeign_token).
        destruct (PositiveMap.E.eq_dec actor scan) as [->|Hneq].
        + destruct (snapshot_choice_replay scan ok q1 qi1 p1 pi1 q qi
            Hchoice1 (pool_shared_eq_sym _ _
              (pool_shared_eq_trans _ _ _ Hqshared
                (pool_shared_eq_sym _ _ (Hshared _ _ _ _ Hq1 Hq2))))
            Hactor_snapshot Hactor_token) as
            (p & pi & Hchoice & Hresult).
          exists p, pi. split.
          * destruct Hchoice; [now apply ac_fork_snapshot_keep|].
            constructor; assumption.
            * destruct Hresult as
              (Hresult_shared & Hresult_snapshot & Hresult_token &
                Hresult_foreign_snapshot & Hresult_foreign_token).
            unfold branch_merge. split.
            -- eapply pool_shared_eq_trans; [exact Hresult_shared|].
               eapply pool_shared_eq_trans; [exact Hqshared|].
               apply pool_shared_eq_sym. now apply snapshot_choice_shared in
                 Hchoice2.
            -- repeat split; try assumption.
               ++ intros observer Hother.
               rewrite Hresult_foreign_snapshot by exact Hother.
               rewrite Hforeign_snapshot by exact Hother.
               symmetry. exact (proj1 (snapshot_choice_foreign _ _ _ _ _ _
                 Hchoice2 observer Hother)).
               ++ intros observer Hother.
               rewrite Hresult_foreign_token by exact Hother.
               rewrite Hforeign_token by exact Hother.
               symmetry. exact (proj2 (snapshot_choice_foreign _ _ _ _ _ _
                 Hchoice2 observer Hother)).
        + assert (Hscan_snapshot :
            TMap.find scan (lp_snapshots q) =
              TMap.find scan (lp_snapshots q2)).
          { apply Hforeign_snapshot. congruence. }
          assert (Hscan_token : TMap.find scan qi = TMap.find scan qi2).
          { apply Hforeign_token. congruence. }
          destruct (snapshot_choice_replay scan ok q2 qi2 p2 pi2 q qi
            Hchoice2 (pool_shared_eq_sym _ _ Hqshared)
            Hscan_snapshot Hscan_token) as
            (p & pi & Hchoice & Hresult).
          exists p, pi. split.
          * destruct Hchoice; [now apply ac_fork_snapshot_keep|].
            constructor; assumption.
            * destruct Hresult as
              (Hresult_shared & Hresult_scan_snapshot & Hresult_scan_token &
                Hresult_foreign_snapshot & Hresult_foreign_token).
            unfold branch_merge. split.
            -- eapply pool_shared_eq_trans; [exact Hresult_shared|].
               eapply pool_shared_eq_trans; [exact Hqshared|].
               apply pool_shared_eq_sym. now apply snapshot_choice_shared in
                 Hchoice2.
            -- repeat split.
               ++ rewrite Hresult_foreign_snapshot by exact (not_eq_sym Hneq).
               rewrite Hactor_snapshot.
               symmetry. exact (proj1 (snapshot_choice_foreign _ _ _ _ _ _
                 Hchoice1 actor (not_eq_sym Hneq))).
               ++ rewrite Hresult_foreign_token by exact (not_eq_sym Hneq).
               rewrite Hactor_token.
               symmetry. exact (proj2 (snapshot_choice_foreign _ _ _ _ _ _
                 Hchoice1 actor (not_eq_sym Hneq))).
               ++ intros observer Hactor_other.
               destruct (PositiveMap.E.eq_dec observer scan)
                 as [Heq|Hscan_other].
               ** subst observer. exact Hresult_scan_snapshot.
               ** rewrite Hresult_foreign_snapshot by congruence.
                  rewrite Hforeign_snapshot by exact Hactor_other.
                  symmetry. exact (proj1 (snapshot_choice_foreign _ _ _ _ _ _
                    Hchoice2 observer (not_eq_sym Hscan_other))).
               ++ intros observer Hactor_other.
               destruct (PositiveMap.E.eq_dec observer scan)
                 as [Heq|Hscan_other].
               ** subst observer. exact Hresult_scan_token.
               ** rewrite Hresult_foreign_token by congruence.
                  rewrite Hforeign_token by exact Hactor_other.
                  symmetry. exact (proj2 (snapshot_choice_foreign _ _ _ _ _ _
                    Hchoice2 observer (not_eq_sym Hscan_other))).
    Qed.

    Lemma possibility_rectangular_push_snapshot
        (Delta : @AbstractConfig _ (li_lts F)) scan :
      possibility_rectangular Delta ->
      possibility_rectangular (ac_push_snapshot Delta scan).
    Proof. apply possibility_rectangular_fork_snapshot. Qed.

    Fixpoint ac_push_saturate (actors : list tid)
        (Delta : @AbstractConfig _ (li_lts F)) :
        @AbstractConfig _ (li_lts F) :=
      match actors with
      | nil => Delta
      | scan :: rest => ac_push_saturate rest (ac_push_snapshot Delta scan)
      end.

    Lemma ac_push_saturate_keep (actors : list tid)
        (Delta : @AbstractConfig _ (li_lts F))
        (rho : abstract_state) (pi : tmap (@LinState (li_sig F))) :
      Delta rho pi -> ac_push_saturate actors Delta rho pi.
    Proof.
      revert Delta. induction actors as [|scan rest IH]; intros Delta Hposs;
        simpl; [exact Hposs|].
      apply IH. now apply ac_push_snapshot_keep.
    Qed.

    Lemma ac_push_saturate_take (actors : list tid)
        (Delta : @AbstractConfig _ (li_lts F)) observer start p pi :
      In observer actors ->
      Delta (LPReady p) pi ->
      TMap.find observer pi = Some (ls_inv (lpool_getTop start)) ->
      TMap.find observer (lp_pop_ts p) = Some start ->
      TMap.find observer (lp_snapshots p) = None ->
      ac_push_saturate actors Delta
        (LPReady (start_snapshot observer p))
        (snapshot_tokens observer start pi).
    Proof.
      revert Delta. induction actors as [|head rest IH]; intros Delta Hin
        Hposs Htoken Hsession Hnone; simpl in *; [contradiction|].
      destruct Hin as [->|Hin].
      - apply ac_push_saturate_keep.
        exact (ac_fork_snapshot_take Delta observer (fun _ => True) start p pi
          Hposs Logic.I Htoken Hsession Hnone).
      - eapply IH; [exact Hin| |exact Htoken|exact Hsession|exact Hnone].
        now apply ac_push_snapshot_keep.
    Qed.

    Lemma ac_push_saturate_subset_steps (actors : list tid)
        (Delta : @AbstractConfig _ (li_lts F)) :
      ac_subset (ac_push_saturate actors Delta) (ac_steps Delta).
    Proof.
      revert Delta. induction actors as [|scan rest IH]; intro Delta; simpl.
      - apply ac_steps_refl.
      - eapply ac_steps_subset_trans.
        + apply ac_push_snapshot_subset_steps.
        + apply IH.
    Qed.

    Lemma I_fork_snapshot (sigma : concrete_state)
        (Delta : @AbstractConfig _ (li_lts F)) (scan : tid) (ok : TS -> Prop) :
      I (sigma, Delta) -> I (sigma, ac_fork_snapshot Delta scan ok).
    Proof.
      intros [Hwf [Hall [Hrect Hcounter]]]. split; [exact Hwf|]. split.
      - intros rho pi Hfork.
        destruct (ac_fork_snapshot_cases _ _ _ _ _ Hfork) as [Hkeep|Htake].
        + now apply Hall.
        + destruct Htake as
            (p & pi0 & start & Hposs & Hok & Htoken & Hsession0 & Hnone &
              Hrho & Hpi).
          subst rho pi. destruct (Hall _ _ Hposs) as
            (p0 & Heq & Hpool & Hprotocol & Htimestamp & Hsession).
          inversion Heq; subst p0.
          exists (start_snapshot scan p). split; [reflexivity|]. split.
          * now apply pool_represents_start_snapshot.
          * split.
            -- eapply pool_protocol_start_snapshot; eauto.
            -- split.
               ++ unfold timestamp_pending_edges, outgoing_before,
                    start_snapshot in *. simpl in *. exact Htimestamp.
               ++ exact Hsession.
      - split.
        + now apply possibility_rectangular_fork_snapshot.
        + intros actor saved Hpending.
          destruct (Hcounter actor saved Hpending) as
            (rho & pi & start & Hposs & Hfind).
          exists rho, pi, start. split.
          * now apply ac_fork_snapshot_keep.
          * exact Hfind.
    Qed.

    Lemma I_push_snapshot (sigma : concrete_state)
        (Delta : @AbstractConfig _ (li_lts F)) (scan : tid) :
      I (sigma, Delta) -> I (sigma, ac_push_snapshot Delta scan).
    Proof. apply I_fork_snapshot. Qed.

    Lemma I_push_saturate (sigma : concrete_state) (actors : list tid)
        (Delta : @AbstractConfig _ (li_lts F)) :
      I (sigma, Delta) -> I (sigma, ac_push_saturate actors Delta).
    Proof.
      revert Delta. induction actors as [|scan rest IH]; intros Delta HI;
        simpl; [exact HI|].
      apply IH. now apply I_push_snapshot.
    Qed.

    Lemma token_rely_fork_snapshot
        (Delta : @AbstractConfig _ (li_lts F)) (observer scan : tid) (ok : TS -> Prop) :
      token_rely observer Delta (ac_fork_snapshot Delta scan ok).
    Proof.
      destruct (PositiveMap.E.eq_dec scan observer) as [->|Hneq].
      - split.
        + intros token (rho & pi & Hposs & Hfind).
          exists rho, pi. split; [now apply ac_fork_snapshot_keep|exact Hfind].
        + intros token (rho & pi & Hfork & Hfind).
          destruct (ac_fork_snapshot_cases _ _ _ _ _ Hfork)
            as [Hkeep|Htake].
          * left. now exists rho, pi.
          * destruct Htake as
              (p & pi0 & start & Hposs & Hok & Htoken & Hsession & Hnone &
                Hrho & Hpi).
            subst rho pi. right. exists start. split.
            -- unfold snapshot_tokens in Hfind.
               rewrite TMap.gss in Hfind. symmetry. exact Hfind.
            -- exists (LPReady p), pi0. auto.
      - apply token_equiv_rely. intros token. split.
        + intros (rho & pi & Hposs & Hfind). exists rho, pi. split.
          * now apply ac_fork_snapshot_keep.
          * exact Hfind.
        + intros (rho & pi & Hfork & Hfind).
          destruct (ac_fork_snapshot_cases _ _ _ _ _ Hfork)
            as [Hkeep|Htake].
          * now exists rho, pi.
          * destruct Htake as
              (p & pi0 & start & Hposs & Hok & Htoken & Hsession & Hnone &
                Hrho & Hpi).
            subst rho pi. exists (LPReady p), pi0. split; [exact Hposs|].
            unfold snapshot_tokens in Hfind.
            rewrite TMap.gso in Hfind by congruence. exact Hfind.
    Qed.

    Lemma token_equiv_fork_snapshot_foreign
        (Delta : @AbstractConfig _ (li_lts F)) (actor observer : tid) (ok : TS -> Prop) :
      actor <> observer ->
      token_equiv observer Delta (ac_fork_snapshot Delta actor ok).
    Proof.
      intros Hneq token. split.
      - intros (rho & pi & Hposs & Hfind).
        exists rho, pi. split; [now apply ac_fork_snapshot_keep|exact Hfind].
      - intros (rho & pi & Hfork & Hfind).
        destruct (ac_fork_snapshot_cases _ _ _ _ _ Hfork)
          as [Hkeep|Htake].
        + now exists rho, pi.
        + destruct Htake as
            (p & pi0 & start & Hposs & Hok & Htoken & Hsession & Hnone &
              Hrho & Hpi).
          subst rho pi. exists (LPReady p), pi0. split; [exact Hposs|].
          unfold snapshot_tokens in Hfind.
          rewrite TMap.gso in Hfind by congruence. exact Hfind.
    Qed.

    Lemma session_equiv_fork_snapshot
        (Delta : @AbstractConfig _ (li_lts F)) (observer scan : tid) (ok : TS -> Prop) :
      session_equiv observer Delta (ac_fork_snapshot Delta scan ok).
    Proof.
      apply session_equiv_of_covers.
      - intros rho pi Hposs. exists rho, pi.
        split; [now apply ac_fork_snapshot_keep|reflexivity].
      - intros rho pi Hfork.
        destruct (ac_fork_snapshot_cases _ _ _ _ _ Hfork) as [Hkeep|Htake].
        + exists rho, pi. auto.
        + destruct Htake as
            (p & pi0 & start & Hposs & Hok & Htoken & Hsession & Hnone &
              Hrho & Hpi).
          subst rho pi. exists (LPReady p), pi0. split; [exact Hposs|].
          reflexivity.
    Qed.

    Lemma token_rely_push_snapshot
        (Delta : @AbstractConfig _ (li_lts F)) (observer scan : tid) :
      token_rely observer Delta (ac_push_snapshot Delta scan).
    Proof. apply token_rely_fork_snapshot. Qed.

    Lemma token_rely_push_saturate (observer : tid) (actors : list tid)
        (Delta : @AbstractConfig _ (li_lts F)) :
      token_rely observer Delta (ac_push_saturate actors Delta).
    Proof.
      revert Delta. induction actors as [|scan rest IH]; intro Delta; simpl.
      - apply token_rely_refl.
      - eapply token_rely_trans.
        + apply token_rely_push_snapshot.
        + apply IH.
    Qed.

    Lemma pool_local_equiv_fork_snapshot
        (Delta : @AbstractConfig _ (li_lts F)) (observer scan : tid) (ok : TS -> Prop) :
      pool_local_equiv observer Delta (ac_fork_snapshot Delta scan ok).
    Proof.
      split.
      - intros local (rho & pi & Hposs & Hlocal).
        exists rho, pi. split; [now apply ac_fork_snapshot_keep|exact Hlocal].
      - intros local' (rho & pi & Hfork & Hlocal).
        destruct (ac_fork_snapshot_cases _ _ _ _ _ Hfork) as [Hkeep|Htake].
        + exists local'. split; [now exists rho, pi|reflexivity].
        + destruct Htake as
            (p & pi0 & start & Hposs & Hok & Htoken & Hsession & Hnone &
              Hrho & Hpi).
          subst rho pi. exists (pool_local_state observer (LPReady p)). split.
          * exists (LPReady p), pi0. auto.
          * exact (f_equal fst Hlocal).
    Qed.

    Lemma pool_local_equiv_push_snapshot
        (Delta : @AbstractConfig _ (li_lts F)) (observer scan : tid) :
      pool_local_equiv observer Delta (ac_push_snapshot Delta scan).
    Proof. apply pool_local_equiv_fork_snapshot. Qed.

    Lemma pool_local_equiv_push_trans (observer : tid)
        (Delta1 Delta2 Delta3 : @AbstractConfig _ (li_lts F)) :
      pool_local_equiv observer Delta1 Delta2 ->
      pool_local_equiv observer Delta2 Delta3 ->
      pool_local_equiv observer Delta1 Delta3.
    Proof.
      intros [H12keep H12new] [H23keep H23new]. split.
      - intros local Hview. now apply H23keep, H12keep.
      - intros local3 Hview3.
        destruct (H23new _ Hview3) as (local2 & Hview2 & Hfst23).
        destruct (H12new _ Hview2) as (local1 & Hview1 & Hfst12).
        exists local1. split; [exact Hview1|congruence].
    Qed.

    Lemma pool_local_equiv_push_saturate (observer : tid)
        (actors : list tid) (Delta : @AbstractConfig _ (li_lts F)) :
      pool_local_equiv observer Delta (ac_push_saturate actors Delta).
    Proof.
      revert Delta. induction actors as [|scan rest IH]; intro Delta; simpl.
      - apply pool_local_equiv_refl.
      - eapply pool_local_equiv_push_trans.
        + apply pool_local_equiv_push_snapshot.
        + apply IH.
    Qed.

    Lemma candidate_views_preserved_push_saturate (observer : tid)
        (actors : list tid) (Delta : @AbstractConfig _ (li_lts F)) :
      candidate_views_preserved observer Delta (ac_push_saturate actors Delta).
    Proof.
      intros done candidate Hview. unfold candidate_view in *.
      destruct Hview as
        (p & pi & N & Hposs & Htoken & Hsnapshot & Hvalue & Hdone & Hstatus &
          Hsafe).
      exists p, pi, N. repeat split; try assumption.
      now apply ac_push_saturate_keep.
    Qed.

    Lemma row_snapshot_views_preserved_push_saturate (observer : tid)
        (actors : list tid) (Delta : @AbstractConfig _ (li_lts F)) :
      row_snapshot_views_preserved observer Delta
        (ac_push_saturate actors Delta).
    Proof.
      intros owner saved Hview. unfold row_snapshot_view in *.
      destruct Hview as
        (p & pi & N & Hposs & Htoken & Hsnapshot & Hsaved & Hlive & Horder).
      exists p, pi, N. repeat split; try assumption.
      now apply ac_push_saturate_keep.
    Qed.

    Lemma push_causal_fork_snapshot (sigma : concrete_state)
        (observer : tid) (loc : Addr) (lower : nat)
        (Delta : @AbstractConfig _ (li_lts F)) (scan : tid) (ok : TS -> Prop) :
      push_causal observer loc lower (sigma, Delta) ->
      push_causal observer loc lower (sigma, ac_fork_snapshot Delta scan ok).
    Proof.
      unfold push_causal. simpl. intros Hcausal rho pi Hfork.
      destruct (ac_fork_snapshot_cases _ _ _ _ _ Hfork) as [Hkeep|Htake].
      - exact (Hcausal rho pi Hkeep).
      - destruct Htake as
          (p & pi0 & start & Hposs & Hok & Htoken & Hsession & Hnone &
            Hrho & Hpi).
        subst rho pi. destruct (Hcausal _ _ Hposs) as
          (p0 & Heq & Hpending & Hbefore).
        inversion Heq; subst p0. exists (start_snapshot scan p).
        split; [reflexivity|]. split; [exact Hpending|].
        unfold outgoing_before, start_snapshot in *. simpl in *. exact Hbefore.
    Qed.

    Lemma push_causal_push_snapshot (sigma : concrete_state)
        (observer : tid) (loc : Addr) (lower : nat)
        (Delta : @AbstractConfig _ (li_lts F)) (scan : tid) :
      push_causal observer loc lower (sigma, Delta) ->
      push_causal observer loc lower (sigma, ac_push_snapshot Delta scan).
    Proof. apply push_causal_fork_snapshot. Qed.

    Lemma session_equiv_push_saturate (observer : tid) (actors : list tid)
        (Delta : @AbstractConfig _ (li_lts F)) :
      session_equiv observer Delta (ac_push_saturate actors Delta).
    Proof.
      revert Delta. induction actors as [|scan rest IH]; intro Delta; simpl.
      - apply session_equiv_refl.
      - eapply session_equiv_trans.
        + apply session_equiv_fork_snapshot.
        + apply IH.
    Qed.

    Lemma push_causal_push_saturate (sigma : concrete_state)
        (observer : tid) (loc : Addr) (lower : nat) (actors : list tid)
        (Delta : @AbstractConfig _ (li_lts F)) :
      push_causal observer loc lower (sigma, Delta) ->
      push_causal observer loc lower (sigma, ac_push_saturate actors Delta).
    Proof.
      revert Delta. induction actors as [|scan rest IH]; intros Delta Hcausal;
        simpl; [exact Hcausal|].
      apply IH. now apply push_causal_push_snapshot.
    Qed.

    Lemma ac_inv_ready_cases
        (Delta : @AbstractConfig _ (li_lts F)) actor op p pi :
      ac_inv Delta actor op (LPReady p) pi ->
      exists pi0,
        Delta (LPReady p) pi0 /\ pi = TMap.add actor (ls_inv op) pi0.
    Proof. inversion 1; subst. eauto. Qed.

    Lemma ac_res_ready_cases
        (Delta : @AbstractConfig _ (li_lts F)) actor p pi :
      ac_res Delta actor (LPReady p) pi ->
      exists pi0, Delta (LPReady p) pi0 /\ pi = TMap.remove actor pi0.
    Proof. inversion 1; subst. eauto. Qed.

    Lemma possibility_rectangular_ac_inv
        (Delta : @AbstractConfig _ (li_lts F)) actor op :
      possibility_rectangular Delta ->
      possibility_rectangular (ac_inv Delta actor op).
    Proof.
      intros [Hshared Hmerge]. split.
      - intros p1 pi1 p2 pi2 H1 H2.
        destruct (ac_inv_ready_cases _ _ _ _ _ H1) as (qi1 & Hq1 & ->).
        destruct (ac_inv_ready_cases _ _ _ _ _ H2) as (qi2 & Hq2 & ->).
        eapply Hshared; eauto.
      - intros observer p1 pi1 p2 pi2 H1 H2.
        destruct (ac_inv_ready_cases _ _ _ _ _ H1) as (qi1 & Hq1 & ->).
        destruct (ac_inv_ready_cases _ _ _ _ _ H2) as (qi2 & Hq2 & ->).
        destruct (Hmerge observer p1 qi1 p2 qi2 Hq1 Hq2) as
          (p & pi & Hposs' & Hmerged).
        destruct Hmerged as
          (Hshared' & Hsnapshot & Htoken & Hforeign_snapshot & Hforeign_token).
        exists p, (TMap.add actor (ls_inv op) pi). split.
        + constructor. exact Hposs'.
        + unfold branch_merge. split; [exact Hshared'|]. repeat split.
          * exact Hsnapshot.
          * destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
            -- rewrite !TMap.gss. reflexivity.
            -- rewrite !TMap.gso by congruence. exact Htoken.
          * exact Hforeign_snapshot.
          * intros other Hother.
            destruct (PositiveMap.E.eq_dec other actor) as [->|Hneq].
            -- rewrite !TMap.gss. reflexivity.
            -- rewrite !TMap.gso by congruence. now apply Hforeign_token.
    Qed.

    Lemma possibility_rectangular_ac_res
        (Delta : @AbstractConfig _ (li_lts F)) actor :
      possibility_rectangular Delta ->
      possibility_rectangular (ac_res Delta actor).
    Proof.
      intros [Hshared Hmerge]. split.
      - intros p1 pi1 p2 pi2 H1 H2.
        destruct (ac_res_ready_cases _ _ _ _ H1) as (qi1 & Hq1 & ->).
        destruct (ac_res_ready_cases _ _ _ _ H2) as (qi2 & Hq2 & ->).
        eapply Hshared; eauto.
      - intros observer p1 pi1 p2 pi2 H1 H2.
        destruct (ac_res_ready_cases _ _ _ _ H1) as (qi1 & Hq1 & ->).
        destruct (ac_res_ready_cases _ _ _ _ H2) as (qi2 & Hq2 & ->).
        destruct (Hmerge observer p1 qi1 p2 qi2 Hq1 Hq2) as
          (p & pi & Hposs' & Hmerged).
        destruct Hmerged as
          (Hshared' & Hsnapshot & Htoken & Hforeign_snapshot & Hforeign_token).
        exists p, (TMap.remove actor pi). split.
        + constructor. exact Hposs'.
        + unfold branch_merge. split; [exact Hshared'|]. repeat split.
          * exact Hsnapshot.
          * destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
            -- rewrite !TMap.grs. reflexivity.
            -- rewrite !TMap.gro by congruence. exact Htoken.
          * exact Hforeign_snapshot.
          * intros other Hother.
            destruct (PositiveMap.E.eq_dec other actor) as [->|Hneq].
            -- rewrite !TMap.grs. reflexivity.
            -- rewrite !TMap.gro by congruence. now apply Hforeign_token.
    Qed.

    Lemma I_ac_inv (sigma : concrete_state)
        (Delta : @AbstractConfig _ (li_lts F))
        (actor : tid) (op : Sig.op (li_sig F)) :
      (forall rho pi, Delta rho pi -> TMap.find actor pi = None) ->
      I (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          sigma Delta) ->
      I (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          sigma (ac_inv Delta actor op)).
    Proof.
      intros Hnone [Hwf [Hrep [Hrect Hcounter]]].
      split; [exact Hwf|]. split.
      - intros rho pi Hposs. inversion Hposs; subst.
        destruct (Hrep _ _ Hposs0) as
          (p & -> & Hpool & Hprotocol & Htimestamp & Hsession).
        exists p. split; [reflexivity|]. split; [exact Hpool|]. split.
        + eapply pool_protocol_add_inv; eauto.
        + split; [exact Htimestamp|exact Hsession].
      - split.
        + now apply possibility_rectangular_ac_inv.
        + intros owner saved Hpending.
          destruct (Hcounter owner saved Hpending) as
            (rho & pi & start & Hposs & Hfind).
          destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
          * specialize (Hnone _ _ Hposs). congruence.
          * exists rho, (TMap.add actor (ls_inv op) pi), start. split.
            -- constructor. exact Hposs.
            -- rewrite TMap.gso by congruence. exact Hfind.
    Qed.

    Lemma I_ac_res (sigma : concrete_state)
        (Delta : @AbstractConfig _ (li_lts F))
        (actor : tid) (op : Sig.op (li_sig F)) (ret : Sig.ar op) :
      (forall rho pi, Delta rho pi ->
        TMap.find actor pi = Some (ls_linr op ret)) ->
      I (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          sigma Delta) ->
      I (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          sigma (ac_res Delta actor)).
    Proof.
      intros Hall [Hwf [Hrep [Hrect Hcounter]]].
      split; [exact Hwf|]. split.
      - intros rho pi Hposs. inversion Hposs; subst.
        destruct (Hrep _ _ Hposs0) as
          (p & -> & Hpool & Hprotocol & Htimestamp & Hsession).
        exists p. split; [reflexivity|]. split; [exact Hpool|]. split.
        + eapply pool_protocol_remove_completed; eauto.
        + split; [exact Htimestamp|exact Hsession].
      - split.
        + now apply possibility_rectangular_ac_res.
        + intros owner saved Hpending.
          destruct (Hcounter owner saved Hpending) as
            (rho & pi & start & Hposs & Hfind).
          destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
          * specialize (Hall _ _ Hposs). rewrite Hall in Hfind.
            dependent destruction Hfind.
          * exists rho, (TMap.remove actor pi), start. split.
            -- constructor. exact Hposs.
            -- rewrite TMap.gro by congruence. exact Hfind.
    Qed.

    Lemma set_ginv_exposes_active actor op :
      ⊨ AssertionsSet.A.ComposeA I (AssertionsSet.Ginv actor op) ==>>
        Active actor op.
    Proof.
      intros w [pre [HIpre [Hsigma [Hnone Hequiv]]]].
      destruct pre as [sigma Delta], w as [sigma' Delta']; simpl in *.
      subst sigma'. split.
      - eapply I_config_equiv.
        + intros rho pi. symmetry. apply Hequiv.
        + apply I_ac_inv; assumption.
      - unfold ALin. intros rho pi Hposs.
        apply (proj1 (Hequiv _ _)) in Hposs.
        eapply ac_inv_find_eq. exact Hposs.
    Qed.

    Lemma set_gret_closes_completed actor op ret :
      ⊨ AssertionsSet.A.ComposeA (Completed actor op ret)
        (AssertionsSet.Gret actor op ret) ==>> I.
    Proof.
      intros w [pre [[HIpre Hlin] [Hsigma [Hall Hequiv]]]].
      destruct pre as [sigma Delta], w as [sigma' Delta']; simpl in *.
      subst sigma'. eapply I_config_equiv.
      - intros rho pi. symmetry. apply Hequiv.
      - apply I_ac_res with (op := op) (ret := ret); assumption.
    Qed.

    Lemma completed_has_return_token actor op ret sigma Delta :
      Completed actor op ret
        (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          sigma Delta) ->
      forall rho pi, Delta rho pi ->
        TMap.find actor pi = Some (ls_linr op ret).
    Proof. intros [_ Hlin]. exact Hlin. Qed.

    Definition tryRemove_rho (owner : tid) (loc : Addr) (removed : bool)
        (rho : abstract_state) : abstract_state :=
      match rho with
      | LPReady p =>
          LPReady (if removed then mark_garbage (pair owner loc) p else p)
      | LPAtomicPending p actor op => LPAtomicPending p actor op
      end.

    Definition atomic_tokens (actor : tid) (op : Sig.op (li_sig F))
        (ret : Sig.ar op) (pi : tmap (@LinState (li_sig F))) :=
      TMap.add actor (ls_linr op ret) (TMap.add actor (ls_lini op) pi).

    Lemma atomic_tokens_same actor op ret pi :
      TMap.find actor (atomic_tokens actor op ret pi) =
        Some (ls_linr op ret).
    Proof. unfold atomic_tokens. apply TMap.gss. Qed.

    Lemma atomic_tokens_other actor op ret pi observer :
      actor <> observer ->
      TMap.find observer (atomic_tokens actor op ret pi) =
        TMap.find observer pi.
    Proof.
      intro Hneq. unfold atomic_tokens. rewrite !TMap.gso by congruence.
      reflexivity.
    Qed.

    Lemma possibility_rectangular_atomic_image
        (Delta : @AbstractConfig _ (li_lts F))
        (f : @ListPoolState A -> @ListPoolState A)
        (rhof : abstract_state -> abstract_state)
        actor op ret
        (Hsteps : forall rho pi, Delta rho pi ->
          poss_steps (PossOk rho pi)
            (PossOk (rhof rho) (atomic_tokens actor op ret pi))) :
      (forall p, rhof (LPReady p) = LPReady (f p)) ->
      (forall rho q, rhof rho = LPReady q ->
        exists p, rho = LPReady p /\ q = f p) ->
      (forall p q, pool_shared_eq p q -> pool_shared_eq (f p) (f q)) ->
      (forall observer p,
        TMap.find observer (lp_snapshots (f p)) =
          TMap.find observer (lp_snapshots p)) ->
      possibility_rectangular Delta ->
      possibility_rectangular
        (ac_image Delta rhof (atomic_tokens actor op ret) Hsteps).
    Proof.
      intros Hrho Hshape Hshared_f Hsnapshot_f [Hshared Hmerge]. split.
      - intros p1 pi1 p2 pi2 H1 H2.
        destruct (ac_image_elim _ _ _ _ _ _ H1) as
          (rho1 & qi1 & Hq1 & Hrho1 & Hpi1).
        destruct (ac_image_elim _ _ _ _ _ _ H2) as
          (rho2 & qi2 & Hq2 & Hrho2 & Hpi2).
        destruct (Hshape _ _ (eq_sym Hrho1)) as (q1 & -> & ->).
        destruct (Hshape _ _ (eq_sym Hrho2)) as (q2 & -> & ->).
        apply Hshared_f. eapply Hshared; eauto.
      - intros observer p1 pi1 p2 pi2 H1 H2.
        destruct (ac_image_elim _ _ _ _ _ _ H1) as
          (rho1 & qi1 & Hq1 & Hrho1 & Hpi1).
        destruct (ac_image_elim _ _ _ _ _ _ H2) as
          (rho2 & qi2 & Hq2 & Hrho2 & Hpi2).
        destruct (Hshape _ _ (eq_sym Hrho1)) as (q1 & -> & ->).
        destruct (Hshape _ _ (eq_sym Hrho2)) as (q2 & -> & ->).
        subst pi1. subst pi2.
        destruct (Hmerge observer q1 qi1 q2 qi2 Hq1 Hq2) as
          (q & qi & Hq & Hmerged).
        destruct Hmerged as
          (Hshared' & Hsnapshot & Htoken & Hforeign_snapshot & Hforeign_token).
        exists (f q), (atomic_tokens actor op ret qi). split.
        + rewrite <- Hrho. constructor. exact Hq.
        + unfold branch_merge. split.
          * now apply Hshared_f.
          * repeat split.
            -- rewrite !Hsnapshot_f. exact Hsnapshot.
            -- destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
               ++ rewrite !atomic_tokens_same. reflexivity.
               ++ rewrite !atomic_tokens_other by congruence. exact Htoken.
            -- intros other Hother. rewrite !Hsnapshot_f.
               now apply Hforeign_snapshot.
            -- intros other Hother.
               destruct (PositiveMap.E.eq_dec other actor) as [->|Hneq].
               ++ rewrite !atomic_tokens_same. reflexivity.
               ++ rewrite !atomic_tokens_other by congruence.
                  now apply Hforeign_token.
    Qed.

    Lemma possibility_rectangular_add_image
        (Delta : @AbstractConfig _ (li_lts F))
        (f : @ListPoolState A -> @ListPoolState A)
        (rhof : abstract_state -> abstract_state)
        actor token
        (Hsteps : forall rho pi, Delta rho pi ->
          poss_steps (PossOk rho pi)
            (PossOk (rhof rho) (TMap.add actor token pi))) :
      (forall p, rhof (LPReady p) = LPReady (f p)) ->
      (forall rho q, rhof rho = LPReady q ->
        exists p, rho = LPReady p /\ q = f p) ->
      (forall p q, pool_shared_eq p q -> pool_shared_eq (f p) (f q)) ->
      (forall observer p,
        TMap.find observer (lp_snapshots (f p)) =
          TMap.find observer (lp_snapshots p)) ->
      possibility_rectangular Delta ->
      possibility_rectangular
        (ac_image Delta rhof (fun pi => TMap.add actor token pi) Hsteps).
    Proof.
      intros Hrho Hshape Hshared_f Hsnapshot_f [Hshared Hmerge]. split.
      - intros p1 pi1 p2 pi2 H1 H2.
        destruct (ac_image_elim _ _ _ _ _ _ H1) as
          (rho1 & qi1 & Hq1 & Hrho1 & Hpi1).
        destruct (ac_image_elim _ _ _ _ _ _ H2) as
          (rho2 & qi2 & Hq2 & Hrho2 & Hpi2).
        destruct (Hshape _ _ (eq_sym Hrho1)) as (q1 & -> & ->).
        destruct (Hshape _ _ (eq_sym Hrho2)) as (q2 & -> & ->).
        apply Hshared_f. eapply Hshared; eauto.
      - intros observer p1 pi1 p2 pi2 H1 H2.
        destruct (ac_image_elim _ _ _ _ _ _ H1) as
          (rho1 & qi1 & Hq1 & Hrho1 & Hpi1).
        destruct (ac_image_elim _ _ _ _ _ _ H2) as
          (rho2 & qi2 & Hq2 & Hrho2 & Hpi2).
        destruct (Hshape _ _ (eq_sym Hrho1)) as (q1 & -> & ->).
        destruct (Hshape _ _ (eq_sym Hrho2)) as (q2 & -> & ->).
        subst pi1. subst pi2.
        destruct (Hmerge observer q1 qi1 q2 qi2 Hq1 Hq2) as
          (q & qi & Hq & Hmerged).
        destruct Hmerged as
          (Hshared' & Hsnapshot & Htoken & Hforeign_snapshot & Hforeign_token).
        exists (f q), (TMap.add actor token qi). split.
        + rewrite <- Hrho. constructor. exact Hq.
        + unfold branch_merge. split.
          * now apply Hshared_f.
          * repeat split.
            -- rewrite !Hsnapshot_f. exact Hsnapshot.
            -- destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
               ++ rewrite !TMap.gss. reflexivity.
               ++ rewrite !TMap.gso by congruence. exact Htoken.
            -- intros other Hother. rewrite !Hsnapshot_f.
               now apply Hforeign_snapshot.
            -- intros other Hother.
               destruct (PositiveMap.E.eq_dec other actor) as [->|Hneq].
               ++ rewrite !TMap.gss. reflexivity.
               ++ rewrite !TMap.gso by congruence.
                  now apply Hforeign_token.
    Qed.

    Lemma pool_shared_eq_mark_garbage_compat removed p q :
      pool_shared_eq p q ->
      pool_shared_eq (mark_garbage removed p) (mark_garbage removed q).
    Proof.
      intros (Hvertices & Hedges & Hpending & Hgarbage & Hpop_starts & Hpop_ts).
      unfold pool_shared_eq, mark_garbage; simpl.
      repeat split; congruence.
    Qed.

    Lemma mark_garbage_snapshot_find removed observer
        (p : @ListPoolState A) :
      TMap.find observer (lp_snapshots (mark_garbage removed p)) =
        TMap.find observer (lp_snapshots p).
    Proof. reflexivity. Qed.

    Definition array_tryRemove_result
        (ev : @ThreadEvent (@ESPListArray A)) : option bool :=
      match te_ev ev with
      | ResEv (array_tryRemove _ _) removed => Some removed
      | _ => None
      end.

    Lemma array_tryRemove_true_shape actor owner loc control control' :
      @StepSPListArray A D
        (Build_ThreadEvent actor
          (ResEv (array_tryRemove owner loc) true)) control control' ->
      exists a,
        control = ArrayAtomicPending a actor (array_tryRemove owner loc) /\
        control' = ArrayReady (remove_node (pair owner loc) a) /\
        array_live a (pair owner loc).
    Proof.
      intro Hstep. remember (Build_ThreadEvent actor
        (ResEv (array_tryRemove owner loc) true)) as ev eqn:Hev in Hstep.
      inversion Hstep.
      all: try match goal with
        | Hctor : ?remembered = ?rhs,
          Htarget : ?remembered = ?target |- _ =>
            let Hevent := fresh "Hevent" in
            pose proof (eq_trans (eq_sym Htarget) Hctor) as Hevent;
            let Hresult := fresh "Hresult" in
            pose proof (f_equal array_tryRemove_result Hevent) as Hresult;
            cbv [array_tryRemove_result] in Hresult;
            first [discriminate Hresult |
              dependent destruction Hevent;
              eexists; split; [reflexivity|]; split;
              [reflexivity|eassumption]]
        end.
    Qed.

    Lemma array_tryRemove_false_shape actor owner loc control control' :
      @StepSPListArray A D
        (Build_ThreadEvent actor
          (ResEv (array_tryRemove owner loc) false)) control control' ->
      exists a,
        control = ArrayAtomicPending a actor (array_tryRemove owner loc) /\
        control' = ArrayReady a /\ as_garbage a (pair owner loc).
    Proof.
      intro Hstep. remember (Build_ThreadEvent actor
        (ResEv (array_tryRemove owner loc) false)) as ev eqn:Hev in Hstep.
      inversion Hstep.
      all: match goal with
        | Hctor : ?remembered = ?rhs,
          Htarget : ?remembered = ?target |- _ =>
            let Hevent := fresh "Hevent" in
            pose proof (eq_trans (eq_sym Htarget) Hctor) as Hevent;
            let Hresult := fresh "Hresult" in
            pose proof (f_equal array_tryRemove_result Hevent) as Hresult;
            cbv [array_tryRemove_result] in Hresult;
            first [discriminate Hresult |
              dependent destruction Hevent;
              eexists; split; [reflexivity|]; split;
              [reflexivity|eassumption]]
        end.
    Qed.

    Lemma tryRemove_inv_preserves_active actor owner loc :
      AssertionsSet.PUpdate (G actor)
        (Build_ThreadEvent actor (InvEv (inl (array_tryRemove owner loc))))
        (Active actor (lpool_tryRemove owner loc))
        (Active actor (lpool_tryRemove owner loc)).
    Proof.
      intros [control tss] Delta [HI Hlin] [control' tss'] Hstep.
      simpl in Hstep. destruct Hstep as [Harray ->].
      inversion Harray; subst; try discriminate.
      exists Delta. split; [apply ac_steps_refl|]. split.
      - split; [exact HI|exact Hlin].
      - unfold G. split.
        + intros observer Hneq. apply token_rely_refl.
        + split; [intros observer Hneq; apply pool_local_equiv_refl|].
          split.
          * intros observer causal_loc lower Hneq Hcausal. exact Hcausal.
          * split; [intros observer Hneq; reflexivity|].
            split; [intros observer Hneq; reflexivity|]. split.
            -- intros observer Hneq. apply candidate_views_preserved_refl.
            -- split.
               ++ intros observer Hneq.
                  apply row_snapshot_views_preserved_refl.
               ++ split.
                  ** apply array_evolves_same_array. reflexivity.
                  ** split; [simpl; lia|].
                     split.
                     --- intros observer Hneq.
                         apply candidate_row_views_preserved_refl.
                     --- split.
                         +++ intros observer Hneq.
                             unfold node_cuts_preserved, concrete_array,
                               array_payload. simpl. firstorder.
                         +++ split.
                             { unfold garbage_evolves, concrete_array,
                                 array_payload. simpl. firstorder. }
                             split.
                             { unfold intervals_evolve, concrete_array,
                                 array_payload. simpl. firstorder. }
                             intros observer Hneq. apply session_equiv_refl.
    Qed.

    Lemma tryRemove_true_res_update actor owner loc :
      AssertionsSet.PUpdate (G actor)
        (Build_ThreadEvent actor
          (ResEv (inl (array_tryRemove owner loc)) true))
        (Active actor (lpool_tryRemove owner loc))
        (Completed actor (lpool_tryRemove owner loc) true).
    Proof.
      intros [control tss] Delta [HIpre Hlin] [control' tss'] Hstep.
      simpl in Hstep. destruct Hstep as [Harray ->].
      destruct (array_tryRemove_true_shape actor owner loc _ _ Harray)
        as (a & -> & -> & Hlive).
      destruct HIpre as [Hwf [Hall [Hrect Hcounter]]].
      assert (Hsteps : forall rho pi, Delta rho pi ->
        poss_steps (PossOk rho pi)
          (PossOk (tryRemove_rho owner loc true rho)
            (atomic_tokens actor (lpool_tryRemove owner loc) true pi))).
      { intros rho pi Hposs.
        destruct (Hall _ _ Hposs) as
          (p & -> & Hpool & Hprotocol & Htimestamp & Hsession).
        destruct Hpool as (Hvertices & Hedges & Hedgevertices & Hgarbage &
          Hpending & Hsnapshots & Hrows).
        assert (Hvertex : is_vertex p (pair owner loc)).
        { unfold is_vertex, array_live, array_vertex in *.
          destruct Hlive as [Hvalue Hnotgarbage].
          rewrite Hvertices. exact Hvalue. }
        assert (Hpoollive : is_live p (pair owner loc)).
        { split; [exact Hvertex|].
          intro Hgarbage_p. destruct Hlive as [_ Hnotgarbage].
          apply Hnotgarbage. apply (proj1 (Hgarbage _)). exact Hgarbage_p. }
        eapply rt_trans.
        - apply rt_step. eapply ps_inv.
          + eapply step_tryRemove_inv; [left; exact Hvertex|reflexivity].
          + exact (Hlin _ _ Hposs).
        - apply rt_step. eapply ps_ret.
          + eapply step_tryRemove_succ; [exact Hpoollive|reflexivity].
          + apply TMap.gss. }
      exists (ac_image Delta (tryRemove_rho owner loc true)
        (atomic_tokens actor (lpool_tryRemove owner loc) true) Hsteps).
      split; [apply ac_image_subset_steps|]. split.
      - split.
        + split.
          * destruct Hlive as [Hlive_vertex Hlive_not_garbage].
            eapply concrete_wf_remove; eassumption.
          * split.
            -- intros rho pi Himage.
            destruct (ac_image_elim _ _ _ _ _ _ Himage) as
              (rho0 & pi0 & Hposs & -> & ->).
            destruct (Hall _ _ Hposs) as
              (p & -> & Hpool & Hprotocol & Htimestamp & Hsession).
            exists (mark_garbage (pair owner loc) p). split; [reflexivity|].
            split.
            ++ apply pool_represents_mark_garbage. exact Hpool.
            ++ split.
               ** simpl. eapply pool_protocol_atomic; eauto.
               ** unfold timestamp_pending_edges in *. simpl in *.
                  split; [exact Htimestamp|exact Hsession].
            -- split.
               ++ eapply possibility_rectangular_atomic_image.
                  ** intro p. reflexivity.
                  ** intros rho q Hready. destruct rho; simpl in Hready.
                     --- inversion Hready. eexists; split; reflexivity.
                     --- discriminate.
                  ** apply pool_shared_eq_mark_garbage_compat.
                  ** apply mark_garbage_snapshot_find.
                  ** exact Hrect.
               ++ intros observer saved Hpending.
                  change (TMap.find observer (as_pending_counters a) =
                    Some saved) in Hpending.
                  destruct (Hcounter observer saved Hpending) as
                    (rho0 & pi0 & start0 & Hposs & Hfind).
                  destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
                  ** pose proof (Hlin rho0 pi0 Hposs) as Hlin_actor.
                     pose proof (eq_trans (eq_sym Hlin_actor) Hfind)
                       as Hstate_eq.
                     dependent destruction Hstate_eq.
                  ** exists (tryRemove_rho owner loc true rho0),
                       (atomic_tokens actor
                         (lpool_tryRemove owner loc) true pi0), start0. split.
                     --- constructor. exact Hposs.
                     --- rewrite atomic_tokens_other by congruence. exact Hfind.
        + unfold ALin. intros rho pi Himage.
          destruct (ac_image_elim _ _ _ _ _ _ Himage) as
            (rho0 & pi0 & Hposs & -> & ->). apply TMap.gss.
      - unfold G. split.
        + intros observer Hneq.
          apply token_equiv_rely. eapply token_equiv_image_foreign. intro pi.
          unfold atomic_tokens. repeat rewrite TMap.gso by congruence.
          reflexivity.
        + split.
          * intros observer Hneq.
            eapply pool_local_equiv_image_foreign. intro rho.
            destruct rho; reflexivity.
          * split.
            -- intros observer causal_loc bound Hneq Hcausal rho pi Himage.
               destruct (ac_image_elim _ _ _ _ _ _ Himage) as
                 (rho0 & pi0 & Hposs & -> & ->).
               destruct (Hcausal _ _ Hposs) as
                 (p & -> & Hpending_pool & Hbefore).
               exists (mark_garbage (pair owner loc) p).
               split; [reflexivity|]. split; [exact Hpending_pool|].
               intros older Hedge.
               destruct (Hbefore older Hedge) as
                 (old_lower & old_upper & Htimestamp & Hlt).
               exists old_lower, old_upper. split; [exact Htimestamp|exact Hlt].
            -- split; [intros observer Hneq; reflexivity|].
               split; [intros observer Hneq; reflexivity|]. split.
               ++ intros observer Hneq done candidate Hview.
                  unfold candidate_view in *.
                  destruct Hview as
                    (p & pi & N & Hposs & Htoken & Hsnapshot & Hvalue &
                      Hdone & Hstatus & Hsafe).
                  exists (mark_garbage (pair owner loc) p),
                    (atomic_tokens actor (lpool_tryRemove owner loc) true pi), N.
                  repeat split.
                  ** change (ac_image_prop Delta
                       (tryRemove_rho owner loc true)
                       (atomic_tokens actor (lpool_tryRemove owner loc) true)
                       Hsteps
                       (tryRemove_rho owner loc true (LPReady p))
                       (atomic_tokens actor
                         (lpool_tryRemove owner loc) true pi)).
                     constructor. exact Hposs.
                  ** unfold atomic_tokens. repeat rewrite TMap.gso by congruence.
                     exact Htoken.
                  ** exact Hsnapshot.
                  ** exact Hvalue.
                  ** exact Hdone.
                  ** eapply candidate_status_mark_garbage. exact Hstatus.
                  ** now apply candidate_tstop_safe_mark_garbage.
               ++ split.
                  ** intros observer Hneq row saved Hview.
                     unfold row_snapshot_view in *.
                     destruct Hview as
                       (p & pi & N & Hposs & Htoken & Hsnapshot &
                         Hsaved & Hlive_saved & Horder_saved).
                     exists (mark_garbage (pair owner loc) p),
                       (atomic_tokens actor
                         (lpool_tryRemove owner loc) true pi), N.
                     repeat split.
                     --- change (ac_image_prop Delta
                           (tryRemove_rho owner loc true)
                           (atomic_tokens actor
                             (lpool_tryRemove owner loc) true)
                           Hsteps
                           (tryRemove_rho owner loc true (LPReady p))
                           (atomic_tokens actor
                             (lpool_tryRemove owner loc) true pi)).
                         constructor. exact Hposs.
                     --- unfold atomic_tokens.
                         repeat rewrite TMap.gso by congruence. exact Htoken.
                     --- exact Hsnapshot.
                     --- exact Hsaved.
                     --- intros address Hmember Hnotgarbage.
                         apply Hlive_saved; [exact Hmember|].
                         intro Hold. apply Hnotgarbage. simpl.
                         unfold set_add. right. exact Hold.
                     --- intros newer older Hnewer_member Holder_member
                           Hnewer_live Holder_live Hedge.
                         apply Horder_saved; try assumption.
                         +++ intro Hgarbage. apply Hnewer_live. simpl.
                             unfold set_add. right. exact Hgarbage.
                         +++ intro Hgarbage. apply Holder_live. simpl.
                             unfold set_add. right. exact Hgarbage.
                  ** split.
                     --- apply array_evolves_remove.
                     --- split; [simpl; lia|].
                         split.
                         ++++ intros observer Hneq done candidate row saved Hview.
                         unfold candidate_row_view in *.
                         destruct Hview as
                           (p & pi & N & Hposs & Htoken & Hsnapshot & Hvalue &
                             Hdone & Hstatus & Hcovered & Horder & Hsafe).
                         exists (mark_garbage (pair owner loc) p),
                           (atomic_tokens actor
                             (lpool_tryRemove owner loc) true pi), N.
                         repeat split.
                         ***** change (ac_image_prop Delta
                               (tryRemove_rho owner loc true)
                               (atomic_tokens actor
                                 (lpool_tryRemove owner loc) true)
                               Hsteps
                               (tryRemove_rho owner loc true (LPReady p))
                               (atomic_tokens actor
                                 (lpool_tryRemove owner loc) true pi)).
                              constructor. exact Hposs.
                         ***** unfold atomic_tokens.
                              repeat rewrite TMap.gso by congruence.
                              exact Htoken.
                         ***** exact Hsnapshot.
                         ***** exact Hvalue.
                         ***** exact Hdone.
                         ***** now apply candidate_status_mark_garbage.
                         ***** intros address Hmember Hnew_live.
                              apply Hcovered; [exact Hmember|].
                              intro Hold. apply Hnew_live. simpl.
                              unfold set_add. right. exact Hold.
                         ***** intros newer older Hnewer_member Holder_member
                                Hnewer_live Holder_live Hedge.
                              apply Horder; try assumption.
                              ------ intro Hold. apply Hnewer_live. simpl.
                                   unfold set_add. right. exact Hold.
                              ------ intro Hold. apply Holder_live. simpl.
                                   unfold set_add. right. exact Hold.
                         ***** now apply candidate_tstop_safe_mark_garbage.
                         ++++ split.
                              ***** intros observer Hneq progress0 start0 Hinside
                                      Hfallback Hsession_all Hcuts n value Hlive_node Hvalue
                                      Hnotignored.
                                    unfold concrete_array, array_payload in *.
                                    simpl in Hlive_node, Hvalue.
                                    destruct Hlive_node as [Hvertex Hnotgarbage].
                                    assert (Hold_live : array_live a n).
                                    { split; [exact Hvertex|]. intro Hold.
                                      apply Hnotgarbage. unfold set_add. right.
                                      exact Hold. }
                                    destruct (Hcuts n value Hold_live Hvalue
                                      Hnotignored) as
                                      (p & pi & N & Hposs & Htoken & Hsnapshot &
                                        Hnode_value & Hmember & Hcut).
                                    exists (mark_garbage (pair owner loc) p),
                                      (atomic_tokens actor
                                        (lpool_tryRemove owner loc) true pi), N.
                                    repeat split; try assumption.
                                    ------ change (ac_image_prop Delta
                                          (tryRemove_rho owner loc true)
                                          (atomic_tokens actor
                                            (lpool_tryRemove owner loc) true)
                                          Hsteps
                                          (tryRemove_rho owner loc true
                                            (LPReady p))
                                          (atomic_tokens actor
                                            (lpool_tryRemove owner loc) true pi)).
                                         constructor. exact Hposs.
                                    ------ unfold atomic_tokens.
                                         repeat rewrite TMap.gso by congruence.
                                         exact Htoken.
                                    ------ intros newer Hnewer Hnewer_live Hedge.
                                         apply Hcut with (newer := newer);
                                           try assumption.
                                         intro Hold. apply Hnewer_live. simpl.
                                         unfold set_add. right. exact Hold.
                              ***** split.
                                    ------ unfold garbage_evolves,
                                           concrete_array, array_payload. simpl.
                                           intros n Hold. unfold set_add. right.
                                           exact Hold.
                                    ------ split.
                                           { unfold intervals_evolve,
                                               concrete_array, array_payload.
                                             simpl. firstorder. }
                                           { intros observer Hneq.
                                             apply session_equiv_image_foreign.
                                             intro rho. destruct rho; reflexivity. }
    Qed.

    Lemma tryRemove_false_res_update actor owner loc :
      AssertionsSet.PUpdate (G actor)
        (Build_ThreadEvent actor
          (ResEv (inl (array_tryRemove owner loc)) false))
        (Active actor (lpool_tryRemove owner loc))
        (Completed actor (lpool_tryRemove owner loc) false).
    Proof.
      intros [control tss] Delta [HIpre Hlin] [control' tss'] Hstep.
      simpl in Hstep. destruct Hstep as [Harray ->].
      destruct (array_tryRemove_false_shape actor owner loc _ _ Harray)
        as (a & -> & -> & Hgarbage_a).
      destruct HIpre as [Hwf [Hall [Hrect Hcounter]]].
      assert (Hsteps : forall rho pi, Delta rho pi ->
        poss_steps (PossOk rho pi)
          (PossOk (tryRemove_rho owner loc false rho)
            (atomic_tokens actor (lpool_tryRemove owner loc) false pi))).
      { intros rho pi Hposs.
        destruct (Hall _ _ Hposs) as
          (p & -> & Hpool & Hprotocol & Htimestamp & Hsession).
        destruct Hpool as (Hvertices & Hedges & Hedgevertices & Hgarbage &
          Hpending & Hsnapshots & Hrows).
        assert (Hgarbage_p : lp_garbage p (pair owner loc)).
        { apply (proj2 (Hgarbage _)). exact Hgarbage_a. }
        eapply rt_trans.
        - apply rt_step. eapply ps_inv.
          + eapply step_tryRemove_inv.
            * right; exact Hgarbage_p.
            * reflexivity.
          + exact (Hlin _ _ Hposs).
        - apply rt_step. eapply ps_ret.
          + eapply step_tryRemove_fail; [exact Hgarbage_p|reflexivity].
          + apply TMap.gss. }
      exists (ac_image Delta (tryRemove_rho owner loc false)
        (atomic_tokens actor (lpool_tryRemove owner loc) false) Hsteps).
      split; [apply ac_image_subset_steps|]. split.
      - split.
        + split.
          * exact Hwf.
          * split.
            -- intros rho pi Himage.
               destruct (ac_image_elim _ _ _ _ _ _ Himage) as
                 (rho0 & pi0 & Hposs & -> & ->).
               destruct (Hall _ _ Hposs) as
                 (p & -> & Hpool & Hprotocol & Htimestamp & Hsession).
               exists p. split; [reflexivity|]. split; [exact Hpool|]. split.
               ++ simpl. eapply pool_protocol_atomic; eauto.
               ++ split; [exact Htimestamp|exact Hsession].
            -- split.
               ++ eapply possibility_rectangular_atomic_image.
                  ** intro p. reflexivity.
                  ** intros rho q Hready. destruct rho; simpl in Hready.
                     --- inversion Hready. eexists; split; reflexivity.
                     --- discriminate.
                  ** intros p q Hshared. exact Hshared.
                  ** intros observer p. reflexivity.
                  ** exact Hrect.
               ++ intros observer saved Hpending.
                  change (TMap.find observer (as_pending_counters a) =
                    Some saved) in Hpending.
                  destruct (Hcounter observer saved Hpending) as
                    (rho0 & pi0 & start0 & Hposs & Hfind).
                  destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
                  ** pose proof (Hlin rho0 pi0 Hposs) as Hlin_actor.
                     pose proof (eq_trans (eq_sym Hlin_actor) Hfind)
                       as Hstate_eq. dependent destruction Hstate_eq.
                  ** exists (tryRemove_rho owner loc false rho0),
                       (atomic_tokens actor
                         (lpool_tryRemove owner loc) false pi0), start0. split.
                     --- constructor. exact Hposs.
                     --- rewrite atomic_tokens_other by congruence. exact Hfind.
        + unfold ALin. intros rho pi Himage.
          destruct (ac_image_elim _ _ _ _ _ _ Himage) as
            (rho0 & pi0 & Hposs & -> & ->). apply TMap.gss.
      - unfold G. split.
        + intros observer Hneq.
          apply token_equiv_rely. eapply token_equiv_image_foreign. intro pi.
          unfold atomic_tokens. repeat rewrite TMap.gso by congruence.
          reflexivity.
        + split.
          * intros observer Hneq.
            eapply pool_local_equiv_image_foreign. intro rho.
            destruct rho; reflexivity.
          * split.
            -- intros observer causal_loc bound Hneq Hcausal rho pi Himage.
               destruct (ac_image_elim _ _ _ _ _ _ Himage) as
                 (rho0 & pi0 & Hposs & -> & ->).
               destruct (Hcausal _ _ Hposs) as
                 (p & -> & Hpending_pool & Hbefore).
               exists p. repeat split; auto.
            -- split; [intros observer Hneq; reflexivity|].
               split; [intros observer Hneq; reflexivity|]. split.
               ++ intros observer Hneq done candidate Hview.
                  unfold candidate_view in *.
                  destruct Hview as
                    (p & pi & N & Hposs & Htoken & Hsnapshot & Hvalue &
                      Hdone & Hstatus & Hsafe).
                  exists p,
                    (atomic_tokens actor (lpool_tryRemove owner loc) false pi), N.
                  repeat split.
                  ** change (ac_image_prop Delta
                       (tryRemove_rho owner loc false)
                       (atomic_tokens actor (lpool_tryRemove owner loc) false)
                       Hsteps
                       (tryRemove_rho owner loc false (LPReady p))
                       (atomic_tokens actor
                         (lpool_tryRemove owner loc) false pi)).
                     constructor. exact Hposs.
                  ** unfold atomic_tokens. repeat rewrite TMap.gso by congruence.
                     exact Htoken.
                  ** exact Hsnapshot.
                  ** exact Hvalue.
                  ** exact Hdone.
                  ** exact Hstatus.
                  ** exact Hsafe.
               ++ split.
                  ** intros observer Hneq row saved Hview.
                     unfold row_snapshot_view in *.
                     destruct Hview as
                       (p & pi & N & Hposs & Htoken & Hsnapshot &
                         Hsaved & Hlive_saved & Horder_saved).
                     exists p,
                       (atomic_tokens actor
                         (lpool_tryRemove owner loc) false pi), N.
                     repeat split; try assumption.
                     --- change (ac_image_prop Delta
                           (tryRemove_rho owner loc false)
                           (atomic_tokens actor
                             (lpool_tryRemove owner loc) false)
                           Hsteps
                           (tryRemove_rho owner loc false (LPReady p))
                           (atomic_tokens actor
                             (lpool_tryRemove owner loc) false pi)).
                         constructor. exact Hposs.
                     --- unfold atomic_tokens.
                         repeat rewrite TMap.gso by congruence. exact Htoken.
                  ** split.
                     --- apply array_evolves_same_array. reflexivity.
                     --- split; [simpl; lia|].
                         split.
                         ++++ intros observer Hneq done candidate row saved Hview.
                         unfold candidate_row_view in *.
                         destruct Hview as
                           (p & pi & N & Hposs & Htoken & Hsnapshot & Hvalue &
                             Hdone & Hstatus & Hcovered & Horder & Hsafe).
                         exists p,
                           (atomic_tokens actor
                             (lpool_tryRemove owner loc) false pi), N.
                         repeat split; try assumption.
                         ***** change (ac_image_prop Delta
                               (tryRemove_rho owner loc false)
                               (atomic_tokens actor
                                 (lpool_tryRemove owner loc) false)
                               Hsteps
                               (tryRemove_rho owner loc false (LPReady p))
                               (atomic_tokens actor
                                 (lpool_tryRemove owner loc) false pi)).
                              constructor. exact Hposs.
                         ***** unfold atomic_tokens.
                              repeat rewrite TMap.gso by congruence.
                              exact Htoken.
                         ++++ split.
                              ***** intros observer Hneq progress start0 Hinside
                                      Hfallback Hsession_all Hcuts n value Hlive Hvalue
                                      Hnotignored.
                                    unfold concrete_array, array_payload in *.
                                    destruct (Hcuts n value Hlive Hvalue Hnotignored)
                                      as (p & pi & N & Hposs & Htoken & Hsnapshot &
                                        Hnode_value & Hmember & Hcut).
                                    exists p,
                                      (atomic_tokens actor
                                        (lpool_tryRemove owner loc) false pi), N.
                                    repeat split; try assumption.
                                    ------ change (ac_image_prop Delta
                                          (tryRemove_rho owner loc false)
                                          (atomic_tokens actor
                                            (lpool_tryRemove owner loc) false)
                                          Hsteps
                                          (tryRemove_rho owner loc false
                                            (LPReady p))
                                          (atomic_tokens actor
                                            (lpool_tryRemove owner loc) false pi)).
                                         constructor. exact Hposs.
                                    ------ unfold atomic_tokens.
                                         repeat rewrite TMap.gso by congruence.
                                         exact Htoken.
                              ***** split.
                                    ------ unfold garbage_evolves,
                                           concrete_array, array_payload. simpl.
                                           firstorder.
                                    ------ split.
                                           { unfold intervals_evolve,
                                               concrete_array, array_payload.
                                             simpl. firstorder. }
                                           { intros observer Hneq.
                                             apply session_equiv_image_foreign.
                                             intro rho. destruct rho; reflexivity. }
    Qed.

    Definition TryRemoveSafe actor owner loc : assertion :=
      fun w => Active actor (lpool_tryRemove owner loc) w /\
        AssertionsSet.A.ANoError
          (Build_ThreadEvent actor
            (InvEv (inl (array_tryRemove owner loc)))) w.

    Lemma tryRemove_safe_or_error actor owner loc w :
      Active actor (lpool_tryRemove owner loc) w ->
      TryRemoveSafe actor owner loc w \/ AssertionsSet.APError w.
    Proof.
      intros Hactive.
      destruct (classic (AssertionsSet.A.ANoError
        (Build_ThreadEvent actor
          (InvEv (inl (array_tryRemove owner loc)))) w))
        as [Hsafe|Hunsafe].
      - left. split; assumption.
      - right. apply NNPP in Hunsafe.
        destruct w as [[control tss] Delta].
        destruct Hactive as [HI Hlin].
        destruct (ac_nonempty Delta) as (rho & pi & Hposs).
        econstructor; [exact Hposs|].
        apply rt_step. eapply ps_error.
        + simpl in Hunsafe.
          destruct HI as [_ [Hall _]].
          destruct (Hall _ _ Hposs) as
            (p & -> & Hpool & Hprotocol & Htimestamp & Hsession).
          destruct Hpool as (Hvertices & Hedges & Hedgevertices & Hgarbage &
            Hpending & Hsnapshots & Hrows).
          inversion Hunsafe; subst.
          * eapply error_actor_outside; [eassumption|reflexivity].
          * eapply error_tryRemove_owner_outside; [eassumption|reflexivity].
          * eapply error_tryRemove_undefined; [|reflexivity].
            unfold is_vertex, array_vertex in *.
            intro Hvertex. rewrite Hvertices in Hvertex.
            match goal with
            | Hundefined : ~ (as_values _ _ <> None) |- False =>
                exact (Hundefined Hvertex)
            | Hnone : as_values _ _ = None |- False =>
                apply Hvertex; exact Hnone
            end.
        + exact (Hlin _ _ Hposs).
    Qed.

    Lemma tryRemove_inv_update_safe actor owner loc :
      AssertionsSet.PUpdate (G actor)
        (Build_ThreadEvent actor
          (InvEv (inl (array_tryRemove owner loc))))
        (TryRemoveSafe actor owner loc)
        (Active actor (lpool_tryRemove owner loc)).
    Proof.
      intros sigma Delta [Hactive _].
      eapply tryRemove_inv_preserves_active. exact Hactive.
    Qed.

    Lemma tryRemove_method_triple actor owner loc :
      SetLogic.HTripleProvable (R actor) (G actor) I actor
        (Active actor (lpool_tryRemove owner loc))
        (tryRemove_impl D owner loc actor)
        (fun ret => Completed actor (lpool_tryRemove owner loc) ret).
    Proof.
      eapply SetLogic.provable_perror with
        (P' := TryRemoveSafe actor owner loc).
      - intros w Hactive. eapply tryRemove_safe_or_error; eauto.
      - unfold tryRemove_impl.
        eapply SetLogic.provable_vis_safe with
          (P' := Active actor (lpool_tryRemove owner loc))
          (Q' := fun removed =>
            Completed actor (lpool_tryRemove owner loc) removed).
        + intros w [_ Hsafe]. exact Hsafe.
        + apply active_entails_I.
        + intros. apply completed_entails_I.
        + apply active_stable. intros ?; discriminate.
        + intros. apply completed_stable.
        + apply tryRemove_inv_update_safe.
        + intros [|]; [apply tryRemove_true_res_update|
            apply tryRemove_false_res_update].
        + intros removed. eapply SetLogic.provable_ret_safe.
          * apply ImplRefl.
          * apply completed_entails_I.
          * apply completed_stable.
    Qed.

    (** Push phases.  The interval token is universal in every phase; the
        returned timestamp bound is the only method-local fact needed after
        [newTS]. *)
    Definition PushActor actor (v : A) : assertion :=
      fun w => Active actor (lpool_push v) w /\
        ThreadDomain.contains D actor.

    Definition PushLinearizing actor (v : A) loc : assertion :=
      fun w => I w /\ actor ↦∀•(lpool_push v) w /\
        ThreadDomain.contains D actor /\
        forall local,
          pool_local_view actor (SetPossState.Δ w) local ->
          fst local = Some loc.

    Definition PushTimestamped actor (v : A) loc lower upper : assertion :=
      fun w => PushLinearizing actor v loc w /\
        lower <= upper /\
        S upper <= ts_clock
          (concrete_timestamp (SetPossState.σ w)) /\
        TMap.find actor
          (ts_pending (concrete_timestamp (SetPossState.σ w))) = None /\
        push_causal actor loc lower w.

    Lemma push_linearizing_entails_I actor v loc :
      ⊨ PushLinearizing actor v loc ==>> I.
    Proof. intros w [HI [Hlin [Hactor Hloc]]]. exact HI. Qed.

    Lemma push_linearizing_stable actor v loc :
      AssertionsSet.A.Stable (R actor) I (PushLinearizing actor v loc).
    Proof.
      unfold AssertionsSet.A.Stable, AssertionsSet.A.ComposeA,
        PushLinearizing, R.
      intros w
        [[pre [[HI [Hlin [Hactor Hloc]]]
          [Hequiv [Hlocal [Hcausal [Harray_local [Hpending
            [Hcandidate [Hevolve Hclock]]]]]]]]] HI'].
      split; [exact HI'|]. split; [|split].
      - unfold ALin in *.
        eapply token_rely_ALin_non_getTop_inv; eauto; intros ?; discriminate.
      - exact Hactor.
      - intros local Hview.
        destruct (proj2 Hlocal local Hview) as
          (old_local & Hold & Hpending_eq).
        rewrite <- Hpending_eq. now apply Hloc.
    Qed.

    Lemma push_timestamped_entails_I actor v loc lower upper :
      ⊨ PushTimestamped actor v loc lower upper ==>> I.
    Proof.
      intros w
        [[HI [Hlin [Hactor Hloc]]]
          [Hwf_ts [Hbound [Hnone Hpush_causal]]]].
      exact HI.
    Qed.

    Lemma push_timestamped_stable actor v loc lower upper :
      AssertionsSet.A.Stable (R actor) I
        (PushTimestamped actor v loc lower upper).
    Proof.
      unfold AssertionsSet.A.Stable, AssertionsSet.A.ComposeA,
        PushTimestamped, PushLinearizing, R.
      intros w
        [[pre [[[HI [Hlin [Hactor Hloc]]]
          [Hwf_ts [Hbound [Hnone Hpush_causal]]]]
          [Hequiv [Hlocal [Hcausal [Harray_local [Hpending
            [Hcandidate [Hevolve Hclock]]]]]]]]] HI'].
      split.
      - split; [exact HI'|]. split; [|split].
        + unfold ALin in *.
          eapply token_rely_ALin_non_getTop_inv; eauto; intros ?; discriminate.
        + exact Hactor.
        + intros local Hview.
          destruct (proj2 Hlocal local Hview) as
            (old_local & Hold & Hpending_eq).
          rewrite <- Hpending_eq. now apply Hloc.
      - split; [exact Hwf_ts|]. split.
        + simpl in *. lia.
        + split.
          * simpl in *. rewrite <- Hpending. exact Hnone.
          * eapply Hcausal. exact Hpush_causal.
    Qed.

    Definition array_insert_response_addr
        (ev : @ThreadEvent (@ESPListArray A)) : option Addr :=
      match te_ev ev with
      | ResEv (array_insert _) loc => Some loc
      | _ => None
      end.

    Definition array_insert_inv_value
        (ev : @ThreadEvent (@ESPListArray A)) : option A :=
      match te_ev ev with
      | InvEv (array_insert v) => Some v
      | _ => None
      end.

    Lemma array_insert_inv_shape actor (v : A) control control' :
      @StepSPListArray A D
        (Build_ThreadEvent actor (InvEv (array_insert v)))
        control control' ->
      exists a,
        control = ArrayReady a /\
        control' = ArrayAtomicPending a actor (array_insert v) /\
        ThreadDomain.contains D actor.
    Proof.
      intro Hstep. remember (Build_ThreadEvent actor
        (InvEv (array_insert v))) as ev eqn:Hev in Hstep.
      inversion Hstep.
      all: match goal with
        | Hctor : ?remembered = ?rhs,
          Htarget : ?remembered = ?target |- _ =>
            let Hevent := fresh "Hevent" in
            pose proof (eq_trans (eq_sym Htarget) Hctor) as Hevent;
            let Hresult := fresh "Hresult" in
            pose proof (f_equal array_insert_inv_value Hevent) as Hresult;
            cbv [array_insert_inv_value] in Hresult;
            first [discriminate Hresult |
              dependent destruction Hevent;
              eexists; split; [reflexivity|]; split;
              [reflexivity|eassumption]]
        end.
    Qed.

    Lemma array_insert_res_shape actor (v : A) loc control control' :
      @StepSPListArray A D
        (Build_ThreadEvent actor (ResEv (array_insert v) loc))
        control control' ->
      exists a,
        control = ArrayAtomicPending a actor (array_insert v) /\
        control' = ArrayReady (insert_node actor loc v a) /\
        array_fresh a (pair actor loc).
    Proof.
      intro Hstep. remember (Build_ThreadEvent actor
        (ResEv (array_insert v) loc)) as ev eqn:Hev in Hstep.
      inversion Hstep.
      all: match goal with
        | Hctor : ?remembered = ?rhs,
          Htarget : ?remembered = ?target |- _ =>
            let Hevent := fresh "Hevent" in
            pose proof (eq_trans (eq_sym Htarget) Hctor) as Hevent;
            let Hresult := fresh "Hresult" in
            pose proof (f_equal array_insert_response_addr Hevent) as Hresult;
            cbv [array_insert_response_addr] in Hresult;
            first [discriminate Hresult |
              dependent destruction Hevent;
              eexists; split; [reflexivity|]; split;
              [reflexivity|eassumption]]
        end.

    Qed.

    Definition array_setTS_response_info
        (ev : @ThreadEvent (@ESPListArray A)) : option (prod Addr TS) :=
      match te_ev ev with
      | ResEv (array_setTS loc ts) _ => Some (pair loc ts)
      | _ => None
      end.

    Definition array_setTS_inv_info
        (ev : @ThreadEvent (@ESPListArray A)) : option (prod Addr TS) :=
      match te_ev ev with
      | InvEv (array_setTS loc ts) => Some (pair loc ts)
      | _ => None
      end.

    Lemma array_setTS_inv_shape actor loc ts control control' :
      @StepSPListArray A D
        (Build_ThreadEvent actor (InvEv (array_setTS loc ts)))
        control control' ->
      exists a,
        control = ArrayReady a /\
        control' = ArrayAtomicPending a actor (array_setTS loc ts) /\
        ThreadDomain.contains D actor /\
        array_vertex a (pair actor loc).
    Proof.
      intro Hstep. remember (Build_ThreadEvent actor
        (InvEv (array_setTS loc ts))) as ev eqn:Hev in Hstep.
      inversion Hstep.
      all: match goal with
        | Hctor : ?remembered = ?rhs,
          Htarget : ?remembered = ?target |- _ =>
            let Hevent := fresh "Hevent" in
            pose proof (eq_trans (eq_sym Htarget) Hctor) as Hevent;
            let Hresult := fresh "Hresult" in
            pose proof (f_equal array_setTS_inv_info Hevent) as Hresult;
            cbv [array_setTS_inv_info] in Hresult;
            first [discriminate Hresult |
              dependent destruction Hevent;
              eexists; split; [reflexivity|]; split; [reflexivity|];
              split; eassumption]
        end.
    Qed.

    Lemma array_setTS_res_shape actor loc ts control control' :
      @StepSPListArray A D
        (Build_ThreadEvent actor (ResEv (array_setTS loc ts) tt))
        control control' ->
      exists a,
        control = ArrayAtomicPending a actor (array_setTS loc ts) /\
        control' = ArrayReady (set_node_timestamp actor loc ts a).
    Proof.
      intro Hstep. remember (Build_ThreadEvent actor
        (ResEv (array_setTS loc ts) tt)) as ev eqn:Hev in Hstep.
      inversion Hstep.
      all: match goal with
        | Hctor : ?remembered = ?rhs,
          Htarget : ?remembered = ?target |- _ =>
            let Hevent := fresh "Hevent" in
            pose proof (eq_trans (eq_sym Htarget) Hctor) as Hevent;
            let Hresult := fresh "Hresult" in
            pose proof (f_equal array_setTS_response_info Hevent) as Hresult;
            cbv [array_setTS_response_info] in Hresult;
            first [discriminate Hresult |
              dependent destruction Hevent;
              eexists; split; [reflexivity|reflexivity]]
        end.
    Qed.

    Lemma timestamp_pending_edges_start_push
        (a : @SPListArrayState A) (tss : TimestampState)
        (p : @ListPoolState A) actor loc (v : A) :
      pool_represents a p ->
      timestamp_pending_edges
        (pair (ArrayAtomicPending a actor (array_insert v)) tss) p ->
      TMap.find actor (lp_pending_pushes p) = None ->
      array_fresh a (pair actor loc) ->
      (forall N0, TMap.find actor (lp_pop_starts p) = Some N0 ->
        TMap.find actor (lp_pop_ts p) <> None) ->
      timestamp_pending_edges
        (pair (ArrayReady (insert_node actor loc v a)) tss)
        (start_push actor loc v p).
    Proof.
      intros Hpool [Hpending_domain Hbefore] Hnone Hfresh Hno_session.
      destruct Hpool as (Hvertices & Hedges & Hedgevertices & Hgarbage &
        Hpending & Hsnapshots & Hrows).
      unfold timestamp_pending_edges, concrete_timestamp, concrete_array,
        array_payload in *. simpl in *.
      assert (Htimestamp_none : forall lower,
        TMap.find actor (ts_pending tss) <> Some lower).
      { intros lower Hfind.
        destruct (Hpending_domain _ _ Hfind) as
          [[old_loc Hold]|[Hts [N0 Hstarts]]].
        - rewrite Hnone in Hold. discriminate.
        - exact (Hno_session N0 Hstarts Hts). }
      split.
      - intros owner lower Hfind.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + exfalso. eapply Htimestamp_none; eauto.
        + destruct (Hpending_domain _ _ Hfind) as [[old_loc Hold]|Hsess].
          * left. exists old_loc. simpl. rewrite TMap.gso by exact Hneq.
            exact Hold.
          * right. simpl. exact Hsess.
      - intros owner lower old_loc Hfind Hpool_pending.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + exfalso. eapply Htimestamp_none; eauto.
        + simpl in Hpool_pending. rewrite TMap.gso in Hpool_pending
            by exact Hneq.
          specialize (Hbefore owner lower old_loc Hfind Hpool_pending).
          intros older Hedge. simpl in Hedge.
          destruct Hedge as [Holdedge | [Hnewer _]].
          2:{ exfalso. apply Hneq. inversion Hnewer. reflexivity. }
          destruct (Hbefore _ Holdedge) as
            (old_lower & old_upper & Htimestamp & Hlt).
          exists old_lower, old_upper. split; [|exact Hlt].
          destruct (node_eq_dec (pair actor loc) older) as [Heq|Holder].
          * subst older.
            destruct (Hedgevertices _ _ Holdedge) as [_ Hvertex].
            unfold is_vertex in Hvertex. rewrite Hvertices in Hvertex.
            rewrite (proj1 Hfresh) in Hvertex. contradiction.
          * rewrite insert_preserves_old_timestamp by congruence.
            exact Htimestamp.
    Qed.

    Lemma outgoing_before_start_push_foreign
        (a : @SPListArrayState A) (p : @ListPoolState A)
        actor loc (v : A) observer observer_loc lower :
      pool_represents a p -> array_fresh a (pair actor loc) ->
      actor <> observer ->
      outgoing_before a p (pair observer observer_loc) lower ->
      outgoing_before (insert_node actor loc v a)
        (start_push actor loc v p) (pair observer observer_loc) lower.
    Proof.
      intros (Hvertices & Hedges & Hedgevertices & Hgarbage & Hpending &
        Hsnapshots & Hrows) Hfresh Hneq Hbefore older Hedge.
      simpl in Hedge. destruct Hedge as [Holdedge | [Hnewer _]].
      - destruct (Hbefore _ Holdedge) as
          (old_lower & old_upper & Htimestamp & Hlt).
        exists old_lower, old_upper. split; [|exact Hlt].
        destruct (node_eq_dec (pair actor loc) older) as [Heq|Holder].
        + subst older. destruct (Hedgevertices _ _ Holdedge) as [_ Hvertex].
          unfold is_vertex in Hvertex. rewrite Hvertices in Hvertex.
          rewrite (proj1 Hfresh) in Hvertex. contradiction.
        + rewrite insert_preserves_old_timestamp by congruence.
          exact Htimestamp.
      - exfalso. apply Hneq. congruence.
    Qed.

    Definition push_start_rho actor loc (v : A)
        (rho : abstract_state) : abstract_state :=
      match rho with
      | LPReady p => LPReady (start_push actor loc v p)
      | LPAtomicPending p pending_actor op =>
          LPAtomicPending p pending_actor op
      end.

    Lemma pool_shared_eq_start_push_compat actor loc (v : A) p q :
      pool_shared_eq p q ->
      pool_shared_eq
        (start_push actor loc v p) (start_push actor loc v q).
    Proof.
      intros (Hvertices & Hedges & Hpending & Hgarbage & Hpop_starts & Hpop_ts).
      unfold pool_shared_eq, start_push; simpl. repeat split.
      - now rewrite Hvertices.
      - apply functional_extensionality; intro newer.
        apply functional_extensionality; intro older.
        unfold is_vertex, is_pending.
        now rewrite Hedges, Hvertices, Hpending.
      - now rewrite Hpending.
      - exact Hgarbage.
      - exact Hpop_starts.
      - exact Hpop_ts.
    Qed.

    Lemma start_push_snapshot_find actor loc (v : A) observer p :
      TMap.find observer (lp_snapshots (start_push actor loc v p)) =
        TMap.find observer (lp_snapshots p).
    Proof. reflexivity. Qed.

    Lemma push_insert_inv_update actor (v : A) :
      AssertionsSet.PUpdate (G actor)
        (Build_ThreadEvent actor (InvEv (inl (array_insert v))))
        (Active actor (lpool_push v))
        (PushActor actor v).
    Proof.
      intros [control tss] Delta [HI Hlin] [control' tss'] Hstep.
      simpl in Hstep. destruct Hstep as [Harray ->].
      destruct (array_insert_inv_shape actor v _ _ Harray)
        as (a & -> & -> & Hactor).
      exists Delta. split; [apply ac_steps_refl|]. split.
      - split; [split; assumption|exact Hactor].
      - unfold G. split.
        + intros observer Hneq. apply token_rely_refl.
        + split; [intros observer Hneq; apply pool_local_equiv_refl|].
          split.
          * intros observer causal_loc lower Hneq Hcausal. exact Hcausal.
          * split; [intros observer Hneq; reflexivity|].
            split; [intros observer Hneq; reflexivity|]. split.
            -- intros observer Hneq. apply candidate_views_preserved_refl.
            -- split.
               ++ intros observer Hneq.
                  apply row_snapshot_views_preserved_refl.
               ++ split.
                  ** apply array_evolves_same_array. reflexivity.
                  ** split; [simpl; lia|].
                     split.
                     --- intros observer Hneq.
                         apply candidate_row_views_preserved_refl.
                     --- split.
                         +++ intros observer Hneq.
                             unfold node_cuts_preserved, concrete_array,
                               array_payload. simpl. firstorder.
                         +++ split.
                             { unfold garbage_evolves, concrete_array,
                                 array_payload. simpl. firstorder. }
                             split.
                             { unfold intervals_evolve, concrete_array,
                                 array_payload. simpl. firstorder. }
                             intros observer Hneq. apply session_equiv_refl.
    Qed.

    Lemma push_insert_res_update actor (v : A) loc :
      AssertionsSet.PUpdate (G actor)
        (Build_ThreadEvent actor (ResEv (inl (array_insert v)) loc))
        (PushActor actor v)
        (PushLinearizing actor v loc).
    Proof.
      intros [control tss] Delta [[HIpre Hlin] Hactor]
        [control' tss'] Hstep.
      simpl in Hstep. destruct Hstep as [Harray ->].
      destruct (array_insert_res_shape actor v loc _ _ Harray)
        as (a & -> & -> & Hfresh).
      destruct HIpre as [Hwf [Hall [Hrect Hcounter]]].
      assert (Hsteps : forall rho pi, Delta rho pi ->
        poss_steps (PossOk rho pi)
          (PossOk (push_start_rho actor loc v rho)
            (TMap.add actor (ls_lini (lpool_push v)) pi))).
      { intros rho pi Hposs.
        destruct (Hall _ _ Hposs) as
          (p & -> & Hpool & Hprotocol & Htimestamp & Hsession).
        assert (Hnone :
          TMap.find actor (lp_pending_pushes p) = None).
        { destruct (TMap.find actor (lp_pending_pushes p))
            as [old_loc|] eqn:Hfind; [|reflexivity].
          destruct (proj1 Hprotocol _ _ Hfind) as [old_v Htoken].
          rewrite (Hlin _ _ Hposs) in Htoken.
          dependent destruction Htoken. }
        apply rt_step. eapply ps_inv.
        - eapply step_push_inv.
          + exact Hnone.
          + eapply pool_fresh_of_array_fresh; eauto.
          + reflexivity.
        - exact (Hlin _ _ Hposs). }
      set (Delta0 := ac_image Delta (push_start_rho actor loc v)
        (fun pi => TMap.add actor (ls_lini (lpool_push v)) pi) Hsteps).
      set (Delta' := ac_push_saturate (ThreadDomain.threads D) Delta0).
      assert (HI0 : I
        (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          (pair (ArrayReady (insert_node actor loc v a)) tss') Delta0)).
      { split.
        - destruct Hwf as [Hvalid [Hstamped [Hdefined Hstructural]]].
          split; [exact Hvalid|]. split.
          + eapply stamped_before_clock_insert. exact Hstamped.
          + split.
            * eapply timestamp_defined_insert; eauto.
            * eapply array_structural_wf_insert; eauto.
        - split.
          + intros rho pi Himage. unfold Delta0 in Himage.
            destruct (ac_image_elim _ _ _ _ _ _ Himage) as
              (rho0 & pi0 & Hposs & -> & ->).
            destruct (Hall _ _ Hposs) as
              (p & -> & Hpool & Hprotocol & Htimestamp & Hsession).
            assert (Hnone : TMap.find actor (lp_pending_pushes p) = None).
            { destruct (TMap.find actor (lp_pending_pushes p))
                as [old_loc|] eqn:Hfind; [|reflexivity].
              destruct (proj1 Hprotocol _ _ Hfind) as [old_v Htoken].
              rewrite (Hlin _ _ Hposs) in Htoken.
              dependent destruction Htoken. }
            exists (start_push actor loc v p). split; [reflexivity|]. split.
            * eapply pool_represents_start_push; eauto.
              exact (proj1 (proj2 (proj2 Hwf))).
              exact (proj2 (proj2 (proj2 Hwf))).
            * split.
              -- eapply pool_protocol_start_push; eauto.
              -- split.
                 ++ eapply timestamp_pending_edges_start_push;
                      [exact Hpool|exact Htimestamp|exact Hnone|exact Hfresh|].
                    eapply no_pending_session_of_token;
                      [exact Hprotocol|exact (Hlin _ _ Hposs)|discriminate].
                 ++ refine (session_represents_evolve _ _ _ _ _ _ _ Hsession).
                    ** intros n lo hi Hts.
                       apply interval_timestamps_preserved_insert;
                         [exact (proj1 (proj2 (proj2 Hwf)))|exact Hfresh|].
                       exact Hts.
                    ** intros owner N0 _ _. reflexivity.
          + split.
            * unfold Delta0.
              eapply possibility_rectangular_add_image.
              -- intro p. reflexivity.
              -- intros rho q Hready. destruct rho; simpl in Hready.
                 ++ inversion Hready. eexists; split; reflexivity.
                 ++ discriminate.
              -- apply pool_shared_eq_start_push_compat.
              -- apply start_push_snapshot_find.
              -- exact Hrect.
            * intros observer saved Hpending.
              change (TMap.find observer (as_pending_counters a) =
                Some saved) in Hpending.
              destruct (Hcounter observer saved Hpending) as
                (rho0 & pi0 & start0 & Hposs & Hfind).
              destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
              -- pose proof (Hlin rho0 pi0 Hposs) as Hlin_actor.
                 pose proof (eq_trans (eq_sym Hlin_actor) Hfind) as Hstate_eq.
                 change (Some (ls_inv (lpool_push v)) =
                   Some (ls_lini (lpool_getTop start0))) in Hstate_eq.
                 discriminate Hstate_eq.
              -- exists (push_start_rho actor loc v rho0),
                   (TMap.add actor (ls_lini (lpool_push v)) pi0), start0. split.
                 ++ unfold Delta0. constructor. exact Hposs.
                 ++ rewrite TMap.gso by congruence. exact Hfind. }
      assert (Hlin0 : forall rho pi, Delta0 rho pi ->
        TMap.find actor pi = Some (ls_lini (lpool_push v))).
      { intros rho pi Himage. unfold Delta0 in Himage.
        destruct (ac_image_elim _ _ _ _ _ _ Himage) as
          (rho0 & pi0 & Hposs & -> & ->). apply TMap.gss. }
      assert (Hlocal0 : forall local,
        pool_local_view actor Delta0 local -> fst local = Some loc).
      { intros local (rho & pi & Himage & Hlocal). unfold Delta0 in Himage.
        destruct (ac_image_elim _ _ _ _ _ _ Himage) as
          (rho0 & pi0 & Hposs & -> & ->).
        destruct (Hall _ _ Hposs) as
          (p & -> & Hpool & Hprotocol & Htimestamp & Hsession).
        unfold pool_local_state, push_start_rho in Hlocal. simpl in Hlocal.
        rewrite TMap.gss in Hlocal. symmetry. exact (f_equal fst Hlocal). }
      assert (Hcausal0 : forall observer causal_loc bound,
        actor <> observer ->
        push_causal observer causal_loc bound
          (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
            (pair (ArrayAtomicPending a actor (array_insert v)) tss') Delta) ->
        push_causal observer causal_loc bound
          (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
            (pair (ArrayReady (insert_node actor loc v a)) tss') Delta0)).
      { intros observer causal_loc bound Hneq Hcausal rho pi Himage.
        unfold Delta0 in Himage.
        destruct (ac_image_elim _ _ _ _ _ _ Himage) as
          (rho0 & pi0 & Hposs & -> & ->).
        destruct (Hall _ _ Hposs) as
          (p & -> & Hpool & Hprotocol & Htimestamp & Hsession).
        destruct (Hcausal _ _ Hposs) as
          (p0 & Heq & Hpending_pool & Hbefore).
        inversion Heq; subst p0. exists (start_push actor loc v p).
        split; [reflexivity|]. split.
        - simpl. rewrite TMap.gso by congruence. exact Hpending_pool.
        - eapply outgoing_before_start_push_foreign; eauto. }
      assert (Hcandidate0 : forall observer, actor <> observer ->
        candidate_views_preserved observer Delta Delta0).
      { intros observer Hneq done candidate Hview.
        unfold candidate_view in *.
        destruct Hview as
          (p & pi & N & Hposs & Htoken & Hsnapshot & Hvalue & Hdone & Hstatus &
            Hsafe).
        destruct (Hall _ _ Hposs) as
          (p0 & Heq & Hpool & Hprotocol & Htimestamp & Hsession).
        inversion Heq; subst p0.
        assert (Hpoolfresh : fresh_node p (pair actor loc)).
        { eapply pool_fresh_of_array_fresh; eauto. }
        assert (Hcandidate_neq : pair actor loc <>
          pair (candidate_owner candidate) (candidate_loc candidate)).
        { intro Heqnode. destruct Hpoolfresh as [Hfresh_value _].
          rewrite Heqnode in Hfresh_value. congruence. }
        assert (Hsnapshot_vertex : forall node, N node -> is_vertex p node).
        { intros node Hmember. unfold is_vertex.
          rewrite (proj1 Hpool node).
          eapply (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hpool))))))
            with (actor := observer) (N := N); eauto. }
        exists (start_push actor loc v p),
          (TMap.add actor (ls_lini (lpool_push v)) pi), N.
        repeat split.
        - unfold Delta0. change (ac_image_prop Delta
            (push_start_rho actor loc v)
            (fun pi => TMap.add actor (ls_lini (lpool_push v)) pi)
            Hsteps (push_start_rho actor loc v (LPReady p))
            (TMap.add actor (ls_lini (lpool_push v)) pi)).
          constructor. exact Hposs.
        - rewrite TMap.gso by congruence. exact Htoken.
        - exact Hsnapshot.
        - simpl. rewrite node_update_neq by exact Hcandidate_neq. exact Hvalue.
        - exact Hdone.
        - eapply candidate_status_start_push;
            [exact Hpoolfresh| |exact Hstatus].
          exact Hsnapshot_vertex.
        - eapply candidate_tstop_safe_start_push; eauto. }
      assert (Hrow0 : forall observer, actor <> observer ->
        row_snapshot_views_preserved observer Delta Delta0).
      { intros observer Hneq row saved Hview.
        unfold row_snapshot_view in *.
        destruct Hview as
          (p & pi & N & Hposs & Htoken & Hsnapshot & Hsaved & Hlive & Horder).
        destruct (Hall _ _ Hposs) as
          (p0 & Heqp & Hpool & Hprotocol & Htimestamp & Hsession).
        inversion Heqp; subst p0.
        assert (Hpoolfresh : fresh_node p (pair actor loc)).
        { eapply pool_fresh_of_array_fresh; eauto. }
        assert (Hsnapshot_vertex : forall node, N node -> is_vertex p node).
        { intros node Hmember. unfold is_vertex.
          rewrite (proj1 Hpool node).
          eapply (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hpool))))))
            with (actor := observer) (N := N); eauto. }
        exists (start_push actor loc v p),
          (TMap.add actor (ls_lini (lpool_push v)) pi), N.
        repeat split; try assumption.
        - unfold Delta0. change (ac_image_prop Delta
            (push_start_rho actor loc v)
            (fun pi => TMap.add actor (ls_lini (lpool_push v)) pi)
            Hsteps (push_start_rho actor loc v (LPReady p))
            (TMap.add actor (ls_lini (lpool_push v)) pi)).
          constructor. exact Hposs.
        - rewrite TMap.gso by congruence. exact Htoken.
        - intros newer older Hnewer_member Holder_member
              Hnewer_live Holder_live Hedge.
          assert (Hnewer_neq : pair row newer <> pair actor loc).
          { intro Heq. apply (Hsnapshot_vertex _ Hnewer_member).
            rewrite Heq. exact (proj1 Hpoolfresh). }
          assert (Holder_neq : pair row older <> pair actor loc).
          { intro Heq. apply (Hsnapshot_vertex _ Holder_member).
            rewrite Heq. exact (proj1 Hpoolfresh). }
          simpl in Hedge. destruct Hedge as [Hold|[Heq _]].
          * apply Horder; try assumption.
          * exfalso. apply Hnewer_neq. exact Heq.
      }
      assert (Hcandidate_row0 : forall observer, actor <> observer ->
        candidate_row_views_preserved observer Delta Delta0).
      { intros observer Hneq done candidate row saved Hview.
        unfold candidate_row_view in *.
        destruct Hview as
          (p & pi & N & Hposs & Htoken & Hsnapshot & Hvalue & Hdone &
            Hstatus & Hcovered & Horder & Hsafe).
        destruct (Hall _ _ Hposs) as
          (p0 & Heqp & Hpool & Hprotocol & Htimestamp & Hsession).
        inversion Heqp; subst p0.
        assert (Hpoolfresh : fresh_node p (pair actor loc)).
        { eapply pool_fresh_of_array_fresh; eauto. }
        assert (Hsnapshot_vertex : forall node, N node -> is_vertex p node).
        { intros node Hmember. unfold is_vertex.
          rewrite (proj1 Hpool node).
          eapply (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hpool))))))
            with (actor := observer) (N := N); eauto. }
        assert (Hcandidate_neq : pair actor loc <>
          pair (candidate_owner candidate) (candidate_loc candidate)).
        { intro Heqnode. destruct Hpoolfresh as [Hfresh_value _].
          rewrite Heqnode in Hfresh_value. congruence. }
        exists (start_push actor loc v p),
          (TMap.add actor (ls_lini (lpool_push v)) pi), N.
        repeat split.
        - unfold Delta0. change (ac_image_prop Delta
            (push_start_rho actor loc v)
            (fun pi => TMap.add actor (ls_lini (lpool_push v)) pi)
            Hsteps (push_start_rho actor loc v (LPReady p))
            (TMap.add actor (ls_lini (lpool_push v)) pi)).
          constructor. exact Hposs.
        - rewrite TMap.gso by congruence. exact Htoken.
        - exact Hsnapshot.
        - simpl. rewrite node_update_neq by exact Hcandidate_neq. exact Hvalue.
        - exact Hdone.
        - eapply candidate_status_start_push;
            [exact Hpoolfresh| |exact Hstatus].
          exact Hsnapshot_vertex.
        - exact Hcovered.
        - intros newer older Hnewer_member Holder_member
              Hnewer_live Holder_live Hedge.
          assert (Hnewer_neq : pair row newer <> pair actor loc).
          { intro Heq. apply (Hsnapshot_vertex _ Hnewer_member).
            rewrite Heq. exact (proj1 Hpoolfresh). }
          simpl in Hedge. destruct Hedge as [Hold|[Heq _]].
          + apply Horder; try assumption.
          + exfalso. apply Hnewer_neq. exact Heq.
        - eapply candidate_tstop_safe_start_push; eauto.
      }
      exists Delta'. split.
      - unfold Delta'. eapply ac_steps_subset_trans.
        + unfold Delta0. apply ac_image_subset_steps.
        + apply ac_push_saturate_subset_steps.
      - split.
        + unfold PushLinearizing. split.
          * unfold Delta'. now apply I_push_saturate.
          * split; [|split].
            -- unfold ALin. eapply token_rely_ALin_non_getTop_inv.
               ++ unfold Delta'. apply token_rely_push_saturate.
               ++ discriminate.
               ++ exact Hlin0.
            -- exact Hactor.
            -- intros local Hview.
               destruct (proj2
                 (pool_local_equiv_push_saturate actor
                   (ThreadDomain.threads D) Delta0) _ Hview)
                 as (local0 & Hview0 & Hfst).
               rewrite <- Hfst. now apply Hlocal0.
        + unfold G. split.
          * intros observer Hneq. eapply token_rely_trans.
            -- apply token_equiv_rely.
               eapply token_equiv_image_foreign. intro pi.
               rewrite TMap.gso by exact (not_eq_sym Hneq). reflexivity.
            -- unfold Delta'. apply token_rely_push_saturate.
          * split.
            -- intros observer Hneq. eapply pool_local_equiv_push_trans.
               ++ unfold Delta0.
                  eapply (pool_local_equiv_image_foreign observer Delta
                    (push_start_rho actor loc v)
                    (fun pi => TMap.add actor (ls_lini (lpool_push v)) pi)
                    Hsteps). intro rho.
                  destruct rho; simpl;
                    try (rewrite TMap.gso by exact (not_eq_sym Hneq));
                    reflexivity.
               ++ unfold Delta'. apply pool_local_equiv_push_saturate.
            -- split.
               ++ intros observer causal_loc bound Hneq Hcausal.
                  unfold Delta'. apply push_causal_push_saturate.
                  now apply Hcausal0.
               ++ split; [intros observer Hneq; reflexivity|].
                  split; [intros observer Hneq; reflexivity|]. split.
                  ** intros observer Hneq.
                     intros done candidate Hview.
                     unfold Delta'.
                     apply candidate_views_preserved_push_saturate.
                     now apply Hcandidate0.
                  ** split.
                     --- intros observer Hneq row saved Hview.
                         unfold Delta'.
                         apply row_snapshot_views_preserved_push_saturate.
                         now apply Hrow0.
                     --- split.
                         +++ apply array_evolves_insert.
                         +++ split; [simpl; lia|].
                             split.
                             *** intros observer Hneq.
                                 unfold Delta'.
                                 eapply candidate_row_views_preserved_trans.
                                 ---- now apply Hcandidate_row0.
                                 ---- eapply candidate_row_views_preserved_mono.
                                      intros rho pi Hposs.
                                      now apply ac_push_saturate_keep.
                             *** split.
                                 ---- intros observer Hneq progress start0 Hinside
                                        Hfallback Hsession_all Hcuts n value Hlive Hvalue
                                        Hnotignored.
                                      change (array_live
                                        (insert_node actor loc v a) n) in Hlive.
                                      change (as_values
                                        (insert_node actor loc v a) n =
                                        Some value) in Hvalue.
                                      destruct (node_eq_dec n (pair actor loc))
                                        as [->|Hnode_neq].
                                      ++++ rewrite insert_value in Hvalue.
                                           inversion Hvalue; subst value.
                                           destruct Hfallback as
                                             (rho & pi & Hposs & Htoken).
                                           destruct (Hall _ _ Hposs) as
                                             (p & -> & Hpool & Hprotocol &
                                               Htimestamp & Hsession).
                                           assert (Hpoolfresh : fresh_node p
                                             (pair actor loc)).
                                           { eapply pool_fresh_of_array_fresh;
                                               eauto. }
                                           assert (Hsnapshot_none :
                                             TMap.find observer
                                               (lp_snapshots p) = None).
                                           { destruct (TMap.find observer
                                               (lp_snapshots p)) as [N|]
                                               eqn:Hfind; [|reflexivity].
                                             destruct
                                               (proj1 (proj2 Hprotocol)
                                                 observer N Hfind) as
                                               [start1 Hlinear].
                                             rewrite Htoken in Hlinear.
                                             discriminate. }
                                           exists (start_snapshot observer
                                               (start_push actor loc v p)),
                                             (snapshot_tokens observer start0
                                               (TMap.add actor
                                                 (ls_lini (lpool_push v)) pi)),
                                             (fun node => is_vertex
                                               (start_push actor loc v p) node).
                                           repeat split.
                                           ***** unfold Delta'.
                                                 eapply ac_push_saturate_take.
                                                 ------ exact Hinside.
                                                 ------ unfold Delta0.
                                                      change (ac_image_prop Delta
                                                        (push_start_rho actor loc v)
                                                        (fun pi => TMap.add actor
                                                          (ls_lini (lpool_push v))
                                                          pi)
                                                        Hsteps
                                                        (push_start_rho actor loc v
                                                          (LPReady p))
                                                        (TMap.add actor
                                                          (ls_lini (lpool_push v))
                                                          pi)).
                                                      constructor. exact Hposs.
                                                 ------ rewrite TMap.gso by
                                                       congruence. exact Htoken.
                                                 ------ exact (Hsession_all _ _ Hposs).
                                                 ------ exact Hsnapshot_none.
                                           ***** exists start0. unfold snapshot_tokens.
                                                 apply TMap.gss.
                                           ***** simpl. apply TMap.gss.
                                           ***** simpl. apply node_update_eq.
                                           ***** unfold is_vertex. simpl.
                                                 rewrite node_update_eq.
                                                 discriminate.
                                           ***** intros newer Hnewer Hnewer_live
                                                   Hedge.
                                                 simpl in Hedge.
                                                 destruct Hedge as
                                                   [Hold|[Heq [Htarget_vertex
                                                     Hold_complete]]].
                                                 ------ destruct
                                                     (proj1 (proj2 (proj2 Hpool))
                                                       _ _ Hold) as
                                                     [_ Htarget_vertex].
                                                      exfalso.
                                                      apply Htarget_vertex.
                                                      exact (proj1 Hpoolfresh).
                                                 ------ exfalso.
                                                      apply Htarget_vertex.
                                                      exact (proj1 Hpoolfresh).
                                      ++++ assert (Hold_live : array_live a n).
                                           { destruct Hlive as
                                               [Hvertex Hnotgarbage].
                                             split.
                                             - unfold array_vertex in *.
                                               simpl in Hvertex.
                                               rewrite node_update_neq in Hvertex
                                                 by exact (not_eq_sym Hnode_neq).
                                               exact Hvertex.
                                             - exact Hnotgarbage. }
                                           assert (Hold_value :
                                             as_values a n = Some value).
                                           { rewrite insert_preserves_old_value
                                               in Hvalue by exact Hnode_neq.
                                             exact Hvalue. }
                                           destruct (Hcuts n value Hold_live
                                             Hold_value Hnotignored) as
                                             (p & pi & N & Hposs & Htoken &
                                               Hsnapshot & Hnode_value & Hmember &
                                               Hcut).
                                           destruct (Hall _ _ Hposs) as
                                             (p0 & Heqp & Hpool & Hprotocol &
                                               Htimestamp & Hsession).
                                           inversion Heqp; subst p0.
                                           assert (Hpoolfresh : fresh_node p
                                             (pair actor loc)).
                                           { eapply pool_fresh_of_array_fresh;
                                               eauto. }
                                           assert (Hsnapshot_vertex :
                                             forall node, N node ->
                                               is_vertex p node).
                                           { intros node Hnode.
                                             unfold is_vertex.
                                             rewrite (proj1 Hpool node).
                                             eapply (proj1 (proj2 (proj2 (proj2
                                               (proj2 (proj2 Hpool))))))
                                               with (actor := observer) (N := N);
                                               eauto. }
                                           exists (start_push actor loc v p),
                                             (TMap.add actor
                                               (ls_lini (lpool_push v)) pi), N.
                                           repeat split.
                                           ***** unfold Delta'.
                                                 apply ac_push_saturate_keep.
                                                 unfold Delta0.
                                                 change (ac_image_prop Delta
                                                   (push_start_rho actor loc v)
                                                   (fun pi => TMap.add actor
                                                     (ls_lini (lpool_push v)) pi)
                                                   Hsteps
                                                   (push_start_rho actor loc v
                                                     (LPReady p))
                                                   (TMap.add actor
                                                     (ls_lini (lpool_push v)) pi)).
                                                 constructor. exact Hposs.
                                           ***** rewrite TMap.gso by congruence.
                                                 exact Htoken.
                                           ***** exact Hsnapshot.
                                           ***** simpl. rewrite node_update_neq
                                                   by exact
                                                     (not_eq_sym Hnode_neq).
                                                 exact Hnode_value.
                                           ***** exact Hmember.
                                           ***** intros newer Hnewer Hnewer_live
                                                   Hedge.
                                                 simpl in Hedge.
                                                 destruct Hedge as
                                                   [Hold|[Heq [Hgenerated_vertex
                                                     Hold_complete]]].
                                                 ------ eapply Hcut; eauto.
                                                 ------ subst newer.
                                                      exfalso.
                                                      apply (Hsnapshot_vertex _
                                                        Hnewer).
                                                      exact (proj1 Hpoolfresh).
                                 ---- split.
                                      ***** unfold garbage_evolves,
                                              concrete_array, array_payload.
                                            simpl. firstorder.
                                      ***** split; [|intros observer Hneq;
                                              unfold Delta';
                                              eapply session_equiv_trans;
                                              [|apply session_equiv_push_saturate];
                                              unfold Delta0;
                                              apply session_equiv_image_foreign;
                                              intro rho; destruct rho; reflexivity].
                                            unfold intervals_evolve,
                                              concrete_array, array_payload.
                                            simpl.
                                            split.
                                            ------ intros n ts Htimestamp0.
                                                   exact
                                                     (timestamp_domain_preserved_insert
                                                       actor loc v a
                                                       (proj1 (proj2
                                                         (proj2 Hwf)))
                                                       Hfresh n ts Htimestamp0).
                                            ------ split.
                                                   { intros n lo hi Htimestamp0.
                                                     exact
                                                       (interval_timestamps_preserved_insert
                                                         actor loc v a
                                                         (proj1 (proj2
                                                           (proj2 Hwf)))
                                                         Hfresh n lo hi Htimestamp0). }
                                                   { intros n v0 Hvalue0.
                                                     simpl. unfold node_update.
                                                     match goal with
                                                     | |- context [node_eq_dec ?x ?y] =>
                                                         destruct (node_eq_dec x y)
                                                           as [Heq|Hneq]
                                                     end.
                                                     - exfalso. subst n.
                                                       pose proof (eq_trans
                                                         (eq_sym (proj1 Hfresh))
                                                         Hvalue0) as Hbad.
                                                       discriminate Hbad.
                                                     - exact Hvalue0. }
    Qed.

    Lemma timestamp_pending_edges_start_timestamp control
        (tss : TimestampState) (p : @ListPoolState A) actor loc :
      pool_represents (array_payload control) p ->
      stamped_before_clock (array_payload control) tss ->
      timestamp_pending_edges (pair control tss) p ->
      TMap.find actor (lp_pending_pushes p) = Some loc ->
      timestamp_pending_edges (pair control (start_newTS actor tss)) p.
    Proof.
      intros Hpool Hstamped [Hdomain Hbefore] Hpending_actor.
      unfold timestamp_pending_edges, concrete_timestamp, concrete_array,
        array_payload in *. simpl in *.
      split.
      - intros owner lower Hfind.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite TMap.gss in Hfind. inversion Hfind; subst lower.
          left. exists loc. exact Hpending_actor.
        + rewrite TMap.gso in Hfind by exact Hneq.
          eapply Hdomain; eauto.
      - intros owner lower address Hfind Hpending.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite TMap.gss in Hfind. inversion Hfind; subst lower.
          rewrite Hpending_actor in Hpending. inversion Hpending; subst address.
          eapply pending_push_outgoing_before; eauto.
        + rewrite TMap.gso in Hfind by exact Hneq.
          eapply Hbefore; eauto.
    Qed.

    Lemma timestamp_pending_edges_finish_timestamp control
        (tss : TimestampState) (p : @ListPoolState A) actor upper :
      timestamp_pending_edges (pair control tss) p ->
      timestamp_pending_edges (pair control (finish_newTS actor upper tss)) p.
    Proof.
      intros [Hdomain Hbefore].
      unfold timestamp_pending_edges, concrete_timestamp, concrete_array,
        array_payload in *. simpl in *.
      split.
      - intros owner lower Hfind.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite TMap.grs in Hfind. discriminate.
        + rewrite TMap.gro in Hfind by exact Hneq.
          eapply Hdomain; eauto.
      - intros owner lower address Hfind Hpending.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite TMap.grs in Hfind. discriminate.
        + rewrite TMap.gro in Hfind by exact Hneq.
          eapply Hbefore; eauto.
    Qed.

    Lemma push_timestamp_inv_update actor (v : A) loc :
      AssertionsSet.PUpdate (G actor)
        (Build_ThreadEvent actor (InvEv (inr newTS)))
        (PushLinearizing actor v loc)
        (PushLinearizing actor v loc).
    Proof.
      intros [control tss] Delta [HIpre [Hlin [Hactor Hloc]]]
        [control' tss'] Hstep.
      simpl in Hstep. destruct Hstep as [Htimestamp_step ->].
      inversion Htimestamp_step; subst; try discriminate.
      injection H as HactorEq. subst actor0.
      destruct HIpre as [Hwf [Hall [Hrect Hcounter]]].
      exists Delta. split; [apply ac_steps_refl|]. split.
      - split.
        + split.
          * destruct Hwf as [Hvalid [Hstamped [Hdefined Hstructural]]].
            split; [now apply start_newTS_valid|]. split; [exact Hstamped|].
            split; assumption.
          * split.
            -- intros rho pi Hposs.
               destruct (Hall _ _ Hposs) as
                 (p & -> & Hpool & Hprotocol & Htimestamp & Hsession).
               assert (Hpending :
                 TMap.find actor (lp_pending_pushes p) = Some loc).
               { specialize (Hloc (pool_local_state actor (LPReady p))).
                 apply Hloc. exists (LPReady p), pi. split; [exact Hposs|].
                 reflexivity. }
               exists p. split; [reflexivity|]. split; [exact Hpool|]. split.
               ++ exact Hprotocol.
               ++ split.
                  ** eapply timestamp_pending_edges_start_timestamp.
                     --- exact Hpool.
                     --- exact (proj1 (proj2 Hwf)).
                     --- exact Htimestamp.
                     --- exact Hpending.
                  ** refine (session_represents_evolve _ _ _ _ _ _ _ Hsession).
                     --- intros n lo hi Hts. exact Hts.
                     --- intros owner N0 Hstarts Hts. simpl.
                         destruct (PositiveMap.E.eq_dec owner actor)
                           as [->|Hneq].
                         +++ exfalso.
                             eapply no_pending_session_of_token;
                               [exact Hprotocol|exact (Hlin _ _ Hposs)
                               |discriminate|exact Hstarts|exact Hts].
                         +++ rewrite TMap.gso by exact Hneq. reflexivity.
            -- split; [exact Hrect|].
               unfold pending_counter_protocol, concrete_array,
                 array_payload in *. simpl in *. exact Hcounter.
        + split; [exact Hlin|]. split; assumption.
      - unfold G. split.
        + intros observer Hneq. apply token_rely_refl.
        + split.
          * intros observer Hneq. apply pool_local_equiv_refl.
          * split.
            -- intros observer causal_loc lower Hneq Hcausal. exact Hcausal.
            -- split.
               ++ intros observer Hneq. reflexivity.
               ++ split.
                  ** intros observer Hneq. simpl.
                     rewrite TMap.gso by congruence. reflexivity.
                  ** split.
                     --- intros observer Hneq.
                         apply candidate_views_preserved_refl.
                     --- split.
                         +++ intros observer Hneq.
                             apply row_snapshot_views_preserved_refl.
                         +++ split.
                             *** apply array_evolves_same_array. reflexivity.
                             *** split; [simpl; lia|].
                                 split.
                                 ++++ intros observer Hneq.
                                      apply candidate_row_views_preserved_refl.
                                 ++++ split.
                                      ***** intros observer Hneq.
                                            apply node_cuts_preserved_same_array;
                                              reflexivity.
                                      ***** split.
                                            ------ apply garbage_evolves_same_array.
                                                   reflexivity.
                                            ------ split.
                                                   { apply intervals_evolve_same_array.
                                                     reflexivity. }
                                                   { intros observer Hneq.
                                                     apply session_equiv_refl. }
    Qed.

    Definition newTS_response
        (ev : @ThreadEvent ETimestamp) : option TS :=
      match te_ev ev with
      | ResEv newTS ts => Some ts
      | _ => None
      end.

    Lemma push_timestamp_res_update actor (v : A) loc lower upper :
      AssertionsSet.PUpdate (G actor)
        (Build_ThreadEvent actor
          (ResEv (inr newTS) (TSInterval lower upper)))
        (PushLinearizing actor v loc)
        (PushTimestamped actor v loc lower upper).
    Proof.
      intros [control tss] Delta [HIpre [Hlin [Hactor Hloc]]]
        [control' tss'] Hstep.
      simpl in Hstep. destruct Hstep as [Htimestamp_step ->].
      inversion Htimestamp_step; subst; try discriminate.
      pose proof (f_equal te_tid H1) as HeventActor. simpl in HeventActor.
      subst actor0.
      pose proof (f_equal newTS_response H1) as Hresult.
      simpl in Hresult. inversion Hresult. subst lower0 upper0.
      destruct HIpre as [Hwf [Hall [Hrect Hcounter]]].
      exists Delta. split; [apply ac_steps_refl|]. split.
      - split.
        + split.
          * split.
            -- destruct Hwf as [Hvalid [Hstamped [Hdefined Hstructural]]].
               split; [now apply finish_newTS_valid|]. split.
               ++ intros n lo hi Hfind. specialize (Hstamped n lo hi Hfind).
                  simpl. eapply Nat.le_trans; [exact Hstamped|].
                  apply Nat.le_max_l.
               ++ split; assumption.
            -- split.
               ++ intros rho pi Hposs.
                  destruct (Hall _ _ Hposs) as
                    (p & -> & Hpool & Hprotocol & Htimestamp & Hsession).
                  exists p. split; [reflexivity|]. split; [exact Hpool|]. split.
                  ** exact Hprotocol.
                  ** split.
                     --- eapply timestamp_pending_edges_finish_timestamp.
                         exact Htimestamp.
                     --- refine (session_represents_evolve _ _ _ _ _ _ _ Hsession).
                         +++ intros n lo hi Hts. exact Hts.
                         +++ intros owner N0 Hstarts Hts. simpl.
                             destruct (PositiveMap.E.eq_dec owner actor)
                               as [->|Hneq].
                             *** exfalso.
                                 eapply no_pending_session_of_token;
                                   [exact Hprotocol|exact (Hlin _ _ Hposs)
                                   |discriminate|exact Hstarts|exact Hts].
                             *** rewrite TMap.gro by exact Hneq. reflexivity.
               ++ split; [exact Hrect|].
                  unfold pending_counter_protocol, concrete_array,
                    array_payload in *. simpl in *. exact Hcounter.
          * split; [exact Hlin|]. split; assumption.
        + split; [exact H0|]. split.
          * simpl. exact (finish_newTS_clock_past actor upper tss).
          * split.
            -- simpl. apply TMap.grs.
            -- intros rho pi Hposs.
               destruct (Hall _ _ Hposs) as
                 (p & -> & Hpool & Hprotocol & Htimestamp & Hsession).
               assert (Hpending_pool :
                 TMap.find actor (lp_pending_pushes p) = Some loc).
               { specialize (Hloc (pool_local_state actor (LPReady p))).
                 apply Hloc. exists (LPReady p), pi.
                 split; [exact Hposs|reflexivity]. }
               exists p. split; [reflexivity|]. split; [exact Hpending_pool|].
               eapply (proj2 Htimestamp); eauto.
      - unfold G. split.
        + intros observer Hneq. apply token_rely_refl.
        + split.
          * intros observer Hneq. apply pool_local_equiv_refl.
          * split.
            -- intros observer loc0 bound Hneq Hcausal. exact Hcausal.
            -- split.
               ++ intros observer Hneq. reflexivity.
               ++ split.
                  ** intros observer Hneq. simpl.
                     rewrite TMap.gro by congruence. reflexivity.
                  ** split.
                     --- intros observer Hneq.
                         apply candidate_views_preserved_refl.
                     --- split.
                         +++ intros observer Hneq.
                             apply row_snapshot_views_preserved_refl.
                         +++ split.
                             *** apply array_evolves_same_array. reflexivity.
                             *** split; [simpl; apply Nat.le_max_l|].
                                 split.
                                 ++++ intros observer Hneq.
                                      apply candidate_row_views_preserved_refl.
                                 ++++ split.
                                      ***** intros observer Hneq.
                                            apply node_cuts_preserved_same_array;
                                              reflexivity.
                                      ***** split.
                                            ------ apply garbage_evolves_same_array.
                                                   reflexivity.
                                            ------ split.
                                                   { apply intervals_evolve_same_array.
                                                     reflexivity. }
                                                   { intros observer Hneq.
                                                     apply session_equiv_refl. }
    Qed.

    Lemma push_setTS_no_error actor (v : A) loc lower upper :
      ⊨ PushTimestamped actor v loc lower upper ==>>
        AssertionsSet.A.ANoError
          (Build_ThreadEvent actor
            (InvEv (inl (array_setTS loc (TSInterval lower upper))))).
    Proof.
      intros [[control tss] Delta]
        [[HI [Hlin [Hactor Hloc]]]
          [Hwf_ts [Hbound [Hnone Hcausal]]]] Herror.
      destruct HI as [Hwf [Hall _]].
      destruct (ac_nonempty Delta) as (rho & pi & Hposs).
      destruct (Hall _ _ Hposs) as
        (p & -> & Hpool & Hprotocol & Htimestamp & Hsession).
      assert (Hpending_pool :
        TMap.find actor (lp_pending_pushes p) = Some loc).
      { specialize (Hloc (pool_local_state actor (LPReady p))).
        apply Hloc. exists (LPReady p), pi. split; [exact Hposs|reflexivity]. }
      assert (Hvertex : array_vertex (array_payload control)
        (pair actor loc)).
        { destruct Hpool as
          (Hvertices & Hedges & Hedgevertices & Hgarbage & Hpending &
            Hsnapshots & Hrows).
        eapply timestamp_defined_timestamp.
        - exact (proj1 (proj2 (proj2 Hwf))).
        - apply (proj1 (Hpending (pair actor loc))).
          unfold is_pending. exact Hpending_pool. }
      simpl in Herror.
      remember (Build_ThreadEvent actor
        (InvEv (array_setTS loc (TSInterval lower upper))))
        as ev eqn:Hev in Herror.
      inversion Herror.
      all: try match goal with
        | Hctor : ?lhs = ?remembered,
          Htarget : ?remembered = ?target |- _ =>
            let Hevent := fresh "Hevent" in
            pose proof (eq_trans Hctor Htarget) as Hevent;
            let Hresult := fresh "Hresult" in
            pose proof (f_equal array_setTS_inv_info Hevent) as Hresult;
            cbv [array_setTS_inv_info] in Hresult;
            first [discriminate Hresult |
              dependent destruction Hevent; contradiction]
        end.
    Qed.

    Lemma push_setTS_inv_update actor (v : A) loc lower upper :
      AssertionsSet.PUpdate (G actor)
        (Build_ThreadEvent actor
          (InvEv (inl (array_setTS loc (TSInterval lower upper)))))
        (PushTimestamped actor v loc lower upper)
        (PushTimestamped actor v loc lower upper).
    Proof.
      intros [control tss] Delta Hpre [control' tss'] Hstep.
      simpl in Hstep. destruct Hstep as [Harray ->].
      destruct (array_setTS_inv_shape actor loc
        (TSInterval lower upper) _ _ Harray)
        as (a & -> & -> & Hactor & Hvertex).
      exists Delta. split; [apply ac_steps_refl|]. split.
      - exact Hpre.
      - unfold G. split.
        + intros observer Hneq. apply token_rely_refl.
        + split.
          * intros observer Hneq. apply pool_local_equiv_refl.
          * split.
            -- intros observer causal_loc bound Hneq Hcausal. exact Hcausal.
            -- split; [intros observer Hneq; reflexivity|].
               split; [intros observer Hneq; reflexivity|]. split.
               ++ intros observer Hneq. apply candidate_views_preserved_refl.
               ++ split.
                  ** intros observer Hneq.
                     apply row_snapshot_views_preserved_refl.
                  ** split.
                     --- apply array_evolves_same_array. reflexivity.
                     --- split; [simpl; lia|].
                         split.
                         ++++ intros observer Hneq.
                              apply candidate_row_views_preserved_refl.
                         ++++ split.
                              ***** intros observer Hneq.
                                    apply node_cuts_preserved_same_array;
                                      reflexivity.
                              ***** split.
                                    ------ apply garbage_evolves_same_array.
                                           reflexivity.
                                    ------ split.
                                           { apply intervals_evolve_same_array.
                                             reflexivity. }
                                           { intros observer Hneq.
                                             apply session_equiv_refl. }
    Qed.

    Lemma timestamp_pending_edges_finish_push_set
        (a : @SPListArrayState A) (tss : TimestampState)
        (p : @ListPoolState A) actor loc lower upper :
      pool_represents a p ->
      timestamp_pending_edges
        (pair (ArrayAtomicPending a actor
          (array_setTS loc (TSInterval lower upper))) tss) p ->
      TMap.find actor (ts_pending tss) = None ->
      TMap.find actor (lp_pending_pushes p) = Some loc ->
      as_timestamps a (pair actor loc) = Some TSTop ->
      timestamp_pending_edges
        (pair (ArrayReady
          (set_node_timestamp actor loc (TSInterval lower upper) a)) tss)
        (finish_push actor p).
    Proof.
      intros Hpool [Hdomain Hbefore] Hnone Hpending_actor Htop.
      assert (Hnoincoming : forall newer,
        ~ lp_edges p newer (pair actor loc)).
      { eapply pending_node_has_no_incoming; [exact Hpool|].
        unfold is_pending. exact Hpending_actor. }
      unfold timestamp_pending_edges, concrete_timestamp, concrete_array,
        array_payload in *. simpl in *.
      split.
      - intros owner saved Hfind.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite Hnone in Hfind. discriminate.
        + destruct (Hdomain _ _ Hfind) as [[old_loc Hold]|Hsess].
          * left. exists old_loc. rewrite TMap.gro by exact Hneq. exact Hold.
          * right. simpl. exact Hsess.
      - intros owner saved old_loc Hfind Hpending.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite Hnone in Hfind. discriminate.
        + rewrite TMap.gro in Hpending by exact Hneq.
          specialize (Hbefore owner saved old_loc Hfind Hpending).
          intros older Hedge.
          destruct (Hbefore _ Hedge) as
            (old_lower & old_upper & Htimestamp & Hlt).
          assert (Holder : older <> pair actor loc).
          { intro Heq. subst older. exact (Hnoincoming _ Hedge). }
          exists old_lower, old_upper. split; [|exact Hlt].
          rewrite set_timestamp_other by exact Holder. exact Htimestamp.
    Qed.

    Lemma outgoing_before_finish_push_set_foreign
        (a : @SPListArrayState A) (p : @ListPoolState A)
        actor loc lower upper observer observer_loc bound :
      pool_represents a p ->
      TMap.find actor (lp_pending_pushes p) = Some loc ->
      actor <> observer ->
      outgoing_before a p (pair observer observer_loc) bound ->
      outgoing_before
        (set_node_timestamp actor loc (TSInterval lower upper) a)
        (finish_push actor p) (pair observer observer_loc) bound.
    Proof.
      intros Hpool Hpending_actor Hneq Hbefore older Hedge.
      assert (Hnoincoming : forall newer,
        ~ lp_edges p newer (pair actor loc)).
      { eapply pending_node_has_no_incoming; [exact Hpool|].
        unfold is_pending. exact Hpending_actor. }
      destruct (Hbefore _ Hedge) as
        (old_lower & old_upper & Htimestamp & Hlt).
      assert (Holder : older <> pair actor loc).
      { intro Heq. subst older. exact (Hnoincoming _ Hedge). }
      exists old_lower, old_upper. split; [|exact Hlt].
      rewrite set_timestamp_other by exact Holder. exact Htimestamp.
    Qed.

    Definition push_finish_rho actor (rho : abstract_state) : abstract_state :=
      match rho with
      | LPReady p => LPReady (finish_push actor p)
      | LPAtomicPending p pending_actor op =>
          LPAtomicPending p pending_actor op
      end.

    Lemma pool_shared_eq_finish_push_compat actor p q :
      pool_shared_eq p q ->
      pool_shared_eq (finish_push actor p) (finish_push actor q).
    Proof.
      intros (Hvertices & Hedges & Hpending & Hgarbage & Hpop_starts & Hpop_ts).
      unfold pool_shared_eq, finish_push; simpl. repeat split; congruence.
    Qed.

    Lemma finish_push_snapshot_find actor observer (p : @ListPoolState A) :
      TMap.find observer (lp_snapshots (finish_push actor p)) =
        TMap.find observer (lp_snapshots p).
    Proof. reflexivity. Qed.

    Lemma push_setTS_res_update actor (v : A) loc lower upper :
      AssertionsSet.PUpdate (G actor)
        (Build_ThreadEvent actor
          (ResEv (inl (array_setTS loc (TSInterval lower upper))) tt))
        (PushTimestamped actor v loc lower upper)
        (Completed actor (lpool_push v) tt).
    Proof.
      intros [control tss] Delta
        [[HIpre [Hlin [Hactor Hloc]]]
          [Hwf_ts [Hbound [Hnone Hcausal]]]]
        [control' tss'] Hstep.
      simpl in Hstep. destruct Hstep as [Harray ->].
      destruct (array_setTS_res_shape actor loc
        (TSInterval lower upper) _ _ Harray) as (a & -> & ->).
      destruct HIpre as [Hwf [Hall [Hrect Hcounter]]].
      destruct (ac_nonempty Delta) as (rho_sample & pi_sample & Hsample).
      destruct (Hall _ _ Hsample) as
        (p_sample & -> & Hpool_sample & Hprotocol_sample & Htimestamp_sample).
      assert (Hpending_sample :
        TMap.find actor (lp_pending_pushes p_sample) = Some loc).
      { specialize (Hloc (pool_local_state actor (LPReady p_sample))).
        apply Hloc. exists (LPReady p_sample), pi_sample.
        split; [exact Hsample|reflexivity]. }
      assert (Htop : as_timestamps a (pair actor loc) = Some TSTop).
      { destruct Hpool_sample as
          (Hvertices & Hedges & Hedgevertices & Hgarbage & Hpending &
            Hsnapshots & Hrows).
        apply (proj1 (Hpending (pair actor loc))).
        unfold is_pending. exact Hpending_sample. }
      assert (Hsteps : forall rho pi, Delta rho pi ->
        poss_steps (PossOk rho pi)
          (PossOk (push_finish_rho actor rho)
            (TMap.add actor (ls_linr (lpool_push v) tt) pi))).
      { intros rho pi Hposs.
        destruct (Hall _ _ Hposs) as
          (p & -> & Hpool & Hprotocol & Htimestamp & Hsession).
        assert (Hpending_pool :
          TMap.find actor (lp_pending_pushes p) = Some loc).
        { specialize (Hloc (pool_local_state actor (LPReady p))).
          apply Hloc. exists (LPReady p), pi.
          split; [exact Hposs|reflexivity]. }
        apply rt_step. eapply ps_ret.
        - eapply step_push_res; [exact Hpending_pool|reflexivity].
        - exact (Hlin _ _ Hposs). }
      exists (ac_image Delta (push_finish_rho actor)
        (fun pi => TMap.add actor (ls_linr (lpool_push v) tt) pi) Hsteps).
      split; [apply ac_image_subset_steps|]. split.
      - split.
        + split.
          * destruct Hwf as [Hvalid [Hstamped [Hdefined Hstructural]]].
            split; [exact Hvalid|]. split.
            -- eapply stamped_before_clock_set; eauto.
            -- split.
               ++ eapply timestamp_defined_set; eauto.
               ++ exact Hstructural.
          * split.
            -- intros rho pi Himage.
               destruct (ac_image_elim _ _ _ _ _ _ Himage) as
                 (rho0 & pi0 & Hposs & -> & ->).
               destruct (Hall _ _ Hposs) as
                 (p & -> & Hpool & Hprotocol & Htimestamp & Hsession).
               assert (Hpending_pool :
                 TMap.find actor (lp_pending_pushes p) = Some loc).
               { specialize (Hloc (pool_local_state actor (LPReady p))).
                 apply Hloc. exists (LPReady p), pi0.
                 split; [exact Hposs|reflexivity]. }
               assert (Hbefore : outgoing_before a p (pair actor loc) lower).
               { destruct (Hcausal _ _ Hposs) as
                   (p0 & Heq & Hpending0 & Hbefore0).
                 inversion Heq; subst p0. exact Hbefore0. }
               exists (finish_push actor p). split; [reflexivity|]. split.
               ++ eapply pool_represents_finish_push; eauto.
                  intros older Hedge.
                  eapply outgoing_before_stamped_edge; eauto.
               ++ split.
                  ** eapply pool_protocol_finish_push; eauto.
                  ** split.
                     --- eapply timestamp_pending_edges_finish_push_set; eauto.
                     --- refine (session_represents_evolve _ _ _ _ _ _ _ Hsession).
                         +++ intros n lo hi Hts.
                             apply interval_timestamps_preserved_set_at_top;
                               [|exact Hts].
                             exact Htop.
                         +++ intros owner N0 _ _. reflexivity.
            -- split.
               ++ eapply possibility_rectangular_add_image.
                  ** intro p. reflexivity.
                  ** intros rho q Hready. destruct rho; simpl in Hready.
                     --- inversion Hready. eexists; split; reflexivity.
                     --- discriminate.
                  ** apply pool_shared_eq_finish_push_compat.
                  ** apply finish_push_snapshot_find.
                  ** exact Hrect.
               ++ intros observer saved Hpending.
                  change (TMap.find observer (as_pending_counters a) =
                    Some saved) in Hpending.
                  destruct (Hcounter observer saved Hpending) as
                    (rho0 & pi0 & start0 & Hposs & Hfind).
                  destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
                  ** pose proof (Hlin rho0 pi0 Hposs) as Hlin_actor.
                     pose proof (eq_trans (eq_sym Hlin_actor) Hfind)
                       as Hstate_eq.
                     change (Some (ls_lini (lpool_push v)) =
                       Some (ls_lini (lpool_getTop start0))) in Hstate_eq.
                     injection Hstate_eq as Hop. discriminate Hop.
                  ** exists (push_finish_rho actor rho0),
                       (TMap.add actor (ls_linr (lpool_push v) tt) pi0), start0. split.
                     --- constructor. exact Hposs.
                     --- rewrite TMap.gso by congruence. exact Hfind.
        + unfold ALin. intros rho pi Himage.
          destruct (ac_image_elim _ _ _ _ _ _ Himage) as
            (rho0 & pi0 & Hposs & -> & ->). apply TMap.gss.
      - unfold G. split.
        + intros observer Hneq.
          apply token_equiv_rely. eapply token_equiv_image_foreign. intro pi.
          rewrite TMap.gso by congruence. reflexivity.
        + split.
          * intros observer Hneq.
            eapply pool_local_equiv_image_foreign. intro rho.
            destruct rho; simpl.
            -- rewrite TMap.gro by congruence. reflexivity.
            -- reflexivity.
          * split.
            -- intros observer causal_loc bound Hneq Hforeign rho pi Himage.
               destruct (ac_image_elim _ _ _ _ _ _ Himage) as
                 (rho0 & pi0 & Hposs & -> & ->).
               destruct (Hall _ _ Hposs) as
                 (p & -> & Hpool & Hprotocol & Htimestamp & Hsession).
               destruct (Hforeign _ _ Hposs) as
                 (p0 & Heq & Hpending_foreign & Hbefore).
               inversion Heq; subst p0.
               assert (Hpending_pool :
                 TMap.find actor (lp_pending_pushes p) = Some loc).
               { specialize (Hloc (pool_local_state actor (LPReady p))).
                 apply Hloc. exists (LPReady p), pi0.
                 split; [exact Hposs|reflexivity]. }
               exists (finish_push actor p). split; [reflexivity|]. split.
               ++ simpl. rewrite TMap.gro by congruence.
                  exact Hpending_foreign.
               ++ eapply outgoing_before_finish_push_set_foreign; eauto.
            -- split; [intros observer Hneq; reflexivity|].
               split; [intros observer Hneq; reflexivity|]. split.
               ++ intros observer Hneq done candidate Hview.
                  unfold candidate_view in *.
                  destruct Hview as
                    (p & pi & N & Hposs & Htoken & Hsnapshot & Hvalue &
                      Hdone & Hstatus & Hsafe).
                  exists (finish_push actor p),
                    (TMap.add actor (ls_linr (lpool_push v) tt) pi), N.
                  repeat split.
                  ** change (ac_image_prop Delta
                       (push_finish_rho actor)
                       (fun pi => TMap.add actor
                         (ls_linr (lpool_push v) tt) pi)
                       Hsteps
                       (push_finish_rho actor (LPReady p))
                       (TMap.add actor (ls_linr (lpool_push v) tt) pi)).
                     constructor. exact Hposs.
                  ** rewrite TMap.gso by congruence. exact Htoken.
                  ** exact Hsnapshot.
                  ** exact Hvalue.
                  ** exact Hdone.
                  ** exact Hstatus.
                  ** eapply candidate_tstop_safe_finish_push. exact Hsafe.
               ++ split.
                  ** intros observer Hneq owner saved Hview.
                     unfold row_snapshot_view in *.
                     destruct Hview as
                       (p & pi & N & Hposs & Htoken & Hsnapshot & Hsaved &
                         Hlive & Horder).
                     exists (finish_push actor p),
                       (TMap.add actor (ls_linr (lpool_push v) tt) pi), N.
                     repeat split.
                     --- change (ac_image_prop Delta
                           (push_finish_rho actor)
                           (fun pi => TMap.add actor
                             (ls_linr (lpool_push v) tt) pi)
                           Hsteps
                           (push_finish_rho actor (LPReady p))
                           (TMap.add actor (ls_linr (lpool_push v) tt) pi)).
                         constructor. exact Hposs.
                     --- rewrite TMap.gso by congruence. exact Htoken.
                     --- exact Hsnapshot.
                     --- exact Hsaved.
                     --- exact Hlive.
                     --- exact Horder.
                  ** split.
                     --- eapply array_evolves_of_counter_order.
                         +++ intro q. reflexivity.
                         +++ intro q. reflexivity.
                     --- split; [simpl; lia|].
                         split.
                         ++++ intros observer Hneq done candidate row saved
                                Hview.
                              unfold candidate_row_view in *.
                              destruct Hview as
                                (p & pi & N & Hposs & Htoken & Hsnapshot &
                                  Hvalue & Hdone & Hstatus & Hcovered & Horder &
                                  Hsafe).
                              exists (finish_push actor p),
                                (TMap.add actor
                                  (ls_linr (lpool_push v) tt) pi), N.
                              repeat split; try assumption.
                              ***** change (ac_image_prop Delta
                                    (push_finish_rho actor)
                                    (fun pi => TMap.add actor
                                      (ls_linr (lpool_push v) tt) pi)
                                    Hsteps
                                    (push_finish_rho actor (LPReady p))
                                    (TMap.add actor
                                      (ls_linr (lpool_push v) tt) pi)).
                                   constructor. exact Hposs.
                              ***** rewrite TMap.gso by congruence.
                                    exact Htoken.
                         ++++ split.
                              ***** intros observer Hneq progress start0 Hinside
                                      Hfallback Hsession_all Hcuts n value Hlive Hvalue
                                      Hnotignored.
                                    change (array_live a n) in Hlive.
                                    change (as_values a n = Some value)
                                      in Hvalue.
                                    destruct (Hcuts n value Hlive Hvalue
                                      Hnotignored) as
                                      (p & pi & N & Hposs & Htoken & Hsnapshot &
                                        Hnode_value & Hmember & Hcut).
                                    exists (finish_push actor p),
                                      (TMap.add actor
                                        (ls_linr (lpool_push v) tt) pi), N.
                                    repeat split; try assumption.
                                    ------ change (ac_image_prop Delta
                                          (push_finish_rho actor)
                                          (fun pi => TMap.add actor
                                            (ls_linr (lpool_push v) tt) pi)
                                          Hsteps
                                          (push_finish_rho actor (LPReady p))
                                          (TMap.add actor
                                            (ls_linr (lpool_push v) tt) pi)).
                                         constructor. exact Hposs.
                                    ------ rewrite TMap.gso by congruence.
                                         exact Htoken.
                              ***** split.
                                    ------ unfold garbage_evolves,
                                            concrete_array, array_payload.
                                           simpl. firstorder.
                                    ------ split; [|intros observer Hneq;
                                             apply session_equiv_image_foreign;
                                             intro rho; destruct rho; reflexivity].
                                           unfold intervals_evolve,
                                            concrete_array, array_payload.
                                           simpl.
                                           split.
                                           +++++++ exact
                                             (timestamp_domain_preserved_set_at_top
                                               a actor loc
                                               (TSInterval lower upper) Htop).
                                           +++++++ split.
                                                   { exact
                                                     (interval_timestamps_preserved_set_at_top
                                                       a actor loc
                                                       (TSInterval lower upper) Htop). }
                                                   { intros n v0 Hvalue0. exact Hvalue0. }
    Qed.

    Definition FalseA : assertion := fun _ => False.

    Lemma falseA_entails_I : ⊨ FalseA ==>> I.
    Proof. intros w Hfalse. contradiction. Qed.

    Lemma falseA_stable actor :
      AssertionsSet.A.Stable (R actor) I FalseA.
    Proof.
      unfold AssertionsSet.A.Stable, AssertionsSet.A.ComposeA.
      intros w [[pre [Hfalse HR]] HI]. contradiction.
    Qed.

    Lemma false_triple actor {X} (p : Prog (li_sig E) X)
        (Q : X -> assertion)
        (HQI : forall x, ⊨ Q x ==>> I)
        (HQstable : forall x,
          AssertionsSet.A.Stable (R actor) I (Q x)) :
      SetLogic.HTripleProvable (R actor) (G actor) I actor FalseA p Q.
    Proof.
      revert p. cofix IH. intros p. destruct p as [m k | x | p].
      - eapply SetLogic.provable_vis with
          (P := FalseA) (P' := FalseA) (Q' := fun _ => FalseA).
        + intros w Hfalse. left. exact Hfalse.
        + intros w Hfalse. contradiction.
        + apply falseA_entails_I.
        + intros. apply falseA_entails_I.
        + apply falseA_stable.
        + intros. apply falseA_stable.
        + intros sigma Delta Hfalse. contradiction.
        + intros ret sigma Delta Hfalse. contradiction.
        + intros ret. apply IH; assumption.
      - eapply SetLogic.provable_ret with (P := FalseA).
        + intros w Hfalse. left. exact Hfalse.
        + intros w Hfalse. contradiction.
        + apply HQI.
        + apply HQstable.
      - apply SetLogic.provable_tau. apply IH; assumption.
    Qed.

    Lemma push_actor_entails_I actor v :
      ⊨ PushActor actor v ==>> I.
    Proof. intros w [[HI Hlin] Hactor]. exact HI. Qed.

    Lemma push_actor_stable actor v :
      AssertionsSet.A.Stable (R actor) I (PushActor actor v).
    Proof.
      unfold AssertionsSet.A.Stable, AssertionsSet.A.ComposeA,
        PushActor, Active, R.
      intros w
        [[pre [[[HI Hlin] Hactor]
          [Hequiv [Hlocal [Hcausal [Harray_local [Hpending
            [Hcandidate [Hevolve Hclock]]]]]]]]] HI'].
      split.
      - split; [exact HI'|]. unfold ALin in *.
        eapply token_rely_ALin_non_getTop_inv; eauto; intros ?; discriminate.
      - exact Hactor.
    Qed.

    Lemma push_actor_no_error actor (v : A) :
      ⊨ PushActor actor v ==>>
        AssertionsSet.A.ANoError
          (Build_ThreadEvent actor (InvEv (inl (array_insert v)))).
    Proof.
      intros [[control tss] Delta] [[HI Hlin] Hactor] Herror.
      simpl in Herror.
      remember (Build_ThreadEvent actor (InvEv (array_insert v)))
        as ev eqn:Hev in Herror.
      inversion Herror.
      all: try match goal with
        | Hctor : ?lhs = ?remembered,
          Htarget : ?remembered = ?target |- _ =>
            let Hevent := fresh "Hevent" in
            pose proof (eq_trans Hctor Htarget) as Hevent;
            let Hresult := fresh "Hresult" in
            pose proof (f_equal array_insert_inv_value Hevent) as Hresult;
            cbv [array_insert_inv_value] in Hresult;
            first [discriminate Hresult |
              dependent destruction Hevent; contradiction]
        end.
    Qed.

    Lemma push_actor_or_error actor (v : A) w :
      Active actor (lpool_push v) w ->
      PushActor actor v w \/ AssertionsSet.APError w.
    Proof.
      intros Hactive.
      destruct (ThreadDomain.contains_dec D actor) as [Hactor|Houtside].
      - left. split; assumption.
      - right. destruct w as [sigma Delta].
        destruct Hactive as [HI Hlin].
        destruct (ac_nonempty Delta) as (rho & pi & Hposs).
        destruct HI as [Hwf [Hall _]].
        destruct (Hall _ _ Hposs) as
          (p & -> & Hpool & Hprotocol & Htimestamp & Hsession).
        econstructor; [exact Hposs|]. apply rt_step. eapply ps_error.
        + eapply error_actor_outside; [exact Houtside|reflexivity].
        + exact (Hlin _ _ Hposs).
    Qed.

    Definition PushTimestampResult actor (v : A) loc (ts : TS) : assertion :=
      match ts with
      | TSTop => FalseA
      | TSInterval lower upper =>
          PushTimestamped actor v loc lower upper
      end.

    Lemma push_timestamp_result_entails_I actor v loc ts :
      ⊨ PushTimestampResult actor v loc ts ==>> I.
    Proof.
      destruct ts as [|lower upper]; simpl.
      - apply falseA_entails_I.
      - apply push_timestamped_entails_I.
    Qed.

    Lemma push_timestamp_result_stable actor v loc ts :
      AssertionsSet.A.Stable (R actor) I
        (PushTimestampResult actor v loc ts).
    Proof.
      destruct ts as [|lower upper]; simpl.
      - apply falseA_stable.
      - apply push_timestamped_stable.
    Qed.

    Lemma push_timestamp_any_res_update actor (v : A) loc ts :
      AssertionsSet.PUpdate (G actor)
        (Build_ThreadEvent actor (ResEv (inr newTS) ts))
        (PushLinearizing actor v loc)
        (PushTimestampResult actor v loc ts).
    Proof.
      destruct ts as [|lower upper].
      - intros [control tss] Delta Hpre [control' tss'] Hstep.
        simpl in Hstep. destruct Hstep as [Htimestamp_step ->].
        inversion Htimestamp_step; subst; try discriminate.
        pose proof (f_equal newTS_response H1) as Hresult.
        simpl in Hresult. discriminate.
      - apply push_timestamp_res_update.
    Qed.

    Lemma push_method_triple actor (v : A) :
      SetLogic.HTripleProvable (R actor) (G actor) I actor
        (Active actor (lpool_push v))
        (push_impl D v actor)
        (fun ret => Completed actor (lpool_push v) ret).
    Proof.
      eapply SetLogic.provable_perror with (P' := PushActor actor v).
      - intros w Hactive. eapply push_actor_or_error; eauto.
      - unfold push_impl.
        eapply SetLogic.provable_vis_safe with
          (P' := PushActor actor v)
          (Q' := fun loc => PushLinearizing actor v loc).
        + apply push_actor_no_error.
        + apply push_actor_entails_I.
        + intros. apply push_linearizing_entails_I.
        + apply push_actor_stable.
        + intros. apply push_linearizing_stable.
        + intros sigma Delta [Hactive Hactor].
          eapply push_insert_inv_update. exact Hactive.
        + intros loc. apply push_insert_res_update.
        + intros loc.
          eapply SetLogic.provable_vis_safe with
            (P' := PushLinearizing actor v loc)
            (Q' := fun ts => PushTimestampResult actor v loc ts).
          * intros [[control tss] Delta] Hpre Herror. exact Herror.
          * apply push_linearizing_entails_I.
          * intros. apply push_timestamp_result_entails_I.
          * apply push_linearizing_stable.
          * intros. apply push_timestamp_result_stable.
          * apply push_timestamp_inv_update.
          * intros ts. apply push_timestamp_any_res_update.
          * intros [|lower upper].
            -- apply false_triple.
               ++ intros. apply completed_entails_I.
               ++ intros. apply completed_stable.
            -- eapply SetLogic.provable_vis_safe with
                 (P' := PushTimestamped actor v loc lower upper)
                 (Q' := fun _ => Completed actor (lpool_push v) tt).
               ++ apply push_setTS_no_error.
               ++ apply push_timestamped_entails_I.
               ++ intros. apply completed_entails_I.
               ++ apply push_timestamped_stable.
               ++ intros. apply completed_stable.
               ++ apply push_setTS_inv_update.
               ++ intros []. apply push_setTS_res_update.
               ++ intros []. eapply SetLogic.provable_ret_safe.
                  ** apply ImplRefl.
                  ** apply completed_entails_I.
                  ** apply completed_stable.
    Qed.

    (** [startPop] is a pass-through [newTS].  Its invocation records the
        start set (the vertices whose push has completed) in every
        possibility, and its response records the returned interval as the
        caller's session token.  The start-set invariant is established
        from [stamped_before_clock] at the invocation. *)
    Definition start_pop_rho actor (rho : abstract_state) : abstract_state :=
      match rho with
      | LPReady p => LPReady (start_pop_session actor p)
      | LPAtomicPending p pending op => LPAtomicPending p pending op
      end.

    Definition finish_pop_rho actor (ts : TS) (rho : abstract_state) :
        abstract_state :=
      match rho with
      | LPReady p => LPReady (finish_pop_session actor ts p)
      | LPAtomicPending p pending op => LPAtomicPending p pending op
      end.

    Lemma pool_shared_eq_start_pop_session_compat actor p q :
      pool_shared_eq p q ->
      pool_shared_eq (start_pop_session actor p) (start_pop_session actor q).
    Proof.
      intros (Hvertices & Hedges & Hpending & Hgarbage & Hpop_starts & Hpop_ts).
      assert (Hcompleted : completed_set p = completed_set q).
      { apply functional_extensionality; intro n.
        unfold completed_set, is_vertex, is_pending.
        rewrite Hvertices, Hpending. reflexivity. }
      unfold pool_shared_eq, start_pop_session; simpl.
      rewrite Hcompleted. repeat split; congruence.
    Qed.

    Lemma pool_shared_eq_finish_pop_session_compat actor ts p q :
      pool_shared_eq p q ->
      pool_shared_eq (finish_pop_session actor ts p)
        (finish_pop_session actor ts q).
    Proof.
      intros (Hvertices & Hedges & Hpending & Hgarbage & Hpop_starts & Hpop_ts).
      unfold pool_shared_eq, finish_pop_session; simpl.
      repeat split; congruence.
    Qed.

    Lemma timestamp_pending_edges_start_pop_session control
        (tss : TimestampState) (p : @ListPoolState A) pi actor :
      pool_protocol p pi ->
      TMap.find actor pi = Some (ls_inv lpool_startPop) ->
      timestamp_pending_edges (pair control tss) p ->
      timestamp_pending_edges (pair control (start_newTS actor tss))
        (start_pop_session actor p).
    Proof.
      intros Hprotocol Hactive [Hdomain Hbefore].
      assert (Hno_push : forall loc,
        TMap.find actor (lp_pending_pushes p) <> Some loc).
      { intros loc Hfind.
        destruct (proj1 Hprotocol _ _ Hfind) as [v Htoken].
        rewrite Hactive in Htoken. discriminate. }
      unfold timestamp_pending_edges, concrete_timestamp, concrete_array,
        array_payload, outgoing_before in *. simpl in *.
      split.
      - intros owner lower Hfind.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + right. split; [apply TMap.grs|].
          exists (completed_set p). apply TMap.gss.
        + rewrite TMap.gso in Hfind by exact Hneq.
          destruct (Hdomain _ _ Hfind) as [Hpush|[Hts [N0 Hstarts]]].
          * left. exact Hpush.
          * right. split; [rewrite TMap.gro by exact Hneq; exact Hts|].
            exists N0. rewrite TMap.gso by exact Hneq. exact Hstarts.
      - intros owner lower loc Hfind Hpending.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + exfalso. exact (Hno_push loc Hpending).
        + rewrite TMap.gso in Hfind by exact Hneq. eapply Hbefore; eauto.
    Qed.

    Lemma timestamp_pending_edges_finish_pop_session control
        (tss : TimestampState) (p : @ListPoolState A) actor ts upper :
      timestamp_pending_edges (pair control tss) p ->
      timestamp_pending_edges (pair control (finish_newTS actor upper tss))
        (finish_pop_session actor ts p).
    Proof.
      intros [Hdomain Hbefore].
      unfold timestamp_pending_edges, concrete_timestamp, concrete_array,
        array_payload, outgoing_before in *. simpl in *.
      split.
      - intros owner lower Hfind.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite TMap.grs in Hfind. discriminate.
        + rewrite TMap.gro in Hfind by exact Hneq.
          destruct (Hdomain _ _ Hfind) as [Hpush|[Hts [N0 Hstarts]]].
          * left. exact Hpush.
          * right. split; [rewrite TMap.gso by exact Hneq; exact Hts|].
            exists N0. exact Hstarts.
      - intros owner lower loc Hfind Hpending.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite TMap.grs in Hfind. discriminate.
        + rewrite TMap.gro in Hfind by exact Hneq. eapply Hbefore; eauto.
    Qed.

    Definition StartPopLinearizing actor : assertion :=
      I //\\ actor ↦∀•(lpool_startPop).

    Lemma start_pop_linearizing_entails_I actor :
      ⊨ StartPopLinearizing actor ==>> I.
    Proof. firstorder. Qed.

    Lemma start_pop_linearizing_stable actor :
      AssertionsSet.A.Stable (R actor) I (StartPopLinearizing actor).
    Proof.
      unfold AssertionsSet.A.Stable, AssertionsSet.A.ComposeA,
        StartPopLinearizing, R. intros w [[pre [[HI Hlin] Hequiv]] HI'].
      destruct Hequiv as [Hequiv _].
      split; [exact HI'|].
      unfold ALin in *.
      eapply token_rely_ALin_non_getTop_inv; eauto; intros ?; discriminate.
    Qed.

    (** Shared tail of the two [startPop] updates: the guarantee for an
        image that only changes the actor's token and session entries. *)
    Lemma G_session_image (control : @SPListArrayControl A)
        (tss tss' : TimestampState)
        (Delta : @AbstractConfig _ (li_lts F)) actor
        (f : @ListPoolState A -> @ListPoolState A) token
        (rhof : abstract_state -> abstract_state)
        (Hsteps : forall rho pi, Delta rho pi ->
          poss_steps (PossOk rho pi)
            (PossOk (rhof rho) (TMap.add actor token pi))) :
      (forall p, rhof (LPReady p) = LPReady (f p)) ->
      (forall p pending op,
        rhof (LPAtomicPending p pending op) = LPAtomicPending p pending op) ->
      (forall p, lp_vertices (f p) = lp_vertices p) ->
      (forall p, lp_edges (f p) = lp_edges p) ->
      (forall p, lp_snapshots (f p) = lp_snapshots p) ->
      (forall p, lp_pending_pushes (f p) = lp_pending_pushes p) ->
      (forall p, lp_garbage (f p) = lp_garbage p) ->
      (forall observer p, actor <> observer ->
        TMap.find observer (lp_pop_starts (f p)) =
          TMap.find observer (lp_pop_starts p)) ->
      (forall observer p, actor <> observer ->
        TMap.find observer (lp_pop_ts (f p)) =
          TMap.find observer (lp_pop_ts p)) ->
      (forall observer, actor <> observer ->
        TMap.find observer (ts_pending tss) =
        TMap.find observer (ts_pending tss')) ->
      ts_clock tss <= ts_clock tss' ->
      G actor
        (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          (pair control tss) Delta)
        (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          (pair control tss')
          (ac_image Delta rhof (fun pi => TMap.add actor token pi) Hsteps)).
    Proof.
      intros Hready Hatomic Hvertices Hedges Hsnapshots Hpending Hgarbage
        Hstarts Hts Hts_pending Hclock.
      unfold G.
      refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
        (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))))).
      - intros observer Hneq. apply token_equiv_rely.
        apply token_equiv_image_other. exact Hneq.
      - intros observer Hneq. apply pool_local_equiv_image_foreign.
        intro rho. destruct rho as [p|p pending op].
        + rewrite Hready. unfold pool_local_state.
          rewrite Hpending, Hsnapshots. reflexivity.
        + rewrite Hatomic. reflexivity.
      - intros observer loc lower Hneq Hcausal rho pi Himage.
        destruct (ac_image_elim _ _ _ _ _ _ Himage) as
          (rho0 & pi0 & Hposs & -> & ->).
        destruct (Hcausal _ _ Hposs) as (p & -> & Hpending_p & Hbefore).
        rewrite Hready. exists (f p). split; [reflexivity|].
        split; [rewrite Hpending; exact Hpending_p|].
        unfold outgoing_before, concrete_array, array_payload in *.
        simpl in *. rewrite Hedges. exact Hbefore.
      - intros observer Hneq. reflexivity.
      - intros observer Hneq. simpl. now apply Hts_pending.
      - intros observer Hneq done candidate Hview'.
        unfold candidate_view in *.
        destruct Hview' as
          (p & pi & N & Hposs & Htoken & Hsnapshot & Hvalue & Hdone & Hstatus &
            Hsafe).
        exists (f p), (TMap.add actor token pi), N.
        split.
        { rewrite <- Hready. constructor. exact Hposs. }
        split.
        { rewrite TMap.gso by congruence. exact Htoken. }
        split; [rewrite Hsnapshots; exact Hsnapshot|].
        split; [rewrite Hvertices; exact Hvalue|].
        split; [exact Hdone|].
        split.
        { unfold visited_top in *. rewrite Hgarbage, Hedges. exact Hstatus. }
        { unfold candidate_tstop_safe in *.
          destruct (candidate_timestamp candidate); [|exact Hsafe].
          rewrite Hgarbage, Hedges. exact Hsafe. }
      - intros observer Hneq owner saved Hview'.
        unfold row_snapshot_view in *.
        destruct Hview' as
          (p & pi & N & Hposs & Htoken & Hsnapshot & Hsaved & Hlive & Horder).
        exists (f p), (TMap.add actor token pi), N.
        split.
        { rewrite <- Hready. constructor. exact Hposs. }
        split.
        { rewrite TMap.gso by congruence. exact Htoken. }
        split; [rewrite Hsnapshots; exact Hsnapshot|].
        split; [exact Hsaved|].
        rewrite Hgarbage, Hedges. split; assumption.
      - apply array_evolves_same_array. reflexivity.
      - simpl. exact Hclock.
      - intros observer Hneq done candidate owner saved Hview'.
        unfold candidate_row_view in *.
        destruct Hview' as
          (p & pi & N & Hposs & Htoken & Hsnapshot & Hvalue & Hdone &
            Hstatus & Hcovered & Horder & Hsafe).
        exists (f p), (TMap.add actor token pi), N.
        split.
        { rewrite <- Hready. constructor. exact Hposs. }
        split.
        { rewrite TMap.gso by congruence. exact Htoken. }
        split; [rewrite Hsnapshots; exact Hsnapshot|].
        split; [rewrite Hvertices; exact Hvalue|].
        split; [exact Hdone|].
        split.
        { unfold visited_top in *. rewrite Hgarbage, Hedges. exact Hstatus. }
        split; [rewrite Hgarbage; exact Hcovered|].
        split; [rewrite Hgarbage, Hedges; exact Horder|].
        unfold candidate_tstop_safe in *.
        destruct (candidate_timestamp candidate); [|exact Hsafe].
        rewrite Hgarbage, Hedges. exact Hsafe.
      - intros observer Hneq progress start0 Hinside Hfallback Hsession_all
          Hcuts n value Hlive Hvalue Hnotignored.
        destruct (Hcuts n value Hlive Hvalue Hnotignored) as
          (p & pi & N & Hposs & Htoken & Hsnapshot & Hnode_value & Hmember &
            Hcut).
        exists (f p), (TMap.add actor token pi), N.
        split.
        { rewrite <- Hready. constructor. exact Hposs. }
        split.
        { rewrite TMap.gso by congruence. exact Htoken. }
        split; [rewrite Hsnapshots; exact Hsnapshot|].
        split; [rewrite Hvertices; exact Hnode_value|].
        split; [exact Hmember|].
        rewrite Hgarbage, Hedges. exact Hcut.
      - apply garbage_evolves_same_array. reflexivity.
      - apply intervals_evolve_same_array. reflexivity.
      - intros observer Hneq. apply session_equiv_image_foreign.
        intro rho. destruct rho as [p|p pending op].
        + rewrite Hready. unfold session_state.
          rewrite Hstarts, Hts by exact Hneq. reflexivity.
        + rewrite Hatomic. reflexivity.
    Qed.

    Lemma startPop_timestamp_inv_update actor :
      AssertionsSet.PUpdate (G actor)
        (Build_ThreadEvent actor (InvEv (inr newTS)))
        (Active actor lpool_startPop)
        (StartPopLinearizing actor).
    Proof.
      intros [control tss] Delta [HIpre Hlin] [control' tss'] Hstep.
      simpl in Hstep. destruct Hstep as [Htimestamp_step ->].
      inversion Htimestamp_step; subst; try discriminate.
      injection H as HactorEq. subst actor0.
      destruct HIpre as [Hwf [Hall [Hrect Hcounter]]].
      assert (Hsteps : forall rho pi, Delta rho pi ->
        poss_steps (PossOk rho pi)
          (PossOk (start_pop_rho actor rho)
            (TMap.add actor (ls_lini lpool_startPop) pi))).
      { intros rho pi Hposs.
        destruct (Hall _ _ Hposs) as
          (p & -> & Hpool & Hprotocol & Htimestamp & Hsession).
        apply rt_step. eapply ps_inv.
        - eapply step_startPop_inv. reflexivity.
        - exact (Hlin _ _ Hposs). }
      set (Delta' := ac_image Delta (start_pop_rho actor)
        (fun pi => TMap.add actor (ls_lini lpool_startPop) pi) Hsteps).
      exists Delta'. split; [apply ac_image_subset_steps|]. split.
      - split.
        + split.
          * destruct Hwf as [Hvalid [Hstamped [Hdefined Hstructural]]].
            split; [now apply start_newTS_valid|]. split; [exact Hstamped|].
            split; assumption.
          * split.
            -- intros rho pi Himage. unfold Delta' in Himage.
               destruct (ac_image_elim _ _ _ _ _ _ Himage) as
                 (rho0 & pi0 & Hposs & -> & ->).
               destruct (Hall _ _ Hposs) as
                 (p & -> & Hpool & Hprotocol & Htimestamp & Hsession).
               exists (start_pop_session actor p). split; [reflexivity|].
               split; [exact Hpool|]. split.
               ++ eapply pool_protocol_start_pop_session;
                    [exact Hprotocol|exact (Hlin _ _ Hposs) ].
               ++ split.
                  ** eapply timestamp_pending_edges_start_pop_session;
                       [exact Hprotocol|exact (Hlin _ _ Hposs)|exact Htimestamp].
                  ** eapply session_represents_start_pop_session.
                     --- exact (proj1 (proj2 (proj2 Hwf))).
                     --- exact (proj1 (proj2 Hwf)).
                     --- exact Hpool.
                     --- exact Hsession.
            -- split.
               ++ unfold Delta'. eapply possibility_rectangular_add_image.
                  ** intro p. reflexivity.
                  ** intros rho q Hready. destruct rho; simpl in Hready.
                     --- inversion Hready. eexists; split; reflexivity.
                     --- discriminate.
                  ** apply pool_shared_eq_start_pop_session_compat.
                  ** intros observer p. reflexivity.
                  ** exact Hrect.
               ++ intros observer saved Hpending.
                  destruct (Hcounter observer saved Hpending) as
                    (rho0 & pi0 & start0 & Hposs & Hfind).
                  destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
                  ** pose proof (Hlin rho0 pi0 Hposs) as Hlin_actor.
                     pose proof (eq_trans (eq_sym Hlin_actor) Hfind) as Hstate_eq.
                     first [discriminate Hstate_eq |
                       dependent destruction Hstate_eq].
                  ** exists (start_pop_rho actor rho0),
                       (TMap.add actor (ls_lini lpool_startPop) pi0), start0.
                     split.
                     --- unfold Delta'. constructor. exact Hposs.
                     --- rewrite TMap.gso by congruence. exact Hfind.
        + unfold ALin. intros rho pi Himage. unfold Delta' in Himage.
          destruct (ac_image_elim _ _ _ _ _ _ Himage) as
            (rho0 & pi0 & Hposs & -> & ->). apply TMap.gss.
      - unfold Delta'.
        apply G_session_image with (f := start_pop_session actor).
        + intro p. reflexivity.
        + intros p pending op. reflexivity.
        + intro p. reflexivity.
        + intro p. reflexivity.
        + intro p. reflexivity.
        + intro p. reflexivity.
        + intro p. reflexivity.
        + intros observer p Hneq. simpl. rewrite TMap.gso by congruence.
          reflexivity.
        + intros observer p Hneq. simpl. rewrite TMap.gro by congruence.
          reflexivity.
        + intros observer Hneq. simpl. rewrite TMap.gso by congruence.
          reflexivity.
        + simpl. lia.
    Qed.

    Lemma startPop_timestamp_res_update actor lower upper :
      AssertionsSet.PUpdate (G actor)
        (Build_ThreadEvent actor
          (ResEv (inr newTS) (TSInterval lower upper)))
        (StartPopLinearizing actor)
        (Completed actor lpool_startPop (TSInterval lower upper)).
    Proof.
      intros [control tss] Delta [HIpre Hlin] [control' tss'] Hstep.
      simpl in Hstep. destruct Hstep as [Htimestamp_step ->].
      inversion Htimestamp_step; subst; try discriminate.
      pose proof (f_equal te_tid H1) as HeventActor. simpl in HeventActor.
      subst actor0.
      pose proof (f_equal newTS_response H1) as Hresult.
      simpl in Hresult. inversion Hresult. subst lower0 upper0.
      match goal with
      | Hp : TMap.find actor (ts_pending tss) = Some lower |- _ =>
          rename Hp into Hpending_clock
      end.
      match goal with
      | Hle : lower <= upper |- _ => rename Hle into Hlower_upper
      end.
      destruct HIpre as [Hwf [Hall [Hrect Hcounter]]].
      assert (Hsteps : forall rho pi, Delta rho pi ->
        poss_steps (PossOk rho pi)
          (PossOk (finish_pop_rho actor (TSInterval lower upper) rho)
            (TMap.add actor
              (ls_linr lpool_startPop (TSInterval lower upper)) pi))).
      { intros rho pi Hposs.
        destruct (Hall _ _ Hposs) as
          (p & -> & Hpool & Hprotocol & Htimestamp & Hsession).
        apply rt_step. eapply ps_ret.
        - eapply step_startPop_res. reflexivity.
        - exact (Hlin _ _ Hposs). }
      set (Delta' := ac_image Delta
        (finish_pop_rho actor (TSInterval lower upper))
        (fun pi => TMap.add actor
          (ls_linr lpool_startPop (TSInterval lower upper)) pi) Hsteps).
      exists Delta'. split; [apply ac_image_subset_steps|]. split.
      - split.
        + split.
          * destruct Hwf as [Hvalid [Hstamped [Hdefined Hstructural]]].
            split; [now apply finish_newTS_valid|]. split.
            -- intros n lo hi Hfind. specialize (Hstamped n lo hi Hfind).
               simpl. eapply Nat.le_trans; [exact Hstamped|].
               apply Nat.le_max_l.
            -- split; assumption.
          * split.
            -- intros rho pi Himage. unfold Delta' in Himage.
               destruct (ac_image_elim _ _ _ _ _ _ Himage) as
                 (rho0 & pi0 & Hposs & -> & ->).
               destruct (Hall _ _ Hposs) as
                 (p & -> & Hpool & Hprotocol & Htimestamp & Hsession).
               pose proof (Hlin _ _ Hposs) as Htoken.
               destruct (proj1 (proj2 (proj2 (proj2 (proj2 Hprotocol))))
                 actor Htoken) as [Hts_none Hstarts_actor].
               exists (finish_pop_session actor (TSInterval lower upper) p).
               split; [reflexivity|]. split; [exact Hpool|]. split.
               ++ eapply pool_protocol_finish_pop_session;
                    [exact Hprotocol|exact Htoken].
               ++ split.
                  ** eapply timestamp_pending_edges_finish_pop_session.
                     exact Htimestamp.
                  ** eapply session_represents_finish_pop_session.
                     --- exact Hpending_clock.
                     --- exact Hlower_upper.
                     --- exact Hts_none.
                     --- exact Hstarts_actor.
                     --- exact Hsession.
            -- split.
               ++ unfold Delta'. eapply possibility_rectangular_add_image.
                  ** intro p. reflexivity.
                  ** intros rho q Hready. destruct rho; simpl in Hready.
                     --- inversion Hready. eexists; split; reflexivity.
                     --- discriminate.
                  ** apply pool_shared_eq_finish_pop_session_compat.
                  ** intros observer p. reflexivity.
                  ** exact Hrect.
               ++ intros observer saved Hpending.
                  destruct (Hcounter observer saved Hpending) as
                    (rho0 & pi0 & start0 & Hposs & Hfind).
                  destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
                  ** pose proof (Hlin rho0 pi0 Hposs) as Hlin_actor.
                     pose proof (eq_trans (eq_sym Hlin_actor) Hfind) as Hstate_eq.
                     first [discriminate Hstate_eq |
                       dependent destruction Hstate_eq].
                  ** exists (finish_pop_rho actor (TSInterval lower upper) rho0),
                       (TMap.add actor
                         (ls_linr lpool_startPop (TSInterval lower upper)) pi0),
                       start0.
                     split.
                     --- unfold Delta'. constructor. exact Hposs.
                     --- rewrite TMap.gso by congruence. exact Hfind.
        + unfold ALin. intros rho pi Himage. unfold Delta' in Himage.
          destruct (ac_image_elim _ _ _ _ _ _ Himage) as
            (rho0 & pi0 & Hposs & -> & ->). apply TMap.gss.
      - unfold Delta'.
        apply G_session_image
          with (f := finish_pop_session actor (TSInterval lower upper)).
        + intro p. reflexivity.
        + intros p pending op. reflexivity.
        + intro p. reflexivity.
        + intro p. reflexivity.
        + intro p. reflexivity.
        + intro p. reflexivity.
        + intro p. reflexivity.
        + intros observer p Hneq. reflexivity.
        + intros observer p Hneq. simpl. rewrite TMap.gso by congruence.
          reflexivity.
        + intros observer Hneq. simpl. rewrite TMap.gro by congruence.
          reflexivity.
        + simpl. apply Nat.le_max_l.
    Qed.

    Definition StartPopResult actor (ts : TS) : assertion :=
      match ts with
      | TSTop => FalseA
      | TSInterval lower upper =>
          Completed actor lpool_startPop (TSInterval lower upper)
      end.

    Lemma start_pop_result_entails_I actor ts :
      ⊨ StartPopResult actor ts ==>> I.
    Proof.
      destruct ts as [|lower upper]; simpl.
      - apply falseA_entails_I.
      - apply completed_entails_I.
    Qed.

    Lemma start_pop_result_stable actor ts :
      AssertionsSet.A.Stable (R actor) I (StartPopResult actor ts).
    Proof.
      destruct ts as [|lower upper]; simpl.
      - apply falseA_stable.
      - apply completed_stable.
    Qed.

    Lemma startPop_timestamp_any_res_update actor ts :
      AssertionsSet.PUpdate (G actor)
        (Build_ThreadEvent actor (ResEv (inr newTS) ts))
        (StartPopLinearizing actor)
        (StartPopResult actor ts).
    Proof.
      destruct ts as [|lower upper].
      - intros [control tss] Delta Hpre [control' tss'] Hstep.
        simpl in Hstep. destruct Hstep as [Htimestamp_step ->].
        inversion Htimestamp_step; subst; try discriminate.
        pose proof (f_equal newTS_response H1) as Hresult.
        simpl in Hresult. discriminate.
      - apply startPop_timestamp_res_update.
    Qed.

    Lemma startPop_method_triple actor :
      SetLogic.HTripleProvable (R actor) (G actor) I actor
        (Active actor lpool_startPop)
        (startPop_impl D actor)
        (fun ret => Completed actor lpool_startPop ret).
    Proof.
      unfold startPop_impl.
      eapply SetLogic.provable_vis_safe with
        (P' := StartPopLinearizing actor)
        (Q' := fun ts => StartPopResult actor ts).
      - intros [[control tss] Delta] Hpre Herror. exact Herror.
      - apply start_pop_linearizing_entails_I.
      - intros. apply start_pop_result_entails_I.
      - apply start_pop_linearizing_stable.
      - intros. apply start_pop_result_stable.
      - apply startPop_timestamp_inv_update.
      - intros ts. apply startPop_timestamp_any_res_update.
      - intros [|lower upper].
        + apply false_triple.
          * intros. apply completed_entails_I.
          * intros. apply completed_stable.
        + eapply SetLogic.provable_ret_safe.
          * apply ImplRefl.
          * apply completed_entails_I.
          * apply completed_stable.
    Qed.

    Section GetTop.
      Variable start : TS.

    (** The scanning thread's own paper-style [⊕] fork: the left family
        retains the unlinearized getTop possibilities, while the right
        family takes the interval invocation (with the caller's session
        token) and records a pool snapshot.  It is the generic fork
        restricted to the actor's own token. *)
    Definition ac_optional_snapshot
        (Delta : @AbstractConfig _ (li_lts F)) (actor : tid) :
        @AbstractConfig _ (li_lts F) :=
      ac_fork_snapshot Delta actor (fun s => s = start).

    Lemma ac_optional_snapshot_keep
        (Delta : @AbstractConfig _ (li_lts F)) (actor : tid)
        (rho : abstract_state) (pi : tmap (@LinState (li_sig F))) :
      Delta rho pi -> ac_optional_snapshot Delta actor rho pi.
    Proof. apply ac_fork_snapshot_keep. Qed.

    Lemma ac_optional_snapshot_take
        (Delta : @AbstractConfig _ (li_lts F)) (actor : tid)
        (p : @ListPoolState A) (pi : tmap (@LinState (li_sig F))) :
      Delta (LPReady p) pi ->
      TMap.find actor pi = Some (ls_inv (lpool_getTop start)) ->
      TMap.find actor (lp_pop_ts p) = Some start ->
      TMap.find actor (lp_snapshots p) = None ->
      ac_optional_snapshot Delta actor
        (LPReady (start_snapshot actor p)) (snapshot_tokens actor start pi).
    Proof.
      intros Hposs Htoken Hsession Hnone.
      exact (ac_fork_snapshot_take Delta actor (fun s => s = start) start p pi
        Hposs eq_refl Htoken Hsession Hnone).
    Qed.

    Lemma ac_optional_snapshot_cases
        (Delta : @AbstractConfig _ (li_lts F)) (actor : tid)
        (rho : abstract_state) (pi : tmap (@LinState (li_sig F))) :
      ac_optional_snapshot Delta actor rho pi ->
      Delta rho pi \/
      exists p pi0,
        Delta (LPReady p) pi0 /\
        TMap.find actor pi0 = Some (ls_inv (lpool_getTop start)) /\
        TMap.find actor (lp_pop_ts p) = Some start /\
        TMap.find actor (lp_snapshots p) = None /\
        rho = LPReady (start_snapshot actor p) /\
        pi = snapshot_tokens actor start pi0.
    Proof.
      intro Hfork.
      destruct (ac_fork_snapshot_cases _ _ _ _ _ Hfork) as [Hkeep|Htake];
        [now left|right].
      destruct Htake as
        (p & pi0 & start0 & Hposs & Hok & Htoken & Hsession & Hnone & Hrho &
          Hpi).
      subst start0. exists p, pi0. repeat split; auto.
    Qed.

    Lemma ac_optional_snapshot_subset_steps
        (Delta : @AbstractConfig _ (li_lts F)) (actor : tid) :
      ac_subset (ac_optional_snapshot Delta actor) (ac_steps Delta).
    Proof. apply ac_fork_snapshot_subset_steps. Qed.

    Lemma token_rely_optional_snapshot
        (Delta : @AbstractConfig _ (li_lts F)) (actor : tid) :
      token_rely actor Delta (ac_optional_snapshot Delta actor).
    Proof. apply token_rely_fork_snapshot. Qed.

    Lemma token_equiv_optional_snapshot_foreign
        (Delta : @AbstractConfig _ (li_lts F)) (actor observer : tid) :
      actor <> observer ->
      token_equiv observer Delta (ac_optional_snapshot Delta actor).
    Proof. apply token_equiv_fork_snapshot_foreign. Qed.

    Lemma pool_local_equiv_optional_snapshot_foreign
        (Delta : @AbstractConfig _ (li_lts F)) (actor observer : tid) :
      actor <> observer ->
      pool_local_equiv observer Delta (ac_optional_snapshot Delta actor).
    Proof. intro Hneq. apply pool_local_equiv_fork_snapshot. Qed.

    Lemma pool_local_equiv_trans observer Delta1 Delta2 Delta3 :
      pool_local_equiv observer Delta1 Delta2 ->
      pool_local_equiv observer Delta2 Delta3 ->
      pool_local_equiv observer Delta1 Delta3.
    Proof.
      intros [H12keep H12new] [H23keep H23new]. split.
      - intros local Hview. now apply H23keep, H12keep.
      - intros local3 Hview3.
        destruct (H23new _ Hview3) as (local2 & Hview2 & Hfst23).
        destruct (H12new _ Hview2) as (local1 & Hview1 & Hfst12).
        exists local1. split; [exact Hview1|congruence].
    Qed.

    Lemma pool_local_equiv_optional_snapshot
        (Delta : @AbstractConfig _ (li_lts F)) (actor observer : tid) :
      pool_local_equiv observer Delta (ac_optional_snapshot Delta actor).
    Proof. apply pool_local_equiv_fork_snapshot. Qed.

    Lemma I_optional_snapshot (sigma : concrete_state)
        (Delta : @AbstractConfig _ (li_lts F)) (actor : tid) :
      I (sigma, Delta) -> I (sigma, ac_optional_snapshot Delta actor).
    Proof. apply I_fork_snapshot. Qed.

    Lemma session_equiv_optional_snapshot
        (Delta : @AbstractConfig _ (li_lts F)) (observer actor : tid) :
      session_equiv observer Delta (ac_optional_snapshot Delta actor).
    Proof. apply session_equiv_fork_snapshot. Qed.

    (** The uniform session facts of the scanning thread survive its own
        snapshot fork. *)
    Lemma session_token_optional_snapshot sigma sigma'
        (Delta : @AbstractConfig _ (li_lts F)) (actor : tid) :
      SessionToken actor start
        (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          sigma Delta) ->
      SessionToken actor start
        (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          sigma' (ac_optional_snapshot Delta actor)).
    Proof.
      intros Hall. eapply session_token_stable; [|exact Hall].
      apply session_equiv_optional_snapshot.
    Qed.

    Definition array_reset_inv_kind
        (ev : @ThreadEvent (@ESPListArray A)) : bool :=
      match te_ev ev with
      | InvEv array_resetIter => true
      | _ => false
      end.

    Definition array_reset_res_kind
        (ev : @ThreadEvent (@ESPListArray A)) : bool :=
      match te_ev ev with
      | ResEv array_resetIter _ => true
      | _ => false
      end.

    Lemma array_reset_inv_shape actor control control' :
      @StepSPListArray A D
        (Build_ThreadEvent actor (InvEv array_resetIter))
        control control' ->
      exists a,
        control = ArrayReady a /\
        control' = ArrayAtomicPending a actor array_resetIter /\
        ThreadDomain.contains D actor.
    Proof.
      intro Hstep. remember (Build_ThreadEvent actor
        (InvEv array_resetIter)) as ev eqn:Hev in Hstep.
      inversion Hstep.
      all: match goal with
        | Hctor : ?remembered = ?rhs,
          Htarget : ?remembered = ?target |- _ =>
            let Hevent := fresh "Hevent" in
            pose proof (eq_trans (eq_sym Htarget) Hctor) as Hevent;
            let Hkind := fresh "Hkind" in
            pose proof (f_equal array_reset_inv_kind Hevent) as Hkind;
            cbv [array_reset_inv_kind] in Hkind;
            first [discriminate Hkind |
              dependent destruction Hevent;
              eexists; split; [reflexivity|]; split;
              [reflexivity|eassumption]]
        end.
    Qed.

    Lemma array_reset_res_shape actor control control' :
      @StepSPListArray A D
        (Build_ThreadEvent actor (ResEv array_resetIter tt))
        control control' ->
      exists a,
        control = ArrayAtomicPending a actor array_resetIter /\
        control' = ArrayReady (reset_scan actor a).
    Proof.
      intro Hstep. remember (Build_ThreadEvent actor
        (ResEv array_resetIter tt)) as ev eqn:Hev in Hstep.
      inversion Hstep.
      all: match goal with
        | Hctor : ?remembered = ?rhs,
          Htarget : ?remembered = ?target |- _ =>
            let Hevent := fresh "Hevent" in
            pose proof (eq_trans (eq_sym Htarget) Hctor) as Hevent;
            let Hkind := fresh "Hkind" in
            pose proof (f_equal array_reset_res_kind Hevent) as Hkind;
            cbv [array_reset_res_kind] in Hkind;
            first [discriminate Hkind |
              dependent destruction Hevent;
              eexists; split; reflexivity]
        end.
    Qed.

    Lemma concrete_wf_reset_scan (a : @SPListArrayState A)
        tss actor :
      concrete_wf (pair (ArrayAtomicPending a actor array_resetIter) tss) ->
      concrete_wf (pair (ArrayReady (reset_scan actor a)) tss).
    Proof.
      unfold concrete_wf, concrete_array, concrete_timestamp, array_payload.
      simpl. intros (Hvalid & Hstamped & Hdefined & Hstructural).
      split; [exact Hvalid|]. split; [exact Hstamped|].
      split; assumption.
    Qed.

    Lemma pool_represents_reset_scan (a : @SPListArrayState A) p actor :
      pool_represents a p -> pool_represents (reset_scan actor a) p.
    Proof.
      unfold pool_represents, reset_scan. simpl. tauto.
    Qed.

    Lemma timestamp_pending_edges_reset_scan
        (a : @SPListArrayState A) tss p actor :
      timestamp_pending_edges
        (pair (ArrayAtomicPending a actor array_resetIter) tss) p ->
      timestamp_pending_edges
        (pair (ArrayReady (reset_scan actor a)) tss) p.
    Proof.
      unfold timestamp_pending_edges, concrete_array, concrete_timestamp,
        array_payload, reset_scan. simpl. tauto.
    Qed.

    Lemma timestamp_pending_edges_start_snapshot
        (s : concrete_state) p actor :
      timestamp_pending_edges s p ->
      timestamp_pending_edges s (start_snapshot actor p).
    Proof.
      unfold timestamp_pending_edges, outgoing_before, start_snapshot.
      simpl. tauto.
    Qed.

    Definition SnapshotExists (actor : tid) : assertion :=
      fun w => exists N local,
        snd local = Some N /\
        pool_local_view actor (SetPossState.Δ w) local.

    Definition GetTopActor (actor : tid) : assertion :=
      fun w => I w /\
        actor ↦∃◦((lpool_getTop start)) w /\
        ThreadDomain.contains D actor /\
        TMap.find actor
          (as_pending_counters
            (concrete_array (SetPossState.σ w))) = None /\
        SessionToken actor start w.

    Definition GetTopReset (actor : tid) : assertion :=
      fun w =>
        I w /\
        ThreadDomain.contains D actor /\
        TMap.find actor
          (as_pending_counters
            (concrete_array (SetPossState.σ w))) = None /\
        TMap.find actor
          (as_scans (concrete_array (SetPossState.σ w))) = Some empty_scan /\
        actor ↦∃◦((lpool_getTop start)) w /\
        actor ↦∃•((lpool_getTop start)) w /\
        SnapshotExists actor w /\
        node_cuts_available actor empty_scan
          (concrete_array (SetPossState.σ w)) (SetPossState.Δ w) /\
        SessionToken actor start w.

    Lemma getTop_actor_entails_I actor : ⊨ GetTopActor actor ==>> I.
    Proof. intros w [HI [Hlin Hactor]]. exact HI. Qed.

    Lemma getTop_actor_stable actor :
      AssertionsSet.A.Stable (R actor) I (GetTopActor actor).
    Proof.
      unfold GetTopActor. intros w
        [[pre [[HIpre [Hlin [Hactor [Hcounter_none Hsession_token]]]] HR]] HI'].
      destruct HR as
        (Htoken & Hlocal & Hcausal & Harray_local & Hpending & Hcandidate &
          Hrow & Hevolve & Hclock & Haligned & Hcuts_pres & Hgarbage &
          Hintervals & Hsession_equiv).
      destruct w as [sigma' Delta'].
      destruct pre as [sigma Delta]. simpl in *.
      split; [exact HI'|]. split.
      - eapply token_rely_ALinExists with
          (Delta := Delta) (Delta' := Delta'); eauto.
      - split; [exact Hactor|]. split.
        + unfold array_local_state in Harray_local.
          pose proof (f_equal snd Harray_local) as Hcounter_eq.
          simpl in Hcounter_eq. congruence.
        + eapply session_token_stable; [exact Hsession_equiv|exact Hsession_token].
    Qed.

    Lemma getTop_reset_entails_I actor : ⊨ GetTopReset actor ==>> I.
    Proof. firstorder. Qed.

    Lemma getTop_reset_stable actor :
      AssertionsSet.A.Stable (R actor) I (GetTopReset actor).
    Proof.
      unfold AssertionsSet.A.Stable, AssertionsSet.A.ComposeA,
        GetTopReset, R.
      intros w [Hcompose HI'].
      destruct Hcompose as [pre [Hpre HR]].
      destruct Hpre as
        (HI & Hactor & Hcounter_none & Hscan & Hfallback & Hsnapshot_token &
          Hsnapshot & Hcuts & Hsession_token).
      destruct HR as
        (Htoken & Hlocal & Hcausal & Harray_local & Hpending & Hcandidate &
          Hrow & Hevolve & Hclock & Haligned & Hcuts_pres & Hgarbage &
          Hintervals & Hsession_equiv).
      destruct w as [sigma' Delta'].
      destruct pre as [sigma Delta]. simpl in *.
      split; [exact HI'|]. split; [exact Hactor|]. split.
      - unfold array_local_state in Harray_local.
        pose proof (f_equal snd Harray_local) as Hcounter_eq.
        simpl in Hcounter_eq. congruence.
      - split.
        + unfold array_local_state in Harray_local.
          pose proof (f_equal fst Harray_local) as Hscan_eq.
          simpl in Hscan_eq. exact (eq_trans (eq_sym Hscan_eq) Hscan).
        + split.
          * eapply token_rely_ALinExists; eauto.
          * split.
            -- eapply token_rely_ALinExists; eauto.
            -- split.
               ++ destruct Hsnapshot as (N & local & Hsnd & Hview).
                  exists N, local. split; [exact Hsnd|].
                  now apply (proj1 Hlocal).
               ++ split.
                  ** eapply Hcuts_pres; [exact Hactor| |exact Hsession_token|exact Hcuts].
                     apply (proj2 (token_view_ALinExists sigma actor Delta _)).
                     exact Hfallback.
                  ** eapply session_token_stable;
                       [exact Hsession_equiv|exact Hsession_token].
    Qed.

    Lemma getTop_actor_no_error actor :
      ⊨ GetTopActor actor ==>>
        AssertionsSet.A.ANoError
          (Build_ThreadEvent actor (InvEv (inl array_resetIter))).
    Proof.
      intros [[control tss] Delta]
        [HI [Hlin [Hactor [Hcounter_none Hsession_token]]]] Herror.
      simpl in Herror.
      remember (Build_ThreadEvent actor (InvEv array_resetIter))
        as ev eqn:Hev in Herror.
      inversion Herror.
      all: try match goal with
        | Hctor : ?lhs = ?remembered,
          Htarget : ?remembered = ?target |- _ =>
            let Hevent := fresh "Hevent" in
            pose proof (eq_trans Hctor Htarget) as Hevent;
            let Hkind := fresh "Hkind" in
            pose proof (f_equal array_reset_inv_kind Hevent) as Hkind;
            cbv [array_reset_inv_kind] in Hkind;
            first [discriminate Hkind |
              dependent destruction Hevent; contradiction]
        end.
    Qed.

    Lemma getTop_reset_inv_update actor :
      AssertionsSet.PUpdate (G actor)
        (Build_ThreadEvent actor (InvEv (inl array_resetIter)))
        (GetTopActor actor) (GetTopActor actor).
    Proof.
      intros [control tss] Delta Hpre [control' tss'] Hstep.
      simpl in Hstep. destruct Hstep as [Harray ->].
      destruct (array_reset_inv_shape actor _ _ Harray)
        as (a & -> & -> & Hactor).
      exists Delta. split; [apply ac_steps_refl|]. split.
      - destruct Hpre as [HI [Hlin [Hinside Hcounter_none]]].
        split.
        + unfold I in *. simpl in *. exact HI.
        + split.
          * apply (proj1 (token_view_ALinExists
              (pair (ArrayAtomicPending a actor array_resetIter) tss')
              actor Delta _)).
            apply (proj2 (token_view_ALinExists
              (pair (ArrayReady a) tss') actor Delta _)).
            exact Hlin.
          * split; [exact Hinside|exact Hcounter_none].
      - unfold G. split.
        + intros observer Hneq. apply token_rely_refl.
        + split.
          * intros observer Hneq. apply pool_local_equiv_refl.
          * split.
            -- intros observer loc lower Hneq Hcausal. exact Hcausal.
            -- split.
               ++ intros observer Hneq. reflexivity.
               ++ split.
                  ** intros observer Hneq. reflexivity.
                  ** split.
                     --- intros observer Hneq.
                         apply candidate_views_preserved_refl.
                     --- split.
                         +++ intros observer Hneq.
                             apply row_snapshot_views_preserved_refl.
                         +++ split.
                             *** apply array_evolves_same_array. reflexivity.
                             *** split; [simpl; lia|].
                                 split.
                                 ++++ intros observer Hneq.
                                      apply candidate_row_views_preserved_refl.
                                 ++++ split.
                                      ***** intros observer Hneq.
                                            apply node_cuts_preserved_same_array;
                                              reflexivity.
                                      ***** split.
                                            ------ apply garbage_evolves_same_array.
                                                   reflexivity.
                                            ------ split.
                                                   { apply intervals_evolve_same_array.
                                                     reflexivity. }
                                                   { intros observer Hneq.
                                                     apply session_equiv_refl. }
    Qed.

    Lemma getTop_reset_res_update actor :
      AssertionsSet.PUpdate (G actor)
        (Build_ThreadEvent actor (ResEv (inl array_resetIter) tt))
        (GetTopActor actor) (GetTopReset actor).
    Proof.
      intros [control tss] Delta
        [HIpre [Hlin [Hactor [Hcounter_none Hsession_token]]]]
        [control' tss'] Hstep.
      simpl in Hstep. destruct Hstep as [Harray ->].
      destruct (array_reset_res_shape actor _ _ Harray)
        as (a & -> & ->).
      destruct HIpre as [Hwf [Hall Hrect]].
      pose proof (proj2 (token_view_ALinExists
        (pair (ArrayAtomicPending a actor array_resetIter) tss')
        actor Delta (ls_inv (lpool_getTop start))) Hlin) as Hseed_view.
      destruct Hseed_view as
        (rho_seed & pi_seed & Hseed & Hseed_token).
      destruct (Hall _ _ Hseed) as
        (p_seed & -> & Hpool_seed & Hprotocol_seed & Htimestamp_seed).
      assert (Hseed_none :
        TMap.find actor (lp_snapshots p_seed) = None).
      { destruct (TMap.find actor (lp_snapshots p_seed))
          as [N|] eqn:Hfind; [|reflexivity].
        destruct (proj1 (proj2 Hprotocol_seed) _ _ Hfind) as [start1 Htoken].
        rewrite Hseed_token in Htoken. discriminate. }
      assert (Hseed_session : TMap.find actor (lp_pop_ts p_seed) = Some start)
        by exact (Hsession_token _ _ Hseed).
      set (Delta' := ac_optional_snapshot Delta actor).
      exists Delta'. split.
      - apply ac_optional_snapshot_subset_steps.
      - split.
        + unfold GetTopReset. split.
          * split.
            -- now apply concrete_wf_reset_scan.
            -- split.
               ++ intros rho pi Hfork.
                  destruct (ac_optional_snapshot_cases _ _ _ _ Hfork)
                    as [Hkeep|Hsnapshot].
                  ** destruct (Hall _ _ Hkeep) as
                       (p & -> & Hpool & Hprotocol & Htimestamp & Hsession).
                     exists p. split; [reflexivity|]. split.
                     --- now apply pool_represents_reset_scan.
                     --- split; [exact Hprotocol|].
                         split; [now apply timestamp_pending_edges_reset_scan|exact Hsession].
                  ** destruct Hsnapshot as
                       [p [pi0 [Hposs [Htoken [Hsession0 [Hnone [Hrho Hpi]]]]]]].
                     destruct (Hall _ _ Hposs) as
                       (p0 & Heq & Hpool & Hprotocol & Htimestamp & Hsession).
                     inversion Heq; subst p0. subst rho pi.
                     exists (start_snapshot actor p). split; [reflexivity|].
                     split.
                     --- apply pool_represents_reset_scan.
                         now apply pool_represents_start_snapshot.
                     --- split.
                         +++ apply pool_protocol_start_snapshot.
                             *** exact Hprotocol.
                             *** exact Htoken.
                             *** exact Hsession0.
                             *** exact Hnone.
                         +++ split.
                             *** apply timestamp_pending_edges_reset_scan.
                                 now apply timestamp_pending_edges_start_snapshot.
                             *** exact Hsession.
               ++ unfold Delta'.
                  pose proof (I_optional_snapshot
                    (pair (ArrayAtomicPending a actor array_resetIter) tss')
                    Delta actor (conj Hwf (conj Hall Hrect))) as Hoptional.
                  exact (proj2 (proj2 Hoptional)).
          * split; [exact Hactor|].
            split.
            { unfold concrete_array, array_payload, reset_scan in *.
              simpl in *. exact Hcounter_none. }
            split.
            { unfold concrete_array, array_payload, reset_scan. simpl.
              apply TMap.gss. }
            split.
            { apply (proj1 (token_view_ALinExists
                (pair (ArrayReady (reset_scan actor a)) tss')
                actor Delta' (ls_inv (lpool_getTop start)))).
              exists (LPReady p_seed), pi_seed. split.
              - unfold Delta'. now apply ac_optional_snapshot_keep.
              - exact Hseed_token. }
            split.
            { apply (proj1 (token_view_ALinExists
                (pair (ArrayReady (reset_scan actor a)) tss')
                actor Delta' (ls_lini (lpool_getTop start)))).
              exists (LPReady (start_snapshot actor p_seed)),
                (snapshot_tokens actor start pi_seed). split.
              - unfold Delta'. eapply ac_optional_snapshot_take; eassumption.
              - unfold snapshot_tokens. apply TMap.gss. }
            split.
            { unfold SnapshotExists.
              exists (fun n => is_vertex p_seed n),
                (pool_local_state actor
                  (LPReady (start_snapshot actor p_seed))). split.
              - simpl. rewrite TMap.gss. reflexivity.
              - exists (LPReady (start_snapshot actor p_seed)),
                  (snapshot_tokens actor start pi_seed). split.
                + simpl. unfold Delta'.
                  eapply ac_optional_snapshot_take; eassumption.
                + reflexivity. }
            split.
            { unfold node_cuts_available, concrete_array,
                array_payload, reset_scan. simpl.
              intros n value Hlive Hvalue Hnotignored.
              exists (start_snapshot actor p_seed),
                (snapshot_tokens actor start pi_seed),
                (fun node => is_vertex p_seed node).
              repeat split.
              - unfold Delta'. eapply ac_optional_snapshot_take; eassumption.
              - exists start. unfold snapshot_tokens. apply TMap.gss.
              - simpl. apply TMap.gss.
              - simpl. rewrite (proj1 Hpool_seed). exact Hvalue.
              - unfold is_vertex. rewrite (proj1 Hpool_seed).
                exact (proj1 Hlive).
              - intros newer Hnewer Hnewer_live Hedge.
                apply empty_scan_not_ignored. }
            { unfold Delta'. eapply session_token_optional_snapshot.
              exact Hsession_token. }
        + unfold G. split.
          * intros observer Hneq. unfold Delta'.
            apply token_equiv_rely.
            now apply token_equiv_optional_snapshot_foreign.
          * split.
            -- intros observer Hneq. unfold Delta'.
               now apply pool_local_equiv_optional_snapshot_foreign.
            -- split.
               ++ intros observer loc lower Hneq Hcausal rho pi Hfork.
                  destruct (ac_optional_snapshot_cases _ _ _ _ Hfork)
                    as [Hkeep|Hsnapshot].
                  ** destruct (Hcausal _ _ Hkeep) as
                       (p & -> & Hpending & Hbefore).
                     exists p. split; [reflexivity|]. split; [exact Hpending|].
                     unfold outgoing_before in *. simpl in *. exact Hbefore.
                  ** destruct Hsnapshot as
                       [p [pi0 [Hposs [Htoken [Hsession0 [Hnone [Hrho Hpi]]]]]]].
                     destruct (Hcausal _ _ Hposs) as
                       (p0 & Heq & Hpending & Hbefore).
                     inversion Heq; subst p0. subst rho pi.
                     exists (start_snapshot actor p). split; [reflexivity|].
                     split.
                     --- exact Hpending.
                     --- unfold outgoing_before in *. simpl in *.
                         exact Hbefore.
               ++ split.
                  ** intros observer Hneq.
                     unfold array_local_state, concrete_array, array_payload,
                       reset_scan. simpl. rewrite TMap.gso by congruence.
                     reflexivity.
                  ** split.
                     --- intros observer Hneq. reflexivity.
                     --- split.
                         +++ intros observer Hneq done candidate Hview.
                             unfold candidate_view in *.
                             destruct Hview as
                               (p & pi & N & Hposs & Htoken & Hsnapshot &
                                 Hvalue & Hdone & Hstatus & Hsafe).
                             exists p, pi, N. repeat split; try assumption.
                             unfold Delta'. now apply ac_optional_snapshot_keep.
                         +++ split.
                             *** intros observer Hneq owner saved Hview.
                                 unfold row_snapshot_view in *.
                                 destruct Hview as
                                   (p & pi & N & Hposs & Htoken & Hsnapshot &
                                     Hsaved & Hlive & Horder).
                                 exists p, pi, N. repeat split; try assumption.
                                 unfold Delta'.
                                 now apply ac_optional_snapshot_keep.
                             *** split.
                                 ++++ eapply array_evolves_of_counter_order;
                                        intro q; reflexivity.
                                 ++++ split; [simpl; lia|].
                                      split.
                                      ***** intros observer Hneq.
                                            eapply
                                              candidate_row_views_preserved_mono.
                                            intros rho pi Hposs. unfold Delta'.
                                            now apply
                                              ac_optional_snapshot_keep.
                                      ***** split.
                                            ------ intros observer Hneq progress start0
                                                   Hinside Hfallback Hsession_all Hcuts n value
                                                   Hlive Hvalue Hnotignored.
                                                   unfold concrete_array,
                                                     array_payload, reset_scan
                                                     in Hlive, Hvalue.
                                                   simpl in Hlive, Hvalue.
                                                   destruct (Hcuts n value Hlive
                                                     Hvalue Hnotignored) as
                                                     (p & pi & N & Hposs & Htoken &
                                                       Hsnapshot & Hnode_value &
                                                       Hmember & Hcut).
                                                   exists p, pi, N.
                                                   repeat split; try assumption.
                                                   unfold Delta'. now apply
                                                     ac_optional_snapshot_keep.
                                            ------ split.
                                                   +++++++ unfold garbage_evolves,
                                                           concrete_array,
                                                           array_payload,
                                                           reset_scan.
                                                           simpl. firstorder.
                                                   +++++++ split.
                                                           { unfold intervals_evolve,
                                                               concrete_array,
                                                               array_payload,
                                                               reset_scan.
                                                             simpl. firstorder. }
                                                           { intros observer Hneq.
                                                             unfold Delta'.
                                                             apply session_equiv_fork_snapshot. }
    Qed.

    (** Counter algebra used by the empty branch of the paper's loop
        invariant.  It is phrased over [sum_counters], so the assertions
        below retain the same notation and aggregation boundary as Fig. 22. *)
    Lemma sum_counters_monotone (owners : list tid)
        (a a' : @SPListArrayState A) :
      (forall owner, In owner owners ->
        counter_at owner a <= counter_at owner a') ->
      sum_counters owners (as_counters a) <=
        sum_counters owners (as_counters a').
    Proof.
      induction owners as [|owner owners IH]; intro Hle; simpl; [lia|].
      assert (Hhead := Hle owner (or_introl eq_refl)).
      assert (Htail : forall q, In q owners ->
        counter_at q a <= counter_at q a').
      { intros q Hq. apply Hle. now right. }
      specialize (IH Htail).
      unfold counter_at in Hhead. lia.
    Qed.

    Lemma sum_counters_equal_component (owners : list tid)
        (a a' : @SPListArrayState A) :
      (forall owner, In owner owners ->
        counter_at owner a <= counter_at owner a') ->
      sum_counters owners (as_counters a) =
        sum_counters owners (as_counters a') ->
      forall owner, In owner owners ->
        counter_at owner a = counter_at owner a'.
    Proof.
      induction owners as [|head owners IH]; intros Hle Hsum owner Hin;
        simpl in *; [contradiction|].
      assert (Hhead := Hle head (or_introl eq_refl)).
      assert (Htail : forall q, In q owners ->
        counter_at q a <= counter_at q a').
      { intros q Hq. apply Hle. now right. }
      pose proof (sum_counters_monotone owners a a' Htail) as Htails.
      unfold counter_at in Hhead.
      destruct Hin as [->|Hin].
      - unfold counter_at. lia.
      - apply IH; [exact Htail| |exact Hin].
        unfold counter_at in Hsum. lia.
    Qed.

    Lemma sum_counters_snoc owners owner counters :
      sum_counters (owners ++ [owner]) counters =
      Nat.add (sum_counters owners counters)
        match TMap.find owner counters with
        | Some count => count
        | None => 0
        end.
    Proof. induction owners; simpl; lia. Qed.

    Definition EmptyEvidence (done : list tid) (count : nat)
        (a : @SPListArrayState A) : Prop :=
      count <= sum_counters done (as_counters a) /\
      (count = sum_counters done (as_counters a) ->
        forall owner, In owner done -> order_at owner a = nil).

    Lemma empty_evidence_nil (a : @SPListArrayState A) :
      EmptyEvidence nil 0 a.
    Proof.
      split; simpl; [lia|]. intros _ owner Hnone. contradiction.
    Qed.

    Lemma empty_evidence_stable done count
        (s s' : concrete_state) :
      EmptyEvidence done count (concrete_array s) ->
      array_evolves s s' ->
      EmptyEvidence done count (concrete_array s').
    Proof.
      intros [Hbound Hempty] Hevol. split.
      - eapply Nat.le_trans; [exact Hbound|].
        apply sum_counters_monotone. intros owner Howner.
        exact (proj1 (Hevol owner)).
      - intro Heq. intros owner Howner.
        assert (Hmono : sum_counters done
            (as_counters (concrete_array s)) <=
          sum_counters done (as_counters (concrete_array s'))).
        { apply sum_counters_monotone. intros q Hq.
          exact (proj1 (Hevol q)). }
        assert (Holdsum : count = sum_counters done
            (as_counters (concrete_array s))) by lia.
        assert (Hsums : sum_counters done
            (as_counters (concrete_array s)) =
          sum_counters done (as_counters (concrete_array s'))) by lia.
        assert (Hcounter : counter_at owner (concrete_array s) =
          counter_at owner (concrete_array s')).
        { eapply sum_counters_equal_component; [|exact Hsums|exact Howner].
          intros q Hq. exact (proj1 (Hevol q)). }
        specialize (proj2 (Hevol owner) Hcounter) as Hincl.
        specialize (Hempty Holdsum owner Howner).
        destruct (order_at owner (concrete_array s')) as [|loc rest]
          eqn:Horder; [reflexivity|].
        exfalso. specialize (Hincl loc (or_introl eq_refl)).
        rewrite Hempty in Hincl. contradiction.
    Qed.

    Definition scan_seen_wf (progress : ScanProgress) : Prop :=
      forall n, scan_seen progress n ->
        In (fst n) (scan_visited progress).

    Definition seen_garbage (progress : ScanProgress)
        (a : @SPListArrayState A) : Prop :=
      forall n, scan_seen progress n -> as_garbage a n.

    (** Every node accumulated by the concrete iterator keeps a timestamp.
        This is the concrete domain fact needed when a rely step completes a
        formerly-[TSTop] timestamp. *)
    Definition seen_timestamped (progress : ScanProgress)
        (a : @SPListArrayState A) : Prop :=
      forall n, scan_seen progress n ->
        exists ts, as_timestamps a n = Some ts.

    (** [I_loop^r] in timestamp form: the stored candidate is maximal among
        the live nodes already seen by the iterator.  The strict order is the
        paper's timestamp order, so overlapping intervals remain
        incomparable, as required. *)
    Definition candidate_maximal (candidate : @Candidate A)
        (progress : ScanProgress) (a : @SPListArrayState A) : Prop :=
      forall n ts,
        scan_seen progress n ->
        ~ as_garbage a n ->
        as_timestamps a n = Some ts ->
        ~ timestamp_lt (candidate_timestamp candidate) ts.

    Lemma seen_timestamped_stable progress (s s' : concrete_state) :
      seen_timestamped progress (concrete_array s) ->
      intervals_evolve s s' ->
      seen_timestamped progress (concrete_array s').
    Proof.
      intros Hseen [Hdomain _] n Hmember.
      destruct (Hseen n Hmember) as [ts Htimestamp].
      now apply (Hdomain n ts Htimestamp).
    Qed.

    Lemma candidate_maximal_stable candidate progress
        (s s' : concrete_state) :
      seen_timestamped progress (concrete_array s) ->
      candidate_maximal candidate progress (concrete_array s) ->
      garbage_evolves s s' ->
      intervals_evolve s s' ->
      candidate_maximal candidate progress (concrete_array s').
    Proof.
      intros Hseen Hmax Hgarbage [_ [Hintervals _]] n ts Hmember Hlive
        Htimestamp Hlt.
      destruct (candidate_timestamp candidate) as [|candidate_lower
        candidate_upper] eqn:Hcandidate; simpl in Hlt; [contradiction|].
      destruct (Hseen n Hmember) as [old_ts Hold_timestamp].
      assert (Hold_live : ~ as_garbage (concrete_array s) n).
      { intro Hold_garbage. apply Hlive. now apply Hgarbage. }
      specialize (Hmax n old_ts Hmember Hold_live Hold_timestamp).
      rewrite Hcandidate in Hmax.
      destruct old_ts as [|old_lower old_upper].
      - apply Hmax. apply interval_lt_top.
      - pose proof (Hintervals n old_lower old_upper Hold_timestamp)
          as Hpreserved.
        rewrite Htimestamp in Hpreserved. inversion Hpreserved; subst.
        exact (Hmax Hlt).
    Qed.

    Definition row_current (owner : tid) (a : @SPListArrayState A) :
        CurrentScan :=
      {| current_owner := owner;
         current_order := order_at owner a;
         current_counter := counter_at owner a |}.

    Definition visiting_progress (owner : tid) (a : @SPListArrayState A)
        (progress : ScanProgress) : ScanProgress :=
      {| scan_visited := scan_visited progress;
         scan_seen := scan_seen progress;
         scan_current := Some (row_current owner a) |}.

    Lemma not_ignored_before_visiting owner a progress n :
      scan_current progress = None ->
      ~ scan_status (visiting_progress owner a progress) n Ignored ->
      ~ scan_status progress n Ignored.
    Proof.
      intros Hidle Hnew Hold. apply Hnew.
      inversion Hold; subst.
      - now apply scan_status_ignored_visited.
      - rewrite Hidle in H. discriminate.
    Qed.

    Lemma live_not_ignored_while_visiting owner a progress n :
      array_structural_wf a ->
      array_live a n ->
      ~ scan_status progress n Ignored ->
      ~ scan_status (visiting_progress owner a progress) n Ignored.
    Proof.
      intros Hstructural Hlive Hold Hnew.
      inversion Hnew; subst.
      - apply Hold. apply scan_status_ignored_visited; assumption.
      - simpl in H. inversion H; subst c.
        apply H1. unfold current_nodes, row_current. simpl.
        change (owner = fst n) in H0.
        split; [symmetry; exact H0|].
        rewrite H0.
        apply (proj1 (proj1 Hstructural (fst n) (snd n))).
        destruct n. exact Hlive.
    Qed.

    Lemma scan_seen_wf_finish progress current :
      scan_seen_wf progress ->
      scan_seen_wf (finish_progress progress current).
    Proof.
      intros Hwf n [Hold|Hcurrent].
      - apply in_or_app. left. now apply Hwf.
      - apply in_or_app. right. simpl.
        left. symmetry. exact (proj1 Hcurrent).
    Qed.

    Lemma not_ignored_after_finish progress current n :
      scan_current progress = Some current ->
      ~ scan_status progress n Ignored ->
      ~ scan_status (finish_progress progress current) n Ignored.
    Proof.
      intros Hcurrent Hold Hfinished.
      inversion Hfinished; subst.
      - simpl in H, H0. apply in_app_or in H.
        destruct H as [Hvisited|Howner].
        + apply Hold. apply scan_status_ignored_visited.
          * exact Hvisited.
          * intro Hseen. apply H0. now left.
        + simpl in Howner. destruct Howner as [Howner|Hfalse];
            [|contradiction].
          apply Hold. eapply scan_status_ignored_current.
          * exact Hcurrent.
          * exact Howner.
          * intro Hnodes. apply H0. now right.
      - discriminate H.
    Qed.

    Lemma not_ignored_before_finish progress current n :
      scan_current progress = Some current ->
      scan_seen_wf progress ->
      ~ In (current_owner current) (scan_visited progress) ->
      ~ scan_status (finish_progress progress current) n Ignored ->
      ~ scan_status progress n Ignored.
    Proof.
      intros Hcurrent Hseenwf Howner_new Hfinished Hold.
      inversion Hold; subst.
      - destruct (classic (current_nodes current n)) as [Hnodes|Hnotnodes].
        + apply Howner_new. rewrite <- (proj1 Hnodes). exact H.
        + apply Hfinished. apply scan_status_ignored_visited.
          * simpl. apply in_or_app. now left.
          * simpl. intros [Hseen|Hnodes].
            -- now apply H0.
            -- now apply Hnotnodes.
      - assert (c = current) by congruence. subst c.
        apply Hfinished. apply scan_status_ignored_visited.
        + simpl. apply in_or_app. right. simpl. left.
          exact H0.
        + simpl. intros [Hseen|Hnodes].
          * apply Howner_new. rewrite H0. now apply Hseenwf.
          * now apply H1.
    Qed.

    Definition ScanAccumulator (actor : tid) (done : list tid)
        (progress : ScanProgress)
        (scan : @ScanState A) : assertion :=
      fun w =>
        match fst scan with
        | None => EmptyEvidence done (snd scan)
            (concrete_array (SetPossState.σ w)) /\
          seen_garbage progress
            (concrete_array (SetPossState.σ w))
        | Some candidate =>
            candidate_view actor done candidate (SetPossState.Δ w) /\
            candidate_interval_valid candidate
              (concrete_array (SetPossState.σ w)) /\
            candidate_maximal candidate progress
              (concrete_array (SetPossState.σ w))
        end.

    Definition PendingAccumulator (actor owner : tid) (done : list tid)
        (progress : ScanProgress)
        (current : CurrentScan) (scan : @ScanState A) : assertion :=
      fun w =>
        match fst scan with
        | None => EmptyEvidence done (snd scan)
            (concrete_array (SetPossState.σ w)) /\
          seen_garbage progress
            (concrete_array (SetPossState.σ w))
        | Some candidate =>
            candidate_row_view actor done candidate owner
              (current_order current) (SetPossState.Δ w) /\
            candidate_interval_valid candidate
              (concrete_array (SetPossState.σ w)) /\
            candidate_maximal candidate progress
              (concrete_array (SetPossState.σ w))
        end.

    (** [ScanFold actor remaining scan] is the paper's loop assertion,
        indexed by the unvisited suffix.  The two existential token views
        are deliberately retained together: [◦] is the atomic fallback,
        while [•] carries a snapshot possibility for a node result. *)
    Definition ScanFold (actor : tid) (remaining : list tid)
        (scan : @ScanState A) : assertion :=
      fun w =>
        I w /\
        ThreadDomain.contains D actor /\
        TMap.find actor
          (as_pending_counters
            (concrete_array (SetPossState.σ w))) = None /\
        exists done progress,
          ThreadDomain.threads D = done ++ remaining /\
          TMap.find actor
            (as_scans (concrete_array (SetPossState.σ w))) = Some progress /\
          scan_visited progress = done /\
          scan_current progress = None /\
          scan_seen_wf progress /\
          seen_timestamped progress
            (concrete_array (SetPossState.σ w)) /\
          actor ↦∃◦((lpool_getTop start)) w /\
          actor ↦∃•((lpool_getTop start)) w /\
          SnapshotExists actor w /\
          node_cuts_available actor progress
            (concrete_array (SetPossState.σ w)) (SetPossState.Δ w) /\
          ScanAccumulator actor done progress scan w /\
          SessionToken actor start w.

    Lemma scan_fold_entails_I actor remaining scan :
      ⊨ ScanFold actor remaining scan ==>> I.
    Proof. intros w [HI _]. exact HI. Qed.

    Lemma scan_fold_stable actor remaining scan :
      AssertionsSet.A.Stable (R actor) I
        (ScanFold actor remaining scan).
    Proof.
      unfold AssertionsSet.A.Stable, AssertionsSet.A.ComposeA,
        ScanFold, R.
      intros w [Hcompose HI'].
      destruct Hcompose as [pre [Hpre HR]].
      destruct Hpre as [HI [Hactor [Hcounter_none Hrest]]].
      destruct Hrest as
        (done & progress & Hparts & Hscan & Hvisited & Hidle & Hseenwf &
          Hseen_timestamped & Hfallback & Hsnapshot_token & Hsnapshot & Hcuts &
          Hacc & Hsession_token).
      destruct HR as
        (Htoken & Hlocal & Hcausal & Harray_local & Hpending & Hcandidate &
          Hrow & Hevolve & Hclock & Haligned & Hcuts_pres & Hgarbage &
          Hintervals & Hsession_equiv).
      destruct w as [sigma' Delta'].
      destruct pre as [sigma Delta]. simpl in *.
      split; [exact HI'|]. split; [exact Hactor|]. split.
      - unfold array_local_state in Harray_local.
        pose proof (f_equal snd Harray_local) as Hcounter_eq.
        simpl in Hcounter_eq. congruence.
      - exists done, progress. repeat split; try assumption.
        + unfold array_local_state in Harray_local.
        pose proof (f_equal fst Harray_local) as Hscan_eq.
        simpl in Hscan_eq. exact (eq_trans (eq_sym Hscan_eq) Hscan).
        + eapply seen_timestamped_stable; eauto.
        + eapply token_rely_ALinExists; eauto.
        + eapply token_rely_ALinExists; eauto.
        + destruct Hsnapshot as (N & local & Hsnd & Hview).
        exists N, local. split; [exact Hsnd|].
        now apply (proj1 Hlocal).
        + eapply Hcuts_pres; [exact Hactor| |exact Hsession_token|exact Hcuts].
        apply (proj2 (token_view_ALinExists sigma actor Delta _)).
        exact Hfallback.
        + unfold ScanAccumulator in *.
        destruct (fst scan) as [candidate|] eqn:Hchoice.
          * destruct Hacc as [Hview [Hvalid Hmax]]. split.
            -- now apply Hcandidate.
            -- split.
              ++ unfold candidate_interval_valid in *.
               destruct (candidate_timestamp candidate) as [|lower upper].
               ** constructor.
               ** eapply (proj1 (proj2 Hintervals)). exact Hvalid.
              ++ eapply candidate_maximal_stable; eauto.
          * destruct Hacc as [Hempty Hseen]. split.
            -- eapply empty_evidence_stable; eauto.
            -- intros n Hmember. apply Hgarbage, Hseen, Hmember.
        + eapply session_token_stable; [exact Hsession_equiv|exact Hsession_token].
    Qed.

    Lemma getTop_reset_entails_scan_fold actor :
      ⊨ GetTopReset actor ==>>
        ScanFold actor (ThreadDomain.threads D)
          (pair (@None (@Candidate A)) O).
    Proof.
      intros w [HI [Hactor [Hcounter_none [Hscan [Hfallback
        [Hsnapshot_token [Hsnapshot [Hcuts Hsession_token]]]]]]]].
      split; [exact HI|]. split; [exact Hactor|]. split;
        [exact Hcounter_none|].
      exists nil, empty_scan. split; [reflexivity|].
      split; [exact Hscan|]. split; [reflexivity|].
      split; [reflexivity|]. split.
      - unfold scan_seen_wf, empty_scan, empty_node_set. simpl. tauto.
      - split.
        + unfold seen_timestamped, empty_scan, empty_node_set. simpl. tauto.
        + split; [exact Hfallback|].
        split; [exact Hsnapshot_token|]. split; [exact Hsnapshot|].
        split; [exact Hcuts|]. split; [|exact Hsession_token].
        unfold ScanAccumulator. simpl. split.
        * apply empty_evidence_nil.
        * unfold seen_garbage, empty_scan, empty_node_set. simpl. tauto.
    Qed.

    Definition ScanPending (actor owner : tid) (remaining : list tid)
        (scan : @ScanState A) : assertion :=
      fun w =>
        I w /\
        ThreadDomain.contains D actor /\
        TMap.find actor
          (as_pending_counters
            (concrete_array (SetPossState.σ w))) = None /\
        exists done progress current,
          ThreadDomain.threads D = done ++ owner :: remaining /\
          TMap.find actor
            (as_scans (concrete_array (SetPossState.σ w))) = Some progress /\
          scan_visited progress = done /\
          scan_current progress = Some current /\
          current_owner current = owner /\
          scan_seen_wf progress /\
          seen_timestamped progress
            (concrete_array (SetPossState.σ w)) /\
          row_snapshot_view actor owner (current_order current)
            (SetPossState.Δ w) /\
          NoDup (current_order current) /\
          actor ↦∃◦((lpool_getTop start)) w /\
          actor ↦∃•((lpool_getTop start)) w /\
          SnapshotExists actor w /\
          node_cuts_available actor progress
            (concrete_array (SetPossState.σ w)) (SetPossState.Δ w) /\
          PendingAccumulator actor owner done progress current scan w /\
          current_counter current <=
            counter_at owner (concrete_array (SetPossState.σ w)) /\
          (current_counter current =
             counter_at owner (concrete_array (SetPossState.σ w)) ->
           incl (order_at owner (concrete_array (SetPossState.σ w)))
             (current_order current)) /\
          SessionToken actor start w.

    Lemma scan_pending_entails_I actor owner remaining scan :
      ⊨ ScanPending actor owner remaining scan ==>> I.
    Proof. intros w [HI _]. exact HI. Qed.

    Lemma scan_pending_stable actor owner remaining scan :
      AssertionsSet.A.Stable (R actor) I
        (ScanPending actor owner remaining scan).
    Proof.
      unfold AssertionsSet.A.Stable, AssertionsSet.A.ComposeA,
        ScanPending, R.
      intros w [Hcompose HI'].
      destruct Hcompose as [pre [Hpre HR]].
      destruct Hpre as [HI [Hactor [Hcounter_none Hpre]]].
      destruct Hpre as
        (done & progress & current & Hparts & Hscan & Hvisited & Hcurrent &
          Howner & Hseenwf & Hseen_timestamped & Hrowview & Hnodup & Hfallback &
          Hsnapshot_token & Hsnapshot & Hcuts & Hacc & Hcounter & Hincl & Hsession_token).
      destruct HR as
        (Htoken & Hlocal & Hcausal & Harray_local & Hpending & Hcandidate &
          Hrow & Hevolve & Hclock & Haligned & Hcuts_pres & Hgarbage &
          Hintervals & Hsession_equiv).
      destruct w as [sigma' Delta'].
      destruct pre as [sigma Delta]. simpl in *.
      split; [exact HI'|]. split; [exact Hactor|]. split.
      - unfold array_local_state in Harray_local.
        pose proof (f_equal snd Harray_local) as Hcounter_eq.
        simpl in Hcounter_eq. congruence.
      - exists done, progress, current. repeat split; try assumption.
        + unfold array_local_state in Harray_local.
        pose proof (f_equal fst Harray_local) as Hscan_eq.
        simpl in Hscan_eq. exact (eq_trans (eq_sym Hscan_eq) Hscan).
        + eapply seen_timestamped_stable; eauto.
        + now apply Hrow.
        + eapply token_rely_ALinExists; eauto.
        + eapply token_rely_ALinExists; eauto.
        + destruct Hsnapshot as (N & local & Hsnd & Hview).
        exists N, local. split; [exact Hsnd|].
        now apply (proj1 Hlocal).
        + eapply Hcuts_pres; [exact Hactor| |exact Hsession_token|exact Hcuts].
        apply (proj2 (token_view_ALinExists sigma actor Delta _)).
        exact Hfallback.
        + unfold PendingAccumulator in *.
        destruct (fst scan) as [candidate|] eqn:Hchoice.
          * destruct Hacc as [Hview [Hvalid Hmax]]. split.
            -- now apply Haligned.
            -- split.
              ++ unfold candidate_interval_valid in *.
               destruct (candidate_timestamp candidate) as [|lower upper].
               ** constructor.
               ** eapply (proj1 (proj2 Hintervals)). exact Hvalid.
              ++ eapply candidate_maximal_stable; eauto.
          * destruct Hacc as [Hempty Hseen]. split.
            -- eapply empty_evidence_stable; eauto.
            -- intros n Hmember. apply Hgarbage, Hseen, Hmember.
        + eapply Nat.le_trans; [exact Hcounter|].
        exact (proj1 (Hevolve owner)).
        + intro Heq.
        pose proof (proj1 (Hevolve owner)) as Hmono.
        assert (Holdcounter : current_counter current =
          counter_at owner (concrete_array sigma)) by lia.
        eapply incl_tran.
          * apply (proj2 (Hevolve owner)). lia.
          * now apply Hincl.
        + eapply session_token_stable; [exact Hsession_equiv|exact Hsession_token].
    Qed.

    Definition array_getTop_inv_kind
        (ev : @ThreadEvent (@ESPListArray A)) : bool :=
      match te_ev ev with
      | InvEv (array_getTop _) => true
      | _ => false
      end.

    Lemma array_getTop_inv_shape actor owner control control' :
      @StepSPListArray A D
        (Build_ThreadEvent actor (InvEv (array_getTop owner)))
        control control' ->
      exists a progress,
        control = ArrayReady a /\
        control' = ArrayReady (begin_scan actor owner progress a) /\
        ThreadDomain.contains D actor /\
        ThreadDomain.contains D owner /\
        TMap.find actor (as_scans a) = Some progress /\
        scan_current progress = None /\
        ~ In owner (scan_visited progress).
    Proof.
      intro Hstep. remember (Build_ThreadEvent actor
        (InvEv (array_getTop owner))) as ev eqn:Hev in Hstep.
      inversion Hstep.
      all: match goal with
        | Hctor : ?remembered = ?rhs,
          Htarget : ?remembered = ?target |- _ =>
            let Hevent := fresh "Hevent" in
            pose proof (eq_trans (eq_sym Htarget) Hctor) as Hevent;
            let Hkind := fresh "Hkind" in
            pose proof (f_equal array_getTop_inv_kind Hevent) as Hkind;
            cbv [array_getTop_inv_kind] in Hkind;
            first [discriminate Hkind |
              dependent destruction Hevent;
              do 2 eexists; repeat split; eauto]
        end.
    Qed.

    Lemma concrete_wf_begin_scan (a : @SPListArrayState A)
        tss actor owner progress :
      concrete_wf (pair (ArrayReady a) tss) ->
      concrete_wf
        (pair (ArrayReady (begin_scan actor owner progress a)) tss).
    Proof.
      unfold concrete_wf, concrete_array, concrete_timestamp, array_payload.
      simpl. intros (Hvalid & Hstamped & Hdefined & Hstructural).
      split; [exact Hvalid|]. split; [exact Hstamped|].
      split; assumption.
    Qed.

    Lemma pool_represents_begin_scan (a : @SPListArrayState A)
        p actor owner progress :
      pool_represents a p ->
      pool_represents (begin_scan actor owner progress a) p.
    Proof.
      unfold pool_represents, begin_scan. simpl. tauto.
    Qed.

    Lemma timestamp_pending_edges_begin_scan
        (a : @SPListArrayState A) tss p actor owner progress :
      timestamp_pending_edges (pair (ArrayReady a) tss) p ->
      timestamp_pending_edges
        (pair (ArrayReady (begin_scan actor owner progress a)) tss) p.
    Proof.
      unfold timestamp_pending_edges, concrete_array, concrete_timestamp,
        array_payload, outgoing_before, begin_scan. simpl. tauto.
    Qed.

    Lemma row_snapshot_view_optional (actor owner : tid)
        (a : @SPListArrayState A) (tss : TimestampState)
        (Delta : @AbstractConfig _ (li_lts F)) :
      I (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
        (pair (ArrayReady a) tss) Delta) ->
      actor ↦∃◦((lpool_getTop start))
        (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          (pair (ArrayReady a) tss) Delta) ->
      SessionToken actor start
        (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          (pair (ArrayReady a) tss) Delta) ->
      row_snapshot_view actor owner (order_at owner a)
        (ac_optional_snapshot Delta actor).
    Proof.
      intros [Hwf [Hall _]] Hfallback Hsession_token.
      destruct (proj2 (token_view_ALinExists
        (pair (ArrayReady a) tss) actor Delta (ls_inv (lpool_getTop start)))
        Hfallback) as (rho & pi & Hposs & Htoken).
      destruct (Hall _ _ Hposs) as
        (p & -> & Hpool & Hprotocol & Htimestamp & Hsession).
      assert (Hnone : TMap.find actor (lp_snapshots p) = None).
      { destruct (TMap.find actor (lp_snapshots p)) as [N|] eqn:Hfind;
          [|reflexivity].
        destruct (proj1 (proj2 Hprotocol) _ _ Hfind) as [start1 Hlin].
        rewrite Htoken in Hlin. discriminate. }
      assert (Hsession_ts : TMap.find actor (lp_pop_ts p) = Some start)
        by exact (Hsession_token _ _ Hposs).
      exists (start_snapshot actor p), (snapshot_tokens actor start pi),
        (fun n => is_vertex p n).
      repeat split.
      - eapply ac_optional_snapshot_take; eassumption.
      - exists start. unfold snapshot_tokens. apply TMap.gss.
      - simpl. rewrite TMap.gss. reflexivity.
      - intros loc Hin. unfold is_vertex, array_vertex in *.
        rewrite (proj1 Hpool). apply (proj1 (proj2 (proj2 (proj2 Hwf)))
          owner loc). exact Hin.
      - intros loc Hvertex Hlive.
        apply (proj1 (proj2 (proj2 (proj2 Hwf))) owner loc).
        split.
        + unfold array_vertex, is_vertex in *.
          rewrite <- (proj1 Hpool). exact Hvertex.
        + rewrite <- (proj1 (proj2 (proj2 (proj2 Hpool)))).
          exact Hlive.
      - intros newer older Hnewer_vertex Holder_vertex
          Hnewer_live Holder_live Hedge.
        eapply (proj1 (proj2 (proj2 (proj2 (proj2 (proj2
          (proj2 Hpool)))))) owner newer older); eauto.
        + split; [exact Hnewer_vertex|exact Hnewer_live].
        + split; [exact Holder_vertex|exact Holder_live].
    Qed.

    Lemma getTop_row_inv_update actor owner remaining scan :
      AssertionsSet.PUpdate (G actor)
        (Build_ThreadEvent actor (InvEv (inl (array_getTop owner))))
        (ScanFold actor (owner :: remaining) scan)
        (ScanPending actor owner remaining scan).
    Proof.
      intros [control tss] Delta
        [HIpre [Hactor [Hcounter_none Hrest]]]
        [control' tss'] Hstep.
      destruct Hrest as
        (done & progress & Hparts & Hscan & Hvisited & Hidle & Hseenwf &
          Hseen_timestamped & Hfallback & Hsnapshot_token & Hsnapshot & Hcuts &
          Hacc & Hsession_token).
      destruct HIpre as [Hwf [Hall Hrect]].
      simpl in Hstep. destruct Hstep as [Harray ->].
      destruct (array_getTop_inv_shape actor owner _ _ Harray) as
        (a & progress0 & -> & -> & Hactor0 & Howner & Hscan0 & Hidle0 &
          Hnotvisited).
      change (TMap.find actor (as_scans a) = Some progress) in Hscan.
      rewrite Hscan in Hscan0. inversion Hscan0; subst progress0.
      set (current := row_current owner a).
      set (progress' := visiting_progress owner a progress).
      set (Delta' := ac_optional_snapshot Delta actor).
      assert (Hrowview : row_snapshot_view actor owner (order_at owner a)
        Delta').
      { unfold Delta'. eapply row_snapshot_view_optional.
        - exact (conj Hwf (conj Hall Hrect)).
        - exact Hfallback.
        - exact Hsession_token. }
      assert (HIbase : I
        (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          (pair (ArrayReady (begin_scan actor owner progress a)) tss')
          Delta)).
      { split.
        - apply concrete_wf_begin_scan.
          exact Hwf.
        - split.
          + intros rho pi Hposs.
            destruct (Hall _ _ Hposs) as
              (p & -> & Hpool & Hprotocol & Htimestamp & Hsession).
            exists p. split; [reflexivity|]. split.
            * now apply pool_represents_begin_scan.
            * split; [exact Hprotocol|].
              split; [now apply timestamp_pending_edges_begin_scan|exact Hsession].
          + exact Hrect. }
      assert (HIpost : I
        (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          (pair (ArrayReady (begin_scan actor owner progress a)) tss')
          Delta')).
      { unfold Delta'. now apply I_optional_snapshot. }
      exists Delta'. split.
      - unfold Delta'. apply ac_optional_snapshot_subset_steps.
      - split.
        + unfold ScanPending. split; [exact HIpost|].
          split; [exact Hactor|].
          split; [unfold concrete_array, begin_scan; simpl;
            exact Hcounter_none|].
          exists done, progress', current.
          split; [exact Hparts|].
          split.
          * unfold progress', current, begin_scan. simpl. apply TMap.gss.
          * split; [unfold progress'; simpl; exact Hvisited|].
            split; [unfold progress'; simpl; reflexivity|].
            split; [unfold current; reflexivity|].
            split.
            -- unfold scan_seen_wf, progress'. simpl. exact Hseenwf.
            -- split.
               ++ unfold seen_timestamped, progress'. simpl.
                  exact Hseen_timestamped.
               ++ split.
                  ** unfold current. exact Hrowview.
                  ** split.
                     --- unfold current.
                  exact (proj2 (proj2 (proj2 (proj2 (proj2 Hwf)))) owner).
                     --- split.
                         +++ eapply token_rely_ALinExists;
                    [apply token_rely_optional_snapshot|exact Hfallback].
                         +++ split.
                             *** eapply token_rely_ALinExists;
                       [apply token_rely_optional_snapshot|
                        exact Hsnapshot_token].
                             *** split.
                                 ++++ destruct Hsnapshot as
                           (N & local & Hsnd & Hview).
                             exists N, local. split; [exact Hsnd|].
                             apply (proj1 (pool_local_equiv_optional_snapshot
                               Delta actor actor)). exact Hview.
                                 ++++ split.
                                      ***** change (node_cuts_available actor
                                        progress a Delta) in Hcuts.
                                      unfold node_cuts_available.
                                      intros n value Hlive Hvalue Hnotignored.
                                      change (array_live a n) in Hlive.
                                      change (as_values a n = Some value)
                                        in Hvalue.
                                      assert (Hold_notignored :
                                        ~ scan_status progress n Ignored).
                                      { eapply not_ignored_before_visiting;
                                          [exact Hidle|].
                                        unfold progress'. exact Hnotignored. }
                                      destruct (Hcuts n value Hlive Hvalue
                                        Hold_notignored) as
                                        (p & pi & N & Hposs & Htoken & Hsnap &
                                          Hnode_value & Hmember & Hcut).
                                      destruct (Hall _ _ Hposs) as
                                        (p0 & Heqp & Hpool & Hprotocol &
                                          Htimestamp & Hsession).
                                      inversion Heqp; subst p0.
                                      exists p, pi, N. repeat split;
                                        try assumption.
                                      { unfold Delta'. now apply
                                          ac_optional_snapshot_keep. }
                                      { intros newer Hnewer Hnewer_live Hedge.
                                            assert (Harray_live :
                                              array_live a newer).
                                            { split.
                                              - eapply (proj1 (proj2 (proj2
                                                  (proj2 (proj2
                                                    (proj2 Hpool)))))); eauto.
                                              - intro Hgarbage.
                                                apply Hnewer_live.
                                                apply (proj2 ((proj1 (proj2
                                                  (proj2 (proj2 Hpool))))
                                                  newer)).
                                                exact Hgarbage. }
                                            unfold progress'.
                                            eapply
                                              live_not_ignored_while_visiting;
                                              [|exact Harray_live|].
                                            { exact (proj2 (proj2 (proj2
                                                Hwf))). }
                                            { eapply Hcut; eauto. } }
                                      ***** split.
                                            ------ unfold PendingAccumulator,
                                             ScanAccumulator in *.
                             destruct (fst scan) as [candidate|] eqn:Hchoice.
                             { destruct Hacc as
                                      [Hcandidate [Hinterval Hmax]].
                                    unfold candidate_view in Hcandidate.
                                    destruct Hcandidate as
                                      (p & pi & N & Hposs & Htoken & Hsnap &
                                        Hvalue & Hdone & Hstatus & Hsafe).
                                    destruct (Hall _ _ Hposs) as
                                      (p0 & Heqp & Hpool & Hprotocol &
                                        Htimestamp & Hsession).
                                    inversion Heqp; subst p0.
                                    assert (Hsnapshot_vertex : forall node,
                                      N node -> array_vertex a node).
                                    { eapply (proj1 (proj2 (proj2 (proj2
                                        (proj2 (proj2 Hpool)))))); eauto. }
                                    split.
                                    { unfold candidate_row_view.
                                      exists p, pi, N.
                                      repeat split; try assumption.
                                      { unfold Delta'. now apply
                                          ac_optional_snapshot_keep. }
                                      { intros address Hmember Hlive.
                                        unfold current. apply (proj1
                                          (proj2 (proj2 (proj2
                                            Hwf)))). split.
                                        { exact (Hsnapshot_vertex _ Hmember). }
                                        { rewrite <- (proj1 (proj2 (proj2
                                            (proj2 Hpool)))). exact Hlive. } }
                                      { intros newer older Hnewer Holder
                                          Hnewer_live Holder_live Hedge.
                                        unfold current.
                                        apply (proj1 (proj2 (proj2 (proj2
                                          (proj2 (proj2 (proj2 Hpool))))))
                                          owner newer older Hedge); split.
                                        { unfold is_vertex.
                                          rewrite (proj1 Hpool).
                                          exact (Hsnapshot_vertex _ Hnewer). }
                                        { exact Hnewer_live. }
                                        { unfold is_vertex.
                                          rewrite (proj1 Hpool).
                                          exact (Hsnapshot_vertex _ Holder). }
                                        { exact Holder_live. } } }
                                    { split.
                                      { exact Hinterval. }
                                      { unfold candidate_maximal, progress' in *.
                                        simpl in *. exact Hmax. } } }
                             { destruct Hacc as [Hempty Hseen]. split;
                                    [exact Hempty|].
                                  unfold seen_garbage in *.
                                  unfold progress'. simpl. exact Hseen. }
                                            ------ split.
                                                   +++++++ unfold current,
                                                   row_current,
                                                   concrete_array,
                                                   array_payload,
                                   begin_scan, counter_at. simpl. lia.
                                                   +++++++ split.
                                                   { intro Heq.
                                                   unfold current,
                                                   row_current,
                                                   concrete_array,
                                   array_payload, begin_scan, order_at. simpl.
                                 intros loc Hloc. exact Hloc. }
                                                   { unfold Delta'.
                                                     eapply session_token_optional_snapshot.
                                                     exact Hsession_token. }
        + unfold G. split.
          * intros observer Hneq. unfold Delta'.
            apply token_equiv_rely.
            now apply token_equiv_optional_snapshot_foreign.
          * split.
            -- intros observer Hneq. unfold Delta'.
               now apply pool_local_equiv_optional_snapshot_foreign.
            -- split.
               ++ intros observer loc lower Hneq Hcausal rho pi Hfork.
                  destruct (ac_optional_snapshot_cases _ _ _ _ Hfork)
                    as [Hkeep|Htake].
                  ** destruct (Hcausal _ _ Hkeep) as
                       (p & -> & Hpending0 & Hbefore).
                     exists p. split; [reflexivity|]. split;
                       [exact Hpending0|].
                     unfold outgoing_before, concrete_array, array_payload,
                       begin_scan in *. simpl in *. exact Hbefore.
                  ** destruct Htake as
                       [p [pi0 [Hposs [Htoken0 [Hsession0 [Hnone [Hrho Hpi]]]]]]].
                     subst rho pi.
                     destruct (Hcausal _ _ Hposs) as
                       (p0 & Heq & Hpending0 & Hbefore).
                     inversion Heq; subst p0.
                     exists (start_snapshot actor p). split; [reflexivity|].
                     split; [exact Hpending0|].
                     unfold outgoing_before, concrete_array, array_payload,
                       begin_scan, start_snapshot in *. simpl in *.
                     exact Hbefore.
               ++ split.
                  ** intros observer Hneq.
                     unfold array_local_state, concrete_array, array_payload,
                       begin_scan. simpl. rewrite TMap.gso by congruence.
                     reflexivity.
                  ** split.
                     --- intros observer Hneq. reflexivity.
                     --- split.
                         +++ intros observer Hneq done0 candidate Hview.
                             unfold candidate_view in *.
                             destruct Hview as
                               (p & pi & N & Hposs & Htoken0 & Hsnap &
                                 Hvalue & Hdone & Hstatus & Hsafe).
                             exists p, pi, N. repeat split; try assumption.
                             unfold Delta'.
                             now apply ac_optional_snapshot_keep.
                         +++ split.
                             *** intros observer Hneq owner0 saved Hview.
                                 unfold row_snapshot_view in *.
                                 destruct Hview as
                                   (p & pi & N & Hposs & Htoken0 & Hsnap &
                                     Hsaved & Hlive & Horder).
                                 exists p, pi, N. repeat split; try assumption.
                                 unfold Delta'.
                                 now apply ac_optional_snapshot_keep.
                             *** split.
                                 ++++ eapply array_evolves_of_counter_order;
                                        intro q; reflexivity.
                                 ++++ split; [simpl; lia|].
                                      split.
                                      ***** intros observer Hneq.
                                            eapply
                                              candidate_row_views_preserved_mono.
                                            intros rho pi Hposs. unfold Delta'.
                                            now apply
                                              ac_optional_snapshot_keep.
                                      ***** split.
                                            ------ intros observer Hneq progress0 start0
                                                   Hinside Hfallback0 Hsession_all Hcuts0 n value
                                                   Hlive Hvalue Hnotignored.
                                                   unfold concrete_array,
                                                     array_payload, begin_scan
                                                     in Hlive, Hvalue.
                                                   simpl in Hlive, Hvalue.
                                                   destruct (Hcuts0 n value Hlive
                                                     Hvalue Hnotignored) as
                                                     (p & pi & N & Hposs & Htoken0 &
                                                       Hsnap & Hnode_value & Hmember &
                                                       Hcut).
                                                   exists p, pi, N.
                                                   repeat split; try assumption.
                                                   unfold Delta'. now apply
                                                     ac_optional_snapshot_keep.
                                            ------ split.
                                                   +++++++ unfold garbage_evolves,
                                                           concrete_array,
                                                           array_payload,
                                                           begin_scan.
                                                           simpl. firstorder.
                                                   +++++++ split.
                                                           { unfold intervals_evolve,
                                                               concrete_array,
                                                               array_payload,
                                                               begin_scan.
                                                             simpl. firstorder. }
                                                           { intros observer Hneq.
                                                             unfold Delta'.
                                                             apply session_equiv_fork_snapshot. }
    Qed.

    Lemma actual_scan_order_selected (c : CurrentScan)
        (a : @SPListArrayState A) loc remaining :
      actual_scan_order c a = loc :: remaining ->
      In loc (current_order c) /\
      In loc (order_at (current_owner c) a).
    Proof.
      unfold actual_scan_order. intro Hscan.
      assert (Hin : In loc
        (List.filter
          (fun address => List.existsb (Nat.eqb address)
            (order_at (current_owner c) a))
          (current_order c))).
      { rewrite Hscan. now left. }
      apply filter_In in Hin. destruct Hin as [Hsaved Hpresent].
      split; [exact Hsaved|].
      apply existsb_exists in Hpresent.
      destruct Hpresent as (address & Haddress & Heq).
      apply Nat.eqb_eq in Heq. now subst address.
    Qed.

    Lemma actual_scan_order_nil_absent (c : CurrentScan)
        (a : @SPListArrayState A) loc :
      actual_scan_order c a = nil ->
      In loc (current_order c) ->
      ~ In loc (order_at (current_owner c) a).
    Proof.
      unfold actual_scan_order. intros Hscan Hsaved Hpresent.
      assert (Hin : In loc
        (List.filter
          (fun address => List.existsb (Nat.eqb address)
            (order_at (current_owner c) a))
          (current_order c))).
      { apply filter_In. split; [exact Hsaved|].
        apply existsb_exists. exists loc. split; [exact Hpresent|].
        apply Nat.eqb_refl. }
      rewrite Hscan in Hin. contradiction.
    Qed.

    Lemma filter_head_no_before (test : Addr -> bool)
        saved head remaining earlier :
      NoDup saved ->
      List.filter test saved = head :: remaining ->
      test earlier = true ->
      earlier <> head ->
      list_before earlier head saved -> False.
    Proof.
      intros Hnodup Hfilter Hearlier Hneq
        (prefix & middle & suffix & Hsaved).
      subst saved.
      assert (Hnodup' : NoDup
        ((prefix ++ earlier :: middle) ++ head :: suffix)).
      { assert (Heqlist :
          (prefix ++ earlier :: middle) ++ head :: suffix =
          prefix ++ earlier :: middle ++ head :: suffix).
        { clear. induction prefix as [|x prefix IH]; simpl; congruence. }
        rewrite Heqlist. exact Hnodup. }
      pose proof (NoDup_remove_2
        (prefix ++ earlier :: middle) suffix head Hnodup') as Hhead_not_before.
      repeat rewrite filter_app in Hfilter. simpl in Hfilter.
      rewrite Hearlier in Hfilter. simpl in Hfilter.
      destruct (List.filter test prefix) as [|first rest] eqn:Hprefix.
      - inversion Hfilter. contradiction.
      - inversion Hfilter; subst first.
        apply Hhead_not_before. apply in_or_app. left.
        apply in_or_app. left.
        assert (Hinfilter : In head (List.filter test prefix)).
        { rewrite Hprefix. now left. }
        apply filter_In in Hinfilter. exact (proj1 Hinfilter).
    Qed.

    Lemma actual_scan_order_no_predecessor (c : CurrentScan)
        (a : @SPListArrayState A) loc remaining earlier :
      NoDup (current_order c) ->
      actual_scan_order c a = loc :: remaining ->
      earlier <> loc ->
      In earlier (order_at (current_owner c) a) ->
      list_before earlier loc (current_order c) -> False.
    Proof.
      intros Hnodup Hscan Hneq Hpresent Hbefore.
      eapply filter_head_no_before; eauto.
      apply existsb_exists. exists earlier. split; [exact Hpresent|].
      apply Nat.eqb_refl.
    Qed.

    Lemma pool_edge_irrefl (a : @SPListArrayState A)
        (p : @ListPoolState A) n :
      pool_represents a p ->
      timestamp_defined a ->
      ~ lp_edges p n n.
    Proof.
      intros Hrep Hdefined Hedge.
      destruct Hrep as
        [Hvertices [Hedges [Hedgevertices
          [Hgarbage [Hpending [Hsnapshots Hrows]]]]]].
      destruct (Hedges _ _ Hedge) as
        (newer_ts & older_ts & Hnewer & Holder & Hlt).
      rewrite Hnewer in Holder. inversion Holder; subst older_ts.
      destruct (Hedgevertices _ _ Hedge) as [Hvertex _].
      unfold is_vertex in Hvertex.
      rewrite Hvertices in Hvertex.
      destruct (timestamp_defined_vertex a n Hdefined Hvertex)
        as (ts & Htimestamp & Hwf).
      rewrite Hnewer in Htimestamp. inversion Htimestamp; subst ts.
      exact (timestamp_lt_irrefl newer_ts Hwf Hlt).
    Qed.

    Lemma row_snapshot_selected_live (a : @SPListArrayState A)
        (p : @ListPoolState A) (N : LPNodeSet)
        (c : CurrentScan) owner loc remaining :
      pool_represents a p ->
      array_structural_wf a ->
      current_owner c = owner ->
      (forall address, In address (current_order c) ->
        N (pair owner address)) ->
      actual_scan_order c a = loc :: remaining ->
      N (pair owner loc) /\ is_live p (pair owner loc).
    Proof.
      intros Hrep Hstructural Howner Hsaved Hscan.
      subst owner.
      destruct (actual_scan_order_selected c a loc remaining Hscan)
        as [Hin_saved Hin_current].
      split; [now apply Hsaved|].
      destruct Hrep as
        [Hvertices [Hedges [Hedgevertices
          [Hgarbage [Hpending [Hsnapshots Hrows]]]]]].
      destruct Hstructural as [Hlive [Hdomain Hnodup]].
      assert (Harray_live : array_live a (pair (current_owner c) loc)).
      { apply Hlive. exact Hin_current. }
      destruct Harray_live as [Hvertex Hnotgarbage].
      split.
      - unfold is_vertex. rewrite Hvertices. exact Hvertex.
      - rewrite Hgarbage. exact Hnotgarbage.
    Qed.

    Lemma row_snapshot_no_live_predecessor (a : @SPListArrayState A)
        (p : @ListPoolState A) (N : LPNodeSet)
        (c : CurrentScan) owner loc remaining :
      pool_represents a p ->
      timestamp_defined a ->
      array_structural_wf a ->
      current_owner c = owner ->
      NoDup (current_order c) ->
      (forall newer older,
        N (pair owner newer) -> N (pair owner older) ->
        ~ lp_garbage p (pair owner newer) ->
        ~ lp_garbage p (pair owner older) ->
        lp_edges p (pair owner newer) (pair owner older) ->
        list_before newer older (current_order c)) ->
      actual_scan_order c a = loc :: remaining ->
      N (pair owner loc) ->
      is_live p (pair owner loc) ->
      forall earlier,
        N (pair owner earlier) ->
        is_live p (pair owner earlier) ->
        ~ lp_edges p (pair owner earlier) (pair owner loc).
    Proof.
      intros Hrep Hdefined Hstructural Howner Hnodup Horder Hscan
        HlocN Hloc_live earlier Hearlier Hearlier_live Hedge.
      destruct Hloc_live as [Hloc_vertex Hloc_live].
      destruct Hearlier_live as [Hearly_vertex Hearly_live].
      destruct (Nat.eq_dec earlier loc) as [->|Hneq].
      - eapply pool_edge_irrefl; eauto.
      - eapply actual_scan_order_no_predecessor; eauto.
        + subst owner.
          apply (proj1 Hstructural). split.
          * unfold array_vertex, is_vertex in *.
            rewrite <- (proj1 Hrep). exact Hearly_vertex.
          * rewrite <- (proj1 (proj2 (proj2 (proj2 Hrep)))).
            exact Hearly_live.
    Qed.

    Lemma row_selected_timestamp_relation
        (a : @SPListArrayState A) (p : @ListPoolState A) (N : LPNodeSet)
        (c : CurrentScan) owner loc remaining selected_ts :
      pool_represents a p ->
      timestamp_defined a ->
      array_structural_wf a ->
      current_owner c = owner ->
      NoDup (current_order c) ->
      (forall address, In address (current_order c) ->
        N (pair owner address)) ->
      (forall newer older,
        N (pair owner newer) -> N (pair owner older) ->
        ~ lp_garbage p (pair owner newer) ->
        ~ lp_garbage p (pair owner older) ->
        lp_edges p (pair owner newer) (pair owner older) ->
        list_before newer older (current_order c)) ->
      actual_scan_order c a = loc :: remaining ->
      as_timestamps a (pair owner loc) = Some selected_ts ->
      forall n node_ts,
        current_nodes c n ->
        ~ as_garbage a n ->
        as_timestamps a n = Some node_ts ->
        n = pair owner loc \/ timestamp_lt node_ts selected_ts.
    Proof.
      intros Hpool Hdefined Hstructural Howner Hnodup Hsaved Horder Hscan
        Hselected_timestamp n node_ts Hcurrent_node Hnode_live
        Hnode_timestamp.
      assert (Hselected := row_snapshot_selected_live a p N c owner loc
        remaining Hpool Hstructural Howner Hsaved Hscan).
      destruct Hselected as [Hselected_member Hselected_live].
      destruct n as [node_owner node_loc].
      destruct Hcurrent_node as [Hnode_owner Hnode_saved]. simpl in *.
      rewrite Howner in Hnode_owner. simpl in Hnode_owner, Hnode_saved.
      subst node_owner.
      destruct (Nat.eq_dec node_loc loc) as [->|Hneq].
      - now left.
      - right.
        assert (Hnode_member : N (pair owner node_loc)) by now apply Hsaved.
        assert (Hnode_live_pool : is_live p (pair owner node_loc)).
        { split.
          - unfold is_vertex. rewrite (proj1 Hpool).
            eapply timestamp_defined_timestamp; eauto.
          - rewrite (proj1 (proj2 (proj2 (proj2 Hpool)))).
            exact Hnode_live. }
        destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2
          (proj2 Hpool))))))
          owner loc node_loc (not_eq_sym Hneq) Hselected_live Hnode_live_pool)
          as [Hselected_edge|Hnode_edge].
        + destruct ((proj1 (proj2 Hpool)) _ _ Hselected_edge) as
            (newer_ts & older_ts & Hnewer & Holder & Hlt).
          rewrite Hselected_timestamp in Hnewer.
          rewrite Hnode_timestamp in Holder.
          inversion Hnewer; inversion Holder; subst. exact Hlt.
        + exfalso.
          eapply row_snapshot_no_live_predecessor with
            (a := a) (p := p) (N := N) (c := c) (owner := owner)
            (loc := loc) (remaining := remaining) (earlier := node_loc);
            eauto.
    Qed.

    Lemma nonignored_visited_or_current_seen progress current n :
      scan_current progress = Some current ->
      (In (fst n) (scan_visited progress) \/
        fst n = current_owner current) ->
      ~ scan_status progress n Ignored ->
      scan_seen (finish_progress progress current) n.
    Proof.
      intros Hcurrent [Hvisited|Howner] Hnotignored.
      - unfold finish_progress, set_union. simpl.
        destruct (classic (scan_seen progress n)) as [Hseen|Hnotseen].
        + now left.
        + exfalso. apply Hnotignored.
          now apply scan_status_ignored_visited.
      - unfold finish_progress, set_union. simpl.
        destruct (classic (current_nodes current n)) as
          [Hcurrent_node|Hnotcurrent].
        + now right.
        + exfalso. apply Hnotignored.
          eapply scan_status_ignored_current; eauto.
    Qed.

    Definition observed_candidate (value : A) (owner : tid) (loc : Addr)
        (ts : TS) : @Candidate A :=
      {| candidate_value := value;
         candidate_owner := owner;
         candidate_loc := loc;
         candidate_timestamp := ts |}.

    Lemma observed_candidate_tstop_safe
        (a : @SPListArrayState A) (p : @ListPoolState A) N
        value owner loc ts :
      pool_represents a p ->
      as_timestamps a (pair owner loc) = Some ts ->
      candidate_tstop_safe (observed_candidate value owner loc ts) p N.
    Proof.
      intros Hpool Hselected_timestamp.
      unfold candidate_tstop_safe, observed_candidate. simpl.
      destruct ts as [|lower upper]; simpl; [|constructor].
      intros newer Hmember Hlive Hedge.
      destruct ((proj1 (proj2 Hpool)) _ _ Hedge) as
        (newer_ts & selected_ts & Hnewer & Hselected & Hlt).
      rewrite Hselected_timestamp in Hselected.
      inversion Hselected; subst selected_ts. simpl in Hlt. contradiction.
    Qed.

    Lemma candidate_top_from_cut
        (a : @SPListArrayState A) (p : @ListPoolState A) (N : LPNodeSet)
        progress current done owner (candidate : @Candidate A) :
      pool_represents a p ->
      scan_visited progress = done ->
      scan_current progress = Some current ->
      current_owner current = owner ->
      candidate_interval_valid candidate a ->
      candidate_maximal candidate (finish_progress progress current) a ->
      candidate_tstop_safe candidate p N ->
      N (pair (candidate_owner candidate) (candidate_loc candidate)) ->
      ~ lp_garbage p
          (pair (candidate_owner candidate) (candidate_loc candidate)) ->
      (forall newer,
        N newer -> ~ lp_garbage p newer ->
        lp_edges p newer
          (pair (candidate_owner candidate) (candidate_loc candidate)) ->
        ~ scan_status progress newer Ignored) ->
      visited_top (done ++ [owner]) p N
        (pair (candidate_owner candidate) (candidate_loc candidate)).
    Proof.
      intros Hpool Hvisited Hcurrent Howner Hvalid Hmax Hsafe Hmember
        Hcandidate_live Hcut.
      split; [exact Hmember|]. split; [exact Hcandidate_live|].
      intros newer Hnewer Hnewer_done Hnewer_live Hedge.
      unfold candidate_tstop_safe in Hsafe.
      unfold candidate_interval_valid in Hvalid.
      destruct (candidate_timestamp candidate) as [|candidate_lower
        candidate_upper] eqn:Hcandidate.
      - eapply Hsafe; eauto.
      - assert (Hnotignored : ~ scan_status progress newer Ignored)
          by (eapply Hcut; eauto).
        assert (Hseen : scan_seen (finish_progress progress current) newer).
        { eapply nonignored_visited_or_current_seen; [exact Hcurrent| |exact
            Hnotignored].
          apply in_app_or in Hnewer_done.
          destruct Hnewer_done as [Hold|Howner_case].
          - left. now rewrite Hvisited.
          - right. simpl in Howner_case.
            destruct Howner_case as [Howner_newer|Hfalse]; [|contradiction].
            rewrite Howner. symmetry. exact Howner_newer. }
        assert (Hnewer_concrete_live : ~ as_garbage a newer).
        { intro Hgarbage.
          apply Hnewer_live.
          apply (proj2 ((proj1 (proj2 (proj2 (proj2 Hpool)))) newer)).
          exact Hgarbage. }
        destruct ((proj1 (proj2 Hpool)) _ _ Hedge) as
          (newer_ts & candidate_ts & Hnewer_timestamp &
            Hcandidate_timestamp & Hlt).
        rewrite Hvalid in Hcandidate_timestamp.
        inversion Hcandidate_timestamp; subst candidate_ts.
        eapply (Hmax newer newer_ts Hseen Hnewer_concrete_live
          Hnewer_timestamp).
        rewrite Hcandidate. exact Hlt.
    Qed.

    Lemma selected_candidate_maximal_none
        (a : @SPListArrayState A) progress current value owner loc ts :
      timestamp_defined a ->
      as_timestamps a (pair owner loc) = Some ts ->
      seen_garbage progress a ->
      (forall n node_ts,
        current_nodes current n ->
        ~ as_garbage a n ->
        as_timestamps a n = Some node_ts ->
        n = pair owner loc \/ timestamp_lt node_ts ts) ->
      candidate_maximal (observed_candidate value owner loc ts)
        (finish_progress progress current) a.
    Proof.
      intros Hdefined Hselected_timestamp Hseen_garbage Hrow n node_ts
        [Hold_seen|Hcurrent_node] Hlive Hnode_timestamp Hlt.
      - apply Hlive. now apply Hseen_garbage.
      - destruct (Hrow n node_ts Hcurrent_node Hlive Hnode_timestamp) as
          [->|Hnode_lt].
        + simpl in Hlt.
          rewrite Hselected_timestamp in Hnode_timestamp.
          inversion Hnode_timestamp; subst node_ts.
          eapply timestamp_lt_irrefl; eauto.
          eapply timestamp_defined_wf; eauto.
        + simpl in Hlt.
          assert (Hwf_node : timestamp_wf node_ts) by
            (eapply timestamp_defined_wf; eauto).
          pose proof (timestamp_lt_trans ts node_ts ts Hwf_node Hlt
            Hnode_lt) as Hcycle.
          eapply (timestamp_lt_irrefl ts); eauto.
          eapply timestamp_defined_wf; eauto.
    Qed.

    Lemma selected_candidate_maximal_newer
        (a : @SPListArrayState A) progress current value owner loc ts previous :
      timestamp_defined a ->
      as_timestamps a (pair owner loc) = Some ts ->
      candidate_maximal previous progress a ->
      timestamp_lt (candidate_timestamp previous) ts ->
      (forall n node_ts,
        current_nodes current n ->
        ~ as_garbage a n ->
        as_timestamps a n = Some node_ts ->
        n = pair owner loc \/ timestamp_lt node_ts ts) ->
      candidate_maximal (observed_candidate value owner loc ts)
        (finish_progress progress current) a.
    Proof.
      intros Hdefined Hselected_timestamp Hprevious Hnewer Hrow n node_ts
        [Hold_seen|Hcurrent_node] Hlive Hnode_timestamp Hlt.
      - apply (Hprevious n node_ts Hold_seen Hlive Hnode_timestamp).
        eapply timestamp_lt_trans; [|exact Hnewer|exact Hlt].
        eapply timestamp_defined_wf; eauto.
      - destruct (Hrow n node_ts Hcurrent_node Hlive Hnode_timestamp) as
          [->|Hnode_lt].
        + simpl in Hlt.
          rewrite Hselected_timestamp in Hnode_timestamp.
          inversion Hnode_timestamp; subst node_ts.
          eapply timestamp_lt_irrefl; eauto.
          eapply timestamp_defined_wf; eauto.
        + simpl in Hlt.
          assert (Hwf_node : timestamp_wf node_ts) by
            (eapply timestamp_defined_wf; eauto).
          pose proof (timestamp_lt_trans ts node_ts ts Hwf_node Hlt
            Hnode_lt) as Hcycle.
          eapply (timestamp_lt_irrefl ts); eauto.
          eapply timestamp_defined_wf; eauto.
    Qed.

    Lemma previous_candidate_maximal_retained
        (a : @SPListArrayState A) progress current owner loc ts previous :
      timestamp_defined a ->
      as_timestamps a (pair owner loc) = Some ts ->
      candidate_maximal previous progress a ->
      ~ timestamp_lt (candidate_timestamp previous) ts ->
      (forall n node_ts,
        current_nodes current n ->
        ~ as_garbage a n ->
        as_timestamps a n = Some node_ts ->
        n = pair owner loc \/ timestamp_lt node_ts ts) ->
      candidate_maximal previous (finish_progress progress current) a.
    Proof.
      intros Hdefined Hselected_timestamp Hprevious Hnotnewer Hrow n node_ts
        [Hold_seen|Hcurrent_node] Hlive Hnode_timestamp Hlt.
      - eapply Hprevious; eauto.
      - destruct (Hrow n node_ts Hcurrent_node Hlive Hnode_timestamp) as
          [Heq|Hnode_lt].
        + subst n. apply Hnotnewer.
          rewrite Hselected_timestamp in Hnode_timestamp.
          inversion Hnode_timestamp; subst node_ts. exact Hlt.
        + apply Hnotnewer.
          eapply timestamp_lt_trans; [|exact Hlt|exact Hnode_lt].
          eapply timestamp_defined_wf; eauto.
    Qed.

    Lemma selected_candidate_view_from_cut
        (a : @SPListArrayState A) tss Delta actor progress current done
        owner value loc ts :
      I (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          (pair (ArrayReady a) tss) Delta) ->
      node_cut_view actor progress (pair owner loc) value Delta ->
      array_live a (pair owner loc) ->
      as_timestamps a (pair owner loc) = Some ts ->
      scan_visited progress = done ->
      scan_current progress = Some current ->
      current_owner current = owner ->
      candidate_maximal (observed_candidate value owner loc ts)
        (finish_progress progress current) a ->
      candidate_view actor (done ++ [owner])
        (observed_candidate value owner loc ts) Delta.
    Proof.
      intros [Hwf [Hall _]] Hcut_view Hselected_live Hselected_timestamp Hvisited
        Hcurrent Howner Hmax.
      destruct Hcut_view as
        (p & pi & N & Hposs & Htoken & Hsnapshot & Hvalue & Hmember & Hcut).
      destruct (Hall _ _ Hposs) as
        (p0 & Heqp & Hpool & Hprotocol & Htimestamp & Hsession).
      inversion Heqp; subst p0.
      assert (Hselected_pool_live : ~ lp_garbage p (pair owner loc)).
      { intro Hgarbage.
        apply (proj2 Hselected_live).
        apply (proj1 ((proj1 (proj2 (proj2 (proj2 Hpool))))
          (pair owner loc))). exact Hgarbage. }
      assert (Hsafe : candidate_tstop_safe
        (observed_candidate value owner loc ts) p N).
      { eapply observed_candidate_tstop_safe; eauto. }
      assert (Hvalid : candidate_interval_valid
        (observed_candidate value owner loc ts) a).
      { unfold candidate_interval_valid, observed_candidate. simpl.
        destruct ts; simpl; auto. }
      unfold candidate_view. exists p, pi, N. repeat split; try assumption.
      - simpl. apply in_or_app. right. now left.
      - right. eapply candidate_top_from_cut; eauto.
    Qed.

    Lemma retained_candidate_view_after_row
        (a : @SPListArrayState A) tss Delta actor progress current done owner
        (candidate : @Candidate A) :
      I (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          (pair (ArrayReady a) tss) Delta) ->
      candidate_row_view actor done candidate owner (current_order current)
        Delta ->
      candidate_interval_valid candidate a ->
      candidate_maximal candidate (finish_progress progress current) a ->
      scan_visited progress = done ->
      scan_current progress = Some current ->
      current_owner current = owner ->
      candidate_view actor (done ++ [owner]) candidate Delta.
    Proof.
      intros [Hwf [Hall _]] Hrow Hvalid Hmax Hvisited Hcurrent Howner.
      unfold candidate_row_view in Hrow.
      destruct Hrow as
        (p & pi & N & Hposs & Htoken & Hsnapshot & Hvalue & Hdone & Hstatus &
          Hcovered & Horder & Hsafe).
      destruct (Hall _ _ Hposs) as
        (p0 & Heqp & Hpool & Hprotocol & Htimestamp & Hsession).
      inversion Heqp; subst p0.
      unfold candidate_view. exists p, pi, N. repeat split; try assumption.
      - apply in_or_app. now left.
      - destruct Hstatus as [Hgarbage|[Hmember [Hlive Htop]]].
        + now left.
        + right. split; [exact Hmember|]. split; [exact Hlive|].
          intros newer Hnewer Hnewer_done Hnewer_live Hedge.
          apply in_app_or in Hnewer_done.
          destruct Hnewer_done as [Hold_done|Howner_done].
          * eapply Htop; eauto.
          * simpl in Howner_done.
            destruct Howner_done as [Hnewer_owner|Hfalse]; [|contradiction].
            unfold candidate_tstop_safe in Hsafe.
            unfold candidate_interval_valid in Hvalid.
            destruct (candidate_timestamp candidate) as
              [|candidate_lower candidate_upper] eqn:Hcandidate.
            -- eapply Hsafe; eauto.
            -- destruct newer as [newer_owner newer_loc]. simpl in *.
               subst newer_owner.
               assert (Hsaved : In newer_loc (current_order current))
                 by (eapply Hcovered; eauto).
               assert (Hseen : scan_seen
                 (finish_progress progress current) (pair owner newer_loc)).
               { unfold finish_progress, set_union. simpl. right. split.
                 - symmetry. exact Howner.
                 - exact Hsaved. }
               assert (Hnewer_concrete_live :
                 ~ as_garbage a (pair owner newer_loc)).
               { intro Hgarbage. apply Hnewer_live.
                 apply (proj2 ((proj1 (proj2 (proj2 (proj2 Hpool))))
                   (pair owner newer_loc))). exact Hgarbage. }
               destruct ((proj1 (proj2 Hpool)) _ _ Hedge) as
                 (newer_ts & candidate_ts & Hnewer_timestamp &
                   Hcandidate_timestamp & Hlt).
               change (as_timestamps a
                 (pair (candidate_owner candidate) (candidate_loc candidate)) =
                 Some candidate_ts) in Hcandidate_timestamp.
               rewrite Hvalid in Hcandidate_timestamp.
               inversion Hcandidate_timestamp; subst candidate_ts.
               eapply (Hmax (pair owner newer_loc) newer_ts Hseen
                 Hnewer_concrete_live Hnewer_timestamp).
               rewrite Hcandidate. exact Hlt.
    Qed.

    Lemma row_snapshot_empty_has_no_live_node
        (a : @SPListArrayState A) (p : @ListPoolState A)
        (N : LPNodeSet) (c : CurrentScan) actor owner :
      pool_represents a p ->
      array_structural_wf a ->
      TMap.find actor (lp_snapshots p) = Some N ->
      current_owner c = owner ->
      (forall loc, N (pair owner loc) ->
        ~ lp_garbage p (pair owner loc) ->
        In loc (current_order c)) ->
      actual_scan_order c a = nil ->
      forall loc,
        N (pair owner loc) ->
        ~ lp_garbage p (pair owner loc) -> False.
    Proof.
      intros Hrep Hstructural Hsnapshot Howner Hsaved Hscan
        loc Hmember Hlive.
      assert (Hsaved_loc : In loc (current_order c)).
      { now apply Hsaved. }
      pose proof (actual_scan_order_nil_absent c a loc Hscan Hsaved_loc)
        as Habsent.
      apply Habsent. subst owner.
      apply (proj1 Hstructural). split.
      - exact ((proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hrep))))))
          actor N Hsnapshot (pair (current_owner c) loc) Hmember).
      - rewrite <- (proj1 (proj2 (proj2 (proj2 Hrep)))). exact Hlive.
    Qed.

    Lemma current_nodes_garbage_after_empty
        (a : @SPListArrayState A) tss Delta actor owner current :
      I (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          (pair (ArrayReady a) tss) Delta) ->
      row_snapshot_view actor owner (current_order current) Delta ->
      current_owner current = owner ->
      actual_scan_order current a = nil ->
      forall n, current_nodes current n -> as_garbage a n.
    Proof.
      intros [Hwf [Hall _]] Hrow Howner Hactual n Hcurrent_node.
      destruct Hrow as
        (p & pi & N & Hposs & Htoken & Hsnapshot & Hsaved & Hcovered &
          Horder).
      destruct (Hall _ _ Hposs) as
        (p0 & Heqp & Hpool & Hprotocol & Htimestamp & Hsession).
      inversion Heqp; subst p0.
      destruct n as [node_owner node_loc]. simpl in *.
      destruct Hcurrent_node as [Hnode_owner Hsaved_loc].
      rewrite Howner in Hnode_owner.
      simpl in Hnode_owner, Hsaved_loc. subst node_owner.
      assert (Hmember : N (pair owner node_loc)).
      { now apply Hsaved. }
      assert (Hvertex : array_vertex a (pair owner node_loc)).
      { eapply (proj1 (proj2 (proj2 (proj2 (proj2
          (proj2 Hpool)))))); eauto. }
      destruct (classic (as_garbage a (pair owner node_loc))) as
        [Hgarbage|Hlive]; [exact Hgarbage|].
      exfalso.
      pose proof (actual_scan_order_nil_absent current a node_loc
        Hactual Hsaved_loc) as Habsent.
      apply Habsent. rewrite Howner.
      apply (proj1 (proj1 (proj2 (proj2 (proj2 Hwf))) owner node_loc)).
      split; assumption.
    Qed.

    Lemma current_nodes_timestamped
        (a : @SPListArrayState A) tss Delta actor owner current :
      I (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          (pair (ArrayReady a) tss) Delta) ->
      row_snapshot_view actor owner (current_order current) Delta ->
      current_owner current = owner ->
      forall n, current_nodes current n ->
        exists ts, as_timestamps a n = Some ts.
    Proof.
      intros [Hwf [Hall _]] Hrow Howner n Hcurrent_node.
      destruct Hrow as
        (p & pi & N & Hposs & Htoken & Hsnapshot & Hsaved & Hcovered &
          Horder).
      destruct (Hall _ _ Hposs) as
        (p0 & Heqp & Hpool & Hprotocol & Htimestamp & Hsession).
      inversion Heqp; subst p0.
      destruct n as [node_owner node_loc]. simpl in *.
      destruct Hcurrent_node as [Hnode_owner Hsaved_loc].
      rewrite Howner in Hnode_owner. simpl in Hnode_owner, Hsaved_loc.
      subst node_owner.
      assert (Hmember : N (pair owner node_loc)) by now apply Hsaved.
      assert (Hvertex : array_vertex a (pair owner node_loc)).
      { eapply (proj1 (proj2 (proj2 (proj2 (proj2
          (proj2 Hpool)))))); eauto. }
      destruct (timestamp_defined_vertex a (pair owner node_loc)
        (proj1 (proj2 (proj2 Hwf))) Hvertex) as
        (ts & Htimestamp_node & Htimestamp_wf).
      exists ts. exact Htimestamp_node.
    Qed.

    Definition array_getTop_res_kind
        (ev : @ThreadEvent (@ESPListArray A)) : bool :=
      match te_ev ev with
      | ResEv (array_getTop _) _ => true
      | _ => false
      end.

    Definition array_getTop_res_payload
        (ev : @ThreadEvent (@ESPListArray A)) : option (@LNode A + nat) :=
      match te_ev ev with
      | ResEv (array_getTop _) result => Some result
      | _ => None
      end.

    Lemma array_getTop_nonempty_res_shape actor owner value ts loc
        control control' :
      @StepSPListArray A D
        (Build_ThreadEvent actor
          (ResEv (array_getTop owner)
            (@inl (@LNode A) nat (pair (pair value ts) loc))))
        control control' ->
      exists a progress current remaining,
        control = ArrayReady a /\
        control' = ArrayReady (end_scan actor progress current a) /\
        TMap.find actor (as_scans a) = Some progress /\
        scan_current progress = Some current /\
        current_owner current = owner /\
        actual_scan_order current a = loc :: remaining /\
        as_values a (pair owner loc) = Some value /\
        as_timestamps a (pair owner loc) = Some ts.
    Proof.
      intro Hstep. remember (Build_ThreadEvent actor
        (ResEv (array_getTop owner)
          (@inl (@LNode A) nat (pair (pair value ts) loc))))
        as ev eqn:Hev in Hstep.
      inversion Hstep.
      all: match goal with
        | Hctor : ?remembered = ?rhs,
          Htarget : ?remembered = ?target |- _ =>
            let Hevent := fresh "Hevent" in
            pose proof (eq_trans (eq_sym Htarget) Hctor) as Hevent;
            let Hkind := fresh "Hkind" in
            pose proof (f_equal array_getTop_res_kind Hevent) as Hkind;
            cbv [array_getTop_res_kind] in Hkind;
            first [discriminate Hkind |
              let Hpayload := fresh "Hpayload" in
              pose proof (f_equal array_getTop_res_payload Hevent) as Hpayload;
              cbv [array_getTop_res_payload] in Hpayload;
              try discriminate Hpayload;
              injection Hpayload; intros; subst;
              dependent destruction Hevent;
              do 4 eexists; repeat split; eauto]
        end.
    Qed.

    Lemma array_getTop_empty_res_shape actor owner count control control' :
      @StepSPListArray A D
        (Build_ThreadEvent actor
          (ResEv (array_getTop owner) (@inr (@LNode A) nat count)))
        control control' ->
      exists a progress current,
        control = ArrayReady a /\
        control' = ArrayReady (end_scan actor progress current a) /\
        TMap.find actor (as_scans a) = Some progress /\
        scan_current progress = Some current /\
        current_owner current = owner /\
        actual_scan_order current a = nil /\
        count = current_counter current.
    Proof.
      intro Hstep. remember (Build_ThreadEvent actor
        (ResEv (array_getTop owner) (@inr (@LNode A) nat count)))
        as ev eqn:Hev in Hstep.
      inversion Hstep.
      all: match goal with
        | Hctor : ?remembered = ?rhs,
          Htarget : ?remembered = ?target |- _ =>
            let Hevent := fresh "Hevent" in
            pose proof (eq_trans (eq_sym Htarget) Hctor) as Hevent;
            let Hkind := fresh "Hkind" in
            pose proof (f_equal array_getTop_res_kind Hevent) as Hkind;
            cbv [array_getTop_res_kind] in Hkind;
            first [discriminate Hkind |
              let Hpayload := fresh "Hpayload" in
              pose proof (f_equal array_getTop_res_payload Hevent) as Hpayload;
              cbv [array_getTop_res_payload] in Hpayload;
              try discriminate Hpayload;
              injection Hpayload; intros; subst;
              dependent destruction Hevent;
              do 3 eexists; repeat split; eauto]
        end.
    Qed.

    Lemma concrete_wf_end_scan (a : @SPListArrayState A)
        tss actor progress current :
      concrete_wf (pair (ArrayReady a) tss) ->
      concrete_wf (pair (ArrayReady (end_scan actor progress current a)) tss).
    Proof.
      unfold concrete_wf, concrete_array, concrete_timestamp, array_payload.
      simpl. intros (Hvalid & Hstamped & Hdefined & Hstructural).
      split; [exact Hvalid|]. split; [exact Hstamped|]. split; assumption.
    Qed.

    Lemma pool_represents_end_scan (a : @SPListArrayState A)
        p actor progress current :
      pool_represents a p ->
      pool_represents (end_scan actor progress current a) p.
    Proof. unfold pool_represents, end_scan. simpl. tauto. Qed.

    Lemma timestamp_pending_edges_end_scan
        (a : @SPListArrayState A) tss p actor progress current :
      timestamp_pending_edges (pair (ArrayReady a) tss) p ->
      timestamp_pending_edges
        (pair (ArrayReady (end_scan actor progress current a)) tss) p.
    Proof.
      unfold timestamp_pending_edges, concrete_array, concrete_timestamp,
        array_payload, outgoing_before, end_scan. simpl. tauto.
    Qed.

    Lemma G_end_scan (a : @SPListArrayState A) (tss : TimestampState)
        (Delta : @AbstractConfig _ (li_lts F))
        (actor : tid) (progress : ScanProgress) (current : CurrentScan) :
      G actor
        (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          (pair (ArrayReady a) tss) Delta)
        (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          (pair (ArrayReady (end_scan actor progress current a)) tss) Delta).
    Proof.
      unfold G. split.
      - intros observer Hneq. apply token_rely_refl.
      - split.
        + intros observer Hneq. apply pool_local_equiv_refl.
        + split.
          * intros observer loc lower Hneq Hcausal.
            unfold push_causal, concrete_array, array_payload,
              end_scan, outgoing_before in *. simpl in *. exact Hcausal.
          * split.
            -- intros observer Hneq.
               unfold array_local_state, concrete_array, array_payload,
                 end_scan. simpl. rewrite TMap.gso by congruence.
               reflexivity.
            -- split; [intros observer Hneq; reflexivity|].
               split.
               ++ intros observer Hneq.
                  apply candidate_views_preserved_refl.
               ++ split.
                  ** intros observer Hneq.
                     apply row_snapshot_views_preserved_refl.
                  ** split.
                     --- eapply array_evolves_of_counter_order;
                           intro owner; reflexivity.
                     --- split; [simpl; lia|].
                         split.
                         ++++ intros observer Hneq.
                              apply candidate_row_views_preserved_refl.
                         ++++ split.
                              ***** intros observer Hneq progress0 start0 Hinside
                                      Hfallback Hsession_all Hcuts.
                                    unfold node_cuts_available, concrete_array,
                                      array_payload, end_scan in *. simpl in *.
                                    exact Hcuts.
                              ***** unfold garbage_evolves, concrete_array,
                                      array_payload, end_scan. simpl. firstorder.
    Qed.

    Lemma getTop_row_empty_res_update actor owner remaining scan count :
      AssertionsSet.PUpdate (G actor)
        (Build_ThreadEvent actor
          (ResEv (inl (array_getTop owner))
            (@inr (@LNode A) nat count)))
        (ScanPending actor owner remaining scan)
        (ScanFold actor remaining
          (pair (fst scan) (Nat.add (snd scan) count))).
    Proof.
      intros [control tss] Delta Hpre [control' tss'] Hstep.
      simpl in Hstep. destruct Hstep as [Harray ->].
      destruct (array_getTop_empty_res_shape actor owner count _ _ Harray)
        as (a & progress0 & current0 & -> & -> & Hscan0 & Hcurrent0 &
          Howner0 & Hactual & Hcount).
      destruct Hpre as [HIpre [Hactor [Hcounter_none Hpre]]].
      destruct Hpre as
        (done & progress & current & Hparts & Hscan & Hvisited & Hcurrent &
          Howner & Hseenwf & Hseen_timestamped & Hrowview & Hnodup & Hfallback &
          Hsnapshot_token & Hsnapshot & Hcuts & Hacc & Hcounter & Hincl & Hsession_token).
      destruct HIpre as [Hwf [Hall Hrect]].
      change (TMap.find actor (as_scans a) = Some progress) in Hscan.
      rewrite Hscan in Hscan0. inversion Hscan0; subst progress0.
      rewrite Hcurrent in Hcurrent0. inversion Hcurrent0; subst current0.
      assert (Howner_new : ~ In (current_owner current)
        (scan_visited progress)).
      { rewrite Hvisited, Howner. intro Hin.
        pose proof (ThreadDomain.contains_nodup D) as Hdomain_nodup.
        rewrite Hparts in Hdomain_nodup.
        pose proof (NoDup_remove_2 done remaining owner Hdomain_nodup)
          as Hnotin.
        apply Hnotin. apply in_or_app. now left. }
      assert (Hseen_timestamped_post :
        seen_timestamped (finish_progress progress current)
          (end_scan actor progress current a)).
      { unfold seen_timestamped, finish_progress, set_union, end_scan.
        simpl. intros n [Hold_seen|Hcurrent_node].
        - now apply Hseen_timestamped.
        - eapply current_nodes_timestamped.
          + exact (conj Hwf (conj Hall Hrect)).
          + exact Hrowview.
          + exact Howner.
          + exact Hcurrent_node. }
      assert (HIpost : I
        (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          (pair (ArrayReady (end_scan actor progress current a)) tss') Delta)).
      { split.
        - apply concrete_wf_end_scan. exact Hwf.
        - split.
          + intros rho pi Hposs.
            destruct (Hall _ _ Hposs) as
              (p & -> & Hpool & Hprotocol & Htimestamp & Hsession).
            exists p. split; [reflexivity|]. split.
            * now apply pool_represents_end_scan.
            * split; [exact Hprotocol|].
              split; [now apply timestamp_pending_edges_end_scan|exact Hsession].
          + exact Hrect. }
      exists Delta. split; [apply ac_steps_refl|]. split.
      - unfold ScanFold. split; [exact HIpost|]. split; [exact Hactor|].
        split; [unfold concrete_array, end_scan; simpl;
          exact Hcounter_none|].
        exists (done ++ [owner]), (finish_progress progress current).
        split.
        + rewrite Hparts, <- app_assoc. reflexivity.
        + split.
          * unfold end_scan. simpl. apply TMap.gss.
          * split.
            -- unfold finish_progress. simpl. rewrite Hvisited, Howner.
               reflexivity.
            -- split; [reflexivity|]. split.
               ++ now apply scan_seen_wf_finish.
               ++ split; [exact Hseen_timestamped_post|]. split.
                  ** apply (proj1 (token_view_ALinExists
                       (pair (ArrayReady
                         (end_scan actor progress current a)) tss')
                       actor Delta _)).
                     apply (proj2 (token_view_ALinExists
                       (pair (ArrayReady a) tss') actor Delta _)).
                     exact Hfallback.
                  ** split.
                     --- apply (proj1 (token_view_ALinExists
                          (pair (ArrayReady
                            (end_scan actor progress current a)) tss')
                          actor Delta _)).
                         apply (proj2 (token_view_ALinExists
                           (pair (ArrayReady a) tss') actor Delta _)).
                         exact Hsnapshot_token.
                     --- split.
                         +++ destruct Hsnapshot as (N & local & Hsnd & Hview).
                             exists N, local. split; assumption.
                         +++ split.
                             *** change (node_cuts_available actor progress a
                                   Delta) in Hcuts.
                                 unfold node_cuts_available.
                                 intros n value Hlive Hvalue Hnotignored.
                                 change (array_live a n) in Hlive.
                                 change (as_values a n = Some value) in Hvalue.
                                 assert (Hold_notignored :
                                   ~ scan_status progress n Ignored).
                                 { eapply not_ignored_before_finish; eauto. }
                                 destruct (Hcuts n value Hlive Hvalue
                                   Hold_notignored) as
                                   (p & pi & N & Hposs & Htoken & Hsnap &
                                     Hnode_value & Hmember & Hcut).
                                 exists p, pi, N. repeat split; try assumption.
                                 intros newer Hnewer Hnewer_live Hedge.
                                 eapply not_ignored_after_finish;
                                   [exact Hcurrent|].
                                 eapply Hcut; eauto.
                             *** split; [|exact Hsession_token].
                                 unfold ScanAccumulator, PendingAccumulator in *.
                         destruct (fst scan) as [candidate|] eqn:Hchoice.
                         ++++ destruct Hacc as
                                [Hrowcandidate [Hinterval Hmax]].
                              unfold candidate_row_view in Hrowcandidate.
                              destruct Hrowcandidate as
                                (p & pi & N & Hposs & Htoken & Hsnap & Hvalue &
                                  Hdone & Hstatus & Hcovered & Horder & Hsafe).
                              destruct (Hall _ _ Hposs) as
                                (p0 & Heqp & Hpool & Hprotocol & Htimestamp & Hsession).
                              inversion Heqp; subst p0.
                              split.
                              { unfold candidate_view.
                                exists p, pi, N. repeat split; try assumption.
                                { apply in_or_app. left. exact Hdone. }
                                { destruct Hstatus as
                                    [Hgarbage|[Hmember [Hlive Htop]]].
                                  - left. exact Hgarbage.
                                  - right. split; [exact Hmember|].
                                    split; [exact Hlive|].
                                    intros newer Hnewer Hnewer_done Hnewer_live
                                      Hedge.
                                    apply in_app_or in Hnewer_done.
                                    destruct Hnewer_done as
                                      [Hold_done|Howner_done].
                                    + eapply Htop; eauto.
                                    + simpl in Howner_done.
                                      destruct Howner_done as
                                        [Hnewer_owner|Hfalse];
                                        [|contradiction].
                                      destruct newer as
                                        [newer_owner newer_loc]. simpl in *.
                                      subst newer_owner.
                                      exfalso.
                                      eapply row_snapshot_empty_has_no_live_node
                                        with (a := a) (p := p) (N := N)
                                          (c := current) (actor := actor)
                                          (owner := owner) (loc := newer_loc);
                                        eauto.
                                      exact (proj2 (proj2 (proj2
                                        Hwf))). } }
                              { split.
                                { unfold candidate_interval_valid in *.
                                  unfold concrete_array, array_payload, end_scan.
                                  simpl. exact Hinterval. }
                                { unfold candidate_maximal, concrete_array,
                                    array_payload, end_scan, finish_progress,
                                    set_union in *.
                                  simpl in *.
                                  intros n ts [Hold_seen|Hcurrent_node] Hlive
                                    Htimestamp_node.
                                  - eapply Hmax; eauto.
                                  - exfalso. apply Hlive.
                                    eapply current_nodes_garbage_after_empty.
                                    + exact (conj Hwf (conj Hall Hrect)).
                                    + exact Hrowview.
                                    + exact Howner.
                                    + exact Hactual.
                                    + exact Hcurrent_node. } }
                         ++++ destruct Hacc as [[Hbound Hempty] Hseen].
                              unfold concrete_array, array_payload in
                                Hbound, Hempty, Hcounter, Hincl.
                              split.
                              { split.
                                - unfold concrete_array, array_payload,
                                    end_scan. simpl.
                                  rewrite sum_counters_snoc.
                                  unfold counter_at in *.
                                  apply Nat.add_le_mono; [exact Hbound|].
                                  rewrite Hcount. exact Hcounter.
                                - unfold concrete_array, array_payload,
                                    end_scan. simpl.
                                  intro Heq. rewrite sum_counters_snoc in Heq.
                                  assert (Hsample_bound : count <=
                                    match TMap.find owner (as_counters a) with
                                    | Some current_count => current_count
                                    | None => 0
                                    end).
                                  { rewrite Hcount. unfold counter_at in Hcounter.
                                    exact Hcounter. }
                                  assert (Hold_eq : snd scan =
                                    sum_counters done (as_counters a)).
                                  { apply Nat.le_antisymm; [exact Hbound|].
                                    apply (proj2 (Nat.add_le_mono_r _ _
                                      (match TMap.find owner (as_counters a) with
                                       | Some current_count => current_count
                                       | None => 0
                                       end))).
                                    rewrite <- Heq.
                                    now apply Nat.add_le_mono_l. }
                                  assert (Hsample_eq : current_counter current =
                                    counter_at owner a).
                                  { unfold counter_at. apply Nat.le_antisymm.
                                    - exact Hcounter.
                                    - rewrite <- Hcount.
                                      apply (proj2 (Nat.add_le_mono_l _ _
                                        (sum_counters done (as_counters a)))).
                                      rewrite <- Heq.
                                      now apply Nat.add_le_mono_r. }
                                  intros q Hq. apply in_app_or in Hq.
                                  destruct Hq as [Hq_done|Hq_owner].
                                  + now apply Hempty.
                                  + simpl in Hq_owner.
                                    destruct Hq_owner as [->|Hfalse];
                                      [|contradiction].
                                    change (order_at q a = nil).
                                    assert (Hincl0 : incl (order_at q a)
                                      (current_order current)).
                                    { apply Hincl. exact Hsample_eq. }
                                    destruct (order_at q a) as [|loc rest]
                                      eqn:Horder_current; [reflexivity|].
                                    exfalso.
                                    assert (Hsaved_loc :
                                      In loc (current_order current)).
                                    { apply Hincl0. now left. }
                                    pose proof (actual_scan_order_nil_absent
                                      current a loc Hactual Hsaved_loc) as
                                      Habsent.
                                    apply Habsent. rewrite Howner.
                                    rewrite Horder_current.
                                    exact (or_introl eq_refl). }
                              { unfold seen_garbage, finish_progress, set_union.
                                simpl. intros n [Hold_seen|Hcurrent_node].
                                - now apply Hseen.
                                - eapply current_nodes_garbage_after_empty.
                                  + exact (conj Hwf (conj Hall Hrect)).
                                  + exact Hrowview.
                                  + exact Howner.
                                  + exact Hactual.
                                  + exact Hcurrent_node. }
      - apply G_end_scan.
    Qed.

    Lemma getTop_row_nonempty_res_update actor owner remaining scan
        value ts loc :
      AssertionsSet.PUpdate (G actor)
        (Build_ThreadEvent actor
          (ResEv (inl (array_getTop owner))
            (@inl (@LNode A) nat (pair (pair value ts) loc))))
        (ScanPending actor owner remaining scan)
        (ScanFold actor remaining
          (pair (choose_candidate owner (pair (pair value ts) loc) (fst scan))
            (snd scan))).
    Proof.
      intros [control tss] Delta Hpre [control' tss'] Hstep.
      simpl in Hstep. destruct Hstep as [Harray ->].
      destruct (array_getTop_nonempty_res_shape actor owner value ts loc _ _
        Harray) as
        (a & progress0 & current0 & row_remaining & -> & -> & Hscan0 &
          Hcurrent0 & Howner0 & Hactual & Hvalue & Hselected_timestamp).
      destruct Hpre as [HIpre [Hactor [Hcounter_none Hpre]]].
      destruct Hpre as
        (done & progress & current & Hparts & Hscan & Hvisited & Hcurrent &
          Howner & Hseenwf & Hseen_timestamped & Hrowview & Hnodup & Hfallback &
          Hsnapshot_token & Hsnapshot & Hcuts & Hacc & Hcounter & Hincl & Hsession_token).
      destruct HIpre as [Hwf [Hall Hrect]].
      change (TMap.find actor (as_scans a) = Some progress) in Hscan.
      rewrite Hscan in Hscan0. inversion Hscan0; subst progress0.
      rewrite Hcurrent in Hcurrent0. inversion Hcurrent0; subst current0.
      assert (Howner_new : ~ In (current_owner current)
        (scan_visited progress)).
      { rewrite Hvisited, Howner. intro Hin.
        pose proof (ThreadDomain.contains_nodup D) as Hdomain_nodup.
        rewrite Hparts in Hdomain_nodup.
        pose proof (NoDup_remove_2 done remaining owner Hdomain_nodup)
          as Hnotin.
        apply Hnotin. apply in_or_app. now left. }
      destruct (actual_scan_order_selected current a loc row_remaining Hactual)
        as [Hselected_saved Hselected_present].
      assert (Hselected_live : array_live a (pair owner loc)).
      { apply (proj2 ((proj1 (proj2 (proj2 (proj2 Hwf))))
          owner loc)).
        rewrite <- Howner. exact Hselected_present. }
      assert (Hselected_current : current_nodes current (pair owner loc)).
      { split; [simpl; symmetry; exact Howner|exact Hselected_saved]. }
      assert (Hselected_notignored :
        ~ scan_status progress (pair owner loc) Ignored).
      { intro Hignored. inversion Hignored; subst.
        - apply Howner_new. simpl in H. exact H.
        - rewrite Hcurrent in H. inversion H; subst c.
          apply H1. exact Hselected_current. }
      change (node_cuts_available actor progress a Delta) in Hcuts.
      assert (Hselected_cut :
        node_cut_view actor progress (pair owner loc) value Delta).
      { eapply Hcuts; eauto. }
      assert (Hrow_relation : forall n node_ts,
        current_nodes current n ->
        ~ as_garbage a n ->
        as_timestamps a n = Some node_ts ->
        n = pair owner loc \/ timestamp_lt node_ts ts).
      { pose proof Hrowview as Hrowview0.
        destruct Hrowview0 as
          (p & pi & N & Hposs & Htoken & Hsnap & Hsaved & Hcovered & Horder).
        destruct (Hall _ _ Hposs) as
          (p0 & Heqp & Hpool & Hprotocol & Htimestamp & Hsession).
        inversion Heqp; subst p0.
        eapply row_selected_timestamp_relation with
          (p := p) (N := N) (remaining := row_remaining); eauto.
        - exact (proj1 (proj2 (proj2 Hwf))).
        - exact (proj2 (proj2 (proj2 Hwf))). }
      assert (Hselected_valid : candidate_interval_valid
        (observed_candidate value owner loc ts) a).
      { unfold candidate_interval_valid, observed_candidate. simpl.
        destruct ts; simpl; auto. }
      assert (Hseen_timestamped_post :
        seen_timestamped (finish_progress progress current)
          (end_scan actor progress current a)).
      { unfold seen_timestamped, finish_progress, set_union, end_scan.
        simpl. intros n [Hold_seen|Hcurrent_node].
        - now apply Hseen_timestamped.
        - eapply current_nodes_timestamped.
          + exact (conj Hwf (conj Hall Hrect)).
          + exact Hrowview.
          + exact Howner.
          + exact Hcurrent_node. }
      assert (HIpost : I
        (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          (pair (ArrayReady (end_scan actor progress current a)) tss') Delta)).
      { split.
        - apply concrete_wf_end_scan. exact Hwf.
        - split.
          + intros rho pi Hposs.
            destruct (Hall _ _ Hposs) as
              (p & -> & Hpool & Hprotocol & Htimestamp & Hsession).
            exists p. split; [reflexivity|]. split.
            * now apply pool_represents_end_scan.
            * split; [exact Hprotocol|].
              split; [now apply timestamp_pending_edges_end_scan|exact Hsession].
          + exact Hrect. }
      assert (Hcuts_post : node_cuts_available actor
        (finish_progress progress current) a Delta).
      { unfold node_cuts_available. intros n node_value Hlive Hnode_value
          Hnotignored.
        assert (Hold_notignored : ~ scan_status progress n Ignored)
          by (eapply not_ignored_before_finish; eauto).
        destruct (Hcuts n node_value Hlive Hnode_value Hold_notignored) as
          (p & pi & N & Hposs & Htoken & Hsnap & Hvalue0 & Hmember & Hcut).
        exists p, pi, N. repeat split; try assumption.
        intros newer Hnewer Hnewer_live Hedge.
        eapply not_ignored_after_finish; [exact Hcurrent|].
        eapply Hcut; eauto. }
      assert (Hacc_post : ScanAccumulator actor (done ++ [owner])
        (finish_progress progress current)
        (pair (choose_candidate owner (pair (pair value ts) loc) (fst scan))
          (snd scan))
        (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          (pair (ArrayReady (end_scan actor progress current a)) tss') Delta)).
      { unfold ScanAccumulator, PendingAccumulator in *.
        destruct (fst scan) as [previous|] eqn:Hchoice.
        - destruct Hacc as [Hprevious_view [Hprevious_valid Hprevious_max]].
          destruct (timestamp_ltb (candidate_timestamp previous) ts)
            eqn:Hcomparison.
          + assert (Hnewer : timestamp_lt
              (candidate_timestamp previous) ts)
              by now apply timestamp_ltb_spec.
            assert (Hselected_max : candidate_maximal
              (observed_candidate value owner loc ts)
              (finish_progress progress current) a).
            { eapply selected_candidate_maximal_newer; eauto.
              exact (proj1 (proj2 (proj2 Hwf))). }
            assert (Hselected_view : candidate_view actor (done ++ [owner])
              (observed_candidate value owner loc ts) Delta).
            { eapply selected_candidate_view_from_cut; eauto. }
            cbn [choose_candidate].
            rewrite Hcomparison. simpl.
            change (candidate_view actor (done ++ [owner])
                (observed_candidate value owner loc ts) Delta /\
              candidate_interval_valid
                (observed_candidate value owner loc ts) a /\
              candidate_maximal (observed_candidate value owner loc ts)
                (finish_progress progress current) a).
            repeat split; assumption.
          + assert (Hnotnewer : ~ timestamp_lt
              (candidate_timestamp previous) ts)
              by now apply timestamp_ltb_false_spec.
            assert (Hprevious_max_post : candidate_maximal previous
              (finish_progress progress current) a).
            { eapply previous_candidate_maximal_retained; eauto.
              exact (proj1 (proj2 (proj2 Hwf))). }
            assert (Hprevious_view_post : candidate_view actor
              (done ++ [owner]) previous Delta).
            { eapply retained_candidate_view_after_row; eauto. }
            cbn [choose_candidate].
            rewrite Hcomparison. simpl.
            change (candidate_view actor (done ++ [owner]) previous Delta /\
              candidate_interval_valid previous a /\
              candidate_maximal previous (finish_progress progress current) a).
            repeat split; assumption.
        - destruct Hacc as [Hempty Hseen_garbage].
          assert (Hselected_max : candidate_maximal
            (observed_candidate value owner loc ts)
            (finish_progress progress current) a).
          { eapply selected_candidate_maximal_none; eauto.
            exact (proj1 (proj2 (proj2 Hwf))). }
          assert (Hselected_view : candidate_view actor (done ++ [owner])
            (observed_candidate value owner loc ts) Delta).
          { eapply selected_candidate_view_from_cut; eauto. }
          cbn [choose_candidate].
          change (candidate_view actor (done ++ [owner])
              (observed_candidate value owner loc ts) Delta /\
            candidate_interval_valid
              (observed_candidate value owner loc ts) a /\
            candidate_maximal (observed_candidate value owner loc ts)
              (finish_progress progress current) a).
          repeat split; assumption. }
      exists Delta. split; [apply ac_steps_refl|]. split.
      - unfold ScanFold. split; [exact HIpost|]. split; [exact Hactor|].
        split; [unfold concrete_array, end_scan; simpl;
          exact Hcounter_none|].
        exists (done ++ [owner]), (finish_progress progress current).
        repeat split.
        + rewrite Hparts, <- app_assoc. reflexivity.
        + unfold end_scan. simpl. apply TMap.gss.
        + unfold finish_progress. simpl. rewrite Hvisited, Howner. reflexivity.
        + now apply scan_seen_wf_finish.
        + exact Hseen_timestamped_post.
        + apply (proj1 (token_view_ALinExists
            (pair (ArrayReady (end_scan actor progress current a)) tss')
            actor Delta _)).
          apply (proj2 (token_view_ALinExists
            (pair (ArrayReady a) tss') actor Delta _)). exact Hfallback.
        + apply (proj1 (token_view_ALinExists
            (pair (ArrayReady (end_scan actor progress current a)) tss')
            actor Delta _)).
          apply (proj2 (token_view_ALinExists
            (pair (ArrayReady a) tss') actor Delta _)). exact Hsnapshot_token.
        + exact Hsnapshot.
        + exact Hcuts_post.
        + exact Hacc_post.
        + exact Hsession_token.
      - apply G_end_scan.
    Qed.

    Lemma scan_fold_row_no_error actor owner remaining scan :
      ⊨ ScanFold actor (owner :: remaining) scan ==>>
        AssertionsSet.A.ANoError
          (Build_ThreadEvent actor (InvEv (inl (array_getTop owner)))).
    Proof.
      intros [[control tss] Delta]
        [HI [Hactor [Hcounter_none Hrest]]] Herror.
      destruct Hrest as
        (done & progress & Hparts & Hscan & Hvisited & Hidle & Hseenwf &
          Hseen_timestamped & Hfallback & Hsnapshot_token & Hsnapshot & Hcuts &
          Hacc & Hsession_token).
      assert (Howner_domain : ThreadDomain.contains D owner).
      { unfold ThreadDomain.contains. rewrite Hparts.
        apply in_or_app. right. now left. }
      assert (Howner_new : ~ In owner (scan_visited progress)).
      { rewrite Hvisited. intro Hin.
        pose proof (ThreadDomain.contains_nodup D) as Hnodup.
        rewrite Hparts in Hnodup.
        pose proof (NoDup_remove_2 done remaining owner Hnodup) as Hnotin.
        apply Hnotin. apply in_or_app. now left. }
      simpl in Herror.
      inversion Herror; subst; try contradiction.
      - change (TMap.find actor (as_scans s) = Some progress) in Hscan.
        rewrite Hscan in H2. discriminate.
      - change (TMap.find actor (as_scans s) = Some progress) in Hscan.
        rewrite Hscan in H1. inversion H1; subst p.
        destruct H3; [contradiction|congruence].
    Qed.

    (** The early exit of the scan: a node stamped after the session start
        is outside the recorded start set (Lemma 4.3 of the plan), so the
        elimination response of the specification applies to it.  The
        value is read from the concrete array, where it is immutable. *)
    Definition ElimReady (actor : tid) (v : A) (owner : tid) (loc : Addr) :
        assertion :=
      fun w =>
        I w /\
        ThreadDomain.contains D actor /\
        TMap.find actor
          (as_pending_counters
            (concrete_array (SetPossState.σ w))) = None /\
        SnapshotExists actor w /\
        SessionToken actor start w /\
        as_values (concrete_array (SetPossState.σ w)) (pair owner loc) =
          Some v /\
        exists N0, StartSet actor N0 w /\ ~ N0 (pair owner loc).

    Lemma elim_ready_entails_I actor v owner loc :
      ⊨ ElimReady actor v owner loc ==>> I.
    Proof. intros w [HI _]. exact HI. Qed.

    Lemma elim_ready_stable actor v owner loc :
      AssertionsSet.A.Stable (R actor) I (ElimReady actor v owner loc).
    Proof.
      unfold AssertionsSet.A.Stable, AssertionsSet.A.ComposeA,
        ElimReady, R.
      intros w [Hcompose HI'].
      destruct Hcompose as [pre [Hpre HR]].
      destruct Hpre as
        (HI & Hactor & Hcounter_none & Hsnapshot & Hsession_token & Hvalue &
          N0 & Hstart_set & Houtside).
      destruct HR as
        (Htoken & Hlocal & Hcausal & Harray_local & Hpending & Hcandidate &
          Hrow & Hevolve & Hclock & Haligned & Hcuts_pres & Hgarbage &
          Hintervals & Hsession_equiv).
      destruct w as [sigma' Delta'].
      destruct pre as [sigma Delta]. simpl in *.
      split; [exact HI'|]. split; [exact Hactor|]. split.
      - unfold array_local_state in Harray_local.
        pose proof (f_equal snd Harray_local) as Hcounter_eq.
        simpl in Hcounter_eq. congruence.
      - split.
        + destruct Hsnapshot as (N & local & Hsnd & Hview).
          exists N, local. split; [exact Hsnd|].
          now apply (proj1 Hlocal).
        + split.
          * eapply session_token_stable;
              [exact Hsession_equiv|exact Hsession_token].
          * split.
            -- apply (proj2 (proj2 Hintervals)). exact Hvalue.
            -- exists N0. split; [|exact Houtside].
               eapply start_set_stable;
                 [exact Hsession_equiv|exact Hstart_set].
    Qed.

    Lemma getTop_row_elim_res_update actor owner remaining scan
        value ts loc :
      timestamp_ltb start ts = true ->
      AssertionsSet.PUpdate (G actor)
        (Build_ThreadEvent actor
          (ResEv (inl (array_getTop owner))
            (@inl (@LNode A) nat (pair (pair value ts) loc))))
        (ScanPending actor owner remaining scan)
        (ElimReady actor value owner loc).
    Proof.
      intros Hcmp [control tss] Delta Hpre [control' tss'] Hstep.
      simpl in Hstep. destruct Hstep as [Harray ->].
      destruct (array_getTop_nonempty_res_shape actor owner value ts loc _ _
        Harray) as
        (a & progress0 & current0 & row_remaining & -> & -> & Hscan0 &
          Hcurrent0 & Howner0 & Hactual & Hvalue & Hselected_timestamp).
      destruct Hpre as [HIpre [Hactor [Hcounter_none Hpre]]].
      destruct Hpre as
        (done & progress & current & Hparts & Hscan & Hvisited & Hcurrent &
          Howner & Hseenwf & Hseen_timestamped & Hrowview & Hnodup & Hfallback &
          Hsnapshot_token & Hsnapshot & Hcuts & Hacc & Hcounter & Hincl &
          Hsession_token).
      destruct HIpre as [Hwf [Hall [Hrect Hcounter_protocol]]].
      assert (HIpost : I
        (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          (pair (ArrayReady (end_scan actor progress current a)) tss') Delta)).
      { split.
        - apply concrete_wf_end_scan. exact Hwf.
        - split.
          + intros rho pi Hposs.
            destruct (Hall _ _ Hposs) as
              (p & -> & Hpool & Hprotocol & Htimestamp & Hsession).
            exists p. split; [reflexivity|]. split.
            * now apply pool_represents_end_scan.
            * split; [exact Hprotocol|].
              split; [now apply timestamp_pending_edges_end_scan|exact Hsession].
          + exact (conj Hrect Hcounter_protocol). }
      destruct (ac_nonempty Delta) as (rho_seed & pi_seed & Hseed).
      destruct (Hall _ _ Hseed) as
        (p_seed & -> & Hpool_seed & Hprotocol_seed & Htimestamp_seed &
          Hsession_seed).
      assert (Hseed_ts : TMap.find actor (lp_pop_ts p_seed) = Some start)
        by exact (Hsession_token _ _ Hseed).
      destruct (proj2 Hsession_seed actor start Hseed_ts) as [N0 Hseed_starts].
      destruct (proj1 Hsession_seed actor N0 Hseed_starts) as
        (c & Hc_token & Hc_clock & Hc_members).
      destruct (Hc_token start Hseed_ts) as (u & Hstart_eq & Hcu).
      assert (Hstart_set : forall rho pi, Delta rho pi ->
        session_starts actor rho = Some N0).
      { intros rho pi Hposs.
        destruct (Hall _ _ Hposs) as (p & -> & _ & _ & _ & _).
        pose proof (proj1 Hrect p_seed pi_seed p pi Hseed Hposs) as Hshared.
        destruct Hshared as (_ & _ & _ & _ & Hstarts_eq & _).
        unfold session_starts, session_state. simpl.
        rewrite <- Hstarts_eq. exact Hseed_starts. }
      assert (Houtside : ~ N0 (pair owner loc)).
      { intro Hmember.
        destruct (Hc_members _ Hmember) as (l & u' & Hts_member & Hlt).
        change (as_timestamps a (pair owner loc) = Some (TSInterval l u'))
          in Hts_member.
        rewrite Hselected_timestamp in Hts_member.
        inversion Hts_member; subst ts.
        apply timestamp_ltb_spec in Hcmp. rewrite Hstart_eq in Hcmp.
        simpl in Hcmp.
        pose proof (timestamp_defined_wf a _ _
          (proj1 (proj2 (proj2 Hwf))) Hselected_timestamp) as Hwf_ts.
        simpl in Hwf_ts. lia. }
      exists Delta. split; [apply ac_steps_refl|]. split.
      - unfold ElimReady. split; [exact HIpost|]. split; [exact Hactor|].
        split; [unfold concrete_array, end_scan; simpl;
          exact Hcounter_none|].
        split; [exact Hsnapshot|]. split; [exact Hsession_token|].
        split.
        + unfold concrete_array, array_payload, end_scan. simpl. exact Hvalue.
        + exists N0. split; [exact Hstart_set|exact Houtside].
      - apply G_end_scan.
    Qed.

    (** The loop assertion over the flagged accumulator. *)
    Definition ElimFold (actor : tid) (remaining : list tid)
        (acc : @ElimScan A) : assertion :=
      match acc with
      | ScanOngoing scan => ScanFold actor remaining scan
      | ScanEliminated v owner loc => ElimReady actor v owner loc
      end.

    Lemma elim_fold_entails_I actor remaining acc :
      ⊨ ElimFold actor remaining acc ==>> I.
    Proof.
      destruct acc as [scan|v owner loc]; simpl.
      - apply scan_fold_entails_I.
      - apply elim_ready_entails_I.
    Qed.

    Lemma elim_fold_stable actor remaining acc :
      AssertionsSet.A.Stable (R actor) I (ElimFold actor remaining acc).
    Proof.
      destruct acc as [scan|v owner loc]; simpl.
      - apply scan_fold_stable.
      - apply elim_ready_stable.
    Qed.

    Lemma getTop_row_elim_any_res_update actor owner remaining scan
        value ts loc :
      AssertionsSet.PUpdate (G actor)
        (Build_ThreadEvent actor
          (ResEv (inl (array_getTop owner))
            (@inl (@LNode A) nat (pair (pair value ts) loc))))
        (ScanPending actor owner remaining scan)
        (ElimFold actor remaining
          (if timestamp_ltb start ts
           then ScanEliminated value owner loc
           else ScanOngoing
             (pair (choose_candidate owner (pair (pair value ts) loc)
               (fst scan)) (snd scan)))).
    Proof.
      destruct (timestamp_ltb start ts) eqn:Hcmp.
      - apply getTop_row_elim_res_update. exact Hcmp.
      - apply getTop_row_nonempty_res_update.
    Qed.

    Lemma getTop_row_step_triple actor owner remaining acc :
      SetLogic.HTripleProvable (R actor) (G actor) I actor
        (ElimFold actor (owner :: remaining) acc)
        (scan_step_elim D start acc owner)
        (fun acc' => ElimFold actor remaining acc').
    Proof.
      destruct acc as [scan|v owner' loc].
      - cbv beta iota delta [scan_step_elim].
        eapply SetLogic.provable_vis_safe with
          (P' := ScanPending actor owner remaining scan)
          (Q' := fun result =>
            match result with
            | inl node =>
                ElimFold actor remaining
                  (match node with
                   | pair (pair v ts) loc =>
                     if timestamp_ltb start ts
                     then ScanEliminated v owner loc
                     else ScanOngoing
                       (pair (choose_candidate owner node (fst scan))
                         (snd scan))
                   end)
            | inr count =>
                ScanFold actor remaining
                  (pair (fst scan) (Nat.add (snd scan) count))
            end).
        + apply scan_fold_row_no_error.
        + apply scan_pending_entails_I.
        + intros [node|count].
          * destruct node as [[value ts] loc]. apply elim_fold_entails_I.
          * apply scan_fold_entails_I.
        + apply scan_pending_stable.
        + intros [node|count].
          * destruct node as [[value ts] loc]. apply elim_fold_stable.
          * apply scan_fold_stable.
        + apply getTop_row_inv_update.
        + intros [node|count].
          * destruct node as [[value ts] loc].
            apply getTop_row_elim_any_res_update.
          * apply getTop_row_empty_res_update.
        + intros [node|count].
          * destruct node as [[value ts] loc].
            eapply SetLogic.provable_ret_safe.
            -- apply ImplRefl.
            -- apply elim_fold_entails_I.
            -- apply elim_fold_stable.
          * eapply SetLogic.provable_ret_safe.
            -- apply ImplRefl.
            -- apply scan_fold_entails_I.
            -- apply scan_fold_stable.
      - cbv beta iota delta [scan_step_elim].
        eapply SetLogic.provable_ret_safe.
        + apply ImplRefl.
        + apply (elim_fold_entails_I actor remaining
            (ScanEliminated v owner' loc)).
        + apply (elim_fold_stable actor remaining
            (ScanEliminated v owner' loc)).
    Qed.

    (** Restrict the possibility set to the Cartesian slice that carries
        [actor]'s local snapshot/token choice from [donor].  Rectangularity
        guarantees that this slice still has a representative of every
        other thread's local choice.  This is the set-valued counterpart of
        selecting one summand of the paper's [⊕] assertion. *)
    Variant ac_actor_slice_prop
        (Delta : @AbstractConfig _ (li_lts F)) (actor : tid)
        (donor : @ListPoolState A)
        (donor_pi : tmap (@LinState (li_sig F))) :
        @AbstractConfigProp _ (li_lts F) :=
    | ACActorSlice p pi
        (Hposs : Delta (LPReady p) pi)
        (Hsnapshot : TMap.find actor (lp_snapshots p) =
          TMap.find actor (lp_snapshots donor))
        (Htoken : TMap.find actor pi = TMap.find actor donor_pi) :
        ac_actor_slice_prop Delta actor donor donor_pi (LPReady p) pi.

    Program Definition ac_actor_slice
        (Delta : @AbstractConfig _ (li_lts F)) (actor : tid)
        (donor : @ListPoolState A)
        (donor_pi : tmap (@LinState (li_sig F)))
        (Hdonor : Delta (LPReady donor) donor_pi) :
        @AbstractConfig _ (li_lts F) :=
      {| ac_active := ac_active Delta;
         ac_prop := ac_actor_slice_prop Delta actor donor donor_pi |}.
    Next Obligation.
      exists (LPReady donor), donor_pi. constructor; auto.
    Qed.
    Next Obligation.
      inversion H; subst. eapply ac_domain; eauto.
    Qed.

    Lemma ac_actor_slice_cases Delta actor donor donor_pi Hdonor p pi :
      ac_actor_slice Delta actor donor donor_pi Hdonor (LPReady p) pi ->
      Delta (LPReady p) pi /\
      TMap.find actor (lp_snapshots p) =
        TMap.find actor (lp_snapshots donor) /\
      TMap.find actor pi = TMap.find actor donor_pi.
    Proof. inversion 1; subst. auto. Qed.

    Lemma ac_actor_slice_subset_steps Delta actor donor donor_pi Hdonor :
      ac_subset (ac_actor_slice Delta actor donor donor_pi Hdonor)
        (ac_steps Delta).
    Proof. intros rho pi Hslice. inversion Hslice; subst.
      now apply ac_steps_refl. Qed.

    Lemma ac_actor_slice_receiver Delta actor donor donor_pi Hdonor
        receiver receiver_pi :
      possibility_rectangular Delta ->
      Delta (LPReady receiver) receiver_pi ->
      exists p pi,
        ac_actor_slice Delta actor donor donor_pi Hdonor (LPReady p) pi /\
        branch_merge actor donor donor_pi receiver receiver_pi p pi.
    Proof.
      intros [_ Hmerge] Hreceiver.
      destruct (Hmerge actor donor donor_pi receiver receiver_pi Hdonor
        Hreceiver) as (p & pi & Hposs & Hmerged).
      exists p, pi. split; [|exact Hmerged].
      destruct Hmerged as (_ & Hsnapshot & Htoken & _).
      constructor; assumption.
    Qed.

    Lemma possibility_rectangular_actor_slice Delta actor donor donor_pi
        Hdonor :
      possibility_rectangular Delta ->
      possibility_rectangular
        (ac_actor_slice Delta actor donor donor_pi Hdonor).
    Proof.
      intros [Hshared Hmerge]. split.
      - intros p1 pi1 p2 pi2 H1 H2.
        apply ac_actor_slice_cases in H1.
        apply ac_actor_slice_cases in H2.
        destruct H1 as [Hposs1 _]. destruct H2 as [Hposs2 _].
        eapply Hshared; eassumption.
      - intros observer p1 pi1 p2 pi2 H1 H2.
        pose proof H1 as H1'. pose proof H2 as H2'.
        apply ac_actor_slice_cases in H1'.
        apply ac_actor_slice_cases in H2'.
        destruct H1' as [Hposs1 [Hsnap1 Htoken1]].
        destruct H2' as [Hposs2 [Hsnap2 Htoken2]].
        destruct (Hmerge observer p1 pi1 p2 pi2 Hposs1 Hposs2) as
          (p & pi & Hposs & Hmerged).
        exists p, pi. split; [|exact Hmerged].
        destruct Hmerged as
          (_ & Hsnapshot & Htoken & Hforeign_snapshot & Hforeign_token).
        constructor; [exact Hposs| |].
        + destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
          * congruence.
          * rewrite Hforeign_snapshot by congruence. exact Hsnap2.
        + destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
          * congruence.
          * rewrite Hforeign_token by congruence. exact Htoken2.
    Qed.

    Lemma session_equiv_actor_slice Delta actor donor donor_pi Hdonor
        observer :
      possibility_rectangular Delta ->
      (forall rho pi, Delta rho pi -> exists p, rho = LPReady p) ->
      session_equiv observer Delta
        (ac_actor_slice Delta actor donor donor_pi Hdonor).
    Proof.
      intros Hrect Hready. apply session_equiv_of_covers.
      - intros rho pi Hposs. destruct (Hready _ _ Hposs) as (p & ->).
        destruct (ac_actor_slice_receiver Delta actor donor donor_pi Hdonor
          p pi Hrect Hposs) as (q & qi & Hslice & Hmerged).
        exists (LPReady q), qi. split; [exact Hslice|].
        destruct Hmerged as (Hshared & _).
        apply session_state_shared. exact Hshared.
      - intros rho pi Hslice. inversion Hslice; subst.
        exists (LPReady p), pi. split; [exact Hposs|reflexivity].
    Qed.

    Lemma I_actor_slice sigma Delta actor donor donor_pi Hdonor :
      I (sigma, Delta) ->
      TMap.find actor
        (as_pending_counters (concrete_array sigma)) = None ->
      I (sigma, ac_actor_slice Delta actor donor donor_pi Hdonor).
    Proof.
      intros [Hwf [Hall [Hrect Hcounter]]] Hcounter_none.
      split; [exact Hwf|]. split.
      - intros rho pi Hslice. inversion Hslice; subst. now apply Hall.
      - split; [now apply possibility_rectangular_actor_slice|].
        intros owner saved Hpending.
        destruct (Hcounter owner saved Hpending) as
          (rho & pi & start0 & Hposs & Htoken).
        destruct (Hall _ _ Hposs) as (p & -> & Hrep).
        destruct (PositiveMap.E.eq_dec actor owner) as [->|Hneq].
        + simpl in Hpending. rewrite Hcounter_none in Hpending. discriminate.
        + destruct (ac_actor_slice_receiver Delta actor donor donor_pi
              Hdonor p pi Hrect Hposs) as (q & qi & Hslice & Hmerged).
          exists (LPReady q), qi, start0. split; [exact Hslice|].
          destruct Hmerged as (_ & _ & _ & _ & Hforeign).
          rewrite Hforeign by congruence. exact Htoken.
    Qed.

    Definition getTop_candidate_rho (actor : tid)
        (rho : abstract_state) : abstract_state :=
      match rho with
      | LPReady p => LPReady (clear_snapshot actor p)
      | LPAtomicPending p pending op => LPAtomicPending p pending op
      end.

    Lemma pool_shared_eq_clear_snapshot_compat actor p q :
      pool_shared_eq p q ->
      pool_shared_eq (clear_snapshot actor p) (clear_snapshot actor q).
    Proof. unfold pool_shared_eq, clear_snapshot; simpl; tauto. Qed.

    Lemma pool_shared_eq_clear_snapshot actor p :
      pool_shared_eq (clear_snapshot actor p) p.
    Proof. unfold pool_shared_eq, clear_snapshot; simpl; repeat split. Qed.

    Lemma pool_protocol_getTop_complete p pi actor ret :
      pool_protocol p pi ->
      TMap.find actor pi = Some (ls_lini (lpool_getTop start)) ->
      pool_protocol (clear_snapshot actor p)
        (TMap.add actor (ls_linr (lpool_getTop start) ret) pi).
    Proof.
      intros (Hpush & Hsnapshot & Hpushback & Hstartpop & Hstartpopback &
        Hgettop) Hactive.
      unfold pool_protocol.
      repeat match goal with |- _ /\ _ => split end.
      - intros owner loc Hfind. simpl in Hfind.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + destruct (Hpush _ _ Hfind) as (v & Htoken).
          rewrite Hactive in Htoken. discriminate.
        + destruct (Hpush _ _ Hfind) as (v & Htoken). exists v.
          rewrite TMap.gso by exact Hneq. exact Htoken.
      - intros owner N Hfind. simpl in Hfind.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite TMap.grs in Hfind. discriminate.
        + rewrite TMap.gso by exact Hneq. eapply Hsnapshot.
          rewrite TMap.gro in Hfind by exact Hneq. exact Hfind.
      - intros owner v Htoken. simpl.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite TMap.gss in Htoken. discriminate.
        + rewrite TMap.gso in Htoken by exact Hneq. eauto.
      - intros owner N0 Hstarts Hts. simpl in Hstarts, Hts.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + specialize (Hstartpop _ _ Hstarts Hts).
          rewrite Hactive in Hstartpop. discriminate.
        + rewrite TMap.gso by exact Hneq. eauto.
      - intros owner Htoken. simpl.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite TMap.gss in Htoken. discriminate.
        + rewrite TMap.gso in Htoken by exact Hneq. eauto.
      - intros owner start0 Htoken. simpl.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite TMap.gss in Htoken. discriminate.
        + rewrite TMap.gso in Htoken by exact Hneq. eauto.
    Qed.

    Lemma timestamp_pending_edges_clear_snapshot sigma p actor :
      timestamp_pending_edges sigma p ->
      timestamp_pending_edges sigma (clear_snapshot actor p).
    Proof.
      unfold timestamp_pending_edges, outgoing_before, clear_snapshot; simpl.
      tauto.
    Qed.

    Lemma snapshot_vertex_owner_in_domain sigma p actor N n :
      concrete_wf sigma ->
      pool_represents (concrete_array sigma) p ->
      TMap.find actor (lp_snapshots p) = Some N ->
      N n -> In (fst n) (ThreadDomain.threads D).
    Proof.
      intros Hwf Hrep Hsnapshot Hmember.
      pose proof (proj1 (proj2 (proj2 (proj2 (proj2 Hwf)))) n
        ((proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hrep))))))
          actor N Hsnapshot n Hmember)) as Hcontains.
      exact Hcontains.
    Qed.

    Lemma visited_top_all_is_top sigma p actor N n :
      concrete_wf sigma ->
      pool_represents (concrete_array sigma) p ->
      TMap.find actor (lp_snapshots p) = Some N ->
      visited_top (ThreadDomain.threads D) p N n ->
      lp_top (fun n' => N n' /\ ~ lp_garbage p n') (lp_edges p) n.
    Proof.
      intros Hwf Hrep Hsnapshot [Hmember [Hlive Htop]]. split.
      - split; assumption.
      - intros newer [Hnewer Hnewer_live].
        apply Htop; try assumption.
        eapply snapshot_vertex_owner_in_domain; eauto.
    Qed.

    Lemma candidate_slice_poss_steps sigma Delta actor candidate
        donor donor_pi (N : LPNodeSet)
        Hdonor
        (Htoken : TMap.find actor donor_pi = Some (ls_lini (lpool_getTop start)))
        (Hsnapshot : TMap.find actor (lp_snapshots donor) = Some N)
        (Hvalue : lp_vertices donor
          (pair (candidate_owner candidate) (candidate_loc candidate)) =
          Some (candidate_value candidate))
        (Hstatus : lp_garbage donor
            (pair (candidate_owner candidate) (candidate_loc candidate)) \/
          visited_top (ThreadDomain.threads D) donor N
            (pair (candidate_owner candidate) (candidate_loc candidate)))
        p pi
        (Hslice : ac_actor_slice Delta actor donor donor_pi Hdonor
          (LPReady p) pi) :
      concrete_wf sigma ->
      (forall rho qi, Delta rho qi -> branch_represents sigma rho qi) ->
      possibility_rectangular Delta ->
      @poss_steps (li_sig F) (li_lts F)
        (@PossOk (li_sig F) (li_lts F) (LPReady p) pi)
        (@PossOk (li_sig F) (li_lts F)
          (getTop_candidate_rho actor (LPReady p))
          (TMap.add actor
            (ls_linr (lpool_getTop start)
              (YSuccNode (candidate_value candidate)
                (candidate_owner candidate) (candidate_loc candidate))) pi)).
    Proof.
      intros Hwf Hall [Hshared _]. apply ac_actor_slice_cases in Hslice.
      destruct Hslice as [Hposs [Hsnapshot_eq Htoken_eq]].
      destruct (Hall _ _ Hposs) as (p0 & Heq & Hrep).
      inversion Heq; subst p0.
      destruct Hrep as [Hpool [Hprotocol Htimestamp]].
      destruct (Hall _ _ Hdonor) as (donor0 & Hdonor_eq & Hdonor_rep).
      inversion Hdonor_eq; subst donor0.
      destruct Hdonor_rep as [Hdonor_pool _].
      pose proof (Hshared donor donor_pi p pi Hdonor Hposs) as Hshared_dp.
      destruct Hshared_dp as
        (Hvertices & Hedges & Hpending_pushes & Hgarbage & Hpop_starts & Hpop_ts).
      assert (Htoken_p : TMap.find actor pi =
        Some (ls_lini (lpool_getTop start))).
      { rewrite Htoken_eq. exact Htoken. }
      assert (Hsnapshot_p : TMap.find actor (lp_snapshots p) =
        Some N).
      { rewrite Hsnapshot_eq. exact Hsnapshot. }
      assert (Hvalue_p : lp_vertices p
          (pair (candidate_owner candidate) (candidate_loc candidate)) =
        Some (candidate_value candidate)).
      { rewrite <- Hvertices. exact Hvalue. }
      apply rt_step. eapply ps_ret; [|exact Htoken_p].
      destruct Hstatus as [Hgarbage_donor|Hvisited].
      - eapply step_getTop_garbage_res with (N := N).
        + exact Hsnapshot_p.
        + rewrite <- Hgarbage. exact Hgarbage_donor.
        + exact Hvalue_p.
        + reflexivity.
      - eapply step_getTop_top_res with (N := N).
        + exact Hsnapshot_p.
        + pose proof (visited_top_all_is_top sigma donor actor N _ Hwf
            Hdonor_pool Hsnapshot Hvisited) as Htop.
          unfold lp_top in *. destruct Htop as [Hmember Htop]. split.
          * destruct Hmember as [HN Hlive]. split; [exact HN|].
            rewrite <- Hgarbage. exact Hlive.
          * intros newer [HN Hlive]. rewrite <- Hedges.
            apply Htop. split; [exact HN|].
            rewrite Hgarbage. exact Hlive.
        + exact Hvalue_p.
        + reflexivity.
    Qed.

    Lemma I_getTop_candidate_image (sigma : concrete_state)
        (Delta : @AbstractConfig _ (li_lts F)) actor ret
        (Hsteps : forall rho pi, Delta rho pi ->
          @poss_steps (li_sig F) (li_lts F)
            (@PossOk (li_sig F) (li_lts F) rho pi)
            (@PossOk (li_sig F) (li_lts F)
              (getTop_candidate_rho actor rho)
              (TMap.add actor (ls_linr (lpool_getTop start) ret) pi))) :
      I (sigma, Delta) ->
      (forall rho pi, Delta rho pi ->
        TMap.find actor pi = Some (ls_lini (lpool_getTop start))) ->
      TMap.find actor
        (as_pending_counters (concrete_array sigma)) = None ->
      I (sigma, ac_image Delta (getTop_candidate_rho actor)
        (fun pi => TMap.add actor (ls_linr (lpool_getTop start) ret) pi) Hsteps).
    Proof.
      intros [Hwf [Hall [Hrect Hcounter]]] Hlinearizing Hcounter_none.
      split; [exact Hwf|]. split.
      - intros rho pi Himage.
        destruct (ac_image_elim _ _ _ _ _ _ Himage) as
          (rho0 & pi0 & Hposs & -> & ->).
        destruct (Hall _ _ Hposs) as
          (p & -> & Hpool & Hprotocol & Htimestamp & Hsession).
        exists (clear_snapshot actor p). split; [reflexivity|]. split.
        + now apply pool_represents_clear_snapshot.
        + split.
          * eapply pool_protocol_getTop_complete; eauto.
          * split; [now apply timestamp_pending_edges_clear_snapshot|exact Hsession].
      - split.
        + destruct Hrect as [Hshared Hmerge]. split.
          * intros p1 pi1 p2 pi2 Himage1 Himage2.
            destruct (ac_image_elim _ _ _ _ _ _ Himage1) as
              (rho1 & qi1 & Hposs1 & Hrho1 & ->).
            destruct (ac_image_elim _ _ _ _ _ _ Himage2) as
              (rho2 & qi2 & Hposs2 & Hrho2 & ->).
            destruct (Hall _ _ Hposs1) as (q1 & -> & Hrep1).
            destruct (Hall _ _ Hposs2) as (q2 & -> & Hrep2).
            simpl in Hrho1, Hrho2. inversion Hrho1; inversion Hrho2; subst.
            apply pool_shared_eq_clear_snapshot_compat.
            eapply Hshared; eassumption.
          * intros observer p1 pi1 p2 pi2 Himage1 Himage2.
            destruct (ac_image_elim _ _ _ _ _ _ Himage1) as
              (rho1 & qi1 & Hposs1 & Hrho1 & Hpi1).
            destruct (ac_image_elim _ _ _ _ _ _ Himage2) as
              (rho2 & qi2 & Hposs2 & Hrho2 & Hpi2).
            destruct (Hall _ _ Hposs1) as (q1 & Hq1 & Hrep1).
            destruct (Hall _ _ Hposs2) as (q2 & Hq2 & Hrep2).
            subst rho1 rho2. simpl in Hrho1, Hrho2.
            inversion Hrho1; inversion Hrho2; subst p1 p2 pi1 pi2.
            destruct (Hmerge observer q1 qi1 q2 qi2 Hposs1 Hposs2) as
              (q & qi & Hposs & Hmerged).
            exists (clear_snapshot actor q),
              (TMap.add actor (ls_linr (lpool_getTop start) ret) qi). split.
            -- change (ac_image_prop Delta (getTop_candidate_rho actor)
                 (fun pi => TMap.add actor (ls_linr (lpool_getTop start) ret) pi)
                 Hsteps (getTop_candidate_rho actor (LPReady q))
                 (TMap.add actor (ls_linr (lpool_getTop start) ret) qi)).
               constructor. exact Hposs.
            -- destruct Hmerged as
                 (Hshared' & Hsnapshot & Htoken & Hforeign_snapshot &
                   Hforeign_token).
               unfold branch_merge. split;
                 [now apply pool_shared_eq_clear_snapshot_compat|].
               repeat split.
               ++ unfold clear_snapshot; simpl.
                  destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
                  ** rewrite !TMap.grs. reflexivity.
                  ** rewrite !TMap.gro by exact Hneq. exact Hsnapshot.
               ++ destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
                  ** rewrite !TMap.gss. reflexivity.
                  ** rewrite !TMap.gso by congruence. exact Htoken.
               ++ intros other Hother. unfold clear_snapshot; simpl.
                  destruct (PositiveMap.E.eq_dec other actor) as [->|Hneq].
                  ** rewrite !TMap.grs. reflexivity.
                  ** rewrite !TMap.gro by exact Hneq.
                     now apply Hforeign_snapshot.
               ++ intros other Hother.
                  destruct (PositiveMap.E.eq_dec other actor) as [->|Hneq].
                  ** rewrite !TMap.gss. reflexivity.
                  ** rewrite !TMap.gso by congruence.
                     now apply Hforeign_token.
        + intros owner saved Hpending. simpl in Hpending.
          destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
          * rewrite Hcounter_none in Hpending. discriminate.
          * destruct (Hcounter owner saved Hpending) as
              (rho & pi & start0 & Hposs & Htoken).
            exists (getTop_candidate_rho actor rho),
              (TMap.add actor (ls_linr (lpool_getTop start) ret) pi), start0.
            split; [constructor; exact Hposs|].
            rewrite TMap.gso by congruence. exact Htoken.
    Qed.

    Lemma getTop_candidate_image_completed (sigma : concrete_state)
        (Delta : @AbstractConfig _ (li_lts F)) actor ret Hsteps :
      I (sigma, ac_image Delta (getTop_candidate_rho actor)
        (fun pi => TMap.add actor (ls_linr (lpool_getTop start) ret) pi) Hsteps) ->
      Completed actor (lpool_getTop start) ret
        (sigma, ac_image Delta (getTop_candidate_rho actor)
          (fun pi => TMap.add actor (ls_linr (lpool_getTop start) ret) pi) Hsteps).
    Proof.
      intro HI. split; [exact HI|]. intros rho pi Himage.
      destruct (ac_image_elim _ _ _ _ _ _ Himage) as
        (rho0 & pi0 & Hposs & -> & ->). apply TMap.gss.
    Qed.

    Definition foreign_branch_cover (observer : tid)
        (Delta Delta' : @AbstractConfig _ (li_lts F)) : Prop :=
      forall p pi, Delta (LPReady p) pi ->
        exists q qi,
          Delta' (LPReady q) qi /\
          pool_shared_eq q p /\
          TMap.find observer (lp_snapshots q) =
            TMap.find observer (lp_snapshots p) /\
          TMap.find observer qi = TMap.find observer pi.

    Lemma visited_top_shared done p q N n :
      pool_shared_eq q p ->
      visited_top done p N n -> visited_top done q N n.
    Proof.
      intros (_ & Hedges & _ & Hgarbage & Hpop_starts & Hpop_ts) [HN [Hlive Htop]].
      split; [exact HN|]. split.
      - rewrite Hgarbage. exact Hlive.
      - intros newer Hnewer Hdone Hnewer_live.
        rewrite Hedges. apply Htop; try assumption.
        rewrite <- Hgarbage. exact Hnewer_live.
    Qed.

    Lemma candidate_tstop_safe_shared candidate p q N :
      pool_shared_eq q p ->
      candidate_tstop_safe candidate p N ->
      candidate_tstop_safe candidate q N.
    Proof.
      intros (_ & Hedges & _ & Hgarbage & Hpop_starts & Hpop_ts).
      unfold candidate_tstop_safe.
      destruct (candidate_timestamp candidate); simpl; auto.
      intros Hsafe newer HN Hlive. rewrite Hedges.
      apply Hsafe; try assumption. rewrite <- Hgarbage. exact Hlive.
    Qed.

    Lemma foreign_cover_candidate_views observer Delta Delta' :
      foreign_branch_cover observer Delta Delta' ->
      candidate_views_preserved observer Delta Delta'.
    Proof.
      intros Hcover done candidate Hview. unfold candidate_view in *.
      destruct Hview as
        (p & pi & N & Hposs & Htoken & Hsnapshot & Hvalue & Hdone &
          Hstatus & Hsafe).
      destruct (Hcover p pi Hposs) as
        (q & qi & Hq & Hshared & Hsnapshot_eq & Htoken_eq).
      exists q, qi, N. repeat split; try assumption.
      - rewrite Htoken_eq. exact Htoken.
      - rewrite Hsnapshot_eq. exact Hsnapshot.
      - destruct Hshared as (Hvertices & _). rewrite Hvertices. exact Hvalue.
      - destruct Hstatus as [Hgarbage|Htop].
        + left. destruct Hshared as (_ & _ & _ & Hgarbage_eq & Hpop_starts & Hpop_ts).
          rewrite Hgarbage_eq. exact Hgarbage.
        + right. eapply visited_top_shared; eauto.
      - eapply candidate_tstop_safe_shared; eauto.
    Qed.

    Lemma foreign_cover_row_snapshot_views observer Delta Delta' :
      foreign_branch_cover observer Delta Delta' ->
      row_snapshot_views_preserved observer Delta Delta'.
    Proof.
      intros Hcover owner saved Hview. unfold row_snapshot_view in *.
      destruct Hview as
        (p & pi & N & Hposs & Htoken & Hsnapshot & Hsaved & Hlive & Horder).
      destruct (Hcover p pi Hposs) as
        (q & qi & Hq & Hshared & Hsnapshot_eq & Htoken_eq).
      destruct Hshared as (Hvertices & Hedges & _ & Hgarbage & Hpop_starts & Hpop_ts).
      exists q, qi, N. repeat split; try assumption.
      - rewrite Htoken_eq. exact Htoken.
      - rewrite Hsnapshot_eq. exact Hsnapshot.
      - intros loc HN Hlive_q. apply Hlive; [exact HN|].
        rewrite <- Hgarbage. exact Hlive_q.
      - intros newer older Hnewer Holder Hnewer_live Holder_live Hedge.
        apply Horder; try assumption.
        + rewrite <- Hgarbage. exact Hnewer_live.
        + rewrite <- Hgarbage. exact Holder_live.
        + rewrite <- Hedges. exact Hedge.
    Qed.

    Lemma foreign_cover_candidate_row_views observer Delta Delta' :
      foreign_branch_cover observer Delta Delta' ->
      candidate_row_views_preserved observer Delta Delta'.
    Proof.
      intros Hcover done candidate owner saved Hview.
      unfold candidate_row_view in *.
      destruct Hview as
        (p & pi & N & Hposs & Htoken & Hsnapshot & Hvalue & Hdone &
          Hstatus & Hcovered & Horder & Hsafe).
      destruct (Hcover p pi Hposs) as
        (q & qi & Hq & Hshared & Hsnapshot_eq & Htoken_eq).
      destruct Hshared as (Hvertices & Hedges & Hpending & Hgarbage & Hpop_starts & Hpop_ts).
      exists q, qi, N. repeat split; try assumption.
      - rewrite Htoken_eq. exact Htoken.
      - rewrite Hsnapshot_eq. exact Hsnapshot.
      - rewrite Hvertices. exact Hvalue.
      - destruct Hstatus as [Hgarbage_p|Htop].
        + left. rewrite Hgarbage. exact Hgarbage_p.
        + right. eapply visited_top_shared; eauto.
          repeat split; assumption.
      - intros loc HN Hlive. apply Hcovered; [exact HN|].
        rewrite <- Hgarbage. exact Hlive.
      - intros newer older Hnewer Holder Hnewer_live Holder_live Hedge.
        apply Horder; try assumption.
        + rewrite <- Hgarbage. exact Hnewer_live.
        + rewrite <- Hgarbage. exact Holder_live.
        + rewrite <- Hedges. exact Hedge.
      - eapply candidate_tstop_safe_shared; eauto.
        repeat split; assumption.
    Qed.

    Lemma foreign_cover_node_cuts observer sigma Delta Delta' :
      foreign_branch_cover observer Delta Delta' ->
      node_cuts_preserved observer sigma sigma Delta Delta'.
    Proof.
      intros Hcover progress start0 Hinside Hfallback Hsession_all Hcuts n value Hlive Hvalue
        Hnotignored.
      destruct (Hcuts n value Hlive Hvalue Hnotignored) as
        (p & pi & N & Hposs & Htoken & Hsnapshot & Hnode_value & Hmember &
          Hcut).
      destruct (Hcover p pi Hposs) as
        (q & qi & Hq & Hshared & Hsnapshot_eq & Htoken_eq).
      destruct Hshared as (Hvertices & Hedges & Hpending & Hgarbage & Hpop_starts & Hpop_ts).
      exists q, qi, N. repeat split; try assumption.
      - rewrite Htoken_eq. exact Htoken.
      - rewrite Hsnapshot_eq. exact Hsnapshot.
      - rewrite Hvertices. exact Hnode_value.
      - intros newer Hnewer Hnewer_live Hedge.
        apply Hcut; try assumption.
        + rewrite <- Hgarbage. exact Hnewer_live.
        + rewrite <- Hedges. exact Hedge.
    Qed.

    Lemma candidate_image_foreign_cover
        (Delta : @AbstractConfig _ (li_lts F)) actor donor donor_pi Hdonor ret
        (Hsteps : forall rho pi,
          ac_actor_slice Delta actor donor donor_pi Hdonor rho pi ->
          @poss_steps (li_sig F) (li_lts F)
            (@PossOk (li_sig F) (li_lts F) rho pi)
            (@PossOk (li_sig F) (li_lts F)
              (getTop_candidate_rho actor rho)
              (TMap.add actor (ls_linr (lpool_getTop start) ret) pi)))
        observer :
      actor <> observer ->
      possibility_rectangular Delta ->
      foreign_branch_cover observer Delta
        (ac_image (ac_actor_slice Delta actor donor donor_pi Hdonor)
          (getTop_candidate_rho actor)
          (fun pi => TMap.add actor (ls_linr (lpool_getTop start) ret) pi) Hsteps).
    Proof.
      intros Hneq Hrect p pi Hposs.
      destruct (ac_actor_slice_receiver Delta actor donor donor_pi Hdonor
        p pi Hrect Hposs) as (q & qi & Hslice & Hmerged).
      destruct Hmerged as
        (Hshared & Hactor_snapshot & Hactor_token & Hforeign_snapshot &
          Hforeign_token).
      exists (clear_snapshot actor q),
        (TMap.add actor (ls_linr (lpool_getTop start) ret) qi).
      split.
      - change (ac_image_prop
          (ac_actor_slice Delta actor donor donor_pi Hdonor)
          (getTop_candidate_rho actor)
          (fun pi => TMap.add actor (ls_linr (lpool_getTop start) ret) pi) Hsteps
          (getTop_candidate_rho actor (LPReady q))
          (TMap.add actor (ls_linr (lpool_getTop start) ret) qi)).
        constructor. exact Hslice.
      - split.
        + eapply pool_shared_eq_trans.
          * apply pool_shared_eq_clear_snapshot.
          * exact Hshared.
        + split.
          * unfold clear_snapshot; simpl. rewrite TMap.gro by congruence.
            now apply Hforeign_snapshot.
          * rewrite TMap.gso by congruence. now apply Hforeign_token.
    Qed.

    Lemma G_getTop_candidate_image sigma
        (Delta : @AbstractConfig _ (li_lts F)) actor donor donor_pi Hdonor ret
        (Hsteps : forall rho pi,
          ac_actor_slice Delta actor donor donor_pi Hdonor rho pi ->
          @poss_steps (li_sig F) (li_lts F)
            (@PossOk (li_sig F) (li_lts F) rho pi)
            (@PossOk (li_sig F) (li_lts F)
              (getTop_candidate_rho actor rho)
              (TMap.add actor (ls_linr (lpool_getTop start) ret) pi)))
        (Hready : forall rho pi, Delta rho pi ->
          exists p, rho = LPReady p) :
      possibility_rectangular Delta ->
      G actor (sigma, Delta)
        (sigma,
          ac_image (ac_actor_slice Delta actor donor donor_pi Hdonor)
            (getTop_candidate_rho actor)
            (fun pi => TMap.add actor (ls_linr (lpool_getTop start) ret) pi) Hsteps).
    Proof.
      intro Hrect. unfold G.
      refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
        (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))))).
      - intros observer Hneq. apply token_equiv_rely. intro token. split.
        + intros (p & pi & Hposs & Htoken).
          destruct (Hready _ _ Hposs) as (p0 & ->).
          destruct (candidate_image_foreign_cover Delta actor donor donor_pi
            Hdonor ret Hsteps observer Hneq Hrect p0 pi Hposs) as
            (q & qi & Himage & Hshared & Hsnapshot_eq & Htoken_eq).
          exists (LPReady q), qi. split; [exact Himage|].
          rewrite Htoken_eq. exact Htoken.
        + intros (rho & pi & Himage & Htoken).
          destruct (ac_image_elim _ _ _ _ _ _ Himage) as
            (rho0 & pi0 & Hslice & Hrho & Hpi).
          inversion Hslice; subst rho0. subst rho pi.
          exists (LPReady p), pi0. split; [exact Hposs|].
          rewrite TMap.gso in Htoken by congruence. exact Htoken.
      - intros observer Hneq. split.
        + intros local (rho & pi & Hposs & Hlocal).
          destruct (Hready _ _ Hposs) as (p & ->).
          destruct (candidate_image_foreign_cover Delta actor donor donor_pi
            Hdonor ret Hsteps observer Hneq Hrect p pi Hposs) as
            (q & qi & Himage & Hshared & Hsnapshot_eq & Htoken_eq).
          exists (LPReady q), qi. split; [exact Himage|].
          unfold pool_local_state in *. simpl in *.
          destruct Hshared as (_ & _ & Hpending & Hgarbage & Hpop_starts & Hpop_ts).
          rewrite Hpending, Hsnapshot_eq. exact Hlocal.
        + intros local' (rho & pi & Himage & Hlocal).
          destruct (ac_image_elim _ _ _ _ _ _ Himage) as
            (rho0 & pi0 & Hslice & Hrho & Hpi).
          inversion Hslice; subst rho0. subst rho pi.
          exists (pool_local_state observer (LPReady p)). split.
          * exists (LPReady p), pi0. split; [exact Hposs|reflexivity].
          * unfold pool_local_state, getTop_candidate_rho,
              clear_snapshot in *. simpl in *.
            exact (f_equal fst Hlocal).
      - intros observer loc lower Hneq Hcausal rho pi Himage.
        destruct (ac_image_elim _ _ _ _ _ _ Himage) as
          (rho0 & pi0 & Hslice & Hrho & Hpi).
        inversion Hslice; subst rho0. subst rho pi.
        destruct (Hcausal (LPReady p) pi0 Hposs) as
          (p0 & Heq & Hpending & Hbefore).
        inversion Heq; subst p0. exists (clear_snapshot actor p).
        split; [reflexivity|]. split; [exact Hpending|].
        unfold outgoing_before, clear_snapshot in *. simpl in *.
        exact Hbefore.
      - intros observer Hneq. reflexivity.
      - intros observer Hneq. reflexivity.
      - intros observer Hneq.
        apply foreign_cover_candidate_views.
        now apply candidate_image_foreign_cover.
      - intros observer Hneq.
        apply foreign_cover_row_snapshot_views.
        now apply candidate_image_foreign_cover.
      - apply array_evolves_refl.
      - apply Nat.le_refl.
      - intros observer Hneq.
        apply foreign_cover_candidate_row_views.
        now apply candidate_image_foreign_cover.
      - intros observer Hneq.
        apply foreign_cover_node_cuts.
        now apply candidate_image_foreign_cover.
      - apply garbage_evolves_refl.
      - apply intervals_evolve_refl.
      - intros observer Hneq. eapply session_equiv_trans.
        + apply session_equiv_actor_slice; [exact Hrect|exact Hready].
        + apply session_equiv_image_foreign. intro rho.
          destruct rho; reflexivity.
    Qed.

    Lemma getTop_candidate_commit_update actor candidate count :
      AssertionsSet.PUpdateId (G actor)
        (ScanFold actor nil (pair (Some candidate) count))
        (Completed actor (lpool_getTop start)
          (YSuccNode (candidate_value candidate)
            (candidate_owner candidate) (candidate_loc candidate))).
    Proof.
      intros sigma Delta Hpre.
      destruct Hpre as [HI [Hactor [Hcounter_none Hrest]]].
      destruct Hrest as
        (done & progress & Hparts & Hscan & Hvisited & Hidle & Hseenwf &
          Hseen_timestamped & Hfallback & Hsnapshot_token & Hsnapshot & Hcuts &
          Hacc & Hsession_token).
      unfold ScanAccumulator in Hacc. simpl in Hacc.
      destruct Hacc as [Hview [Hvalid Hmax]].
      unfold candidate_view in Hview.
      destruct Hview as
        (donor & donor_pi & N & Hdonor & Htoken & Hsnapshot_donor & Hvalue &
          Hdone & Hstatus & Hsafe).
      rewrite app_nil_r in Hparts. subst done.
      pose proof HI as HI0.
      destruct HI as [Hwf [Hall [Hrect Hcounter]]].
      destruct Htoken as [start' Htoken].
      assert (Hstart' : start' = start).
      { destruct (Hall _ _ Hdonor) as
          (donor0 & Heqd & _ & Hprotocol_d & _ & _).
        inversion Heqd; subst donor0.
        pose proof (proj2 (proj2 (proj2 (proj2 (proj2 Hprotocol_d))))
          actor start' Htoken) as Hts'.
        pose proof (Hsession_token _ _ Hdonor) as Hts.
        unfold session_ts, session_state in Hts. simpl in Hts.
        rewrite Hts' in Hts. injection Hts as Heq. exact Heq. }
      subst start'.
      set (Slice := ac_actor_slice Delta actor donor donor_pi Hdonor).
      set (ret := YSuccNode (candidate_value candidate)
        (candidate_owner candidate) (candidate_loc candidate)).
      assert (Hsteps : forall rho pi, Slice rho pi ->
        @poss_steps (li_sig F) (li_lts F)
          (@PossOk (li_sig F) (li_lts F) rho pi)
          (@PossOk (li_sig F) (li_lts F)
            (getTop_candidate_rho actor rho)
            (TMap.add actor (ls_linr (lpool_getTop start) ret) pi))).
      { intros rho pi Hslice. inversion Hslice; subst rho.
        unfold ret. eapply candidate_slice_poss_steps with
          (N := N) (donor := donor) (donor_pi := donor_pi)
          (Hdonor := Hdonor); eauto. }
      set (Delta' := ac_image Slice (getTop_candidate_rho actor)
        (fun pi => TMap.add actor (ls_linr (lpool_getTop start) ret) pi) Hsteps).
      assert (Hslice_I : I (sigma, Slice)).
      { unfold Slice. eapply I_actor_slice; eauto. }
      assert (Hslice_token : forall rho pi, Slice rho pi ->
        TMap.find actor pi = Some (ls_lini (lpool_getTop start))).
      { intros rho pi Hslice. inversion Hslice; subst. congruence. }
      assert (Hpost_I : I (sigma, Delta')).
      { unfold Delta'. eapply I_getTop_candidate_image; eauto. }
      exists Delta'. split.
      - unfold Delta', Slice.
        eapply ac_steps_subset_trans.
        + apply ac_actor_slice_subset_steps.
        + apply ac_image_subset_steps.
      - split.
        + unfold Delta', ret.
          now apply getTop_candidate_image_completed.
        + unfold Delta', Slice.
          eapply G_getTop_candidate_image; [|exact Hrect].
          intros rho pi Hposs.
          destruct (Hall _ _ Hposs) as (p & -> & Hrep).
          now exists p.
    Qed.

    Lemma getTop_candidate_exit_triple actor candidate count :
      SetLogic.HTripleProvable (R actor) (G actor) I actor
        (ScanFold actor nil (pair (Some candidate) count))
        (Ret (YSuccNode (candidate_value candidate)
          (candidate_owner candidate) (candidate_loc candidate)))
        (fun ret => Completed actor (lpool_getTop start) ret).
    Proof.
      eapply SetLogic.provable_linstep with
        (P' := Completed actor (lpool_getTop start)
          (YSuccNode (candidate_value candidate)
            (candidate_owner candidate) (candidate_loc candidate))).
      - apply completed_entails_I.
      - apply completed_stable.
      - apply getTop_candidate_commit_update.
      - eapply SetLogic.provable_ret_safe.
        + apply ImplRefl.
        + apply completed_entails_I.
        + apply completed_stable.
    Qed.

    (** The elimination exit: restrict to the branches carrying the
        actor's snapshot (which, by the protocol, also carry its interval
        token) and apply the elimination response in each of them. *)
    Lemma getTop_elim_commit_update actor (v : A) owner loc :
      AssertionsSet.PUpdateId (G actor)
        (ElimReady actor v owner loc)
        (Completed actor (lpool_getTop start) (YSuccNode v owner loc)).
    Proof.
      intros sigma Delta Hpre.
      destruct Hpre as
        (HI & Hactor & Hcounter_none & Hsnapshot & Hsession_token & Hvalue &
          N0 & Hstart_set & Houtside).
      pose proof HI as HI0.
      destruct HI as [Hwf [Hall [Hrect Hcounter]]].
      destruct Hsnapshot as (N & local & Hsnd & rho_d & donor_pi & Hdonor0 & Hlocal).
      destruct (Hall _ _ Hdonor0) as
        (donor & Heqd & Hpool_d & Hprotocol_d & _ & _).
      subst rho_d.
      assert (Hsnapshot_donor : TMap.find actor (lp_snapshots donor) = Some N).
      { unfold pool_local_state in Hlocal.
        pose proof (f_equal snd Hlocal) as Hsnd'. simpl in Hsnd'.
        exact (eq_trans Hsnd' Hsnd). }
      destruct (proj1 (proj2 Hprotocol_d) actor N Hsnapshot_donor) as
        [start' Htoken_d].
      assert (Hstart' : start' = start).
      { pose proof (proj2 (proj2 (proj2 (proj2 (proj2 Hprotocol_d))))
          actor start' Htoken_d) as Hts'.
        pose proof (Hsession_token _ _ Hdonor0) as Hts.
        unfold session_ts, session_state in Hts. simpl in Hts.
        rewrite Hts' in Hts. injection Hts as Heq. exact Heq. }
      subst start'.
      set (Slice := ac_actor_slice Delta actor donor donor_pi Hdonor0).
      set (ret := YSuccNode v owner loc).
      assert (Hsteps : forall rho pi, Slice rho pi ->
        @poss_steps (li_sig F) (li_lts F)
          (@PossOk (li_sig F) (li_lts F) rho pi)
          (@PossOk (li_sig F) (li_lts F)
            (getTop_candidate_rho actor rho)
            (TMap.add actor (ls_linr (lpool_getTop start) ret) pi))).
      { intros rho pi Hslice.
        destruct rho as [p|p pending op]; [|inversion Hslice].
        apply ac_actor_slice_cases in Hslice.
        destruct Hslice as [Hposs1 [Hsnapshot_eq Htoken_eq]].
        destruct (Hall _ _ Hposs1) as (p0 & Heq & Hpool & Hprotocol & _ & _).
        inversion Heq; subst p0.
        apply rt_step. eapply ps_ret; [|rewrite Htoken_eq; exact Htoken_d].
        unfold ret.
        eapply step_getTop_elim_res with (N := N) (N0 := N0).
        - rewrite Hsnapshot_eq. exact Hsnapshot_donor.
        - pose proof (Hstart_set _ _ Hposs1) as Hs.
          unfold session_starts, session_state in Hs. simpl in Hs. exact Hs.
        - exact Houtside.
        - rewrite (proj1 Hpool). exact Hvalue.
        - reflexivity. }
      set (Delta' := ac_image Slice (getTop_candidate_rho actor)
        (fun pi => TMap.add actor (ls_linr (lpool_getTop start) ret) pi) Hsteps).
      assert (Hslice_I : I (sigma, Slice)).
      { unfold Slice. eapply I_actor_slice; eauto. }
      assert (Hslice_token : forall rho pi, Slice rho pi ->
        TMap.find actor pi = Some (ls_lini (lpool_getTop start))).
      { intros rho pi Hslice. inversion Hslice; subst. congruence. }
      assert (Hpost_I : I (sigma, Delta')).
      { unfold Delta'. eapply I_getTop_candidate_image; eauto. }
      exists Delta'. split.
      - unfold Delta', Slice.
        eapply ac_steps_subset_trans.
        + apply ac_actor_slice_subset_steps.
        + apply ac_image_subset_steps.
      - split.
        + unfold Delta', ret.
          now apply getTop_candidate_image_completed.
        + unfold Delta', Slice.
          eapply G_getTop_candidate_image; [|exact Hrect].
          intros rho pi Hposs.
          destruct (Hall _ _ Hposs) as (p & -> & Hrep).
          now exists p.
    Qed.

    Lemma getTop_elim_exit_triple actor (v : A) owner loc :
      SetLogic.HTripleProvable (R actor) (G actor) I actor
        (ElimReady actor v owner loc)
        (Ret (YSuccNode v owner loc))
        (fun ret => Completed actor (lpool_getTop start) ret).
    Proof.
      eapply SetLogic.provable_linstep with
        (P' := Completed actor (lpool_getTop start) (YSuccNode v owner loc)).
      - apply completed_entails_I.
      - apply completed_stable.
      - apply getTop_elim_commit_update.
      - eapply SetLogic.provable_ret_safe.
        + apply ImplRefl.
        + apply completed_entails_I.
        + apply completed_stable.
    Qed.

    Definition CounterPending (actor : tid) (scan_count : nat) : assertion :=
      fun w =>
        I w /\
        ThreadDomain.contains D actor /\
        exists saved,
          TMap.find actor
            (as_pending_counters
              (concrete_array (SetPossState.σ w))) = Some saved /\
          scan_count <= saved /\
          EmptyEvidence (ThreadDomain.threads D) scan_count
            (concrete_array (SetPossState.σ w)) /\
          actor ↦∃◦((lpool_getTop start)) w /\
          actor ↦∃•((lpool_getTop start)) w /\
          actor ↦∃•((lpool_getTop start), YFail) w /\
          (scan_count = saved ->
            actor ↦∃•((lpool_getTop start), YSuccEmpty) w) /\
          SessionToken actor start w.

    Lemma counter_pending_entails_I actor count :
      ⊨ CounterPending actor count ==>> I.
    Proof. firstorder. Qed.

    Lemma counter_pending_stable actor count :
      AssertionsSet.A.Stable (R actor) I (CounterPending actor count).
    Proof.
      unfold AssertionsSet.A.Stable, AssertionsSet.A.ComposeA,
        CounterPending, R.
      intros w [Hcompose HI']. destruct Hcompose as [pre [Hpre HR]].
      destruct Hpre as [HI [Hactor Hrest]].
      destruct Hrest as
        (saved & Hpending & Hbound & Hempty & Hfallback & Hlinearizing &
          Hfail & Hempty_result & Hsession_token).
      destruct HR as
        (Htoken & Hlocal & Hcausal & Harray_local & Hts_pending & Hcandidate &
          Hrow & Hevolve & Hclock & Hcandidate_row & Hcuts & Hgarbage &
          Hintervals & Hsession_equiv).
      destruct w as [sigma' Delta'], pre as [sigma Delta]. simpl in *.
      pose proof (empty_evidence_stable (ThreadDomain.threads D) count
        sigma sigma' Hempty Hevolve) as Hempty'.
      destruct Hempty' as [Hempty_bound Hempty_orders].
      split; [exact HI'|]. split; [exact Hactor|]. exists saved.
      repeat split; try assumption.
      - unfold array_local_state in Harray_local.
        pose proof (f_equal snd Harray_local) as Heq. simpl in Heq.
        congruence.
      - eapply token_rely_ALinExists; eauto.
      - eapply token_rely_ALinExists; eauto.
      - eapply token_rely_ALinExists; eauto.
      - intro Heq. eapply token_rely_ALinExists; eauto.
      - eapply session_token_stable; [exact Hsession_equiv|exact Hsession_token].
    Qed.

    Definition array_counter_inv_kind
        (ev : @ThreadEvent (@ESPListArray A)) : bool :=
      match te_ev ev with
      | InvEv array_getCounter => true
      | _ => false
      end.

    Lemma array_counter_inv_shape actor control control' :
      @StepSPListArray A D
        (Build_ThreadEvent actor (InvEv array_getCounter)) control control' ->
      exists a,
        control = ArrayReady a /\
        control' = ArrayReady (start_counter D actor a) /\
        ThreadDomain.contains D actor /\
        TMap.find actor (as_pending_counters a) = None.
    Proof.
      intro Hstep. remember (Build_ThreadEvent actor
        (InvEv array_getCounter)) as ev eqn:Hev in Hstep.
      inversion Hstep.
      all: match goal with
        | Hctor : ?remembered = ?rhs,
          Htarget : ?remembered = ?target |- _ =>
            let Hevent := fresh "Hevent" in
            pose proof (eq_trans (eq_sym Htarget) Hctor) as Hevent;
            let Hkind := fresh "Hkind" in
            pose proof (f_equal array_counter_inv_kind Hevent) as Hkind;
            cbv [array_counter_inv_kind] in Hkind;
            first [discriminate Hkind |
              dependent destruction Hevent;
              eexists; repeat split; eauto]
        end.
    Qed.

    Lemma concrete_wf_start_counter a tss actor :
      concrete_wf (pair (ArrayReady a) tss) ->
      concrete_wf (pair (ArrayReady (start_counter D actor a)) tss).
    Proof. unfold concrete_wf, concrete_array, concrete_timestamp,
      array_payload, start_counter; simpl; tauto. Qed.

    Lemma branch_represents_start_counter a tss actor rho pi :
      branch_represents (pair (ArrayReady a) tss) rho pi ->
      branch_represents
        (pair (ArrayReady (start_counter D actor a)) tss) rho pi.
    Proof.
      intros (p & -> & Hpool & Hprotocol & Htimestamp & Hsession).
      exists p. split; [reflexivity|]. split.
      - unfold pool_represents, start_counter in *. simpl in *. exact Hpool.
      - split; [exact Hprotocol|].
        unfold timestamp_pending_edges, concrete_array, concrete_timestamp,
          array_payload, start_counter in *. simpl in *. split; [exact Htimestamp|exact Hsession].
    Qed.

    Lemma G_start_counter (a : @SPListArrayState A)
        (tss : TimestampState) actor
        (Delta : @AbstractConfig _ (li_lts F)) :
      G actor
        (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          (pair (ArrayReady a) tss) Delta)
        (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          (pair (ArrayReady (start_counter D actor a)) tss) Delta).
    Proof.
      unfold G. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
        (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))))).
      - intros observer Hneq. apply token_rely_refl.
      - intros observer Hneq. apply pool_local_equiv_refl.
      - intros observer loc lower Hneq.
        unfold push_causal, concrete_array, array_payload, start_counter.
        simpl. tauto.
      - intros observer Hneq. unfold array_local_state, concrete_array,
          array_payload, start_counter. simpl. rewrite TMap.gso by congruence.
        reflexivity.
      - intros observer Hneq. reflexivity.
      - intros observer Hneq. apply candidate_views_preserved_refl.
      - intros observer Hneq. apply row_snapshot_views_preserved_refl.
      - eapply array_evolves_of_counter_order; intro owner; reflexivity.
      - apply Nat.le_refl.
      - intros observer Hneq. apply candidate_row_views_preserved_refl.
      - intros observer Hneq progress start0 Hinside Hfallback Hsession_all Hcuts.
        unfold node_cuts_available, concrete_array, array_payload,
          start_counter in *. simpl in *. exact Hcuts.
      - unfold garbage_evolves, concrete_array, array_payload,
          start_counter. simpl. tauto.
      - unfold intervals_evolve, concrete_array, array_payload,
          start_counter. simpl. split; firstorder.
      - intros observer Hneq. apply session_equiv_refl.
    Qed.

    Definition getTop_atomic_rho (rho : abstract_state) : abstract_state :=
      match rho with
      | LPReady p => LPReady p
      | LPAtomicPending p pending op => LPAtomicPending p pending op
      end.

    Definition ac_actor_alternative
        (Delta : @AbstractConfig _ (li_lts F)) actor donor donor_pi Hdonor
        (ret : @YResult A)
        (Hsteps : forall rho pi,
          ac_actor_slice Delta actor donor donor_pi Hdonor rho pi ->
          @poss_steps (li_sig F) (li_lts F)
            (@PossOk (li_sig F) (li_lts F) rho pi)
            (@PossOk (li_sig F) (li_lts F) (getTop_atomic_rho rho)
              (atomic_tokens actor (lpool_getTop start) ret pi))) :
        @AbstractConfig _ (li_lts F) :=
      ac_image (ac_actor_slice Delta actor donor donor_pi Hdonor)
        getTop_atomic_rho (atomic_tokens actor (lpool_getTop start) ret) Hsteps.

    Lemma actor_alternative_source Delta actor donor donor_pi Hdonor ret
        Hsteps p pi :
      ac_actor_alternative Delta actor donor donor_pi Hdonor ret Hsteps
        (LPReady p) pi ->
      exists pi0,
        ac_actor_slice Delta actor donor donor_pi Hdonor (LPReady p) pi0 /\
        pi = atomic_tokens actor (lpool_getTop start) ret pi0.
    Proof.
      intro Halternative. unfold ac_actor_alternative in Halternative.
      destruct (ac_image_elim _ _ _ _ _ _ Halternative) as
        (rho & pi0 & Hslice & Hrho & Hpi).
      destruct rho; simpl in Hrho; try discriminate.
      inversion Hrho; subst. exists pi0.
      split; [exact Hslice|reflexivity].
    Qed.

    Lemma actor_alternative_subset_steps Delta actor donor donor_pi Hdonor ret
        Hsteps :
      ac_subset
        (ac_actor_alternative Delta actor donor donor_pi Hdonor ret Hsteps)
        (ac_steps Delta).
    Proof.
      unfold ac_actor_alternative. eapply ac_steps_subset_trans.
      - apply ac_actor_slice_subset_steps.
      - apply ac_image_subset_steps.
    Qed.

    Lemma possibility_rectangular_actor_alternative Delta actor donor donor_pi
        Hdonor ret Hsteps :
      possibility_rectangular Delta ->
      possibility_rectangular
        (ac_actor_alternative Delta actor donor donor_pi Hdonor ret Hsteps).
    Proof.
      intro Hrect. unfold ac_actor_alternative.
      eapply possibility_rectangular_atomic_image with (f := fun p => p).
      - reflexivity.
      - intros rho q Hrho. destruct rho; simpl in Hrho;
          try discriminate. inversion Hrho; subst. eexists; split; reflexivity.
      - intros p q Hshared. exact Hshared.
      - intros observer p. reflexivity.
      - now apply possibility_rectangular_actor_slice.
    Qed.

    Lemma actor_alternative_foreign_cover Delta actor donor donor_pi Hdonor
        ret Hsteps observer :
      actor <> observer ->
      possibility_rectangular Delta ->
      foreign_branch_cover observer Delta
        (ac_actor_alternative Delta actor donor donor_pi Hdonor ret Hsteps).
    Proof.
      intros Hneq Hrect p pi Hposs.
      destruct (ac_actor_slice_receiver Delta actor donor donor_pi Hdonor
        p pi Hrect Hposs) as (q & qi & Hslice & Hmerged).
      destruct Hmerged as
        (Hshared & Hactor_snapshot & Hactor_token & Hforeign_snapshot &
          Hforeign_token).
      exists q, (atomic_tokens actor (lpool_getTop start) ret qi). split.
      - unfold ac_actor_alternative.
        change (ac_image_prop
          (ac_actor_slice Delta actor donor donor_pi Hdonor)
          getTop_atomic_rho (atomic_tokens actor (lpool_getTop start) ret) Hsteps
          (getTop_atomic_rho (LPReady q))
          (atomic_tokens actor (lpool_getTop start) ret qi)).
        constructor. exact Hslice.
      - split; [exact Hshared|]. split.
        + now apply Hforeign_snapshot.
        + rewrite atomic_tokens_other by congruence.
          now apply Hforeign_token.
    Qed.

    Definition ac_add_actor_alternative
        (Delta : @AbstractConfig _ (li_lts F)) actor donor donor_pi Hdonor ret
        Hsteps : @AbstractConfig _ (li_lts F) :=
      @ac_union _ (li_lts F) Delta
        (ac_actor_alternative Delta actor donor donor_pi Hdonor ret Hsteps)
        (domain_equiv_refl (ac_active Delta)).

    Lemma ac_add_actor_alternative_keep
        (Delta : @AbstractConfig _ (li_lts F)) actor donor donor_pi Hdonor ret
        Hsteps rho pi :
      Delta rho pi ->
      ac_add_actor_alternative Delta actor donor donor_pi Hdonor ret Hsteps
        rho pi.
    Proof. intro Hposs. apply ac_union_left. exact Hposs. Qed.

    Lemma ac_add_actor_alternative_take
        (Delta : @AbstractConfig _ (li_lts F)) actor donor donor_pi Hdonor ret
        Hsteps rho pi :
      ac_actor_alternative Delta actor donor donor_pi Hdonor ret Hsteps
        rho pi ->
      ac_add_actor_alternative Delta actor donor donor_pi Hdonor ret Hsteps
        rho pi.
    Proof. intro Hposs. apply ac_union_right. exact Hposs. Qed.

    Lemma ac_add_actor_alternative_cases
        (Delta : @AbstractConfig _ (li_lts F)) actor donor donor_pi Hdonor ret
        Hsteps rho pi :
      ac_add_actor_alternative Delta actor donor donor_pi Hdonor ret Hsteps
        rho pi ->
      Delta rho pi \/
      ac_actor_alternative Delta actor donor donor_pi Hdonor ret Hsteps
        rho pi.
    Proof. unfold ac_add_actor_alternative. now apply ac_union_cases. Qed.

    Lemma session_equiv_add_actor_alternative
        (Delta : @AbstractConfig _ (li_lts F)) actor donor donor_pi Hdonor ret
        Hsteps observer :
      session_equiv observer Delta
        (ac_add_actor_alternative Delta actor donor donor_pi Hdonor ret
          Hsteps).
    Proof.
      apply session_equiv_of_covers.
      - intros rho pi Hposs. exists rho, pi.
        split; [now apply ac_add_actor_alternative_keep|reflexivity].
      - intros rho pi Hadded.
        apply ac_add_actor_alternative_cases in Hadded.
        destruct Hadded as [Hbase|Halternative].
        + exists rho, pi. auto.
        + unfold ac_actor_alternative in Halternative.
          destruct (ac_image_elim _ _ _ _ _ _ Halternative) as
            (rho0 & pi0 & Hslice & Hrho & Hpi).
          inversion Hslice; subst rho0. subst rho pi.
          exists (LPReady p), pi0. split; [exact Hposs|reflexivity].
    Qed.

    Lemma ac_add_actor_alternative_subset_steps
        (Delta : @AbstractConfig _ (li_lts F)) actor donor donor_pi
        Hdonor ret Hsteps :
      ac_subset
        (ac_add_actor_alternative Delta actor donor donor_pi Hdonor ret Hsteps)
        (ac_steps Delta).
    Proof.
      intros rho pi Hadded.
      destruct (ac_add_actor_alternative_cases _ _ _ _ _ _ _ _ _ Hadded)
        as [Hkeep|Htake].
      - now apply ac_steps_refl.
      - now apply actor_alternative_subset_steps in Htake.
    Qed.

    Lemma possibility_rectangular_add_actor_alternative
        (Delta : @AbstractConfig _ (li_lts F)) actor donor donor_pi Hdonor ret
        Hsteps :
      possibility_rectangular Delta ->
      possibility_rectangular
        (ac_add_actor_alternative Delta actor donor donor_pi Hdonor ret
          Hsteps).
    Proof.
      intros Hrect. destruct Hrect as [Hshared Hmerge].
      assert (Haltrect : possibility_rectangular
        (ac_actor_alternative Delta actor donor donor_pi Hdonor ret Hsteps)).
      { apply possibility_rectangular_actor_alternative. split; assumption. }
      destruct Haltrect as [Haltshared Haltmerge]. split.
      - intros p1 pi1 p2 pi2 H1 H2.
        apply ac_add_actor_alternative_cases in H1.
        apply ac_add_actor_alternative_cases in H2.
        destruct H1 as [Hbase1|Halt1], H2 as [Hbase2|Halt2].
        + eapply Hshared; eauto.
	        + destruct (actor_alternative_source _ _ _ _ _ _ _ _ _ Halt2)
	            as (qi2 & Hslice2 & ->).
	          apply ac_actor_slice_cases in Hslice2.
	          destruct Hslice2 as [Hsource2 _].
	          eapply Hshared; eassumption.
	        + destruct (actor_alternative_source _ _ _ _ _ _ _ _ _ Halt1)
	            as (qi1 & Hslice1 & ->).
	          apply ac_actor_slice_cases in Hslice1.
	          destruct Hslice1 as [Hsource1 _].
	          eapply Hshared; eassumption.
        + eapply Haltshared; eauto.
      - intros observer p1 pi1 p2 pi2 H1 H2.
        apply ac_add_actor_alternative_cases in H1.
        apply ac_add_actor_alternative_cases in H2.
        destruct H1 as [Hbase1|Halt1], H2 as [Hbase2|Halt2].
        + destruct (Hmerge observer p1 pi1 p2 pi2 Hbase1 Hbase2) as
            (q & qi & Hq & Hmerged).
          exists q, qi. split; [now apply ac_add_actor_alternative_keep|].
          exact Hmerged.
        + destruct (actor_alternative_source _ _ _ _ _ _ _ _ _ Halt2)
            as (qi2 & Hslice2 & Hpi2).
          subst pi2. pose proof Hslice2 as Hslice2'.
          apply ac_actor_slice_cases in Hslice2'.
          destruct Hslice2' as [Hbase2 [Hactor_snapshot2 Hactor_token2]].
          destruct (Hmerge observer p1 pi1 p2 qi2 Hbase1 Hbase2) as
            (q & qi & Hq & Hmerged).
          destruct Hmerged as
            (Hshared' & Hsnapshot & Htoken & Hforeign_snapshot &
              Hforeign_token).
          destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
          * exists q, qi. split; [now apply ac_add_actor_alternative_keep|].
            unfold branch_merge. split; [exact Hshared'|]. repeat split.
            -- exact Hsnapshot.
            -- exact Htoken.
            -- exact Hforeign_snapshot.
            -- intros other Hother. rewrite atomic_tokens_other by congruence.
               now apply Hforeign_token.
          * assert (Hq_snapshot : TMap.find actor (lp_snapshots q) =
                TMap.find actor (lp_snapshots donor)).
            { rewrite Hforeign_snapshot by congruence. exact Hactor_snapshot2. }
            assert (Hq_token : TMap.find actor qi =
                TMap.find actor donor_pi).
            { rewrite Hforeign_token by congruence. exact Hactor_token2. }
            assert (Hqslice : ac_actor_slice Delta actor donor donor_pi Hdonor
                (LPReady q) qi) by (constructor; assumption).
            exists q, (atomic_tokens actor (lpool_getTop start) ret qi). split.
            -- apply ac_add_actor_alternative_take.
               unfold ac_actor_alternative.
               change (ac_image_prop
                 (ac_actor_slice Delta actor donor donor_pi Hdonor)
                 getTop_atomic_rho (atomic_tokens actor (lpool_getTop start) ret)
                 Hsteps (getTop_atomic_rho (LPReady q))
                 (atomic_tokens actor (lpool_getTop start) ret qi)).
               constructor. exact Hqslice.
            -- unfold branch_merge. split; [exact Hshared'|]. repeat split.
               ++ exact Hsnapshot.
               ++ rewrite !atomic_tokens_other by congruence. exact Htoken.
               ++ exact Hforeign_snapshot.
               ++ intros other Hother.
                  destruct (PositiveMap.E.eq_dec other actor) as [->|Hotheractor].
                  ** rewrite !atomic_tokens_same. reflexivity.
                  ** rewrite !atomic_tokens_other by congruence.
                     now apply Hforeign_token.
        + destruct (actor_alternative_source _ _ _ _ _ _ _ _ _ Halt1)
            as (qi1 & Hslice1 & Hpi1).
          subst pi1. pose proof Hslice1 as Hslice1'.
          apply ac_actor_slice_cases in Hslice1'.
          destruct Hslice1' as [Hbase1 [Hactor_snapshot1 Hactor_token1]].
          destruct (Hmerge observer p1 qi1 p2 pi2 Hbase1 Hbase2) as
            (q & qi & Hq & Hmerged).
          destruct Hmerged as
            (Hshared' & Hsnapshot & Htoken & Hforeign_snapshot &
              Hforeign_token).
          destruct (PositiveMap.E.eq_dec observer actor) as [->|Hneq].
          * assert (Hqslice : ac_actor_slice Delta actor donor donor_pi Hdonor
                (LPReady q) qi).
            { constructor; [exact Hq|congruence|congruence]. }
            exists q, (atomic_tokens actor (lpool_getTop start) ret qi). split.
            -- apply ac_add_actor_alternative_take.
               unfold ac_actor_alternative.
               change (ac_image_prop
                 (ac_actor_slice Delta actor donor donor_pi Hdonor)
                 getTop_atomic_rho (atomic_tokens actor (lpool_getTop start) ret)
                 Hsteps (getTop_atomic_rho (LPReady q))
                 (atomic_tokens actor (lpool_getTop start) ret qi)).
               constructor. exact Hqslice.
            -- unfold branch_merge. split; [exact Hshared'|]. repeat split.
               ++ exact Hsnapshot.
               ++ rewrite !atomic_tokens_same. reflexivity.
               ++ exact Hforeign_snapshot.
               ++ intros other Hother. rewrite atomic_tokens_other by congruence.
                  now apply Hforeign_token.
          * exists q, qi. split; [now apply ac_add_actor_alternative_keep|].
            unfold branch_merge. split; [exact Hshared'|]. repeat split.
            -- exact Hsnapshot.
            -- rewrite atomic_tokens_other by congruence. exact Htoken.
	            -- exact Hforeign_snapshot.
	            -- intros other Hother. now apply Hforeign_token.
        + destruct (Haltmerge observer p1 pi1 p2 pi2 Halt1 Halt2) as
            (q & qi & Hq & Hmerged).
          exists q, qi. split; [now apply ac_add_actor_alternative_take|].
          exact Hmerged.
    Qed.

    Lemma I_add_actor_alternative
        (sigma : concrete_state)
        (Delta : @AbstractConfig _ (li_lts F)) actor donor donor_pi Hdonor ret
        Hsteps :
      I (sigma, Delta) ->
      TMap.find actor donor_pi = Some (ls_inv (lpool_getTop start)) ->
      I (sigma,
        ac_add_actor_alternative Delta actor donor donor_pi Hdonor ret
          Hsteps).
    Proof.
      intros [Hwf [Hall [Hrect Hcounter]]] Hinv.
      split; [exact Hwf|]. split.
      - intros rho pi Hadded.
        apply ac_add_actor_alternative_cases in Hadded.
        destruct Hadded as [Hbase|Halternative].
        + now apply Hall.
        + destruct rho as [p|p pending op].
          * destruct (actor_alternative_source _ _ _ _ _ _ _ _ _
                Halternative) as (pi0 & Hslice & ->).
            apply ac_actor_slice_cases in Hslice.
            destruct Hslice as [Hposs [_ Hactor]].
            destruct (Hall _ _ Hposs) as
              (q & Heq & Hpool & Hprotocol & Htimestamp & Hsession).
            inversion Heq; subst q. exists p. split; [reflexivity|].
            split; [exact Hpool|]. split.
            -- eapply pool_protocol_atomic; [exact Hprotocol|].
               rewrite Hactor. exact Hinv.
            -- split; [exact Htimestamp|exact Hsession].
          * exfalso.
            unfold ac_actor_alternative in Halternative.
            destruct (ac_image_elim _ _ _ _ _ _ Halternative) as
              (rho & pi0 & Hslice & Hrho & Hpi).
            destruct rho; [inversion Hrho|inversion Hslice].
      - split.
        + now apply possibility_rectangular_add_actor_alternative.
        + intros owner saved Hpending.
          destruct (Hcounter owner saved Hpending) as
            (rho & pi & start0 & Hposs & Htoken).
          exists rho, pi, start0. split.
          * now apply ac_add_actor_alternative_keep.
          * exact Htoken.
    Qed.

    Lemma add_actor_alternative_foreign_cover
        (Delta : @AbstractConfig _ (li_lts F)) actor donor donor_pi Hdonor ret
        Hsteps observer :
      foreign_branch_cover observer Delta
        (ac_add_actor_alternative Delta actor donor donor_pi Hdonor ret
          Hsteps).
    Proof.
      intros p pi Hposs. exists p, pi. split.
      - now apply ac_add_actor_alternative_keep.
      - split; [apply pool_shared_eq_refl|]. split; reflexivity.
    Qed.

    Lemma G_add_actor_alternative sigma
        (Delta : @AbstractConfig _ (li_lts F)) actor donor donor_pi Hdonor ret
        Hsteps :
      G actor (sigma, Delta)
        (sigma,
          ac_add_actor_alternative Delta actor donor donor_pi Hdonor ret
            Hsteps).
    Proof.
      unfold G.
      refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
        (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))))).
      - intros observer Hneq. apply token_equiv_rely. intro token. split.
        + intros (rho & pi & Hposs & Htoken).
          exists rho, pi. split.
          * now apply ac_add_actor_alternative_keep.
          * exact Htoken.
        + intros (rho & pi & Hadded & Htoken).
          apply ac_add_actor_alternative_cases in Hadded.
          destruct Hadded as [Hbase|Halternative].
          * exists rho, pi. auto.
          * unfold ac_actor_alternative in Halternative.
            destruct (ac_image_elim _ _ _ _ _ _ Halternative) as
              (rho0 & pi0 & Hslice & Hrho & Hpi).
            inversion Hslice; subst rho0. subst rho pi.
            exists (LPReady p), pi0. split; [exact Hposs|].
            rewrite atomic_tokens_other in Htoken by congruence.
            exact Htoken.
      - intros observer Hneq. split.
        + intros local (rho & pi & Hposs & Hlocal).
          exists rho, pi. split.
          * now apply ac_add_actor_alternative_keep.
          * exact Hlocal.
        + intros local' (rho & pi & Hadded & Hlocal).
          apply ac_add_actor_alternative_cases in Hadded.
          destruct Hadded as [Hbase|Halternative].
          * exists local'. split; [exists rho, pi; auto|reflexivity].
          * unfold ac_actor_alternative in Halternative.
            destruct (ac_image_elim _ _ _ _ _ _ Halternative) as
              (rho0 & pi0 & Hslice & Hrho & Hpi).
            inversion Hslice; subst rho0. subst rho pi.
            exists local'. split.
            -- exists (LPReady p), pi0. split; [exact Hposs|].
               exact Hlocal.
            -- reflexivity.
      - intros observer loc lower Hneq Hcausal rho pi Hadded.
        unfold push_causal in Hcausal.
        apply ac_add_actor_alternative_cases in Hadded.
        destruct Hadded as [Hbase|Halternative].
        + simpl. exact (Hcausal rho pi Hbase).
        + unfold ac_actor_alternative in Halternative.
          destruct (ac_image_elim _ _ _ _ _ _ Halternative) as
            (rho0 & pi0 & Hslice & Hrho & Hpi).
          inversion Hslice; subst rho0. subst rho pi.
          simpl. exact (Hcausal (LPReady p) pi0 Hposs).
      - intros observer Hneq. reflexivity.
      - intros observer Hneq. reflexivity.
      - intros observer Hneq. apply foreign_cover_candidate_views.
        apply add_actor_alternative_foreign_cover.
      - intros observer Hneq. apply foreign_cover_row_snapshot_views.
        apply add_actor_alternative_foreign_cover.
      - apply array_evolves_refl.
      - apply Nat.le_refl.
      - intros observer Hneq. apply foreign_cover_candidate_row_views.
        apply add_actor_alternative_foreign_cover.
      - intros observer Hneq. apply foreign_cover_node_cuts.
        apply add_actor_alternative_foreign_cover.
      - apply garbage_evolves_refl.
      - apply intervals_evolve_refl.
      - intros observer Hneq. apply session_equiv_add_actor_alternative.
    Qed.

    Lemma empty_evidence_all_vertices_garbage sigma p count :
      concrete_wf sigma ->
      pool_represents (concrete_array sigma) p ->
      EmptyEvidence (ThreadDomain.threads D) count (concrete_array sigma) ->
      count = total_counter D (concrete_array sigma) ->
      all_vertices_garbage p.
    Proof.
      intros (Htimestamp_valid & Hstamped & Hdefined & Hstructural)
        (Hvertices & Hedges & Hedgevertices & Hgarbage & Hpending &
          Hsnapshots & Hrows)
        [Hbound Hempty] Hcount.
      destruct Hdefined as [Hvalue_timestamp [Htimestamp_value Hallocated]].
      destruct Hstructural as [Hlive [Hdomain Hnodup]].
      assert (Horders : forall owner, In owner (ThreadDomain.threads D) ->
          order_at owner (concrete_array sigma) = nil).
      { apply Hempty. exact Hcount. }
      intros [owner loc]. split.
      - intro Hvertex. apply (proj2 (Hgarbage (pair owner loc))).
        apply NNPP. intro Hnotgarbage.
        assert (Harray_vertex :
          array_vertex (concrete_array sigma) (pair owner loc)).
        { unfold is_vertex, array_vertex in *. now rewrite <- Hvertices. }
        assert (Harray_live :
          array_live (concrete_array sigma) (pair owner loc)).
        { split; [exact Harray_vertex|exact Hnotgarbage]. }
        pose proof (proj1 (Hlive owner loc) Harray_live) as Hin.
        rewrite Horders in Hin.
        + contradiction.
        + exact (Hdomain (pair owner loc) Harray_vertex).
      - intro Hgarbage_p. unfold is_vertex, array_vertex in *.
        rewrite Hvertices. apply Hallocated.
        now apply (proj1 (Hgarbage (pair owner loc))).
    Qed.

    Lemma all_vertices_garbage_shared p q :
      pool_shared_eq p q ->
      all_vertices_garbage p ->
      all_vertices_garbage q.
    Proof.
      intros (Hvertices & Hedges & Hpending & Hgarbage & Hpop_starts & Hpop_ts) Hall n.
      unfold all_vertices_garbage in Hall. unfold is_vertex in *.
      rewrite <- Hvertices, <- Hgarbage. apply Hall.
    Qed.

    Lemma getTop_fail_slice_steps (Delta : @AbstractConfig _ (li_lts F))
        actor donor donor_pi Hdonor
        (Hinv : TMap.find actor donor_pi = Some (ls_inv (lpool_getTop start)))
        (Hsession : forall rho pi, Delta rho pi ->
          session_ts actor rho = Some start)
        rho pi
        (Hslice : ac_actor_slice Delta actor donor donor_pi Hdonor rho pi) :
      poss_steps (PossOk rho pi)
        (PossOk (getTop_atomic_rho rho)
          (atomic_tokens actor (lpool_getTop start) YFail pi)).
    Proof.
      destruct rho as [p|p pending op]; [|inversion Hslice].
      pose proof Hslice as Hslice_cases.
      apply ac_actor_slice_cases in Hslice_cases.
      destruct Hslice_cases as [Hsource [Hsnapshot Htoken]].
      assert (Hinv_pi : TMap.find actor pi = Some (ls_inv (lpool_getTop start)))
        by (rewrite Htoken; exact Hinv).
      pose proof (Hsession _ _ Hsource) as Hts.
      unfold session_ts, session_state in Hts. simpl in Hts.
      eapply rt_trans.
      - apply rt_step. eapply ps_inv.
        + eapply step_getTop_atomic_inv; [exact Hts|reflexivity].
        + exact Hinv_pi.
      - apply rt_step. eapply ps_ret.
        + eapply step_getTop_fail_res. reflexivity.
        + apply TMap.gss.
    Qed.

    Lemma getTop_empty_slice_steps (Delta : @AbstractConfig _ (li_lts F))
        actor donor donor_pi Hdonor
        (Hinv : TMap.find actor donor_pi = Some (ls_inv (lpool_getTop start)))
        (Hsession : forall rho pi, Delta rho pi ->
          session_ts actor rho = Some start)
        (Hempty : all_vertices_garbage donor)
        (Hrect : possibility_rectangular Delta)
        rho pi
        (Hslice : ac_actor_slice Delta actor donor donor_pi Hdonor rho pi) :
      poss_steps (PossOk rho pi)
        (PossOk (getTop_atomic_rho rho)
          (atomic_tokens actor (lpool_getTop start) YSuccEmpty pi)).
    Proof.
      destruct rho as [p|p pending op]; [|inversion Hslice].
      pose proof Hslice as Hslice_cases.
      apply ac_actor_slice_cases in Hslice_cases.
      destruct Hslice_cases as [Hsource [Hsnapshot Htoken]].
      assert (Hinv_pi : TMap.find actor pi = Some (ls_inv (lpool_getTop start)))
        by (rewrite Htoken; exact Hinv).
      assert (Hempty_p : all_vertices_garbage p).
      { eapply all_vertices_garbage_shared; [|exact Hempty].
        exact ((proj1 Hrect) donor donor_pi p pi Hdonor Hsource).
      }
      pose proof (Hsession _ _ Hsource) as Hts.
      unfold session_ts, session_state in Hts. simpl in Hts.
      eapply rt_trans.
      - apply rt_step. eapply ps_inv.
        + eapply step_getTop_atomic_inv; [exact Hts|reflexivity].
        + exact Hinv_pi.
      - apply rt_step. eapply ps_ret.
        + eapply step_getTop_empty_res; [exact Hempty_p|reflexivity].
        + apply TMap.gss.
    Qed.

    Lemma ALinExists_add_actor_alternative_keep sigma sigma'
        (Delta : @AbstractConfig _ (li_lts F)) actor donor donor_pi Hdonor ret
        Hsteps ls :
      ALinExists actor ls
        (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          sigma Delta) ->
      ALinExists actor ls
        (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          sigma'
          (ac_add_actor_alternative Delta actor donor donor_pi Hdonor ret
            Hsteps)).
    Proof.
      intro Hexists. apply (proj1 (token_view_ALinExists sigma' actor _ ls)).
      destruct (proj2 (token_view_ALinExists sigma actor Delta ls) Hexists)
        as (rho & pi & Hposs & Htoken).
      exists rho, pi. split.
      - now apply ac_add_actor_alternative_keep.
      - exact Htoken.
    Qed.

    Lemma add_actor_alternative_result_exists sigma
        (Delta : @AbstractConfig _ (li_lts F)) actor donor donor_pi Hdonor ret
        Hsteps :
      actor ↦∃•((lpool_getTop start), ret)
        (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          sigma
          (ac_add_actor_alternative Delta actor donor donor_pi Hdonor ret
            Hsteps)).
    Proof.
      apply (proj1 (token_view_ALinExists sigma actor _ _)).
      exists (LPReady donor),
        (atomic_tokens actor (lpool_getTop start) ret donor_pi). split.
      - apply ac_add_actor_alternative_take.
        unfold ac_actor_alternative.
        change (ac_image_prop
          (ac_actor_slice Delta actor donor donor_pi Hdonor)
          getTop_atomic_rho (atomic_tokens actor (lpool_getTop start) ret) Hsteps
          (getTop_atomic_rho (LPReady donor))
          (atomic_tokens actor (lpool_getTop start) ret donor_pi)).
        constructor. constructor; [exact Hdonor|reflexivity|reflexivity].
      - apply atomic_tokens_same.
    Qed.

    Lemma I_start_counter (a : @SPListArrayState A) tss actor Delta :
      I (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          (pair (ArrayReady a) tss) Delta) ->
      ThreadDomain.contains D actor ->
      TMap.find actor (as_pending_counters a) = None ->
      actor ↦∃•((lpool_getTop start))
        (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          (pair (ArrayReady a) tss) Delta) ->
      I (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          (pair (ArrayReady (start_counter D actor a)) tss) Delta).
    Proof.
      intros [Hwf [Hall [Hrect Hcounter]]] Hactor Hnone Hlinearizing.
      split; [now apply concrete_wf_start_counter|]. split.
      - intros rho pi Hposs. now apply branch_represents_start_counter, Hall.
      - split; [exact Hrect|].
        intros owner saved Hpending.
        unfold concrete_array, array_payload, start_counter in Hpending.
        simpl in Hpending.
        destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
        + rewrite TMap.gss in Hpending. inversion Hpending; subst saved.
          destruct (proj2 (token_view_ALinExists
            (pair (ArrayReady a) tss) actor Delta _) Hlinearizing) as
            (rho & pi & Hposs & Htoken).
          exists rho, pi, start. auto.
        + rewrite TMap.gso in Hpending by exact Hneq.
          now apply Hcounter in Hpending.
    Qed.

    Lemma G_trans actor w1 w2 w3 :
      G actor w1 w2 -> G actor w2 w3 -> G actor w1 w3.
    Proof.
      intros H12 H23.
      destruct H12 as
        (Htoken12 & Hlocal12 & Hcausal12 & Harray_local12 & Hpending12 &
          Hcandidate12 & Hrow12 & Harray12 & Hclock12 & Hcandidate_row12 &
          Hcuts12 & Hgarbage12 & Hintervals12 & Hsession12).
      destruct H23 as
        (Htoken23 & Hlocal23 & Hcausal23 & Harray_local23 & Hpending23 &
          Hcandidate23 & Hrow23 & Harray23 & Hclock23 & Hcandidate_row23 &
          Hcuts23 & Hgarbage23 & Hintervals23 & Hsession23).
      unfold G.
      refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
        (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))))).
      - intros observer Hneq. eapply token_rely_trans;
          [apply Htoken12|apply Htoken23]; exact Hneq.
      - intros observer Hneq. eapply pool_local_equiv_trans;
          [apply Hlocal12|apply Hlocal23]; exact Hneq.
      - intros observer loc lower Hneq Hcausal.
        apply Hcausal23; [exact Hneq|]. apply Hcausal12; assumption.
      - intros observer Hneq. rewrite Harray_local12, Harray_local23;
          [reflexivity|exact Hneq|exact Hneq].
      - intros observer Hneq. rewrite Hpending12, Hpending23;
          [reflexivity|exact Hneq|exact Hneq].
      - intros observer Hneq done candidate Hview.
        apply Hcandidate23; [exact Hneq|]. now apply Hcandidate12.
      - intros observer Hneq owner saved Hview.
        apply Hrow23; [exact Hneq|]. now apply Hrow12.
      - intros owner. destruct (Harray12 owner) as [Hle12 Hincl12].
        destruct (Harray23 owner) as [Hle23 Hincl23]. split; [lia|].
        intro Heq. apply incl_tran with
          (m := order_at owner (concrete_array (SetPossState.σ w2))).
        + apply Hincl23. lia.
        + apply Hincl12. lia.
      - lia.
      - intros observer Hneq done candidate owner saved Hview.
        apply Hcandidate_row23; [exact Hneq|].
        now apply Hcandidate_row12.
      - intros observer Hneq progress start0 Hinside Hfallback Hsession_all Hcuts.
        apply (Hcuts23 observer Hneq progress start0 Hinside).
        + apply (proj1 (Htoken12 observer Hneq)) with
            (token := Some (ls_inv (lpool_getTop start0))). exact Hfallback.
        + eapply session_token_equiv; [apply Hsession12; exact Hneq|].
          exact Hsession_all.
        + apply (Hcuts12 observer Hneq progress start0 Hinside Hfallback
            Hsession_all Hcuts).
      - intros n Hgarbage. apply Hgarbage23, Hgarbage12, Hgarbage.
      - split; [|split].
        + intros n ts Htimestamp.
          destruct (proj1 Hintervals12 n ts Htimestamp) as
            [ts' Htimestamp'].
          now apply (proj1 Hintervals23 n ts' Htimestamp').
        + intros n lower upper Htimestamp.
          apply (proj1 (proj2 Hintervals23)), (proj1 (proj2 Hintervals12)),
            Htimestamp.
        + intros n v Hvalue.
          apply (proj2 (proj2 Hintervals23)), (proj2 (proj2 Hintervals12)),
            Hvalue.
      - intros observer Hneq. eapply session_equiv_trans;
          [apply Hsession12|apply Hsession23]; exact Hneq.
    Qed.

    Lemma scan_fold_counter_no_error actor count :
      ⊨ ScanFold actor nil (pair (@None (@Candidate A)) count) ==>>
        AssertionsSet.A.ANoError
          (Build_ThreadEvent actor (InvEv (inl array_getCounter))).
    Proof.
      intros [[control tss] Delta] [HI [Hactor Hrest]] Herror.
      simpl in Herror. inversion Herror; subst; contradiction.
    Qed.

    Lemma getTop_counter_inv_update actor count :
      AssertionsSet.PUpdate (G actor)
        (Build_ThreadEvent actor (InvEv (inl array_getCounter)))
        (ScanFold actor nil (pair (@None (@Candidate A)) count))
        (CounterPending actor count).
    Proof.
      intros [control tss] Delta Hpre [control' tss'] Hstep.
      destruct Hpre as [HIpre [Hactor [Hcounter_none Hrest]]].
      destruct Hrest as
        (done & progress & Hparts & Hscan & Hvisited & Hidle & Hseenwf &
          Hseen_timestamped & Hfallback & Hlinearizing & Hsnapshot & Hcuts &
          Hacc & Hsession_token).
      rewrite app_nil_r in Hparts. subst done.
      unfold ScanAccumulator in Hacc. simpl in Hacc.
      destruct Hacc as [Hempty_evidence Hseen_garbage].
      destruct Hempty_evidence as [Hempty_bound Hempty_rows].
      simpl in Hstep. destruct Hstep as [Harray ->].
      destruct (array_counter_inv_shape actor _ _ Harray) as
        (a & -> & -> & Hactor0 & Hnone).
      destruct HIpre as [Hwf [Hall [Hrect Hcounter]]].
      destruct (proj2 (token_view_ALinExists
        (pair (ArrayReady a) tss') actor Delta _) Hfallback) as
        (rho & donor_pi & Hdonor0 & Hinv).
      destruct (Hall _ _ Hdonor0) as
        (donor & Heqdonor & Hpool & Hprotocol & Htimestamp & Hsession).
      subst rho.
      set (sigma0 := (pair (ArrayReady a) tss' : concrete_state)).
      set (sigma1 :=
        (pair (ArrayReady (start_counter D actor a)) tss' : concrete_state)).
      assert (HIstart : I (sigma1, Delta)).
      { unfold sigma0, sigma1.
        eapply I_start_counter; [|exact Hactor|exact Hcounter_none|].
        - exact (conj Hwf (conj Hall (conj Hrect Hcounter))).
        - exact Hlinearizing. }
      set (fail_steps := getTop_fail_slice_steps Delta actor donor donor_pi
        Hdonor0 Hinv Hsession_token).
      set (DeltaFail := ac_add_actor_alternative Delta actor donor donor_pi
        Hdonor0 YFail fail_steps).
      assert (HIfail : I (sigma1, DeltaFail)).
      { unfold DeltaFail. eapply I_add_actor_alternative; eauto. }
      assert (Hsession_fail : SessionToken actor start (sigma1, DeltaFail)).
      { unfold DeltaFail. eapply session_token_stable;
          [apply session_equiv_add_actor_alternative|exact Hsession_token]. }
      assert (HGstart : G actor (sigma0, Delta) (sigma1, Delta)).
      { unfold sigma0, sigma1. apply G_start_counter. }
      assert (HGfail : G actor (sigma1, Delta) (sigma1, DeltaFail)).
      { unfold DeltaFail. apply G_add_actor_alternative. }
      destruct (Nat.eq_dec count (total_counter D a)) as [Heq|Hneq].
      - assert (Hempty_donor : all_vertices_garbage donor).
        { eapply empty_evidence_all_vertices_garbage; eauto.
          split; eassumption. }
        assert (Hdonor_fail : DeltaFail (LPReady donor) donor_pi).
        { unfold DeltaFail. now apply ac_add_actor_alternative_keep. }
        destruct HIfail as [Hwf_fail [Hall_fail [Hrect_fail Hcounter_fail]]].
        set (empty_steps := getTop_empty_slice_steps DeltaFail actor donor
          donor_pi Hdonor_fail Hinv Hsession_fail Hempty_donor Hrect_fail).
        set (DeltaEmpty := ac_add_actor_alternative DeltaFail actor donor
          donor_pi Hdonor_fail YSuccEmpty empty_steps).
        assert (HIempty : I (sigma1, DeltaEmpty)).
        { unfold DeltaEmpty. eapply I_add_actor_alternative; eauto.
          exact (conj Hwf_fail
            (conj Hall_fail (conj Hrect_fail Hcounter_fail))). }
        exists DeltaEmpty. split.
        + unfold DeltaEmpty. eapply ac_steps_subset_trans.
          * unfold DeltaFail. apply ac_add_actor_alternative_subset_steps.
          * apply ac_add_actor_alternative_subset_steps.
        + split.
          * unfold CounterPending. split; [exact HIempty|].
            split; [exact Hactor|]. exists (total_counter D a).
            repeat split.
            -- unfold sigma1, concrete_array, array_payload, start_counter.
               simpl. apply TMap.gss.
            -- exact Hempty_bound.
            -- unfold sigma1, concrete_array, array_payload, start_counter.
               simpl. exact Hempty_bound.
            -- unfold sigma1, concrete_array, array_payload, start_counter.
               simpl. exact Hempty_rows.
            -- unfold DeltaEmpty.
               eapply ALinExists_add_actor_alternative_keep.
               unfold DeltaFail.
               eapply ALinExists_add_actor_alternative_keep. exact Hfallback.
            -- unfold DeltaEmpty.
               eapply ALinExists_add_actor_alternative_keep.
               unfold DeltaFail.
               eapply ALinExists_add_actor_alternative_keep.
               exact Hlinearizing.
            -- unfold DeltaEmpty.
               eapply ALinExists_add_actor_alternative_keep.
               unfold DeltaFail. apply add_actor_alternative_result_exists.
            -- intro Heq_unused. unfold DeltaEmpty.
               apply add_actor_alternative_result_exists.
            -- unfold DeltaEmpty. eapply session_token_stable;
                 [apply session_equiv_add_actor_alternative|exact Hsession_fail].
          * eapply G_trans; [exact HGstart|].
            eapply G_trans; [exact HGfail|].
            unfold DeltaEmpty. apply G_add_actor_alternative.
      - exists DeltaFail. split.
        + unfold DeltaFail. apply ac_add_actor_alternative_subset_steps.
        + split.
          * unfold CounterPending. split; [exact HIfail|].
            split; [exact Hactor|]. exists (total_counter D a).
            repeat split.
            -- unfold sigma1, concrete_array, array_payload, start_counter.
               simpl. apply TMap.gss.
            -- exact Hempty_bound.
            -- unfold sigma1, concrete_array, array_payload, start_counter.
               simpl. exact Hempty_bound.
            -- unfold sigma1, concrete_array, array_payload, start_counter.
               simpl. exact Hempty_rows.
            -- unfold DeltaFail.
               eapply ALinExists_add_actor_alternative_keep. exact Hfallback.
            -- unfold DeltaFail.
               eapply ALinExists_add_actor_alternative_keep.
               exact Hlinearizing.
            -- unfold DeltaFail. apply add_actor_alternative_result_exists.
            -- intro Heq'. contradiction.
            -- exact Hsession_fail.
          * exact (G_trans actor (sigma0, Delta) (sigma1, Delta)
              (sigma1, DeltaFail) HGstart HGfail).
      Unshelve.
      all: exact sigma1.
    Qed.

    Definition array_counter_res_kind
        (ev : @ThreadEvent (@ESPListArray A)) : bool :=
      match te_ev ev with
      | ResEv array_getCounter _ => true
      | _ => false
      end.

    Lemma array_counter_res_shape actor result control control' :
      @StepSPListArray A D
        (Build_ThreadEvent actor (ResEv array_getCounter result))
        control control' ->
      exists a saved,
        control = ArrayReady a /\
        control' = ArrayReady (finish_counter actor a) /\
        TMap.find actor (as_pending_counters a) = Some saved /\
        saved <= result /\
        result <= total_counter D a.
    Proof.
      intro Hstep. remember (Build_ThreadEvent actor
        (ResEv array_getCounter result)) as ev eqn:Hev in Hstep.
      inversion Hstep.
      all: match goal with
        | Hctor : ?remembered = ?rhs,
          Htarget : ?remembered = ?target |- _ =>
            let Hevent := fresh "Hevent" in
            pose proof (eq_trans (eq_sym Htarget) Hctor) as Hevent;
            let Hkind := fresh "Hkind" in
            pose proof (f_equal array_counter_res_kind Hevent) as Hkind;
            cbv [array_counter_res_kind] in Hkind;
            first [discriminate Hkind |
              dependent destruction Hevent;
              do 2 eexists; split; [reflexivity|]; split; [reflexivity|];
              repeat split; eassumption]
        end.
    Qed.

    Lemma concrete_wf_finish_counter a tss actor :
      concrete_wf (pair (ArrayReady a) tss) ->
      concrete_wf (pair (ArrayReady (finish_counter actor a)) tss).
    Proof. unfold concrete_wf, concrete_array, concrete_timestamp,
      array_payload, finish_counter; simpl; tauto. Qed.

    Lemma branch_represents_finish_counter a tss actor rho pi :
      branch_represents (pair (ArrayReady a) tss) rho pi ->
      branch_represents
        (pair (ArrayReady (finish_counter actor a)) tss) rho pi.
    Proof.
      intros (p & -> & Hpool & Hprotocol & Htimestamp & Hsession).
      exists p. split; [reflexivity|]. split.
      - unfold pool_represents, finish_counter in *. simpl in *. exact Hpool.
      - split; [exact Hprotocol|].
        unfold timestamp_pending_edges, concrete_array, concrete_timestamp,
          array_payload, finish_counter in *. simpl in *. split; [exact Htimestamp|exact Hsession].
    Qed.

    Lemma I_finish_counter (a : @SPListArrayState A)
        (tss : TimestampState) (actor : tid)
        (Delta : @AbstractConfig _ (li_lts F)) :
      I (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          (pair (ArrayReady a) tss) Delta) ->
      I (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          (pair (ArrayReady (finish_counter actor a)) tss) Delta).
    Proof.
      intros [Hwf [Hall [Hrect Hcounter]]]. split.
      - now apply concrete_wf_finish_counter.
      - split.
        + intros rho pi Hposs. now apply branch_represents_finish_counter, Hall.
        + split; [exact Hrect|]. intros owner saved Hpending.
          unfold concrete_array, array_payload, finish_counter in Hpending.
          simpl in Hpending.
          destruct (PositiveMap.E.eq_dec owner actor) as [->|Hneq].
          * rewrite TMap.grs in Hpending. discriminate.
          * rewrite TMap.gro in Hpending by exact Hneq.
            now apply Hcounter in Hpending.
    Qed.

    Lemma G_finish_counter (a : @SPListArrayState A)
        (tss : TimestampState) (actor : tid)
        (Delta : @AbstractConfig _ (li_lts F)) :
      G actor
        (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          (pair (ArrayReady a) tss) Delta)
        (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          (pair (ArrayReady (finish_counter actor a)) tss) Delta).
    Proof.
      unfold G. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
        (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))))).
      - intros observer Hneq. apply token_rely_refl.
      - intros observer Hneq. apply pool_local_equiv_refl.
      - intros observer loc lower Hneq.
        unfold push_causal, concrete_array, array_payload, finish_counter.
        simpl. tauto.
      - intros observer Hneq. unfold array_local_state, concrete_array,
          array_payload, finish_counter. simpl. rewrite TMap.gro by congruence.
        reflexivity.
      - intros observer Hneq. reflexivity.
      - intros observer Hneq. apply candidate_views_preserved_refl.
      - intros observer Hneq. apply row_snapshot_views_preserved_refl.
      - eapply array_evolves_of_counter_order; intro owner; reflexivity.
      - apply Nat.le_refl.
      - intros observer Hneq. apply candidate_row_views_preserved_refl.
      - intros observer Hneq progress start0 Hinside Hfallback Hsession_all Hcuts.
        unfold node_cuts_available, concrete_array, array_payload,
          finish_counter in *. simpl in *. exact Hcuts.
      - unfold garbage_evolves, concrete_array, array_payload,
          finish_counter. simpl. tauto.
      - unfold intervals_evolve, concrete_array, array_payload,
          finish_counter. simpl. split; firstorder.
      - intros observer Hneq. apply session_equiv_refl.
    Qed.

    Lemma actor_slice_foreign_cover Delta actor donor donor_pi Hdonor observer :
      actor <> observer ->
      possibility_rectangular Delta ->
      foreign_branch_cover observer Delta
        (ac_actor_slice Delta actor donor donor_pi Hdonor).
    Proof.
      intros Hneq Hrect p pi Hposs.
      destruct (ac_actor_slice_receiver Delta actor donor donor_pi Hdonor
        p pi Hrect Hposs) as (q & qi & Hslice & Hmerged).
      destruct Hmerged as
        (Hshared & Hactor_snapshot & Hactor_token & Hforeign_snapshot &
          Hforeign_token).
      exists q, qi. split; [exact Hslice|]. split; [exact Hshared|]. split.
      - now apply Hforeign_snapshot.
      - now apply Hforeign_token.
    Qed.

    Lemma G_actor_slice sigma Delta actor donor donor_pi Hdonor :
      possibility_rectangular Delta ->
      (forall rho pi, Delta rho pi -> exists p, rho = LPReady p) ->
      G actor (sigma, Delta)
        (sigma, ac_actor_slice Delta actor donor donor_pi Hdonor).
    Proof.
      intros Hrect Hready. unfold G.
      refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
        (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))))).
      - intros observer Hneq. apply token_equiv_rely. intro token. split.
        + intros (rho & pi & Hposs & Htoken).
          destruct (Hready _ _ Hposs) as (p & ->).
          destruct (actor_slice_foreign_cover Delta actor donor donor_pi
            Hdonor observer Hneq Hrect p pi Hposs) as
            (q & qi & Hslice & Hshared & Hsnapshot & Htoken_eq).
          exists (LPReady q), qi. split; [exact Hslice|]. congruence.
        + intros (rho & pi & Hslice & Htoken).
          inversion Hslice; subst. exists (LPReady p), pi. auto.
      - intros observer Hneq. split.
        + intros local (rho & pi & Hposs & Hlocal).
          destruct (Hready _ _ Hposs) as (p & ->).
          destruct (actor_slice_foreign_cover Delta actor donor donor_pi
            Hdonor observer Hneq Hrect p pi Hposs) as
            (q & qi & Hslice & Hshared & Hsnapshot & Htoken_eq).
          exists (LPReady q), qi. split; [exact Hslice|].
          unfold pool_local_state in *. simpl in *.
          destruct Hshared as (_ & _ & Hpending & Hgarbage & Hpop_starts & Hpop_ts).
          rewrite Hpending, Hsnapshot. exact Hlocal.
        + intros local' (rho & pi & Hslice & Hlocal).
          inversion Hslice; subst.
          exists (pool_local_state observer (LPReady p)). split.
          * exists (LPReady p), pi. auto.
          * reflexivity.
      - intros observer loc lower Hneq Hcausal rho pi Hslice.
        unfold push_causal in Hcausal.
        inversion Hslice; subst. simpl.
        exact (Hcausal (LPReady p) pi Hposs).
      - intros observer Hneq. reflexivity.
      - intros observer Hneq. reflexivity.
      - intros observer Hneq. apply foreign_cover_candidate_views.
        now apply actor_slice_foreign_cover.
      - intros observer Hneq. apply foreign_cover_row_snapshot_views.
        now apply actor_slice_foreign_cover.
      - apply array_evolves_refl.
      - apply Nat.le_refl.
      - intros observer Hneq. apply foreign_cover_candidate_row_views.
        now apply actor_slice_foreign_cover.
      - intros observer Hneq. apply foreign_cover_node_cuts.
        now apply actor_slice_foreign_cover.
      - apply garbage_evolves_refl.
      - apply intervals_evolve_refl.
      - intros observer Hneq. apply session_equiv_actor_slice.
        + exact Hrect.
        + exact Hready.
    Qed.

    Lemma actor_slice_completed sigma Delta actor donor donor_pi Hdonor ret :
      I (sigma, ac_actor_slice Delta actor donor donor_pi Hdonor) ->
      TMap.find actor donor_pi = Some (ls_linr (lpool_getTop start) ret) ->
      Completed actor (lpool_getTop start) ret
        (sigma, ac_actor_slice Delta actor donor donor_pi Hdonor).
    Proof.
      intros HI Hresult. split; [exact HI|]. intros rho pi Hslice.
      destruct rho as [p|p pending op]; [|inversion Hslice].
      apply ac_actor_slice_cases in Hslice.
      destruct Hslice as [Hsource [Hsnapshot Htoken]].
      rewrite Htoken. exact Hresult.
    Qed.

    Lemma getTop_counter_res_update actor count result :
      AssertionsSet.PUpdate (G actor)
        (Build_ThreadEvent actor
          (ResEv (inl array_getCounter) result))
        (CounterPending actor count)
        (Completed actor (lpool_getTop start)
          (if Nat.eqb result count then YSuccEmpty else YFail)).
    Proof.
      intros [control tss] Delta Hpre [control' tss'] Hstep.
      destruct Hpre as [HIpre [Hactor Hrest]].
      destruct Hrest as
        (saved & Hpending & Hbound & Hempty_evidence & Hfallback &
          Hlinearizing & Hfail & Hempty_result & Hsession_token).
      simpl in Hstep. destruct Hstep as [Harray ->].
      destruct (array_counter_res_shape actor result _ _ Harray) as
        (a & saved0 & -> & -> & Hpending0 & Hsaved_result & Hresult_total).
      change (TMap.find actor (as_pending_counters a) = Some saved)
        in Hpending.
      rewrite Hpending in Hpending0. inversion Hpending0; subst saved0.
      destruct HIpre as [Hwf [Hall [Hrect Hcounter]]].
      set (sigma_finished :=
        (pair (ArrayReady (finish_counter actor a)) tss' : concrete_state)).
      destruct (Nat.eqb result count) eqn:Hchoice.
      - apply Nat.eqb_eq in Hchoice.
        assert (Hcount_saved : count = saved) by lia.
        specialize (Hempty_result Hcount_saved).
        destruct (proj2 (token_view_ALinExists
          (pair (ArrayReady a) tss') actor Delta _) Hempty_result) as
          (rho & donor_pi & Hdonor0 & Htoken).
        destruct (Hall _ _ Hdonor0) as
          (donor & -> & Hpool & Hprotocol & Htimestamp & Hsession).
        set (Delta' := ac_actor_slice Delta actor donor donor_pi Hdonor0).
        assert (HIfinished : I (sigma_finished, Delta)).
        { unfold sigma_finished. apply I_finish_counter.
          exact (conj Hwf (conj Hall (conj Hrect Hcounter))). }
        assert (HIpost : I (sigma_finished, Delta')).
        { unfold Delta'. eapply I_actor_slice; [exact HIfinished|].
          unfold concrete_array, array_payload, finish_counter. simpl.
          apply TMap.grs. }
        exists Delta'. split.
        + unfold Delta'. apply ac_actor_slice_subset_steps.
        + split.
          * unfold Delta'.
            now apply actor_slice_completed.
          * eapply G_trans.
            -- unfold sigma_finished. apply G_finish_counter.
            -- unfold Delta'. eapply G_actor_slice; [exact Hrect|].
               intros rho0 pi0 Hposs.
               destruct (Hall _ _ Hposs) as (p & -> & Hrep). now exists p.
      - destruct (proj2 (token_view_ALinExists
          (pair (ArrayReady a) tss') actor Delta _) Hfail) as
          (rho & donor_pi & Hdonor0 & Htoken).
        destruct (Hall _ _ Hdonor0) as
          (donor & -> & Hpool & Hprotocol & Htimestamp & Hsession).
        set (Delta' := ac_actor_slice Delta actor donor donor_pi Hdonor0).
        assert (HIfinished : I (sigma_finished, Delta)).
        { unfold sigma_finished. apply I_finish_counter.
          exact (conj Hwf (conj Hall (conj Hrect Hcounter))). }
        assert (HIpost : I (sigma_finished, Delta')).
        { unfold Delta'. eapply I_actor_slice; [exact HIfinished|].
          unfold concrete_array, array_payload, finish_counter. simpl.
          apply TMap.grs. }
        exists Delta'. split.
        + unfold Delta'. apply ac_actor_slice_subset_steps.
        + split.
          * unfold Delta'.
            now apply actor_slice_completed.
          * eapply G_trans.
            -- unfold sigma_finished. apply G_finish_counter.
            -- unfold Delta'. eapply G_actor_slice; [exact Hrect|].
               intros rho0 pi0 Hposs.
               destruct (Hall _ _ Hposs) as (p & -> & Hrep). now exists p.
    Qed.

    Lemma getTop_empty_exit_triple actor count :
      SetLogic.HTripleProvable (R actor) (G actor) I actor
        (ScanFold actor nil (pair (@None (@Candidate A)) count))
        (inl array_getCounter >= current_counter =>
          Ret (if Nat.eqb current_counter count then YSuccEmpty else YFail))
        (fun ret => Completed actor (lpool_getTop start) ret).
    Proof.
      eapply SetLogic.provable_vis_safe with
        (P' := CounterPending actor count)
        (Q' := fun result => Completed actor (lpool_getTop start)
          (if Nat.eqb result count then YSuccEmpty else YFail)).
      - apply scan_fold_counter_no_error.
      - apply counter_pending_entails_I.
      - intros result. apply completed_entails_I.
      - apply counter_pending_stable.
      - intros result. apply completed_stable.
      - apply getTop_counter_inv_update.
      - intros result. apply getTop_counter_res_update.
      - intros result. eapply SetLogic.provable_ret_safe.
        + apply ImplRefl.
        + apply completed_entails_I.
        + apply completed_stable.
    Qed.

    Lemma getTop_scan_exit_triple actor scan :
      SetLogic.HTripleProvable (R actor) (G actor) I actor
        (ScanFold actor nil scan)
        (match fst scan with
         | Some candidate =>
             Ret (YSuccNode (candidate_value candidate)
               (candidate_owner candidate) (candidate_loc candidate))
         | None =>
             inl array_getCounter >= current_counter =>
             Ret (if Nat.eqb current_counter (snd scan)
                  then YSuccEmpty else YFail)
         end)
        (fun ret => Completed actor (lpool_getTop start) ret).
    Proof.
      destruct scan as [candidate count]. destruct candidate.
      - apply getTop_candidate_exit_triple.
      - apply getTop_empty_exit_triple.
    Qed.

    Lemma G_refl actor w : G actor w w.
    Proof.
      unfold G. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
        (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))))).
      - intros observer Hneq. apply token_rely_refl.
      - intros observer Hneq. apply pool_local_equiv_refl.
      - firstorder.
      - intros observer Hneq. reflexivity.
      - intros observer Hneq. reflexivity.
      - intros observer Hneq. apply candidate_views_preserved_refl.
      - intros observer Hneq. apply row_snapshot_views_preserved_refl.
      - apply array_evolves_refl.
      - apply Nat.le_refl.
      - intros observer Hneq. apply candidate_row_views_preserved_refl.
      - intros observer Hneq. apply node_cuts_preserved_refl.
      - apply garbage_evolves_refl.
      - apply intervals_evolve_refl.
      - intros observer Hneq. apply session_equiv_refl.
    Qed.

    Lemma getTop_reset_to_scan_update actor :
      AssertionsSet.PUpdateId (G actor) (GetTopReset actor)
        (ScanFold actor (ThreadDomain.threads D)
          (pair (@None (@Candidate A)) O)).
    Proof.
      intros sigma Delta Hreset. exists Delta. split.
      - apply ac_steps_refl.
      - split.
        + now apply getTop_reset_entails_scan_fold.
        + apply G_refl.
    Qed.

    Lemma getTop_foreach_triple actor :
      SetLogic.HTripleProvable (R actor) (G actor) I actor
        (ElimFold actor (ThreadDomain.threads D)
          (ScanOngoing (pair (@None (@Candidate A)) O)))
        (ForEach ThreadDomain.threads D
          From (ScanOngoing (pair (@None (@Candidate A)) O))
          Using scan_step_elim D start)
        (fun acc => ElimFold actor nil acc).
    Proof.
      eapply SetLogic.provable_foreach
        with (Inv := ElimFold actor).
      - intros acc. eapply SetLogic.provable_ret_safe.
        + apply ImplRefl.
        + apply elim_fold_entails_I.
        + apply elim_fold_stable.
      - intros item items acc. apply getTop_row_step_triple.
    Qed.

    Lemma getTop_elim_scan_exit_triple actor (acc : @ElimScan A) :
      SetLogic.HTripleProvable (R actor) (G actor) I actor
        (ElimFold actor nil acc)
        (match acc with
         | ScanEliminated v owner loc => Ret (YSuccNode v owner loc)
         | ScanOngoing scan =>
             match fst scan with
             | Some candidate =>
                 Ret (YSuccNode (candidate_value candidate)
                   (candidate_owner candidate) (candidate_loc candidate))
             | None =>
                 inl array_getCounter >= current_counter =>
                 Ret (if Nat.eqb current_counter (snd scan)
                      then YSuccEmpty else YFail)
             end
         end)
        (fun ret => Completed actor (lpool_getTop start) ret).
    Proof.
      destruct acc as [scan|v owner loc].
      - apply getTop_scan_exit_triple.
      - apply getTop_elim_exit_triple.
    Qed.

    Lemma getTop_scan_body_triple actor :
      SetLogic.HTripleProvable (R actor) (G actor) I actor
        (ScanFold actor (ThreadDomain.threads D)
          (pair (@None (@Candidate A)) O))
        ((ForEach ThreadDomain.threads D
            From (ScanOngoing (pair (@None (@Candidate A)) O))
            Using scan_step_elim D start)
          p>= acc =>
          match acc with
          | ScanEliminated v owner loc => Ret (YSuccNode v owner loc)
          | ScanOngoing scan =>
              match fst scan with
              | Some candidate =>
                  Ret (YSuccNode (candidate_value candidate)
                    (candidate_owner candidate) (candidate_loc candidate))
              | None =>
                  (@Vis (li_sig E) (@YResult A)
                    (@inl (@ESPListArray_op A) ETimestamp_op array_getCounter)
                    (fun current_counter =>
                      @Ret (li_sig E) (@YResult A)
                        (if Nat.eqb current_counter (snd scan)
                         then YSuccEmpty else YFail)))
              end
          end)
        (fun ret => Completed actor (lpool_getTop start) ret).
    Proof.
      eapply SetLogic.provable_seq with
        (Q' := fun acc => ElimFold actor nil acc).
      - apply getTop_foreach_triple.
      - intro acc. apply getTop_elim_scan_exit_triple.
    Qed.

    Lemma getTop_after_reset_triple actor :
      SetLogic.HTripleProvable (R actor) (G actor) I actor
        (GetTopReset actor)
        ((ForEach ThreadDomain.threads D
            From (ScanOngoing (pair (@None (@Candidate A)) O))
            Using scan_step_elim D start)
          p>= acc =>
          match acc with
          | ScanEliminated v owner loc => Ret (YSuccNode v owner loc)
          | ScanOngoing scan =>
              match fst scan with
              | Some candidate =>
                  Ret (YSuccNode (candidate_value candidate)
                    (candidate_owner candidate) (candidate_loc candidate))
              | None =>
                  (@Vis (li_sig E) (@YResult A)
                    (@inl (@ESPListArray_op A) ETimestamp_op array_getCounter)
                    (fun current_counter =>
                      @Ret (li_sig E) (@YResult A)
                        (if Nat.eqb current_counter (snd scan)
                         then YSuccEmpty else YFail)))
              end
          end)
        (fun ret => Completed actor (lpool_getTop start) ret).
    Proof.
      eapply SetLogic.provable_linstep with
        (P' := ScanFold actor (ThreadDomain.threads D)
          (pair (@None (@Candidate A)) O)).
      - apply scan_fold_entails_I.
      - apply scan_fold_stable.
      - apply getTop_reset_to_scan_update.
      - apply getTop_scan_body_triple.
    Qed.

    (** Method entry.  Besides the domain check, a [getTop] whose token is
        not the caller's current session token is a specification error
        ([error_getTop_no_session]); the session facts are uniform across
        the possibilities, so the three cases are exhaustive. *)
    Definition GetTopEntry (actor : tid) : assertion :=
      fun w =>
        I w /\
        actor ↦∃◦((lpool_getTop start)) w /\
        ((ThreadDomain.contains D actor /\
          TMap.find actor
            (as_pending_counters
              (concrete_array (SetPossState.σ w))) = None /\
          SessionToken actor start w) \/
         ~ ThreadDomain.contains D actor \/
         (forall rho pi, SetPossState.Δ w rho pi ->
            session_ts actor rho <> Some start)).

    Lemma getTop_entry_entails_I actor : ⊨ GetTopEntry actor ==>> I.
    Proof. firstorder. Qed.

    Lemma getTop_entry_stable actor :
      AssertionsSet.A.Stable (R actor) I (GetTopEntry actor).
    Proof.
      unfold AssertionsSet.A.Stable, AssertionsSet.A.ComposeA,
        GetTopEntry, R.
      intros w [[pre [[HI [Hfallback Hcase]] HR]] HI'].
      destruct pre as [sigma Delta], w as [sigma' Delta']. simpl in *.
      destruct HR as
        (Htoken & Hlocal & Hcausal & Harray_local & Hpending & Hcandidate &
          Hrow & Hevolve & Hclock & Hcandidate_row & Hcuts & Hgarbage &
          Hintervals & Hsession_equiv).
      split; [exact HI'|]. split.
      - eapply token_rely_ALinExists; eauto.
      - destruct Hcase as [[Hinside [Hnone Hsession_token]]|[Houtside|Hmismatch]].
        + left. split; [exact Hinside|]. split.
          * unfold array_local_state in Harray_local.
            pose proof (f_equal snd Harray_local) as Heq. simpl in Heq.
            congruence.
          * eapply session_token_stable;
              [exact Hsession_equiv|exact Hsession_token].
        + right. left. exact Houtside.
        + right. right.
          eapply session_mismatch_equiv; [exact Hsession_equiv|exact Hmismatch].
    Qed.

    Lemma set_ginv_exposes_getTop_entry actor :
      ⊨ AssertionsSet.A.ComposeA I
          (AssertionsSet.Ginv actor (lpool_getTop start)) ==>>
        GetTopEntry actor.
    Proof.
      intros w Hcompose.
      pose proof (set_ginv_exposes_active actor (lpool_getTop start) w Hcompose)
        as [HI Hall].
      destruct w as [sigma Delta]. simpl in *.
      split; [exact HI|]. split.
      - apply (proj1 (token_view_ALinExists sigma actor Delta _)).
        destruct (ac_nonempty Delta) as (rho & pi & Hposs).
        exists rho, pi. split; [exact Hposs|]. now apply Hall with rho.
      - destruct (ThreadDomain.contains_dec D actor) as [Hinside|Houtside].
        + destruct (classic (forall rho pi, Delta rho pi ->
            session_ts actor rho = Some start)) as [Hsession|Hmismatch].
          * left. split; [exact Hinside|]. split; [|exact Hsession].
            destruct HI as [Hwf [Hrep [Hrect Hcounter]]].
            destruct (TMap.find actor
              (as_pending_counters (concrete_array sigma))) as [saved|]
                eqn:Hpending; [|first [reflexivity|exact Hpending]].
            destruct (Hcounter actor saved Hpending) as
              (rho & pi & start0 & Hposs & Hlinearizing).
            pose proof (Hall rho pi Hposs) as Hinv.
            pose proof (eq_trans (eq_sym Hinv) Hlinearizing) as Hbad.
            dependent destruction Hbad.
          * right. right. intros rho pi Hposs Hts.
            apply Hmismatch. intros rho' pi' Hposs'.
            destruct HI as [Hwf [Hrep [Hrect Hcounter]]].
            destruct (Hrep _ _ Hposs) as (p & -> & _).
            destruct (Hrep _ _ Hposs') as (p' & -> & _).
            pose proof (proj1 Hrect p pi p' pi' Hposs Hposs') as Hshared.
            destruct Hshared as (_ & _ & _ & _ & _ & Hts_eq).
            unfold session_ts, session_state in *. simpl in *.
            rewrite <- Hts_eq. exact Hts.
        + right. left. exact Houtside.
    Qed.

    Lemma getTop_entry_or_error actor w :
      GetTopEntry actor w ->
      GetTopActor actor w \/ AssertionsSet.APError w.
    Proof.
      intros [HI [Hfallback Hcase]].
      destruct Hcase as [[Hinside [Hnone Hsession_token]]|[Houtside|Hmismatch]].
      - left. split; [exact HI|]. split; [exact Hfallback|].
        split; [exact Hinside|]. split; [exact Hnone|exact Hsession_token].
      - right. destruct w as [sigma Delta].
        destruct (proj2 (token_view_ALinExists sigma actor Delta _)
          Hfallback) as (rho & pi & Hposs & Htoken).
        destruct HI as [Hwf [Hall Hrest]].
        destruct (Hall _ _ Hposs) as
          (p & -> & Hpool & Hprotocol & Htimestamp & Hsession).
        econstructor; [exact Hposs|]. apply rt_step. eapply ps_error.
        + eapply error_actor_outside; [exact Houtside|reflexivity].
        + exact Htoken.
      - right. destruct w as [sigma Delta].
        destruct (proj2 (token_view_ALinExists sigma actor Delta _)
          Hfallback) as (rho & pi & Hposs & Htoken).
        destruct HI as [Hwf [Hall Hrest]].
        pose proof (Hmismatch _ _ Hposs) as Hm.
        destruct (Hall _ _ Hposs) as
          (p & -> & Hpool & Hprotocol & Htimestamp & Hsession).
        unfold session_ts, session_state in Hm. simpl in Hm.
        econstructor; [exact Hposs|]. apply rt_step. eapply ps_error.
        + eapply error_getTop_no_session; [exact Hm|reflexivity].
        + exact Htoken.
    Qed.

    Lemma getTop_method_triple actor :
      SetLogic.HTripleProvable (R actor) (G actor) I actor
        (GetTopEntry actor)
        (getTop_impl D start actor)
        (fun ret => Completed actor (lpool_getTop start) ret).
    Proof.
      eapply SetLogic.provable_perror with (P' := GetTopActor actor).
      - intros w Hentry. now apply getTop_entry_or_error.
      - unfold getTop_impl.
        eapply SetLogic.provable_vis_safe with
          (P' := GetTopActor actor)
          (Q' := fun _ => GetTopReset actor).
        + apply getTop_actor_no_error.
        + apply getTop_actor_entails_I.
        + intros _. apply getTop_reset_entails_I.
        + apply getTop_actor_stable.
        + intros _. apply getTop_reset_stable.
        + apply getTop_reset_inv_update.
        + intros []. apply getTop_reset_res_update.
        + intros []. apply getTop_after_reset_triple.
    Qed.

    End GetTop.

    Program Definition MListPoolElim : layer_implementation_simulation E F :=
      {| li_impl := list_pool_elim_impl D |}.
    Next Obligation.
      eapply SetLogic.soundness with (R := R) (G := G) (I := I).
      - exact valid_rg.
      - exact parallel_compatible.
      - intros actor op. destruct op as [v| |start|owner loc].
        + exists (Active actor (lpool_push v)).
          exists (fun ret => Completed actor (lpool_push v) ret).
          constructor.
          * intros w Hcompose. eapply set_ginv_exposes_active; exact Hcompose.
          * apply active_entails_I.
          * apply active_stable. intros ?; discriminate.
          * intros ret w Hcompose. eapply set_gret_closes_completed;
              exact Hcompose.
          * intros ret sigma Delta Hcompleted rho pi Hposs.
            eapply completed_has_return_token; eauto.
          * apply push_method_triple.
        + exists (Active actor lpool_startPop).
          exists (fun ret => Completed actor lpool_startPop ret).
          constructor.
          * intros w Hcompose. eapply set_ginv_exposes_active; exact Hcompose.
          * apply active_entails_I.
          * apply active_stable. intros ?; discriminate.
          * intros ret w Hcompose. eapply set_gret_closes_completed;
              exact Hcompose.
          * intros ret sigma Delta Hcompleted rho pi Hposs.
            eapply completed_has_return_token; eauto.
          * apply startPop_method_triple.
        + exists (GetTopEntry start actor).
          exists (fun ret => Completed actor (lpool_getTop start) ret).
          constructor.
          * apply set_ginv_exposes_getTop_entry.
          * apply getTop_entry_entails_I.
          * apply getTop_entry_stable.
          * intros ret w Hcompose. eapply set_gret_closes_completed;
              exact Hcompose.
          * intros ret sigma Delta Hcompleted rho pi Hposs.
            eapply completed_has_return_token; eauto.
          * apply getTop_method_triple.
        + exists (Active actor (lpool_tryRemove owner loc)).
          exists (fun ret => Completed actor
            (lpool_tryRemove owner loc) ret).
          constructor.
          * intros w Hcompose. eapply set_ginv_exposes_active; exact Hcompose.
          * apply active_entails_I.
          * apply active_stable. intros ?; discriminate.
          * intros ret w Hcompose. eapply set_gret_closes_completed;
              exact Hcompose.
          * intros ret sigma Delta Hcompleted rho pi Hposs.
            eapply completed_has_return_token; eauto.
          * apply tryRemove_method_triple.
      - exact initial_I.
    Qed.

    Definition MListPoolElimLinearizable :
        layer_implementation_linearizability E F :=
      LISim2LILin MListPoolElim.

    Print Assumptions MListPoolElimLinearizable.

  End Proof.
End ListPoolElimProof.
