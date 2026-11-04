Require Import FMapPositive.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.PArith.PArith.

Require Import models.EffectSignatures.
Require Import examples.Common.Heap.
Require Import examples.Common.ThreadDomain.
Require Import examples.TSStack.Shared.TimestampSpec.
Require Import examples.TSStack.Basic.ListPoolSpec.
Require Import examples.TSStack.WithElim.ListPoolElimSpec.
Require Import LinCCAL.
Require Import LTS.
Require Import TPSimulationSet.


(** The auxiliary try-stack specification with elimination
    (docs/plans/TSStackEliminationPlan.tex, Section 5.2).

    This is [TryStackAuxSpec] with pop sessions.  [tsa_startPop] records
    the start set of the caller's session (and later its token); a
    [tsa_trypop start] belongs to the session with token [start].  A
    successful response removes a top vertex of the snapshot (as before)
    or, by elimination, any live vertex outside the session's start set.
    The successful and empty responses close the session; a failure keeps
    it, since the retry loop above continues.

    Ghost timing data: [tsa_now] is a logical clock advanced by every
    recorded event.  [tsa_session_time] records the clock at the session's
    [startPop] invocation, and [tsa_removals] records, for each removed
    vertex, the remover, the remover's session time and the removal
    time. *)
Module TryStackAuxElimSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import TimestampSpec.
  Import ListPoolSpec.
  Import ListPoolElimSpec.
  Import TPSimulationSet.TPSimulation.

  Section Spec.
    Context {A : Type}.
    Context (D : ThreadDomain.t).

    Variant TResult : Type :=
    | TSuccNode (v : A) (owner : tid) (loc : Addr)
    | TSuccEmpty
    | TFail.
    Arguments TResult : clear implicits.

    Variant ETryStackAux_op :=
    | tsa_push (v : A)
    | tsa_startPop
    | tsa_trypop (start : TS).
    Arguments ETryStackAux_op : clear implicits.

    Definition ETryStackAux_ar (op : ETryStackAux_op) : Type :=
      match op with
      | tsa_push _ => unit
      | tsa_startPop => TS
      | tsa_trypop _ => TResult
      end.

    Canonical Structure ETryStackAux :=
    {|
      Sig.op := ETryStackAux_op;
      Sig.ar := ETryStackAux_ar
    |}.

    Record TryStackAuxState : Type := {
      tsa_vertices : LPNodeMap A;
      tsa_edges : LPEdges;
      tsa_snapshots : TMap.t LPNodeSet;
      tsa_pending_pushes : TMap.t Addr;
      tsa_garbage : LPNodeSet;
      tsa_pop_starts : TMap.t LPNodeSet;
      tsa_pop_ts : TMap.t TS;
      (** Ghost timing data; see the module comment. *)
      tsa_now : nat;
      tsa_node_inv : LPNodeMap nat;
      tsa_node_ret : LPNodeMap nat;
      tsa_snap_time : TMap.t nat;
      tsa_session_time : TMap.t nat;
      tsa_removals : LPNodeMap (tid * nat * nat);
    }.

    Definition tsa_is_vertex
        (s : TryStackAuxState) (n : LPNodeId) : Prop :=
      tsa_vertices s n <> None.

    Definition tsa_is_pending
        (s : TryStackAuxState) (n : LPNodeId) : Prop :=
      TMap.find (fst n) (tsa_pending_pushes s) = Some (snd n).

    Definition tsa_is_live
        (s : TryStackAuxState) (n : LPNodeId) : Prop :=
      tsa_is_vertex s n /\ ~ tsa_garbage s n.

    Definition tsa_fresh_node
        (s : TryStackAuxState) (n : LPNodeId) : Prop :=
      tsa_vertices s n = None /\ ~ tsa_garbage s n.

    Definition tsa_all_vertices_garbage
        (s : TryStackAuxState) : Prop :=
      forall n, tsa_is_vertex s n <-> tsa_garbage s n.

    Definition tsa_completed_set (s : TryStackAuxState) : LPNodeSet :=
      fun n => tsa_is_vertex s n /\ ~ tsa_is_pending s n.

    Definition tsa_start_push
        (actor : tid) (loc : Addr) (v : A)
        (s : TryStackAuxState) : TryStackAuxState :=
      let n := (actor, loc) in
      {|
        tsa_vertices := node_update n v (tsa_vertices s);
        tsa_edges :=
          fun n1 n2 =>
            tsa_edges s n1 n2 \/
            (n1 = n /\ tsa_is_vertex s n2 /\ ~ tsa_is_pending s n2);
        tsa_snapshots := tsa_snapshots s;
        tsa_pending_pushes :=
          TMap.add actor loc (tsa_pending_pushes s);
        tsa_garbage := tsa_garbage s;
        tsa_pop_starts := tsa_pop_starts s;
        tsa_pop_ts := tsa_pop_ts s;
        tsa_now := S (tsa_now s);
        tsa_node_inv := node_update n (tsa_now s) (tsa_node_inv s);
        tsa_node_ret := tsa_node_ret s;
        tsa_snap_time := tsa_snap_time s;
        tsa_session_time := tsa_session_time s;
        tsa_removals := tsa_removals s
      |}.

    Definition tsa_finish_push
        (actor : tid) (s : TryStackAuxState) : TryStackAuxState :=
      {|
        tsa_vertices := tsa_vertices s;
        tsa_edges := tsa_edges s;
        tsa_snapshots := tsa_snapshots s;
        tsa_pending_pushes :=
          TMap.remove actor (tsa_pending_pushes s);
        tsa_garbage := tsa_garbage s;
        tsa_pop_starts := tsa_pop_starts s;
        tsa_pop_ts := tsa_pop_ts s;
        tsa_now := S (tsa_now s);
        tsa_node_inv := tsa_node_inv s;
        tsa_node_ret :=
          match TMap.find actor (tsa_pending_pushes s) with
          | Some loc => node_update (actor, loc) (tsa_now s) (tsa_node_ret s)
          | None => tsa_node_ret s
          end;
        tsa_snap_time := tsa_snap_time s;
        tsa_session_time := tsa_session_time s;
        tsa_removals := tsa_removals s
      |}.

    (** [startPop] invocation: open the session with the completed
        vertices as its start set, stamped with the current clock. *)
    Definition tsa_start_pop_session
        (actor : tid) (s : TryStackAuxState) : TryStackAuxState :=
      {|
        tsa_vertices := tsa_vertices s;
        tsa_edges := tsa_edges s;
        tsa_snapshots := tsa_snapshots s;
        tsa_pending_pushes := tsa_pending_pushes s;
        tsa_garbage := tsa_garbage s;
        tsa_pop_starts :=
          TMap.add actor (tsa_completed_set s) (tsa_pop_starts s);
        tsa_pop_ts := TMap.remove actor (tsa_pop_ts s);
        tsa_now := S (tsa_now s);
        tsa_node_inv := tsa_node_inv s;
        tsa_node_ret := tsa_node_ret s;
        tsa_snap_time := tsa_snap_time s;
        tsa_session_time := TMap.add actor (tsa_now s) (tsa_session_time s);
        tsa_removals := tsa_removals s
      |}.

    Definition tsa_finish_pop_session
        (actor : tid) (ts : TS) (s : TryStackAuxState) : TryStackAuxState :=
      {|
        tsa_vertices := tsa_vertices s;
        tsa_edges := tsa_edges s;
        tsa_snapshots := tsa_snapshots s;
        tsa_pending_pushes := tsa_pending_pushes s;
        tsa_garbage := tsa_garbage s;
        tsa_pop_starts := tsa_pop_starts s;
        tsa_pop_ts := TMap.add actor ts (tsa_pop_ts s);
        tsa_now := S (tsa_now s);
        tsa_node_inv := tsa_node_inv s;
        tsa_node_ret := tsa_node_ret s;
        tsa_snap_time := tsa_snap_time s;
        tsa_session_time := tsa_session_time s;
        tsa_removals := tsa_removals s
      |}.

    Definition tsa_start_snapshot
        (actor : tid) (s : TryStackAuxState) : TryStackAuxState :=
      {|
        tsa_vertices := tsa_vertices s;
        tsa_edges := tsa_edges s;
        tsa_snapshots :=
          TMap.add actor (fun n => tsa_is_vertex s n) (tsa_snapshots s);
        tsa_pending_pushes := tsa_pending_pushes s;
        tsa_garbage := tsa_garbage s;
        tsa_pop_starts := tsa_pop_starts s;
        tsa_pop_ts := tsa_pop_ts s;
        tsa_now := S (tsa_now s);
        tsa_node_inv := tsa_node_inv s;
        tsa_node_ret := tsa_node_ret s;
        tsa_snap_time := TMap.add actor (tsa_now s) (tsa_snap_time s);
        tsa_session_time := tsa_session_time s;
        tsa_removals := tsa_removals s
      |}.

    (** A failed [trypop] clears the snapshot and keeps the session. *)
    Definition tsa_clear_snapshot
        (actor : tid) (s : TryStackAuxState) : TryStackAuxState :=
      {|
        tsa_vertices := tsa_vertices s;
        tsa_edges := tsa_edges s;
        tsa_snapshots := TMap.remove actor (tsa_snapshots s);
        tsa_pending_pushes := tsa_pending_pushes s;
        tsa_garbage := tsa_garbage s;
        tsa_pop_starts := tsa_pop_starts s;
        tsa_pop_ts := tsa_pop_ts s;
        tsa_now := S (tsa_now s);
        tsa_node_inv := tsa_node_inv s;
        tsa_node_ret := tsa_node_ret s;
        tsa_snap_time := TMap.remove actor (tsa_snap_time s);
        tsa_session_time := tsa_session_time s;
        tsa_removals := tsa_removals s
      |}.

    (** The empty response closes the session without touching the
        graph. *)
    Definition tsa_close_session
        (actor : tid) (s : TryStackAuxState) : TryStackAuxState :=
      {|
        tsa_vertices := tsa_vertices s;
        tsa_edges := tsa_edges s;
        tsa_snapshots := tsa_snapshots s;
        tsa_pending_pushes := tsa_pending_pushes s;
        tsa_garbage := tsa_garbage s;
        tsa_pop_starts := TMap.remove actor (tsa_pop_starts s);
        tsa_pop_ts := TMap.remove actor (tsa_pop_ts s);
        tsa_now := S (tsa_now s);
        tsa_node_inv := tsa_node_inv s;
        tsa_node_ret := tsa_node_ret s;
        tsa_snap_time := tsa_snap_time s;
        tsa_session_time := TMap.remove actor (tsa_session_time s);
        tsa_removals := tsa_removals s
      |}.

    (** A successful [trypop] is one recorded event: the snapshot is
        cleared, the node becomes garbage, the removal is logged with the
        remover's session time, and the session is closed. *)
    Definition tsa_remove_node
        (actor : tid) (n : LPNodeId) (s : TryStackAuxState) :
        TryStackAuxState :=
      {|
        tsa_vertices := tsa_vertices s;
        tsa_edges := tsa_edges s;
        tsa_snapshots := TMap.remove actor (tsa_snapshots s);
        tsa_pending_pushes := tsa_pending_pushes s;
        tsa_garbage := set_add n (tsa_garbage s);
        tsa_pop_starts := TMap.remove actor (tsa_pop_starts s);
        tsa_pop_ts := TMap.remove actor (tsa_pop_ts s);
        tsa_now := S (tsa_now s);
        tsa_node_inv := tsa_node_inv s;
        tsa_node_ret := tsa_node_ret s;
        tsa_snap_time := TMap.remove actor (tsa_snap_time s);
        tsa_session_time := TMap.remove actor (tsa_session_time s);
        tsa_removals :=
          match TMap.find actor (tsa_session_time s) with
          | Some st => node_update n (actor, st, tsa_now s) (tsa_removals s)
          | None => tsa_removals s
          end
      |}.

    Definition empty_try_stack_aux_state : TryStackAuxState :=
      {|
        tsa_vertices := empty_node_map;
        tsa_edges := empty_edges;
        tsa_snapshots := TMap.empty LPNodeSet;
        tsa_pending_pushes := TMap.empty Addr;
        tsa_garbage := empty_node_set;
        tsa_pop_starts := TMap.empty LPNodeSet;
        tsa_pop_ts := TMap.empty TS;
        tsa_now := 0;
        tsa_node_inv := empty_node_map;
        tsa_node_ret := empty_node_map;
        tsa_snap_time := TMap.empty nat;
        tsa_session_time := TMap.empty nat;
        tsa_removals := empty_node_map
      |}.

    Variant TryStackAuxControl : Type :=
    | TSAReady (s : TryStackAuxState)
    | TSAAtomicPending
        (s : TryStackAuxState)
        (actor : tid)
        (op : ETryStackAux_op).

    Variant StepTryStackAux :
      @ThreadEvent ETryStackAux ->
      TryStackAuxControl ->
      TryStackAuxControl ->
      Prop :=

    (** Push is lifted unchanged from ListPool. *)
    | step_tsa_push_inv actor s v loc e :
        TMap.find actor (tsa_pending_pushes s) = None ->
        tsa_fresh_node s (actor, loc) ->
        e = {| te_tid := actor; te_ev := InvEv (tsa_push v) |} ->
        StepTryStackAux e
          (TSAReady s)
          (TSAReady (tsa_start_push actor loc v s))
    | step_tsa_push_res actor s v loc e :
        TMap.find actor (tsa_pending_pushes s) = Some loc ->
        e = {| te_tid := actor;
               te_ev := ResEv (tsa_push v) tt |} ->
        StepTryStackAux e
          (TSAReady s)
          (TSAReady (tsa_finish_push actor s))

    (** startPop mirrors ListPool's. *)
    | step_tsa_startPop_inv actor s e :
        e = {| te_tid := actor; te_ev := InvEv tsa_startPop |} ->
        StepTryStackAux e
          (TSAReady s)
          (TSAReady (tsa_start_pop_session actor s))
    | step_tsa_startPop_res actor s ts e :
        e = {| te_tid := actor; te_ev := ResEv tsa_startPop ts |} ->
        StepTryStackAux e
          (TSAReady s)
          (TSAReady (tsa_finish_pop_session actor ts s))

    (** Empty [trypop] linearizes atomically at invocation and closes the
        session at the response. *)
    | step_tsa_trypop_empty_inv actor s start e :
        TMap.find actor (tsa_snapshots s) = None ->
        TMap.find actor (tsa_pop_ts s) = Some start ->
        tsa_all_vertices_garbage s ->
        e = {| te_tid := actor; te_ev := InvEv (tsa_trypop start) |} ->
        StepTryStackAux e
          (TSAReady s)
          (TSAAtomicPending s actor (tsa_trypop start))
    | step_tsa_trypop_empty_res actor s start e :
        e = {| te_tid := actor;
               te_ev := ResEv (tsa_trypop start) TSuccEmpty |} ->
        StepTryStackAux e
          (TSAAtomicPending s actor (tsa_trypop start))
          (TSAReady (tsa_close_session actor s))

    (** The snapshot branch records [dom(V)]. *)
    | step_tsa_trypop_snapshot_inv actor s start e :
        TMap.find actor (tsa_snapshots s) = None ->
        TMap.find actor (tsa_pop_ts s) = Some start ->
        e = {| te_tid := actor; te_ev := InvEv (tsa_trypop start) |} ->
        StepTryStackAux e
          (TSAReady s)
          (TSAReady (tsa_start_snapshot actor s))

    (** A successful response removes a top member of the saved live set
        and closes the session. *)
    | step_tsa_trypop_succ actor s start N n v e :
        TMap.find actor (tsa_snapshots s) = Some N ->
        lp_top
          (fun n' => N n' /\ ~ tsa_garbage s n')
          (tsa_edges s) n ->
        tsa_vertices s n = Some v ->
        e = {| te_tid := actor;
               te_ev := ResEv (tsa_trypop start)
                 (TSuccNode v (fst n) (snd n)) |} ->
        StepTryStackAux e
          (TSAReady s)
          (TSAReady (tsa_remove_node actor n s))
    (** Elimination: a live vertex outside the session's start set. *)
    | step_tsa_trypop_elim actor s start N N0 n v e :
        TMap.find actor (tsa_snapshots s) = Some N ->
        TMap.find actor (tsa_pop_starts s) = Some N0 ->
        ~ N0 n ->
        tsa_is_live s n ->
        tsa_vertices s n = Some v ->
        e = {| te_tid := actor;
               te_ev := ResEv (tsa_trypop start)
                 (TSuccNode v (fst n) (snd n)) |} ->
        StepTryStackAux e
          (TSAReady s)
          (TSAReady (tsa_remove_node actor n s))
    | step_tsa_trypop_fail actor s start N e :
        TMap.find actor (tsa_snapshots s) = Some N ->
        e = {| te_tid := actor;
               te_ev := ResEv (tsa_trypop start) TFail |} ->
        StepTryStackAux e
          (TSAReady s)
          (TSAReady (tsa_clear_snapshot actor s)).

    Variant ErrorTryStackAux :
      @ThreadEvent ETryStackAux -> TryStackAuxControl -> Prop :=
    | error_tsa_actor_outside actor op s e :
        ~ ThreadDomain.contains D actor ->
        e = {| te_tid := actor; te_ev := InvEv op |} ->
        ErrorTryStackAux e (TSAReady s)
    | error_tsa_trypop_no_session actor start s e :
        TMap.find actor (tsa_pop_ts s) <> Some start ->
        e = {| te_tid := actor; te_ev := InvEv (tsa_trypop start) |} ->
        ErrorTryStackAux e (TSAReady s).

    Definition VTryStackAux : @LTS ETryStackAux :=
      {|
        State := TryStackAuxControl;
        Step := StepTryStackAux;
        Error := ErrorTryStackAux
      |}.

    Lemma empty_tsa_state_has_no_vertex n :
      ~ tsa_is_vertex empty_try_stack_aux_state n.
    Proof.
      unfold tsa_is_vertex, empty_try_stack_aux_state, empty_node_map; simpl.
      intro Hneq. apply Hneq. reflexivity.
    Qed.

    Lemma empty_tsa_state_all_vertices_garbage :
      tsa_all_vertices_garbage empty_try_stack_aux_state.
    Proof.
      intro n. split.
      - intro H. exfalso. now apply (empty_tsa_state_has_no_vertex n).
      - simpl. contradiction.
    Qed.

  End Spec.

  Module TryStackAuxElimLayer.
    Section Layer.
      Context {A : Type}.
      Context (D : ThreadDomain.t).

      Definition L : layer_interface :=
      {|
        li_sig := @ETryStackAux A;
        li_lts := @VTryStackAux A D;
        li_init := TSAReady (@empty_try_stack_aux_state A)
      |}.
    End Layer.
  End TryStackAuxElimLayer.

End TryStackAuxElimSpec.
