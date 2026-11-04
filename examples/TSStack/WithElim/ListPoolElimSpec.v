Require Import FMapPositive.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.

Require Import models.EffectSignatures.
Require Import examples.Common.Heap.
Require Import examples.Common.ThreadDomain.
Require Import examples.TSStack.Shared.TimestampSpec.
Require Import examples.TSStack.Basic.ListPoolSpec.
Require Import LinCCAL.
Require Import LTS.
Require Import TPSimulationSet.


(** The interval-sequential DAG specification of the List Pool with
    elimination (docs/plans/TSStackEliminationPlan.tex, Section 5.1).

    This is [ListPoolSpec] with a pass-through operation [lpool_startPop]
    and a start token passed to [lpool_getTop].  The abstract effect of
    [startPop] is the start set: the vertices whose push had completed at
    the invocation.  A [getTop] may additionally return any vertex outside
    the caller's start set (the elimination candidate).  The [TS] value is
    an opaque token above this layer; a [getTop] whose token does not match
    the caller's recorded session is an error.

    The generic node vocabulary ([LPNodeId], [node_update], [lp_top], ...)
    and the result type [YResult] are shared with [ListPoolSpec]; the state
    and the transition system are new. *)
Module ListPoolElimSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import TimestampSpec.
  Import ListPoolSpec.
  Import TPSimulationSet.TPSimulation.

  Section Spec.
    Context {A : Type}.
    Context (D : ThreadDomain.t).

    Variant EListPool_op :=
    | lpool_push (v : A)
    | lpool_startPop
    | lpool_getTop (start : TS)
    | lpool_tryRemove (owner : tid) (loc : Addr).
    Arguments EListPool_op : clear implicits.

    Definition EListPool_ar (op : EListPool_op) : Type :=
      match op with
      | lpool_push _ => unit
      | lpool_startPop => TS
      | lpool_getTop _ => @YResult A
      | lpool_tryRemove _ _ => bool
      end.

    Canonical Structure EListPool :=
    {|
      Sig.op := EListPool_op;
      Sig.ar := EListPool_ar
    |}.

    (** [lp_vertices] contains removed vertices as well as live ones.
        Edges point from a newer/higher node to an older/lower node.
        [lp_pop_starts] is the start set of each open pop session and
        [lp_pop_ts] the token returned by that session's [startPop]. *)
    Record ListPoolState : Type := {
      lp_vertices : LPNodeMap A;
      lp_edges : LPEdges;
      lp_snapshots : TMap.t LPNodeSet;
      lp_pending_pushes : TMap.t Addr;
      lp_garbage : LPNodeSet;
      lp_pop_starts : TMap.t LPNodeSet;
      lp_pop_ts : TMap.t TS;
    }.

    Definition is_vertex (s : ListPoolState) (n : LPNodeId) : Prop :=
      lp_vertices s n <> None.

    Definition is_pending (s : ListPoolState) (n : LPNodeId) : Prop :=
      TMap.find (fst n) (lp_pending_pushes s) = Some (snd n).

    Definition is_live (s : ListPoolState) (n : LPNodeId) : Prop :=
      is_vertex s n /\ ~ lp_garbage s n.

    Definition fresh_node (s : ListPoolState) (n : LPNodeId) : Prop :=
      lp_vertices s n = None /\ ~ lp_garbage s n.

    Definition all_vertices_garbage (s : ListPoolState) : Prop :=
      forall n, is_vertex s n <-> lp_garbage s n.

    (** The completed vertices: the start set recorded by [startPop]. *)
    Definition completed_set (s : ListPoolState) : LPNodeSet :=
      fun n => is_vertex s n /\ ~ is_pending s n.

    Definition start_push
        (actor : tid) (loc : Addr) (v : A)
        (s : ListPoolState) : ListPoolState :=
      let n := (actor, loc) in
      {|
        lp_vertices := node_update n v (lp_vertices s);
        lp_edges :=
          fun n1 n2 =>
            lp_edges s n1 n2 \/
            (n1 = n /\ is_vertex s n2 /\ ~ is_pending s n2);
        lp_snapshots := lp_snapshots s;
        lp_pending_pushes :=
          TMap.add actor loc (lp_pending_pushes s);
        lp_garbage := lp_garbage s;
        lp_pop_starts := lp_pop_starts s;
        lp_pop_ts := lp_pop_ts s
      |}.

    Definition finish_push
        (actor : tid) (s : ListPoolState) : ListPoolState :=
      {|
        lp_vertices := lp_vertices s;
        lp_edges := lp_edges s;
        lp_snapshots := lp_snapshots s;
        lp_pending_pushes := TMap.remove actor (lp_pending_pushes s);
        lp_garbage := lp_garbage s;
        lp_pop_starts := lp_pop_starts s;
        lp_pop_ts := lp_pop_ts s
      |}.

    Definition start_snapshot
        (actor : tid) (s : ListPoolState) : ListPoolState :=
      {|
        lp_vertices := lp_vertices s;
        lp_edges := lp_edges s;
        lp_snapshots :=
          TMap.add actor (fun n => is_vertex s n) (lp_snapshots s);
        lp_pending_pushes := lp_pending_pushes s;
        lp_garbage := lp_garbage s;
        lp_pop_starts := lp_pop_starts s;
        lp_pop_ts := lp_pop_ts s
      |}.

    Definition clear_snapshot
        (actor : tid) (s : ListPoolState) : ListPoolState :=
      {|
        lp_vertices := lp_vertices s;
        lp_edges := lp_edges s;
        lp_snapshots := TMap.remove actor (lp_snapshots s);
        lp_pending_pushes := lp_pending_pushes s;
        lp_garbage := lp_garbage s;
        lp_pop_starts := lp_pop_starts s;
        lp_pop_ts := lp_pop_ts s
      |}.

    Definition mark_garbage
        (n : LPNodeId) (s : ListPoolState) : ListPoolState :=
      {|
        lp_vertices := lp_vertices s;
        lp_edges := lp_edges s;
        lp_snapshots := lp_snapshots s;
        lp_pending_pushes := lp_pending_pushes s;
        lp_garbage := set_add n (lp_garbage s);
        lp_pop_starts := lp_pop_starts s;
        lp_pop_ts := lp_pop_ts s
      |}.

    (** [startPop] invocation: record the start set and drop any token of
        an earlier session.  Response: record the token. *)
    Definition start_pop_session
        (actor : tid) (s : ListPoolState) : ListPoolState :=
      {|
        lp_vertices := lp_vertices s;
        lp_edges := lp_edges s;
        lp_snapshots := lp_snapshots s;
        lp_pending_pushes := lp_pending_pushes s;
        lp_garbage := lp_garbage s;
        lp_pop_starts := TMap.add actor (completed_set s) (lp_pop_starts s);
        lp_pop_ts := TMap.remove actor (lp_pop_ts s)
      |}.

    Definition finish_pop_session
        (actor : tid) (ts : TS) (s : ListPoolState) : ListPoolState :=
      {|
        lp_vertices := lp_vertices s;
        lp_edges := lp_edges s;
        lp_snapshots := lp_snapshots s;
        lp_pending_pushes := lp_pending_pushes s;
        lp_garbage := lp_garbage s;
        lp_pop_starts := lp_pop_starts s;
        lp_pop_ts := TMap.add actor ts (lp_pop_ts s)
      |}.

    Definition empty_list_pool_state : ListPoolState :=
      {|
        lp_vertices := empty_node_map;
        lp_edges := empty_edges;
        lp_snapshots := TMap.empty LPNodeSet;
        lp_pending_pushes := TMap.empty Addr;
        lp_garbage := empty_node_set;
        lp_pop_starts := TMap.empty LPNodeSet;
        lp_pop_ts := TMap.empty TS
      |}.

    Variant ListPoolControl : Type :=
    | LPReady (s : ListPoolState)
    | LPAtomicPending
        (s : ListPoolState)
        (actor : tid)
        (op : EListPool_op).

    Variant StepListPool :
      @ThreadEvent EListPool ->
      ListPoolControl ->
      ListPoolControl ->
      Prop :=

    (** Interval-sequential push, unchanged. *)
    | step_push_inv actor s v loc e :
        TMap.find actor (lp_pending_pushes s) = None ->
        fresh_node s (actor, loc) ->
        e = {| te_tid := actor; te_ev := InvEv (lpool_push v) |} ->
        StepListPool e
          (LPReady s)
          (LPReady (start_push actor loc v s))
    | step_push_res actor s v loc e :
        TMap.find actor (lp_pending_pushes s) = Some loc ->
        e = {| te_tid := actor;
               te_ev := ResEv (lpool_push v) tt |} ->
        StepListPool e
          (LPReady s)
          (LPReady (finish_push actor s))

    (** Interval-sequential startPop: the start set is recorded at the
        invocation; any token is accepted at the response. *)
    | step_startPop_inv actor s e :
        e = {| te_tid := actor; te_ev := InvEv lpool_startPop |} ->
        StepListPool e
          (LPReady s)
          (LPReady (start_pop_session actor s))
    | step_startPop_res actor s ts e :
        e = {| te_tid := actor; te_ev := ResEv lpool_startPop ts |} ->
        StepListPool e
          (LPReady s)
          (LPReady (finish_pop_session actor ts s))

    (** The interval-sequential getTop path saves the current vertex set.
        Later pushes cannot change that saved set. *)
    | step_getTop_snapshot_inv actor s start e :
        TMap.find actor (lp_snapshots s) = None ->
        TMap.find actor (lp_pop_ts s) = Some start ->
        e = {| te_tid := actor; te_ev := InvEv (lpool_getTop start) |} ->
        StepListPool e
          (LPReady s)
          (LPReady (start_snapshot actor s))
    | step_getTop_top_res actor s start N n v e :
        TMap.find actor (lp_snapshots s) = Some N ->
        lp_top
          (fun n' => N n' /\ ~ lp_garbage s n')
          (lp_edges s) n ->
        lp_vertices s n = Some v ->
        e = {| te_tid := actor;
               te_ev := ResEv (lpool_getTop start)
                 (YSuccNode v (fst n) (snd n)) |} ->
        StepListPool e
          (LPReady s)
          (LPReady (clear_snapshot actor s))
    | step_getTop_garbage_res actor s start N n v e :
        TMap.find actor (lp_snapshots s) = Some N ->
        lp_garbage s n ->
        lp_vertices s n = Some v ->
        e = {| te_tid := actor;
               te_ev := ResEv (lpool_getTop start)
                 (YSuccNode v (fst n) (snd n)) |} ->
        StepListPool e
          (LPReady s)
          (LPReady (clear_snapshot actor s))
    (** Elimination: any vertex outside the caller's start set may be
        reported.  The rule overlaps the garbage rule on purpose. *)
    | step_getTop_elim_res actor s start N N0 n v e :
        TMap.find actor (lp_snapshots s) = Some N ->
        TMap.find actor (lp_pop_starts s) = Some N0 ->
        ~ N0 n ->
        lp_vertices s n = Some v ->
        e = {| te_tid := actor;
               te_ev := ResEv (lpool_getTop start)
                 (YSuccNode v (fst n) (snd n)) |} ->
        StepListPool e
          (LPReady s)
          (LPReady (clear_snapshot actor s))

    (** Fail and empty are the atomic alternatives for getTop. *)
    | step_getTop_atomic_inv actor s start e :
        TMap.find actor (lp_pop_ts s) = Some start ->
        e = {| te_tid := actor; te_ev := InvEv (lpool_getTop start) |} ->
        StepListPool e
          (LPReady s)
          (LPAtomicPending s actor (lpool_getTop start))
    | step_getTop_fail_res actor s start e :
        e = {| te_tid := actor;
               te_ev := ResEv (lpool_getTop start) YFail |} ->
        StepListPool e
          (LPAtomicPending s actor (lpool_getTop start))
          (LPReady s)
    | step_getTop_empty_res actor s start e :
        all_vertices_garbage s ->
        e = {| te_tid := actor;
               te_ev := ResEv (lpool_getTop start) YSuccEmpty |} ->
        StepListPool e
          (LPAtomicPending s actor (lpool_getTop start))
          (LPReady s)

    (** tryRemove is atomic, unchanged. *)
    | step_tryRemove_inv actor owner loc s e :
        is_vertex s (owner, loc) \/ lp_garbage s (owner, loc) ->
        e = {| te_tid := actor;
               te_ev := InvEv (lpool_tryRemove owner loc) |} ->
        StepListPool e
          (LPReady s)
          (LPAtomicPending s actor (lpool_tryRemove owner loc))
    | step_tryRemove_succ actor owner loc s e :
        is_live s (owner, loc) ->
        e = {| te_tid := actor;
               te_ev := ResEv (lpool_tryRemove owner loc) true |} ->
        StepListPool e
          (LPAtomicPending s actor (lpool_tryRemove owner loc))
          (LPReady (mark_garbage (owner, loc) s))
    | step_tryRemove_fail actor owner loc s e :
        lp_garbage s (owner, loc) ->
        e = {| te_tid := actor;
               te_ev := ResEv (lpool_tryRemove owner loc) false |} ->
        StepListPool e
          (LPAtomicPending s actor (lpool_tryRemove owner loc))
          (LPReady s).

    Variant ErrorListPool :
      @ThreadEvent EListPool -> ListPoolControl -> Prop :=
    | error_actor_outside actor op s e :
        ~ ThreadDomain.contains D actor ->
        e = {| te_tid := actor; te_ev := InvEv op |} ->
        ErrorListPool e (LPReady s)
    | error_tryRemove_owner_outside actor owner loc s e :
        ~ ThreadDomain.contains D owner ->
        e = {| te_tid := actor;
               te_ev := InvEv (lpool_tryRemove owner loc) |} ->
        ErrorListPool e (LPReady s)
    | error_tryRemove_undefined actor owner loc s e :
        ~ is_vertex s (owner, loc) ->
        e = {| te_tid := actor;
               te_ev := InvEv (lpool_tryRemove owner loc) |} ->
        ErrorListPool e (LPReady s)
    (** A getTop whose token is not the caller's current session token. *)
    | error_getTop_no_session actor start s e :
        TMap.find actor (lp_pop_ts s) <> Some start ->
        e = {| te_tid := actor; te_ev := InvEv (lpool_getTop start) |} ->
        ErrorListPool e (LPReady s).

    Definition VListPool : @LTS EListPool :=
      {|
        State := ListPoolControl;
        Step := StepListPool;
        Error := ErrorListPool
      |}.

    Lemma empty_state_has_no_vertex n :
      ~ is_vertex empty_list_pool_state n.
    Proof.
      unfold is_vertex, empty_list_pool_state, empty_node_map; simpl.
      intro Hneq. apply Hneq. reflexivity.
    Qed.

    Lemma empty_state_all_vertices_garbage :
      all_vertices_garbage empty_list_pool_state.
    Proof.
      intro n. split.
      - intro H. exfalso. now apply (empty_state_has_no_vertex n).
      - simpl. contradiction.
    Qed.

  End Spec.

  Module ListPoolElimLayer.
    Section Layer.
      Context {A : Type}.
      Context (D : ThreadDomain.t).

      Definition L : layer_interface :=
      {|
        li_sig := @EListPool A;
        li_lts := @VListPool A D;
        li_init := LPReady (@empty_list_pool_state A)
      |}.
    End Layer.
  End ListPoolElimLayer.

End ListPoolElimSpec.
