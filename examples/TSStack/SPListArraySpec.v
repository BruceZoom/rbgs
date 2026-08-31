Require Import FMapPositive.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.PArith.PArith.

Require Import models.EffectSignatures.
Require Import examples.Common.Heap.
Require Import examples.TSStack.TimestampSpec.
Require Import examples.TSStack.SPListSpec.
Require Import examples.TSStack.ListPoolSpec.
Require Import examples.Common.ThreadDomain.
Require Import LinCCAL.
Require Import LTS.
Require Import TPSimulationSet.


(** The SPList-array abstraction from Appendix A.2.  It flattens the rows
    into a node/timestamp graph and exposes per-caller scan progress needed
    by the List Pool invariant. *)
Module SPListArraySpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import TimestampSpec.
  Import SPListSpec.
  Import ListPoolSpec.
  Import TPSimulationSet.TPSimulation.
  Import ListNotations.

  Inductive VisitStatus : Type :=
  | Unvisited
  | Visiting
  | Visited
  | Ignored.

  Record CurrentScan : Type := {
    current_owner : tid;
    (** The row order saved at invocation.  Membership in this list is the
        snapshot set used by [scan_status]; its order determines [getTop]. *)
    current_order : list Addr;
    current_counter : nat;
  }.

  Definition current_nodes (c : CurrentScan) : LPNodeSet :=
    fun n =>
      fst n = current_owner c /\
      In (snd n) (current_order c).

  Record ScanProgress : Type := {
    scan_visited : list tid;
    scan_seen : LPNodeSet;
    scan_current : option CurrentScan;
  }.

  Definition empty_scan : ScanProgress :=
    {|
      scan_visited := nil;
      scan_seen := empty_node_set;
      scan_current := None
    |}.

  Definition set_union (N1 N2 : LPNodeSet) : LPNodeSet :=
    fun n => N1 n \/ N2 n.

  Definition finish_progress
      (p : ScanProgress) (c : CurrentScan) : ScanProgress :=
    {|
      scan_visited := scan_visited p ++ [current_owner c];
      scan_seen := set_union (scan_seen p) (current_nodes c);
      scan_current := None
    |}.

  (** Status is derived rather than eagerly stored.  Consequently a push
      changes only its row: a node inserted after a row snapshot is
      automatically [Ignored] for that scan. *)
  Inductive scan_status (p : ScanProgress) (n : LPNodeId) :
      VisitStatus -> Prop :=
  | scan_status_visited :
      In (fst n) (scan_visited p) ->
      scan_seen p n ->
      scan_status p n Visited
  | scan_status_ignored_visited :
      In (fst n) (scan_visited p) ->
      ~ scan_seen p n ->
      scan_status p n Ignored
  | scan_status_visiting c :
      scan_current p = Some c ->
      current_owner c = fst n ->
      current_nodes c n ->
      scan_status p n Visiting
  | scan_status_ignored_current c :
      scan_current p = Some c ->
      current_owner c = fst n ->
      ~ current_nodes c n ->
      scan_status p n Ignored
  | scan_status_unvisited :
      ~ In (fst n) (scan_visited p) ->
      (forall c, scan_current p = Some c -> current_owner c <> fst n) ->
      scan_status p n Unvisited.

  Section Spec.
    Context {A : Type}.
    Context (D : ThreadDomain.t).

    Variant ESPListArray_op :=
    | array_insert (v : A)
    | array_setTS (loc : Addr) (ts : TS)
    | array_getTop (owner : tid)
    | array_resetIter
    | array_tryRemove (owner : tid) (loc : Addr)
    | array_getCounter.
    Arguments ESPListArray_op : clear implicits.

    Definition ESPListArray_ar (op : ESPListArray_op) : Type :=
      match op with
      | array_insert _ => Addr
      | array_setTS _ _ => unit
      | array_getTop _ => @LNode A + nat
      | array_resetIter => unit
      | array_tryRemove _ _ => bool
      | array_getCounter => nat
      end.

    Canonical Structure ESPListArray :=
    {|
      Sig.op := ESPListArray_op;
      Sig.ar := ESPListArray_ar
    |}.

    Record SPListArrayState : Type := {
      as_counters : TMap.t nat;
      as_values : LPNodeMap A;
      as_timestamps : LPNodeId -> option TS;
      as_garbage : LPNodeSet;
      (** Current live list order for every row. *)
      as_orders : TMap.t (list Addr);
      as_scans : TMap.t ScanProgress;
      as_pending_counters : TMap.t nat;
    }.

    Definition counter_at (owner : tid) (s : SPListArrayState) : nat :=
      match TMap.find owner (as_counters s) with
      | Some count => count
      | None => 0
      end.

    Fixpoint sum_counters
        (owners : list tid) (counters : TMap.t nat) : nat :=
      match owners with
      | nil => 0
      | owner :: owners' =>
          match TMap.find owner counters with
          | Some count => count
          | None => 0
          end + sum_counters owners' counters
      end.

    Definition total_counter (s : SPListArrayState) : nat :=
      sum_counters (ThreadDomain.threads D) (as_counters s).

    Definition array_vertex (s : SPListArrayState) (n : LPNodeId) : Prop :=
      as_values s n <> None.

    Definition array_live (s : SPListArrayState) (n : LPNodeId) : Prop :=
      array_vertex s n /\ ~ as_garbage s n.

    Definition array_fresh (s : SPListArrayState) (n : LPNodeId) : Prop :=
      as_values s n = None /\ ~ as_garbage s n.

    Definition order_at (owner : tid) (s : SPListArrayState) : list Addr :=
      match TMap.find owner (as_orders s) with
      | Some order => order
      | None => nil
      end.

    Definition row_snapshot
        (owner : tid) (s : SPListArrayState) : LPNodeSet :=
      fun n =>
        fst n = owner /\
        In (snd n) (order_at owner s).

    (** The concrete row saves its order at invocation and, at response,
        filters out locations no longer present in the current live order.
        This is the array-level counterpart of [SPListSpec.actual_snapshot]. *)
    Definition actual_scan_order
        (c : CurrentScan) (s : SPListArrayState) : list Addr :=
      List.filter
        (fun loc =>
          List.existsb (Nat.eqb loc)
            (order_at (current_owner c) s))
        (current_order c).

    Definition timestamp_update
        (n : LPNodeId) (ts : TS)
        (timestamps : LPNodeId -> option TS) : LPNodeId -> option TS :=
      fun n' => if node_eq_dec n n' then Some ts else timestamps n'.

    Definition timestamp_above (newer older : TS) : Prop :=
      timestamp_lt older newer.

    Definition array_edge
        (s : SPListArrayState) (newer older : LPNodeId) : Prop :=
      exists newer_ts older_ts,
        as_timestamps s newer = Some newer_ts /\
        as_timestamps s older = Some older_ts /\
        timestamp_above newer_ts older_ts.

    Definition insert_node
        (actor : tid) (loc : Addr) (v : A)
        (s : SPListArrayState) : SPListArrayState :=
      {|
        as_counters :=
          TMap.add actor (S (counter_at actor s)) (as_counters s);
        as_values := node_update (actor, loc) v (as_values s);
        as_timestamps :=
          timestamp_update (actor, loc) TSTop (as_timestamps s);
        as_garbage := as_garbage s;
        as_orders :=
          TMap.add actor (loc :: order_at actor s) (as_orders s);
        as_scans := as_scans s;
        as_pending_counters := as_pending_counters s
      |}.

    Definition set_node_timestamp
        (actor : tid) (loc : Addr) (ts : TS)
        (s : SPListArrayState) : SPListArrayState :=
      let n := (actor, loc) in
      {|
        as_counters := as_counters s;
        as_values := as_values s;
        as_timestamps :=
          match as_timestamps s n with
          | Some TSTop => timestamp_update n ts (as_timestamps s)
          | _ => as_timestamps s
          end;
        as_garbage := as_garbage s;
        as_orders := as_orders s;
        as_scans := as_scans s;
        as_pending_counters := as_pending_counters s
      |}.

    Definition reset_scan
        (actor : tid) (s : SPListArrayState) : SPListArrayState :=
      {|
        as_counters := as_counters s;
        as_values := as_values s;
        as_timestamps := as_timestamps s;
        as_garbage := as_garbage s;
        as_orders := as_orders s;
        as_scans := TMap.add actor empty_scan (as_scans s);
        as_pending_counters := as_pending_counters s
      |}.

    Definition begin_scan
        (actor owner : tid) (p : ScanProgress)
        (s : SPListArrayState) : SPListArrayState :=
      let current :=
        {|
          current_owner := owner;
          current_order := order_at owner s;
          current_counter := counter_at owner s
        |} in
      let p' :=
        {|
          scan_visited := scan_visited p;
          scan_seen := scan_seen p;
          scan_current := Some current
        |} in
      {|
        as_counters := as_counters s;
        as_values := as_values s;
        as_timestamps := as_timestamps s;
        as_garbage := as_garbage s;
        as_orders := as_orders s;
        as_scans := TMap.add actor p' (as_scans s);
        as_pending_counters := as_pending_counters s
      |}.

    Definition end_scan
        (actor : tid) (p : ScanProgress) (c : CurrentScan)
        (s : SPListArrayState) : SPListArrayState :=
      {|
        as_counters := as_counters s;
        as_values := as_values s;
        as_timestamps := as_timestamps s;
        as_garbage := as_garbage s;
        as_orders := as_orders s;
        as_scans :=
          TMap.add actor (finish_progress p c) (as_scans s);
        as_pending_counters := as_pending_counters s
      |}.

    Definition remove_node
        (n : LPNodeId) (s : SPListArrayState) : SPListArrayState :=
      {|
        as_counters := as_counters s;
        as_values := as_values s;
        as_timestamps := as_timestamps s;
        as_garbage := set_add n (as_garbage s);
        as_orders :=
          TMap.add (fst n)
            (List.remove Nat.eq_dec (snd n) (order_at (fst n) s))
            (as_orders s);
        as_scans := as_scans s;
        as_pending_counters := as_pending_counters s
      |}.

    Definition start_counter
        (actor : tid) (s : SPListArrayState) : SPListArrayState :=
      {|
        as_counters := as_counters s;
        as_values := as_values s;
        as_timestamps := as_timestamps s;
        as_garbage := as_garbage s;
        as_orders := as_orders s;
        as_scans := as_scans s;
        as_pending_counters :=
          TMap.add actor (total_counter s) (as_pending_counters s)
      |}.

    Definition finish_counter
        (actor : tid) (s : SPListArrayState) : SPListArrayState :=
      {|
        as_counters := as_counters s;
        as_values := as_values s;
        as_timestamps := as_timestamps s;
        as_garbage := as_garbage s;
        as_orders := as_orders s;
        as_scans := as_scans s;
        as_pending_counters :=
          TMap.remove actor (as_pending_counters s)
      |}.

    Fixpoint initial_counters (owners : list tid) : TMap.t nat :=
      match owners with
      | nil => TMap.empty nat
      | owner :: owners' => TMap.add owner 0 (initial_counters owners')
      end.

    Fixpoint initial_orders (owners : list tid) : TMap.t (list Addr) :=
      match owners with
      | nil => TMap.empty (list Addr)
      | owner :: owners' => TMap.add owner nil (initial_orders owners')
      end.

    Definition empty_array_state : SPListArrayState :=
      {|
        as_counters := initial_counters (ThreadDomain.threads D);
        as_values := empty_node_map;
        as_timestamps := fun _ => None;
        as_garbage := empty_node_set;
        as_orders := initial_orders (ThreadDomain.threads D);
        as_scans := TMap.empty ScanProgress;
        as_pending_counters := TMap.empty nat
      |}.

    Variant SPListArrayControl : Type :=
    | ArrayReady (s : SPListArrayState)
    | ArrayAtomicPending
        (s : SPListArrayState)
        (actor : tid)
        (op : ESPListArray_op).

    Variant StepSPListArray :
      @ThreadEvent ESPListArray ->
      SPListArrayControl ->
      SPListArrayControl ->
      Prop :=
    | step_insert_inv actor s v e :
        ThreadDomain.contains D actor ->
        e = {| te_tid := actor; te_ev := InvEv (array_insert v) |} ->
        StepSPListArray e
          (ArrayReady s)
          (ArrayAtomicPending s actor (array_insert v))
    | step_insert_res actor s v loc e :
        array_fresh s (actor, loc) ->
        e = {| te_tid := actor;
               te_ev := ResEv (array_insert v) loc |} ->
        StepSPListArray e
          (ArrayAtomicPending s actor (array_insert v))
          (ArrayReady (insert_node actor loc v s))

    | step_setTS_inv actor s loc ts e :
        ThreadDomain.contains D actor ->
        array_vertex s (actor, loc) ->
        e = {| te_tid := actor;
               te_ev := InvEv (array_setTS loc ts) |} ->
        StepSPListArray e
          (ArrayReady s)
          (ArrayAtomicPending s actor (array_setTS loc ts))
    | step_setTS_res actor s loc ts e :
        e = {| te_tid := actor;
               te_ev := ResEv (array_setTS loc ts) tt |} ->
        StepSPListArray e
          (ArrayAtomicPending s actor (array_setTS loc ts))
          (ArrayReady (set_node_timestamp actor loc ts s))

    | step_reset_inv actor s e :
        ThreadDomain.contains D actor ->
        e = {| te_tid := actor; te_ev := InvEv array_resetIter |} ->
        StepSPListArray e
          (ArrayReady s)
          (ArrayAtomicPending s actor array_resetIter)
    | step_reset_res actor s e :
        e = {| te_tid := actor;
               te_ev := ResEv array_resetIter tt |} ->
        StepSPListArray e
          (ArrayAtomicPending s actor array_resetIter)
          (ArrayReady (reset_scan actor s))

    | step_getTop_inv actor owner s p e :
        ThreadDomain.contains D actor ->
        ThreadDomain.contains D owner ->
        TMap.find actor (as_scans s) = Some p ->
        scan_current p = None ->
        ~ In owner (scan_visited p) ->
        e = {| te_tid := actor;
               te_ev := InvEv (array_getTop owner) |} ->
        StepSPListArray e
          (ArrayReady s)
          (ArrayReady (begin_scan actor owner p s))
    (** The response is the first location from the saved row order that is
        still present in the row's current live order.  Timestamp order is
        deliberately not part of this layer's [getTop] contract. *)
    | step_getTop_nonempty_res actor owner s p c loc remaining v ts e :
        TMap.find actor (as_scans s) = Some p ->
        scan_current p = Some c ->
        current_owner c = owner ->
        actual_scan_order c s = loc :: remaining ->
        as_values s (owner, loc) = Some v ->
        as_timestamps s (owner, loc) = Some ts ->
        e = {| te_tid := actor;
               te_ev := ResEv (array_getTop owner)
                 (@inl (@LNode A) nat (v, ts, loc)) |} ->
        StepSPListArray e
          (ArrayReady s)
          (ArrayReady (end_scan actor p c s))
    | step_getTop_empty_res actor owner s p c e :
        TMap.find actor (as_scans s) = Some p ->
        scan_current p = Some c ->
        current_owner c = owner ->
        actual_scan_order c s = nil ->
        e = {| te_tid := actor;
               te_ev := ResEv (array_getTop owner)
                 (@inr (@LNode A) nat (current_counter c)) |} ->
        StepSPListArray e
          (ArrayReady s)
          (ArrayReady (end_scan actor p c s))

    | step_tryRemove_inv actor owner loc s e :
        ThreadDomain.contains D actor ->
        ThreadDomain.contains D owner ->
        array_vertex s (owner, loc) ->
        e = {| te_tid := actor;
               te_ev := InvEv (array_tryRemove owner loc) |} ->
        StepSPListArray e
          (ArrayReady s)
          (ArrayAtomicPending s actor (array_tryRemove owner loc))
    | step_tryRemove_succ actor owner loc s e :
        array_live s (owner, loc) ->
        e = {| te_tid := actor;
               te_ev := ResEv (array_tryRemove owner loc) true |} ->
        StepSPListArray e
          (ArrayAtomicPending s actor (array_tryRemove owner loc))
          (ArrayReady (remove_node (owner, loc) s))
    | step_tryRemove_fail actor owner loc s e :
        as_garbage s (owner, loc) ->
        e = {| te_tid := actor;
               te_ev := ResEv (array_tryRemove owner loc) false |} ->
        StepSPListArray e
          (ArrayAtomicPending s actor (array_tryRemove owner loc))
          (ArrayReady s)

    | step_counter_inv actor s e :
        ThreadDomain.contains D actor ->
        TMap.find actor (as_pending_counters s) = None ->
        e = {| te_tid := actor; te_ev := InvEv array_getCounter |} ->
        StepSPListArray e
          (ArrayReady s)
          (ArrayReady (start_counter actor s))
    | step_counter_res actor s saved result e :
        TMap.find actor (as_pending_counters s) = Some saved ->
        saved <= result ->
        result <= total_counter s ->
        e = {| te_tid := actor;
               te_ev := ResEv array_getCounter result |} ->
        StepSPListArray e
          (ArrayReady s)
          (ArrayReady (finish_counter actor s)).

    Variant ErrorSPListArray :
      @ThreadEvent ESPListArray -> SPListArrayControl -> Prop :=
    | error_actor_outside actor op s :
        ~ ThreadDomain.contains D actor ->
        ErrorSPListArray
          {| te_tid := actor; te_ev := InvEv op |}
          (ArrayReady s)
    | error_getTop_owner_outside actor owner s :
        ~ ThreadDomain.contains D owner ->
        ErrorSPListArray
          {| te_tid := actor; te_ev := InvEv (array_getTop owner) |}
          (ArrayReady s)
    | error_getTop_without_reset actor owner s :
        TMap.find actor (as_scans s) = None ->
        ErrorSPListArray
          {| te_tid := actor; te_ev := InvEv (array_getTop owner) |}
          (ArrayReady s)
    | error_getTop_repeat actor owner s p :
        TMap.find actor (as_scans s) = Some p ->
        (In owner (scan_visited p) \/ scan_current p <> None) ->
        ErrorSPListArray
          {| te_tid := actor; te_ev := InvEv (array_getTop owner) |}
          (ArrayReady s)
    | error_tryRemove_owner_outside actor owner loc s :
        ~ ThreadDomain.contains D owner ->
        ErrorSPListArray
          {| te_tid := actor;
             te_ev := InvEv (array_tryRemove owner loc) |}
          (ArrayReady s)
    | error_tryRemove_undefined actor owner loc s :
        ~ array_vertex s (owner, loc) ->
        ErrorSPListArray
          {| te_tid := actor;
             te_ev := InvEv (array_tryRemove owner loc) |}
          (ArrayReady s)
    | error_setTS_undefined actor loc ts s :
        ~ array_vertex s (actor, loc) ->
        ErrorSPListArray
          {| te_tid := actor;
             te_ev := InvEv (array_setTS loc ts) |}
          (ArrayReady s).

    Definition VSPListArray : @LTS ESPListArray :=
      {|
        State := SPListArrayControl;
        Step := StepSPListArray;
        Error := ErrorSPListArray
      |}.

  End Spec.

  Module SPListArrayLayer.
    Section Layer.
      Context {A : Type}.
      Context (D : ThreadDomain.t).

      Definition L : layer_interface :=
      {|
        li_sig := @ESPListArray A;
        li_lts := @VSPListArray A D;
        li_init := ArrayReady (@empty_array_state A D)
      |}.
    End Layer.
  End SPListArrayLayer.

End SPListArraySpec.
