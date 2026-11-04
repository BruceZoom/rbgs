Require Import FMapPositive.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.PArith.PArith.

Require Import models.EffectSignatures.
Require Import examples.Common.Heap.
Require Import examples.Common.ThreadDomain.
Require Import examples.TSStack.ListPoolSpec.
Require Import LinCCAL.
Require Import LTS.
Require Import TPSimulationSet.


(** The atomic DAG-stack specification: the atomic boundary of the stack
    with elimination (docs/plans/TSStackEliminationPlan.tex, Section 5.3).

    The abstract data is the DAG of [TryStackSpec]: vertices, edges, the
    pending pushes and the garbage set.  Push is interval sequential and
    pop is atomic: it removes any top live vertex or reports the graph
    empty.  There is no fail result; the retry loop lives below this
    layer. *)
Module DagStackSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import ListPoolSpec.
  Import TPSimulationSet.TPSimulation.

  Section Spec.
    Context {A : Type}.
    Context (D : ThreadDomain.t).

    (** The vertex identity stays in the result because the stack layer
        above keys its possibility filter on it. *)
    Variant PopResult : Type :=
    | PNode (v : A) (owner : tid) (loc : Addr)
    | PEmpty.
    Arguments PopResult : clear implicits.

    Variant EDagStack_op :=
    | dag_push (v : A)
    | dag_pop.
    Arguments EDagStack_op : clear implicits.

    Definition EDagStack_ar (op : EDagStack_op) : Type :=
      match op with
      | dag_push _ => unit
      | dag_pop => PopResult
      end.

    Canonical Structure EDagStack :=
    {|
      Sig.op := EDagStack_op;
      Sig.ar := EDagStack_ar
    |}.

    Record DagStackState : Type := {
      ds_vertices : LPNodeMap A;
      ds_edges : LPEdges;
      ds_pending_pushes : TMap.t Addr;
      ds_garbage : LPNodeSet;
    }.

    Definition ds_is_vertex
        (s : DagStackState) (n : LPNodeId) : Prop :=
      ds_vertices s n <> None.

    Definition ds_is_pending
        (s : DagStackState) (n : LPNodeId) : Prop :=
      TMap.find (fst n) (ds_pending_pushes s) = Some (snd n).

    Definition ds_is_live
        (s : DagStackState) (n : LPNodeId) : Prop :=
      ds_is_vertex s n /\ ~ ds_garbage s n.

    Definition ds_fresh_node
        (s : DagStackState) (n : LPNodeId) : Prop :=
      ds_vertices s n = None /\ ~ ds_garbage s n.

    Definition ds_all_vertices_garbage
        (s : DagStackState) : Prop :=
      forall n, ds_is_vertex s n <-> ds_garbage s n.

    Definition ds_start_push
        (actor : tid) (loc : Addr) (v : A)
        (s : DagStackState) : DagStackState :=
      let n := (actor, loc) in
      {|
        ds_vertices := node_update n v (ds_vertices s);
        ds_edges :=
          fun n1 n2 =>
            ds_edges s n1 n2 \/
            (n1 = n /\ ds_is_vertex s n2 /\ ~ ds_is_pending s n2);
        ds_pending_pushes :=
          TMap.add actor loc (ds_pending_pushes s);
        ds_garbage := ds_garbage s
      |}.

    Definition ds_finish_push
        (actor : tid) (s : DagStackState) : DagStackState :=
      {|
        ds_vertices := ds_vertices s;
        ds_edges := ds_edges s;
        ds_pending_pushes := TMap.remove actor (ds_pending_pushes s);
        ds_garbage := ds_garbage s
      |}.

    Definition ds_mark_garbage
        (n : LPNodeId) (s : DagStackState) : DagStackState :=
      {|
        ds_vertices := ds_vertices s;
        ds_edges := ds_edges s;
        ds_pending_pushes := ds_pending_pushes s;
        ds_garbage := set_add n (ds_garbage s)
      |}.

    Definition empty_dag_stack_state : DagStackState :=
      {|
        ds_vertices := empty_node_map;
        ds_edges := empty_edges;
        ds_pending_pushes := TMap.empty Addr;
        ds_garbage := empty_node_set
      |}.

    Variant DagStackControl : Type :=
    | DSReady (s : DagStackState)
    | DSAtomicPending
        (s : DagStackState)
        (actor : tid)
        (op : EDagStack_op).

    Variant StepDagStack :
      @ThreadEvent EDagStack ->
      DagStackControl ->
      DagStackControl ->
      Prop :=

    | step_ds_push_inv actor s v loc e :
        TMap.find actor (ds_pending_pushes s) = None ->
        ds_fresh_node s (actor, loc) ->
        e = {| te_tid := actor; te_ev := InvEv (dag_push v) |} ->
        StepDagStack e
          (DSReady s)
          (DSReady (ds_start_push actor loc v s))
    | step_ds_push_res actor s v loc e :
        TMap.find actor (ds_pending_pushes s) = Some loc ->
        e = {| te_tid := actor;
               te_ev := ResEv (dag_push v) tt |} ->
        StepDagStack e
          (DSReady s)
          (DSReady (ds_finish_push actor s))

    | step_ds_pop_inv actor s e :
        e = {| te_tid := actor; te_ev := InvEv dag_pop |} ->
        StepDagStack e
          (DSReady s)
          (DSAtomicPending s actor dag_pop)
    | step_ds_pop_succ actor s n v e :
        lp_top (fun n' => ds_is_live s n') (ds_edges s) n ->
        ds_vertices s n = Some v ->
        e = {| te_tid := actor;
               te_ev := ResEv dag_pop (PNode v (fst n) (snd n)) |} ->
        StepDagStack e
          (DSAtomicPending s actor dag_pop)
          (DSReady (ds_mark_garbage n s))
    | step_ds_pop_empty actor s e :
        ds_all_vertices_garbage s ->
        e = {| te_tid := actor; te_ev := ResEv dag_pop PEmpty |} ->
        StepDagStack e
          (DSAtomicPending s actor dag_pop)
          (DSReady s).

    Variant ErrorDagStack :
      @ThreadEvent EDagStack -> DagStackControl -> Prop :=
    | error_ds_actor_outside actor op s e :
        ~ ThreadDomain.contains D actor ->
        e = {| te_tid := actor; te_ev := InvEv op |} ->
        ErrorDagStack e (DSReady s).

    Definition VDagStack : @LTS EDagStack :=
      {|
        State := DagStackControl;
        Step := StepDagStack;
        Error := ErrorDagStack
      |}.

    Lemma empty_ds_state_has_no_vertex n :
      ~ ds_is_vertex empty_dag_stack_state n.
    Proof.
      unfold ds_is_vertex, empty_dag_stack_state, empty_node_map; simpl.
      intro Hneq. apply Hneq. reflexivity.
    Qed.

    Lemma empty_ds_state_all_vertices_garbage :
      ds_all_vertices_garbage empty_dag_stack_state.
    Proof.
      intro n. split.
      - intro H. exfalso. now apply (empty_ds_state_has_no_vertex n).
      - simpl. contradiction.
    Qed.

  End Spec.

  Module DagStackLayer.
    Section Layer.
      Context {A : Type}.
      Context (D : ThreadDomain.t).

      Definition L : layer_interface :=
      {|
        li_sig := @EDagStack A;
        li_lts := @VDagStack A D;
        li_init := DSReady (@empty_dag_stack_state A)
      |}.
    End Layer.
  End DagStackLayer.

End DagStackSpec.
