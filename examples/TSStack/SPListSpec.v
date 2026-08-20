Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.
Require Import PeanoNat.
Require Import List.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import examples.Common.Heap.
Require Import examples.Common.AtomicLTS.
Require Import examples.TSStack.TimestampSpec.
Require Import LinCCAL.
Require Import LTS.
Require Import TPSimulation.

Open Scope list.

Module SPListSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.
  Import TimestampSpec.

  Section Spec.
    Context {A : Type}.
    Context {owner : tid}.

  Definition LNode : Type := A * TS * Addr (* node address *).

  Variant ESPList_op :=
  | linsert (v : A)
  | lsetTS (l : Addr) (t : TS)
  | lgetTop
  | lgetCounter
  | ltryRemove (l : Addr).
  Arguments ESPList_op : clear implicits.

  Definition ESPlist_ar (m : ESPList_op) : Type :=
    match m with
    | linsert _ => Addr
    | lsetTS _ _ => unit
    | lgetTop => LNode + nat
    | lgetCounter => nat
    | ltryRemove _ => bool
    end.

  Canonical Structure ESPList :=
  {|
    Sig.op := ESPList_op;
    Sig.ar := ESPlist_ar
  |}.

  Record SPListState : Type :=  {
    counter : nat;
    nodes : @Heap (A * TS);
    (* order contains the order of current non-removed nodes *)
    order : list Addr;
    snapshot : TMap.t (list Addr * nat);
  }.

  Definition start_snapshot t (s : SPListState) : SPListState :=
    {|
      counter := counter s;
      nodes := nodes s;
      order := order s;
      snapshot := TMap.add t (order s, counter s) (snapshot s)
    |}.

  Definition clear_snapshot t (s : SPListState) : SPListState :=
    {|
      counter := counter s;
      nodes := nodes s;
      order := order s;
      snapshot := TMap.remove t (snapshot s)
    |}.

  Definition actual_snapshot t (s : SPListState) :
      option (list Addr * nat) :=
    match TMap.find t (snapshot s) with
    | None => None
    | Some (saved, saved_counter) =>
        Some
          (List.filter
             (fun l => List.existsb (Nat.eqb l) (order s))
             saved,
           saved_counter)
    end.


  Definition insert v (l : Addr) (s : SPListState) : SPListState :=
    {|
      counter := counter s + 1;
      nodes := heap_update l (v, TSTop) (nodes s);
      order := l :: (order s);
      snapshot := snapshot s
    |}.

  Definition setTS (l : Addr) (ts : TS) (s : SPListState) : SPListState :=
    match nodes s l with
    | Some (v, TSTop) =>
        {|
          counter := counter s;
          nodes := heap_update l (v, ts) (nodes s);
          order := order s;
          snapshot := snapshot s
        |}
    | _ => s
    end.

  Definition remove (l : Addr) (s : SPListState) : SPListState :=
    {|
      counter := counter s;
      nodes := nodes s;
      order := List.remove Nat.eq_dec l (order s);
      snapshot := snapshot s
    |}.

  Variant SPListControl :=
  | Ready (s : SPListState)
  | AtomicPending
      (s : SPListState)
      (t : tid)
      (op : ESPList_op).

  Variant StepSPList :
    @ThreadEvent ESPList ->
    SPListControl ->
    SPListControl ->
    Prop :=

  (* interval-sequential getTop *)
  | step_getTop_inv t s :
      TMap.find t (snapshot s) = None ->
      StepSPList
        {| te_tid := t; te_ev := InvEv lgetTop |}
        (Ready s)
        (Ready (start_snapshot t s))
  | step_getTop_nonEmpty t s hd tl count v ts :
      actual_snapshot t s = Some (hd :: tl, count) ->
      nodes s hd = Some (v, ts) ->
      StepSPList
        {| te_tid := t;
           te_ev := ResEv lgetTop (@inl LNode nat (v, ts, hd)) |}
        (Ready s)
        (Ready (clear_snapshot t s))
  | step_getTop_empty t s count :
      actual_snapshot t s = Some (nil, count) ->
      StepSPList
        {| te_tid := t;
           te_ev := ResEv lgetTop (@inr LNode nat count) |}
        (Ready s)
        (Ready (clear_snapshot t s))

  (* insert *)
  | step_linsert_inv t s v:
      t = owner ->
      StepSPList
        {| te_tid := t; te_ev := InvEv (linsert v) |}
        (Ready s)
        (AtomicPending s t (linsert v))
  | step_linsert_res t s v l:
      (nodes s) l = None ->
      StepSPList
        {| te_tid := t; te_ev := ResEv (linsert v) l |}
        (AtomicPending s t (linsert v))
        (Ready (insert v l s))
  | step_setTS_inv t s ts l:
      t = owner ->
      StepSPList
        {| te_tid := t; te_ev := InvEv (lsetTS l ts) |}
        (Ready s)
        (AtomicPending s t (lsetTS l ts))
  | step_setTS_res t s ts l:
      StepSPList
        {| te_tid := t; te_ev := ResEv (lsetTS l ts) tt |}
        (AtomicPending s t (lsetTS l ts))
        (Ready (setTS l ts s))
  | step_getCounter_inv t s:
      StepSPList
        {| te_tid := t; te_ev := InvEv lgetCounter |}
        (Ready s)
        (AtomicPending s t lgetCounter)
  | step_getCounter_res t s:
      StepSPList
        {| te_tid := t; te_ev := ResEv lgetCounter (counter s) |}
        (AtomicPending s t lgetCounter)
        (Ready s)
  | step_tryRemove_inv t s l:
      nodes s l <> None ->
      StepSPList
        {| te_tid := t; te_ev := InvEv (ltryRemove l) |}
        (Ready s)
        (AtomicPending s t (ltryRemove l))
  | step_tryRemove_succ t s l:
      nodes s l <> None ->
      In l (order s) ->
      StepSPList
        {| te_tid := t; te_ev := ResEv (ltryRemove l) true |}
        (AtomicPending s t (ltryRemove l))
        (Ready (remove l s))
  | step_tryRemove_fail t s l:
      nodes s l <> None ->
      ~ In l (order s) ->
      StepSPList
        {| te_tid := t; te_ev := ResEv (ltryRemove l) false |}
        (AtomicPending s t (ltryRemove l))
        (Ready s).

  Variant ErrorSPList :
    @ThreadEvent ESPList -> SPListControl -> Prop :=
  | error_linsert_not_owner t s v e :
      t <> owner ->
      e = {| te_tid := t; te_ev := InvEv (linsert v) |} ->
      ErrorSPList e (Ready s)
  | error_setTS_not_owner t s l ts e :
      t <> owner ->
      e = {| te_tid := t; te_ev := InvEv (lsetTS l ts) |} ->
      ErrorSPList e (Ready s)
  | error_tryRemove_undefined t s l e :
      nodes s l = None ->
      e = {| te_tid := t; te_ev := InvEv (ltryRemove l) |} ->
      ErrorSPList e (Ready s)
  | error_setTS_undefined t s l ts e :
      nodes s l = None ->
      e = {| te_tid := t; te_ev := InvEv (lsetTS l ts) |} ->
      ErrorSPList e (Ready s).

  Definition VSPList : @LTS ESPList :=
  {|
    State := SPListControl;
    Step := StepSPList;
    Error := ErrorSPList
  |}.

  End Spec.

End SPListSpec.
