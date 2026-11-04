Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import TPSimulationSet.

Require Import examples.Common.Heap.
Require Import examples.Common.ThreadDomain.
Require Import examples.TSStack.TimestampSpec.
Require Import examples.TSStack.SPListSpec.
Require Import examples.TSStack.SPListArraySpec.
Require Import examples.TSStack.ListPoolSpec.
Require Import examples.TSStack.ListPoolElimSpec.
Require Import examples.TSStack.ListPool.


(** Implementation of the list-pool layer with elimination
    (docs/plans/TSStackEliminationPlan.tex, Section 6.1).

    [startPop] takes a fresh timestamp.  The scan of [getTop start] is the
    scan of [ListPoolImpl] with an early exit: a node whose timestamp is
    later than the start timestamp (in the strict interval order, with
    the unset timestamp [TSTop] later than everything) is returned at
    once.  The early exit is encoded by a flag in the fold accumulator,
    so that the remaining iterations perform no underlay call; the trace
    of underlay operations is the one of the original algorithm. *)
Module ListPoolElimImpl.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import TPSimulationSet.TPSimulation.
  Import TimestampSpec.
  Import SPListSpec.
  Import SPListArraySpec.
  Import ListPoolSpec.
  Import ListPoolElimSpec.
  Import ListPoolImpl.
  Import (coercions, canonicals, notations) Sig.
  Import (canonicals) Sig.Plus.

  Open Scope prog_scope.

  Section Impl.
    Context {A : Type}.
    Context (D : ThreadDomain.t).

    Definition EArray : layer_interface :=
      @SPListArrayLayer.L A D.

    Definition ETimestampLayer : layer_interface :=
      TimestampLayer.L.

    Definition E : layer_interface := EArray ⊗ₗ ETimestampLayer.

    Definition F : layer_interface :=
      @ListPoolElimLayer.L A D.

    (** The scan accumulator: the ordinary candidate/counter pair of
        [ListPoolImpl], or an elimination candidate after the early exit. *)
    Variant ElimScan : Type :=
    | ScanOngoing (scan : @ScanState A)
    | ScanEliminated (v : A) (owner : tid) (loc : Addr).

    Definition scan_step_elim (start : TS)
        (acc : ElimScan) (owner : tid) :
        Prog (li_sig E) ElimScan :=
      match acc with
      | ScanEliminated _ _ _ => Ret acc
      | ScanOngoing scan =>
          inl (array_getTop owner) >= result =>
          match result with
          | inl node =>
              let '(v, ts, loc) := node in
              Ret (if timestamp_ltb start ts
                   then ScanEliminated v owner loc
                   else ScanOngoing
                     (choose_candidate owner node (fst scan), snd scan))
          | inr count =>
              Ret (ScanOngoing (fst scan, Nat.add (snd scan) count))
          end
      end.

    Definition push_impl
        (v : A) (_actor : tid) : Prog (li_sig E) unit :=
      inl (array_insert v) >= loc =>
      inr newTS >= ts =>
      inl (array_setTS loc ts) >= _ =>
      Ret tt.

    Definition startPop_impl (_actor : tid) : Prog (li_sig E) TS :=
      inr newTS >= ts =>
      Ret ts.

    Definition getTop_impl (start : TS) (_actor : tid) :
        Prog (li_sig E) (@YResult A) :=
      inl array_resetIter >= _ =>
      (ForEach ThreadDomain.threads D
        From (ScanOngoing (None, O)) Using scan_step_elim start)
        p>= acc =>
      match acc with
      | ScanEliminated v owner loc => Ret (YSuccNode v owner loc)
      | ScanOngoing scan =>
          match fst scan with
          | Some candidate =>
              Ret (YSuccNode
                (candidate_value candidate)
                (candidate_owner candidate)
                (candidate_loc candidate))
          | None =>
              inl array_getCounter >= current_counter =>
              Ret (if Nat.eqb current_counter (snd scan)
                   then YSuccEmpty
                   else YFail)
          end
      end.

    Definition tryRemove_impl
        (owner : tid) (loc : Addr) (_actor : tid) :
        Prog (li_sig E) bool :=
      inl (array_tryRemove owner loc) >= removed =>
      Ret removed.

    Definition list_pool_elim_impl :
        ModuleImpl (li_sig E) (li_sig F) :=
      fun op =>
        match op with
        | lpool_push v => push_impl v
        | lpool_startPop => startPop_impl
        | lpool_getTop start => getTop_impl start
        | lpool_tryRemove owner loc => tryRemove_impl owner loc
        end.

  End Impl.

End ListPoolElimImpl.
