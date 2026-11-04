Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import TPSimulationSet.

Require Import examples.Common.ThreadDomain.
Require Import examples.TSStack.TimestampSpec.
Require Import examples.TSStack.ListPoolSpec.
Require Import examples.TSStack.TryStackAuxElimSpec.
Require Import examples.TSStack.DagStackSpec.


(** Implementation of the DagStack layer
    (docs/plans/TSStackEliminationPlan.tex, Section 6.3).

    [push] forwards to TryStackAux.  [pop] opens a session with
    [startPop] and retries [trypop] with the session token until it
    returns a node or reports the graph empty.  This is the retry loop of
    the original TS stack with the start time taken once, before the
    loop. *)
Module DagStackImpl.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import TPSimulationSet.TPSimulation.
  Import TimestampSpec.
  Import TryStackAuxElimSpec.
  Import DagStackSpec.
  Import (coercions, canonicals, notations) Sig.

  Open Scope prog_scope.

  Section Impl.
    Context {A : Type}.
    Context (D : ThreadDomain.t).

    Definition E : layer_interface :=
      @TryStackAuxElimLayer.L A D.

    Definition F : layer_interface :=
      @DagStackLayer.L A D.

    Definition push_impl
        (v : A) (_actor : tid) : Prog (li_sig E) unit :=
      tsa_push v >= _ =>
      Ret tt.

    Definition retry_body (start : TS) :
        Prog (li_sig E) (unit + @PopResult A) :=
      tsa_trypop start >= result =>
      Ret (match result with
           | TSuccNode v owner loc => inr (PNode v owner loc)
           | TSuccEmpty => inr PEmpty
           | TFail => inl tt
           end).

    Definition pop_impl
        (_actor : tid) : Prog (li_sig E) (@PopResult A) :=
      tsa_startPop >= start =>
      Do { retry_body start } Loop.

    Definition dag_stack_impl :
        ModuleImpl (li_sig E) (li_sig F) :=
      fun op =>
        match op with
        | dag_push v => push_impl v
        | dag_pop => pop_impl
        end.

  End Impl.

End DagStackImpl.
