Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import TPSimulationSet.

Require Import examples.Common.ThreadDomain.
Require Import examples.TSStack.Shared.TimestampSpec.
Require Import examples.TSStack.Basic.ListPoolSpec.
Require Import examples.TSStack.WithElim.ListPoolElimSpec.
Require Import examples.TSStack.WithElim.TryStackAuxElimSpec.


(** Implementation of the TryStackAux layer with elimination
    (docs/plans/TSStackEliminationPlan.tex, Section 6.2).

    [push] and [startPop] are pass-throughs.  [trypop start] merges a
    [getTop start] result with the subsequent removal attempt, exposing
    the successful node only when [tryRemove] accepts it; an elimination
    candidate is removed exactly like a normal candidate. *)
Module TryStackAuxElimImpl.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import TPSimulationSet.TPSimulation.
  Import TimestampSpec.
  Import ListPoolSpec.
  Import ListPoolElimSpec.
  Import TryStackAuxElimSpec.
  Import (coercions, canonicals, notations) Sig.

  Open Scope prog_scope.

  Section Impl.
    Context {A : Type}.
    Context (D : ThreadDomain.t).

    Definition E : layer_interface :=
      @ListPoolElimLayer.L A D.

    Definition F : layer_interface :=
      @TryStackAuxElimLayer.L A D.

    Definition push_impl
        (v : A) (_actor : tid) : Prog (li_sig E) unit :=
      lpool_push v >= _ =>
      Ret tt.

    Definition startPop_impl (_actor : tid) : Prog (li_sig E) TS :=
      lpool_startPop >= ts =>
      Ret ts.

    Definition trypop_impl (start : TS)
        (_actor : tid) : Prog (li_sig E) (@TResult A) :=
      lpool_getTop start >= result =>
      match result with
      | YSuccNode v owner loc =>
          lpool_tryRemove owner loc >= removed =>
          Ret (if removed
               then TSuccNode v owner loc
               else TFail)
      | YSuccEmpty => Ret TSuccEmpty
      | YFail => Ret TFail
      end.

    Definition try_stack_aux_elim_impl :
        ModuleImpl (li_sig E) (li_sig F) :=
      fun op =>
        match op with
        | tsa_push v => push_impl v
        | tsa_startPop => startPop_impl
        | tsa_trypop start => trypop_impl start
        end.

  End Impl.

End TryStackAuxElimImpl.
