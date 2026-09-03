Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import TPSimulationSet.

Require Import examples.Common.ThreadDomain.
Require Import examples.TSStack.ListPoolSpec.
Require Import examples.TSStack.TryStackAuxSpec.


(** Implementation of the TryStackAux layer from Appendix A.3.

    [push] is inherited from ListPool.  [trypop] merges a [getTop] result
    with the subsequent removal attempt, exposing the successful node only
    when [tryRemove] accepts it. *)
Module TryStackAuxImpl.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import TPSimulationSet.TPSimulation.
  Import ListPoolSpec.
  Import TryStackAuxSpec.
  Import (coercions, canonicals, notations) Sig.

  Open Scope prog_scope.

  Section Impl.
    Context {A : Type}.
    Context (D : ThreadDomain.t).

    Definition E : layer_interface :=
      @ListPoolLayer.L A D.

    Definition F : layer_interface :=
      @TryStackAuxLayer.L A D.

    Definition push_impl
        (v : A) (_actor : tid) : Prog (li_sig E) unit :=
      lpool_push v >= _ =>
      Ret tt.

    Definition trypop_impl
        (_actor : tid) : Prog (li_sig E) (@TResult A) :=
      lpool_getTop >= result =>
      match result with
      | YSuccNode v owner loc =>
          lpool_tryRemove owner loc >= removed =>
          Ret (if removed
               then TSuccNode v owner loc
               else TFail)
      | YSuccEmpty => Ret TSuccEmpty
      | YFail => Ret TFail
      end.

    Definition try_stack_aux_impl :
        ModuleImpl (li_sig E) (li_sig F) :=
      fun op =>
        match op with
        | tsa_push v => push_impl v
        | tsa_trypop => trypop_impl
        end.

  End Impl.

End TryStackAuxImpl.
