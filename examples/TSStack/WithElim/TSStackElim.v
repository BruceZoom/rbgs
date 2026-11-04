Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import TPSimulationSet.

Require Import examples.Common.ThreadDomain.
Require Import examples.Stacks.StackSpec.
Require Import examples.TSStack.WithElim.DagStackSpec.
Require Import examples.TSStack.Basic.TSStackSpec.


(** Implementation of the stack with elimination over DagStack
    (docs/plans/TSStackEliminationPlan.tex, Section 6.4).

    Both operations are pass-throughs: the retry loop of [TSStack.v] has
    moved into the DagStack layer.  Only the DAG-to-list step remains. *)
Module TSStackElimImpl.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import TPSimulationSet.TPSimulation.
  Import DagStackSpec.
  Import TSStackSpec.
  Import (coercions, canonicals, notations) Sig.

  Open Scope prog_scope.

  Section Impl.
    Context {A : Type}.
    Context (D : ThreadDomain.t).

    Definition E : layer_interface :=
      @DagStackLayer.L A D.

    Definition F : layer_interface :=
      @TSStackLayer.L A D.

    Definition push_impl
        (v : A) (_actor : tid) : Prog (li_sig E) unit :=
      dag_push v >= _ =>
      Ret tt.

    Definition pop_impl
        (_actor : tid) : Prog (li_sig E) (option A) :=
      dag_pop >= result =>
      Ret (match result with
           | PNode v _ _ => Some v
           | PEmpty => None
           end).

    Definition ts_stack_elim_impl :
        ModuleImpl (li_sig E) (li_sig F) :=
      fun op =>
        match op with
        | StackSpec.push v => push_impl v
        | StackSpec.pop => pop_impl
        end.

  End Impl.

End TSStackElimImpl.
