Require Import Coq.Lists.List.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.Program.Equality.

Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.

(** Compositional Linearizability (Definition 4.1, §4.3).

    This file mechanizes the trace-based correctness criterion of the paper
    directly on top of the thread-pool operational semantics already defined
    in [Semantics]: it introduces no new notion of step, it only assembles
    the existing [invstep]/[retstep]/[ustep]/[taustep]/[uerror] relations
    into the trace semantics [[M]]_VE of §4.3, and compares it against the
    trace semantics of the identity implementation id_F, which plays the
    role of the atomic "copy-cat" specification.

    This is intentionally independent from the speculative
    [Poss]/[AbstractConfig] machinery used by [TPSimulationSet] for the
    Threadpool Simulation (Definition 5.2). Relating the two (Lemma 5.3:
    [cal M σ0 ρ0 <-> CompLin M σ0 ρ0]) is left for future work, matching the
    existing [(* TODO: soundness: linearizability *)] markers in
    [TPSimulation.v]/[TPSimulationSet.v]. *)
Module CompLin.
  Import Reg.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import Semantics.

  (* Traces only record overlay (F) invocation/response events; §4.3. *)
  Definition Trace {F} : Type := list (@ThreadEvent F).
  Arguments Trace : clear implicits.

  Section ImplTraceSemantics.
    Context {E F : Op.t}.
    Context {VE : @LTS E}.
    Context (M : ModuleImpl E F).

    (* A trace-generation configuration bundles the trace accumulated so
       far with the underlying concrete configuration (σ, T). This is kept
       as a dedicated record (rather than an anonymous pair) since this
       development's ambient categorical notations for [( _ , _ )] and
       [( _ , _ , .. )] are bound in scopes that shadow the plain pair
       constructor notation. *)
    Record TraceConfig : Type := mkTraceConfig {
      tc_trace : Trace F;
      tc_state : State VE;
      tc_pool : @ThreadPoolState E F;
    }.

    (* One step of the trace-generation relation ↠ (§4.3):
       - starting an operation (tp-inv) or finishing one (tp-ret) extends
         the trace with the corresponding overlay event;
       - a library step (tp-step/[ustep]) or a silent step (tp-tau/
         [taustep]) leaves the trace unchanged, since the trace only
         collects overlay events;
       - once the current thread pool can error, an arbitrary trace [t] may
         be appended: this is undefined behavior, so any continuation is
         accepted by the criterion. *)
    Inductive trace_step : TraceConfig -> TraceConfig -> Prop :=
    | TraceStepInv s sigma c t f c'
        (Hstep : invstep M t f c c') :
        trace_step (mkTraceConfig s sigma c)
          (mkTraceConfig (s ++ (Build_ThreadEvent t (InvEv f) :: nil)) sigma c')
    | TraceStepRet s sigma c t f ret c'
        (Hstep : retstep t f ret c c') :
        trace_step (mkTraceConfig s sigma c)
          (mkTraceConfig (s ++ (Build_ThreadEvent t (ResEv f ret) :: nil)) sigma c')
    | TraceStepU s sigma c ev sigma' c'
        (Hstep : ustep ev sigma c sigma' c') :
        trace_step (mkTraceConfig s sigma c) (mkTraceConfig s sigma' c')
    | TraceStepTau s sigma c t c'
        (Hstep : taustep t c c') :
        trace_step (mkTraceConfig s sigma c) (mkTraceConfig s sigma c')
    | TraceStepError s sigma c t ev
        (Herror : uerror ev sigma c) :
        trace_step (mkTraceConfig s sigma c) (mkTraceConfig (s ++ t) sigma c).

    Definition trace_steps := clos_refl_trans _ trace_step.

    (* [[M]]_VE : the set of traces generated from the initial configuration
       (σ0, emp); §4.3. *)
    Definition ImplTraces (sigma0 : State VE) (s : Trace F) : Prop :=
      exists sigma c,
        trace_steps (mkTraceConfig nil sigma0 (TMap.empty _))
          (mkTraceConfig s sigma c).
  End ImplTraceSemantics.

  Section Identity.
    Context {F : Op.t}.

    (* id_F : F → F, the "copy-cat" implementation used as the spec code
       against which linearizability is measured; §4.3. *)
    Definition idImpl : ModuleImpl F F :=
      fun f _ => Vis f (fun v => Ret v).
  End Identity.

  (* Definition 4.1 (Compositional Linearizability).
     M : VE { VF iff every trace M can produce over the library VE is also
     a trace the identity implementation can produce over VF. *)
  Definition CompLin {E F : Op.t} {VE : @LTS E} {VF : @LTS F}
      (M : ModuleImpl E F) (sigma0 : State VE) (rho0 : State VF) : Prop :=
    forall s : Trace F,
      ImplTraces M sigma0 s -> @ImplTraces F F VF idImpl rho0 s.

End CompLin.
