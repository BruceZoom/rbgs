Require Import Coq.Lists.List.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.Program.Equality.

Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import TPSimulationSet.

(** Compositional Linearizability (Definition 4.1, §4.3).

    This file mechanizes the trace-based correctness criterion of the paper
    directly on top of the thread-pool operational semantics already defined
    in [Semantics]: it introduces no new notion of step, it only assembles
    the existing [invstep]/[retstep]/[ustep]/[taustep]/[ts_error] relations
    into the trace semantics [[M]]_VE of §4.3, and compares it against the
    trace semantics of the identity implementation id_F, which plays the
    role of the atomic "copy-cat" specification.

    Undefined behavior (§4.3: "once a thread pool can error, any
    continuation is accepted") is modeled by an explicit, terminal trace
    marker [TErr] rather than by literally appending an arbitrary
    concrete tail. Appending an arbitrary tail directly into the generated
    trace set works for a single, non-composed object, but does not survive
    horizontal composition: the composed system could then "produce" a
    trace whose other-component-tagged tail is pure fabrication, unrelated
    to anything that component's own state ever did, breaking the trace
    containment used to relate the two components' [CompLin] hypotheses to
    the composed one. Recording instead that a run of [M] merely *reaches*
    a error at some point (with [TErr] a designator, not a wildcard) lets
    the generation relation ([trace_step]/[ImplTraces]) stay a precise,
    compositional description of what each component actually does; the
    "anything can happen afterwards" reading of undefined behavior is then
    pushed into the *comparison* against the specification only
    ([ImplTracesClosed]/[CompLin]), where it belongs: the specification
    side is compared up to "if it also errors at some prefix, that prefix
    licenses any continuation", while the implementation side is compared
    on the nose.

    [TErr] is tagged with the overlay operation [f : Sig.op F] whose thread
    was in flight at the moment of the error (mirroring [InvEv]/[ResEv],
    which are likewise tagged with the overlay operation they belong to).
    This is not just bookkeeping: it is exactly what lets horizontal
    composition ([CompLinHComp.v]) project a combined trace back
    onto its two components, since [f]'s tag (in the combined signature
    [Sig.Plus.omap F1 F2], either [inl _] or [inr _]) is the only way to
    tell, from the trace alone, which side actually errored — a bare,
    untagged [TErr] marker cannot be projected at all.

    This is intentionally independent from the speculative
    [Poss]/[AbstractConfig] machinery used by [TPSimulationSet] for the
    Threadpool Simulation (Definition 5.2); relating the two is
    [CompLinSound.v] (Lemma 5.3). *)
Module CompLin.
  Import Reg.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import Semantics.

  (* Traces only record overlay (F) invocation/response events, plus a
     terminal marker for undefined behavior, tagged with the overlay
     operation of the thread that errored; §4.3. [TErr _] is never followed
     by further items: [trace_step] only ever appends it as the very last
     element (see [TraceStepError] below), so a trace either has no [TErr]
     at all, or has exactly one, at the end. *)
  Variant TraceItem {F} : Type :=
  | TEvent (ev : @ThreadEvent F)
  | TErr (f : Sig.op F).
  Arguments TraceItem : clear implicits.

  Definition Trace {F} : Type := list (@TraceItem F).
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
       - once the current thread pool can error, the terminal [TErr] marker
         is appended, tagged with the overlay operation [f] of the
         offending thread: this designates undefined behavior at this
         exact point, without committing to (or fabricating) any specific
         concrete continuation. (Inlining [uerror]'s [Hfind]/[Herror]
         fields here, rather than using [uerror] itself as a premise, is
         what exposes [f] so it can be recorded in the trace.) *)
    Inductive trace_step : TraceConfig -> TraceConfig -> Prop :=
    | TraceStepInv s sigma c t f c'
        (Hstep : invstep M t f c c') :
        trace_step (mkTraceConfig s sigma c)
          (mkTraceConfig (s ++ (TEvent (Build_ThreadEvent t (InvEv f)) :: nil)) sigma c')
    | TraceStepRet s sigma c t f ret c'
        (Hstep : retstep t f ret c c') :
        trace_step (mkTraceConfig s sigma c)
          (mkTraceConfig (s ++ (TEvent (Build_ThreadEvent t (ResEv f ret)) :: nil)) sigma c')
    | TraceStepU s sigma c ev sigma' c'
        (Hstep : ustep ev sigma c sigma' c') :
        trace_step (mkTraceConfig s sigma c) (mkTraceConfig s sigma' c')
    | TraceStepTau s sigma c t c'
        (Hstep : taustep t c c') :
        trace_step (mkTraceConfig s sigma c) (mkTraceConfig s sigma c')
    | TraceStepError s sigma c f ev ts
        (Hfind : TMap.find (te_tid ev) c = Some ts)
        (Herror : ts_error f ev sigma ts) :
        trace_step (mkTraceConfig s sigma c) (mkTraceConfig (s ++ TErr f :: nil) sigma c).

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

  Section Closure.
    Context {F : Op.t}.
    Context {VF : @LTS F}.
    Context (N : ModuleImpl F F).

    (* The specification is compared up to undefined behavior: if [N] can
       reach a [TErr f] at some prefix [p], that licenses every trace
       extending [p] (in particular, every concrete continuation a
       matching implementation might really produce), not just the literal
       [p ++ TErr f :: nil] trace itself. *)
    Definition ImplTracesClosed (rho0 : State VF) (s : Trace F) : Prop :=
      ImplTraces N rho0 s \/
      exists p f tl, ImplTraces N rho0 (p ++ TErr f :: nil) /\ s = p ++ tl.
  End Closure.

  (* Definition 4.1 (Compositional Linearizability).
     M : VE ⇝ VF iff every trace M can produce over the library VE is also
     a trace the identity implementation can produce over VF, up to
     undefined behavior on the identity implementation's side. *)
  Definition CompLin {E F : Op.t} {VE : @LTS E} {VF : @LTS F}
      (M : ModuleImpl E F) (sigma0 : State VE) (rho0 : State VF) : Prop :=
    forall s : Trace F,
      ImplTraces M sigma0 s -> @ImplTracesClosed F VF idImpl rho0 s.

  Definition CompLinInterface (VE VF: TPSimulation.layer_interface) (M : ModuleImpl (TPSimulation.li_sig VE) (TPSimulation.li_sig VF)) : Prop :=
    CompLin M (TPSimulation.li_init VE) (TPSimulation.li_init VF).

  (* [M : VE ⇝ VF] : M is a compositionally linearizable implementation of
     the layer interface VF on top of the layer interface VE. [VE] is
     parsed at level 200 (like the right-hand side of a type cast) so that
     this rule factorizes with the built-in cast syntax [(t : T)] instead
     of shadowing it. *)
  Notation "M : VE ⇝ VF" := (CompLinInterface VE VF M)
    (at level 100, VE at level 200, VF at next level).

End CompLin.