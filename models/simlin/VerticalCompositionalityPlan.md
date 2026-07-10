# Proof Plan: Vertical Compositionality of `CompLin` (Lemma 4.3)

Target: `CompLinVComp.v`, module `CompLinVComp.VComp`, lemma `CompLin_vcomp`
(currently `Admitted`):

```coq
Lemma CompLin_vcomp
    {E F G : Op.t}
    {VE : @LTS E} {VF : @LTS F} {VG : @LTS G}
    (M1 : ModuleImpl E F) (M2 : ModuleImpl F G)
    (sigma0 : State VE) (rho0 : State VF) (tau0 : State VG) :
  CompLin M1 sigma0 rho0 ->
  CompLin M2 rho0 tau0 ->
  CompLin (M1 ▶ M2) sigma0 tau0.
```

Scope decision: this proof works **directly on the trace semantics of
`CompLin.v`** (`ImplTraces`/`ImplTracesClosed`/`CompLin`), independent of the
`TPSimulationSet`/`AbstractConfig` machinery in `Compositionality.v`. That
file already contains a complete, ~950-line vertical-compositionality proof
for the older, simulation-based `TPSimulation` notion (`VCompTPSim`), plus an
unfinished port to the Set-based `AbstractConfig` version
(`VCompTPSimSet.vcompSim`, currently `Admitted`). We deliberately do **not**
build on that file: it proves compositionality of a different (stronger,
simulation-witnessed) correctness notion, and bridging it back down to
`CompLin`-level hypotheses would additionally require the unproven
"completeness" direction of Lemma 5.3 (`CompLin ⟹ cal`). The plan below
re-derives everything needed directly against `CompLin`, from scratch.

## Relation to LHL (`ehatti/LHL`)

The user pointed at [LHL](https://github.com/ehatti/LHL), which proves
vertical compositionality of linearizability by first establishing an
*observational refinement* principle and composing it with associativity of
layering. Reading `Core/{Specs,Linearizability,VCompFacts,RefinesFacts,LinFacts}.v`
confirms this and gives a direct template for our proof.

### LHL's decomposition

LHL's `Spec T E` is an arbitrary (thread-locally well-formed) labeled
transition system. `overObj (spec :> impl) : Spec T F` is the object built by
running `impl` over `spec` and hiding underlay events — critically, it has
the *same type* as any hand-written spec, so it can be recursively fed into
another `overObj`. Their vertical-compositionality theorem `vcomp_lin` is a
short proof built from four independent facts:

| LHL lemma | Role |
|---|---|
| `layerRefines_trans` / `specRefines_trans` | trivial transitivity of trace inclusion |
| `mkLayer_monotonic` | `overObj(_ :> impl)` is monotonic in its underlying spec w.r.t. trace refinement |
| `layerRefines_VComp_assoc` / `_inv` | `overObj(spec :> impl\|>impl') ≡ overObj(overObj(spec:>impl) :> impl')` (the hard part — described in their own comments as the trickiest proof in the file, needing explicit `assoc_states`/`assoc_traces` witnesses to realign two independently-generated traces) |
| `eutt_layerRefines` + `idImpl_is_identity_l` | the copy-cat implementation is a `\|>`-identity up to weak bisimulation |

These combine into `lin_obs_ref`: *if the bottom layer linearizes to spec
`VF`, then any client stacked on the concrete bottom layer observationally
refines the same client stacked on the abstract `VF`*. `vcomp_lin` itself is
then: `assoc_inv`, then `lin_obs_ref` (using the first linearizability
hypothesis), then the second hypothesis, chained by transitivity.

### How this maps onto our development, and where it helps

Our `LTS` record (`Step`/`Error` as bare relations, no proof obligation) is
exactly as unconstrained as LHL's `Spec`, so the same trick — packaging a
"composed object" as a first-class value of the same type as a primitive
library — transplants directly. Concretely:

- LHL's `overObj (spec :> impl)` ↦ our new derived object `compLTS VE M1 :
  @LTS F` (defined below). Building this was the one design question left
  open in the earlier planning pass, and LHL's construction (visible event +
  hidden-underlay-closure, packaged as an ordinary transition system) is
  exactly what resolved it.
- LHL's `mkLayer_monotonic` ↦ our `ImplTraces_lib_mono`: a *generic*
  precongruence lemma (holds for **any** `ModuleImpl E F` and any two
  `@LTS E` values related by trace-refinement) — this is the real content of
  "observational refinement" and is the piece our codebase was missing
  entirely; nothing like it exists yet even for horizontal composition.
- LHL's `layerRefines_VComp_assoc[_inv]` ↦ our `vcomp_decompose`: the
  hardest lemma either way, in both developments. LHL needs bespoke
  `assoc_states`/`assoc_traces` realignment witnesses because their traces
  are untyped lists; our `CompLinHComp.v` already had to solve an analogous
  "realign an interleaved trace against two independently-stepping
  components" problem for horizontal composition (see
  `trace_steps_single_growth_split`, `hpools`), so we reuse that
  proof *technique* (not code) via a fresh three-way pool invariant
  `pools_vcomp`/`thread_vcomp`, playing the role of LHL's realignment
  witnesses.
- LHL's `eutt_layerRefines`/`idImpl_is_identity_l` step ↦ **not needed as a
  separate lemma** in our setting. Because our `compLTS` is defined by
  *literally unfolding* `M1`'s own `trace_step` relation (rather than via a
  general coalgebraic `overObj` requiring a separate identity-up-to-weak-
  bisimulation argument), the fact that "the copy-cat over `compLTS` is
  M1's own semantics" is provable as a direct, low-risk unfolding lemma
  (`compLTS_id_correct`) instead of a coinductive bisimulation proof. This
  is a simplification LHL's more general `Spec`/`Prog` setup doesn't get for
  free, but our closer coupling between `ModuleImpl` and `trace_step` does.

So LHL's role in this plan is less "supplies a lemma we import" and more
"supplies the right *shape* of decomposition" — in particular, it told us
(a) that a derived/composed spec object of the same type as a primitive one
is the right abstraction to reach for, (b) that monotonicity-in-the-
underlying-library needs to be proved as its own generic, reusable lemma
rather than inlined into the final proof, and (c) exactly which four facts
compose into the final theorem, which lets us budget effort (the
associativity/decompose lemma is the one genuinely hard piece; everything
else is comparatively mechanical).

## New object: `compLTS`

```coq
Definition compLTS {E F} (VE : @LTS E) (M : ModuleImpl E F) : @LTS F :=
  {| State := State VE * ThreadPoolState E F;
     Step  := compStep VE M;
     Error := compError VE M |}.
```

- `compStep VE M ev X Y` := some `silent_steps` (a `trace_step` closure
  restricted to the `TraceStepU`/`TraceStepTau` constructors, i.e. the ones
  that don't grow the trace) from `X` to some `X'`, followed by exactly one
  `trace_step` from `X'` producing `TEvent ev` (i.e. exactly a
  `TraceStepInv`/`TraceStepRet`). Reads as "one visible F-event, with silent
  VE-closure folded in."
- `compError VE M (t, InvEv op) X` := after `silent_steps` to some `X'` with
  thread `t` idle, immediately invoking `op` (matching `invstep`'s effect)
  leads via **one** further `trace_step` straight to `TErr op` — matching
  the one-shot-oracle shape `Error` has everywhere else in this development
  (`ts_error` is always a direct, one-step check, never a reachability
  search).

## Lemma roadmap

1. **`compLTS_id_correct`** (linchpin):
   `ImplTraces (idImpl : ModuleImpl F F) (VE := compLTS VE M) (sigma0, ∅) =
   ImplTraces M sigma0`
   — running the copy-cat over the derived object literally *is* M's own
   trace semantics. Proved by unfolding `compStep`/`compError` directly
   against `trace_step`; no induction subtlety, just definitional
   correspondence. Low risk — good first target to validate the `compLTS`
   design before investing in the harder lemmas.

2. **`ImplTraces_lib_mono`** (generic monotonicity / observational
   refinement):
   ```coq
   (forall s, ImplTraces idImpl sigma1 s -> ImplTracesClosed idImpl sigma2 s) ->
   forall s, ImplTraces M sigma1 s -> ImplTracesClosed M sigma2 s.
   ```
   for any `M : ModuleImpl E F`, `sigma1 : State VE1`, `sigma2 : State VE2`
   (same `E`). Says `ImplTraces _` is a precongruence w.r.t. swapping the
   underlying library for a trace-refining one. Proof: replay VE1's own
   `Step`-call sequence (embedded in `ustep` during M's run) as an
   `idImpl`-over-VE1 run, invoke the hypothesis to get a matching
   (or earlier-erroring) `idImpl`-over-VE2 run, and feed VE2's responses
   back into re-running M's fixed thread continuations — the same
   shadow-replay technique `CompLinSound.v` already uses (Layer 1/Layer 2),
   minus any Poss/AbstractConfig speculation, since there is nothing
   nondeterministic to track at this level. Largest self-contained piece.

3. **`pools_vcomp` / `thread_vcomp`** (fresh three-way pool-splitting
   invariant, built directly against `ThreadPoolState`, no reuse of
   `Compositionality.v`): relates a composite `ThreadState E G` entry
   (running `substProg t M1 (M2 g t)`-shaped programs) to its shadow
   `ThreadState F G` entry (as if M2 ran directly over `compLTS`) and M1's
   own bookkeeping `ThreadState E F` entry inside `compLTS`'s pool
   component. Plays the role `hpools`/`ts_left` play in `CompLinHComp.v`,
   for stacking instead of tensor.

4. **`vcomp_decompose`** (the hard associativity theorem):
   ```coq
   ImplTraces (M1 ▶ M2) sigma0 s ->
   ImplTraces (VE := compLTS VE M1) M2 (sigma0, ∅) s   (* up to the usual closure *)
   ```
   By induction on `trace_steps (M1▶M2) ...`, using `pools_vcomp` to track
   the correspondence and `substProgVis`/`bindSubstProgVis`/
   `bindSubstProgRet` unfolding equations to identify exactly when a
   composite micro-step crosses an F-level invocation/return boundary.
   Same difficulty tier as `CompLinHComp.hcomp_decompose`, adapted to
   vertical stacking. This is the proof's centerpiece, and the direct
   counterpart of LHL's `layerRefines_VComp_assoc`.

5. **Assembly — `CompLin_vcomp`**: chain
   `ImplTraces (M1▶M2) sigma0` --(4)--> `ImplTraces M2 (compLTS-initial)`
   --(2, fed by `CompLin M1` rewritten through 1)--> `ImplTracesClosed M2 rho0`
   --(hypothesis `CompLin M2 rho0 tau0`)--> `ImplTracesClosed idImpl tau0`,
   using a small `ImplTracesClosed`-transitivity helper (same shape as
   `CompLinSound.trace_snoc_prefix`, reusable since it lives in
   `CompLinSound.v`, not `Compositionality.v`).

## Suggested order of attack

1. `compLTS` + `compLTS_id_correct` — cheapest, validates the design.
2. `ImplTraces_lib_mono` — self-contained, single signature `E`, no stacking.
3. `pools_vcomp`/`thread_vcomp` + `vcomp_decompose` together (3 only exists
   to serve 4).
4. `CompLin_vcomp` assembly — should be short given 1–4 (mirrors how short
   LHL's own `vcomp_lin` is once its four supporting facts are in place).
