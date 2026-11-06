# Verification Plan: Timestamp over CAS

## Objective

Prove the implementation in `Timestamp.v` (Fig. 15 of `main-tr.pdf`) correct
with respect to the `(t, p)` specification of Appendix A.1 in
`TimestampSpec.v`.  The underlay is a single `ECASReg nat` register; the
paper's hardware `CAS` interface has only `cas` and `get`, so `set` is simply
never called.  The production theorem is

```coq
TimestampProof.MTimestamp :
  layer_implementation_simulation TimestampImpl.E TimestampImpl.F
```

with `MTimestampLinearizable := LISim2LILin MTimestamp`.

## Proof shape

Singleton-possibility proof in the style of `FAISet.v`.

* **Invariant** `I`: the abstract clock `t` equals the register value.
* **Thread-local assertions**: `Stamped t t1` (the actor's pending entry is
  `t1`) and `Observed n` (`n` is at most the register value; the register is
  monotone, so this is stable).
* **Guarantee** `G t`: register non-decreasing; other threads' pending
  entries and linearization tokens unchanged.  **Rely** `R t` is the
  corresponding view from the actor's side.
* **Linearization points**:
  * the abstract invocation linearizes at the response of the first `get`,
    so the pending entry records exactly `t1`;
  * a successful `cas t1 (t1+1)` linearizes the response `[t1, t1]`
    (register and clock both become `t1 + 1`);
  * in the two branches returning `[t1, n - 1]` for a later read `n`, the
    response is linearized at that read itself, inside the
    `singleton_vis_safe` step: there the register, hence the clock, is
    exactly `n`, and `t1 < n` gives `t1 <= n - 1`.  For the second read
    this makes the postcondition a conditional on `t1 =? n`.

## Response rule of the specification

`step_newTS_res` requires, besides `p[a] = l` and `l <= u`, the clock bounds
`u <= t` and `t <= u + 1` (stated last so that the hypothesis names from
`inversion` in the LPool proofs are unchanged).  In the paper's notation the
premise is `max(l, t - 1) <= u <= t`: a response closes its interval just
before the current clock, or at the clock by ticking it once.  Consequently
the clock advances by at most one per response, which is why the responses
returning `[t1, n - 1]` must be linearized at the read of `n` and not by a
later abstract-only step, where only `n <= t` is stable.

The LPool layers only invert `StepTimestamp` and use `start_newTS`,
`finish_newTS` and their lemmas, so they are unaffected by the extra premises.

## Structure of `TimestampProof.v`

The method triple is one proof whose skeleton is the sequence of
`singleton_vis_safe` / `singleton_ret_safe` steps, with
the possibility updates inline.  Only non-logical facts are separate lemmas:
stability of each assertion, rely/guarantee compatibility, absence of
underlay errors, and the shapes of the four CAS register steps
(`step_*_shape`).  Thread events carry dependent result arguments that
`injection` drops, so `cas_result` reads the boolean back explicitly.
