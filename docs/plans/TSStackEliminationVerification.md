# Elimination in the TS stack: verification status

Companion to `TSStackEliminationPlan.tex` (the plan). This note records what
was built, where the proofs depart from the plan, and what each new file
establishes. All files are variants next to the existing stack; no existing
file was modified.

## Files

| Layer | Spec | Implementation | Proof |
| --- | --- | --- | --- |
| ListPoolElim | `ListPoolElimSpec.v` | `ListPoolElim.v` | `ListPoolElimProof.v` |
| TryStackAuxElim | `TryStackAuxElimSpec.v` | `TryStackAuxElim.v` | `TryStackAuxElimProof.v` |
| DagStack (atomic pop) | `DagStackSpec.v` | `DagStack.v` | `DagStackHistory.v`, `DagStackProof.v` |
| TSStackElim | `TSStackSpec.v` (reused) | `TSStackElim.v` | `TSStackElimProof.v` |
| Top level | | | `TSStack_TopLevelElim.v`, `TSStack_TopLevelElimUnlink.v` |

`ListPoolElimSpec` reuses the node vocabulary (`LPNodeId`, `node_update`,
`lp_top`, ...) and the result type `YResult` of `ListPoolSpec`; files that
need both import `ListPoolSpec` first and `ListPoolElimSpec` after it, so the
elimination definitions shadow the old ones.

## Specifications (as frozen)

- **ListPoolElim.** State gains `lp_pop_starts : TMap.t LPNodeSet` and
  `lp_pop_ts : TMap.t TS`. `step_startPop_inv` records the completed
  vertices (`completed_set`) as the actor's start set and drops its token;
  `step_startPop_res ts` records the token. The two `getTop` invocation rules
  take the token argument and require `lp_pop_ts[actor] = Some start`;
  `error_getTop_no_session` fires otherwise. `step_getTop_elim_res` reports
  any vertex outside the start set (it overlaps the garbage rule, as planned).
- **TryStackAuxElim.** Same two maps plus the ghost `tsa_session_time`.
  `tsa_remove_node` now also closes the session and logs
  `(remover, session time, removal time)`; the empty response goes through
  `tsa_close_session`; the fail response (`tsa_clear_snapshot`) keeps the
  session. New rule `step_tsa_trypop_elim` (snapshot pending, `n` live and
  outside the start set); new error `error_tsa_trypop_no_session`.
- **DagStack.** `TryStackSpec` with `pop` instead of `trypop`, result
  `PopResult = PNode v owner loc | PEmpty`, and no fail rule.

## Implementations

As in the plan, except that the ListPool scan keeps `ForEach` (the plan's
fallback): the accumulator is `ElimScan = ScanOngoing scan | ScanEliminated v
owner loc`, and `scan_step_elim start` returns the accumulator unchanged once
a candidate has been eliminated, so the underlay trace is exactly the early
exit of the original algorithm. `DagStack.pop_impl` is
`tsa_startPop >= start => Do { retry_body start } Loop`.

## Proofs

### `DagStackHistory.v` (the history theory, Appendix A.4 generalized)

- Legality: the pop clause of `legal` is session-based. A committed pop of
  `n` by `β` at `p` needs `tsa_removals n = Some (β, σ, rt)` with
  `σ < gap p <= rt`; a speculative pop needs `tsa_session_time β = Some σ`
  and `σ < gap p`. Snapshots no longer occur in legality.
- `ghost_wf` gains `gw_session` (the start set is exactly the set of
  vertices completed before the session clock), `gw_session_time`,
  `gw_pop_ts` (a token belongs to an open session) and `gw_snap_session` (a
  snapshot belongs to a session started before it). Preservation lemmas
  exist for every TryStackAuxElim transformer, plus `tsa_drop_session` and
  `tsa_tick` (see the DagStack proof).
- Lemma A.1 (`fs_insertion`) takes the case hypothesis
  `lp_top (N \ g) E n \/ (live n /\ exists N0, Start[α] = N0 /\ ~ N0 n)` and
  concludes `σ_α < gap P <= t`. The snapshot case is the old `slot_exists`
  (its `st < gap Q` gives `σ < gap Q` through `gw_snap_session`); the
  elimination case (`slot_exists`, second half) places the pop at the very
  start of gap `r(n)+1` (`rank_under`) when `n` is completed, or at the end
  of the current gap when `n` is pending; in both cases the blocker set is
  empty. The `Section Slot` insertion construction is unchanged apart from
  the lower bound.
- Assumptions: `classic` only.

### `DagStackProof.v` (the atomic boundary)

- Plans have no failing set: `plan s H h` is legality, agreement with the
  canonical history on committed pops, and the lag of push placements.
  `rep_tokens` says: a thread with an open session holds
  `•(pop, Succ(v,n))` if the plan speculates its pop of `n` and `◦(pop)`
  otherwise. `popS` requires an open session, `◦(pop)` and a top live vertex
  of the possibility's own graph; `giveUpS` is gone, `specS` is the closure
  of `placeS` and `popS`, and `plans_reached` is the replay without the
  give-up suffix.
- Guarantees: `G_push_inv`, `G_push_ret` (unchanged), `G_start_inv`
  (concrete session opening with `◦(pop)` everywhere, then `specS`),
  `G_start_ret` (`specS`, concrete token record, `specS`), `G_snap`
  (requires the token, no token fact about the actor), `G_rmv` (filter on
  `•(pop, Succ(v,n))`, enabledness from the generalized Lemma A.1 in either
  case), `G_fail` (no filter), `G_emp` (invocation: filter on `◦(pop)` plus
  enabledness; response: `specS` after the clock advance).
- **Departure: the dead-session view.** The empty branch of `trypop` is two
  adjacent events, and the session is closed only at the response. Between
  them `I_pop` would be false (the actor's token is `•(pop, Empty)` while
  its session is still recorded). Instead of changing the TryStackAuxElim
  specification, the proof's view of the state, `payload`, drops the
  atomic-pending actor's session: `payload (TSAAtomicPending s β _) =
  tsa_drop_session β s`, and the response is `tsa_tick` of that view
  (`close_session_tick`). The `Emp` section proves `I` for the dropped
  view; the `Tick` section handles the response.
- Assertions: `Active` carries `NoSession` (established from the framework's
  invocation step, since a tokenless thread has no session; it is what
  keeps the `◦` token stable against other threads' speculation).
  `LoopInv α start = I ∧ contains ∧ P[α]=⊥ ∧ S[α]=⊥ ∧ pop_ts[α]=start` is
  the `provable_doloop` invariant; `PopMid`'s empty disjunct records the
  dead session; `PopPost` maps a fail back to `LoopInv`.
- Token stability: another thread's `specS` changes `obs`'s token only by
  placing `obs`'s pending push or by speculating a pop of `obs`'s open
  session (`◦(pop)` to `•(pop, Succ)`), so `alin_stable_core` requires
  `NoPending` and either `NoSession` or a token different from `◦(pop)`.
- Assumptions: `classic`, `Eq_rect_eq`, as for the old TryStack proof.

### `TSStackElimProof.v`

`TSStackProof.v` with the DagStack vocabulary, the fail branch and the
`provable_doloop` wrapper deleted (the pop method is one `provable_vis_safe`),
and `g_control_leave` dropped. Assumptions unchanged.

### `TryStackAuxElimProof.v`

Singleton proof as before. Sessions are related one way (`session_protocol`):
every open TSA session is an open ListPool session with the same start set
and token, because ListPoolElim never closes a session while TryStackAuxElim
closes it on the terminal results. After `getTop start` returns a node the
three ListPool rules are inverted and `TryRemoveReady` carries the disjunction
garbage / top of the snapshot / outside the start set; on a successful
`tryRemove` the second and third cases apply `step_tsa_trypop_succ` and
`step_tsa_trypop_elim`. The token premise of `trypop start` is discharged at
method entry through `error_tsa_trypop_no_session`. Assumptions as before.

### `ListPoolElimProof.v`

`ListPoolProof.v` (set-of-possibilities proof) with:

- `pool_shared_eq` extended by the two session maps, so start sets and
  tokens are uniform across branches (rectangularity).
- A new conjunct `session_represents` of `branch_represents`: for every
  open session there is a clock bound `c` such that the recorded token is
  `TSInterval c u` (or, while `startPop` is pending, `c` is the clock saved
  by the actor's `newTS`), and every member of the start set carries an
  interval with upper endpoint `< c`. This is Lemma 4.3 of the plan and the
  only place timestamps are compared.
- `pool_protocol` gains the token clauses for a pending `startPop` and the
  fact that an interval `getTop start` token matches the recorded session
  token; the first clause of `timestamp_pending_edges` admits a pending
  `newTS` of a `startPop`.
- Rely/guarantee: a `session_equiv` clause (other threads never change an
  observer's session view). **Departure:** `intervals_evolve` gained value
  persistence (`as_values` entries never change), needed because the
  eliminated node's value is carried as a concrete fact in `ElimReady`.
- The snapshot fork is generalized (`ac_fork_snapshot` with a predicate on
  the token); the whole getTop proof lives in `Section GetTop` with
  `Variable start : TS`.
- `startPop`: `startPop_method_triple` applies `step_startPop_inv` in every
  branch at the `newTS` invocation and `step_startPop_res` with the
  returned interval at its response.
- Scan: `provable_foreach` with `Inv := ElimFold`; the `ScanEliminated` body
  is `provable_ret_safe`; the nonempty row response splits on
  `timestamp_ltb start ts`, the new case being `getTop_row_elim_res_update`
  (derives `n ∉ Start[α]` by `u' < c <= u < l <= u'`); the exit commits
  through `ac_actor_slice` and an `ac_image` of `step_getTop_elim_res`
  (`getTop_elim_commit_update`).
- Entry: `GetTopEntry` has a third case, a token mismatch in every branch,
  discharged with `error_getTop_no_session`.
- Assumptions: those of `ListPoolProof` (`classic`, `Eq_rect_eq`,
  functional and propositional extensionality).

## Compositions and axioms

`TSStack_TopLevelElim.v` composes memories and CAS registers up to
`TSStackElim` (`MTSStack_linearizable`); `TSStack_TopLevelElimUnlink.v` does
the same over the unlinking lists. Both compile, and `Print Assumptions`
lists exactly the axioms of `TSStack_TopLevel.v`: `classic`, `Eq_rect_eq`,
`functional_extensionality_dep`, `propositional_extensionality`,
`dependent_unique_choice`, `relational_choice`. Intermediate compositions:
`TryStackAuxElimProof.MListPoolTryStackAuxElim`,
`DagStackProof.MListPoolDagStack`.
