# Verification Plan: one-shot write-snapshot

## Objective and deliverables

Prove that the write-snapshot object over a thread-indexed family of
registers is linearizable with respect to the paper's concurrent
specification `ν_write_snapshot` (`docs/paper/main copy.pdf`, Sections 2
and 4; the proof there is out of date).  The decomposition is

    WriteSnapshot ◁ ⊗_{α ∈ Υ} Reg'_α        (Reg' at type option A)

Status (2026-10-16): **done**.  `WriteSnapshotProof.MWriteSnapshot` is a
`layer_implementation_simulation E F` and
`MWriteSnapshotLinearizable` the derived linearizability result; both
depend only on `classic` and `Eqdep.Eq_rect_eq.eq_rect_eq`.

Files:

- `examples/WriteSnapshot/WriteSnapshotSpec.v`: the write-snapshot
  specification and the layer `WriteSnapshotLayer.L D`.
- `examples/WriteSnapshot/WriteSnapshot.v`: the underlay family
  `WriteSnapshotImpl.E` (the existing `Reg'Spec.VReg` at `option A`,
  packaged with `IndexedFamilySpec`) and the implementation
  `WriteSnapshotImpl.ws_impl` (Figure 1 of the paper).  No new underlay
  specification is introduced.
- `examples/WriteSnapshot/WriteSnapshotProof.v`: the layer proof in the
  set-of-possibilities logic (`RGILogicSet`), in the style of `CCAS.v`.

## Modelling decisions

1. **`OMem` is the existing race-free register.**  The paper's one-shot
   register is `Reg'Spec.VReg` at type `option A` (`None` is ⊥), one per
   thread via `IndexedFamilySpec`; `get` is `read` and `set (Some v)` is
   `write(v)`.  The register is not one-shot.  The one-shot discipline is
   the program's (it writes only the actor's own cell, once per call)
   together with decision 2.  The register is race-free (`NoError`), which
   is sound because only the owner ever writes a cell.  The paper's
   "poisoned" value ∅ of `omstate` is unreachable and is not modelled.
2. **Interval-sequential specification.**  `ν_write_snapshot` places the
   invocation (which adds `v` to `snpstate`) and the response (which reads
   `snpstate`) at different points, so `VWriteSnapshot` is a plain LTS, not
   a `VAE` object.  The state is `TMap.t A` (thread ↦ value written):
   its range is `snpstate`, its domain records who has invoked.
   The paper's one-shot clause `α ∉ s'` (no trace has two invocations by
   one thread) becomes the error `error_ws_double_inv`: a second
   invocation by a thread is client misuse, the framework's usual
   convention (compare the undefined-address errors of `MemSpec`).  The
   `step_ws_inv` guard `TMap.find t s = None` is kept so that the step and
   the error never coexist.  In the proof, the second call is discharged
   through `APError` at the invocation, so the method body may assume its
   own cell is `None`.
3. **Result type.**  The paper returns an element of `2^Val`.  The Coq
   arity is `list A`, and `step_ws_res` accepts any list whose members are
   exactly the values in the state (`ws_snapshot`).  Order and multiplicity
   are unconstrained, so the implementation is free to return its
   `ListSet` set.
4. **Thread domain.**  The implementation indexes the family with the
   actor, which is a family error for an actor outside `D`.  As in
   `TSStackSpec`, the specification raises `error_ws_actor_outside` at such
   an invocation.  These two are the only errors.
5. **Decidable equality.**  `new ≠ old` needs decidable equality on `A`;
   it is a section hypothesis `A_eq_dec` of the implementation only.
6. **⊥ is never collected.**  Figure 1 adds every read, ⊥ included, to
   `new` and the proof returns `new \ {⊥}`.  The implementation skips reads
   of `None`, so `new` and `old` are value sets throughout and the return
   is `new` itself.
7. **Loop shapes.**  The scan over `Υ` is `ForEach ThreadDomain.threads D`
   (as in `SPListArray.getCounter_impl`); the outer `while (new ≠ old)` is
   `From (new, old) Do { ... } Loop`, testing the pair before each scan.

## Dictionary

| Paper | Coq |
| --- | --- |
| `OMem`, `read`, `write(v)` | `Reg'Spec.EReg (option A)`, `get`, `set (Some v)` |
| `omstate(s)` | the `option A` state of `Reg'Spec.VReg` |
| `⊗_{α} OMem_α`, `M[α].read()`, `M[α].write(v)` | `WriteSnapshotImpl.E`, `cell_read α`, `cell_write α v` |
| `WriteSnapshot`, `write_snapshot(v)` | `EWriteSnapshot`, `write_snapshot v` |
| `snpstate(s)` | `ws_value s` (range of the `TMap`) |
| `α ∉ s'` | `error_ws_double_inv` (and the guard of `step_ws_inv`) |
| `α : V` with `V = snpstate(s')` | `step_ws_res` with `ws_snapshot s l` |
| `new`, `old` | the pair state of the `Loop` in `write_snapshot_impl` |

## Proof architecture

The response of a `write_snapshot` is linearized in the past (at the end
of the paper's prefix `p`), which the possibility model cannot do by
stepping a single abstract state.  The proof therefore keeps a *set* of
possibilities and speculates:

- **Product invariant.**  Every possibility carries the same abstract
  state `ρc`, which mirrors the cells (`inv_cells`), and the configuration
  is the cartesian product of the per-thread choices `proj s t`, up to the
  representation of the linearization maps (`inv_closed`).  Thread
  choices are `{ls_inv}` before the write is linearized,
  `{ls_lini} ∪ {ls_linr l | l ≈ S}` for every snapshot `S` taken since the
  write (`inv_lini`, the eager branching), and `{ls_linr l}` after
  selection.  The product is what makes one thread's selection harmless
  to the branches of the others (`sel_proj_keep`).
- **`G_write`** (`write_res_update`): at the response of the cell write,
  every possibility takes the abstract invocation, and every pending
  thread (the writer included) gets one branch per list representing the
  new snapshot.  The new configuration is the image `write_image`, i.e.
  the closure under response chains (`resp_chain`), so reachability is by
  construction and product closure is rebuilt from the projections by
  `build_base`/`build_chain`.
- **`G_snapshot`** (`select_update`): at the loop exit the writer keeps
  exactly the possibilities in which it answered the collected set
  (`ac_restrict`).  The branch exists because the frozen snapshot of the
  loop invariant (below) equals the collected set.
- **Loop invariants.**  The paper's `I_o[i, old, p]` and `I_n[i, new, p]`
  become `LoopInv` and `ScanInv`.  The prefix `p` is a frozen abstract
  state `ρp` with `Frozen α v ρp`: all of `α`'s branches for `ρp` exist and
  the cells of `ρp` are written.  It is frozen at the start of every scan
  (`freeze`, no abstract update: the current `ρc` qualifies by
  `inv_lini`), `old ⊆ ρp` holds because every collected value is in the
  cells, and `ρp ⊆ new` is accumulated cell by cell during the scan.  No
  `max{p, q}` argument is needed, because a freeze always picks the
  current state.
- **Errors.**  A second call by the same thread, or a call from outside
  `D`, makes the abstract configuration erroneous at the invocation
  (`ginv_P` case-splits on it); the method precondition is
  `Pgood ∨ (I ∧ ErrW)`, and `ErrW` is kept stable by the guarantee clause
  `gc_err`.
- **Rely/guarantee.**  `G actor` says: other threads' choices are kept
  (`ov_keep`), new choices of others are only branches for a pending
  `ls_lini` (`ov_new`), other threads' cells are unchanged, cells are
  monotone, and the actor preserves its own error witness.  `R t` is the
  union of the other threads' guarantees.

## Departures from the paper's outline (Section 4)

1. The paper linearizes the response once, at the end; here the response
   is speculatively linearized at every snapshot and selected at the end.
2. The paper's `I` ("the order of writes equals the order of
   `write_snapshot` in the linearization") is replaced by the product
   invariant above; no linearization order is kept, only snapshots.
3. The outline's program has two initial scans before the `while`; the
   proof follows Figure 1, so `LoopInv` has an extra disjunct for the
   first iteration (`old = ∅`, `v ∈ new`), where the loop test is false.

## Validation

```text
make examples/WriteSnapshot/WriteSnapshotProof.vo
git diff --check
rg -n "Admitted|admit|Axiom" examples/WriteSnapshot/*.v
```

`Print Assumptions MWriteSnapshot` lists `classic` and
`Eqdep.Eq_rect_eq.eq_rect_eq` only.
