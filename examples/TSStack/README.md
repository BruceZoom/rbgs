# The timestamped stack

Verified layer stack for the TS stack (Dodds, Haas, Kirsch), organized as
one shared base, one basic stack, two optional features, and the top-level
compositions. Every file imports with its full path
(`examples.TSStack.<Dir>.<File>`), so basenames stay unique across
directories.

| Directory | Contents |
| --- | --- |
| `Shared/` | Layers used unchanged by every composition: `Timestamp*` (interval timestamps over a CAS counter), `NodeMem*` (node memory over five plain memories), `SPList*` (one single-producer list over node memory and a head register), `SPListFamily*` (one list per thread), `SPListArray*` (the array interface the pools use), `ProgIterator.v` (the `ForEach` iterator). |
| `Basic/` | The TS stack without elimination: `ListPool*` (push/getTop/tryRemove over the array and the timestamp, set-of-possibilities proof), `TryStackAux*` (singleton proof merging getTop and tryRemove), `TryStack*` (the atomic boundary, `TryStackHistory.v` is Appendix A.4's history theory), `TSStack*` (the retry loop and the stack specification). |
| `WithUnlink/` | Feature: physical unlinking of removed nodes. `NodeMemUnlink*`, `SPListGhostSpec.v` (ghost-log specification), `SPListUnlink*`, `SPListUnlinkFamily.v`. Replaces the corresponding `Shared/` layers below the array. |
| `WithElim/` | Feature: elimination of concurrent push/pop pairs. `ListPoolElim*`, `TryStackAuxElim*` (start sets, sessions), `DagStack*` (the atomic boundary moves to `pop`; owns `startPop` and the retry loop), `TSStackElim*`. Reuses `Basic/TSStackSpec.v`. Replaces the `Basic/` layers above the array. |
| `TopLevel/` | The compositions, each ending in `MTSStack_linearizable` with a `Print Assumptions`. |

## Compositions

| File | Lists | Stack |
| --- | --- | --- |
| `TopLevel/TSStack_TopLevel.v` | `Shared/` | `Basic/` |
| `TopLevel/TSStack_TopLevelUnlink.v` | `WithUnlink/` | `Basic/` |
| `TopLevel/TSStack_TopLevelElimUnlink.v` | `WithUnlink/` | `WithElim/` |

All three list the same axioms: `classic`, `Eq_rect_eq`,
`functional_extensionality_dep`, `propositional_extensionality`,
`dependent_unique_choice`, `relational_choice`.

## Plans and status

Per-layer plans and departures are in `docs/plans/` (`TimestampVerificationPlan.md`,
`NodeMemVerificationPlan.md`, `SPListArrayVerificationPlan.md`,
`SPListUnlinkVerificationPlan.md`, `ListPoolVerificationPlan.md`,
`TryStackAuxVerificationPlan.md`, `TryStackVerificationPlan.md`,
`TSStackVerificationPlan.md`, `TSStackEliminationPlan.tex`,
`TSStackEliminationVerification.md`). `examples/Stacks/TryStack.v` is an
unrelated file with the same basename as `Basic/TryStack.v`.
