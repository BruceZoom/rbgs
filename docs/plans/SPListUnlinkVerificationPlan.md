# SPListUnlink: verification of the unlinking single-producer list

Status (2026-10-26): done. `examples/TSStack/SPListUnlinkProof.v` and
`examples/TSStack/NodeMemUnlinkProof.v` are closed, and
`examples/TSStack/TSStack_TopLevelUnlink.v` composes a timestamped stack
whose per-owner lists physically unlink taken nodes, down to plain
memories and CAS registers, with the same axioms as `TSStack_TopLevel.v`.

## The object

`SPListUnlink.v` is `SPList.v` plus the cleanup of the original TS stack
(Dodds, Haas, Kirsch, POPL 2015, Listing 2):

- `insert` walks from the register's pointer over taken nodes and
  allocates the new node with the first node it did not skip as
  successor (the original publishes first and rewrites afterwards; that
  rewrite races with the taker's rewrite, which is an error in our owner
  memory, so the walk is done before allocation).
- `getTop` keeps its traversal and read order; after finding the first
  untaken node it CASes the register down to it, keeping the counter
  (the original does this in `remove` with the `oldTop` returned by
  `getYoungest`; our interfaces carry only owner and address upwards).
- `tryRemove` walks from the taken node's successor over taken nodes and
  rewrites the taken node's successor to the result. The rewrite is a
  CAS from the successor value read after the take (`nmcasNext`), not
  the original's plain store: only the taker writes that cell so the CAS
  cannot fail, and a CAS has no racy-write error in `NodeMemUnlinkSpec`,
  so the proof needs no argument about who took which node. The
  original's write to the previous top's successor is not ported (two
  removers can race on it).

The overlay is literally `SPListImpl.F`, so SPListFamily, SPListArray,
ListPool, TryStackAux, TryStack and TSStack are reused verbatim.

## Why a ghost log

The old representation invariant followed the immutable chain from the
top. With unlinking, successors change and taken nodes drop out of the
chain, so the chain no longer records the insertion order, and that
order is exactly what makes "every node between `x` and its successor is
taken" a stable statement. Two formulations without it were tried and
rejected:

- Log-free, chain-based facts ("the live nodes reachable from the cursor
  are exactly the live saved nodes"): stable, but acyclicity of the
  successor pointers after a `casNext` cannot be shown from them, since
  a shortcut can move a pointer to a node that has since been dropped
  from every chain the proof knows about.
- An existential log with "every valid log stays valid" as guarantee:
  false, because "fake" logs that order unrelated taken nodes differently
  are valid before a `casNext` and invalid after it; and a fixed log held
  by one thread is useless for another thread's obligations.

So the proof is against `SPListGhostSpec`, which is `SPListSpec` with the
insertion log (newest first) in the state, extended by the response of
`linsert` and untouched by every other event. `CompLinProj` (new, in
`models/simlin`) erases the log: a step-and-error-preserving projection of
specification states lifts to compositional linearizability of the same
implementation, so `MSPListUnlinkLinearizable` is a proof against the
unchanged `SPListSpec` for the real implementation. The projection lemma
is about the copy-cat implementation's traces only; the object proof
stays in the program logic.

## The invariant

`valid h top log` := `NoDup log` and `skips h log top` and
`links_ok h log`, where `skips h xs p` says `p` points into `xs` after a
prefix of taken nodes (or past the end when all of `xs` is taken) and
`links_ok` says every node's successor skips into the suffix after it.
`represents` adds `counter s = count`, `length log = count`,
`nodes s = abstract_nodes h log`, `order s = live_order h log`.

Taken flags only flip to true, so `skips` facts are stable; the log only
grows at the front, so facts about a suffix are stable. The per-thread
facts are:

- `SkipsLog p` (owner, insert walk), `SkipsAfter l p` (taker, tryRemove
  walk and successor read; also the scanner's remembered successor);
- `ScanCore t count saved logS prefix suffix p`: the snapshot `saved`
  over a suffix `logS` of the log of the recorded length, a dead prefix,
  a cursor skipping into the rest, `saved` a subsequence of `logS`
  containing every node live now;
- `DoneData count l`: the data the final CAS needs. If the CAS succeeds
  the counter is unchanged, so the log is exactly `logS` and the node's
  prefix is dead, which gives `skips h log (Some l)`.

The guarantee replaces `cas_evol` by: other threads keep the counter, and
the log of the new state is `extra ++` the old log with `extra = nil` for
non-owners. Successors are unconstrained in `node_evol`; their structure
is carried by `valid` on both sides.

## Facade changes

`offslot_agree` and `slot_agree` include equality of the logs. Twins are
built from the same possibility so they share the log, and replay keeps
it (`control_agree` on ghost states is control agreement plus log
equality). Payload determination from the concrete state alone is gone;
`source_I_payload_determined` takes log equality as a premise. The
"valid or error" split of each method can no longer assume all
possibilities agree on `nodes`; it is done classically
(`defined_everywhere_or_undefined_somewhere`), which is enough because
the error branch only needs one possibility.

The walk over taken nodes is proved once (`Section Walk`) for any
pointer-indexed assertion closed under the hop over a taken node, and
instantiated for insert and tryRemove.

## Departures recorded

CAS instead of store for the successor rewrite; top adjustment in getTop
rather than remove; no write to the previous top's successor; insert
computes its successor before allocation. Memory is not reclaimed (the
heap has no free), as in the original.
