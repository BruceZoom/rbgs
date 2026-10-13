# Verification Plan: Herlihy–Wing queue

## Objective and deliverables

Prove that the Herlihy–Wing queue over an atomic counter and an atomic
swap array is linearizable with respect to the FIFO queue, following
`docs/proof-details/HWQueueProofDetails.tex` (section numbers below refer
to that write-up).  The decomposition is

    Queue ◁ POQueue ◁ (Counter ⊗ SwapArray)

Files:

- `examples/HWQ/CounterSpec.v`, `examples/Common/SwapSpec.v`: the hardware
  objects (Section 3).
- `examples/HWQ/POQueueSpec.v`: the partial-order queue with its
  well-formedness lemma and transformer facts (Section 4).
- `examples/HWQ/QueueSpec.v`: the FIFO queue (Section 6.1).
- `examples/HWQ/HWQueue.v`, `HWQueueProof.v`: Layer 1, singleton facade
  (Section 5).
- `examples/HWQ/QueueLin.v`, `QueueLinProof.v`: Layer 2, set logic
  (Section 6).
- `examples/HWQ/HWQueue_TopLevel.v`: the composition (Section 7).

Exported results:

```coq
HWQueueProof.MHWQueue           : layer_implementation_simulation E_1 POQueue
QueueLinProof.MQueueLin         : layer_implementation_simulation POQueue Queue
HWQueueTopLevel.MHWQueue_linearizable
  : layer_implementation_linearizability (Counter ⊗ₗ SwapArray) Queue
```

All three depend only on `classic` and `Eq_rect_eq.eq_rect_eq`.

## Departures from the write-up

1. **Well-formedness.**  (W1)–(W5) are not inductive on their own.  The
   Coq record `poq_wf` adds (W6) edge sources are vertices, (W7) pending
   vertices are vertices, (W8) garbage vertices are vertices; the write-up
   uses these implicitly ("the new identifier is fresh").
2. **Layer 1 invariant.**  (I1)–(I3) are extended by `pending_tokens`: a
   thread with a pending enqueue holds the token `⋆enq(x)` with `V(n) = x`.
   It is what makes `EnqStart` (which needs `P[α] = ⊥`) follow from `I` at
   the concrete invocation, where the framework only tells us that `α` had
   no token.
3. **Guarantee of Layer 1.**  `G(α)` records only the abstract transition
   and token move of a step (`g_silent`, `g_enq_inv`, `g_enq_ret`, `g_deq`);
   the concrete state is unconstrained because the program logic supplies
   `I` at the post-state of every stability obligation.  The write-up's
   "every step preserves `I`" is therefore not part of `G`.
4. **The inner loop.**  The `for` loop is a `ForEach` over `seq 0 r` whose
   accumulator is the value found so far; after a hit the remaining
   iterations do nothing.  The loop invariant `ScanInv` is the write-up's
   `Scan(α, i, r)` together with "the remaining slots are `seq i (r - i)`".
5. **No thread domain.**  Nothing in the queue is per-thread, so no layer
   carries the actor-outside-domain error of the TSStack development; all
   objects are error-free.
6. **Layer 2 invariant.**  (J2)'s ghost phase map is not needed: the
   phase of another thread is determined by its pending entry
   (`I_pending`) and the thread's own phase by the method's assertions
   (`Active`, `EnqPending`, `DeqAtomic`, `Completed`), as in
   `TSStackProof`.  (J1) is `I_graph`, stated through lookups.
7. **Topological orders.**  Because vertex identifiers are handed out in
   order and (W2) directs every edge to a smaller identifier, listing a set
   of vertices in increasing order is a topological order
   (`topo_exists` selects a sublist of `seq 0 nxt`).  No finiteness witness
   is stored in the invariant.
8. **The dequeue filter.**  As in the TSStack proof, `G_deq` keeps the
   possibilities *justified by an order headed by the removed vertex*, which
   is what the (J1) argument of Lemma 6.5 uses.

## Dictionary

| Write-up | Coq |
| --- | --- |
| `(V, E, P, g, nxt)` | `POQueueState` with `poq_vertices`, `poq_edges`, `poq_pending`, `poq_garbage`, `poq_next` |
| `Ready(s)`, `Atomic(s, α)` | `POQReady s`, `POQAtomic s α poq_deq` |
| `◦ enq(x)`, `⋆ enq(x)`, `• (enq(x), ok)` | `enq_inv_token x`, `enq_lini_token x`, `enq_ret_token x` |
| `Scan(α, i, r)` | `HWQueueProof.Scan α i r` (with `scan_clause`) |
| `omitted(s, π, n)`, `X(s, π)` | `QueueLinProof.omitted`, `lin_set` |
| `topo(s, Y, N)`, `vals(s, N)` | `topo`, `values_of` |
| branch (a)+(b) of Lemma 6.3 | `ac_lin` (image under `lin_closure`) |
| Lemma 6.4's filter, Lemma 6.5's selection | `ac_select` |

## Validation

```text
make examples/HWQ/HWQueue_TopLevel.vo
git diff --check
rg -n "Admitted|admit|Axiom" examples/HWQ/*.v examples/Common/SwapSpec.v
```
