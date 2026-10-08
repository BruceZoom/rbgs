# Plan: TryStack over TryStackAux, following Appendix A.4 (TryStack part)

Status (2026-10-08): **done**.  The proof follows the rewritten A.4 that is
in `examples/TSStack/docs/main-tr.pdf` (pp. 41-51), per the user's decision.
The earlier definitions (`CanPop`, `PopAttempt`, ...) are superseded;
Section 5 keeps the analysis of why they cannot work.  Files:
`examples/TSStack/TryStackHistory.v` (positions, histories, legality
(Fig. 31), the canonical history, Lemma A.1 as `fs_insertion`, and the
ghost-clock well-formedness of TryStackAux) and
`examples/TSStack/TryStackProofPaper.v` (the layer proof, exports
`MTryStackPaper`, `MTryStackPaperLinearizable`, `MListPoolTryStackPaper`).
Nothing is admitted.  `MTryStackPaper` and `MTryStackPaperLinearizable`
depend only on `classic` and `Eq_rect_eq`; `MListPoolTryStackPaper` adds the
propositional and functional extensionality principles of the lower layers.
Lemma A.1 depends only on `classic`.

## 0. Which paper text

`docs/main-tr.pdf` = `examples/TSStack/docs/main-tr.pdf` (same md5) hold
the rewritten A.4 (`I_lag`, `Plans`, `specS`, `G_push-inv`, `G_push-ret`,
`G_snap`, `G_rmv`, `G_fail`, `G_emp`, Lemma A.1; Fig. 30 spec rules,
Fig. 31 legality, Fig. 32 push outline, Fig. 33 trypop outline).  Its LaTeX
source is the uncommitted working copy of
`POPL2027/CompSim/appendix/tsstack.tex` in `~/Research/async-ccal`.  The
committed source (`e0f6373c`, "July text") is the one the task text
originally named; it is unsound (Section 5).

## 1. Dictionary: paper notation to Coq

### Clocks (Coq stamps events with the pre-state clock)

Every TryStackAux transition except the atomic empty branch stores
`tsa_now s` in the ghost fields and sets `tsa_now := S (tsa_now s)`.  So an
event is stamped `u` when it is the `(u+1)`-th event, and the paper's clock
value of that event is `u+1`.  All conditions below are restated for the
Coq stamps; "gap `u`" is the gap after the events stamped `< u` and before
the event stamped `u`.  The current gap of `s` is `tsa_now s`.

| Paper | Coq |
| --- | --- |
| `σ.t` | `tsa_now s`, written `t` |
| `ι(x)`, `r(x)` | `tsa_node_inv s x`, `tsa_node_ret s x` (`option nat`); Coq stamps |
| `τ(α)` | `TMap.find α (tsa_snap_time s)` |
| `M[n] = (α, st, rt)` | `tsa_removals s n = Some (α, st, rt)` |
| `S[α] = {x \| ι(x) < τ(α)}` | `TMap.find α (tsa_snapshots s) = Some N` with `N x ↔ ∃i, ι x = Some i ∧ i < st` (part of `ghost_wf`) |
| `(x,y) ∈ E ⟺ r(y) < ι(x)` | `tsa_edges s x y ↔ ∃i ry, ι x = Some i ∧ r y = Some ry ∧ ry < i` (part of `ghost_wf`) |
| `(x,y) ∈ E`, `n ∈ top(X \ g, E)` | `tsa_edges s x y`, `lp_top (fun m => X m ∧ ~ tsa_garbage s m) (tsa_edges s) n` |
| position `p = (u, k)`, `gap(p)` | `Pos := (nat * Qc)`, `gap p := fst p`, lexicographic `plt`; ranks are canonical rationals so that insertion never renumbers |
| `ι(x) ≤ gap(p)` (paper) | `ι x < gap p` |
| `gap(p) < r(x)` (paper) | `gap p ≤ r x` |
| `st ≤ gap(p) < rt` (paper) | `st < gap p ≤ rt` |
| `x →_h y ⟺ r(y) ≤ gap(h_inv(x))` | `above s h x y := ∃p ry, h_inv h x = Some p ∧ r y = Some ry ∧ ry < gap p` |
| history `h = (h_inv, h_pop)` | `Record history := { h_inv : LPNodeId -> option Pos; h_pop : LPNodeId -> option (Pos * tid) }` |
| legal (Fig. 31) | `legal s h` = `(inv)` `inv_all` `(pop)` `pop_all` `(spec)` `(top)` `(dist)`, Section 2 |
| `H` canonical | `canonical s H := legal s H ∧ places_all s H ∧ no_spec s H ∧ NND s H`; existential inside `I` |
| `NND(H)` | `∀x m, H_pop x = None → above s H x m → ~ tsa_edges s x m → ∃p β q, H_pop m = Some (p,β) ∧ H_inv x = Some q ∧ plt p q` |
| `Rep(h,B) = (ρ,π)` | `ρ = TSReady r` with `rep_state s h r` (pointwise) and `rep_tokens s h B π` (lookups) |
| `Plans(σ)` | `plan s H h B` (P1-P3 plus `B ⊆ dom S` without speculative pop) |
| overlay `(V_p,E_p,P_p,g_p)` | `r : TryStackState`; `ρ = TSReady r` |
| `◦(push v)`, `•(push v)`, `•(push v, ok)` | `ls_inv (ts_push v)`, `ls_lini (ts_push v)`, `ls_linr (ts_push v) tt` |
| `◦(trypop)`, `•(trypop, Succ(v,n))`, `•(trypop, Fail)`, `•(trypop, Succ ⊥)` | `ls_inv ts_trypop`, `ls_linr ts_trypop (TSuccNode v (fst n) (snd n))`, `… TFail`, `… TSuccEmpty` |
| `step(ρ, β:push(v))` | `TSReady (ts_start_push β l v r)` with `l = P[β]` |
| `step(ρ, β:trypop·β:trypop.Succ(v,n))` | two `poss_step`s via `TSAtomicPending`, result `TSReady (ts_mark_garbage n r)` |
| `placeS`, `popS`, `giveUpS`, `specS` | `PossibilityRelation` values; `specS σ := clos_refl_trans` of their union on `(ρ,π)` |
| `pstep(S)` | `PStep S`, derived with `PUpdateIdPStep`; exact image via the generic lemma `PUpdateIdPStepExact` (departure 9) |
| `pupd-imply`, `EvTriple-conseq` | `PUpdateIdImply`, `PUpdateConseqUpdates` (`ComposeR`) |
| `α ↦∀ ls` | `ALin α ls` |
| method outlines | `provable_perror`, `provable_vis_safe`, `provable_ret_safe` |

## 2. Definitions written out (Coq shape)

### Legality (Fig. 31), with Coq stamps

```text
(inv)     ∀x p. h_inv x = Some p →
            gap p ≤ t ∧ (∃i. ι x = Some i ∧ i < gap p) ∧ (∀ry. r x = Some ry → gap p ≤ ry)
(inv-all) ∀x. r x ≠ None → h_inv x ≠ None
(pop)     ∀n p β. h_pop n = Some (p,β) →
            gap p ≤ t ∧ (∃q. h_inv n = Some q ∧ q < p) ∧
            ( (∃st rt. M n = Some (β,st,rt) ∧ st < gap p ∧ gap p ≤ rt)
            ∨ (M n = None ∧ ∃st N. τ β = Some st ∧ S β = Some N ∧ N n ∧ st < gap p) )
(pop-all) ∀n. M n ≠ None → h_pop n ≠ None
(spec)    ∀n m p q β. h_pop n = Some (p,β) → h_pop m = Some (q,β) → M n = None → M m = None → n = m
(top)     ∀n p β x q. h_pop n = Some (p,β) → h_inv x = Some q → q < p → above s h x n →
            ∃p' β'. h_pop x = Some (p',β') ∧ p' < p
(dist)    h_inv injective on Some, h_pop injective on Some (positions), no inv/pop share a position
```

### Representation and plans

```text
rep_state s h r :=
  (∀x. ts_vertices r x = if h_inv x defined then tsa_vertices s x else None)
  ∧ (∀x y. ts_edges r x y ↔ h_inv x ≠ None ∧ h_inv y ≠ None ∧ above s h x y)
  ∧ (∀β l. TMap.find β (ts_pending_pushes r) = Some l ↔ P β = Some l ∧ h_inv (β,l) ≠ None)
  ∧ (∀n. ts_garbage r n ↔ h_pop n ≠ None)
rep_tokens s h B π :=
  (∀β l v. P β = Some l → V (β,l) = Some v →
      (h_inv (β,l) = None → π β = Some ◦(push v)) ∧ (h_inv (β,l) ≠ None → π β = Some •(push v)))
  ∧ (∀β. S β ≠ None →
      (∀n p v. h_pop n = Some (p,β) → M n = None → V n = Some v → π β = Some •(trypop, Succ(v,n)))
      ∧ ((¬∃n p. h_pop n = Some (p,β) ∧ M n = None) → ¬B β → π β = Some ◦(trypop))
      ∧ (B β → π β = Some •(trypop, Fail)))
plan s H h B :=
  legal s h
  ∧ (∀m. M m ≠ None → h_pop m = H_pop m)                         (P2)
  ∧ (∀x p. h_inv x = Some p → ∃q. H_inv x = Some q ∧ q ≤ p)       (P3)
  ∧ (∀β. B β → S β ≠ None ∧ ¬∃n p. h_pop n = Some (p,β) ∧ M n = None)
```

Tokens of threads that `σ` does not determine (completed-but-unreturned
pushes and trypops, threads outside any call) are left unconstrained by
`rep_tokens`; see departure 3.

### Invariant

```text
lag s r π :=  V_p ⊆ V; unplaced vertices are pending with ◦(push V[x]);
              placed pending vertices have •(push V[x]);
              P_p[β] = l ↔ P[β] = l ∧ (β,l) ∈ V_p;
              E ∩ V_p² ⊆ E_p ⊆ E ∪ {(x,y) | (x,y),(y,x) ∉ E ∧ y completed}, E_p ⊆ V_p²;
              g ⊆ g_p ⊆ V_p;
              n ∈ g_p \ g → ∃β ∈ dom S. n ∈ S[β] ∧ π[β] = •(trypop, Succ(V[n], n));
              π[β] = •(trypop, Succ(v,n)) → n ∈ g_p
I_lag s Δ  := ∀(ρ,π) ∈ Δ. ∃r. ρ = TSReady r ∧ lag s r π
I_pop s H Δ := ∀h B. plan s H h B → ∃r π. Δ (TSReady r) π ∧ rep_state s h r ∧ rep_tokens s h B π
I w        := ghost_wf s ∧ I_lag s Δ ∧ ∃H. canonical s H ∧ I_pop s H Δ      (s = payload (σ w))
```

### Speculation relations (on the payload `s` of `σ`)

```text
placeS σ (TSReady r) π (TSReady r') π' := ∃β l v. P β = Some l ∧ V (β,l) = Some v ∧ π β = Some ◦(push v)
      ∧ r' = ts_start_push β l v r ∧ π' = π[β ↦ •(push v)]
popS   σ (TSReady r) π (TSReady r') π' := ∃β N n v. S β = Some N ∧ π β = Some ◦(trypop) ∧ V n = Some v
      ∧ N n ∧ lp_top (ts_is_live r) (ts_edges r) n
      ∧ r' = ts_mark_garbage n r ∧ π' = π[β ↦ •(trypop, Succ(v,n))]
giveUpS σ ρ π ρ' π' := ∃β. S β ≠ None ∧ π β = Some ◦(trypop) ∧ ρ' = ρ ∧ π' = π[β ↦ •(trypop, Fail)]
specS σ := clos_refl_trans (placeS σ ∪ popS σ ∪ giveUpS σ)
```

### Guarantees (explicit relations; `Δ'` clauses are the paper's set comprehensions)

```text
G_push_inv α : σ --α:push(v)--> σ' ∧ α ↦∀ ◦(push v) on Δ ∧ Δ' = specS_σ'(Δ)
G_push_ret α : P[α] = l ∧ σ --α:push(v).ok--> σ' ∧ Δ'' = specS_σ(Δ)
               ∧ Δ''' = {(step(ρ, α:push(v).ok), π[α ↦ •(push v, ok)]) | (ρ,π) ∈ Δ'' ∧ π[α] = •(push v)}
               ∧ Δ' = specS_σ'(Δ''')                                       (departure 5)
G_snap α     : σ --α:trypop--> σ' (snapshot) ∧ α ↦∀ ◦(trypop) on Δ ∧ Δ' = specS_σ'(Δ)
G_rmv α      : σ --α:trypop.Succ(v,n)--> σ' ∧ Δ'' = specS_σ(Δ)
               ∧ Δ''' = {(ρ,π) ∈ Δ'' | π[α] = •(trypop, Succ(v,n))} ∧ Δ' = specS_σ'(Δ''')
G_fail α     : σ --α:trypop.Fail--> σ' ∧ Δ'' = specS_σ(Δ) ∧ Δ''' = {(ρ,π) ∈ Δ'' | π[α] = •(trypop, Fail)} ∧ Δ' = specS_σ'(Δ''')
G_emp α      : σ --α:trypop--> σ' (empty branch, control TSAAtomicPending) ∧ α ↦∀ ◦(trypop) on Δ
               ∧ Δ' = {(step(ρ, α:trypop·Succ ⊥), π[α ↦ •(trypop, Succ ⊥)]) | (ρ,π) ∈ Δ}
G_emp_ret α  : the forced Succ(⊥) response; Δ' = Δ
G α := union; R obs := ∪_{β ≠ obs} (G β ∪ GINV β ∪ GRET β) ∪ GId
```

`specS_σ(Δ)` abbreviates the exact image `{(ρ',π') | ∃(ρ,π) ∈ Δ. specS σ ρ π ρ' π'}`, which is
what `PStep (specS σ)` with the exact-image lemma produces.

### Derivations (decision 4)

```text
G_push_inv : PUpdateConseqUpdates (PUpdateIdImply GId) (underlay event triple, Δ unchanged) (PStep specS, exact)
G_push_ret : PUpdateConseqUpdates (PStep specS) (event, Δ unchanged) (PUpdateIdCompose (PStep S_ret) (PStep specS))
             where S_ret filters on •(push v) and takes the abstract response; PStepEnabled from I_pop
G_snap     : as G_push_inv
G_rmv/G_fail : PUpdateConseqUpdates (PStep specS) (event) (PUpdateIdCompose (PStep filter) (PStep specS)); PStepEnabled from I_pop (+ Lemma A.1 for G_rmv)
G_emp      : PUpdateConseqUpdates (PUpdateIdImply GId) (event) (PStep S_emp); enabled by I_lag; response: event with Δ unchanged
```

### Outlines (Fig. 32, Fig. 33)

```text
push:   {I ∧ α ↦∀ ◦(push v) ∧ P[α] = ⊥} S.push(v) {I ∧ ∃l. P[α]=l ∧ V[α,l]=v} S.push(v).ok {I ∧ α ↦∀ •(push v, ok) ∧ P[α]=⊥} ret
trypop: {I ∧ α ↦∀ ◦(trypop) ∧ S[α] = ⊥} S.trypop()
        {(I ∧ S[α] ≠ ⊥ ∧ control ready) ∨ (I ∧ α ↦∀ •(trypop, Succ ⊥) ∧ control TSAAtomicPending α)}
        r ← S.trypop() {I ∧ α ↦∀ •(trypop, r) ∧ S[α] = ⊥} ret r
```

## 3. Proof obligations, in the paper's order (all discharged)

1. `TryStackHistory.v`: positions (`Qc` ranks, order, density lemmas), histories,
   `above`, `legal`, `canonical`, `NND`, `plan`, `ghost_wf` and its preservation by
   every TryStackAux step, finite min/max/fresh-rank lemmas over the vertex list.
2. Lemma A.1 (`fs_insertion`): given `ghost_wf s`, `canonical s H`, `S[α] = N`,
   `τ(α) = st`, `n ∈ top(N \ g, E)`: ∃`H'` `P`, `canonical s' H'`, `H'_pop m = H_pop m`
   on `dom M`, `H_inv ≤ H'_inv` pointwise, `H'_pop n = (P, α)`, `st < gap P ≤ t`.
3. Layer: `rep_state`, `rep_tokens`, `plan`, `I_lag`, `I_pop`, `specS`, guarantees.
4. Every speculation step preserves `I_lag`.
5. Plans with events in the current gap are reached by speculation (induction on the
   number of current-gap events, removing the last one; then `giveUpS` for `B`).
6. `⊨ I ∘ G_push_inv ⇒ I`, `G_push_ret`, `G_snap`, `G_rmv`, `G_fail`, `G_emp`,
   `GINV`, `GRET`, in that order, each with its nonemptiness.
7. Stability of the outline assertions; `ValidRGI`; parallel compatibility.
8. Outlines and packaging: `MTryStackPaper`, `MTryStackPaperLinearizable`,
   `MListPoolTryStackPaper := LIVComp MListPoolTryStackAux MTryStackPaperLinearizable`.

## 4. Departures from the paper (decided and recorded)

1. **Dense positions, no renumbering.**  Ranks are canonical rationals (`Qc`), so
   `ins` inserts without renumbering and positions are absolute across histories
   (needed for (P2), (P3)).  The paper's identification of histories up to
   renumbering is dropped (`Rep` does not depend on ranks).  Consequence for
   Lemma A.1: "the least position with FS(P)" does not exist in a dense order; the
   proof takes the position the paper's own argument reaches, namely the position
   immediately before the earliest-placed newer unpopped vertex (over *all* newer
   unpopped vertices, pending or completed, since the paper's descent from the
   completed ones ends there) or the end of the current gap, and proves every
   conclusion of the lemma for it.
2. **`H` inside the invariant** (user decision 1): `WF(σ)` is `ghost_wf s ∧ ∃H. canonical s H`,
   and `I_pop` is relative to that `H`; `G_rmv` picks `H' = ins(H, α, n, st)`.
3. **`Rep` tokens.**  `σ` does not determine the tokens of completed-but-unreturned
   operations or of threads outside calls, so `rep_tokens` constrains only pending
   pushes and `dom S`; `I_pop` is "∃π with those tokens".
4. **`ρ` pointwise.**  `rep_state` is a lookup-based characterisation; no functional
   extensionality.
5. **`pstep(specS)` after the concrete event in `G_push_ret`, `G_rmv`, `G_fail`.**
   The paper's `I_pop` argument for `G_push-ret` ("`(h',B)` is also a plan of `σ`")
   fails for plans with speculative events in the new current gap `σ'.t`, which lie
   above the just-completed vertex and cannot be produced in `σ`.  Closing under
   speculation after the event (as the paper already does for invocation events)
   repairs it; the rule derivation is still `EvTriple-conseq`.
6. **`lag` strengthened** with two clauses the paper's arguments use but its `I_lag`
   lacks: placed pending vertices carry `•(push V[x])` (for `G_push_ret`'s filter to
   pick the right `v`), and a token `•(trypop, Succ(v,n))` implies `n ∈ g_p` (the
   paper cites "the last clause of `I_lag`", which is the converse).
7. **(P3)** is the inequality `H_inv ≤ h_inv`; the sentence about postponement is
   explanation.  `G_push_ret` shows the inequality alone suffices.
8. **Intermediate trypop assertion** is `I ∧ S[α] ≠ ⊥`; the paper's
   `(α ↦ ◦ ⊕ α ↦ •Fail) * true` is not stable under other threads' `popS` for `α`
   and is anyway a consequence of `I_pop` (plans `(H,∅)`, `(H,{α})`).
9. **Generic rule lemmas.**  Coq's `PStep S` only bounds `Δ'` from above, so the
   paper's `pstep(S)` (exact image) is a generic lemma `PUpdateIdPStepExact`;
   the "underlay event triple" (concrete step, `Δ` unchanged) is a generic lemma
   `PUpdateEventId`.  These are the only direct `PUpdate` proofs.
10. **`⊕` not needed**: `specS` is reflexive, so `ID` is inside the image.
11. **Coq encodings** kept from before: two-event push and trypop-empty (`G_emp`,
    `G_emp_ret` with control ownership), empty snapshot followed by `Fail`,
    overlay error via `provable_perror`, ghost fields untouched.
12. **Clock conventions** as in Section 1 (Coq stamps the pre-state clock).
13. **Lemma A.1 as proved.**  `TryStackHistory.fs_insertion` proves, for a
    canonical `H` and a removal `n ∈ top(S[α] \ g, E)` with `τ(α) = st`: there
    are `H'` and `P` with `canonical s' H'`, `H'_pop = H_pop` on `dom M`,
    `H_inv ≤ H'_inv` pointwise, `H'_pop(n) = (P, α)` and `st < gap P ≤ t`.
    The slot is chosen by `slot_exists` (the position immediately before the
    earliest-placed newer unpopped vertex, or the end of the current gap;
    departure 1), and `ins_canonical` is the paper's "H' is legal and
    satisfies NND" paragraph, with the blockers postponed to ranks
    `rank Q + (rank Qend - rank Q)·(ι(x)+1)/(t+2)` in the order of `ι`.  The
    paper's statement "every blocker of P is popped in H after P" is the
    hypothesis `HF6` of the slot, established in `slot_exists`.
14. **Trypop invocation as one update.**  Coq's event update must cover both
    underlay branches, so the trailing `pstep` uses the relation
    `S_trypop_inv`, which is `specS` when the control is `TSAReady` (the
    snapshot branch, `G_snap`) and the atomic `trypop-empty` step when it is
    `TSAAtomicPending` (`G_emp`).  The response update similarly uses
    `S_pre`/`S_filter`/`S_post`, selected by the control and the result.
15. **Generic rule lemmas actually used**: `PUpdateIdPStepExact` (pupd-pstep,
    exact image), `PUpdateEventId` (the underlay event triple),
    `PUpdateIdImplyPre` and `PUpdateIdRecordPre` (pupd-imply, with the
    precondition recorded in the relation so that the composed relation can
    be shown to be the paper's guarantee), `pstep_iff_change_σ` (rewriting the
    concrete state inside an image).  Every event triple is
    `PUpdateConseqUpdates` of these; no event-specific `PUpdate` is proved
    directly.  `PUpdateIdSpec`/`RelSpecUnion` are unused (departure 10).
16. **Enabledness recorded in `G_push_ret` and `G_emp`.**  The paper's
    `step(ρ, e)` presupposes that the abstract step is enabled; the Variants
    carry the side conditions `P_p[α] = l` (push response) and
    `dom(V_p) = g_p` (empty pop) explicitly, and `pr_Δ3_paper_form`,
    `em_Δ'_paper_form` show they are redundant under `I_lag`.

## 5. Why the July-text argument does not go through

The execution is the one the October text uses on p. 42 ("Why the
abstract pop must be placed retroactively"); it is legal for the Coq
TryStackAux specification.  `n → m` abbreviates `(n, m) ∈ E`.

1. `β1` pushes `m` and completes.
2. `β2` starts pushing `n`; `n → m`; `n` stays pending.
3. `α` invokes `trypop` and snapshots `S[α] = {m, n}`.
4. `β3` pushes `x` and completes: `x → m`, no `x → n` (`n` is pending).
5. `β2` completes `n`.
6. `β4` snapshots `{m, n, x}` and removes `n` (`n ∈ top(S[β4] \ g, E)`,
   nothing points into `n`).  `g = {n}`.
7. `α` removes `m`: `m ∈ top({m, n} \ {n}, E) = {m}`.  `g = {n, m}`.

Facts, in the July text's own terms.

- **`I_graph` is unsound.**  The abstract `trypop-succ` of `m` by `α`
  needs `m ∈ top(dom(V_p) \ g_p, E_p)`.  With `V_p = V`, `E_p = E`: after
  step 2, `n → m` with `n` live; after step 4, `x → m` with `x` live
  forever (`x` is in no snapshot but `β4`'s, and `β4` removes `n`).  So
  `m` is never a top in any lock-step possibility, and step 7 cannot be
  linearized.  The only abstract run is: `α` pops `m` in the gap after
  step 3 while `n`'s abstract `push-pending` is still unplaced (so
  `V_p = {m}`), then `n`'s `push-pending` is placed before step 5.  This
  is exactly the "pending push unlinearized" possibility of departure 3,
  and it contradicts `V_p = V ∧ P_p = P`.
- **`I_pop` is not inductive under `G_rmv` even if `I_graph` is relaxed.**
  After step 6 the new `I_pop` requires, for `A = [α]`,
  `can_pop = (m ∈ top({m} \ {n}))`, hence a possibility with
  `π[α] = •(trypop, Succ(m))` and `π[β4] = •(trypop, Succ(n))`.  Before
  step 6 the old `I_pop` demanded no such possibility: for `A = [β4, α]`,
  `α`'s vertex must be in `top({m} \ {n}) ∩ top(({m,n,x} ∪ {m,n}) \ {n})
  = {m} ∩ {x} = ∅`; for `A = [α, β4]`, `α`'s vertex must be in
  `top({m, n}, E) = {n}`, not `m`.  The July text's `G_rmv` argument
  ("`A'·A''` still satisfies the invariant because the joined snapshot
  shrinks") covers only indices that already contained `α`; it cannot
  produce the new index.  The October text says the same (p. 50: "This
  is the step where the paper's earlier argument was incomplete").
- **Root cause.**  `CanPop` evaluates `top` on the concrete graph and
  treats every vertex of a snapshot as placed.  The needed possibility
  exists only because `n` was pending at `α`'s snapshot and can be placed
  after `α`'s pop.  Whether `n` was pending at `τ(α)` is not a function
  of `(V, E, S, P, g)` in general (two executions with and without that
  property reach the same state), which is why the October text adds the
  timing data `(t, ι, r, τ, M)` and indexes completeness by histories
  (`Plans`) instead of by `(A, B)`.

Consequently the July-text invariant cannot be proved: ground rule 3
applies ("stop and ask before implementing; do not invent a different
invariant").

## 6. Decision record

2026-10-08: the user chose to follow the rewritten A.4 (option A above was
accepted), with decisions 1-6 recorded at the top of this file.

## 7. Deliverables and validation

```text
MTryStackPaper              : layer_implementation_simulation (@TryStackImpl.E A D) (@TryStackImpl.F A D)
MTryStackPaperLinearizable  : layer_implementation_linearizability … (LISim2LILin)
MListPoolTryStackPaper      : LIVComp (@TryStackAuxProof.MListPoolTryStackAux A D) MTryStackPaperLinearizable

make examples/TSStack/TryStackHistory.vo examples/TSStack/TryStackProofPaper.vo
make -j2
git diff --check
rg -n "Admitted|admit|Axiom" examples/TSStack/TryStackHistory.v examples/TSStack/TryStackProofPaper.v
Print Assumptions MTryStackPaper.   (expected: classic, Eq_rect_eq; the composition adds the
                                    extensionality axioms of lower layers)
```
