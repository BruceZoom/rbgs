# Coq pitfalls in this development

A running list of things that repeatedly cost time when writing proofs here.
Each entry says how the problem shows up, why it happens, and what to do.
Add an entry whenever a proof session loses more than a few minutes to
something that is not a real proof obstacle.

Maintained by hand. Keep entries short; put long explanations in the plan
of the layer where the problem arose.

## Parsing and notation

| Symptom | Cause | Fix |
| --- | --- | --- |
| `Syntax error: ',' or ')' expected` right before a `]` | `)]` lexes as one token: `TPSimulation` defines the notation `[( ρ , π )]` for abstract configurations. | Write `) ]` with a space, in tactic lists (`[tac (H) \| tac]`) and everywhere else. The same holds for `[(` in intro patterns: write `[ (a & b) H ]`. |
| `Unknown interpretation for notation "( _ , _ )"` | Files that import `AssertionsSingle`/`AssertionsSet` get the notations `( σ , ρ , π )` and `( σ , Δ )` for proof states, which replace the standard tuple notation. | Write pairs as `pair a b`. Nested tuples in patterns (`(v, ts, taken, next)`) still work as intro patterns. |
| `lia` fails with `Cannot find witness` on a trivial goal such as `1 <= 2` | `<=`, `<` and numerals are re-bound by imported scopes (positives from `PArith`, orders from `coqrel`). The goal is not Peano arithmetic. | State facts with `Peano.le`/`Peano.lt` and constructor numerals (`S O`), or annotate with `%nat`; reduce definitions with `unfold ...; simpl` before `lia`. |
| A `t` in scope has type `Type` | `Import Reg` (and similar) brings a module type field named `t` into scope; `inversion` then renames a constructor binder `t` to `t0`. | Do not refer to binder names introduced by `inversion`. Use `match goal with H : ... ?tt ... \|- _ => ... end` to capture them. |

## Unification and rewriting

| Symptom | Cause | Fix |
| --- | --- | --- |
| `rewrite H` reports `Found no subterm matching ...` although the printed goal contains the term | The implicit argument differs up to unfolding, typically `@LinState (@ESPList A)` versus `@LinState (li_sig F)`, or `@fst mem_control cas_control` versus `@fst (State ...) (State ...)`. `rewrite` matches syntactically. | Avoid `rewrite`: use `exact (eq_trans H1 H2)`, `refine (eq_trans _ _)`, `pose proof (eq_trans (eq_sym H) H') as Habs; discriminate Habs`. Or state the lemma on the concrete shapes (`pair mc cc`) so both sides print and elaborate identically. |
| `congruence` fails on two chained equalities | Same cause as above: the equalities' types differ up to conversion. | `exact (eq_trans H1 H2)`. |
| `simpl` makes a later `rewrite` fail | `simpl` unfolds `live_at`, `live_order`, projections of `mk`/`mks`, and sometimes `mem_heap`, changing the syntactic shape. | Use targeted reduction: `cbn [mk SinglePossState.σ fst snd]`, or prove small equations (`live_order_cons_live`) and rewrite with those instead of calling `simpl`. |
| `exact (lemma _ _ H)` fails with `Cannot infer this placeholder of type concrete_state` | Arguments are elaborated before the goal is unified, so a hole that only the goal determines stays open. | Give the argument explicitly (`(pair (Idle s3) s2)`), or use `apply lemma with (σ := ...)`. |
| `Unable to find an instance for the variable t` on `apply lemma` | A lemma parameter appears only in hypotheses, not in the conclusion. | `apply (lemma q t0)`. |
| `The term "K" has type "... -> Type"` with a universe inconsistency in an `assert (forall K, ...)` | The binder was inferred as `Type`-valued. | Annotate: `forall K : tid -> single_state -> Prop`. |
| `apply H` fails with `Unable to unify "CI P" with "P (...)"` although `H : CI P` and `CI P` is a `forall` | `apply` does not unfold a `Definition` whose body is a `forall` to expose the product. | Apply it explicitly: `apply (H σ1 σ2 ρ1 π1)`. Holes (`apply (H _ _ _ _)`) fail with `Cannot infer this placeholder` for the reason above; give the arguments. |
| After `eapply lemma; eauto` the wrong goal remains, typically a fact about the *post*-state that is false | A premise of the form `(forall x, P ?p x -> P p' x)` with `?p` still an evar is closed by `eauto` with `?p := p'`, and the premise that should have fixed `?p` is left unprovable. | Do not `eauto` across premises that share an evar; list them: `eapply lemma; [exact H1\|exact H2\|apply pres\|exact HI]`. |
| `rewrite Hlin in Hat` reports `Found no subterm` on two facts about the same `TMap.find t π` | Canonical-structure resolution gives `ls_inv (nmsetTS l ts)` the signature `@ENodeMem A` while the map has `@LinState (li_sig F)`; the printed terms agree, the implicit arguments do not. | Combine the two equalities with `eq_trans (eq_sym H1) H2` and `injection` (`NodeMemProof.AtSetTS_self`), or annotate the binder `(p : tmap (@LinState (li_sig F)))`. |
| `simpl` leaves `rec_val (mkrec lv lts lt ln)` or `node_ts (mknode ...)` unreduced | `simpl` does not unfold a definition whose body is a constructor application (`mkrec`) even when a projection is applied to it. | `cbn [rec_val rec_ts mkrec fst snd]` (see `simpl_fields` in `NodeMemProof.v`). |
| `congruence`/`rewrite` fail on a goal about `rec_h (σ (st c a p))` when the hypotheses speak of `rec_h c` | After `eapply` into a lemma stated on `st c a p`, the goal keeps the unreduced projection. | `cbn [st SinglePossState.σ]` (or `simpl in Ha, Hb`) before `congruence`; `simpl_abs` in `NodeMemProof.v` does the same for `abs`. |
| `eapply lemma` fails with `Unable to unify "P ?p (mk (?mc, ?cc) (ρ ?w) (π ?w))" with "P (Some l) ((Pending ..., s2), ρ1, π1)"` | The lemma's conclusion projects a proof-state variable (`SinglePossState.ρ w`); unification will not invent `w` from `ρ1`. | State transfer lemmas over explicit components: `P p (mk σ ρ π) -> ... -> P p (mk (pair mc' cc') ρ π)` (`source_I_controls`, `*_controls` in `SPListUnlinkProof.v`); then `eapply` unifies `σ ρ π` from the hypothesis and `mc' cc'` from the goal. |
| `rewrite Hlive` fails after `simpl` on a goal `filter (live_at h) (l :: xs) = ...` | `simpl` unfolds `live_at` into its `match`. | `cbn [List.filter]` exposes the `if live_at h l then ...` without unfolding `live_at`. |
| `The reference NoDup_app_remove_l was not found` | Coq 8.15's `List` lacks it (added later). | Prove `NoDup (a ++ b) -> NoDup b` by induction on `a` (`NoDup_app_right_part`). |
| `injection H as <- H'` then `H'` is "not found", or `rewrite H'` fails | When one of the injected equations is between variables, the `as` pattern's names and directions are unreliable (the equation may be substituted away). | `inversion H; subst` and pick the surviving equation with `match goal with H : ?a ++ _ :: ?b = _ ++ _ :: _ |- _ => ... end` (`split_unique` in `SPListUnlinkProof.v`). |

## Tactics on this framework

| Symptom | Cause | Fix |
| --- | --- | --- |
| `No matching clauses for match` from `match goal` | The pattern matched but the *body* failed; Ltac backtracks over all clauses and then reports no match. | Debug the body with explicit names first (`all: exact I.` prints the context), then restore the `match`. |
| `repeat split; auto` leaves goals or splits too far | `split` also splits definitions that unfold to conjunctions (`source_G`, `represents`), and fails on `linked`/`HLinked` conjuncts. | Split explicitly: `split; [exact H1\|]. split; [exact H2\|]. ...` |
| `Hstep is already used` | `pupdate_intros_atomic` introduces `Hstep`, `Hpre`, `σ1`/`Δ1`, `s2`, `s3`, `t0`, `l0`, `H0`. | Do not reuse those names. Rename `H0` with `match goal with H : s3 l0 = Some _ \|- _ => rename H into Hconcrete end`. |
| The event's return variable disappears after `pupdate_intros_atomic` | `inversion` substitutes the lemma's variable that appears in the event (`t`, `l`, `ts`) by the constructor's. | Bind the surviving term from the goal: `match goal with \|- context [GetTopWindow _ _ _ _ _ ?tss] => pose (TS := tss) end`. Get field values from a member's `NodeCell` and `injection`, not from the constructor's names. |
| `Error: The reference End was not found` when compiling a truncated file | The truncation point is inside a `Definition`/`Lemma`. | Truncate one line before the header, or after the previous `Qed`. |
| `Syntax error` at `[Hvx|->]` or `[He|(a & b)]` in an intro pattern | `|->` is the `↦` notation and `|(` / `)]` / `[(` lex as tokens in files that import `AssertionsSet`/`TPSimulation`. | Put spaces: `[Hvx| ->]`, `[He| (a & b) ]`. |
| `The term "I" has type "assertion" while it is expected to have type "True"` | A user-level `Definition I : assertion` shadows `Logic.I`. | Write `exact Logic.I`. |
| A section lemma takes a hypothesis it does not mention, or omits one it seems to use | `lia`, `congruence`, `eauto` may use any hypothesis in scope, so the proof term, not the statement, decides which section hypotheses become parameters. | Apply section lemmas with `eapply ...; eauto` or `edestruct (lemma explicit_args) as ...; eauto` instead of positional hypothesis lists. |
| `congruence` fails on a chain `σ w'' = σ w3 = σ w1 = TSAReady s` although all equalities are in context | The occurrences of `SetPossState.σ` differ in implicit arguments (`proof_state` versus its unfolding). | `exact (eq_trans (eq_sym H1) (eq_trans (eq_sym H2) H3))`. |
| `injection`/`discriminate` fail on `Some (ls_linr f r1) = Some (ls_linr f r2)` | `ls_linr f ret` has a dependent argument. | Project with a `match` on `f` (`pop_result` in `TryStackProofPaper.v`) and inject/discriminate the projected equation. |
| `rewrite H` fails with `Found no subterm matching "c ?n = Some ?a -> ..."` where `H : I_cells s c` is a `Definition` whose body is `forall i x, _ <-> _` | `rewrite` does not unfold the definition to find the iff; it reports the half-unfolded implication. | `apply H in Hc` / `apply H` (which unfold), or state the lemma with explicit iff directions (`HWQueueProof.I_cells_start_enq`). |
| `injection Hev` on `InvEv poq_deq = InvEv poq_deq` fails with "No information can be deduced" | Both sides are syntactically equal. | Wrap in `try`, or read results through a projection (`QueueLinProof.enq_res_value`) and `discriminate`/`injection` the projected equation; this also replaces `dependent destruction` on `ResEv` equalities, which fails when the result type depends on the operation. |
| `rewrite Hinv'` fails after `simpl` although the printed goal matches | `simpl` unfolded a record projection applied to a `set`-abbreviated state (`tsa_node_inv s'`) into the underlying `node_update`. | Rewrite before `simpl`, or `unfold s'` and use `cbn [proj mk]` with an explicit list. |
| `repeat split; auto` leaves a goal `control_agree_ctrl q (fst ρ) (fst ρ')` or breaks the following bullets | After the abstract state became a pair (ghost log), `control_agree` is a conjunction and `repeat split` splits it; `auto` cannot prove the half from the whole hypothesis. | `split; [exact Hagree|]` before `repeat split; auto` (see `poss_steps_replay` in `SPListUnlinkProof.v`). |
| `pupdate_forward`'s `constructor` cannot close the abstract step when the overlay state is a pair | The target state is an evar; `split` on `StepGhost ev s1 ?s2` leaves `fst ?s2`, which `constructor` cannot instantiate. | Give the target state: `gstep_inv t op (pair (AtomicPending s t op) log)` / `gstep_ret ...` in `SPListUnlinkProof.v`, then close the `StepSPList` goal yourself (`constructor`, `rewrite <- Hcount; constructor`). |
| An `eapply lemma; [exact H1\|exact H2\|auto\|auto\|exact HI]` leaves the `auto` goals open and the next bullet reports `Wrong bullet` | When `auto` runs, an evar of the lemma is still unresolved (only a later item instantiates it), so `auto` fails silently. | Order the list so the instantiating item comes first, or `eapply lemma; [exact H1\|exact H2\| \| \|exact HI]; auto`. |
| `exists ...` fails with `Not an inductive goal with 1 constructor` on a `Definition` | The definition was turned into a disjunction. | `left.`/`right.` first; the message does not name the definition. |
| `x is already used` on `intros x` or `destruct ... as [\|x ...]` deep in a method proof | A variable of that name already exists after `pupdate_intros_atomic`/`inversion`. | Pick another name (`y`, `x0`). |

## Proof engineering that worked

- **Iterate on a truncated copy.** `SPListProof.v` compiles in seconds up to
  any point. A script that copies the first `N` lines, appends
  `End Proof. End SPListProof.`, and runs `coqc` with the `_CoqProject`
  flags (`-R examples examples -R models models ...`, see `Makefile.conf`)
  gives one error per iteration.
- **Print the goal by failing.** `exact I.` (or `all: exact I.`) shows the
  full context and goal in the error message; `Set Printing All.` before it
  exposes implicit-argument mismatches.
- **Plan the set-of-possibilities structure before proving.** Twins,
  filters and forks (`SPListProof.v`, section "Pointwise possibility
  facade") need their invariants fixed first; the individual update lemmas
  are then mechanical.
- **Ghost state in the overlay, erased afterwards.** When the
  representation invariant needs information no state records (the
  insertion order of `SPListUnlink`), prove the layer against a
  specification extended with ghost state and erase it with
  `CompLinProj.LIProj`; the projection must map steps to steps and errors
  to errors. The possibility facade then needs the ghost in
  `offslot_agree`/`slot_agree` (twins share it) and classical splits
  where it used to rely on payload determinism from the concrete state.
- **Generic loop lemmas.** A loop used by several methods with different
  invariants (`skip_taken_impl`) is proved once in a `Section` over a
  pointer-indexed assertion with hop/stability/locality hypotheses.
