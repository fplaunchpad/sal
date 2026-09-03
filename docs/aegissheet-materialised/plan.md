# AegisSheet materialised merge: plan for validation

This plan is written for a second agent to validate. It states what exists,
what is claimed with which evidence class, what is proposed, and what the
validator should try to break.

## 1. Research question

The verified AegisSheet (`Sal/MRDTs/Instances/AegisSheet.lean`) is a CRDT
in the MRDT signature: its state is the set of all events, `merge _ a b :=
a ∪ b` ignores the common ancestor, and every event carries `seen`, the
timestamp set of its entire causal past, so state is quadratic in history.
Question: can the ancestor argument of a three-way merge replace that
metadata while preserving every observation of the current model, and what
must still be retained?

## 2. Source of truth, in order

1. Tables 3 and 4 and Figure 1 of the AegisSheet paper (external intent).
2. The executable Lean model: `view`, `applicableB`, `validUndo`,
   `inverseFor`, `resolveRange`, and the SPOT fixtures in `AegisSheet.lean`.
3. `AegisSheetAbstraction.no_view_only_step`: the visible sheet alone does
   not determine future behaviour; any representation must keep observed-
   remove tokens and active cell and range version identities.
4. `AegisSheetGC.lean`: naive local purging is refuted; the corrected
   collector is a replicated marker with roster acknowledgements.
5. This directory: `note.pdf` (exploratory note), `model.py` (Python
   reference plus candidate design plus differential harness),
   `campaign.md` (campaign report).

## 3. What exists and its evidence class

- Python reference transcribing the Lean `view` and issuance: validated on
  the 20 SPOT fixtures copied from `AegisSheet.lean` (`check_fixtures`).
- Candidate design (Section 3 of the note): materialised state of keep
  tokens, latest-position registers, active cell versions, active range
  versions; componentwise merge `mvr(l,a,b) = (l∩a∩b) ∪ (a∖l) ∪ (b∖l)` for
  sets and last-writer-wins by timestamp for registers. Specified; no Lean.
- H1 (design matches the union model): validated, no counterexample in 3000
  DAG executions over three seeds (117,290 versions, 21,375 merges at a
  registered ancestor, 851 at a virtual base) for the named-removal
  variant. Conjectured in general.
- H1 clearing variant (a removal empties the token set instead of naming
  the tokens it kills): matches the reference but 103 of 3000 executions
  have a merge that differs from timestamp-order replay, so remove and a
  concurrent keep do not commute. Refuted as an all-commuting design.
- H2 (a dead axis's last position can be dropped when no live range names
  it): refuted by three hand-derived witnesses checked by the reference
  (`h2_witnesses`, `h2_pair3`) and by 16 to 55 failing executions per 1000
  in the harness. Residue: one position register per axis identifier,
  retained until the removal is causally stable.
- Finding: in the current model, undoing a cell write revives a row removed
  causally later (`undo_revival_witness`). Reproduced; a specification
  question.
- H3 (purge dissolves into ordinary version deletion): staged, not modelled.
- Measured: stored timestamps at the final version grow 131 → 13,866 for
  the reference and 21 → 169 for the materialised design as operations go
  23 → 184 (3 replicas, 20 executions, seed 1).

Nothing is machine-checked. Negative controls (ancestor-ignoring merge,
eager range re-anchoring) fail on every seed.

## 4. Decision needed before any Lean work

D1. Should undoing a cell write revive a row or column removed after the
write? Current model: yes. Recommendation: no, via an issuance clause
requiring live axes for the inverse of a cell write. Either answer changes
the public sequential specification of the port; it does not change the
current package.

## 5. Steps

### S1. Close H3 in the harness

Claim: with materialised state, purge is ordinary deletion of cell versions
at dead coordinates; the roster acknowledgement is needed only to drop the
dead register.

Falsifier: any of (a) purged content reappears after a later merge, (b) a
write concurrent with the purge fails to survive or revives the axis at the
wrong position, (c) dropping the register after every replica has observed
the removal changes some later observation.

Formal oracle: none yet. Reality oracle: the Lean `view` with purge markers,
transcribed into the Python reference (currently omitted) and validated on
the purge fixtures in `AegisSheetGC.lean` before use.

Controls: positive, the reference's purge fixtures; negative, drop the
register before stability and observe a failure of class (c).

Done when: 1000 executions per seed on three seeds with purge generated,
zero failures for the stable-drop rule, and a documented failure for the
premature-drop control.

### S2. Pin the witnesses as Lean SPOTs against the current model

Add to `AegisSheet.lean` (or a sibling SPOT file) with `native_decide`:

- H2 witness 1: two single-replica histories, same live sheet, range
  resolves to `(r1, r2)` versus `(r2, r2)`.
- H2 witness 2: lazy resolution after a concurrent insert gives `(r3, r2)`.
- H2 witness 3: move-then-remove versus remove, concurrent write revives at
  52 versus 10.
- Undo-revival finding: remove at t=4, undo of the t=3 write at t=5, row
  live at 10 with empty cell.

Each with a FAIL companion that pins the tempting wrong answer (eager
re-anchoring, remove-wins, delete-order). Hand-derive expected values from
the paper's policies; do not `#eval` the model.

Done when: `lake build` passes, `#print axioms` shows only the compiler
axioms `native_decide` adds, and the SPOTs are listed in the ledger.

### S3. Lean port of the named-removal design

A second package beside the current one, not a replacement:

- State: product of `known` sets, token sets, position registers `(ts,
  pos)`, cell version sets, range version sets.
- `do`: as Definition 3.2 of the note; removal carries the killed tokens.
- `merge`: Definition 3.3.
- `Join`: every pair commutes, so either the universal-equation route
  (`MergeLaws`, `DeltaLaws`, `causalDeltaLaw_of_all_comm`) or the product
  theorem `joinAt_prod` with MVR-style component lemmas. Check first whether
  `DeltaLaws` holds for arbitrary states of each component; if not, use the
  feasible-state route.
- Sequential certificate: new representation relation to the existing
  incremental machine in `AegisSheetSequential.lean`; the relation must
  cover tokens, version identities, and registers (this is what
  `no_view_only_step` forces).
- Issuance: the current `applicable` minus `seen = eventTimes`, plus the D1
  decision, plus `kills = liveAxisTokens` for removals.

Done when: `VerifiedMRDT` for the new signature is registered, the 20 SPOT
fixtures pass against it, and `scripts/check-mrdt-refactor.sh` is green.

### S4. Documentation sync

Framework paper instance table row for the new package; note the two
encodings and the measured gap; `PRIORITIZED_REMAINING_WORK.md`.

## 6. What the validator should try to break

1. Transcription fidelity: diff `model.py`'s reference functions against
   the Lean definitions line by line, especially `axisTokenRemoved`
   (`token ∈ remove.seen`), `cellOverwritten`, `resolveFirst`/`resolveLast`
   (min/max over live positions, `idAtPosition` tie-break by smallest id),
   and `inverseFor`.
2. Named removal fidelity: the Lean removal cancels tokens in `seen`; the
   named variant cancels `liveAxisTokens` at issuance. These coincide only
   if every token in `seen` that is not live was already cancelled by an
   earlier removal. Check the argument or find a counterexample.
3. Generator honesty: every generated event must satisfy `applicableB` at
   its issuing state. The harness mirrors the guard but does not call a
   transcribed `applicableB`; add that check and rerun.
4. Virtual merge base: the harness uses the timestamp-order fold of the
   intersection event set as the base when no recorded version matches. Is
   this the state `canonicalVirtualMergeBase` would produce? The framework
   proves the fold is canonical for the intersection; confirm the
   materialised fold order is irrelevant only for the named variant.
5. Componentwise claim: the note says no cross-component clause is needed
   because cell writes are keep tokens. Confirm `keepsAxis` includes cell
   updates and nothing else feeds liveness across components.
6. H2 witness 3: check that both branch histories are legal at each step
   and that the reference really places the revived row at 52 and 10.
7. Growth metric: the count is timestamps stored, not bytes. Check that the
   comparison is not biased by counting `seen` once per event while
   counting registers once per identifier.
8. Coverage gaps: undo of undo, merges between non-head versions, purge,
   and ranges whose endpoints were never known are not generated.

## 7. Risks

- D1 may be answered "yes", in which case dead registers must be retained
  for as long as any replica can still undo a write into the row, which is
  unbounded without stability.
- The `known` grow-only sets are one identifier per axis ever created; the
  note does not attempt to collect them.
- The named removal adds `|liveAxisTokens|` to each removal event; the
  bound is the row's activity since its last removal, not history, but it
  is not measured separately in the growth table.
