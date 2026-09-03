# AegisSheet materialised merge: plan (revised after validation round 1)

This plan states what exists, what is claimed with which evidence class, what
is proposed, and what a validator should try to break. Section 8 records the
first validation round and how each finding changed the plan.

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
3. `AegisSheetAbstraction.lean`: `no_view_only_step` shows the visible sheet
   alone does not determine future behaviour; `row_tokens_distinguish_future`,
   `cell_versions_distinguish_future`, and `range_versions_distinguish_future`
   fix that tokens, cell version identities, and range version identities
   must be retained.
4. `AegisSheetGC.lean`: naive local purging is refuted; the corrected
   collector is a replicated marker with roster acknowledgements.
5. This directory: `note.pdf`, `model.py`, `campaign.md`.

## 3. What exists and its evidence class

- Python reference transcribing the Lean `view` and issuance: validated on
  the 20 SPOT fixtures and 5 issuance fixtures copied from `AegisSheet.lean`
  (`check_fixtures`).
- Candidate design (Section 3 of the note): materialised state of keep
  tokens, latest-position registers, active cell versions, active range
  versions; componentwise merge `mvr(l,a,b) = (l∩a∩b) ∪ (a∖l) ∪ (b∖l)` for
  sets and last-writer-wins by timestamp for registers. Specified; no Lean.
- H1 (design matches the union model): validated on honest executions, no
  counterexample in 3000 DAG executions over three seeds (117,290 versions,
  21,375 merges at a registered ancestor, 851 at a virtual base) for the
  named-removal variant. Every generated event, after erasing `kills`,
  passes a transcription of `applicableB` and `clockedB` (95,064 events).
  Conjectured in general.
- H1 clearing variant: matches the reference but 103 of 3000 executions
  have a merge that differs from timestamp-order replay, so a removal and a
  concurrent keep do not commute. Refuted as an all-commuting design.
- Commutation of the named variant: concurrent pairs commute; causally
  ordered pairs do not (a keep followed by the removal naming its token
  differs from the reverse order; likewise an overwrite and the version it
  names). Universal commutation therefore fails, and the all-commuting proof
  route is unavailable. Established by inspection; see Section 8.
- H2 (a dead axis's last position can be dropped when no live range names
  it): refuted by three hand-derived witnesses checked by the reference
  (`h2_witnesses`, `h2_pair3`) and by 16 to 55 failing executions per 1000
  in the harness. Residue: one position register per axis identifier. When
  it may be dropped depends on D1 below.
- Finding: in the current model, undoing a cell write revives a row removed
  causally later (`undo_revival_witness`). Reproduced; a specification
  question.
- H3 (purge dissolves into ordinary version deletion): staged, not modelled.
- Measured: stored timestamps at the final version grow 131 → 13,866 for
  the reference and 21 → 169 for the materialised design as operations go
  23 → 184 (3 replicas, 20 executions, seed 1). A timestamp-count
  measurement consistent with quadratic versus linear scaling, not a proof.

None of the candidate claims is machine-checked; the reference definitions
and baseline theorems cited above are. Negative controls (ancestor-ignoring
merge, eager range re-anchoring) fail on every seed.

## 4. Decision D1 (taken 2026-09-02): no revival

Undoing a cell write must not revive a row or column removed after the
write. Treated as an issuance rule: an inverse cell write is legal only
while its row and column are live. Consequences:

- Causal stability of a removal (every replica has observed it) can
  eventually justify discarding the dead position register; S1 tests this.
- The current-model revival SPOT (`undo_revival_witness`, and its Lean
  counterpart in S2) is preserved as documentation of the legacy semantics.
- The S3b equivalence is stated only for honest executions under the new
  rule, not for legacy traces that exercise revival.
- The harness applies the rule by default; `--legacy-undo` restores the old
  generator. Under D1 the named design has no failing execution on three
  seeds (96,069 honest events); see `campaign.md`.

## 5. Steps, in order

### S1. Model purge under the chosen D1 policy and close H3

Claim: with materialised state, purge is ordinary deletion of cell versions
at dead coordinates; the roster acknowledgement is needed only to drop the
dead register, and (under D1 = no revival) suffices for it.

Falsifier: (a) purged content reappears after a later merge; (b) a write
concurrent with the purge fails to survive or revives the axis at the wrong
position; (c) dropping the register after every replica has observed the
removal changes a later observation.

Reality oracle: the Lean `view` with purge markers, transcribed into the
Python reference and validated on the purge fixtures in `AegisSheetGC.lean`
before use.

Controls: positive, the reference's purge fixtures; negative, drop the
register before stability and observe a class (c) failure; legacy control,
run with `--legacy-undo` and exhibit the undo-after-stability revival as a
class (c) failure that the D1 rule removes.

Done when: 1000 executions per seed on three seeds with purge generated,
zero failures for the chosen retirement rule, documented failures for the
controls.

### S2. Pin the witnesses as Lean SPOTs against the current model

With `native_decide`, PASS and FAIL companions, expected values hand-derived
from the paper's policies:

- H2 witness 1: same live sheet, range resolves to `(r1, r2)` versus
  `(r2, r2)`.
- H2 witness 2: lazy resolution after a concurrent insert gives `(r3, r2)`;
  FAIL companion pins the eager answer `(r1, r2)`.
- H2 witness 3: move-then-remove versus remove; concurrent write revives at
  52 versus 10; FAIL companion pins remove-wins.
- Undo revival: remove at t=4, undo of the t=3 write at t=5, row live at 10
  with empty cell; FAIL companion pins the no-revival reading. Keep this
  SPOT regardless of D1: it documents the current model.

Done when: `lake build` passes, `#print axioms` shows only the compiler
axioms `native_decide` adds, and the SPOTs are listed in the ledger.

### S3. Lean port of the named-removal design

A second package beside the current one, not a replacement.

- State: product of `known` sets, token sets, position registers
  `(ts, pos)`, cell version sets, range version sets.
- `do`: Definition 3.2 of the note; a removal carries the tokens it kills.
- `merge`: Definition 3.3.
- Join route: not the all-commuting route. Token and version components are
  observed-remove sets whose removals name observed elements; prove `JoinAt`
  for each under an honesty predicate on the replay context (every removal's
  `kills` and every overwrite's `overwrites` lie in the issuer's causal
  past), the way `Queue` and `EmbedRGA` prove `JoinOn` under `QHonestCore`
  and `EHonestCore`, and discharge the predicate from issuance with
  `IssuanceEstablishes`. Compose with `joinAt_prod`. The position register
  is the one all-commuting component (max by timestamp) and may use the
  simple route.
- Sequential certificate: a new representation relation to the incremental
  machine in `AegisSheetSequential.lean`, covering tokens, version
  identities, and registers.
- Issuance: the current `applicable` minus `seen = eventTimes`, plus the D1
  clause, plus `kills = liveAxisTokens` for removals.

### S3b. Cross-model observational equivalence (the actual H1 theorem)

`VerifiedMRDT` for the new package proves correctness against its own
sequential specification; it does not show the union model is preserved.
State and prove:

- an erasure `erase` on events dropping `kills` (and any D1 clause) such
  that every honest execution of the new package erases to an honest
  execution of the union model;
- a representation relation `Represents(σ, E)` between materialised states
  and event sets, preserved by `do` and by `merge` at a canonical ancestor;
- `view(E) = observe(σ)` whenever `Represents(σ, E)`.

Scope: honest executions under the D1 issuance rule only. Legacy traces
that exercise revival are outside the theorem.

Done when: the theorem is stated over `MintCertifiedReachV` for the new
package and both directions of the fixture suite pass against it.

### S4. Documentation sync

Framework paper instance table; the two encodings and the measured gap;
`PRIORITIZED_REMAINING_WORK.md`.

## 6. What the validator should try to break

1. Transcription fidelity of `model.py` against the Lean definitions, in
   particular `axisTokenRemoved` (`token ∈ remove.seen`), `cellOverwritten`,
   `resolveFirst`/`resolveLast`, `idAtPosition`, `inverseFor`, and the new
   `applicable_b`.
2. Named removal fidelity: the Lean removal cancels tokens in `seen`; the
   named variant cancels `liveAxisTokens` at issuance. These coincide only
   if every token in `seen` that is not live was already cancelled by an
   earlier removal in the same causal past. Prove or refute.
3. Virtual merge base: the harness uses the timestamp-order fold of the
   intersection event set as the base when no recorded version matches.
   Confirm this equals the state `canonicalVirtualMergeBase` induces.
4. Componentwise claim: no cross-component clause is needed because
   `keepsAxis` includes cell updates and nothing else feeds liveness.
5. H2 witness 3: legality of both branch histories at each step.
6. Growth metric bias: `seen` counted once per event versus registers once
   per identifier.
7. Coverage gaps: undo of undo, merges between non-head versions, purge,
   ranges whose endpoints were never known.

## 7. Risks

- The retirement rule under D1 is causal stability; S1 must show it is
  sufficient, not only necessary.
- The `known` grow-only sets are one identifier per axis ever created; not
  collected.
- Named removal adds `|liveAxisTokens|` to each removal event; bounded by
  the row's activity since its last removal, not measured separately.
- The honesty predicate for S3 may need to be stronger than "kills and
  overwrites in the causal past"; the Queue proof needed a full core
  predicate.

## 8. Validation round 1

Findings from the reviewing agent, with the response.

1. "Every pair commutes" was false: a keep then the removal naming its token
   differs from the reverse. Accepted. The note and this plan now say that
   concurrent pairs commute, causally ordered pairs do not, and S3 uses the
   conditioned `JoinAt`/`JoinOn` route with `joinAt_prod`.
2. Causal stability does not authorise dropping the register unless D1 is
   "no revival". Accepted. D1 now gates S1, and S1's controls include the
   undo-after-stability case.
3. `VerifiedMRDT` alone does not establish H1. Accepted. S3b adds the
   erasure and the cross-model observational-equivalence theorem.
4. Generator honesty was an evidence gap; the axis-undo inverse with
   `kills` is not literally `inverseFor`. Accepted and closed: `model.py`
   now erases `kills` and checks every generated event against a
   transcription of `applicableB` and `clockedB`; all 95,064 events pass
   and all campaign counts are unchanged. The transcription itself is
   validated on five issuance fixtures from `AegisSheet.lean`.
5. Evidence wording: `no_view_only_step` versus the three `distinguish`
   theorems; "nothing is machine-checked" versus "none of the new claims";
   growth as a count measurement. Accepted and corrected in the note.

The reviewer reproduced both campaign commands and the growth table.

## 9. Validation round 2

D1 decided as no revival by the reviewer and the author, with the two
caveats now in Section 4. The branch was rebased onto `main` at `50e48e2`.
The generator default switched to the D1 rule and the three-seed campaign
was rerun: named-keep 0/0/0 failing executions, clearing 35/31/55 (replay
mismatch), ranges-GC 16/11/11, all-dead-GC 9/6/9, ancestor-ignored
179/156/141, eager 646/675/684; 96,069 generated events all pass the
transcribed `applicableB`.
