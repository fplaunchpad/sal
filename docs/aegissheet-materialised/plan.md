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

## 4b. Decision D2 (taken 2026-09-04): keep concurrent sub-cutoff writes

A write concurrent with a purge marker and at or below its cutoff is kept;
the marker masks exactly the versions it covered. Consequence (Section 12):
the materialised purge is plain deletion with no stored purge state. The
port's sequential specification uses the covered-set clause; the current
model's cutoff clause stays available as `--legacy-purge` for controls.

## 5. Steps, in order

### S1. Model purge under the chosen D1 policy and close H3 (done; Section 10)

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

### S2. Pin the witnesses as Lean SPOTs against the current model (done; Section 11)

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

### S3. Lean port of the named-removal design (Join, replay adequacy, observation equivalence proved; Sections 13 to 16)

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

## 10. S1 results

Harness extended with per-replica Lamport clocks, a laggard replica, purge
markers issued under `purgeApplicable` with frontier acknowledgements, purge
masks in the materialised state, three retirement rules, and per-design
failure counting (the earlier reports counted only the first failure per
execution; all numbers were rerun). Reference validated on the five purge
fixtures of `AegisSheetGC.lean`. Numbers in `campaign.md`.

- H1 holds: 0 of 3000 for the named design with masks, 90,859 honest events.
- H3 strict is refuted: plain deletion diverges on writes concurrent with a
  marker and below its cutoff (6, 3, 3 per 1000). With a (cutoff,
  coordinates) mask per marker: 0 failures. The mask is the purge residue.
- Retirement needs no evidence: dropping a dead identifier's tokens and
  `known` immediately, with frontier evidence, or with descendant evidence
  all give 0 failures; the merge re-learns `known` from stale branches. The
  position register must be kept (35 to 41 failures per 1000 when dropped).
- D1 is load-bearing for retirement: under `--legacy-undo` immediate
  retirement fails 53 of 1000 and descendant 2 of 1000; the baseline is 0.
- The roster acknowledgement protocol is therefore not needed by the
  materialised design for convergence, masking, or retirement.

New decision D2 (open): mask or keep a write concurrent with a purge and
below its cutoff. The harness follows the current model (mask).

S3 additions: under D2 no purge state is needed (Section 12 supersedes the
mask); the retirement rule "drop tokens and `known` when dead, keep the
register" is part of the design.

## 11. S2 results

`Sal/MRDTs/Instances/AegisSheetRetentionSPOT.lean` pins the four witnesses
against the current model with `native_decide`: legality of every step,
equality of the live sheets, the PASS observation, and a FAIL companion
(eager re-anchoring, remove-wins, the no-revival reading of undo). Theorems:
`dead_position_load_bearing_for_ranges`, `eager_reanchoring_refuted`,
`dead_position_load_bearing_for_revival`, `remove_wins_refuted`,
`undo_revives_later_removal`. Axioms: `propext`, `Classical.choice`,
`Quot.sound`, `Lean.ofReduceBool`. Listed in
`Metatheory/NegativeLedger.lean`, which builds. Compiled with `lake lean` in
an isolated build directory sharing only the Mathlib packages, because the
main checkout has uncommitted edits to 28 Lean files (including
`AegisSheet.lean` and a deleted `InteractionSPOT.lean`) whose oleans do not
match the committed sources this branch builds on.

Coordination note: the SPOT file uses the fixture helpers `axisEvent`,
`cellEvent`, `rangeEvent`, `undoCellEvent`, `base`, `baseCell`, `r0`, `r1`,
`r2`, `c0` from `AegisSheet.lean`, and the ledger edit sits next to the
`InteractionSPOT` import. If the pending refactor renames or removes these,
this commit needs a follow-up when it is merged.

## 12. D2 results

Reference switched to the covered-set purge clause (D2). Three seeds of 1000:

- Plain deletion (no stored purge state): 0 failing executions, including
  461 merges at a virtual base. Covered-set tombstones: 0. Retirement
  (immediate, descendant) on top: 0.
- Compact cutoff mask (current semantics) against the D2 reference: 6, 3, 3
  failures, exactly the concurrent sub-cutoff writes D2 keeps.
- `--legacy-purge` control (cutoff reference, seed 1): cutoff mask 0, plain
  deletion 6, covered set 6.

Why plain deletion suffices: the framework's merge base is canonical for the
exact intersection of the branch histories (`gca_events_of_storeInv`,
`virtualMergeBaseState_canonical`). A purged version that reached the other
branch is therefore in the base and absent from the purging branch, and
`mvr` removes it. The earlier worry about re-delivery through a criss-cross
path avoiding the base does not apply in this framework; it would in a
system whose merge base can be a strict ancestor of the intersection.

Purge residue under D2: none. Retention residue overall: one position
register per identifier ever known, plus the tokens and versions of live
data.

## 13. S3 progress

`Sal/MRDTs/Instances/AegisSheetMaterialised.lean` compiles with no `sorry`
and is listed in `NegativeLedger.lean` as an internal signature without a
complete package. It contains:

- the signature `M`: operations `MOp` (a `Command` plus the killed tokens of
  a removal), state `MState` (known identifiers, tokens, position registers,
  cell versions, range versions, all flat finite sets of tuples), `mupdate`,
  `mmerge` (componentwise `mvr` plus last-writer-wins `posMerge`), and the
  observation `mview` with range resolution;
- the canonical state `canon : Finset Event → MState` of a union-model
  history, using the union model's own `liveAxisTokens`,
  `laterAxisCandidate`, `rangeOverwritten`, and a D2 `cellOverwrittenD2`;
  and the erasure `toM` in the other direction (drop `seen`, attach
  `killsOf`);
- the honesty predicate `Honest` on replay contexts (killed tokens,
  overwritten versions, and covered versions were issued `vis`-before the
  operation naming them);
- the theorem statements `ObservationEquivalence` (purge-free, against the
  union model's `view`), `UpdatePreservesCanon`, and `JoinTarget :=
  JoinOn M Honest`, as `Prop` definitions;
- 45 fixtures: the union model's published-matrix and Figure 1 cases
  replayed through `mmerge` at their common base, the retention witness,
  the D2 purge case, and `canon refBase = base` plus `canon` of the
  edit-versus-remove set equal to its three-way merge.

Proof plan (the queue's route): (1) `canon (insert e E) = mupdate (canon E)
(toM E e)` for honest `e`; (2) any `loOn`-respecting enumeration of a closed
set under `Honest` folds to `canon`; (3) `mmerge (canon (E₁ ∩ E₂)) (canon E₁)
(canon E₂) = canon (E₁ ∪ E₂)` under `Honest` and weak closure, by set
algebra per component (the token case: a token killed on one side only is
absent from the other side by closure); (4) `JoinAt` from (2) and (3) with
the queue's witness enumeration `ρ₀ ++ Δ₁ ++ Δ₂`; (5) `Honest` from
`MintHonest` of an issuance predicate that checks `kills = live tokens`,
`overwrites = active versions`, and the D1 clause. The sequential
certificate then reuses the incremental machine with a representation
relation through `canon`, and S3b follows from (1) and (3).

## 14. S3: the restricted Join is machine-checked

`Sal/MRDTs/Instances/AegisSheetMaterialisedJoin.lean` (1,024 lines, no
`sorry`) proves `m_join_at : Honest C → JoinAt M C` and `joinTarget :
JoinOn M Honest`, with axioms `propext`, `Classical.choice`, `Quot.sound`.
Registered in `NegativeLedger.lean`, which builds.

Structure, following the queue's route:

- A generic *named-removal component* `NR α` (events add entries carrying
  their own timestamp; events remove entries they name) with: the canonical
  content of an enumeration (`canonL`), well-formedness (`Wf`: unique
  timestamps, removals name earlier additions), the snoc and fold lemmas
  (`canonL_snoc`, `fold_canon`), the set-level membership
  (`inSet`), and the observed-remove merge identity `inSet_union_iff`
  under an honesty predicate (`HonestFor`: the adder of a named entry is
  `vis`-before the namer, adders are unique per entry, adder and namer do
  not commute) and weak closure. `NR.mvr_canonL` is the finite form.
- Three instantiations: tokens (`tokNR`), cell versions with D2 purge
  (`cellNR`), range versions (`rangeNR`), each with a step lemma showing
  `mupdate` projects to the component's step, and `HonestFor` derived from
  the signature file's `Honest` plus `ReplayContext.ts_unique`.
- The last-writer-wins register: `posL`, `posL_snoc` (a late smaller
  candidate never displaces the register, a fresh larger one replaces it),
  `pos_fold`, and `posL_union` (the union's maximum is the maximum of the
  sides' maxima, via `exists_max_cand`).
- The grow-only `known` component.
- `m_join_at`: the witness enumeration `ρ₀ ++ Δ₁ ++ Δ₂` with the queue's
  permutation and respects proofs, then `MState.ext'` componentwise.

Two design facts were forced by the proof and are now part of the design:
honesty is stated as "the adder of a named entry is `vis`-before the
namer" (no existential), and well-formedness constrains only entries that
some element actually added, since an overwrite names a timestamp, not a
payload.

Remaining for the package: `IssuanceEstablishes` from an issuance predicate
checking `kills = live tokens`, `overwrites = active versions`, `covered`
entries present, and the D1 clause; then
`ReplayAdequacyCertificate.ofJoinOn`; the sequential certificate through
`canon`; `UpdatePreservesCanon`; `ObservationEquivalence`; `VerifiedMRDT`.

## 15. S3: issuance and replay adequacy are machine-checked

`Sal/MRDTs/Instances/AegisSheetMaterialisedCertificates.lean` (no `sorry`,
axioms `propext`, `Classical.choice`, `Quot.sound`):

- `mApplicable`, the port's issuance predicate at the issuer's materialised
  state: a removal requires the identifier live and names exactly its live
  tokens; a keep-shaped axis update carries no kills, an insert requires an
  unknown identifier, a move a live one; a cell effect (direct or inverse,
  hence the D1 clause) requires both axes live and names exactly the active
  versions of the cell; a range edit names exactly the active versions of
  the range; a purge covers only versions present at its coordinates.
  `generation : Issuance M`.
- `NR.fold_adds`: fold provenance, every entry of a fold's component was
  added by an element of the enumeration, with no well-formedness premise.
- `honest_of_mint : MintHonest M mApplicable C → Honest C.replayContext`:
  each named token, version, or covered entry is present in the issuer's
  state, hence added by an event of the causal past, hence `vis`-before the
  namer, with the adder's timestamp equal to the named one.
- `issuanceEstablishes : IssuanceEstablishes M generation Honest` and
  `replayAdequacy : ReplayAdequacyCertificate M generation` by
  `ReplayAdequacyCertificate.ofJoinOn m_joinOn issuanceEstablishes`.

This is the framework's internal replay adequacy for the port: every version
of every issued ordinary or virtual-merge-base execution has a replay
witness. Registered in `NegativeLedger.lean`, which builds. The
before-image clauses of the union model's guard are not yet part of
`mApplicable`; they are needed by the sequential certificate, not by
replay adequacy.

## 16. S3b, first half: observation equivalence is machine-checked

`Sal/MRDTs/Instances/AegisSheetMaterialisedEquivalence.lean` (no `sorry`,
standard axioms) proves `observationEquivalence : ObservationEquivalence`,
that is `mview (canon E) = view E` for every purge-free union-model history
`E`. Per component: `mLive (canon E) = axisLive E` (known identifiers and
live tokens), `mLiveIds (canon E) = liveAxisIds E`, `mPositions (canon E) =
axisPositions E` (the register entries are exactly the candidates with no
later candidate), `mCellValues (canon E) = cellValues E` (with
`cellOverwrittenD2 = cellOverwritten` on purge-free histories), and
`mRangeValues (canon E) = rangeValues E`. Each bridge turns a Boolean fold
of the union model into an existential over entries of `canon`.

With purges the reference is the D2 view; the union model's `view` masks by
cutoff, so the statement is purge-free by design. Registered in
`NegativeLedger.lean`, which builds.

Remaining for S3b after this section: `UpdatePreservesCanon` (Section 17)
and the fold over concurrent honest enumerations.

## 17. S3b, second half: update preservation is machine-checked

`Sal/MRDTs/Instances/AegisSheetMaterialisedUpdate.lean` (no `sorry`,
standard axioms) proves `updatePreservesCanon : UpdatePreservesCanon`: for
every honest history `E` and event `e` applicable at `E`,
`mupdate (canon E) (toM E e) = canon (insert e E)`.

The statement needed a premise. As first written, over an arbitrary event
set, it is false: such a set may carry overwrites at foreign coordinates
(the union model's overwrite clause is coordinate-blind, the materialised
filter is per coordinate) or causal summaries outside its own timestamps.
`HonestHistory E` (now in `AegisSheetMaterialised.lean`) names four
invariants: every summary lies within `eventTimes E`; timestamps identify
events; every event's metadata is valid against `E`; every purged entry
names a cell event at its coordinate. `HonestHistory.insert` shows an
applicable insertion preserves them, and `HonestHistory.empty` holds, so
every history reached by applicable insertions is honest (`Reach.honest`).

Per component:

- known: `canonKnown (insert e E)` adds the axis key of `e`, and the
  materialised step adds the same.
- pos: a candidate of `e` is later than every existing candidate by the
  clock, so it is installed; an existing entry is shadowed by `e` exactly
  when `e` is a later candidate for its identifier.
- cells and ranges: for every overwritten timestamp `metadataValidB` gives an
  earlier event at the same coordinate or range identity, and timestamp
  uniqueness turns the coordinate-blind clause into the per-coordinate
  filter. A fresh event is overwritten by nothing (`not_*_fresh`). A purge
  removes exactly the covered versions on both sides.
- tokens: `mem_liveAxisTokens_insert`: a token is live after the insertion
  iff it was live before and `e` does not remove its identifier, or `e`
  keeps the identifier at its own timestamp. The purge marker's contribution
  to the union model's keep set is absorbed since every covered entry names
  a cell event already in `E` (`covered_of_applicable`, from
  `purgeApplicable`; an applicable purge is never an undo effect,
  `applicable_purge`). The removal's `kills`, computed as the live tokens at
  the issuing state, kill exactly the tokens the union model's `seen`-based
  removal kills, because every keep time lies in `eventTimes E = e.seen`.

Corollary `Reach.materialised`: for every history reached by applicable
insertions there is a sequence of erased operations (the history's events
at their issuing states, in issue order) whose materialised fold from the
initial state is `canon E`. With Section 16 this is H1 for sequential honest
histories: the materialised replica replaying the erased operations of any
union-model execution in issue order observes exactly the union model's
purge-free view. Registered in `NegativeLedger.lean`, which builds.

Section 18 generalises this to issuing pasts that are proper subsets of
the history, which is what concurrent executions need.

## 18. S3b, concurrent case: issue-ordered histories and the bridge

`update_preserves_canon_of_past` (in `AegisSheetMaterialisedUpdate.lean`,
no `sorry`, standard axioms) generalises Section 17: for an honest history
`E`, a past `P ⊆ E`, an event `e` applicable at `P` with a timestamp fresh
in `E`, `mupdate (canon E) (toM P e) = canon (insert e E)`. Section 17's
theorem is the special case `P = E`. Two components changed:

- pos: the register argument is now a genuine last-writer argument. If a
  later candidate for the identifier already exists in `E`, a latest one
  sits in `canonPos E` (`exists_nolater`, `mem_canonPos_of`), so
  `posInsert` leaves the register alone and `e`'s candidate is excluded on
  the union side; otherwise every existing candidate is strictly earlier
  (freshness), so `e` is installed and shadows them.
- tokens: the removal's `kills` are the live tokens at `P`, while the union
  model removes tokens in `e.seen = eventTimes P`. The bridge is
  `live_past_iff`: a token live in `E` is live in `P` exactly when `P`
  knows its timestamp. A token of the removed identifier that is live at
  `E` but outside the issuer's past is killed by neither model, as
  predicted at the end of Section 17.

`Issued ρ` is the inductive predicate on lists of (event, past) pairs: each
past lies among the earlier events, each timestamp is fresh among the
earlier events' times, each event is applicable at its past. `Issued.fold`:
the materialised fold of the erased operations of an issue-ordered history
is the canonical state of its events. `Issued.honest`: its events form an
honest history.

`AegisSheetMaterialisedBridge.lean` connects this to the union model's
framework executions. `issued_of_version`: for every version of a certified
execution of the union model `D` (ordinary or virtual-merge-base), the
version's event set is enumerated by an issue-ordered history: sort the
events by timestamp (`causal_mono` makes timestamp order respect
visibility) and pair each with its causal past (`pastOf`, from
`MintHonest`); causal closure and support of version event sets come from
`CanonicalConfig`, itself from the union model's all-context Join;
freshness from `timestamps_distinct`, with covered purge timestamps traced
back to cell events in the purge's past. `cross_model`: the materialised
fold of the erased operations is `canon s` for the version's event set `s`,
and on purge-free versions `M.query` of that fold equals `D.query s`.

`verified : VerifiedMRDT M` (in `AegisSheetMaterialisedCertificates.lean`)
completes the framework package with the datatype's own sequential machine
(`spec`: fold of `mupdate`, every list legal, observation `mview`), by
`SequentialCorrectnessCertificate.ofTotal`. It certifies convergence of
every version to the fold and observation through `mview`; it carries no
union-model content by itself. The union model's own package
(`AegisSheetSequential.clientSpec`) uses a materialised sequential state
with causal-origin legality; the materialised design promotes that
sequential state to the replicated state.

All registered in `NegativeLedger.lean`, which builds.

What is proved and what is not, for H1:

- Proved: union model to port. Every certified execution of the union
  model, at every version, is matched by the materialised fold of an
  issue-ordered enumeration, with equal observations on purge-free
  versions (`cross_model`).
- Not proved: port to union model. That every certified execution of the
  port under `generation` (issuance `mApplicable` at the materialised
  state) corresponds to a certified execution of the union model. The
  restricted Join gives that every reachable materialised state is the fold
  of a vis-respecting enumeration of the port's own events, but the port's
  events carry no `seen`, and `mApplicable` lacks the union model's
  before-image clauses (`currentAxisPositions = before`, `cellValues =
  before`, `rangeValues = before`, the purge roster), so the reconstructed
  union-model events need not pass `applicable`. The recipe: strengthen
  `mApplicable` with those clauses (they are decidable on `MState` through
  `mPositions`, `mCellValues`, `mRangeValues`), then show `MintHonest M`
  yields an `Issued` history with `seen := eventTimes` of the past. This
  is the remaining S3b obligation.

Section 19 proves the converse.

## 19. S3b, converse: the port's executions are union-model histories

`AegisSheetMaterialisedConverse.lean` (no `sorry`, standard axioms) proves
`converse`: for every version of a certified execution of the port `M`
under `generation`, ordinary or virtual-merge-base, with no purge event and
with honest undo, there is an issue-ordered union-model history whose
erasure enumerates the version's events, whose canonical state is the
version's state, and whose union-model view is the materialised observation.
With `cross_model` (Section 18) this closes H1 in both directions on
purge-free executions.

Two changes to the port's issuance were needed, in
`AegisSheetMaterialisedCertificates.lean`. `mApplicable` is now
`mEffect ∧ mBefore`: the effect clauses as before (with `kills = ∅` for
every non-removal), and for a direct command the union model's before-image
guards read through the materialised observers: an insert has no
before-image and a position after; a move or removal has
`mPositions = optionFinset before` with a position before; a write has
`mCellValues = before`; a range edit has `mRangeValues = optionFinset before`;
a direct restore is refused. An undo carries no before-image clause: the
union model checks an undo against its event set (`validUndo`), which the
materialised state cannot decide. `UndoHonest C` is the corresponding
premise on the execution: every undo names an operation of the issuer's
causal past, by the same issuer, whose computed inverse it carries. The
port's existing effect clause for writes also applies to inverse writes, so
the port can undo a cell version only while it is the sole active version at
its coordinate; this is stricter than the union model and is recorded as
such.

The proof. The replay witness of a version is not causal (the port's proof
order has visibility edges only between non-commuting pairs), so sort the
events by timestamp. `fold_eq_of_enums`: at an honest replay context two
`loOn`-respecting enumerations of one closed supported set fold to the same
state, componentwise from the Join file's `fold_canon`, `pos_fold`, and
`known_fold` together with their set-level membership lemmas; so the sorted
fold is the version's state. Then align the sorted list, prefix by prefix,
with an issue-ordered history (`Aligned`): each port event is lifted at the
lift of its mint-time past (`liftAt`, `pastList` from `MintHonest`). At each
step the lifted past is issue-ordered (`Issued.restrict`, restriction to a
predicate closed under pasts), its erasure is a sorted enumeration of the
mint-time past, so by fold independence the state `MintHonest` evaluated the
guard at is the canonical state of the lifted past, and `applicable_of_mApplicable`
transfers the guard: freshness and clock from the timestamps, the metadata
from active versions being cell and range events of the past, the direct
guard from `mBefore` through `mLive_canon`, `mPositions_canon`,
`mCellValues_canon`, `mRangeValues_canon`, and two new observer lemmas
`activeCellTimesOf_canon`, `activeRangeTimesOf_canon`, and undo validity
from `UndoHonest`. The erased lifted event is the original port event
because its `kills` are the live tokens of the past (`liveTokensOf_canon`).

What is proved for H1 now:

- union model to port (`cross_model`): every version of every certified
  union-model execution is matched by the materialised fold of an
  issue-ordered enumeration, with equal observations when purge-free;
- port to union model (`converse`): every version of every certified
  port execution without purges, with honest undo, is the canonical state
  of an issue-ordered union-model history with equal observations.

Purges are outside both statements by design: the union model's view masks
by cutoff and the port deletes covered versions (decision D2), so with
purges the two observations differ on concurrent sub-cutoff writes; the
port's purge semantics is specified by `canon` and validated by the
campaign (Section 12), not by an equivalence with the union model.

Section 20 closes the GC item.

## 20. Datatype-state GC for the port: retirement needs no evidence

What the port could collect. Removals take their tokens with them (named
removal), a purge is an ordinary operation deleting covered versions under
D2 (Section 12), and the position register is load-bearing (H2, Section 7
and `RetentionSPOT.dead_position_load_bearing_for_ranges`). The only
metadata left is the `known` entry of an identifier without tokens, which
Section 10 validated can be dropped immediately.

`AegisSheetMaterialisedRetirement.lean` (no `sorry`, standard axioms)
mechanises this as `retirement : StateGCCertificate M generation`, the
framework's datatype-state GC interface, with `Evidence := Unit`,
`EvidenceValid := True`, and `Compatible := True`: retirement needs no
acknowledgement, frontier, or cross-branch condition. The collector
`retire` filters `known` to identifiers with a token
(`retire_keeps_live`: an identifier stays known iff it is live). The
representation relation `Represents c f` says the compact and full states
agree on tokens, register, cells, and ranges; the compact `known` is a
subset of the full one missing only identifiers without tokens; and every
token of the full state names a known identifier (`TokensKnown`, an
invariant of states reached under `generation`, since a write requires both
axes live and an insert adds token and `known` together). Under it every
observation agrees (`Represents.view_eq`), issued updates preserve it
(`update_represents`, using the D1 clause that a write's axes are live so no
dropped identifier gains a token), and three-way merges preserve it
(`merge_represents`: a token of the merged state comes from a branch, whose
compact state therefore knows its identifier). The union model's collector
(`AegisSheetGC.lean`) needs the roster acknowledgements and the compact
marker; the port needs neither, as Section 10 predicted.

The residue is therefore exact: live tokens, live cell and range versions,
and one register entry per identifier ever positioned. Whether the register
can be bounded differently is a design question outside this arc.

On the runtime measurement: the JavaScript runtime has no AegisSheet, so the
measurement in this arc is the Python one (campaign, "Measured: state size
growth"): stored items 122 to 10,076 for the reference against 30 to 192 for
the materialised design over 23 to 176 operations, consistent with quadratic
against linear. A production measurement belongs with a decision to adopt
the port, which is outside this research arc.
