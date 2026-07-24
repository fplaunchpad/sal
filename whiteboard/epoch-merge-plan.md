# Cross-epoch merge: living plan

Independent GC + convergence. Two cases behind "a cross-epoch merge":

- **Case 1** -- one compactor, a straggler with local edits on a single epoch
  line. The straggler lifts its edits into the new epoch through the epoch's
  translate. Backed by #97 (`eRecode_ra_transport`, `eRecode_reads_identical`).
- **Case 2** -- two peers compacting INCOMPARABLE cuts. Composing two
  independent re-codings; #97 proved the NEGATIVE (`naive_composition_collides`,
  id-addressing breaks after epoch one). Open metatheory.

## Status

### Case 1 (JS) -- DONE (2026-07-24)
Landed in `runtime/src/replica.js`, faithful to #97:
- `#mergeStates` / `#liftState` lift the lower-epoch side + LCA base to
  `eT = max(epochs)` via `remapState` through per-epoch translate maps; identity
  when nobody compacted (ordinary merges unchanged).
- The translate is a non-serializable closure, so a peer that INGESTED a
  compaction recomputes it from the compact commit's parent state + the CUT.
  `compactStable` stores the cut (`compactCut`), `delta` and the persistence
  records (`p2p-demo/src/records.js`) ship it as a non-hashed hint, and
  `#absorbEpoch` recomputes `compact(parent, cut)` and trusts the translate only
  on a fingerprint match (forged cut caught).
- `epochOwner` / `epochConflict` mark an epoch CONFLICTED when a second, distinct
  compaction claims it, so Case 2 lifts refuse instead of mislifting.
- Verified: `test/crossepoch.test.js` (embed + peritext lift == never-compacted
  control; survives persist/rebuild; tampered cut refused; Case 2 refused) and
  `test/replica.test.js` (Case 1 converges, Case 2 refused). runtime 125, p2p 47.
- Note: multi-step lift (`to - from >= 2`) is defensive; a rostered straggler
  advances one epoch per sync, and a dark straggler caps the compactor's cut, so
  a natural 2-epoch-in-one-merge lift is not reachable. Composition is correct by
  construction (the `#liftState` loop) but not separately fixture-tested.

### Case 2 (metatheory) -- OWNED BY ANOTHER AGENT (do not collide)
The multi-replica protocol half (two peers compacting incomparable cuts,
composing two epoch DAGs without the rank-reclaim collision) is being worked by
a SEPARATE agent on the Lean side. The live #97 artifacts are
`Sal/ConditionedMRDTs/MRDT_Instances/EmbedRGA/`:
`EmbedRGA_Recoding.lean`, `EmbedRGA_HonestyRebase.lean`, `EmbedRGA_CompatChain.lean`,
`EmbedRGA_MultiEpoch.lean` (plus `naive_composition_collides` as the countermodel).

Coordination: this plan's JS side does NOT touch those files. When the Case 2
metatheory lands (a composition theorem or a decidable "composable epochs"
predicate weaker than "any two distinct epochs"), the JS follow-on is:
- lift `#mergeStates`/`#liftState`'s refusal to the proven condition (today it
  refuses on `epochConflict`); and
- if composition needs a translate BETWEEN two incomparable re-codings, extend
  `#absorbEpoch` to obtain/recompute it the same content-gated way Case 1 does.
Standing rule (see the verified-JS memory): JS mirrors PROVEN theory -- do not
ship Case 2 in JS ahead of the proof.
