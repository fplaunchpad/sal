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

### Case 2 (metatheory) -- IN PROGRESS
Goal: discharge the multi-replica protocol half so two peers compacting
incomparable cuts can merge across epochs (or a principled refusal condition
that is weaker than "any two distinct epochs"). The #97 summary names the open
obligations: `oq:starlemma`, `oq:epochdag` -- deriving `ContOK`/straggler
declarations from a real delivery protocol, and composing two replicas' epoch
DAGs without the rank-reclaim collision.

Plan (to be refined after reading the #97 Lean + tex):
1. Read the state: `Sal/.../EmbedRGA_Recoding.lean`, `EmbedRGA_HonestyRebase.lean`,
   the `naive_composition_collides` countermodel, and the tex Part II storage
   sections (`def:spm` through the `(*)` cluster). Pin down the EXACT open
   obligations and why the naive composition collides (the shape of the
   countermodel tells us what a sound composition must avoid).
2. Decide the target theorem: a `CompatChain`/epoch-DAG that composes two
   re-codings at incomparable cuts, OR a decidable predicate that says when two
   epochs ARE composable (a common refinement exists) vs not.
3. Prove it (or reduce to a clearly-stated residual), keeping the kernel clean.
4. Only THEN wire the JS: lift Case 2's refusal to the proven condition.
   (Standing rule: JS mirrors PROVEN theory -- do not ship Case 2 in JS ahead of
   the proof.)

Before touching Lean: read `AgentNotes.md` (RGA attempt index) and confirm which
files are the live #97 artifacts.
