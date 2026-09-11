# AegisSheet Scala audit

## Result

The Scala artifact at Bismuth commit `dd4c614` does not implement all published
AegisSheet semantics. Executable adversarial tests found three independent
failures:

1. Move undo uses stale numeric indices. It violates two cells of Table 4.
2. Range undo stores stale numeric coordinates. A concurrent insertion changes
   the range's stable endpoints.
3. Range crossing validation can leave an invalid range ID live. The public
   `listRanges()` method then throws `NoSuchElementException`.

These failures do not refute convergence of the merge kernel. The upstream
tests, 216 exhaustive one-step merge combinations, and 500 deterministic
multi-step merge-law trials did not find a commutativity, idempotence, or
associativity failure.

## Enquiry

**Goal:** Check whether the published merge, selective-undo, range, and purge
semantics agree with the Scala implementation.

**Candidate claim:** Every Table 3 and Table 4 outcome and every stated range
and purge behavior is implemented by the Bismuth artifact.

**Falsifier:** A concrete trace constructed from the paper that returns a
different observation, retains an object that the paper discards, or throws
from a public query.

**Formal oracle:** The Lean model in `Sal/MRDTs/Instances/AegisSheet.lean`
provides named policy fixtures. It does not establish Scala equivalence.

**Reality oracle:** Scala.js execution of the Bismuth implementation at commit
`dd4c614`, using the operation sequences and expected outcomes from Tables 3
and 4 and the range/purge prose.

## Executed scope

The audit ran with Java 21, sbt 2.0.7, Scala 3.9.0-RC6, and the `exWeb` Scala.js
test target.

The permanent regression source is
`audits/aegissheet/AegisSheetRegressionSuite.scala`. From the Bismuth checkout,
run it as an additional test source:

```text
sbt 'set exWeb / Test / unmanagedSourceDirectories += file("../../audits/aegissheet")' \
  'exWeb/testOnly ex2025tabular.AegisSheetRegressionSuite'
```

| Check | Result |
|---|---:|
| Existing upstream AegisSheet tests | 69 passed |
| One-step three-branch merge combinations | 216 passed |
| Deterministic multi-step merge-law seeds | 500 passed |
| Purge plus concurrent edit | Passed |
| Purge plus later local row undo | Passed |
| Table 4 move/remove control | Passed |
| Table 4 move/insert | Failed |
| Table 4 move/move | Failed |
| Range undo plus concurrent insertion | Failed |
| Range crossing plus `listRanges()` | Threw |

Passing randomized tests are validation on this test scope, not a proof of the
merge laws.

## Bug 1: Move undo loses stable identity

`UndoRecordingSpreadsheet.moveRow` and `moveColumn` record only the original
source and target indices. The undo closure applies those indices to the
post-merge sheet:

```scala
pushUndo { s =>
  s.moveRow(if sourceIdx < targetIdx then targetIdx - 1 else targetIdx, sourceIdx)
}
```

A concurrent insertion or move changes which row occupies the recorded index.
The closure then moves the wrong stable row.

### Counterexample: move versus insert

Start with `[r0, r1, r2]`.

1. Replica A moves `r0` to the end.
2. Replica B concurrently inserts `x` immediately after the old position of
   `r0`.
3. Merge both replicas.
4. Replica A undoes its move.

Table 4 requires `[r0, x, r1, r2]`: revert the move without changing the
insert's position. Scala returns `[r2, x, r1, r0]`.

### Counterexample: move versus move

Start with `[r0, r1, r2, r3]`.

1. Replica A moves `r0` to the end.
2. Replica B concurrently moves `r0` to a different position.
3. Merge and let replica A undo its move.

Table 4 says “revert both,” which returns the initial order. Scala returns
`[r3, r1, r0, r2]`.

The nearby move/remove Table 4 control returns the initial order as published.
The defect depends on a concurrent positional change, not on every move undo.

## Bug 2: Range undo restores the wrong stable endpoints

`UndoRecordingSpreadsheet.removeRange` records `Range` coordinates and later
passes those old indices to `addRange`. It does not record the four stable row
and column IDs or the marker state.

Start with a range over rows 1 through 2.

1. Replica A removes the range.
2. Replica B concurrently inserts a row at index 0.
3. Merge both replicas.
4. Replica A undoes the range removal.

The original endpoints now occupy rows 2 through 3. Scala restores the range at
rows 1 through 2, attaching it to different stable rows.

The paper does not include range operations in Table 4, but it states that the
undo feature integrates the other spreadsheet operations and that ranges track
stable structural edits. This trace violates that combined contract.

## Bug 3: Crossing a range leaves a live invalid range

`Range.validAfterSwapping` receives no row/column axis. It compares `source`
against row indices before column indices, rewrites untouched coordinates, and
does not account for index shifts caused by a move. `moveRow` and `moveColumn`
use this result to decide whether to remove the range ID.

Start with a range from `(1, 1)` to `(3, 3)`. Move its last column from index 3
to index 1. The end marker now precedes the start marker, so the paper requires
the range to be discarded. Scala produces this behavior:

- `getRange(id)` returns `None` because the markers are crossed;
- the replicated range ID remains live;
- `listRanges()` evaluates `None.get` and throws `NoSuchElementException`.

This is both a semantic mismatch and a public API failure.

## Purge finding

The audit did not reproduce a Scala purge correctness bug on the tested scope.
The implementation's observed-remove map records purge as a semantic removal:

- a concurrent unseen edit survives and revives the row with the new value;
- a cell observed by purge does not return after undo restores its row.

This agrees with the artifact documentation, which explicitly says purge
changes semantics. It remains distinct from silent state GC, and it does not
provide the stable-cut protocol or bounded retained-metadata theorem required
by Sal's state-GC interface.

## Required repairs

1. Record the moved stable row or column ID and stable placement anchors in the
   undo entry. Resolve its current index only when applying undo.
2. Record range marker state or stable endpoint IDs, not rendered coordinates.
3. Split range validity into row- and column-specific functions. Evaluate the
   post-move marker order, including index shifts, before retaining `rangeIds`.
4. Make `listRanges()` total even if an invariant is violated. Using `flatMap`
   prevents a query crash, but does not replace the range-ID invariant repair.
5. Re-run every Table 4 cell and the range regressions before claiming Scala
   equivalence. Then update the Lean reality boundary; the current Lean
   convergence theorem does not certify these undo closures.
