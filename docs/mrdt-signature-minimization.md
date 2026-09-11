# Minimize the MRDT merge interface

## Result sought

Expose one merge operation to an MRDT implementer:

```text
merge : State -> State -> State -> State
```

The arguments are the common-ancestor state, left branch state, and right
branch state. The public interface must not also request a binary merge or a
law relating two independently supplied implementations.

## Enquiry

- **Goal:** Remove the independent binary merge and its compatibility field
  from `MRDTSig`, and call the sole ternary operation `merge` throughout the
  live MRDT development.
- **Candidate claim:** The production MRDT semantics, convergence proof,
  sequential theorem, virtual-merge-base construction, and GC developments depend
  only on ternary merge. Generic replay lemmas consume the merge-free
  `UpdateSig` projection. Retained binary lemmas request a separate
  `HistoricalBinaryMerge` capability, whose MRDT instance is `D.merge D.init`.
- **Falsifier:** A live MRDT theorem or instance that requires an independently
  supplied binary merge whose behavior cannot be defined as the initial slice
  of ternary merge.
- **Formal oracle:** `lake build Sal.MRDTs.Metatheory.RefactorLedger`, followed
  by `scripts/check-mrdt-refactor.sh`.
- **Reality oracle:** The paper-level operational semantics performs every
  ordinary and virtual merge with an explicit ancestor state. Runtime tests
  and paper builds check that the implementation-facing and explanatory
  interfaces remain synchronized.

## Evidence boundary

The successful `RefactorLedger` build establishes that binary merge is
redundant in the current Lean
dependency graph. `UpdateSig` remains as a merge-free proof-level algebra for
generic replay lemmas; it is derived from `MRDTSig` in the live MRDT development
and defines no second implementer interface or execution semantics. The binary
countermodels and lemmas carry `HistoricalBinaryMerge` explicitly.
