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
  sequential theorem, virtual-LCA construction, and GC developments depend
  only on ternary merge. Reused binary-CRDT infrastructure can consume a
  derived projection whose binary merge is `D.merge D.init`.
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
dependency graph. It does not claim that every historical state-based CRDT
formalization should remove binary merge. `CRDTSig` remains available for the
older binary metatheory and countermodels; only the `MRDTSig` implementer
interface is minimized.
