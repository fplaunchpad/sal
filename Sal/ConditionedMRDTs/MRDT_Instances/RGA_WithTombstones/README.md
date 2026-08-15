# Tombstone RGA certificate

`RGA_WithTombstones.lean` proves the flat convergence result. `RGA_Intent.lean`
adds the independent intent layer without importing Shesha or the refuted
rehoming development.

The generation guard requires:

- root or already-present anchors, with an earlier anchor timestamp;
- globally fresh insertion timestamps and element identifiers;
- no resurrection of a grave identifier;
- removal only of a previously inserted, still-live identifier.

`rgaSequentialSpec` stores finite insertion and grave sets independently of the
implementation's Boolean characteristic functions. `rgaSequence` gives their
deterministic client list: timestamp-ordered insertions are placed after their
anchors and graves are filtered. `rgaSequentialSound` machine-checks the
representation relation, and `rgaHistorySequentialRefinement` exposes it under
the exact prefix guard discipline. `rgaUnified` combines this intent theorem,
the existing flat Join theorem, the public generation contract, and trivial
client safety (the semantic list claim is carried by the refinement, not by a
fabricated safety invariant).

Run `sh scripts/check-rga-tombstone-intent.sh`. The Lean module contains PASS
controls for add/remove and FAIL controls for missing anchors, premature
removal, and timestamp reuse.
