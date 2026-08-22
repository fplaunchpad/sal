# Working papers

This directory contains the two anonymous long-form working drafts that
accompany the Lean and JavaScript development in this repository.

- `framework-paper/main.pdf` covers the corrected MRDT metatheory, generation
  and safety certificates, virtual LCAs, distributed commit-history GC, and
  composition with optional datatype-state GC.
- `collaborative-editing-paper/main.pdf` covers RGA, EmbedRGA,
  SidedEmbedRGA/FugueMax, Peritext, state compaction, the runtime, and the
  evaluation.

Both wrappers select sections from `working-papers.tex`. Build them from the
repository root with:

```sh
./scripts/check-working-papers.sh
```

The script builds each wrapper independently and rejects references to the
retired `Sal/ConditionedMRDTs` tree. The current Lean theorem inventory is
`Sal/MRDTs/Metatheory/RefactorLedger.lean`.
