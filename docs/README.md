# Working papers

This directory contains two anonymous, independently buildable working drafts
that accompany the Lean and JavaScript development in this repository.

- `framework-paper/main.pdf` covers the corrected MRDT metatheory, generation
  and safety certificates, virtual LCAs, distributed commit-history GC, and
  composition with optional datatype-state GC.
- `collaborative-editing-paper/main.pdf` covers RGA, EmbedRGA,
  SidedEmbedRGA/FugueMax, Peritext, state compaction, the runtime, and the
  evaluation.

Each paper has its own `main.tex`; they share only `paper-preamble.tex`. Build
them from the repository root with:

```sh
./scripts/check-working-papers.sh
```

The script builds the paper-specific Lean ledger, rejects retired framework
names and non-anonymous metadata, and then builds both PDFs. The complete
production theorem inventory is `Sal/MRDTs/Metatheory/RefactorLedger.lean`;
the declarations cited by the papers are gated by
`Sal/MRDTs/Metatheory/PaperLedger.lean`.

`production-packaging.md` records the formal-oracle enquiry behind the typed
`PackagedMRDT` release boundary, the separate negative ledger, and the runtime
evidence manifest.
