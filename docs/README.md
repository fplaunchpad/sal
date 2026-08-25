# Working papers

This directory contains two anonymous, independently buildable working drafts
that accompany the Lean and JavaScript development in this repository.

- `framework-paper/main.pdf` is the self-contained formal narrative. It covers
  the corrected MRDT metatheory, issuance and sequential certificates,
  virtual LCAs, distributed commit-history GC, and composition with optional
  datatype-state GC. `framework-paper/claim-ledger.md` maps every load-bearing
  paper claim to its Lean source.
- `collaborative-editing-paper/main.pdf` covers RGA, EmbedRGA,
  SidedEmbedRGA/FugueMax, Peritext, state compaction, the runtime, and the
  evaluation. It is supporting application material, not a second standalone
  submission narrative.

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
