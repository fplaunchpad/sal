# Working papers

This directory contains two anonymous working papers and one independently
buildable formal reference that accompany the Lean and JavaScript development
in this repository.

- `framework-paper/main.pdf` is the self-contained formal narrative. It covers
  the corrected MRDT metatheory, issuance and sequential certificates,
  virtual merge bases, distributed commit-history GC, and composition with optional
  datatype-state GC. `framework-paper/claim-ledger.md` maps every load-bearing
  paper claim to its Lean source.
- `collaborative-editing-paper/main.pdf` covers RGA, EmbedRGA,
  SidedEmbedRGA/FugueMax, Peritext, state compaction, the runtime, and the
  evaluation. It is supporting application material, not a second standalone
  submission narrative.
- `formal-reference/main.pdf` presents the complete public MRDT formalism in
  bottom-up semantic dependency order: primitive types and operational rules,
  set-relative replay and Join, issuance and client-facing correctness,
  canonical virtual merge bases, and the two GC refinements. Its synchronized
  declaration gate is `Sal/MRDTs/Metatheory/FormalReferenceLedger.lean`.

Each document has its own `main.tex`; the two papers share
`paper-preamble.tex`. Build all three from the repository root with:

```sh
./scripts/check-working-papers.sh
```

The script builds the paper and reference Lean ledgers, rejects retired
framework names and non-anonymous metadata, and then builds all three PDFs.
The complete production theorem inventory is
`Sal/MRDTs/Metatheory/RefactorLedger.lean`. Paper declarations are gated
by `Sal/MRDTs/Metatheory/PaperLedger.lean`; reference declarations are gated
by `Sal/MRDTs/Metatheory/FormalReferenceLedger.lean`.

`production-packaging.md` records the formal-oracle enquiry behind the typed
`PackagedMRDT` release boundary, the separate negative ledger, and the runtime
evidence manifest.

`historical-vcs-join-audit.md` records the checked counterexample showing that
the archived ternary 24-VC bundle does not imply the corrected set-relative
ternary Join lemma. It also separates the same-policy research statement from
the framework's current policy-erased `Join` declaration.
