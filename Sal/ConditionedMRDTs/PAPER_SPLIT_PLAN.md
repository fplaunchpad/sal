# Two-paper split map

This file is the durable editorial contract for splitting `sal-mrdts.tex`.
The monolith remains the canonical source while the split is stabilized. The
two standalone entry points are:

- `papers/metatheory/main.tex` — Paper A, **A Corrected and Conditioned
  Metatheory for Mergeable Replicated Data Types**.
- `papers/sequences/main.tex` — Paper B, **Verified Sequence MRDTs: Embedded
  Chains, Compaction, and Runtime**.

Both entry points must build independently with Tectonic. Content shared by
the two papers stays single-source; paper-specific selection uses
`\salPaperA`, `\salPaperB`, and `\salSplitPaper`. The consolidated manuscript
must continue to build without defining any selector.

## Ownership map

| Current material | Owner | Editorial role |
|---|---|---|
| Correctness stack | Shared | Short interface diagram; tailor surrounding prose per paper |
| Part I: MRDT definitions through conditioned metatheorem | A | Central corrected theory and countermodels |
| Part I: factored discharge, products, and observational quotients | A | Higher-level doctrine and composition story |
| Part I: virtual LCAs, commit GC, stability | A | Runtime-facing metatheory |
| Part II: embedded-chain family | B | Core sequence construction |
| Part II: maximal non-interleaving and chain-price lower bound | B | Semantic and representation results |
| Part II: recoding, compaction, run tables, marks | B | Storage layer |
| Part III: sequential specifications | B | Independent intent argument and negative controls |
| Part IV: runtime and evaluation | B | System realization, benchmarks, SMT tooling |
| Open questions | Split | Each paper retains only questions in its ownership domain |
| Mechanization map | Split | Each paper retains its own rows; shared foundations may be repeated |

## Dependency contract

Paper B consumes Paper A through a compact stated interface: ternary MRDT
signature, canonical history state, contextual Join adequacy, honest
reachability, observational equality, and stability epochs. It must not rely
on Paper A section numbers. Paper A may use the sequence work only as a named
application; detailed construction and evaluation belong to Paper B.

There is no external BibTeX database in the current manuscript. Citations are
prose links/names, so the split has no bibliography-file dependency yet.
TikZ figures and notation are source-local and therefore remain available to
both selected builds. A later source-file extraction may move the common
preamble into `papers/shared/` without changing this ownership contract.

## Completion checklist

- [x] Durable section-by-section ownership and dependency map.
- [x] Independently selectable Paper A and Paper B entry points.
- [x] Paper-specific titles and abstracts.
- [x] Replace the shared correctness-stack prose with paper-specific framing.
- [x] Give Paper B a self-contained statement of the Paper A interface.
- [x] Split the open-work and mechanization appendices by ownership.
- [x] Resolve cross-paper references through explicit local interface anchors.
- [x] Build the monolith and both standalone papers with no undefined refs.

The later claim-synchronization, expanded audit-table, and prose-compression
pass is Priority 10 in the canonical backlog.
