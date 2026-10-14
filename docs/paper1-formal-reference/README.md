# Paper-aligned formal reference

[Read the PDF](main.pdf). Its Sections 3–6 follow the same formal sections of
Overleaf snapshot `0450d48` (8 October 2026). Appendix A maps the manuscript to
this reference; Appendix B maps the reference to Lean declarations.

The reference uses the concrete equality development on `paper1`. Source links
use proof baseline `07fe525` for unchanged files and `paper1` for revised files.
`PaperPresentation.lean` supplies the direct sequential lifting theorem.

From the Sal repository root:

```sh
python3 docs/paper1-formal-reference/check-sources.py /tmp/sal-reference-check.lean
lake build Sal.MRDTs.Paper1.PaperPresentation
lake env lean /tmp/sal-reference-check.lean
tectonic -X compile docs/paper1-formal-reference/main.tex
```

The script regenerates the source appendix from the four `*-sources.tsv` files
and emits a check for every listed declaration. Repository gates additionally build
and audit the theorem ledger. When changing statements or numbering, update
[the manuscript reconciliation note](../paper1-formalism-reconciliation.md),
rebuild the PDF, and inspect its rendered pages.

The 13 October revision adopts Kartik's split formulation in Definitions 4.5
and 4.8: operation-distinct `rc-non-comm` plus equal-operation self-commutation,
with the same eligible-event and state domains. `SplitPolicy.lean` supplies the production split interfaces and their checked
equivalence to the combined contracts. `SplitSoundness.lean` exposes soundness
through these interfaces; the source appendix checks the production declarations. The remaining manuscript mapping
retains the October 8 baseline.

The sole bounded-counter example is the published Balegas matrix/max design
(Example 6.7); the Neem flags follow as Example 6.8. The current source appendix
resolves 113 declarations across 30 reference anchors.
