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
