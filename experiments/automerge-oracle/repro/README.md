# Plain-Automerge reproductions

One self-contained script per defect shape, importing only
`@automerge/automerge` (3.5.0 pinned). Each prints the observed document,
the control's document and the expected one, and exits non-zero when the
defect shows and the control does not. `run-all.mjs` runs the three.

    npm install --ignore-scripts && node run-all.mjs

| Script | Shape | Reproduces on 3.5.0 |
|---|---|---|
| `A-001.mjs` | non-expanding start of a bold covers a concurrently typed character when the bold's counter is larger; control without the counter-raising delete | yes |
| `A-001-link.mjs` | non-expanding end of a link covers a concurrently typed character when the inserter's counter is larger; control without the counter-raising insert | yes |
| `A-002.mjs` | single replica: bold `q`, link `q`, delete `q`, type `i`: `i` is bold; control without the link | yes |

Measured on Node 26.3.1 on 2026-10-29.

Posted upstream on 2026-10-29: A-001 (both shapes) as automerge/automerge#1649,
A-002 as automerge/automerge#1650. `upstream-drafts.md` holds the posted texts.
