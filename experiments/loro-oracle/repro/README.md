# Plain-Loro reproductions

One self-contained script per defect shape, importing only `loro-crdt`
(1.17.1 pinned). Each prints the observed and expected documents and exits
non-zero when the defect shows and the control does not. `run-all.mjs`
runs the five.

    npm install --ignore-scripts && node run-all.mjs

| Script | Shape | Reproduces on 1.17.1 |
|---|---|---|
| `L-001.mjs` | user 1 bolds `a` (expand after) while user 2 types `h` before it; `h` is bold with one assignment of peer ids and plain with the other | yes |
| `L-002.mjs` | single replica: highlight `ab` (expand both), remove the highlight, type `X` at 0; `X` is highlighted | yes |
| `L-003.mjs` | single replica: link `abc` (expand none), unlink `b`, type `X` at 1; `X` is linked; control with bold is as expected | yes |
| `L-004.mjs` | single replica: link `a` and `b` separately with one value (displayed as one link), type `X` at 1; `X` is not linked; control with one link over `ab` links `X` | yes |
| `L-005.mjs` | two replicas: user 1 bolds `y` while user 2 makes it superscript; after receiving user 2's change, user 1 types `X` before `y`; `X` is neither, and superscript with the keys swapped | yes |

Measured on Node 26.3.1 on 2026-10-29.

Posted upstream on 2026-10-29: L-001 as a comment on loro-dev/loro#1009,
L-002 to L-005 as loro-dev/loro#1240. `upstream-drafts.md` holds the posted
texts.
