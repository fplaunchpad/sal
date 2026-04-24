# Emulation-paper plan

Research-paper write-up of the `Sal/Emulation/` formalisation. Lives
here to keep paper work visible in the repo without cluttering the
Lean subtree.

## Files

- `main.tex` — single-file LaTeX source.
- `refs.bib` — bibliography.
- `Makefile` — `make` builds the PDF via `latexmk`.

## Sections

1. Introduction — the state/op-based verification gap.
2. Background — state vs op CRDTs, 24 VCs, weak simulation.
3. Architecture — 11-step decomposition, dependency graph.
4. Bridge theorem — 24 VCs ⟹ RA-lin. Apply closed, Merge in progress.
5. Emulation and transfer — weak sim, canonical G.
6. Smoke test — Grow-Only Set end-to-end.
7. Design decisions & discussion.
8. Related work.
9. Conclusion & future work.

## Framing

- Progress-report paper, not "solved it" paper.
- Emphasise: architecture, closed sub-lemmas, honest effort estimates.
- Theorems typeset in LaTeX math; Lean code listings only where
  concreteness matters (e.g. `Configuration` definition, `SatisfiesVCs`
  structure).

## References to cite

- Sal paper (Ramesh, Soundarapandian, Sivaramakrishnan, arXiv:2502.19967).
- Liittschwager et al. (ICFP '25, arXiv:2504.05398).
- Neem (Soundarapandian et al., OOPSLA '25).
- Zeller et al., Gomes et al., Timany/Trillium, Nieto/Aneris (CRDT mechanization prior work).
- Milner (weak bisimulation).

## Status

Drafted: this plan + main.tex scaffold. TODO: fill in sections, build.
