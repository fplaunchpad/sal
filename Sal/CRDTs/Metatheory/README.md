# Sal/CRDTs/Metatheory — the RA-linearizability metatheorem for state-based CRDTs

Mechanization (and correction) of the Neem soundness meta-theorem
(arXiv:2502.19967, OOPSLA 2025) in its **binary-merge / CRDT**
specialization: *which verification conditions make every reachable
configuration RA-linearizable?* The investigation refuted the paper's
original proof route, built a repaired route (canonical states + the Join
Lemma), and mapped the exact boundary of which VC bundles suffice.

The chronological journal is [`FINDINGS.md`](FINDINGS.md) (findings
**A1–A9**), continued in [`A10_DRAFT.md`](A10_DRAFT.md),
[`A11_DRAFT.md`](A11_DRAFT.md) and [`A12_DRAFT.md`](A12_DRAFT.md). The
paper-style write-up of the arc is
[`docs/metatheory-note/joinpeel-note.tex`](../../../docs/metatheory-note/joinpeel-note.tex).

## Headline results

| Result | Theorem(s) | File |
|---|---|---|
| **End-to-end metatheorem (A9):** `CoreVCs + JoinPeelVCs ⇒` every reachable configuration RA-linearizable | `ra_linearizable_of_core_join` | [`RA_Lin_Of_Join.lean`](RA_Lin_Of_Join.lean) |
| **End-to-end via the CD ladder (A11):** `CoreVCs + ACI + update-inflation + CD ⇒` RA-linearizable | `join_lemma_of_cd`, `ra_linearizable_of_core_lattice_cd` | [`JoinLemma_Of_CD.lean`](JoinLemma_Of_CD.lean) |
| **(b′) refuted (A10):** CoreVCs + full bounded-semilattice merge (ACI) does **not** imply RA-linearizability — fails on a reachable execution | `coreVCs_lattice_insufficient`, `ra_linearizability_fails_for_lattice_CRDTs` | [`Assoc_CounterModel.lean`](Assoc_CounterModel.lean), [`Assoc_CounterModel_Reachable.lean`](Assoc_CounterModel_Reachable.lean) |
| **Paper's convergence lemma is false (A1):** the §5 blocker lemma has a machine-checked countermodel; the `shared_peel_1op` VC is false for OR-set-style RDTs | `convergence_over_backward_closed_subsets_false`, `AWSet_shared_peel_1op_false` | [`Convergence_CounterModel.lean`](Convergence_CounterModel.lean) |
| **The repair (A2, A5–A6):** set-relative linearization order `loOn`, convergence on any set, canonical states σ(E), the Join Lemma from the peel identities | `loOn`, `convergence_on`, `IsCanonicalState`, `CoreVCs`, `JoinPeelVCs`, `join_lemma_of_peel`, `joinPeelVCs_of_all_comm` | [`Merge_Linearization_Set.lean`](Merge_Linearization_Set.lean) |
| **AWSet discharge (A7):** the Join Lemma holds for a non-trivial-`rc` CRDT | `AWSet_coreVCs`, `AWSet_joinPeelVCs` | [`Convergence_CounterModel.lean`](Convergence_CounterModel.lean) |
| **CD discharge for AWSet (A11):** the causal-delta VC at <½ the peel-route proof cost; commuting class free | `AWSet_cdVC`, `AWSet_ra_linearizable_via_cd`; `cdVC_of_all_comm` | [`CD_AWSet.lean`](CD_AWSet.lean), [`JoinLemma_Of_CD.lean`](JoinLemma_Of_CD.lean) |
| **CD is exact and minimal (A12):** under `CoreVCs + LatticeVCsPlus`, `CDVC ↔ JoinLemma`; no strictly weaker bridge VC exists — (b″) *is* the metatheorem question | `joinLemma_iff_cdVC`, `cdVC_weakest`, `cdVC_of_joinPeelVCs` | [`CD_Exact.lean`](CD_Exact.lean) |

## The VC-bundle ladder

```
CoreVCs                      ✗  (A8 — AWSetX separator, hand-verified; FINDINGS.md)
  + ACI (assoc/comm/idem)    ✗  reachably non-RA-linearizable (A10 — AWSetF)
  + update-inflation         ?  open question (b″) — ≡ CDVC (A12, joinLemma_iff_cdVC)
  + CD (causal-delta bound)  ✅  end-to-end (A11); exact & minimal residual (A12)
```

Tight from below in both directions: drop associativity → AWSetX (A8);
drop inflation → AWSetF (`AWSetF_not_latticeVCsPlus`). The residual open
question **(b″)** — is `CDVC` derivable from `CoreVCs + LatticeVCsPlus`? —
is *equivalent* to the unconditional metatheorem (A12: `CDVC ↔
JoinLemma`, and any sufficient bridge VC implies `CDVC`). Both attack
routes hit characterized walls — the mutual-induction route is circular
at two identified case shapes; the countermodel space is narrowed by a
forcing dichotomy to non-atomic-lattice states — see the hand-off
question in `A12_DRAFT.md` §4.

## Files

Lean (build with `lake build Sal.CRDTs.Metatheory.<Module>`):

- [`RA_Linearizability.lean`](RA_Linearizability.lean) — `IsRALinearizable`
  (paper Def-lin), `lo`, the paper's 24-VC bundle `SatisfiesVCs` (+ the 5
  implicit extras the mechanization surfaced). 0 sorries.
- [`Merge_Linearization.lean`](Merge_Linearization.lean) — the paper's
  original BottomUp-{0,1,2}-OP route. **Superseded** (the route is
  unsound as written — A3); kept as the record. 2 legacy sorries,
  unprovable as posed.
- [`Merge_Linearization_Set.lean`](Merge_Linearization_Set.lean) — the
  corrected core (see table). 0 sorries.
- [`RA_Lin_Of_Join.lean`](RA_Lin_Of_Join.lean) — end-to-end bridge (A9).
  0 sorries.
- [`Convergence_CounterModel.lean`](Convergence_CounterModel.lean) —
  `AWSet`, the A1 countermodels, the A7 discharge. 0 sorries.
- [`Assoc_CounterModel.lean`](Assoc_CounterModel.lean) /
  [`Assoc_CounterModel_Reachable.lean`](Assoc_CounterModel_Reachable.lean)
  — `AWSetF`, `LatticeVCs`, the A10 refutation of (b′). 0 sorries.
- [`JoinLemma_Of_CD.lean`](JoinLemma_Of_CD.lean) — `LatticeVCsPlus`,
  `CDVC`, downset infrastructure, the A11 conditional theorem. 0 sorries.
- [`CD_AWSet.lean`](CD_AWSet.lean) — AWSet discharge of CD. 0 sorries.
- [`CD_Exact.lean`](CD_Exact.lean) — exactness/minimality of CD (A12).
  0 sorries.

Docs:

- [`FINDINGS.md`](FINDINGS.md) — the journal (A1–A9); each entry states
  the finding, its status, and the mechanization pointer.
- [`A10_DRAFT.md`](A10_DRAFT.md), [`A11_DRAFT.md`](A11_DRAFT.md) — draft
  entries for the (b′) refutation and the CD ladder; to be folded into
  `FINDINGS.md`.
- [`PLAN.md`](PLAN.md), [`MERGE_PROOF.md`](MERGE_PROOF.md),
  [`MERGE_DISTINCT_LAST_ANALYSIS.md`](MERGE_DISTINCT_LAST_ANALYSIS.md) —
  historical analyses of the (superseded) BottomUp route.

## Notes

- **Lean namespace is `Sal.Emulation`** (historical: this development
  began inside `Sal/Emulation/`). The shared execution-model layer
  (`CRDTSig`, `Configuration`, `Step`, labeled transition systems) still
  lives in [`Sal/Emulation/`](../../Emulation/); this directory contains
  the metatheory proper. Physical layout changed; no logical renames.
- The **ternary (MRDT, three-way merge)** lift of this theory lives in
  [`Sal/MRDTs/Metatheory/`](../../MRDTs/Metatheory/).
