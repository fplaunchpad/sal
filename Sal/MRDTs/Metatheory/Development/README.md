# Development/ — the research record

These are **findings and history, not junk**: every file here either forced
a design decision in the canonical development one level up, or documents
how it was reached.

**The conditioned-metatheory chain is live, not historical**: the
tombstone-free RGA's end-to-end RA-linearizability (up to observational
`≈`) is proved by the chain culminating in `RGA_Honest_Residual.lean`
(quotient functor `GenericEqQuotient*.lean` → H-layer `GoodConfig3H.lean` →
canonical engine `RGA_CanonConvergence.lean`/`RGA_CanonFoldOK.lean` →
capstone `RGA_Skeleton3.lean` + the `RGA_*_Discharge.lean` leaves →
`RGA_Final_Assembly.lean` → `RGA_Honest_Residual.lean`), promoted at
[`../RGA_TombstoneFree_RA_Lin.lean`](../RGA_TombstoneFree_RA_Lin.lean).

- [`MRDT_METATHEORY_DRAFT.md`](MRDT_METATHEORY_DRAFT.md) — the findings
  journal **T0–T10.7**: the LCA-lemma gap analysis, the ternary defeater,
  the delta contract's discovery and its boundaries, the feasible-tuple
  route, the three capstone discharges, the full-closure finding. File
  names inside refer to the **pre-reorganization layout** (see the preamble
  note there); theorem names are unchanged and searchable.
- [`Peel_Route.lean`](Peel_Route.lean) — the first proved ternary
  metatheorem (`JoinPeelVCs3` + `join_lemma3_of_peel` +
  `ra_linearizable_of_core_join3`), superseded by the CD/feasible route but
  kept 0-sorry as the record.
- [`Impossibility.lean`](Impossibility.lean) — the machine-checked boundary:
  `Counter_binary_lem_0op_false` (ternary strictly exceeds binary), the
  unconditional-contract refutations for all three production MRDTs, the
  feasibility-boundedness of the unit/0-OP laws, and the
  `differentReplicas` forcing corner.
- [`VCs.lean`](VCs.lean) — the original 29-field ternary transcription
  (`SatisfiesVCsT`) of the paper's VC table, with the collapse-to-binary
  reuse contract. Superseded by `../VC_Set.lean`.
- [`BLUEPRINT.md`](BLUEPRINT.md), [`PHASE0_PLAN.md`](PHASE0_PLAN.md),
  [`SOUNDNESS_SPEC.md`](SOUNDNESS_SPEC.md) — the original mechanization
  plan, Phase-0 architecture, and target-theorem spec.
