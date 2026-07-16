# Development/ — the research record

These are **findings and history, not junk**: every file here either forced
a design decision in the canonical development one level up, or documents
how it was reached.

**The presented tree lives one level up** (`Sal/ConditionedMRDTs/`):
the foundations in [`../Framework/`](../Framework/), the metatheorems in
[`../Metatheory/`](../Metatheory/), the machine-checked negative results in
[`../Refutations/`](../Refutations/) (four note-cited refutations were
promoted there from this directory: `Impossibility`,
`InterLca2op_Defeater_Arbiter`, `JoinLemma3F_Of_AlmostClosed`,
`RGA_Rehoming_Gate`), and the per-RDT conditioned instances in
[`../MRDT_Instances/`](../MRDT_Instances/), with the tombstone-free RGA
chain at [`../MRDT_Instances/RGA_Rehoming/`](../MRDT_Instances/RGA_Rehoming/).
What remains here is the research record; files here may import the
presented tree, never the reverse. (A few probe-flavored files moved with
the chain because load-bearing definitions live in them.)

Thirteen superseded RGA files returned here from `Conditioned/` once the
living chain stopped consuming them (earlier capstone skeletons and assembly
routes: `RGA_Skeleton`/`RGA_Skeleton2`, `RGA_EndToEnd`, the `RGA_EqJoin_NF_*`
assembly pair, and eight discharge intermediates); all still build 0-sorry.

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
