import Sal.ConditionedMRDTs.MRDT_Instances.Shesha.Shesha_Witness

/-! # Shesha — the conditioned instance and the RA-linearizability capstone

Shesha enters the one framework by the **mergeable-queue route**: the
ternary merge is exhibited directly as the linearization witness. But the
queue's plain hook (`JoinLemma3At` at every honest configuration) is
**FALSE for Shesha** — machine-checked in `Shesha_Join_Refuted.lean`:
`IsCanonicalState` is existential, Shesha's canonical states are not unique
per event set (a concurrent `(ins x←a, del a)` pair folds to different live
sets under the two enumeration orders), and a misaligned canonical triple
makes the merge emit a node twice. The queue was immune only because its
canonical states are unique.

The corrected route (`WitnessClass.lean`) restricts the witnesses to the
class real executions produce: **effective** enumerations (`SheshaEff` —
every insert applies: its anchor is live, or the root, at its point in the
fold). Effectiveness realigns the three slots of the join.

The whole replay half is now closed generically:
- `Shesha_EffFold.lean` — every effective fold is `dropF (deleted)` of its
  insert-phase **anchored forest** (delete postponement + set-drop);
- `Shesha_Hook_Facts.lean` — causal pasts are enumerable (Lamport clocks),
  the honesty exclusions, and `witness_nf`: every hook slot is the collapse
  of an anchored forest whose rows are the slot's inserts, vis-descending;
- `Shesha_Witness.lean` — `presplice_canonical`: conversely, ANY such
  forest for the union realizes its collapse as a `SheshaEff`-canonical
  state (plan the forest, then delete ascending).

What remains is the **single owed hook** `shesha_presplice` (documented
`sorry`): the ternary merge output IS the collapse of such a forest — the
merge-correctness core (M3 + fold realization), sitting on the closed
M0–M2 layer. -/

namespace Sal.ConditionedMRDTs

open Sal.Emulation

open Classical in
/-- **The owed pre-splice forest** (the last obligation, machine-checked
interface): from `SheshaEff`-canonical witnesses for the LCA and the two
branches, a WF anchored forest `T` for the union whose

* rows are exactly the union's inserts (original anchors), and
* row orders never place a `vis`-earlier same-anchor insert left of a
  later one (newer-left), and whose
* delete-collapse (`dropF` at the union's delete targets) is **the
  ternary merge output**.

`sorry` — the merge-correctness core (pen-and-paper: M3 + Theorem-P layer
of `whiteboard/sibling-linked-proof.md`). What is already machine-checked
around it:
- each slot's state is `dropF (deleted) Tᵢ` of an anchored forest `Tᵢ`
  with these same row properties (`witness_nf`, kernel-clean), so the
  live sets are set-determined (`read_dropF`: inserted ∖ deleted) and the
  M0–M2 hypotheses (`ModelOK`, `LRowsOK`) are derivable for `s₀ s₁ s₂`;
- collapse rows are fronts (`row_dropF`), collapse membership is
  dead-descent (`mem_row_dropF`) — the structural language in which the
  merge's `outRows`/`skelOf`/run machinery (M0/M2: `skelOf_alGet`,
  `outRows_cases`, `merge_ids`, `expandRow_filter_L`, `collapseRow`)
  must be re-read to exhibit `T`;
- the converse direction is closed (`presplice_canonical`): producing
  `T` here IS producing the canonical witness.
The remaining content: read the un-spliced forest off `merge s₀ s₁ s₂`
(output rows + the ghosts each branch collapsed), check its rows against
the three input forests' rows (the merge keeps L-order on the skeleton,
branch order on runs, head-timestamp order across concurrent runs — all
vis-compatible), and prove the collapse equation (the merge-time splice
is the delete splice — `expandRow`/`collapseRow` generalized from the
L-filter instance to the full output). -/
theorem shesha_presplice
    (C' : Configuration SheshaD) (hH : SheshaHonest C')
    (htrans : ∀ {a b c : Op SAppOp}, C'.vis a b → C'.vis b c → C'.vis a c)
    (hirr : ∀ a : Op SAppOp, ¬ C'.vis a a)
    {ev₁ ev₂ : Set (Op SAppOp)} {s₀ s₁ s₂ : Shesha.St}
    (hsub₁ : ∀ a ∈ ev₁, a ∈ C'.events) (hsub₂ : ∀ a ∈ ev₂, a ∈ C'.events)
    (hclosed₁ : ∀ a b, C'.vis a b → ¬ SheshaD.toCRDTSig.commutes a b →
      b ∈ ev₁ → a ∈ ev₁)
    (hclosed₂ : ∀ a b, C'.vis a b → ¬ SheshaD.toCRDTSig.commutes a b →
      b ∈ ev₂ → a ∈ ev₂)
    (hc₀ : IsCanonicalStateW SheshaEff (Configuration.core C')
      (ev₁ ∩ ev₂) s₀)
    (hc₁ : IsCanonicalStateW SheshaEff (Configuration.core C') ev₁ s₁)
    (hc₂ : IsCanonicalStateW SheshaEff (Configuration.core C') ev₂ s₂) :
    ∃ T : Shesha.St,
      Shesha.WF T
      ∧ (∀ p x, x ∈ Shesha.row T p ↔ InsIn (ev₁ ∪ ev₂) x p)
      ∧ (∀ p x y rx ry, (x, rx, SAppOp.insA p) ∈ ev₁ ∪ ev₂ →
          (y, ry, SAppOp.insA p) ∈ ev₁ ∪ ev₂ →
          Shesha.precedes (Shesha.row T p) x y →
          ¬ C'.vis (x, rx, SAppOp.insA p) (y, ry, SAppOp.insA p))
      ∧ Shesha.dropF
          (fun u => decide (DelIn (ev₁ ∪ ev₂) u)) T
          = SheshaD.mergeL s₀ s₁ s₂ := by
  sorry

/-- **The join hook**: under honest histories, Shesha's ternary merge is
the fold of some `lo`-respecting **effective** enumeration of the union
of the branches' events — the pre-splice forest (`shesha_presplice`),
planned and then collapsed (`presplice_canonical`). -/
theorem shesha_join_at_eff :
    ∀ C', SheshaHonest C' →
      JoinLemma3AtW SheshaD SheshaEff (Configuration.core C') := by
  intro C' hH ev₁ ev₂ s₀ s₁ s₂ htrans hirr hsub₁ hsub₂ hclosed₁ hclosed₂
    hc₀ hc₁ hc₂
  obtain ⟨T, hwfT, hrows, hcompat, hmerge⟩ :=
    shesha_presplice C' hH htrans hirr hsub₁ hsub₂ hclosed₁ hclosed₂
      hc₀ hc₁ hc₂
  obtain ⟨ρ₁, hperm₁, -, -, -⟩ := hc₁
  obtain ⟨ρ₂, hperm₂, -, -, -⟩ := hc₂
  rw [← hmerge]
  exact presplice_canonical hH htrans hirr
    (fun a ha => ha.elim (hsub₁ a) (hsub₂ a))
    (unionEnum_perm hperm₁ hperm₂) T hwfT hrows hcompat

/-- **RA-linearizability of Shesha**: at every honestly-reachable
configuration, every version's state is the raw fold of some
`lo`-respecting linearization of its events. -/
theorem shesha_ra_linearizable3 {C : Configuration SheshaD}
    (hReach : HonestReach SheshaD SheshaHonest trivial C) :
    IsRALinearizable3 C :=
  ra_linearizable3_of_genHonest_reachW (P := sGuard)
    sheshaEff_init sheshaEff_step shesha_join_at_eff
    (show HonestReach SheshaD (GenHonest SheshaD sGuard) trivial C from hReach)

end Sal.ConditionedMRDTs

section AxiomAuditCond
/-! Axiom audit: the capstone carries exactly the pre-splice `sorry`; the
route, the witness class, the analysis (`witness_nf`) and the assembly
(`presplice_canonical`) are kernel-clean. -/
#print axioms Sal.ConditionedMRDTs.shesha_ra_linearizable3
#print axioms Sal.ConditionedMRDTs.shesha_join_at_eff
#print axioms Sal.ConditionedMRDTs.presplice_canonical
#print axioms Sal.ConditionedMRDTs.witness_nf
#print axioms Sal.ConditionedMRDTs.sheshaEff_step
#print axioms Sal.ConditionedMRDTs.applySeq_toSOp
end AxiomAuditCond
