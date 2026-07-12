import Sal.ConditionedMRDTs.MRDT_Instances.Shesha.Shesha_Coherence

/-! # Shesha — the conditioned instance and the RA-linearizability capstone

Shesha enters the one framework by the **mergeable-queue route**: the
ternary merge is exhibited directly as the linearization witness. Two
successive hook interfaces proved too weak, each with a machine-checked
counterexample at an honest configuration:

* the plain `JoinLemma3At` (`Shesha_Join_Refuted.lean`): canonical states
  are not unique per event set — a concurrent `(ins x←a, del a)` pair
  folds to different **live sets** under the two orders;
* the effective-class `JoinLemma3AtW` (`Shesha_Presplice_Refuted.lean`):
  effectiveness realigns the live sets but not the **orders** — the
  display order of concurrent same-anchor inserts is a `loOn`-free choice
  surviving in the state, and independently canonical slots may realize
  it incompatibly, breaking the branch agreement (Lemma B) the merge's
  run placement relies on.

The corrected route (`WitnessCoherence.lean`) threads the missing datum —
**same-anchor insert coherence** (`SCoh`), branch agreement at the witness
level — along the store's version ancestry: the hook now receives the
three slots' witnesses aligned (`SCoh ρ₀ ρ₁`, `SCoh ρ₀ ρ₂`), and owes the
merged witness aligned with both branches.

What remains is the **single owed hook** `shesha_presplice` (documented
`sorry`): the ternary merge output is the collapse of a pre-splice
anchored forest for the union whose rows *extend both branch witnesses'
same-anchor orders* — the merge-correctness core (M2/M3 + fold
realization), sitting on the closed M0–M2 layer, now with true
hypotheses: the slots agree on every common same-anchor pair. -/

namespace Sal.ConditionedMRDTs

open Sal.Emulation

open Classical in
/-- **The plan-order transport**: row order of the pre-splice forest,
realized as `Before` order of the assembled witness
(`plan of the forest ++ deletes`). `hprec` places `ty` left of `tx` in
`T`'s row — rows are newest-first, so the plan enumerates `tx` first. -/
theorem plan_before_of_row {C : Sal.Emulation.Configuration SheshaD.toCRDTSig}
    {E : Set (Op SAppOp)} {T : Shesha.St} {ρu : List (Op SAppOp)}
    (hsub : ∀ a ∈ E, a ∈ C.events)
    (hwfT : Shesha.WF T)
    (hrows : ∀ p x, x ∈ Shesha.row T p ↔ InsIn E x p)
    {p tx ty : Nat} {rx ry : Replica}
    (hx : (tx, rx, SAppOp.insA p) ∈ C.events)
    (hy : (ty, ry, SAppOp.insA p) ∈ C.events)
    (hprec : Shesha.precedes (Shesha.row T p) ty tx) :
    Before (evPlan E (Shesha.planF 0 T) ++ delBlock ρu)
      (tx, rx, SAppOp.insA p) (ty, ry, SAppOp.insA p) := by
  have hAI := Shesha.allIns_planF 0 T
  have hsl : List.Sublist [tx, ty]
      (Shesha.anchIds ((evPlan E (Shesha.planF 0 T)).map toSOp) p) := by
    rw [evPlan_map_toSOp hAI, Shesha.anchIds_planF_row hwfT p]
    exact List.Sublist.reverse hprec
  obtain ⟨ru, rv, hbef⟩ := anchIds_sublist2_before hsl
  have hplan_row : ∀ {x q : Nat}, Shesha.Op.ins x q ∈ Shesha.planF 0 T →
      x ∈ Shesha.row T q := by
    intro x q h
    obtain ⟨z, w, heq, hz⟩ := Shesha.planF_mem_row hwfT T
      (fun _ ht => Shesha.mem_subF_of_mem ht)
      (fun t ht => by
        rw [Shesha.row, if_pos rfl]
        exact List.mem_map.mpr ⟨t, ht, rfl⟩) h
    injection heq with h1 h2
    rw [h1, h2]
    exact hz
  have hmemE : ∀ e, e ∈ evPlan E (Shesha.planF 0 T) → e ∈ E := by
    intro e he
    obtain ⟨x, q, rfl, hins⟩ := mem_evPlan he
    exact evOfIns_mem ((hrows q x).mp (hplan_row hins))
  have hxeq : ((tx, ru, SAppOp.insA p) : Op SAppOp)
      = (tx, rx, SAppOp.insA p) :=
    C.ts_unique (hsub _ (hmemE _ (before_mem_left hbef))) hx rfl
  have hyeq : ((ty, rv, SAppOp.insA p) : Op SAppOp)
      = (ty, ry, SAppOp.insA p) :=
    C.ts_unique (hsub _ (hmemE _ (before_mem_right hbef))) hy rfl
  rw [hxeq, hyeq] at hbef
  exact before_append_left hbef

open Classical in
/-- **The owed pre-splice forest** (the last obligation, machine-checked
interface): from `SheshaEff`-canonical, **branch-agreement-aligned**
witnesses for the LCA and the two branches, a WF anchored forest `T` for
the union whose

* rows are exactly the union's inserts (original anchors),
* row orders never place a `vis`-earlier same-anchor insert left of a
  later one (newer-left),
* row orders **extend both branch witnesses' same-anchor orders**
  (rows are newest-first, so `Before ρᵢ` reverses into `precedes`), and
* delete-collapse (`dropF` at the union's delete targets) is **the
  ternary merge output**.

`sorry` — the merge-correctness core (pen-and-paper: M2/M3 + Theorem-P
layer of `whiteboard/sibling-linked-proof.md` §4-5). What the corrected
hypotheses add over the refuted phase-2e statement
(`Shesha_Presplice_Refuted.lean`): `SCoh ρ₀ ρ₁` and `SCoh ρ₀ ρ₂` — the
three slots agree on every common same-anchor pair, i.e. **branch
agreement (Lemma B) holds at the join**, which is exactly the invariant
the merge's skeleton/run placement relies on and exactly what the
refutation shows indispensable. What is machine-checked around it:
- each slot's state is `dropF (deleted) Tᵢ` of an anchored forest `Tᵢ`
  with rows = the slot's inserts, ordered against `vis` (`witness_nf`),
  and the slots' rows now *agree on common pairs* (via `SCoh` and
  `witness_nf`'s row/`anchIds` reversal), so the M0–M2 hypotheses
  (`ModelOK`, `LRowsOK`) and Lemma-B-alignment are all derivable;
- the two row-extension clauses pin `T`'s rows completely on every
  same-branch pair; the only remaining freedom is cross-branch-born
  order (decided by the merge's newest-head-first tiebreak) and ghost
  placement (deleted inserts, invisible to the collapse (b)/(d) but
  constrained by (c)) — `T` is the union forest of the design's §4;
- the converse is closed (`presplice_canonical_wit` + the transport
  `plan_before_of_row`): producing `T` here IS producing the aligned
  canonical witness, coherence obligations included
  (`shesha_join_at_effC` below is a full proof from this statement).
The remaining content: read the un-spliced forest off `merge s₀ s₁ s₂`
(output rows + the ghosts each branch collapsed), check its rows against
the three input forests' rows (the merge keeps L-order on the skeleton —
`merge_extends_L` — branch order on runs, head-timestamp order across
concurrent same-slot runs), and prove the collapse equation (the
merge-time marker splice IS the delete splice — `expandRow`/`collapseRow`
generalized from the L-filter instance `expandRow_filter_L` to the full
output). The state equation (d) is already REDUCED to per-row equations:
by `forest_ext`/`dropF_eq_of_rows` (`Shesha_Coherence.lean`) it suffices
that `row (dropF D T) p = row (merge s₀ s₁ s₂) p` for every `p` — LHS is
a front (`row_dropF`), RHS needs the one missing characterization: `row`
of `buildF` at an emitted key is its `expandRow`-expanded `outRows` entry
(the M0 `lvl`/fuel machinery makes this mechanical). -/
theorem shesha_presplice
    (C' : Configuration SheshaD) (hH : SheshaHonest C')
    (htrans : ∀ {a b c : Op SAppOp}, C'.vis a b → C'.vis b c → C'.vis a c)
    (hirr : ∀ a : Op SAppOp, ¬ C'.vis a a)
    {ev₁ ev₂ : Set (Op SAppOp)} {s₀ s₁ s₂ : Shesha.St}
    {ρ₀ ρ₁ ρ₂ : List (Op SAppOp)}
    (hsub₁ : ∀ a ∈ ev₁, a ∈ C'.events) (hsub₂ : ∀ a ∈ ev₂, a ∈ C'.events)
    (hclosed₁ : ∀ a b, C'.vis a b → ¬ SheshaD.toCRDTSig.commutes a b →
      b ∈ ev₁ → a ∈ ev₁)
    (hclosed₂ : ∀ a b, C'.vis a b → ¬ SheshaD.toCRDTSig.commutes a b →
      b ∈ ev₂ → a ∈ ev₂)
    (hc₀ : IsCanonWitness SheshaEff (Configuration.core C')
      (ev₁ ∩ ev₂) s₀ ρ₀)
    (hc₁ : IsCanonWitness SheshaEff (Configuration.core C') ev₁ s₁ ρ₁)
    (hc₂ : IsCanonWitness SheshaEff (Configuration.core C') ev₂ s₂ ρ₂)
    (hK₀₁ : SCoh ρ₀ ρ₁) (hK₀₂ : SCoh ρ₀ ρ₂) :
    ∃ T : Shesha.St,
      Shesha.WF T
      ∧ (∀ p x, x ∈ Shesha.row T p ↔ InsIn (ev₁ ∪ ev₂) x p)
      ∧ (∀ p x y rx ry, (x, rx, SAppOp.insA p) ∈ ev₁ ∪ ev₂ →
          (y, ry, SAppOp.insA p) ∈ ev₁ ∪ ev₂ →
          Shesha.precedes (Shesha.row T p) x y →
          ¬ C'.vis (x, rx, SAppOp.insA p) (y, ry, SAppOp.insA p))
      ∧ (∀ p tx ty rx ry,
          Before ρ₁ (tx, rx, SAppOp.insA p) (ty, ry, SAppOp.insA p) →
          Shesha.precedes (Shesha.row T p) ty tx)
      ∧ (∀ p tx ty rx ry,
          Before ρ₂ (tx, rx, SAppOp.insA p) (ty, ry, SAppOp.insA p) →
          Shesha.precedes (Shesha.row T p) ty tx)
      ∧ Shesha.dropF
          (fun u => decide (DelIn (ev₁ ∪ ev₂) u)) T
          = SheshaD.mergeL s₀ s₁ s₂ := by
  sorry

/-- **The aligned join hook**: under honest histories, Shesha's ternary
merge of branch-agreement-aligned slots is the fold of an aligned
`lo`-respecting **effective** enumeration of the union — the pre-splice
forest (`shesha_presplice`), planned and then collapsed
(`presplice_canonical_wit`), its coherence obligations discharged by the
plan-order transport (`plan_before_of_row`). -/
theorem shesha_join_at_effC :
    ∀ C', SheshaHonest C' →
      JoinLemma3AtWC SheshaD SheshaEff SCoh (Configuration.core C') := by
  intro C' hH ev₁ ev₂ s₀ s₁ s₂ ρ₀ ρ₁ ρ₂ htrans hirr hsub₁ hsub₂
    hclosed₁ hclosed₂ hc₀ hc₁ hc₂ hK₀₁ hK₀₂
  obtain ⟨T, hwfT, hrows, hcompat, hext₁, hext₂, hmerge⟩ :=
    shesha_presplice C' hH htrans hirr hsub₁ hsub₂ hclosed₁ hclosed₂
      hc₀ hc₁ hc₂ hK₀₁ hK₀₂
  have hsubU : ∀ a ∈ ev₁ ∪ ev₂, a ∈ (Configuration.core C').events :=
    fun a ha => ha.elim (hsub₁ a) (hsub₂ a)
  refine ⟨evPlan (ev₁ ∪ ev₂) (Shesha.planF 0 T)
      ++ delBlock (unionEnum ρ₁ ρ₂ ev₁), ?_, ?_, ?_⟩
  · rw [← hmerge]
    exact presplice_canonical_wit hH htrans hirr hsubU
      (unionEnum_perm hc₁.1 hc₂.1) T hwfT hrows hcompat
  · -- SCoh ρ₁ ρm
    intro p tx ty rx ry hxm hym hbef
    exact plan_before_of_row hsubU hwfT hrows
      (hsub₁ _ ((hc₁.1.2 _).mp (before_mem_left hbef)))
      (hsub₁ _ ((hc₁.1.2 _).mp (before_mem_right hbef)))
      (hext₁ p tx ty rx ry hbef)
  · -- SCoh ρ₂ ρm
    intro p tx ty rx ry hxm hym hbef
    exact plan_before_of_row hsubU hwfT hrows
      (hsub₂ _ ((hc₂.1.2 _).mp (before_mem_left hbef)))
      (hsub₂ _ ((hc₂.1.2 _).mp (before_mem_right hbef)))
      (hext₂ p tx ty rx ry hbef)

/-- **RA-linearizability of Shesha**: at every honestly-reachable
configuration, every version's state is the raw fold of some
`lo`-respecting linearization of its events. -/
theorem shesha_ra_linearizable3 {C : Configuration SheshaD}
    (hReach : HonestReach SheshaD SheshaHonest trivial C) :
    IsRALinearizable3 C :=
  ra_linearizable3_of_genHonest_reachWC (P := sGuard)
    sheshaEff_init sheshaEff_step scoh_refl scoh_ext scoh_sub
    shesha_join_at_effC
    (show HonestReach SheshaD (GenHonest SheshaD sGuard) trivial C from hReach)

end Sal.ConditionedMRDTs

section AxiomAuditCond
/-! Axiom audit: the capstone carries exactly the pre-splice `sorry`; the
coherent route, the witness class, the analysis (`witness_nf`), the
assembly (`presplice_canonical_wit`) and the transport
(`plan_before_of_row`) are kernel-clean. -/
#print axioms Sal.ConditionedMRDTs.shesha_ra_linearizable3
#print axioms Sal.ConditionedMRDTs.shesha_join_at_effC
#print axioms Sal.ConditionedMRDTs.plan_before_of_row
#print axioms Sal.ConditionedMRDTs.presplice_canonical_wit
#print axioms Sal.ConditionedMRDTs.witness_nf
#print axioms Sal.ConditionedMRDTs.sheshaEff_step
#print axioms Sal.ConditionedMRDTs.ra_linearizable3_of_genHonest_reachWC
end AxiomAuditCond
