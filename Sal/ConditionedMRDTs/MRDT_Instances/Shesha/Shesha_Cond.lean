import Sal.ConditionedMRDTs.MRDT_Instances.Shesha.Shesha_Presplice

/-! # Shesha: the conditioned instance and the RA-linearizability capstone

Shesha enters the one framework by the **mergeable-queue route**: the
ternary merge is exhibited directly as the linearization witness. Two
successive hook interfaces proved too weak, each with a machine-checked
counterexample at an honest configuration:

* the plain `JoinLemma3At` (`Shesha_Join_Refuted.lean`): canonical states
  are not unique per event set, a concurrent `(ins x←a, del a)` pair
  folds to different **live sets** under the two orders;
* the effective-class `JoinLemma3AtW` (`Shesha_Presplice_Refuted.lean`):
  effectiveness realigns the live sets but not the **orders**, the
  display order of concurrent same-anchor inserts is a `loOn`-free choice
  surviving in the state, and independently canonical slots may realize
  it incompatibly, breaking the branch agreement (Lemma B) the merge's
  run placement relies on.

This route (`WitnessCoherence.lean`) threads the missing datum,
**same-anchor insert coherence** (`SCoh`), branch agreement at the witness
level, along the store's version ancestry: the hook receives the
three slots' witnesses aligned (`SCoh ρ₀ ρ₁`, `SCoh ρ₀ ρ₂`), and owes the
merged witness aligned with both branches.

The pre-splice obligation `shesha_presplice` is **proved down to the
row level** (`Shesha_Presplice.lean`): the forest is built from a row
store by the graded builder (`Shesha_Out.lean`), and every clause, WF,
rows, anti-`vis` order, the branch-order extensions, and the collapse
equation, is discharged from the row-store package. The **single owed
residue** `shesha_rows_residue` (documented `sorry`) is the store itself.

**Refuted** (`Shesha_Rows_Refuted.lean`, machine-checked):
`shesha_rows_residue` is **FALSE**. At an honest, `SCoh`-aligned config
(`SCoh` vacuous, only one common insert) the merge of the canonical folds
of `LCA=[ins 1]`, `A=[ins 2←1, ins 4←⌂, del 1]`, `B=[ins 3←1]` is
`[3,4,2]`, which splits marker `1`'s children `{2,3}` around the concurrent
sibling `4`, no pre-splice forest collapses to it, and `[3,4,2]` is not the
fold of any `loOn`-respecting linearization of the union. So the pre-splice
route cannot close this capstone as stated, and `shesha_ra_linearizable3`
below, proved *from* this `sorry`, rests on a known-false lemma; its
statement is itself unsatisfiable at this reachable merge. The split is caused
by Shesha's *local-order-preserving splice over a mutable forest*, **not** by
anchor-forgetting: `RGA_Tombstone_Free` also forgets the anchor on delete, but
it re-homes and *re-sorts survivors by their global key*, so its read is always
a fold (⇒ RA-linearizable) at the cost of reordering survivors
(`tombstone_free_violates_delete_order`). Shesha instead keeps local sibling
order (`delete_preserves_survivor_order`), so a single replica is delete-order-
faithful but the merge of two mutable forests is not a global fold, the
**sequence-CRDT trilemma** (local-order-preserving delete ⊻ merge RA-lin). The
dissolution is not anchor-retention but **immutable stored positions** (KC+Kartik,
`Development/RGA_OrderPreserving_Reference.lean`): freeze the ancestry
path at insert, read = lex-sort by frozen position, delete = drop; positions
never move, so both delete-order holds and the read is a fold, on this trace
`2`,`3` keep contiguous frozen paths so `4` cannot split them. A restatement to a
weaker convergence / licensed-divergence spec (which Shesha *does* satisfy), or
the immutable-position re-encoding, is the owed research decision. The theorem
below is kept byte-identical and compiling to preserve the type-locked
interface. -/

namespace Sal.ConditionedMRDTs

open Sal.Emulation

open Classical in
/-- **The plan-order transport**: row order of the pre-splice forest,
realized as `Before` order of the assembled witness
(`plan of the forest ++ deletes`). `hprec` places `ty` left of `tx` in
`T`'s row, rows are newest-first, so the plan enumerates `tx` first. -/
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

**Proved** (`presplice_of_rows` ∘ `shesha_rows_residue`,
`Shesha_Presplice.lean`): the forest level is fully machine-checked,
`T` is the graded build of a pre-splice row store, its WF/rows/coverage
come from the builder kit (`Shesha_Out.lean`), the anti-`vis` clause (c)
is *derived* from the extension clauses (c′) through the
honesty/non-commutation kernel, and the collapse equation (d) reduces
per-row (`forest_ext`/`dropF_eq_of_rows`) to: live keys, the collapse
row is the ghost expansion of the stored row
(`build_collapse_row_raw`) and matches the merge row by the residue's
`hK6`; absent keys, both sides die by the live-set identity
(`slots_live_iff` + `merge_ids`). The single remaining `sorry` is the
row store itself (`shesha_rows_residue`): the merge-correctness core in
pure row combinatorics, with hypotheses `SCoh ρ₀ ρ₁`,
`SCoh ρ₀ ρ₂` (branch agreement at the join, indispensable per the
refutation in `Shesha_Presplice_Refuted.lean`). -/
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
  obtain ⟨preRows, n, hK1, hK2, hK3, hK4, hK5, hK6⟩ :=
    shesha_rows_residue C' hH (fun h1 h2 => htrans h1 h2) hirr
      hsub₁ hsub₂ hclosed₁ hclosed₂ hc₀ hc₁ hc₂ hK₀₁ hK₀₂
  exact presplice_of_rows C' hH (fun h1 h2 => htrans h1 h2) hirr
    hsub₁ hsub₂ hclosed₁ hclosed₂ hc₀ hc₁ hc₂
    preRows n hK1 hK2 hK3 hK4 hK5 hK6

/-- **The aligned join hook**: under honest histories, Shesha's ternary
merge of branch-agreement-aligned slots is the fold of an aligned
`lo`-respecting **effective** enumeration of the union, the pre-splice
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
/-! Axiom audit: the capstone carries exactly the row-store `sorry`
(`shesha_rows_residue`); the coherent route, the witness class, the
analysis (`witness_nf`), the assembly (`presplice_canonical_wit`), the
transport (`plan_before_of_row`), the output characterization
(`merge_row`), the builder kit, and the forest-level reduction
(`presplice_of_rows`) are all kernel-clean. -/
#print axioms Sal.ConditionedMRDTs.shesha_ra_linearizable3
#print axioms Sal.ConditionedMRDTs.shesha_join_at_effC
#print axioms Sal.ConditionedMRDTs.presplice_of_rows
#print axioms Shesha.merge_row
#print axioms Shesha.build_collapse_row_raw
#print axioms Sal.ConditionedMRDTs.plan_before_of_row
#print axioms Sal.ConditionedMRDTs.presplice_canonical_wit
#print axioms Sal.ConditionedMRDTs.witness_nf
#print axioms Sal.ConditionedMRDTs.sheshaEff_step
#print axioms Sal.ConditionedMRDTs.ra_linearizable3_of_genHonest_reachWC
end AxiomAuditCond
