import Sal.ConditionedMRDTs.MRDT_Instances.Shesha.Shesha_Join_Refuted

/-! # Shesha — the `W`-join hook (phase 2e) is ALSO false: slot orders misalign

`shesha_join_at_eff` (the phase-2e formulation: every `SheshaHonest`
configuration admits `JoinLemma3AtW` at the **effective** witness class) is
**refuted** here, and with it `shesha_presplice` as stated.

The root cause, one level above `Shesha_Join_Refuted.lean`'s: effectiveness
realigned the three slots' **live sets**, but not their **orders**. Two
*concurrent same-anchor inserts* are `loOn`-unordered, so the LCA slot and a
branch slot may enumerate them in opposite orders — the folds then display
the common pair in opposite orders, breaking **branch agreement** (Lemma B of
`whiteboard/sibling-linked-proof.md` §3), which the merge's run placement
silently relies on. Here: three inserts at the root,

    f₁ = ins 1←⌂ (r0),  f₂ = ins 2←⌂ (r1, concurrent with f₁),
    f₃ = ins 3←⌂ (r0, after seeing both),

with `ev₁ = {f₁,f₂,f₃}`, `ev₂ = {f₁,f₂}`. The witness `[f₂,f₁]` folds to the
display `1 2` (canonical for the LCA and `ev₂` slots), while `[f₁,f₂,f₃]`
folds to `3 2 1` (canonical for `ev₁`). All three witnesses are effective —
root-anchored inserts always apply. The merge trusts the LCA's order `1 2`
for the skeleton and places the head run `[3]` before its branch successor
`2`: output display `1 3 2`. But **every** `loOn`-respecting enumeration of
the union must place `f₃` last (it causally sees both same-anchor inserts,
`G2`), so every witness fold displays `3` first. No witness folds to the
merge; a fortiori no pre-splice forest for the union collapses to it (its
root row would need `1` left of `3` against `vis`).

In real executions the misaligned triple is **unreachable**: a version's
state inherits the LCA's display of common pairs (branch agreement is an
*evolution* invariant, not a per-slot property). The repair therefore
threads a cross-slot **coherence** relation along version ancestry
(`Metatheory/WitnessCoherence.lean`), and the corrected hook receives
branch-agreement-aligned witnesses.

Axiom note: the merge computation runs through `List.mergeSort`, so the
single computational leaf `cy_merge_eq` uses `native_decide`; everything
else is `decide`-level. -/

namespace Sal.ConditionedMRDTs
namespace SheshaPrespliceCX

open Sal.Emulation

/-- `ins 1←⌂` at replica 0, timestamp 1. -/
def f1 : Op SAppOp := (1, 0, SAppOp.insA 0)
/-- `ins 2←⌂` at replica 1, timestamp 2 (concurrent with `f1`). -/
def f2 : Op SAppOp := (2, 1, SAppOp.insA 0)
/-- `ins 3←⌂` at replica 0, timestamp 3 (its issuer saw `f1` and `f2`). -/
def f3 : Op SAppOp := (3, 0, SAppOp.insA 0)

/-- Replica 0's observed set (it received `f2` before issuing `f3`). -/
def S0 : Set (Op SAppOp) := fun x => x = f1 ∨ x = f2 ∨ x = f3
/-- Replica 1's observed set. -/
def S1 : Set (Op SAppOp) := fun x => x = f2

/-- The branch event set of the refutation. -/
def EV1 : Set (Op SAppOp) := fun x => x = f1 ∨ x = f2 ∨ x = f3
/-- The other branch: the two concurrent root inserts only. -/
def EV2 : Set (Op SAppOp) := fun x => x = f1 ∨ x = f2

/-- Visibility: `f1, f2` precede `f3`; `f1 ∥ f2`. -/
def visy (a b : Op SAppOp) : Prop := (a = f1 ∨ a = f2) ∧ b = f3

/-- The replica-sets function of the counterexample configuration. -/
def Lfun : Replica → Option (Set (Op SAppOp)) :=
  fun r => if r = 0 then some S0 else if r = 1 then some S1 else none

theorem Lfun_mem {r : Replica} {s : Set (Op SAppOp)} {a : Op SAppOp}
    (h : Lfun r = some s) (ha : s a) : a = f1 ∨ a = f2 ∨ a = f3 := by
  rw [Lfun] at h
  by_cases h0 : r = 0
  · rw [if_pos h0, Option.some.injEq] at h
    exact (h ▸ ha : S0 a)
  · rw [if_neg h0] at h
    by_cases h1 : r = 1
    · rw [if_pos h1, Option.some.injEq] at h
      exact Or.inr (Or.inl (h ▸ ha : S1 a))
    · rw [if_neg h1] at h
      exact absurd h (by simp)

theorem S0_f1 : S0 f1 := Or.inl rfl
theorem L0 : Lfun 0 = some S0 := rfl
theorem L1 : Lfun 1 = some S1 := rfl

private theorem ver0 {v : Version} {s : Shesha.St} {e : Set (Op SAppOp)}
    (hv : (if v = 0 then some (SheshaD.init, (∅ : Set (Op SAppOp))) else none)
      = some (s, e)) : e = ∅ := by
  by_cases h : v = 0
  · rw [if_pos h, Option.some.injEq, Prod.mk.injEq] at hv
    exact hv.2.symm
  · rw [if_neg h] at hv
    exact absurd hv (by simp)

/-- The honest counterexample configuration: two replicas, `{f1,f2,f3}` and
`{f2}`; a trivial one-version store. -/
def Cy : Configuration SheshaD where
  N := fun r => if r = 0 then some (sUpdate (sUpdate (sUpdate SheshaD.init f1) f2) f3)
    else if r = 1 then some (sUpdate SheshaD.init f2) else none
  L := Lfun
  vis := visy
  dom_eq := by
    intro r
    by_cases h0 : r = 0
    · simp [Lfun, h0]
    · by_cases h1 : r = 1 <;> simp [Lfun, h0, h1]
  vis_src := by
    rintro a b ⟨rfl | rfl, -⟩
    · exact ⟨0, S0, L0, S0_f1⟩
    · exact ⟨0, S0, L0, Or.inr (Or.inl rfl)⟩
  vis_tgt := by
    rintro a b ⟨-, rfl⟩
    exact ⟨0, S0, L0, Or.inr (Or.inr rfl)⟩
  vis_causal := by
    rintro a b r s ⟨ha, rfl⟩ hLr hsb
    rw [Lfun] at hLr
    by_cases h0 : r = 0
    · rw [if_pos h0, Option.some.injEq] at hLr
      subst hLr
      rcases ha with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · rw [if_neg h0] at hLr
      by_cases h1 : r = 1
      · rw [if_pos h1, Option.some.injEq] at hLr
        subst hLr
        exact absurd (show f3 = f2 from hsb) (by decide)
      · rw [if_neg h1] at hLr
        exact absurd hLr (by simp)
  timestamps_distinct := by
    intro a b r s r' s' hLr hsa hLr' hsb hne
    rcases Lfun_mem hLr hsa with rfl | rfl | rfl <;>
      rcases Lfun_mem hLr' hsb with rfl | rfl | rfl <;>
      first
        | exact absurd rfl hne
        | decide
  causal_mono := by
    rintro a b ⟨rfl | rfl, rfl⟩ <;> decide
  vis_total_same_replica := by
    intro a b r s r' s' hLr hsa hLr' hsb hne hrid
    rcases Lfun_mem hLr hsa with rfl | rfl | rfl <;>
      rcases Lfun_mem hLr' hsb with rfl | rfl | rfl <;>
      first
        | exact absurd rfl hne
        | exact absurd hrid (by decide)
        | exact Or.inl ⟨Or.inl rfl, rfl⟩
        | exact Or.inr ⟨Or.inl rfl, rfl⟩
  ver := fun v => if v = 0 then some (SheshaD.init, ∅) else none
  head := fun _ => none
  parents := fun _ => []
  parents_lt := by
    intro v p hp
    exact absurd hp (by simp)
  ver_init := rfl
  head_coherent := fun r v hr => absurd hr (by simp)
  ver_inv := fun _ _ _ _ => trivial
  lca_events := by
    intro v₁ v₂ vT s₁ ev₁ s₂ ev₂ sT evT _ hv₁ hv₂ hvT
    rw [ver0 hv₁, ver0 hv₂, ver0 hvT]
    exact (Set.empty_inter _).symm

/-! ## Honesty of `Cy` -/

theorem events_cases {a : Op SAppOp} (h : a ∈ Cy.events) :
    a = f1 ∨ a = f2 ∨ a = f3 := by
  obtain ⟨r, s, hLr, hsa⟩ := h
  exact Lfun_mem hLr hsa

/-- `f1`'s causal past is empty. -/
theorem perm_past_f1 {π : List (Op SAppOp)}
    (hπ : listPermOf π {e' ∈ Cy.events | Cy.vis e' f1}) : π = [] := by
  cases π with
  | nil => rfl
  | cons x rest =>
    have hx := (hπ.2 x).mp (List.mem_cons_self ..)
    exact absurd (hx.2.2 : f1 = f3) (by decide)

/-- `f2`'s causal past is empty. -/
theorem perm_past_f2 {π : List (Op SAppOp)}
    (hπ : listPermOf π {e' ∈ Cy.events | Cy.vis e' f2}) : π = [] := by
  cases π with
  | nil => rfl
  | cons x rest =>
    have hx := (hπ.2 x).mp (List.mem_cons_self ..)
    exact absurd (hx.2.2 : f2 = f3) (by decide)

theorem f1_events : f1 ∈ Cy.events := ⟨0, S0, L0, S0_f1⟩
theorem f2_events : f2 ∈ Cy.events := ⟨0, S0, L0, Or.inr (Or.inl rfl)⟩
theorem f3_events : f3 ∈ Cy.events := ⟨0, S0, L0, Or.inr (Or.inr rfl)⟩

theorem past_f3_iff :
    ∀ x, x ∈ {e' ∈ Cy.events | Cy.vis e' f3} ↔ x = f1 ∨ x = f2 := by
  intro x
  constructor
  · rintro ⟨-, h, -⟩
    exact h
  · rintro (rfl | rfl)
    · exact ⟨f1_events, Or.inl rfl, rfl⟩
    · exact ⟨f2_events, Or.inr rfl, rfl⟩

/-- **`Cy` is honest**: every event's generation guard holds at the fold of
every enumeration of its causal past. -/
theorem cy_honest : SheshaHonest Cy := by
  intro e he π hπ
  rcases events_cases he with rfl | rfl | rfl
  · rw [perm_past_f1 hπ]
    exact ⟨by decide, by decide, Or.inl rfl⟩
  · rw [perm_past_f2 hπ]
    exact ⟨by decide, by decide, Or.inl rfl⟩
  · rcases SheshaJoinCX.perm_two (u := f1) (v := f2) (by decide) hπ.1
        (fun a => (hπ.2 a).trans (past_f3_iff a)) with rfl | rfl
    · exact ⟨by decide, by decide, Or.inl rfl⟩
    · exact ⟨by decide, by decide, Or.inl rfl⟩

/-! ## The misaligned effective canonical triple -/

/-- The LCA-slot (and `ev₂`-slot) fold: display `1 2`. -/
def st0 : Shesha.St := [Shesha.Tree.node 1 [], Shesha.Tree.node 2 []]

/-- The `ev₁`-slot fold: display `3 2 1`. -/
def st1 : Shesha.St :=
  [Shesha.Tree.node 3 [], Shesha.Tree.node 2 [], Shesha.Tree.node 1 []]

/-- With `rc := Either`, a `loOn`-edge is a `vis`-edge. -/
theorem loOn_vis {ev : Set (Op SAppOp)} {a b : Op SAppOp}
    (h : loOn (Configuration.core Cy) ev a b) : visy a b := by
  rcases h with ⟨hv, -⟩ | ⟨-, -, hrc, -⟩
  · exact hv
  · exact RcRes.noConfusion hrc

/-- `[f2, f1]` respects `loOn` (the pair is concurrent). -/
theorem resp_21 {ev : Set (Op SAppOp)} :
    respects [f2, f1] (loOn (Configuration.core Cy) ev) := by
  refine List.Pairwise.cons ?_ (List.pairwise_singleton _ _)
  rintro b hb hlo
  rw [List.mem_singleton] at hb
  subst hb
  exact absurd (loOn_vis hlo).2 (by decide)

/-- `[f1, f2, f3]` respects `loOn` (`f3` last). -/
theorem resp_123 {ev : Set (Op SAppOp)} :
    respects [f1, f2, f3] (loOn (Configuration.core Cy) ev) := by
  refine List.Pairwise.cons ?_
    (List.Pairwise.cons ?_ (List.pairwise_singleton _ _))
  · rintro b hb hlo
    exact absurd (loOn_vis hlo).2 (by decide)
  · rintro b hb hlo
    rw [List.mem_singleton] at hb
    subst hb
    exact absurd (loOn_vis hlo).2 (by decide)

/-- Root-anchored inserts are always effective. -/
theorem eff_21 : SheshaEff [f2, f1] :=
  ⟨Or.inl rfl, Or.inl rfl, trivial⟩

theorem eff_123 : SheshaEff [f1, f2, f3] :=
  ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl, trivial⟩

/-- The LCA slot: `st0` is `W`-canonical for `EV1 ∩ EV2` via `[f2, f1]`. -/
theorem hcW0 : IsCanonicalStateW SheshaEff (Configuration.core Cy)
    (EV1 ∩ EV2) st0 := by
  refine ⟨[f2, f1], ⟨by decide, fun a => ?_⟩, resp_21, eff_21, by decide⟩
  rw [List.mem_cons, List.mem_singleton]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨Or.inr (Or.inl rfl), Or.inr rfl⟩
    · exact ⟨Or.inl rfl, Or.inl rfl⟩
  · rintro ⟨-, rfl | rfl⟩
    · exact Or.inr rfl
    · exact Or.inl rfl

/-- The `ev₁` slot: `st1` is `W`-canonical for `EV1` via `[f1, f2, f3]`. -/
theorem hcW1 : IsCanonicalStateW SheshaEff (Configuration.core Cy) EV1 st1 := by
  refine ⟨[f1, f2, f3], ⟨by decide, fun a => ?_⟩, resp_123, eff_123, by decide⟩
  rw [List.mem_cons, List.mem_cons, List.mem_singleton]
  exact Iff.rfl

/-- The `ev₂` slot: `st0` is `W`-canonical for `EV2` via `[f2, f1]`. -/
theorem hcW2 : IsCanonicalStateW SheshaEff (Configuration.core Cy) EV2 st0 := by
  refine ⟨[f2, f1], ⟨by decide, fun a => ?_⟩, resp_21, eff_21, by decide⟩
  rw [List.mem_cons, List.mem_singleton]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rintro (rfl | rfl)
    · exact Or.inr rfl
    · exact Or.inl rfl

/-! ## The refutation -/

theorem cy_trans : ∀ {a b c : Op SAppOp},
    (Configuration.core Cy).vis a b → (Configuration.core Cy).vis b c →
    (Configuration.core Cy).vis a c := by
  rintro a b c ⟨-, rfl⟩ ⟨hb | hb, -⟩ <;> exact absurd hb (by decide)

theorem cy_irrefl : ∀ a : Op SAppOp, ¬ (Configuration.core Cy).vis a a := by
  rintro a ⟨h | h, rfl⟩ <;> exact absurd h (by decide)

theorem cy_in1 : ∀ a ∈ EV1, a ∈ (Configuration.core Cy).events := by
  rintro a (rfl | rfl | rfl)
  · exact f1_events
  · exact f2_events
  · exact f3_events

theorem cy_in2 : ∀ a ∈ EV2, a ∈ (Configuration.core Cy).events := by
  rintro a (rfl | rfl)
  · exact f1_events
  · exact f2_events

theorem cy_closed1 : ∀ a b, (Configuration.core Cy).vis a b →
    ¬ SheshaD.toCRDTSig.commutes a b → b ∈ EV1 → a ∈ EV1 := by
  rintro a b ⟨rfl | rfl, -⟩ - -
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)

theorem cy_closed2 : ∀ a b, (Configuration.core Cy).vis a b →
    ¬ SheshaD.toCRDTSig.commutes a b → b ∈ EV2 → a ∈ EV2 := by
  rintro a b ⟨rfl | rfl, -⟩ - -
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The merge of the misaligned triple: the skeleton keeps the LCA's display
`1 2` and the head run `[3]` lands before its branch successor `2`. -/
theorem cy_merge_eq : SheshaD.mergeL st0 st1 st0
    = [Shesha.Tree.node 1 [], Shesha.Tree.node 3 [], Shesha.Tree.node 2 []] := by
  native_decide

/-- Any `loOn`-respecting enumeration of the union folds to a state whose
head is `node 3` — `f3` sees both same-anchor inserts, so it is enumerated
last and its (root) insert is the final head-insertion. -/
theorem fold_head_three {ρ : List (Op SAppOp)}
    (hperm : listPermOf ρ (EV1 ∪ EV2))
    (hresp : respects ρ (loOn (Configuration.core Cy) (EV1 ∪ EV2))) :
    ∃ t, applySeq SheshaD.toCRDTSig SheshaD.init ρ
      = Shesha.Tree.node 3 [] :: t := by
  have hf3ρ : f3 ∈ ρ := (hperm.2 f3).mpr (Or.inl (Or.inr (Or.inr rfl)))
  obtain ⟨α, β, hsplit⟩ := List.append_of_mem hf3ρ
  cases β with
  | cons e β' =>
    exfalso
    have heρ : e ∈ ρ := by
      rw [hsplit]
      exact List.mem_append_right _
        (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have hb : Before ρ f3 e := ⟨α, e :: β', hsplit, List.mem_cons_self ..⟩
    have hnl := respects_before hresp hb
    have hcases : e = f1 ∨ e = f2 ∨ e = f3 := by
      rcases (hperm.2 e).mp heρ with he | he
      · exact he
      · rcases he with he | he
        · exact Or.inl he
        · exact Or.inr (Or.inl he)
    rcases hcases with rfl | rfl | rfl
    · exact hnl (Or.inl ⟨⟨Or.inl rfl, rfl⟩,
        ncomm_ins_ins_same_anchor (by decide) (by decide) (by decide)⟩)
    · exact hnl (Or.inl ⟨⟨Or.inr rfl, rfl⟩,
        ncomm_ins_ins_same_anchor (by decide) (by decide) (by decide)⟩)
    · have hnd := hperm.1
      rw [hsplit, List.nodup_append] at hnd
      exact (List.nodup_cons.mp hnd.2.1).1 (List.mem_cons_self ..)
  | nil =>
    refine ⟨applySeq SheshaD.toCRDTSig SheshaD.init α, ?_⟩
    rw [hsplit, applySeq_append_single,
      show SheshaD.toCRDTSig.update
          (applySeq SheshaD.toCRDTSig SheshaD.init α) f3
        = Shesha.insert (applySeq SheshaD.toCRDTSig SheshaD.init α) 3 0
        from rfl,
      Shesha.insert, if_pos rfl]

/-- **The phase-2e join hook is FALSE**: an honest configuration exists at
which `JoinLemma3AtW` at the effective class fails — the misaligned (but
individually canonical and effective) triple `st0, st1, st0` makes the merge
display `1 3 2`, which no `loOn`-respecting enumeration of the union folds
to. This is the exact statement of the former `shesha_join_at_eff`. -/
theorem shesha_join_at_eff_refuted :
    ¬ (∀ C', SheshaHonest C' →
        JoinLemma3AtW SheshaD SheshaEff (Configuration.core C')) := by
  intro h
  obtain ⟨ρ, hperm, hresp, hW, hfold⟩ :=
    h Cy cy_honest EV1 EV2 st0 st1 st0 cy_trans cy_irrefl
      cy_in1 cy_in2 cy_closed1 cy_closed2 hcW0 hcW1 hcW2
  obtain ⟨t, hhead⟩ := fold_head_three hperm hresp
  rw [hhead, cy_merge_eq] at hfold
  injection hfold with h1 h2
  injection h1 with h3 h4
  exact absurd h3 (by decide)

open Classical in
/-- **`shesha_presplice` as stated is FALSE** (its exact ∀-closure): at the
same instance, the demanded pre-splice forest `T` would have to *be* the
merge output (the union has no deletes, so the collapse is the identity),
whose root row `[1, 3, 2]` places `1` left of `3` — against
`vis (ins 1) (ins 3)` and the anti-`vis` row-order clause. -/
theorem shesha_presplice_refuted :
    ¬ (∀ (C' : Configuration SheshaD), SheshaHonest C' →
        (∀ {a b c : Op SAppOp}, C'.vis a b → C'.vis b c → C'.vis a c) →
        (∀ a : Op SAppOp, ¬ C'.vis a a) →
        ∀ {ev₁ ev₂ : Set (Op SAppOp)} {s₀ s₁ s₂ : Shesha.St},
        (∀ a ∈ ev₁, a ∈ C'.events) → (∀ a ∈ ev₂, a ∈ C'.events) →
        (∀ a b, C'.vis a b → ¬ SheshaD.toCRDTSig.commutes a b →
          b ∈ ev₁ → a ∈ ev₁) →
        (∀ a b, C'.vis a b → ¬ SheshaD.toCRDTSig.commutes a b →
          b ∈ ev₂ → a ∈ ev₂) →
        IsCanonicalStateW SheshaEff (Configuration.core C') (ev₁ ∩ ev₂) s₀ →
        IsCanonicalStateW SheshaEff (Configuration.core C') ev₁ s₁ →
        IsCanonicalStateW SheshaEff (Configuration.core C') ev₂ s₂ →
        ∃ T : Shesha.St,
          Shesha.WF T
          ∧ (∀ p x, x ∈ Shesha.row T p ↔ InsIn (ev₁ ∪ ev₂) x p)
          ∧ (∀ p x y rx ry, (x, rx, SAppOp.insA p) ∈ ev₁ ∪ ev₂ →
              (y, ry, SAppOp.insA p) ∈ ev₁ ∪ ev₂ →
              Shesha.precedes (Shesha.row T p) x y →
              ¬ C'.vis (x, rx, SAppOp.insA p) (y, ry, SAppOp.insA p))
          ∧ Shesha.dropF
              (fun u => decide (DelIn (ev₁ ∪ ev₂) u)) T
              = SheshaD.mergeL s₀ s₁ s₂) := by
  intro h
  obtain ⟨T, hwfT, hrows, hcompat, hmerge⟩ :=
    h Cy cy_honest cy_trans cy_irrefl (ev₁ := EV1) (ev₂ := EV2)
      cy_in1 cy_in2 cy_closed1 cy_closed2 hcW0 hcW1 hcW2
  have hnodel : ∀ u, ¬ DelIn (EV1 ∪ EV2) u := by
    rintro u ⟨t, r, hm⟩
    rcases hm with hm | hm
    · rcases hm with h' | h' | h' <;>
        exact SAppOp.noConfusion (congrArg (fun o : Op SAppOp => o.2.2) h')
    · rcases hm with h' | h' <;>
        exact SAppOp.noConfusion (congrArg (fun o : Op SAppOp => o.2.2) h')
  have hid : Shesha.dropF (fun u => decide (DelIn (EV1 ∪ EV2) u)) T = T := by
    rw [Shesha.dropF_congr (D' := fun _ => false)
      (fun u => decide_eq_false (hnodel u)) T, Shesha.dropF_false]
  have hTM : T = SheshaD.mergeL st0 st1 st0 := by
    rw [← hid]
    exact hmerge
  subst hTM
  have hprec : Shesha.precedes (Shesha.row (SheshaD.mergeL st0 st1 st0) 0) 1 3 := by
    rw [cy_merge_eq,
      show Shesha.row [Shesha.Tree.node 1 [], Shesha.Tree.node 3 [],
        Shesha.Tree.node 2 []] 0 = [1, 3, 2] by decide]
    exact List.Sublist.cons₂ _ (List.Sublist.cons₂ _ (List.nil_sublist _))
  exact hcompat 0 1 3 0 0 (Or.inl (Or.inl rfl)) (Or.inl (Or.inr (Or.inr rfl)))
    hprec ⟨Or.inl rfl, rfl⟩

#print axioms shesha_join_at_eff_refuted
#print axioms shesha_presplice_refuted

end SheshaPrespliceCX
end Sal.ConditionedMRDTs
