import Sal.ConditionedMRDTs.MRDT_Instances.Shesha.Shesha_Presplice

/-! # Shesha: the join hook, as originally stated, is FALSE

`shesha_join_at` (*every* `SheshaHonest`
configuration admits `JoinLemma3At`) is **refuted** here by an explicit
honest configuration and an explicit misaligned canonical triple.

The root cause: with `rc := Either`, `loOn` constrains only non-commuting
*vis*-pairs, so a concurrent pair `(ins x←a, del a)` is enumerable in either
order, and the two orders fold to states with **different live sets** (the
insert no-ops when the delete lands first). `IsCanonicalState` is
existential, so the LCA slot and the branch slots of `JoinLemma3At` may be
handed folds of *incompatible* enumeration choices. Here: three events

    e₁ = ins 1←⌂ (ts 1),  e₂ = ins 2←1 (ts 2, saw e₁),  e₃ = del 1 (ts 3, saw e₁),

`e₂ ∥ e₃`, all honest. With `ev₁ = ev₂ = {e₁,e₂,e₃}`, the delete-first fold
`[]` is canonical for the LCA slot while the insert-first fold `[2]` is
canonical for both branch slots. The merge then sees `2` live in both
branches but absent from the LCA, classifies it as *born twice*, and emits
it twice: `merge [] [2] [2] = [2,2]`, not the fold of any enumeration.

The queue's direct-witness route never met this because the queue's
canonical states are unique per event set; Shesha's are not. The hook in
`Shesha_Cond.lean` restricts the witness class to **effective**
enumerations (every insert applies), which real executions produce and
which realigns the three slots' live sets.

Axiom note: the merge computation runs through `List.mergeSort`, which the
kernel cannot reduce, so the single computational leaf `cx_merge_eq` uses
`native_decide` (axiom `Lean.ofReduceBool`); everything else is `decide`. -/

namespace Sal.ConditionedMRDTs
namespace SheshaJoinCX

open Sal.Emulation

/-- `ins 1←⌂` at replica 0, timestamp 1. -/
def e1 : Op SAppOp := (1, 0, SAppOp.insA 0)
/-- `ins 2←1` at replica 0, timestamp 2 (its issuer saw `e1`). -/
def e2 : Op SAppOp := (2, 0, SAppOp.insA 1)
/-- `del 1` at replica 1, timestamp 3 (its issuer saw `e1` only). -/
def e3 : Op SAppOp := (3, 1, SAppOp.delA 1)

/-- Replica 0's observed set. -/
def SA : Set (Op SAppOp) := fun x => x = e1 ∨ x = e2
/-- Replica 1's observed set. -/
def SB : Set (Op SAppOp) := fun x => x = e1 ∨ x = e3
/-- The full event universe (also the `ev₁ = ev₂` of the refutation). -/
def EU : Set (Op SAppOp) := fun x => x = e1 ∨ x = e2 ∨ x = e3

/-- Visibility: `e1` precedes `e2` and `e3`; `e2 ∥ e3`. -/
def visx (a b : Op SAppOp) : Prop := a = e1 ∧ (b = e2 ∨ b = e3)

/-- The replica-sets function of the counterexample configuration. -/
def Lfun : Replica → Option (Set (Op SAppOp)) :=
  fun r => if r = 0 then some SA else if r = 1 then some SB else none

theorem Lfun_mem {r : Replica} {s : Set (Op SAppOp)} {a : Op SAppOp}
    (h : Lfun r = some s) (ha : s a) : a = e1 ∨ a = e2 ∨ a = e3 := by
  rw [Lfun] at h
  by_cases h0 : r = 0
  · rw [if_pos h0, Option.some.injEq] at h
    rcases (h ▸ ha : SA a) with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · rw [if_neg h0] at h
    by_cases h1 : r = 1
    · rw [if_pos h1, Option.some.injEq] at h
      rcases (h ▸ ha : SB a) with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr h')
    · rw [if_neg h1] at h
      exact absurd h (by simp)

theorem SA_e1 : SA e1 := Or.inl rfl
theorem SB_e1 : SB e1 := Or.inl rfl
theorem L0 : Lfun 0 = some SA := rfl
theorem L1 : Lfun 1 = some SB := rfl

private theorem ver0 {v : Version} {s : Shesha.St} {e : Set (Op SAppOp)}
    (hv : (if v = 0 then some (SheshaD.init, (∅ : Set (Op SAppOp))) else none)
      = some (s, e)) : e = ∅ := by
  by_cases h : v = 0
  · rw [if_pos h, Option.some.injEq, Prod.mk.injEq] at hv
    exact hv.2.symm
  · rw [if_neg h] at hv
    exact absurd hv (by simp)

/-- The honest counterexample configuration: two replicas, `{e1,e2}` and
`{e1,e3}`; a trivial one-version store. -/
def Cx : Configuration SheshaD where
  N := fun r => if r = 0 then some (sheshaUpdate (sheshaUpdate SheshaD.init e1) e2)
    else if r = 1 then some (sheshaUpdate (sheshaUpdate SheshaD.init e1) e3) else none
  L := Lfun
  vis := visx
  dom_eq := by
    intro r
    by_cases h0 : r = 0
    · simp [Lfun, h0]
    · by_cases h1 : r = 1 <;> simp [Lfun, h0, h1]
  vis_src := fun h => ⟨0, SA, L0, h.1 ▸ SA_e1⟩
  vis_tgt := by
    rintro a b ⟨-, rfl | rfl⟩
    · exact ⟨0, SA, L0, Or.inr rfl⟩
    · exact ⟨1, SB, L1, Or.inr rfl⟩
  vis_causal := by
    rintro a b r s ⟨rfl, -⟩ hLr -
    rw [Lfun] at hLr
    by_cases h0 : r = 0
    · rw [if_pos h0, Option.some.injEq] at hLr
      exact hLr ▸ SA_e1
    · rw [if_neg h0] at hLr
      by_cases h1 : r = 1
      · rw [if_pos h1, Option.some.injEq] at hLr
        exact hLr ▸ SB_e1
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
    rintro a b ⟨rfl, rfl | rfl⟩ <;> decide
  vis_total_same_replica := by
    intro a b r s r' s' hLr hsa hLr' hsb hne hrid
    rcases Lfun_mem hLr hsa with rfl | rfl | rfl <;>
      rcases Lfun_mem hLr' hsb with rfl | rfl | rfl <;>
      first
        | exact absurd rfl hne
        | exact absurd hrid (by decide)
        | exact Or.inl ⟨rfl, Or.inl rfl⟩
        | exact Or.inl ⟨rfl, Or.inr rfl⟩
        | exact Or.inr ⟨rfl, Or.inl rfl⟩
        | exact Or.inr ⟨rfl, Or.inr rfl⟩
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

/-! ## Honesty of `Cx` -/

theorem events_cases {a : Op SAppOp} (h : a ∈ Cx.events) :
    a = e1 ∨ a = e2 ∨ a = e3 := by
  obtain ⟨r, s, hLr, hsa⟩ := h
  exact Lfun_mem hLr hsa

/-- `e1`'s causal past is empty. -/
theorem perm_past_e1 {π : List (Op SAppOp)}
    (hπ : listPermOf π {e' ∈ Cx.events | Cx.vis e' e1}) : π = [] := by
  cases π with
  | nil => rfl
  | cons x rest =>
    have hx := (hπ.2 x).mp (List.mem_cons_self ..)
    rcases hx.2.2 with h | h <;> exact absurd h (by decide)

/-- A `listPermOf` of a set that is exactly `{e1}` is the list `[e1]`. -/
theorem perm_of_singleton {π : List (Op SAppOp)} {P : Set (Op SAppOp)}
    (hπ : listPermOf π P) (hiff : ∀ x, x ∈ P ↔ x = e1) : π = [e1] := by
  cases π with
  | nil =>
    exact absurd ((hπ.2 e1).mpr ((hiff e1).mpr rfl)) (by simp)
  | cons x rest =>
    have hx : x = e1 := (hiff x).mp ((hπ.2 x).mp (List.mem_cons_self ..))
    subst hx
    cases rest with
    | nil => rfl
    | cons y r2 =>
      have hy : y = e1 :=
        (hiff y).mp ((hπ.2 y).mp (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      subst hy
      exact absurd (List.mem_cons_self ..) (List.nodup_cons.mp hπ.1).1

theorem past_e2_iff :
    ∀ x, x ∈ {e' ∈ Cx.events | Cx.vis e' e2} ↔ x = e1 := by
  intro x
  constructor
  · rintro ⟨-, rfl, -⟩
    rfl
  · rintro rfl
    exact ⟨⟨0, SA, L0, SA_e1⟩, rfl, Or.inl rfl⟩

theorem past_e3_iff :
    ∀ x, x ∈ {e' ∈ Cx.events | Cx.vis e' e3} ↔ x = e1 := by
  intro x
  constructor
  · rintro ⟨-, rfl, -⟩
    rfl
  · rintro rfl
    exact ⟨⟨0, SA, L0, SA_e1⟩, rfl, Or.inr rfl⟩

/-- **`Cx` is honest**: every event's generation guard holds at the fold of
every enumeration of its causal past. -/
theorem cx_honest : SheshaHonest Cx := by
  intro e he π hπ
  rcases events_cases he with rfl | rfl | rfl
  · rw [perm_past_e1 hπ]
    exact ⟨by decide, by decide, Or.inl rfl⟩
  · rw [perm_of_singleton hπ past_e2_iff]
    exact ⟨by decide, by decide, Or.inr (by decide)⟩
  · rw [perm_of_singleton hπ past_e3_iff]
    show (1 : Nat) ∈ Shesha.read (applySeq SheshaD.toCRDTSig SheshaD.init [e1])
    decide

/-! ## The misaligned canonical triple -/

/-- The insert-first fold `[2]`, canonical for the branch slots. -/
def stA : Shesha.St := [Shesha.Tree.node 2 []]

/-- With `rc := Either`, a `loOn`-edge is a `vis`-edge. -/
theorem loOn_vis {ev : Set (Op SAppOp)} {a b : Op SAppOp}
    (h : loOn (Configuration.core Cx) ev a b) : visx a b := by
  rcases h with ⟨hv, -⟩ | ⟨-, -, hrc, -⟩
  · exact hv
  · exact RcRes.noConfusion hrc

theorem ncomm_e1_e2 : ¬ SheshaD.toCRDTSig.commutes e1 e2 :=
  fun h => absurd (h []) (by decide)

theorem ncomm_e1_e3 : ¬ SheshaD.toCRDTSig.commutes e1 e3 :=
  fun h => absurd (h []) (by decide)

theorem loOn_e1_e2 {ev : Set (Op SAppOp)} :
    loOn (Configuration.core Cx) ev e1 e2 :=
  Or.inl ⟨⟨rfl, Or.inl rfl⟩, ncomm_e1_e2⟩

theorem loOn_e1_e3 {ev : Set (Op SAppOp)} :
    loOn (Configuration.core Cx) ev e1 e3 :=
  Or.inl ⟨⟨rfl, Or.inr rfl⟩, ncomm_e1_e3⟩

theorem resp_123 {ev : Set (Op SAppOp)} :
    respects [e1, e2, e3] (loOn (Configuration.core Cx) ev) := by
  refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.pairwise_singleton _ _))
  · rintro b - hlo
    rcases loOn_vis hlo with ⟨-, h | h⟩ <;> exact absurd h (by decide)
  · rintro b hb hlo
    rw [List.mem_singleton] at hb
    subst hb
    exact absurd (loOn_vis hlo).1 (by decide)

theorem resp_132 {ev : Set (Op SAppOp)} :
    respects [e1, e3, e2] (loOn (Configuration.core Cx) ev) := by
  refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.pairwise_singleton _ _))
  · rintro b - hlo
    rcases loOn_vis hlo with ⟨-, h | h⟩ <;> exact absurd h (by decide)
  · rintro b hb hlo
    rw [List.mem_singleton] at hb
    subst hb
    exact absurd (loOn_vis hlo).1 (by decide)

/-- The branch slots: `[2]` is canonical for `{e1,e2,e3}` (insert-first). -/
theorem hc1 : IsCanonicalState (Configuration.core Cx) EU stA :=
  ⟨[e1, e2, e3],
    ⟨by decide, fun a => by
      rw [List.mem_cons, List.mem_cons, List.mem_singleton]
      exact Iff.rfl⟩,
    resp_123, by decide⟩

/-- The LCA slot: `[]` is canonical for `{e1,e2,e3} ∩ {e1,e2,e3}`
(delete-first; the insert of `2` no-ops). -/
theorem hc0 : IsCanonicalState (Configuration.core Cx) (EU ∩ EU)
    ([] : Shesha.St) :=
  ⟨[e1, e3, e2],
    ⟨by decide, fun a => by
      rw [List.mem_cons, List.mem_cons, List.mem_singleton]
      constructor
      · rintro (rfl | rfl | rfl)
        · exact ⟨Or.inl rfl, Or.inl rfl⟩
        · exact ⟨Or.inr (Or.inr rfl), Or.inr (Or.inr rfl)⟩
        · exact ⟨Or.inr (Or.inl rfl), Or.inr (Or.inl rfl)⟩
      · rintro ⟨h, -⟩
        rcases h with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inr rfl)
        · exact Or.inr (Or.inl rfl)⟩,
    resp_132, by decide⟩

/-- A nodup enumeration of a two-element set is one of the two orders. -/
theorem perm_two {ρ : List (Op SAppOp)} {u v : Op SAppOp} (huv : u ≠ v)
    (hnd : ρ.Nodup) (hmem : ∀ a, a ∈ ρ ↔ a = u ∨ a = v) :
    ρ = [u, v] ∨ ρ = [v, u] := by
  cases ρ with
  | nil => exact absurd ((hmem u).mpr (Or.inl rfl)) (by simp)
  | cons x rest =>
    have htwo : ∀ (w' : Op SAppOp),
        (∀ a, a ∈ x :: rest → a = x ∨ a = w') → w' ∈ rest → rest = [w'] := by
      intro w' hcases hw'
      cases rest with
      | nil => exact absurd hw' (by simp)
      | cons y r2 =>
        have hy : y = w' := by
          rcases hcases y (List.mem_cons_of_mem _ (List.mem_cons_self ..))
            with hy | hy
          · exact absurd (List.mem_cons.mpr (Or.inl hy.symm))
              (List.nodup_cons.mp hnd).1
          · exact hy
        cases r2 with
        | nil => rw [hy]
        | cons z r3 =>
          rcases hcases z (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_self ..))) with hz | hz
          · exact absurd (List.mem_cons.mpr (Or.inr
              (List.mem_cons.mpr (Or.inl hz.symm)))) (List.nodup_cons.mp hnd).1
          · exact absurd (List.mem_cons.mpr (Or.inl (hy.trans hz.symm)))
              (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
    rcases (hmem x).mp (List.mem_cons_self ..) with hx | hx
    · refine Or.inl ?_
      have hv' : v ∈ rest := by
        rcases List.mem_cons.mp ((hmem v).mpr (Or.inr rfl)) with h | h
        · exact absurd (h.trans hx).symm huv
        · exact h
      have hcases : ∀ a, a ∈ x :: rest → a = x ∨ a = v := by
        intro a ha
        rcases (hmem a).mp ha with h | h
        · exact Or.inl (h.trans hx.symm)
        · exact Or.inr h
      rw [htwo v hcases hv', hx]
    · refine Or.inr ?_
      have hu' : u ∈ rest := by
        rcases List.mem_cons.mp ((hmem u).mpr (Or.inl rfl)) with h | h
        · exact absurd (h.trans hx) huv
        · exact h
      have hcases : ∀ a, a ∈ x :: rest → a = x ∨ a = u := by
        intro a ha
        rcases (hmem a).mp ha with h | h
        · exact Or.inr h
        · exact Or.inl (h.trans hx.symm)
      rw [htwo u hcases hu', hx]

/-! ## The refutation -/

theorem cx_trans : ∀ {a b c : Op SAppOp},
    (Configuration.core Cx).vis a b → (Configuration.core Cx).vis b c →
    (Configuration.core Cx).vis a c := by
  rintro a b c ⟨rfl, rfl | rfl⟩ ⟨hb, -⟩ <;> exact absurd hb (by decide)

theorem cx_irrefl : ∀ a : Op SAppOp, ¬ (Configuration.core Cx).vis a a := by
  rintro a ⟨rfl, h | h⟩ <;> exact absurd h (by decide)

theorem cx_in : ∀ a ∈ EU, a ∈ (Configuration.core Cx).events := by
  rintro a (rfl | rfl | rfl)
  · exact ⟨0, SA, L0, SA_e1⟩
  · exact ⟨0, SA, L0, Or.inr rfl⟩
  · exact ⟨1, SB, L1, Or.inr rfl⟩

theorem cx_closed : ∀ a b, (Configuration.core Cx).vis a b →
    ¬ SheshaD.toCRDTSig.commutes a b → b ∈ EU → a ∈ EU := by
  rintro a b ⟨rfl, -⟩ - -
  exact Or.inl rfl

/-- **The join hook is FALSE.** An honest configuration exists at
which `JoinLemma3At` fails: the misaligned canonical triple
`s₀ = [], s₁ = s₂ = [2]` makes `merge` emit `2` twice, and `[2,2]` is not
the fold of any `loOn`-respecting enumeration of the union. -/
theorem shesha_join_at_refuted :
    ¬ (∀ C', SheshaHonest C' → JoinLemma3At SheshaD (Configuration.core C')) := by
  intro h
  obtain ⟨ρ, hperm, hresp, hfold⟩ :=
    h Cx cx_honest EU EU ([] : Shesha.St) stA stA cx_trans cx_irrefl
      cx_in cx_in cx_closed cx_closed hc0 hc1 hc1
  have hM : SheshaD.mergeL ([] : Shesha.St) stA stA
      = [Shesha.Tree.node 2 [], Shesha.Tree.node 2 []] := by native_decide
  rw [hM] at hfold
  have hmemEU : ∀ a, a ∈ ρ ↔ a = e1 ∨ a = e2 ∨ a = e3 := by
    intro a
    rw [hperm.2 a]
    constructor
    · rintro (h' | h') <;> exact h'
    · exact Or.inl
  cases ρ with
  | nil => exact absurd ((hmemEU e1).mpr (Or.inl rfl)) (by simp)
  | cons x rest =>
    have hpc := (List.pairwise_cons.mp hresp).1
    have hxrest : ∀ a, a ∈ EU → a ≠ x → a ∈ rest := by
      intro a ha hne
      rcases List.mem_cons.mp ((hmemEU a).mpr ha) with h' | h'
      · exact absurd h' hne
      · exact h'
    rcases (hmemEU x).mp (List.mem_cons_self ..) with rfl | rfl | rfl
    · -- head is e1; the tail enumerates {e2, e3}
      have hrmem : ∀ a, a ∈ rest ↔ a = e2 ∨ a = e3 := by
        intro a
        constructor
        · intro ha
          rcases (hmemEU a).mp (List.mem_cons_of_mem _ ha) with rfl | h'
          · exact absurd ha (List.nodup_cons.mp hperm.1).1
          · exact h'
        · rintro (rfl | rfl)
          · exact hxrest e2 (Or.inr (Or.inl rfl)) (by decide)
          · exact hxrest e3 (Or.inr (Or.inr rfl)) (by decide)
      rcases perm_two (by decide) (List.nodup_cons.mp hperm.1).2 hrmem
        with hr | hr
      · rw [hr] at hfold
        have hF : applySeq SheshaD.toCRDTSig SheshaD.init [e1, e2, e3]
            = [Shesha.Tree.node 2 []] := by decide
        rw [hF] at hfold
        injection hfold with _ h2
        cases h2
      · rw [hr] at hfold
        have hF : applySeq SheshaD.toCRDTSig SheshaD.init [e1, e3, e2]
            = ([] : Shesha.St) := by decide
        rw [hF] at hfold
        cases hfold
    · -- head e2 would invert the loOn-edge e1 → e2
      exact absurd loOn_e1_e2
        (hpc e1 (hxrest e1 (Or.inl rfl) (by decide)))
    · -- head e3 would invert the loOn-edge e1 → e3
      exact absurd loOn_e1_e3
        (hpc e1 (hxrest e1 (Or.inl rfl) (by decide)))

#print axioms shesha_join_at_refuted

end SheshaJoinCX
end Sal.ConditionedMRDTs
