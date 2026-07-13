import Sal.ConditionedMRDTs.MRDT_Instances.Shesha.Shesha_Presplice

/-! # Shesha — the row-store residue `shesha_rows_residue` is FALSE

`shesha_rows_residue` (`Shesha_Presplice.lean`, the single owed `sorry` on the
`shesha_ra_linearizable3` capstone path) is **refuted** here by an explicit
honest configuration whose three canonical, `SCoh`-aligned slot witnesses make
the ternary merge display a state that **no pre-splice forest collapses to** —
and, worse, that is **not the fold of any `loOn`-respecting linearization** of
the union at all.

## The countermodel (5 events, one delete)

    e1 = ins 1←⌂   (ts 1, replica 0)   -- the LCA node
    e2 = ins 2←1   (ts 2, replica 0)   -- a child of 1, in branch A
    e5 = del 1     (ts 5, replica 0)   -- branch A deletes 1  (past {e1,e2})
    e4 = ins 4←⌂   (ts 4, replica 2)   -- a root sibling, in branch A
    e3 = ins 3←1   (ts 3, replica 1)   -- a child of 1, in branch B

`ev₁ = {e1,e2,e4,e5}` (branch A), `ev₂ = {e1,e3}` (branch B),
`ev₁ ∩ ev₂ = {e1}`. Because the only common insert is `e1`, `SCoh` is
**vacuous** — the coherence layer that repaired the earlier `W`-join
refutations does not exclude this instance. The three canonical folds are
forced:

    s₀ = fold[e1]          = [1]
    s₁ = fold[e1,e2,e4,e5] = [4, 2]      (1 deleted; 2 re-homed to root after 4)
    s₂ = fold[e1,e3]       = [1, 3]

and the merge (machine-checked below) is `merge s₀ s₁ s₂ = [3, 4, 2]`.

## Why it refutes the residue

Node `1` is a **marker** (dead in A, live in B). Its live children are `3`
(from B, spliced at `1`'s skeleton slot) and `2` (from A, where `1` was
deleted so `2` rode A's re-homed root run — *after* the concurrent sibling
`4`). The merge therefore **splits** `1`'s children around `4`: `[3, 4, 2]`.

A pre-splice store `preRows` must, by `hK1`, put **both** union inserts
anchored at `1` — namely `{2,3}` — in `alGet preRows 1`, and both union
inserts anchored at `0` — namely `{1,4}` — in `alGet preRows 0`. Since `1` is
a union-delete target (`DelIn (ev₁∪ev₂) 1`), `hK6` at the root splices `1`'s
whole (contiguous) expansion into `alGet preRows 0`. With `alGet preRows 0` a
permutation of `[1,4]`, that expansion is either `⟨1's block⟩ ++ [4]` (ends in
`4`) or `[4] ++ ⟨1's block⟩` (starts with `4`) — never `[3,4,2]` (which starts
`3`, ends `2`, with `4` *between* `1`'s two children). So `hK6` at the root is
unsatisfiable: **no `preRows` exists.**

## Scope of the finding

This is the ghost-re-homing failure the frontier note flagged as the risk,
realised: the merge re-homes a *marker's own-branch-deleted* child (`2`) to a
different slot than the marker's live-branch child (`3`). The output `[3,4,2]`
is not the fold of any causal linearization of `{ins1,ins2,ins3,ins4,del1}`
(deleting `1` splices its children contiguously; no root sibling can land
between them), so the anomaly also refutes `IsRALinearizable3` for this merge
version — exactly the RGA criss-cross situation (`AgentNotes.md`, "K2 REFUTED").
`SCoh` does not help: it aligns concurrent *same-anchor* inserts, but here the
split is between a node's own children across the two branches.

Axiom note: the merge and the folds run through `List.mergeSort`, so the
computational leaves use `native_decide` (axiom `Lean.ofReduceBool`); this
file is **off** the capstone path — `shesha_ra_linearizable3` still carries
only its `sorryAx`. -/

namespace Sal.ConditionedMRDTs
namespace SheshaRowsCX

open Sal.Emulation

/-! ## §0 generic list helpers -/

/-- A `listPermOf` of a singleton set `{w}` is the list `[w]`. -/
theorem perm_singleton {π : List (Op SAppOp)} {P : Set (Op SAppOp)} {w : Op SAppOp}
    (hπ : listPermOf π P) (hiff : ∀ x, x ∈ P ↔ x = w) : π = [w] := by
  cases π with
  | nil => exact absurd ((hπ.2 w).mpr ((hiff w).mpr rfl)) (by simp)
  | cons x rest =>
    have hx : x = w := (hiff x).mp ((hπ.2 x).mp (List.mem_cons_self ..))
    subst hx
    cases rest with
    | nil => rfl
    | cons y r2 =>
      have hy : y = x :=
        (hiff y).mp ((hπ.2 y).mp (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      subst hy
      exact absurd (List.mem_cons_self ..) (List.nodup_cons.mp hπ.1).1

/-- A nodup list whose members are exactly `{u,v}` (with `u ≠ v`) is one of the
two orderings. -/
theorem two_orderings {α : Type} {l : List α} {u v : α} (huv : u ≠ v)
    (hnd : l.Nodup) (hmem : ∀ a, a ∈ l ↔ a = u ∨ a = v) :
    l = [u, v] ∨ l = [v, u] := by
  cases l with
  | nil => exact absurd ((hmem u).mpr (Or.inl rfl)) (by simp)
  | cons x rest =>
    have htwo : ∀ (w' : α),
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

/-- `Before` is unsatisfiable on a one-element list. -/
theorem before_singleton_false {w a b : Op SAppOp} : ¬ Before [w] a b := by
  rintro ⟨l1, l2, heq, hb⟩
  cases l1 with
  | nil =>
    rw [List.nil_append] at heq
    injection heq with _ h2
    rw [← h2] at hb
    exact absurd hb List.not_mem_nil
  | cons x xs =>
    rw [List.cons_append] at heq
    injection heq with _ h2
    rcases List.append_eq_nil_iff.mp h2.symm with ⟨-, h⟩
    exact absurd h (by simp)

/-! ## §1 events and sets -/

def e1 : Op SAppOp := (1, 0, SAppOp.insA 0)
def e2 : Op SAppOp := (2, 0, SAppOp.insA 1)
def e3 : Op SAppOp := (3, 1, SAppOp.insA 1)
def e4 : Op SAppOp := (4, 2, SAppOp.insA 0)
def e5 : Op SAppOp := (5, 0, SAppOp.delA 1)

/-- Replica 0's observed set: `{e1,e2,e5}`. -/
def S0 : Set (Op SAppOp) := fun x => x = e1 ∨ x = e2 ∨ x = e5
/-- Replica 1's observed set: `{e1,e3}`. -/
def S1 : Set (Op SAppOp) := fun x => x = e1 ∨ x = e3
/-- Replica 2's observed set: `{e1,e4}`. -/
def S2 : Set (Op SAppOp) := fun x => x = e1 ∨ x = e4

/-- Branch A's event set `ev₁`. -/
def EV1 : Set (Op SAppOp) := fun x => x = e1 ∨ x = e2 ∨ x = e4 ∨ x = e5
/-- Branch B's event set `ev₂`. -/
def EV2 : Set (Op SAppOp) := fun x => x = e1 ∨ x = e3

/-- Visibility: `e1` precedes everything; additionally `e2 → e5`. -/
def visz (a b : Op SAppOp) : Prop :=
  (a = e1 ∧ (b = e2 ∨ b = e3 ∨ b = e4 ∨ b = e5)) ∨ (a = e2 ∧ b = e5)

def Lfun : Replica → Option (Set (Op SAppOp)) :=
  fun r => if r = 0 then some S0 else if r = 1 then some S1
    else if r = 2 then some S2 else none

theorem Lfun_mem {r : Replica} {s : Set (Op SAppOp)} {a : Op SAppOp}
    (h : Lfun r = some s) (ha : s a) :
    a = e1 ∨ a = e2 ∨ a = e3 ∨ a = e4 ∨ a = e5 := by
  rw [Lfun] at h
  by_cases h0 : r = 0
  · rw [if_pos h0, Option.some.injEq] at h
    rcases (h ▸ ha : S0 a) with h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (Or.inr (Or.inr h')))
  · rw [if_neg h0] at h
    by_cases h1 : r = 1
    · rw [if_pos h1, Option.some.injEq] at h
      rcases (h ▸ ha : S1 a) with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr (Or.inl h'))
    · rw [if_neg h1] at h
      by_cases h2 : r = 2
      · rw [if_pos h2, Option.some.injEq] at h
        rcases (h ▸ ha : S2 a) with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
      · rw [if_neg h2] at h
        exact absurd h (by simp)

theorem L0 : Lfun 0 = some S0 := rfl
theorem L1 : Lfun 1 = some S1 := rfl
theorem L2 : Lfun 2 = some S2 := rfl
theorem S0_e1 : S0 e1 := Or.inl rfl
theorem S1_e1 : S1 e1 := Or.inl rfl
theorem S2_e1 : S2 e1 := Or.inl rfl

private theorem ver0 {v : Version} {s : Shesha.St} {e : Set (Op SAppOp)}
    (hv : (if v = 0 then some (SheshaD.init, (∅ : Set (Op SAppOp))) else none)
      = some (s, e)) : e = ∅ := by
  by_cases h : v = 0
  · rw [if_pos h, Option.some.injEq, Prod.mk.injEq] at hv
    exact hv.2.symm
  · rw [if_neg h] at hv
    exact absurd hv (by simp)

/-! ## §2 the honest configuration -/

def Cz : Configuration SheshaD where
  N := fun r => if r = 0 then some (sUpdate (sUpdate (sUpdate SheshaD.init e1) e2) e5)
    else if r = 1 then some (sUpdate (sUpdate SheshaD.init e1) e3)
    else if r = 2 then some (sUpdate (sUpdate SheshaD.init e1) e4) else none
  L := Lfun
  vis := visz
  dom_eq := by
    intro r
    by_cases h0 : r = 0
    · simp [Lfun, h0]
    · by_cases h1 : r = 1
      · simp [Lfun, h1]
      · by_cases h2 : r = 2 <;> simp [Lfun, h0, h1, h2]
  vis_src := by
    rintro a b (⟨rfl, -⟩ | ⟨rfl, -⟩)
    · exact ⟨0, S0, L0, S0_e1⟩
    · exact ⟨0, S0, L0, Or.inr (Or.inl rfl)⟩
  vis_tgt := by
    rintro a b (⟨-, rfl | rfl | rfl | rfl⟩ | ⟨-, rfl⟩)
    · exact ⟨0, S0, L0, Or.inr (Or.inl rfl)⟩
    · exact ⟨1, S1, L1, Or.inr rfl⟩
    · exact ⟨2, S2, L2, Or.inr rfl⟩
    · exact ⟨0, S0, L0, Or.inr (Or.inr rfl)⟩
    · exact ⟨0, S0, L0, Or.inr (Or.inr rfl)⟩
  vis_causal := by
    rintro a b r s hab hLr hsb
    rw [Lfun] at hLr
    have ha : a = e1 ∨ (a = e2 ∧ b = e5) := by
      rcases hab with ⟨rfl, -⟩ | ⟨rfl, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨rfl, rfl⟩
    by_cases h0 : r = 0
    · rw [if_pos h0, Option.some.injEq] at hLr; subst hLr
      rcases ha with rfl | ⟨rfl, -⟩
      · exact S0_e1
      · exact Or.inr (Or.inl rfl)
    · rw [if_neg h0] at hLr
      by_cases h1 : r = 1
      · rw [if_pos h1, Option.some.injEq] at hLr; subst hLr
        rcases ha with rfl | ⟨rfl, rfl⟩
        · exact S1_e1
        · rcases (hsb : S1 e5) with h | h <;> exact absurd h (by decide)
      · rw [if_neg h1] at hLr
        by_cases h2 : r = 2
        · rw [if_pos h2, Option.some.injEq] at hLr; subst hLr
          rcases ha with rfl | ⟨rfl, rfl⟩
          · exact S2_e1
          · rcases (hsb : S2 e5) with h | h <;> exact absurd h (by decide)
        · rw [if_neg h2] at hLr
          exact absurd hLr (by simp)
  timestamps_distinct := by
    intro a b r s r' s' hLr hsa hLr' hsb hne
    rcases Lfun_mem hLr hsa with rfl | rfl | rfl | rfl | rfl <;>
      rcases Lfun_mem hLr' hsb with rfl | rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl hne
        | decide
  causal_mono := by
    rintro a b (⟨rfl, rfl | rfl | rfl | rfl⟩ | ⟨rfl, rfl⟩) <;> decide
  vis_total_same_replica := by
    intro a b r s r' s' hLr hsa hLr' hsb hne hrid
    rcases Lfun_mem hLr hsa with rfl | rfl | rfl | rfl | rfl <;>
      rcases Lfun_mem hLr' hsb with rfl | rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl hne
        | exact absurd hrid (by decide)
        | exact Or.inl (Or.inl ⟨rfl, by decide⟩)
        | exact Or.inl (Or.inr ⟨rfl, by decide⟩)
        | exact Or.inr (Or.inl ⟨rfl, by decide⟩)
        | exact Or.inr (Or.inr ⟨rfl, by decide⟩)
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

theorem events_cases {a : Op SAppOp} (h : a ∈ Cz.events) :
    a = e1 ∨ a = e2 ∨ a = e3 ∨ a = e4 ∨ a = e5 := by
  obtain ⟨r, s, hLr, hsa⟩ := h
  exact Lfun_mem hLr hsa

theorem e1_events : e1 ∈ Cz.events := ⟨0, S0, L0, S0_e1⟩

/-- The causal past of `e2`, `e3`, or `e4` is exactly `{e1}`. -/
theorem past_singleton {e : Op SAppOp} (he : e = e2 ∨ e = e3 ∨ e = e4) :
    ∀ x, x ∈ {e' ∈ Cz.events | Cz.vis e' e} ↔ x = e1 := by
  intro x
  constructor
  · rintro ⟨-, hvis⟩
    rcases hvis with ⟨rfl, -⟩ | ⟨rfl, hb⟩
    · rfl
    · rcases he with rfl | rfl | rfl <;> exact absurd hb (by decide)
  · rintro rfl
    refine ⟨e1_events, ?_⟩
    rcases he with rfl | rfl | rfl
    · exact Or.inl ⟨rfl, Or.inl rfl⟩
    · exact Or.inl ⟨rfl, Or.inr (Or.inl rfl)⟩
    · exact Or.inl ⟨rfl, Or.inr (Or.inr (Or.inl rfl))⟩

/-- The causal past of `e5 = del 1` is exactly `{e1, e2}`. -/
theorem past_e5 : ∀ x, x ∈ {e' ∈ Cz.events | Cz.vis e' e5} ↔ x = e1 ∨ x = e2 := by
  intro x
  constructor
  · rintro ⟨-, hvis⟩
    rcases hvis with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨e1_events, Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr rfl))⟩⟩
    · exact ⟨⟨0, S0, L0, Or.inr (Or.inl rfl)⟩, Or.inr ⟨rfl, rfl⟩⟩

/-- **`Cz` is honest.** -/
theorem cz_honest : SheshaHonest Cz := by
  intro e he π hπ
  rcases events_cases he with rfl | rfl | rfl | rfl | rfl
  · -- e1: empty past
    have hnil : π = [] := by
      cases π with
      | nil => rfl
      | cons x rest =>
        have hx := (hπ.2 x).mp (List.mem_cons_self ..)
        rcases hx.2 with ⟨-, hb⟩ | ⟨-, hb⟩ <;> exact absurd hb (by decide)
    rw [hnil]; exact ⟨by decide, by decide, Or.inl rfl⟩
  · rw [perm_singleton hπ (past_singleton (Or.inl rfl))]
    exact ⟨by decide, by decide, Or.inr (by decide)⟩
  · rw [perm_singleton hπ (past_singleton (Or.inr (Or.inl rfl)))]
    exact ⟨by decide, by decide, Or.inr (by decide)⟩
  · rw [perm_singleton hπ (past_singleton (Or.inr (Or.inr rfl)))]
    exact ⟨by decide, by decide, Or.inl rfl⟩
  · -- e5 = del 1: past {e1,e2}; guard = 1 ∈ read (fold π), holds for both orders
    have hmem : ∀ a, a ∈ π ↔ a = e1 ∨ a = e2 := fun a => (hπ.2 a).trans (past_e5 a)
    rcases two_orderings (show e1 ≠ e2 by decide) hπ.1 hmem with hπ' | hπ' <;>
      · rw [hπ']
        show (1 : Nat) ∈ Shesha.read (applySeq SheshaD.toCRDTSig SheshaD.init _)
        native_decide

/-! ## §3 the three canonical, `SCoh`-aligned slot witnesses -/

def st0 : Shesha.St := [Shesha.Tree.node 1 []]
def st1 : Shesha.St := [Shesha.Tree.node 4 [], Shesha.Tree.node 2 []]
def st2 : Shesha.St := [Shesha.Tree.node 1 [Shesha.Tree.node 3 []]]

theorem loOn_visz {ev : Set (Op SAppOp)} {a b : Op SAppOp}
    (h : loOn (Configuration.core Cz) ev a b) : visz a b := by
  rcases h with ⟨hv, -⟩ | ⟨-, -, hrc, -⟩
  · exact hv
  · exact RcRes.noConfusion hrc

theorem seff0 : SheshaEff [e1] := ⟨Or.inl rfl, trivial⟩
theorem seff1 : SheshaEff [e1, e2, e4, e5] :=
  ⟨Or.inl rfl, Or.inr (by native_decide), Or.inl rfl, trivial, trivial⟩
theorem seff2 : SheshaEff [e1, e3] := ⟨Or.inl rfl, Or.inr (by native_decide), trivial⟩

/-- `ρ₀ = [e1]` is canonical for `ev₁ ∩ ev₂ = {e1}`. -/
theorem hc0 : IsCanonWitness SheshaEff (Configuration.core Cz) (EV1 ∩ EV2) st0 [e1] := by
  refine ⟨⟨by decide, fun a => ?_⟩, List.pairwise_singleton _ _, seff0, by native_decide⟩
  rw [List.mem_singleton]
  constructor
  · rintro rfl; exact ⟨Or.inl rfl, Or.inl rfl⟩
  · rintro ⟨h1, h2⟩
    rcases h2 with rfl | rfl
    · rfl
    · rcases h1 with h | h | h | h <;> exact absurd h (by decide)

/-- `ρ₁ = [e1,e2,e4,e5]` is canonical for `ev₁`, folding to `s₁ = [4,2]`. -/
theorem hc1 : IsCanonWitness SheshaEff (Configuration.core Cz) EV1 st1 [e1, e2, e4, e5] := by
  refine ⟨⟨by decide, fun a => ?_⟩, ?_, seff1, by native_decide⟩
  · constructor
    · intro ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact Or.inl rfl
      rcases List.mem_cons.mp ha with rfl | ha
      · exact Or.inr (Or.inl rfl)
      rcases List.mem_cons.mp ha with rfl | ha
      · exact Or.inr (Or.inr (Or.inl rfl))
      rcases List.mem_cons.mp ha with rfl | ha
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact absurd ha List.not_mem_nil
    · intro ha
      rcases ha with rfl | rfl | rfl | rfl
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  · refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_
      (List.pairwise_singleton _ _)))
    · rintro b hb hlo
      rcases loOn_visz hlo with ⟨-, hd⟩ | ⟨-, hd⟩ <;> exact absurd hd (by decide)
    · rintro b hb hlo
      rcases List.mem_cons.mp hb with rfl | hb2
      · rcases loOn_visz hlo with ⟨hd, -⟩ | ⟨hd, -⟩ <;> exact absurd hd (by decide)
      · rw [List.mem_singleton] at hb2; subst hb2
        rcases loOn_visz hlo with ⟨hd, -⟩ | ⟨hd, -⟩ <;> exact absurd hd (by decide)
    · rintro b hb hlo
      rw [List.mem_singleton] at hb; subst hb
      rcases loOn_visz hlo with ⟨hd, -⟩ | ⟨hd, -⟩ <;> exact absurd hd (by decide)

/-- `ρ₂ = [e1,e3]` is canonical for `ev₂`, folding to `s₂ = [1,[3]]`. -/
theorem hc2 : IsCanonWitness SheshaEff (Configuration.core Cz) EV2 st2 [e1, e3] := by
  refine ⟨⟨by decide, fun a => ?_⟩, ?_, seff2, by native_decide⟩
  · constructor
    · intro ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact Or.inl rfl
      rcases List.mem_cons.mp ha with rfl | ha
      · exact Or.inr rfl
      · exact absurd ha List.not_mem_nil
    · intro ha
      rcases ha with rfl | rfl
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  · refine List.Pairwise.cons ?_ (List.pairwise_singleton _ _)
    rintro b hb hlo
    rcases loOn_visz hlo with ⟨-, hd⟩ | ⟨-, hd⟩ <;> exact absurd hd (by decide)

theorem hK01 : SCoh [e1] [e1, e2, e4, e5] := by
  intro p tx ty rx ry _ _ hbef
  exact absurd hbef before_singleton_false

theorem hK02 : SCoh [e1] [e1, e3] := by
  intro p tx ty rx ry _ _ hbef
  exact absurd hbef before_singleton_false

/-! ## §4 the configuration-shape side conditions -/

theorem cz_trans : ∀ {a b c : Op SAppOp}, Cz.vis a b → Cz.vis b c → Cz.vis a c := by
  rintro a b c hab hbc
  rcases hab with ⟨rfl, -⟩ | ⟨rfl, rfl⟩
  · rcases hbc with ⟨-, rfl | rfl | rfl | rfl⟩ | ⟨-, rfl⟩
    · exact Or.inl ⟨rfl, Or.inl rfl⟩
    · exact Or.inl ⟨rfl, Or.inr (Or.inl rfl)⟩
    · exact Or.inl ⟨rfl, Or.inr (Or.inr (Or.inl rfl))⟩
    · exact Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr rfl))⟩
    · exact Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr rfl))⟩
  · rcases hbc with ⟨hd, -⟩ | ⟨hd, -⟩ <;> exact absurd hd (by decide)

theorem cz_irrefl : ∀ a : Op SAppOp, ¬ Cz.vis a a := by
  rintro a (⟨rfl, hb⟩ | ⟨rfl, hb⟩) <;> exact absurd hb (by decide)

theorem cz_in1 : ∀ a ∈ EV1, a ∈ Cz.events := by
  rintro a (rfl | rfl | rfl | rfl)
  · exact e1_events
  · exact ⟨0, S0, L0, Or.inr (Or.inl rfl)⟩
  · exact ⟨2, S2, L2, Or.inr rfl⟩
  · exact ⟨0, S0, L0, Or.inr (Or.inr rfl)⟩

theorem cz_in2 : ∀ a ∈ EV2, a ∈ Cz.events := by
  rintro a (rfl | rfl)
  · exact e1_events
  · exact ⟨1, S1, L1, Or.inr rfl⟩

theorem cz_closed1 : ∀ a b, Cz.vis a b → ¬ SheshaD.toCRDTSig.commutes a b →
    b ∈ EV1 → a ∈ EV1 := by
  rintro a b hab - -
  rcases hab with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)

theorem cz_closed2 : ∀ a b, Cz.vis a b → ¬ SheshaD.toCRDTSig.commutes a b →
    b ∈ EV2 → a ∈ EV2 := by
  rintro a b hab - hbEV2
  rcases hab with ⟨rfl, -⟩ | ⟨rfl, hb⟩
  · exact Or.inl rfl
  · rcases hbEV2 with h | h <;> exact absurd (hb.symm.trans h) (by decide)

/-! ## §5 the merge output and the impossibility -/

theorem cz_merge_read : Shesha.row (SheshaD.mergeL st0 st1 st2) 0 = [3, 4, 2] := by
  native_decide

/-- The root union inserts are exactly `{1,4}`. -/
theorem insIn_root_iff : ∀ x, InsIn (EV1 ∪ EV2) x 0 ↔ x = 1 ∨ x = 4 := by
  intro x
  constructor
  · rintro ⟨r, hm⟩
    rcases (Set.mem_union _ _ _).mp hm with (h | h | h | h) | (h | h)
    · injection h with hx _; exact Or.inl hx
    · injection h with _ h2; injection h2 with _ h3; exact absurd h3 (by decide)
    · injection h with hx _; exact Or.inr hx
    · injection h with _ h2; injection h2 with _ h3; exact absurd h3 (by decide)
    · injection h with hx _; exact Or.inl hx
    · injection h with _ h2; injection h2 with _ h3; exact absurd h3 (by decide)
  · rintro (rfl | rfl)
    · exact ⟨0, Set.mem_union_left _ (Or.inl rfl)⟩
    · exact ⟨2, Set.mem_union_left _ (Or.inr (Or.inr (Or.inl rfl)))⟩

theorem delIn_one : DelIn (EV1 ∪ EV2) 1 :=
  ⟨5, 0, Set.mem_union_left _ (Or.inr (Or.inr (Or.inr rfl)))⟩

theorem not_delIn_four : ¬ DelIn (EV1 ∪ EV2) 4 := by
  rintro ⟨t, r, hm⟩
  rcases (Set.mem_union _ _ _).mp hm with (h | h | h | h) | (h | h) <;>
    · injection h with _ h2
      injection h2 with _ h3
      exact absurd h3 (by decide)

open Classical in
/-- **`shesha_rows_residue` is refuted.** No `SCoh`-aligned honest instance
admits a pre-splice row store: the merge `[3,4,2]` splits marker `1`'s children
around the concurrent sibling `4`, and `hK6` at the root has no solution. -/
theorem shesha_rows_residue_refuted :
    ¬ (∀ (C' : Configuration SheshaD), SheshaHonest C' →
        (∀ {a b c : Op SAppOp}, C'.vis a b → C'.vis b c → C'.vis a c) →
        (∀ a : Op SAppOp, ¬ C'.vis a a) →
        ∀ {ev₁ ev₂ : Set (Op SAppOp)} {s₀ s₁ s₂ : Shesha.St}
          {ρ₀ ρ₁ ρ₂ : List (Op SAppOp)},
        (∀ a ∈ ev₁, a ∈ C'.events) → (∀ a ∈ ev₂, a ∈ C'.events) →
        (∀ a b, C'.vis a b → ¬ SheshaD.toCRDTSig.commutes a b → b ∈ ev₁ → a ∈ ev₁) →
        (∀ a b, C'.vis a b → ¬ SheshaD.toCRDTSig.commutes a b → b ∈ ev₂ → a ∈ ev₂) →
        IsCanonWitness SheshaEff (Configuration.core C') (ev₁ ∩ ev₂) s₀ ρ₀ →
        IsCanonWitness SheshaEff (Configuration.core C') ev₁ s₁ ρ₁ →
        IsCanonWitness SheshaEff (Configuration.core C') ev₂ s₂ ρ₂ →
        SCoh ρ₀ ρ₁ → SCoh ρ₀ ρ₂ →
        ∃ (preRows : List (Nat × List Nat)) (n : Nat),
          (∀ q x, x ∈ Shesha.alGet preRows q ↔ InsIn (ev₁ ∪ ev₂) x q)
          ∧ (∀ q, (Shesha.alGet preRows q).Nodup)
          ∧ (∀ q c, c ∈ Shesha.alGet preRows q → q < c ∧ c ≤ n)
          ∧ (∀ p tx ty rx ry,
              Before ρ₁ (tx, rx, SAppOp.insA p) (ty, ry, SAppOp.insA p) →
              Shesha.precedes (Shesha.alGet preRows p) ty tx)
          ∧ (∀ p tx ty rx ry,
              Before ρ₂ (tx, rx, SAppOp.insA p) (ty, ry, SAppOp.insA p) →
              Shesha.precedes (Shesha.alGet preRows p) ty tx)
          ∧ (∀ q, q ∈ Shesha.read (SheshaD.mergeL s₀ s₁ s₂) ∨ q = 0 →
              Shesha.expandRow preRows
                  (fun u => decide (DelIn (ev₁ ∪ ev₂) u)) n
                  (Shesha.alGet preRows q)
                = Shesha.row (SheshaD.mergeL s₀ s₁ s₂) q)) := by
  intro h
  obtain ⟨preRows, n, hK1, hK2, hK3, _hK4, _hK5, hK6⟩ :=
    h Cz cz_honest cz_trans cz_irrefl cz_in1 cz_in2 cz_closed1 cz_closed2
      hc0 hc1 hc2 hK01 hK02
  set D : Nat → Bool := fun u => decide (DelIn (EV1 ∪ EV2) u) with hDdef
  have hD1 : D 1 = true := decide_eq_true delIn_one
  have hD4 : D 4 = false := decide_eq_false not_delIn_four
  have hmem0 : ∀ x, x ∈ Shesha.alGet preRows 0 ↔ (x = 1 ∨ x = 4) := by
    intro x; rw [hK1 0 x]; exact insIn_root_iff x
  have h1mem : (1 : Nat) ∈ Shesha.alGet preRows 0 := (hmem0 1).mpr (Or.inl rfl)
  have hcol := hK6 0 (Or.inr rfl)
  rw [cz_merge_read] at hcol
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
    ⟨n - 1, by have := (hK3 0 1 h1mem).2; omega⟩
  rcases two_orderings (show (1 : Nat) ≠ 4 by decide) (hK2 0) hmem0 with h04 | h40
  · -- alGet preRows 0 = [1, 4]: expansion ends in 4, but [3,4,2] ends in 2
    rw [h04] at hcol
    have hexp : Shesha.expandRow preRows D (m + 1) [1, 4]
        = Shesha.expandRow preRows D m (Shesha.alGet preRows 1) ++ [4] := by
      show ([1, 4].flatMap fun u => if D u then
          Shesha.expandRow preRows D m (Shesha.alGet preRows u) else [u]) = _
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [if_pos hD1, if_neg (by rw [hD4]; simp)]
    rw [hexp] at hcol
    have hrev : (4 : Nat) :: (Shesha.expandRow preRows D m (Shesha.alGet preRows 1)).reverse
        = [2, 4, 3] := by
      have h := congrArg List.reverse hcol
      rwa [List.reverse_append, show ([4] : List Nat).reverse = [4] from rfl,
        show ([3, 4, 2] : List Nat).reverse = [2, 4, 3] from rfl,
        List.cons_append, List.nil_append] at h
    injection hrev with h4
    exact absurd h4 (by decide)
  · -- alGet preRows 0 = [4, 1]: expansion starts with 4, but [3,4,2] starts 3
    rw [h40] at hcol
    have hexp : Shesha.expandRow preRows D (m + 1) [4, 1]
        = 4 :: Shesha.expandRow preRows D m (Shesha.alGet preRows 1) := by
      show ([4, 1].flatMap fun u => if D u then
          Shesha.expandRow preRows D m (Shesha.alGet preRows u) else [u]) = _
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [if_neg (by rw [hD4]; simp), if_pos hD1, List.cons_append, List.nil_append]
    rw [hexp] at hcol
    injection hcol with h4 _
    exact absurd h4 (by decide)

#print axioms shesha_rows_residue_refuted

end SheshaRowsCX
end Sal.ConditionedMRDTs
