import Sal.CRDTs.Metatheory.Assoc_CounterModel
import Sal.CRDTs.Metatheory.RA_Lin_Of_Join

/-!
# The lattice counter-model breaks RA-linearizability on a REACHABLE
# configuration

`Assoc_CounterModel.lean` shows `AWSetF` satisfies
`CoreVCs` + the full bounded-semilattice laws yet violates
`JoinPeelVCs` and the Join Lemma. That alone leaves a loophole: maybe
`JoinPeelVCs`/`JoinLemma` are stronger than the metatheorem needs, and
some *other* proof route derives RA-linearizability from
`CoreVCs + ACI`. This file closes the loophole: the five-step
execution

    createReplica 1;
    apply add@r0 (event `aF`, t = 0);
    merge r1 ← r0;                     -- r1's set becomes {aF}
    apply rem@r0 (event `eF`, t = 1);  -- vis aF eF
    merge r1 ← r0                      -- r1's set becomes {aF, eF}

is exhibited step by step from `initConfig`, and its final
configuration `flagC5` is **not RA-linearizable**: replica 1 holds a
state with flag `true` (the joins preserve `aF`'s add-flag), but the
only `lo`-respecting enumeration of `{aF, eF}` is `[aF, eF]`
(`vis aF eF` and add/rem do not commute), which folds to flag
`false`.

Headline: `ra_linearizability_fails_for_lattice_CRDTs`. The
metatheorem's per-CRDT hypothesis (`JoinPeelVCs`) cannot be
weakened to the ACI lattice laws: *the conclusion itself* fails for a
`CoreVCs`+ACI signature on a reachable configuration. The missing
demarcation is update-inflationarity
(`AWSetF_update_not_inflationary`).
-/

namespace Sal.Emulation

open Classical

/-! ### The states and event sets along the execution -/

/-- Replica 0 after `aF`. -/
noncomputable def stA : AWSetF.State := AWSetF.update AWSetF.init aF
/-- Replica 0 after `aF; eF`. -/
noncomputable def stAE : AWSetF.State := AWSetF.update stA eF
/-- Replica 1 after the first merge (flag `true`). -/
noncomputable def stM1 : AWSetF.State := AWSetF.merge AWSetF.init stA
/-- Replica 1 after the second merge (flag `true ∨ false = true`). -/
noncomputable def stM2 : AWSetF.State := AWSetF.merge stM1 stAE

/-- Replica 0's set after `aF`. -/
def evA : Set (Op AWSetF.AppOp) := ∅ ∪ {aF}
/-- Replica 1's set after the first merge. -/
def evM1 : Set (Op AWSetF.AppOp) := ∅ ∪ evA
/-- Replica 0's set after `eF`. -/
def evAE : Set (Op AWSetF.AppOp) := evA ∪ {eF}
/-- Replica 1's set after the second merge. -/
def evM2 : Set (Op AWSetF.AppOp) := evM1 ∪ evAE

private theorem mem_evA : ∀ x ∈ evA, x = aF := by
  rintro x (h | h)
  · exact h.elim
  · exact h

private theorem mem_evM1 : ∀ x ∈ evM1, x = aF := by
  rintro x (h | h)
  · exact h.elim
  · exact mem_evA x h

private theorem mem_evAE : ∀ x ∈ evAE, x = aF ∨ x = eF := by
  rintro x (h | h)
  · exact Or.inl (mem_evA x h)
  · exact Or.inr h

private theorem mem_evM2 : ∀ x ∈ evM2, x = aF ∨ x = eF := by
  rintro x (h | h)
  · exact Or.inl (mem_evM1 x h)
  · exact mem_evAE x h

/-! ### The per-step replica maps -/

noncomputable def N1 : Replica → Option AWSetF.State :=
  updateRep (initConfig AWSetF).N 1 AWSetF.init
noncomputable def L1 : Replica → Option (Set (Op AWSetF.AppOp)) :=
  updateRep (initConfig AWSetF).L 1 ∅
noncomputable def N2 : Replica → Option AWSetF.State := updateRep N1 0 stA
noncomputable def L2 : Replica → Option (Set (Op AWSetF.AppOp)) := updateRep L1 0 evA
noncomputable def N3 : Replica → Option AWSetF.State := updateRep N2 1 stM1
noncomputable def L3 : Replica → Option (Set (Op AWSetF.AppOp)) := updateRep L2 1 evM1
noncomputable def N4 : Replica → Option AWSetF.State := updateRep N3 0 stAE
noncomputable def L4 : Replica → Option (Set (Op AWSetF.AppOp)) := updateRep L3 0 evAE
noncomputable def N5 : Replica → Option AWSetF.State := updateRep N4 1 stM2
noncomputable def L5 : Replica → Option (Set (Op AWSetF.AppOp)) := updateRep L4 1 evM2

private theorem L1_cases {r : Replica} {s : Set (Op AWSetF.AppOp)}
    (hL : L1 r = some s) : s = ∅ := by
  by_cases h1 : r = 1
  · simp [L1, updateRep, h1] at hL
    exact hL.symm
  · by_cases h0 : r = 0
    · simp [L1, updateRep, initConfig, h1, h0] at hL
      exact hL.symm
    · simp [L1, updateRep, initConfig, h1, h0] at hL

private theorem L2_cases {r : Replica} {s : Set (Op AWSetF.AppOp)}
    (hL : L2 r = some s) : ∀ x ∈ s, x = aF := by
  by_cases h0 : r = 0
  · simp [L2, updateRep, h0] at hL
    rw [← hL]
    exact mem_evA
  · simp [L2, updateRep, h0] at hL
    rw [L1_cases hL]
    intro x hx
    exact hx.elim

private theorem L3_cases {r : Replica} {s : Set (Op AWSetF.AppOp)}
    (hL : L3 r = some s) : ∀ x ∈ s, x = aF := by
  by_cases h1 : r = 1
  · simp [L3, updateRep, h1] at hL
    rw [← hL]
    exact mem_evM1
  · simp [L3, updateRep, h1] at hL
    exact L2_cases hL

private theorem L4_cases {r : Replica} {s : Set (Op AWSetF.AppOp)}
    (hL : L4 r = some s) : ∀ x ∈ s, x = aF ∨ x = eF := by
  by_cases h0 : r = 0
  · simp [L4, updateRep, h0] at hL
    rw [← hL]
    exact mem_evAE
  · simp [L4, updateRep, h0] at hL
    exact fun x hx => Or.inl (L3_cases hL x hx)

private theorem L5_cases {r : Replica} {s : Set (Op AWSetF.AppOp)}
    (hL : L5 r = some s) : ∀ x ∈ s, x = aF ∨ x = eF := by
  by_cases h1 : r = 1
  · simp [L5, updateRep, h1] at hL
    rw [← hL]
    exact mem_evM2
  · simp [L5, updateRep, h1] at hL
    exact L4_cases hL

/-! ### The five configurations -/

/-- After `createReplica 1`. -/
noncomputable def flagC1 : Configuration AWSetF where
  N := N1
  L := L1
  vis := fun _ _ => False
  dom_eq := by
    intro r
    by_cases h1 : r = 1
    · simp [N1, L1, updateRep, h1]
    · by_cases h0 : r = 0 <;>
        simp [N1, L1, updateRep, initConfig, h1, h0]
  vis_src := fun h => absurd h id
  vis_tgt := fun h => absurd h id
  vis_causal := fun h _ _ => absurd h id
  timestamps_distinct := by
    intro a b r s r' s' hL hs _ _ _
    rw [L1_cases hL] at hs
    exact hs.elim
  vis_total_same_replica := by
    intro a b r s r' s' hL hs _ _ _ _
    rw [L1_cases hL] at hs
    exact hs.elim

/-- After `apply add@r0` (event `aF`). -/
noncomputable def flagC2 : Configuration AWSetF where
  N := N2
  L := L2
  vis := fun _ _ => False
  dom_eq := by
    intro r
    by_cases h0 : r = 0
    · simp [N2, L2, updateRep, h0]
    · by_cases h1 : r = 1 <;>
        simp [N2, L2, N1, L1, updateRep, initConfig, h1, h0]
  vis_src := fun h => absurd h id
  vis_tgt := fun h => absurd h id
  vis_causal := fun h _ _ => absurd h id
  timestamps_distinct := by
    intro a b r s r' s' hL hs hL' hs' hne
    rw [L2_cases hL a hs, L2_cases hL' b hs'] at hne
    exact absurd rfl hne
  vis_total_same_replica := by
    intro a b r s r' s' hL hs hL' hs' hne _
    rw [L2_cases hL a hs, L2_cases hL' b hs'] at hne
    exact absurd rfl hne

/-- After `merge r1 ← r0`. -/
noncomputable def flagC3 : Configuration AWSetF where
  N := N3
  L := L3
  vis := fun _ _ => False
  dom_eq := by
    intro r
    by_cases h1 : r = 1
    · simp [N3, L3, updateRep, h1]
    · by_cases h0 : r = 0 <;>
        simp [N3, L3, N2, L2, N1, L1, updateRep, initConfig, h1, h0]
  vis_src := fun h => absurd h id
  vis_tgt := fun h => absurd h id
  vis_causal := fun h _ _ => absurd h id
  timestamps_distinct := by
    intro a b r s r' s' hL hs hL' hs' hne
    rw [L3_cases hL a hs, L3_cases hL' b hs'] at hne
    exact absurd rfl hne
  vis_total_same_replica := by
    intro a b r s r' s' hL hs hL' hs' hne _
    rw [L3_cases hL a hs, L3_cases hL' b hs'] at hne
    exact absurd rfl hne

/-- After `apply rem@r0` (event `eF`): `vis aF eF` appears. -/
noncomputable def flagC4 : Configuration AWSetF where
  N := N4
  L := L4
  vis := fun x y => x = aF ∧ y = eF
  dom_eq := by
    intro r
    by_cases h0 : r = 0
    · simp [N4, L4, updateRep, h0]
    · by_cases h1 : r = 1 <;>
        simp [N4, L4, N3, L3, N2, L2, N1, L1, updateRep, initConfig,
          h1, h0]
  vis_src := by
    rintro x y ⟨rfl, rfl⟩
    exact ⟨0, evAE, rfl, Or.inl (Or.inr rfl)⟩
  vis_tgt := by
    rintro x y ⟨rfl, rfl⟩
    exact ⟨0, evAE, rfl, Or.inr rfl⟩
  vis_causal := by
    rintro x y r s ⟨rfl, rfl⟩ hL hs
    by_cases h0 : r = 0
    · have hs' : s = evAE := by
        simp [L4, updateRep, h0] at hL
        exact hL.symm
      subst hs'
      exact Or.inl (Or.inr rfl)
    · have h3 : L3 r = some s := by
        simp [L4, updateRep, h0] at hL
        exact hL
      exact absurd (L3_cases h3 eF hs) (by simp [aF, eF])
  timestamps_distinct := by
    intro a b r s r' s' hL hs hL' hs' hne
    rcases L4_cases hL a hs with rfl | rfl <;>
      rcases L4_cases hL' b hs' with rfl | rfl <;>
      first
        | exact absurd rfl hne
        | simp [aF, eF]
  vis_total_same_replica := by
    intro a b r s r' s' hL hs hL' hs' hne _
    rcases L4_cases hL a hs with rfl | rfl <;>
      rcases L4_cases hL' b hs' with rfl | rfl <;>
      first
        | exact absurd rfl hne
        | exact Or.inl ⟨rfl, rfl⟩
        | exact Or.inr ⟨rfl, rfl⟩

/-- After the final `merge r1 ← r0` — the refuting configuration. -/
noncomputable def flagC5 : Configuration AWSetF where
  N := N5
  L := L5
  vis := fun x y => x = aF ∧ y = eF
  dom_eq := by
    intro r
    by_cases h1 : r = 1
    · simp [N5, L5, updateRep, h1]
    · by_cases h0 : r = 0 <;>
        simp [N5, L5, N4, L4, N3, L3, N2, L2, N1, L1, updateRep,
          initConfig, h1, h0]
  vis_src := by
    rintro x y ⟨rfl, rfl⟩
    exact ⟨0, evAE, rfl, Or.inl (Or.inr rfl)⟩
  vis_tgt := by
    rintro x y ⟨rfl, rfl⟩
    exact ⟨0, evAE, rfl, Or.inr rfl⟩
  vis_causal := by
    rintro x y r s ⟨rfl, rfl⟩ hL hs
    by_cases h1 : r = 1
    · have hs' : s = evM2 := by
        simp [L5, updateRep, h1] at hL
        exact hL.symm
      subst hs'
      exact Or.inl (Or.inr (Or.inr rfl))
    · have h4 : L4 r = some s := by
        simp [L5, updateRep, h1] at hL
        exact hL
      by_cases h0 : r = 0
      · have hs' : s = evAE := by
          simp [L4, updateRep, h0] at h4
          exact h4.symm
        subst hs'
        exact Or.inl (Or.inr rfl)
      · have h3 : L3 r = some s := by
          simp [L4, updateRep, h0] at h4
          exact h4
        exact absurd (L3_cases h3 eF hs) (by simp [aF, eF])
  timestamps_distinct := by
    intro a b r s r' s' hL hs hL' hs' hne
    rcases L5_cases hL a hs with rfl | rfl <;>
      rcases L5_cases hL' b hs' with rfl | rfl <;>
      first
        | exact absurd rfl hne
        | simp [aF, eF]
  vis_total_same_replica := by
    intro a b r s r' s' hL hs hL' hs' hne _
    rcases L5_cases hL a hs with rfl | rfl <;>
      rcases L5_cases hL' b hs' with rfl | rfl <;>
      first
        | exact absurd rfl hne
        | exact Or.inl ⟨rfl, rfl⟩
        | exact Or.inr ⟨rfl, rfl⟩

/-! ### The five steps -/

private theorem step01 :
    Step AWSetF (initConfig AWSetF) (Label.createReplica 1) flagC1 :=
  Step.createReplica rfl flagC1 rfl rfl rfl

private theorem step12 :
    Step AWSetF flagC1 (Label.apply 0 0 AWOp.add) flagC2 :=
  Step.apply (s := AWSetF.init) (ev := ∅) rfl rfl
    (by
      rintro e' ⟨r, s, hL, hs⟩
      rw [L1_cases hL] at hs
      exact hs.elim)
    flagC2 rfl rfl
    (by
      funext a b
      apply propext
      constructor
      · exact fun h => h.elim
      · rintro (h | ⟨h, _⟩)
        · exact h
        · exact h)

private theorem step23 :
    Step AWSetF flagC2 (Label.merge 1 0) flagC3 :=
  Step.merge (s₁ := AWSetF.init) (s₂ := stA) (ev₁ := ∅) (ev₂ := evA)
    rfl rfl rfl rfl flagC3 rfl rfl rfl

private theorem step34 :
    Step AWSetF flagC3 (Label.apply 1 0 AWOp.rem) flagC4 :=
  Step.apply (s := stA) (ev := evA) rfl rfl
    (by
      rintro e' ⟨r, s, hL, hs⟩
      rw [L3_cases hL e' hs]
      simp [aF, Op.time])
    flagC4 rfl rfl
    (by
      funext a b
      apply propext
      constructor
      · rintro ⟨rfl, rfl⟩
        exact Or.inr ⟨Or.inr rfl, rfl⟩
      · rintro (h | ⟨ha, rfl⟩)
        · exact h.elim
        · exact ⟨mem_evA a ha, rfl⟩)

private theorem step45 :
    Step AWSetF flagC4 (Label.merge 1 0) flagC5 :=
  Step.merge (s₁ := stM1) (s₂ := stAE) (ev₁ := evM1) (ev₂ := evAE)
    rfl rfl rfl rfl flagC5 rfl rfl rfl

/-- **`flagC5` is reachable** from the initial configuration. -/
theorem flagC5_reachable :
    (labeledTS AWSetF).ReachableFrom (initConfig AWSetF) flagC5 :=
  Relation.ReflTransGen.tail
    (Relation.ReflTransGen.tail
      (Relation.ReflTransGen.tail
        (Relation.ReflTransGen.tail
          (Relation.ReflTransGen.tail Relation.ReflTransGen.refl
            ⟨_, step01⟩)
          ⟨_, step12⟩)
        ⟨_, step23⟩)
      ⟨_, step34⟩)
    ⟨_, step45⟩

/-! ### The refutation -/

/-- **`flagC5` is not RA-linearizable.** Replica 1 holds `stM2`
(flag `true`), but the only `lo`-respecting enumeration of its set
`{aF, eF}` is `[aF, eF]` (the edge `aF → eF` is `vis ∧ ¬commutes`),
which folds to flag `false`. -/
theorem flagC5_not_ra_linearizable : ¬ IsRALinearizable flagC5 := by
  intro h
  obtain ⟨π, hp, hr, hf⟩ := h 1 stM2 evM2 rfl rfl
  -- π enumerates the two-element set {aF, eF}.
  have hperm_pair : listPermOf [aF, eF] evM2 := by
    constructor
    · refine List.Pairwise.cons ?_ (List.pairwise_singleton _ _)
      intro b hb
      rw [List.mem_singleton] at hb; subst hb
      simp [aF, eF]
    · intro x
      constructor
      · intro hx
        rcases List.mem_cons.mp hx with h' | h'
        · rw [h']
          exact Or.inl (Or.inr (Or.inr rfl))
        · rw [List.mem_singleton] at h'
          rw [h']
          exact Or.inr (Or.inr rfl)
      · intro hx
        rcases mem_evM2 x hx with h' | h'
        · rw [h']; exact List.mem_cons_self
        · rw [h']; exact List.mem_cons_of_mem _ List.mem_cons_self
  have hlen := listPermOf_length_eq hp hperm_pair
  obtain ⟨x, y, rfl⟩ : ∃ x y, π = [x, y] := by
    rcases π with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩
    · exact absurd hlen (by simp)
    · exact absurd hlen (by simp)
    · exact ⟨x, y, rfl⟩
    · exact absurd hlen (by simp)
  have hx_mem := (hp.2 x).mp List.mem_cons_self
  have hy_mem := (hp.2 y).mp (List.mem_cons_of_mem _ List.mem_cons_self)
  have hxy : x ≠ y := by
    intro hEq
    have hnd := hp.1
    rw [hEq, List.nodup_cons] at hnd
    exact hnd.1 List.mem_cons_self
  rcases mem_evM2 x hx_mem with rfl | rfl
  · rcases mem_evM2 y hy_mem with rfl | rfl
    · exact absurd rfl hxy
    · -- π = [aF, eF]: the fold's flag is false, but stM2's is true.
      have hsnd := congrArg Prod.snd hf
      exact Bool.noConfusion (show (false : Bool) = true from hsnd)
  · rcases mem_evM2 y hy_mem with rfl | rfl
    · -- π = [eF, aF]: violates the mandatory lo-edge aF → eF.
      have hedge : lo flagC5 aF eF :=
        Or.inl ⟨⟨rfl, rfl⟩, AWSetF_not_comm_add_rem rfl rfl⟩
      exact (List.pairwise_cons.mp hr).1 aF List.mem_cons_self hedge
    · exact absurd rfl hxy

/-- **The metatheorem's per-CRDT hypothesis cannot be weakened to the
lattice laws.** There is a CRDT signature satisfying `CoreVCs` and the
full bounded join-semilattice laws whose transition system reaches a
non-RA-linearizable configuration. Contrast
`ra_linearizable_of_core_join`: with `JoinPeelVCs` in place of
`LatticeVCs`, RA-linearizability of every reachable configuration is a
theorem. -/
theorem ra_linearizability_fails_for_lattice_CRDTs :
    ∃ (D : CRDTSig) (C : Configuration D),
      CoreVCs D ∧ LatticeVCs D ∧
      (labeledTS D).ReachableFrom (initConfig D) C ∧
      ¬ IsRALinearizable C :=
  ⟨AWSetF, flagC5, AWSetF_coreVCs, AWSetF_latticeVCs,
   flagC5_reachable, flagC5_not_ra_linearizable⟩

end Sal.Emulation
