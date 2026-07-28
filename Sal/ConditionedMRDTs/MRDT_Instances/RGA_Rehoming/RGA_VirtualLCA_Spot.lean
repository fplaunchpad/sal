import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_CondSig
import Sal.ConditionedMRDTs.Metatheory.LCA_Lemma

/-!
# SPOT: the virtual-LCA rule on a concrete criss-cross REHOMING store

Concrete-execution pins for the recursive antichain merge on the rehoming RGA itself,
hand-derived from the probe's directed T1 case
(`whiteboard/litmus/rehoming_vlca_check.py`, `whiteboard/rehoming-vlca-probe.md` §3):
one criss-cross branch **deletes** a node whose **child is inserted concurrently** on
the other branch.  Expected values below are derived by hand in the comments, never
`#eval`'d from the implementation under test.

**Ops** (`α := ℕ`; ids are timestamps; elements are distinct payload numbers):

    i10 = (10, 0, Ins 100 [] 0)   -- insert id 10 (payload 100) under the root
    i20 = (20, 1, Ins 200 [] 0)   -- insert id 20 (payload 200) under the root
    d10 = (25, 0, Del [] 10)      -- delete id 10 (its live chain is empty: parent = root)
    i30 = (30, 1, Ins 300 [] 10)  -- insert id 30 (payload 300) ANCHORED AT 10

**The store** (raw `ver`/`parents`; ranks are version ids; states are the model's own
`do_`/`merge` images of the honest execution, event sets listed by hand):

    0 (init, ∅)                                                    root
    1 = i10 on 0     {10↦(100,0)}            E {i10}          par [0]
    2 = i20 on 0     {20↦(200,0)}            E {i20}          par [0]
    3 = merge(1,2)   {10↦(100,0),20↦(200,0)} E {i10,i20}      par [1,2]  rival m1
    4 = merge(1,2)   (same)                  E {i10,i20}      par [1,2]  rival m2
    5 = d10 on 3     {20↦(200,0)}            E {i10,i20,d10}  par [3]    head A
    6 = i30 on 4     {…, 30↦(300,10)}        E {i10,i20,i30}  par [4]    head B

**The criss-cross.** `CA(5,6) = {1,2,0}`, `MCA(5,6) = {1,2}`: no `IsLCA` version
exists — the gated Merge is blocked (pinned).  The recursion resolves the sub-pair
`(1,2)` through its registered LCA `0` and folds:
`vlca(5,6) = merge σ₀ σ(1) σ(2) = {10↦(100,0), 20↦(200,0)}` — exactly the meet's fold.

**T1 (PASS), hand-derived.**  `mergeL vlca σ(5) σ(6)`: survivor identities
`I = (dl∩da∩db) ∪ (da∖dl) ∪ (db∖dl) = {20} ∪ ∅ ∪ {30} = {20,30}` — the delete of 10
wins (10 sits in the virtual LCA's event view, so side 6's copy is not a fresh add),
and the concurrent child 30 survives with its dead anchor 10 **climbed through the
virtual LCA's chain 10 → 0**: the record REHOMES to the root.  Merged state
`{20↦(200,0), 30↦(300,0)}`.

**T1F (FAIL), hand-derived.**  The fixed single-MCA pick `2` (the branch that never
saw `i10`) in the LCA slot: `dl = {20}`, so `db∖dl = {10,30}` — the deleted id 10
**resurrects** (`{10,20,30}`), and 30 keeps its anchor 10.  The pick disagrees with
the virtual resolution on the read of id 10.
-/

namespace Sal.ConditionedMRDTs.RGAVirtualLCASpot

open Sal.ConditionedMRDTs
open Sal.Emulation
open Sal.ConditionedMRDTs.RGASig (RGACondSig)

/-! ## §1 Ops and the store -/

abbrev O := Op (RGACondSig ℕ).AppOp

def i10 : O := (10, 0, .Ins 100 [] 0)
def i20 : O := (20, 1, .Ins 200 [] 0)
def d10 : O := (25, 0, .Del [] 10)
def i30 : O := (30, 1, .Ins 300 [] 10)

/-- Branch and merge states, as the model's own images of the honest execution. -/
noncomputable def sA : (RGACondSig ℕ).State := do_ (init_st (α := ℕ)) i10
noncomputable def sB : (RGACondSig ℕ).State := do_ (init_st (α := ℕ)) i20
noncomputable def sM : (RGACondSig ℕ).State := _root_.merge (init_st (α := ℕ)) sA sB
noncomputable def sD : (RGACondSig ℕ).State := do_ sM d10
noncomputable def sI : (RGACondSig ℕ).State := do_ sM i30

/-- The ranked store: version ↦ `(state, event set)`. -/
noncomputable def verR : Version → Option ((RGACondSig ℕ).State × Set O) := fun v =>
  if v = 0 then some (init_st (α := ℕ), ∅)
  else if v = 1 then some (sA, {i10})
  else if v = 2 then some (sB, {i20})
  else if v = 3 then some (sM, {i10, i20})
  else if v = 4 then some (sM, {i10, i20})
  else if v = 5 then some (sD, {i10, i20, d10})
  else if v = 6 then some (sI, {i10, i20, i30})
  else none

/-- The version DAG (criss-cross at `(5,6)` over the rivals `3,4`). -/
def parR : Version → List Version := fun v =>
  if v = 1 then [0]
  else if v = 2 then [0]
  else if v = 3 then [1, 2]
  else if v = 4 then [1, 2]
  else if v = 5 then [3]
  else if v = 6 then [4]
  else []

theorem parR_lt : ∀ v p, p ∈ parR v → p < v := by
  intro v p hp
  simp only [parR] at hp
  split_ifs at hp <;> simp_all <;> rcases hp with rfl | rfl <;> decide

/-! ## §2 Reachability inversions -/

theorem re01 : Reaches parR 0 1 := Relation.ReflTransGen.single (by decide)
theorem re02 : Reaches parR 0 2 := Relation.ReflTransGen.single (by decide)
theorem re13 : Reaches parR 1 3 := Relation.ReflTransGen.single (by decide)
theorem re23 : Reaches parR 2 3 := Relation.ReflTransGen.single (by decide)
theorem re14 : Reaches parR 1 4 := Relation.ReflTransGen.single (by decide)
theorem re24 : Reaches parR 2 4 := Relation.ReflTransGen.single (by decide)
theorem re35 : Reaches parR 3 5 := Relation.ReflTransGen.single (by decide)
theorem re46 : Reaches parR 4 6 := Relation.ReflTransGen.single (by decide)

theorem re15 : Reaches parR 1 5 := re13.trans re35
theorem re25 : Reaches parR 2 5 := re23.trans re35
theorem re16 : Reaches parR 1 6 := re14.trans re46
theorem re26 : Reaches parR 2 6 := re24.trans re46

theorem reach0 {w : Version} (h : Reaches parR w 0) : w = 0 := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, _, hstep⟩
  · exact h.symm
  · exact absurd hstep (by simp [parR])

theorem reach1 {w : Version} (h : Reaches parR w 1) : w = 1 ∨ w = 0 := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, hpre, hstep⟩
  · exact Or.inl h.symm
  · have hc : c = 0 := by simpa [parR] using hstep
    subst hc
    exact Or.inr (reach0 hpre)

theorem reach2 {w : Version} (h : Reaches parR w 2) : w = 2 ∨ w = 0 := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, hpre, hstep⟩
  · exact Or.inl h.symm
  · have hc : c = 0 := by simpa [parR] using hstep
    subst hc
    exact Or.inr (reach0 hpre)

theorem reach3 {w : Version} (h : Reaches parR w 3) :
    w = 3 ∨ w = 1 ∨ w = 2 ∨ w = 0 := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, hpre, hstep⟩
  · exact Or.inl h.symm
  · have hc : c = 1 ∨ c = 2 := by simpa [parR] using hstep
    rcases hc with rfl | rfl
    · rcases reach1 hpre with rfl | rfl <;> simp
    · rcases reach2 hpre with rfl | rfl <;> simp

theorem reach4 {w : Version} (h : Reaches parR w 4) :
    w = 4 ∨ w = 1 ∨ w = 2 ∨ w = 0 := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, hpre, hstep⟩
  · exact Or.inl h.symm
  · have hc : c = 1 ∨ c = 2 := by simpa [parR] using hstep
    rcases hc with rfl | rfl
    · rcases reach1 hpre with rfl | rfl <;> simp
    · rcases reach2 hpre with rfl | rfl <;> simp

theorem reach5 {w : Version} (h : Reaches parR w 5) :
    w = 5 ∨ w = 3 ∨ w = 1 ∨ w = 2 ∨ w = 0 := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, hpre, hstep⟩
  · exact Or.inl h.symm
  · have hc : c = 3 := by simpa [parR] using hstep
    subst hc
    rcases reach3 hpre with rfl | rfl | rfl | rfl <;> simp

theorem reach6 {w : Version} (h : Reaches parR w 6) :
    w = 6 ∨ w = 4 ∨ w = 1 ∨ w = 2 ∨ w = 0 := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, hpre, hstep⟩
  · exact Or.inl h.symm
  · have hc : c = 4 := by simpa [parR] using hstep
    subst hc
    rcases reach4 hpre with rfl | rfl | rfl | rfl <;> simp

/-! ## §3 The MCA antichains, hand-derived -/

theorem ca56 {x : Version}
    (hx : x ∈ CommonAnc parR (↑({5} : Finset Version)) 6) :
    x = 1 ∨ x = 2 ∨ x = 0 := by
  obtain ⟨⟨u, hu, hxu⟩, hx6⟩ := hx
  have hu5 : u = 5 := by simpa using hu
  subst hu5
  rcases reach5 hxu with rfl | rfl | rfl | rfl | rfl <;>
    rcases reach6 hx6 with h | h | h | h | h <;> simp_all

/-- `MCA(5,6) = {1,2}` — the criss-cross's proper antichain. -/
theorem mca56R : mcaFinset parR {5} 6 = {1, 2} := by
  ext m
  rw [mem_mcaFinset parR parR_lt]
  constructor
  · rintro ⟨hCA, hmax⟩
    rcases ca56 hCA with rfl | rfl | rfl
    · decide
    · decide
    · exfalso
      have h1CA : (1 : Version) ∈ CommonAnc parR (↑({5} : Finset Version)) 6 :=
        ⟨⟨5, by simp, re15⟩, re16⟩
      exact absurd (hmax 1 h1CA re01) (by decide)
  · intro hm
    have hm' : m = 1 ∨ m = 2 := by
      rcases Finset.mem_insert.mp hm with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_singleton.mp h)
    rcases hm' with rfl | rfl
    · refine ⟨⟨⟨5, by simp, re15⟩, re16⟩, ?_⟩
      intro x hx h1x
      rcases ca56 hx with rfl | rfl | rfl
      · rfl
      · rcases reach2 h1x with h | h <;> exact absurd h (by decide)
      · exact absurd (reach0 h1x) (by decide)
    · refine ⟨⟨⟨5, by simp, re25⟩, re26⟩, ?_⟩
      intro x hx h2x
      rcases ca56 hx with rfl | rfl | rfl
      · rcases reach1 h2x with h | h <;> exact absurd h (by decide)
      · rfl
      · exact absurd (reach0 h2x) (by decide)

theorem ca12 {x : Version}
    (hx : x ∈ CommonAnc parR (↑({1} : Finset Version)) 2) : x = 0 := by
  obtain ⟨⟨u, hu, hxu⟩, hx2⟩ := hx
  have hu1 : u = 1 := by simpa using hu
  subst hu1
  rcases reach1 hxu with rfl | rfl <;> rcases reach2 hx2 with h | h <;> simp_all

/-- The sub-pair `(1,2)` bottoms out at the registered LCA `0`. -/
theorem mca12R : mcaFinset parR {1} 2 = {0} := by
  ext m
  rw [mem_mcaFinset parR parR_lt]
  constructor
  · rintro ⟨hCA, _⟩
    have h0 := ca12 hCA
    subst h0
    decide
  · intro hm
    have hm0 : m = 0 := Finset.mem_singleton.mp hm
    subst hm0
    refine ⟨⟨⟨1, by simp, re01⟩, re02⟩, ?_⟩
    intro x hx _
    exact ca12 hx

/-! ## §4 The gate pin: no registered LCA exists (¬-companion) -/

/-- No version is an `IsLCA` of the head pair `(5,6)`: the gated `Step3.merge` cannot
fire — the shape genuinely requires `Step3V.mergeVirtual`. -/
theorem rga_no_registered_lca : ¬ ∃ vT, IsLCA parR 5 6 vT := by
  rintro ⟨vT, hlca⟩
  have h1 : (1 : Version) = vT :=
    isMCA_eq_of_isLCA hlca (by
      have := (mem_mcaFinset parR parR_lt).mp
        (show (1 : Version) ∈ mcaFinset parR {5} 6 by rw [mca56R]; decide)
      rwa [Finset.coe_singleton] at this)
  have h2 : (2 : Version) = vT :=
    isMCA_eq_of_isLCA hlca (by
      have := (mem_mcaFinset parR parR_lt).mp
        (show (2 : Version) ∈ mcaFinset parR {5} 6 by rw [mca56R]; decide)
      rwa [Finset.coe_singleton] at this)
  exact absurd (h1.trans h2.symm) (by decide)

/-! ## §5 The virtual resolution -/

/-- Sorting a two-element antichain literal (`Finset.sort_insert`; `decide` does not
reduce `Multiset.sort`). -/
private theorem sort_pair {a b : Version} (hab : a < b) :
    ({a, b} : Finset Version).sort (· ≤ ·) = [a, b] := by
  have h₁ : ∀ c ∈ ({b} : Finset Version), a ≤ c := by
    intro c hc
    rw [Finset.mem_singleton] at hc
    subst hc
    exact Nat.le_of_lt hab
  have h₂ : a ∉ ({b} : Finset Version) := by
    rw [Finset.mem_singleton]
    exact Nat.ne_of_lt hab
  calc ({a, b} : Finset Version).sort (· ≤ ·)
      = a :: ({b} : Finset Version).sort (· ≤ ·) :=
        Finset.sort_insert (· ≤ ·) h₁ h₂
    _ = [a, b] := by rw [Finset.sort_singleton]

/-- The sub-pair resolution bottoms out at the registered LCA `0`: `σ₀`. -/
theorem vlca12R : vlcaAux verR parR parR_lt {1} 2 = init_st (α := ℕ) := by
  have hsort : (mcaFinset parR {1} 2).sort (· ≤ ·) = [0] := by
    rw [mca12R]
    exact Finset.sort_singleton (· ≤ ·) 0
  rw [vlcaAux_of_sort_cons verR parR parR_lt hsort, vfoldAux_nil]
  rfl

/-- The virtual LCA of the criss-cross pair: the antichain `{1,2}` folds in ascending
rank through the inner LCA `0` — the merge of the two single-insert branches over
`σ₀`. -/
theorem vlca56R : vlcaAux verR parR parR_lt {5} 6
    = _root_.merge (init_st (α := ℕ)) sA sB := by
  have hsort : (mcaFinset parR {5} 6).sort (· ≤ ·) = [1, 2] := by
    rw [mca56R]
    exact sort_pair (by decide)
  rw [vlcaAux_of_sort_cons verR parR parR_lt hsort, vfoldAux_cons,
    vfoldAux_nil, vlca12R]
  rfl

/-- The payload the widened rule registers at the fresh version. -/
noncomputable def vMerged : (RGACondSig ℕ).State :=
  (RGACondSig ℕ).mergeL (vlcaAux verR parR parR_lt {5} 6) (stateD verR 5) (stateD verR 6)

/-! ## §6 T1 (PASS): the virtual merge's reads, hand-derived

`I = (dl∩da∩db) ∪ (da∖dl) ∪ (db∖dl) = {20} ∪ ∅ ∪ {30}`: the delete of 10 wins, the
concurrent child 30 survives, and its dead anchor 10 climbs the virtual LCA's chain
`10 → 0`: rehomed to the root. -/

/-- The deleted id 10 stays deleted (the delete wins across the criss-cross). -/
theorem t1_del_wins : contains vMerged 10 = false := by
  rw [vMerged, vlca56R]
  decide

/-- The concurrent child survives and is REHOMED: `30 ↦ (300, 0)` (anchor 10 dead,
climbed to the root through the virtual LCA's parent chain). -/
theorem t1_child_rehomed :
    contains vMerged 30 = true ∧ sel vMerged 30 = (300, 0) := by
  rw [vMerged, vlca56R]
  exact ⟨by decide, by decide⟩

/-- The untouched survivor is untouched: `20 ↦ (200, 0)`. -/
theorem t1_survivor : contains vMerged 20 = true ∧ sel vMerged 20 = (200, 0) := by
  rw [vMerged, vlca56R]
  exact ⟨by decide, by decide⟩

/-! ## §7 T1F (FAIL): the fixed single-MCA pick resurrects the deleted id -/

/-- The arbitrary-pick merge with MCA `2` (the branch that never saw `i10`) in the
LCA slot. -/
noncomputable def pickMerged : (RGACondSig ℕ).State :=
  (RGACondSig ℕ).mergeL (stateD verR 2) (stateD verR 5) (stateD verR 6)

/-- **T1F**: pick-`2` reads the deleted id 10 as PRESENT — `10 ∉ dl`, so side 6's
copy looks like a fresh add and RESURRECTS, `10 ↦ (100, 0)`; and the child 30 keeps
its (now-live) anchor 10.  The virtual resolution does neither (`t1_del_wins`,
`t1_child_rehomed`): the picks disagree on the read of id 10. -/
theorem t1f_pick_resurrects :
    contains pickMerged 10 = true ∧ sel pickMerged 30 = (300, 10) := by
  exact ⟨by decide, by decide⟩

/-- The ≠-companion: the pick and the virtual resolution disagree at id 10 (and at
30's anchor), so the LCA slot is decisive on this store. -/
theorem t1f_pick_ne_virtual :
    contains pickMerged 10 ≠ contains vMerged 10 ∧
    sel pickMerged 30 ≠ sel vMerged 30 := by
  rw [vMerged, vlca56R]
  exact ⟨by decide, by decide⟩

/-! ## §8 Axiom audit (all `decide`; no `ofReduceBool`) -/

#print axioms mca56R
#print axioms rga_no_registered_lca
#print axioms vlca56R
#print axioms t1_del_wins
#print axioms t1_child_rehomed
#print axioms t1_survivor
#print axioms t1f_pick_resurrects
#print axioms t1f_pick_ne_virtual

end Sal.ConditionedMRDTs.RGAVirtualLCASpot
