import Sal.ConditionedMRDTs.Metatheory.Adequacy
import Sal.ConditionedMRDTs.Metatheory.GC_Safety
import Sal.ConditionedMRDTs.Metatheory.HonestReach

/-!
# SPOT: virtual LCAs on a concrete criss-cross store

Concrete-execution pins for the recursive antichain merge. The
expected values below are derived by hand in the comments, never `#eval`'d from the
implementation under test.

**Datatype.** `ORPair`, a two-element observed-remove set: `State = Bool × Bool`
(presence of `x` = first coordinate, `y` = second), `update` writes a coordinate,
and the ternary merge is the classic LCA-*sensitive* observed-remove 3-way per
coordinate: present iff present on both sides, or present on one side and **absent at
the LCA** (a fresh add). The LCA slot is decisive — exactly what makes a wrong LCA
pick observable (T1F). Not RA-lin-certified; the SPOT pins the *rule's* behavior.

**The store** (raw `ver`/`parents`, GCSpot style; ranks are ids):

    0 (init, ∅)                        root
    1 = A adds x      state (t,f)  E {ex}    parents [0]   — head u
    2 = B adds y      state (f,t)  E {ey}    parents [0]   — head v
    3 = merge(1,2)    state (t,t)  E {ex,ey} parents [1,2] — rival m1
    4 = merge(1,2)    state (t,t)  E {ex,ey} parents [1,2] — rival m2
    5 = del x on m1   state (f,t)  E {ex,ey,dx} parents [3] — head a
    6 = del y on m2   state (t,f)  E {ex,ey,dy} parents [4] — head c
    7 = merge(3,4)    state (t,t)  E {ex,ey} parents [3,4] — rival n1
    8 = merge(3,4)    state (t,t)  E {ex,ey} parents [3,4] — rival n2

**T1/T1F (pair 5,6).** `CA(5,6) = {1,2,0}`, `MCA = {1,2}`: no `IsLCA` version exists
(the gated Merge is blocked; pinned). The recursion resolves `(1,2)` through their
LCA `0`, giving virtual state `(t,t)` — both adds visible, exactly the meet's fold.
Head merge: `mergeL (t,t) (f,t) (t,f) = (f,f)` — **both deletions survive**. FAIL
companions: picking the single MCA `1` gives `mergeL (t,f) (f,t) (t,f) = (f,t)` —
the deleted `y` **resurrects** (`y ∉ E(1)`, so `y` on side 6 reads as a fresh add);
picking `2` dually resurrects `x`.

**T3 (pair 7,8, nested).** `MCA(7,8) = {3,4}` — and resolving the sub-pair `(3,4)`
again finds the proper antichain `{1,2}`: recursion depth 2, pinned structurally
(`mca34`) plus the no-registered-LCA pin for the sub-pair (a depth-limited
implementation would gate again: rivalry propagates upward).

**Covering instance.** `E(1) ∪ E(2) = {ex,ey} = E(5) ∩ E(6)`: the antichain's
event-set union is exactly the pair's meet, pinned by hand on this store.
-/

namespace Sal.ConditionedMRDTs.VirtualLCASpot

open Sal.ConditionedMRDTs
open Sal.Emulation

/-! ## §1 The toy datatype -/

/-- Two-element observed-remove set with an LCA-sensitive 3-way merge. -/
def ORPair : ConditionedMRDTSig where
  State := Bool × Bool
  dec_state := inferInstance
  init := (false, false)
  AppOp := Bool × Bool
  dec_op := inferInstance
  Query := Bool
  Value := Bool
  update := fun s o => if o.2.2.1 then (s.1, o.2.2.2) else (o.2.2.2, s.2)
  merge := fun a b => (a.1 || b.1, a.2 || b.2)
  query := fun s q => if q then s.2 else s.1
  rc := fun _ _ => RcRes.Either
  mergeL := fun l a b =>
    ((a.1 && b.1) || (a.1 && !l.1) || (b.1 && !l.1),
     (a.2 && b.2) || (a.2 && !l.2) || (b.2 && !l.2))
  merge_init_slice := by
    intro a b
    rcases a with ⟨ax, ay⟩
    rcases b with ⟨bx, bz⟩
    cases ax <;> cases ay <;> cases bx <;> cases bz <;> rfl
  Inv := fun _ => True
  applicable := fun _ _ => True

/-- Op alias: `(timestamp, replica, (coordinate, value))`. -/
abbrev O := Op ORPair.AppOp

def ex : O := (1, 0, (false, true))
def ey : O := (2, 1, (true, true))
def dx : O := (3, 0, (false, false))
def dy : O := (4, 2, (true, false))

/-! ## §2 The store -/

/-- The ranked store: version ↦ `(state, event set)`. -/
noncomputable def verEx : Version → Option (ORPair.State × Set O) := fun v =>
  if v = 0 then some ((false, false), ∅)
  else if v = 1 then some ((true, false), {ex})
  else if v = 2 then some ((false, true), {ey})
  else if v = 3 then some ((true, true), {ex, ey})
  else if v = 4 then some ((true, true), {ex, ey})
  else if v = 5 then some ((false, true), {ex, ey, dx})
  else if v = 6 then some ((true, false), {ex, ey, dy})
  else if v = 7 then some ((true, true), {ex, ey})
  else if v = 8 then some ((true, true), {ex, ey})
  else none

/-- The version DAG (criss-cross at `(5,6)`, nested criss-cross at `(7,8)`). -/
def parEx : Version → List Version := fun v =>
  if v = 1 then [0]
  else if v = 2 then [0]
  else if v = 3 then [1, 2]
  else if v = 4 then [1, 2]
  else if v = 5 then [3]
  else if v = 6 then [4]
  else if v = 7 then [3, 4]
  else if v = 8 then [3, 4]
  else []

theorem parEx_lt : ∀ v p, p ∈ parEx v → p < v := by
  intro v p hp
  simp only [parEx] at hp
  split_ifs at hp <;> simp_all <;> rcases hp with rfl | rfl <;> decide

/-! ## §3 Reachability: chains and inversions -/

theorem re01 : Reaches parEx 0 1 := Relation.ReflTransGen.single (by decide)
theorem re02 : Reaches parEx 0 2 := Relation.ReflTransGen.single (by decide)
theorem re13 : Reaches parEx 1 3 := Relation.ReflTransGen.single (by decide)
theorem re23 : Reaches parEx 2 3 := Relation.ReflTransGen.single (by decide)
theorem re14 : Reaches parEx 1 4 := Relation.ReflTransGen.single (by decide)
theorem re24 : Reaches parEx 2 4 := Relation.ReflTransGen.single (by decide)
theorem re35 : Reaches parEx 3 5 := Relation.ReflTransGen.single (by decide)
theorem re46 : Reaches parEx 4 6 := Relation.ReflTransGen.single (by decide)
theorem re37 : Reaches parEx 3 7 := Relation.ReflTransGen.single (by decide)
theorem re47 : Reaches parEx 4 7 := Relation.ReflTransGen.single (by decide)
theorem re38 : Reaches parEx 3 8 := Relation.ReflTransGen.single (by decide)
theorem re48 : Reaches parEx 4 8 := Relation.ReflTransGen.single (by decide)

theorem re15 : Reaches parEx 1 5 := re13.trans re35
theorem re25 : Reaches parEx 2 5 := re23.trans re35
theorem re16 : Reaches parEx 1 6 := re14.trans re46
theorem re26 : Reaches parEx 2 6 := re24.trans re46
theorem re03 : Reaches parEx 0 3 := re01.trans re13

theorem reach0 {w : Version} (h : Reaches parEx w 0) : w = 0 := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, _, hstep⟩
  · exact h.symm
  · exact absurd hstep (by simp [parEx])

theorem reach1 {w : Version} (h : Reaches parEx w 1) : w = 1 ∨ w = 0 := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, hpre, hstep⟩
  · exact Or.inl h.symm
  · have hc : c = 0 := by simpa [parEx] using hstep
    subst hc
    exact Or.inr (reach0 hpre)

theorem reach2 {w : Version} (h : Reaches parEx w 2) : w = 2 ∨ w = 0 := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, hpre, hstep⟩
  · exact Or.inl h.symm
  · have hc : c = 0 := by simpa [parEx] using hstep
    subst hc
    exact Or.inr (reach0 hpre)

theorem reach3 {w : Version} (h : Reaches parEx w 3) :
    w = 3 ∨ w = 1 ∨ w = 2 ∨ w = 0 := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, hpre, hstep⟩
  · exact Or.inl h.symm
  · have hc : c = 1 ∨ c = 2 := by simpa [parEx] using hstep
    rcases hc with rfl | rfl
    · rcases reach1 hpre with rfl | rfl <;> simp
    · rcases reach2 hpre with rfl | rfl <;> simp

theorem reach4 {w : Version} (h : Reaches parEx w 4) :
    w = 4 ∨ w = 1 ∨ w = 2 ∨ w = 0 := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, hpre, hstep⟩
  · exact Or.inl h.symm
  · have hc : c = 1 ∨ c = 2 := by simpa [parEx] using hstep
    rcases hc with rfl | rfl
    · rcases reach1 hpre with rfl | rfl <;> simp
    · rcases reach2 hpre with rfl | rfl <;> simp

theorem reach5 {w : Version} (h : Reaches parEx w 5) :
    w = 5 ∨ w = 3 ∨ w = 1 ∨ w = 2 ∨ w = 0 := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, hpre, hstep⟩
  · exact Or.inl h.symm
  · have hc : c = 3 := by simpa [parEx] using hstep
    subst hc
    rcases reach3 hpre with rfl | rfl | rfl | rfl <;> simp

theorem reach6 {w : Version} (h : Reaches parEx w 6) :
    w = 6 ∨ w = 4 ∨ w = 1 ∨ w = 2 ∨ w = 0 := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, hpre, hstep⟩
  · exact Or.inl h.symm
  · have hc : c = 4 := by simpa [parEx] using hstep
    subst hc
    rcases reach4 hpre with rfl | rfl | rfl | rfl <;> simp

theorem reach7 {w : Version} (h : Reaches parEx w 7) :
    w = 7 ∨ w = 3 ∨ w = 4 ∨ w = 1 ∨ w = 2 ∨ w = 0 := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, hpre, hstep⟩
  · exact Or.inl h.symm
  · have hc : c = 3 ∨ c = 4 := by simpa [parEx] using hstep
    rcases hc with rfl | rfl
    · rcases reach3 hpre with rfl | rfl | rfl | rfl <;> simp
    · rcases reach4 hpre with rfl | rfl | rfl | rfl <;> simp

theorem reach8 {w : Version} (h : Reaches parEx w 8) :
    w = 8 ∨ w = 3 ∨ w = 4 ∨ w = 1 ∨ w = 2 ∨ w = 0 := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, hpre, hstep⟩
  · exact Or.inl h.symm
  · have hc : c = 3 ∨ c = 4 := by simpa [parEx] using hstep
    rcases hc with rfl | rfl
    · rcases reach3 hpre with rfl | rfl | rfl | rfl <;> simp
    · rcases reach4 hpre with rfl | rfl | rfl | rfl <;> simp

/-! ## §4 The MCA antichains, hand-derived -/

theorem ca56 {x : Version}
    (hx : x ∈ CommonAnc parEx (↑({5} : Finset Version)) 6) :
    x = 1 ∨ x = 2 ∨ x = 0 := by
  obtain ⟨⟨u, hu, hxu⟩, hx6⟩ := hx
  have hu5 : u = 5 := by simpa using hu
  subst hu5
  rcases reach5 hxu with rfl | rfl | rfl | rfl | rfl <;>
    rcases reach6 hx6 with h | h | h | h | h <;> simp_all

/-- `MCA(5,6) = {1,2}` — the criss-cross's proper antichain. -/
theorem mca56 : mcaFinset parEx {5} 6 = {1, 2} := by
  ext m
  rw [mem_mcaFinset parEx parEx_lt]
  constructor
  · rintro ⟨hCA, hmax⟩
    rcases ca56 hCA with rfl | rfl | rfl
    · decide
    · decide
    · exfalso
      have h1CA : (1 : Version) ∈ CommonAnc parEx (↑({5} : Finset Version)) 6 :=
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
    (hx : x ∈ CommonAnc parEx (↑({1} : Finset Version)) 2) : x = 0 := by
  obtain ⟨⟨u, hu, hxu⟩, hx2⟩ := hx
  have hu1 : u = 1 := by simpa using hu
  subst hu1
  rcases reach1 hxu with rfl | rfl <;> rcases reach2 hx2 with h | h <;> simp_all

/-- The nested sub-pair `(1,2)` is NOT criss-crossed: its MCA set is the singleton
root — the recursion bottoms out at the existing LCA rule. -/
theorem mca12 : mcaFinset parEx {1} 2 = {0} := by
  ext m
  rw [mem_mcaFinset parEx parEx_lt]
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

theorem ca78 {x : Version}
    (hx : x ∈ CommonAnc parEx (↑({7} : Finset Version)) 8) :
    x = 3 ∨ x = 4 ∨ x = 1 ∨ x = 2 ∨ x = 0 := by
  obtain ⟨⟨u, hu, hxu⟩, hx8⟩ := hx
  have hu7 : u = 7 := by simpa using hu
  subst hu7
  rcases reach7 hxu with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases reach8 hx8 with h | h | h | h | h | h <;> simp_all

/-- `MCA(7,8) = {3,4}` — the TOP antichain of the nested case. -/
theorem mca78 : mcaFinset parEx {7} 8 = {3, 4} := by
  ext m
  rw [mem_mcaFinset parEx parEx_lt]
  constructor
  · rintro ⟨hCA, hmax⟩
    have h3CA : (3 : Version) ∈ CommonAnc parEx (↑({7} : Finset Version)) 8 :=
      ⟨⟨7, by simp, re37⟩, re38⟩
    rcases ca78 hCA with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · exact absurd (hmax 3 h3CA re13) (by decide)
    · exact absurd (hmax 3 h3CA re23) (by decide)
    · exact absurd (hmax 3 h3CA re03) (by decide)
  · intro hm
    have hm' : m = 3 ∨ m = 4 := by
      rcases Finset.mem_insert.mp hm with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_singleton.mp h)
    rcases hm' with rfl | rfl
    · refine ⟨⟨⟨7, by simp, re37⟩, re38⟩, ?_⟩
      intro x hx h3x
      rcases ca78 hx with rfl | rfl | rfl | rfl | rfl
      · rfl
      · rcases reach4 h3x with h | h | h | h <;> exact absurd h (by decide)
      · rcases reach1 h3x with h | h <;> exact absurd h (by decide)
      · rcases reach2 h3x with h | h <;> exact absurd h (by decide)
      · exact absurd (reach0 h3x) (by decide)
    · refine ⟨⟨⟨7, by simp, re47⟩, re48⟩, ?_⟩
      intro x hx h4x
      rcases ca78 hx with rfl | rfl | rfl | rfl | rfl
      · rcases reach3 h4x with h | h | h | h <;> exact absurd h (by decide)
      · rfl
      · rcases reach1 h4x with h | h <;> exact absurd h (by decide)
      · rcases reach2 h4x with h | h <;> exact absurd h (by decide)
      · exact absurd (reach0 h4x) (by decide)

theorem ca34 {x : Version}
    (hx : x ∈ CommonAnc parEx (↑({3} : Finset Version)) 4) :
    x = 1 ∨ x = 2 ∨ x = 0 := by
  obtain ⟨⟨u, hu, hxu⟩, hx4⟩ := hx
  have hu3 : u = 3 := by simpa using hu
  subst hu3
  rcases reach3 hxu with rfl | rfl | rfl | rfl <;>
    rcases reach4 hx4 with h | h | h | h <;> simp_all

/-- **The nested antichain**: `MCA(3,4) = {1,2}` — resolving the top pair's antichain
members again finds a proper antichain: recursion depth 2, structurally pinned. -/
theorem mca34 : mcaFinset parEx {3} 4 = {1, 2} := by
  ext m
  rw [mem_mcaFinset parEx parEx_lt]
  constructor
  · rintro ⟨hCA, hmax⟩
    rcases ca34 hCA with rfl | rfl | rfl
    · decide
    · decide
    · exfalso
      have h1CA : (1 : Version) ∈ CommonAnc parEx (↑({3} : Finset Version)) 4 :=
        ⟨⟨3, by simp, re13⟩, re14⟩
      exact absurd (hmax 1 h1CA re01) (by decide)
  · intro hm
    have hm' : m = 1 ∨ m = 2 := by
      rcases Finset.mem_insert.mp hm with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_singleton.mp h)
    rcases hm' with rfl | rfl
    · refine ⟨⟨⟨3, by simp, re13⟩, re14⟩, ?_⟩
      intro x hx h1x
      rcases ca34 hx with rfl | rfl | rfl
      · rfl
      · rcases reach2 h1x with h | h <;> exact absurd h (by decide)
      · exact absurd (reach0 h1x) (by decide)
    · refine ⟨⟨⟨3, by simp, re23⟩, re24⟩, ?_⟩
      intro x hx h2x
      rcases ca34 hx with rfl | rfl | rfl
      · rcases reach1 h2x with h | h <;> exact absurd h (by decide)
      · rfl
      · exact absurd (reach0 h2x) (by decide)

/-! ## §5 The gated rule is blocked (the criss-cross is genuine) -/

/-- No version is an `IsLCA` of the head pair `(5,6)`: `Step3.merge` cannot fire —
the shape genuinely requires the virtual rule. (An LCA would be THE unique MCA, but
`1 ≠ 2` are both maximal.) -/
theorem t1_no_registered_lca : ¬ ∃ vT, IsLCA parEx 5 6 vT := by
  rintro ⟨vT, hlca⟩
  have h1 : (1 : Version) = vT :=
    isMCA_eq_of_isLCA hlca (by
      have := (mem_mcaFinset parEx parEx_lt).mp
        (show (1 : Version) ∈ mcaFinset parEx {5} 6 by rw [mca56]; decide)
      rwa [Finset.coe_singleton] at this)
  have h2 : (2 : Version) = vT :=
    isMCA_eq_of_isLCA hlca (by
      have := (mem_mcaFinset parEx parEx_lt).mp
        (show (2 : Version) ∈ mcaFinset parEx {5} 6 by rw [mca56]; decide)
      rwa [Finset.coe_singleton] at this)
  exact absurd (h1.trans h2.symm) (by decide)

/-- The nested sub-pair `(3,4)` is ALSO ungated-unresolvable: rivalry propagates
upward, and a depth-limited implementation would gate again. -/
theorem t3_no_registered_lca_nested : ¬ ∃ vT, IsLCA parEx 3 4 vT := by
  rintro ⟨vT, hlca⟩
  have h1 : (1 : Version) = vT :=
    isMCA_eq_of_isLCA hlca (by
      have := (mem_mcaFinset parEx parEx_lt).mp
        (show (1 : Version) ∈ mcaFinset parEx {3} 4 by rw [mca34]; decide)
      rwa [Finset.coe_singleton] at this)
  have h2 : (2 : Version) = vT :=
    isMCA_eq_of_isLCA hlca (by
      have := (mem_mcaFinset parEx parEx_lt).mp
        (show (2 : Version) ∈ mcaFinset parEx {3} 4 by rw [mca34]; decide)
      rwa [Finset.coe_singleton] at this)
  exact absurd (h1.trans h2.symm) (by decide)

/-- Sorting a two-element antichain literal (the `decide` route does not reduce
`Multiset.sort`; this pins it by `Finset.sort_insert`). -/
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

/-! ## §6 T1 (PASS): the virtual resolution and its reads -/

/-- The inner sub-pair resolution bottoms out at the true LCA `0`: virtual state
`σ₀ = (f,f)`. -/
theorem vlca12 : vlcaAux verEx parEx parEx_lt {1} 2
    = ((false, false) : Bool × Bool) := by
  have hsort : (mcaFinset parEx {1} 2).sort (· ≤ ·) = [0] := by
    rw [mca12]
    exact Finset.sort_singleton (· ≤ ·) 0
  rw [vlcaAux_of_sort_cons verEx parEx parEx_lt hsort, vfoldAux_nil]
  decide

/-- The virtual LCA of the criss-cross pair: the antichain `{1,2}` folds in
ascending rank order through the inner LCA `0` — hand-derived
`mergeL (f,f) (t,f) (f,t) = (t,t)`: BOTH adds visible, exactly the meet's fold. -/
theorem vlca56 : vlcaAux verEx parEx parEx_lt {5} 6
    = ((true, true) : Bool × Bool) := by
  have hsort : (mcaFinset parEx {5} 6).sort (· ≤ ·) = [1, 2] := by
    rw [mca56]
    exact sort_pair (by decide)
  rw [vlcaAux_of_sort_cons verEx parEx parEx_lt hsort, vfoldAux_cons,
    vfoldAux_nil, vlca12]
  decide

/-- **T1 (PASS)**: the payload the widened rule registers at the fresh version —
`mergeL (virtual LCA) σ(5) σ(6)` — preserves BOTH concurrent deletions: hand-derived
`mergeL (t,t) (f,t) (t,f) = (f,f)`. -/
theorem t1_virtual_merge :
    ORPair.mergeL (vlcaAux verEx parEx parEx_lt {5} 6)
      (stateD verEx 5) (stateD verEx 6) = ((false, false) : Bool × Bool) := by
  rw [vlca56]; decide

/-- Both reads of the virtually merged head are `false` (`x` and `y` stay deleted). -/
theorem t1_virtual_reads :
    (ORPair.query (ORPair.mergeL (vlcaAux verEx parEx parEx_lt {5} 6)
        (stateD verEx 5) (stateD verEx 6)) false : Bool) = false ∧
    (ORPair.query (ORPair.mergeL (vlcaAux verEx parEx parEx_lt {5} 6)
        (stateD verEx 5) (stateD verEx 6)) true : Bool) = false :=
  ⟨by rw [t1_virtual_merge]; rfl, by rw [t1_virtual_merge]; rfl⟩

/-! ## §7 T1F (FAIL): every single-MCA pick resurrects a deleted element -/

/-- **T1F**: the arbitrary-pick merge with MCA `u = 1` in the LCA slot — hand-derived
`mergeL (t,f) (f,t) (t,f) = (f,t)`. -/
theorem t1f_pick_u :
    ORPair.mergeL (stateD verEx 1) (stateD verEx 5) (stateD verEx 6)
      = ((false, true) : Bool × Bool) := by decide

/-- Pick-`u` reads the deleted `y` as PRESENT (`y ∉ E(1)`, so side 6's `y` looks like
a fresh add); the virtual resolution reads it absent. -/
theorem t1f_pick_u_resurrects_y :
    (ORPair.query (ORPair.mergeL (stateD verEx 1) (stateD verEx 5)
        (stateD verEx 6)) true : Bool) = true ∧
    (ORPair.query (ORPair.mergeL (vlcaAux verEx parEx parEx_lt {5} 6)
        (stateD verEx 5) (stateD verEx 6)) true : Bool) = false :=
  ⟨by rfl, by rw [t1_virtual_merge]; rfl⟩

/-- The other pick, `v = 2`: hand-derived `mergeL (f,t) (f,t) (t,f) = (t,f)`. -/
theorem t1f_pick_v :
    ORPair.mergeL (stateD verEx 2) (stateD verEx 5) (stateD verEx 6)
      = ((true, false) : Bool × Bool) := by decide

/-- Pick-`v` resurrects the deleted `x`; the virtual resolution does not. -/
theorem t1f_pick_v_resurrects_x :
    (ORPair.query (ORPair.mergeL (stateD verEx 2) (stateD verEx 5)
        (stateD verEx 6)) false : Bool) = true ∧
    (ORPair.query (ORPair.mergeL (vlcaAux verEx parEx parEx_lt {5} 6)
        (stateD verEx 5) (stateD verEx 6)) false : Bool) = false :=
  ⟨by rfl, by rw [t1_virtual_merge]; rfl⟩

/-- Neither pick agrees with the virtual resolution (the `≠` companions). -/
theorem t1f_picks_ne :
    ORPair.mergeL (stateD verEx 1) (stateD verEx 5) (stateD verEx 6)
        ≠ ORPair.mergeL (vlcaAux verEx parEx parEx_lt {5} 6)
            (stateD verEx 5) (stateD verEx 6) ∧
    ORPair.mergeL (stateD verEx 2) (stateD verEx 5) (stateD verEx 6)
        ≠ ORPair.mergeL (vlcaAux verEx parEx parEx_lt {5} 6)
            (stateD verEx 5) (stateD verEx 6) := by
  rw [vlca56]
  exact ⟨by decide, by decide⟩

/-! ## §8 T3 (PASS): the nested, depth-2 resolution -/

/-- Depth-2 inner resolution: the sub-pair `(3,4)` of the top antichain is itself
criss-crossed on `{1,2}`; its virtual state is `mergeL (f,f) (t,f) (f,t) = (t,t)`. -/
theorem vlca34 : vlcaAux verEx parEx parEx_lt {3} 4
    = ((true, true) : Bool × Bool) := by
  have hsort : (mcaFinset parEx {3} 4).sort (· ≤ ·) = [1, 2] := by
    rw [mca34]
    exact sort_pair (by decide)
  rw [vlcaAux_of_sort_cons verEx parEx parEx_lt hsort, vfoldAux_cons,
    vfoldAux_nil, vlca12]
  decide

/-- **T3**: the top pair `(7,8)` resolves through the antichain `{3,4}`, whose own
resolution recursed through `{1,2}` (`vlca34`): recursion depth 2, hand-derived
final virtual state `(t,t)`. -/
theorem vlca78 : vlcaAux verEx parEx parEx_lt {7} 8
    = ((true, true) : Bool × Bool) := by
  have hsort : (mcaFinset parEx {7} 8).sort (· ≤ ·) = [3, 4] := by
    rw [mca78]
    exact sort_pair (by decide)
  rw [vlcaAux_of_sort_cons verEx parEx parEx_lt hsort, vfoldAux_cons,
    vfoldAux_nil, vlca34]
  decide

/-- The nested head merge converges to the hand value `(t,t)` (all adds visible,
nothing deleted on this slice). -/
theorem t3_merge :
    ORPair.mergeL (vlcaAux verEx parEx parEx_lt {7} 8)
      (stateD verEx 7) (stateD verEx 8) = ((true, true) : Bool × Bool) := by
  rw [vlca78]; decide

/-! ## §9 The covering instance -/

/-- `E(1) ∪ E(2) = E(5) ∩ E(6)`: the antichain's event-set union IS the pair's meet,
the covering lemma checked by hand on the concrete store (`{ex} ∪ {ey} = {ex,ey}`;
`dx`/`dy` are each on one side only). -/
theorem t1_covering :
    (({ex} : Set O) ∪ {ey}) = (({ex, ey, dx} : Set O) ∩ {ex, ey, dy}) := by
  ext e
  constructor
  · rintro (rfl | rfl)
    · exact ⟨Or.inl rfl, Or.inl rfl⟩
    · exact ⟨Or.inr (Or.inl rfl), Or.inr (Or.inl rfl)⟩
  · rintro ⟨h5, h6⟩
    rcases h5 with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · rcases h6 with h | h | h <;> exact absurd h (by decide)

/-! ## §10 Axiom audit (SPOTs may add `ofReduceBool`; none appears — all `decide`) -/

#print axioms mca56
#print axioms mca34
#print axioms mca78
#print axioms t1_no_registered_lca
#print axioms t1_virtual_merge
#print axioms t1_virtual_reads
#print axioms t1f_pick_u_resurrects_y
#print axioms t1f_pick_v_resurrects_x
#print axioms t1f_picks_ne
#print axioms vlca78
#print axioms t3_merge
#print axioms t3_no_registered_lca_nested
#print axioms t1_covering

/-! Axiom audit of the main results. -/

#print axioms Sal.ConditionedMRDTs.mca_events_cover
#print axioms Sal.ConditionedMRDTs.virtualLCAState_canonical
#print axioms Sal.ConditionedMRDTs.goodConfig3_mergeVirtual_at
#print axioms Sal.ConditionedMRDTs.ra_linearizable3V_of_join
#print axioms Sal.ConditionedMRDTs.ra_linearizable3_of_honest_reachV
#print axioms Sal.ConditionedMRDTs.mcaClosure_not_dropped
#print axioms Sal.ConditionedMRDTs.gc_safetyV

end Sal.ConditionedMRDTs.VirtualLCASpot
