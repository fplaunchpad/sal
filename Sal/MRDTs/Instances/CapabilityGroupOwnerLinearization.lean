import Sal.MRDTs.Instances.CapabilityGroupOwnerOrder
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Lattice.Fold

namespace Sal.MRDTs.Instances.CapabilityGroup.OwnerLinearization
open OwnerOrder

abbrev Admin (owner : Actor) (e : Event) : Prop :=
  e.actor = owner ∧ isAdministrative e.action = true

def leftAdmins (owner : Actor) (s : State) (e : Event) : State :=
  s.filter (AdminBeforeCut owner e)

def cutRank (owner : Actor) (s : State) (e : Event) : Nat :=
  (leftAdmins owner s e).sup Event.id

/-- An administrative event has an even key; an assignment sits immediately
following the last administration that is not its causal successor. -/
def major (owner : Actor) (s : State) (e : Event) : Nat :=
  if isAdministrative e.action then 2 * e.id else 2 * cutRank owner s e + 1

abbrev RankLE (owner : Actor) (s : State) (a b : Event) : Prop :=
  major owner s a < major owner s b ∨
    major owner s a = major owner s b ∧ a.id ≤ b.id
abbrev RankLT (owner : Actor) (s : State) (a b : Event) : Prop :=
  major owner s a < major owner s b ∨
    major owner s a = major owner s b ∧ a.id < b.id

instance (owner : Actor) (s : State) : DecidableRel (RankLE owner s) := inferInstance
instance (owner : Actor) (s : State) : Std.Total (RankLE owner s) where
  total a b := by
    rcases lt_trichotomy (major owner s a) (major owner s b) with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases Nat.le_total a.id b.id with hi | hi
      · exact Or.inl (Or.inr ⟨h, hi⟩)
      · exact Or.inr (Or.inr ⟨h.symm, hi⟩)
    · exact Or.inr (Or.inl h)
instance (owner : Actor) (s : State) : IsTrans Event (RankLE owner s) where
  trans a b c hab hbc := by
    rcases hab with hab | ⟨hab, hid⟩ <;> rcases hbc with hbc | ⟨hbc, hid'⟩
    · exact Or.inl (Nat.lt_trans hab hbc)
    · exact Or.inl (hbc ▸ hab)
    · exact Or.inl (hab ▸ hbc)
    · exact Or.inr ⟨hab.trans hbc, Nat.le_trans hid hid'⟩
instance (owner : Actor) (s : State) : Std.Refl (RankLE owner s) where
  refl _a := Or.inr ⟨rfl, Nat.le_refl _⟩

theorem rankLT_not_reverse {owner : Actor} {s : State} {a b : Event}
    (h : RankLT owner s a b) : ¬ RankLE owner s b a := by
  intro hrev
  rcases h with h | ⟨h, hi⟩ <;> rcases hrev with hrev | ⟨hrev, hri⟩
  · exact Nat.lt_asymm h hrev
  · exact Nat.ne_of_lt h hrev.symm
  · exact Nat.ne_of_lt hrev h.symm
  · exact Nat.not_le_of_gt hi hri

noncomputable def canonical (owner : Actor) (s : State) : List Event :=
  s.toList.insertionSort (RankLE owner s)

theorem canonical_perm (owner : Actor) (s : State) : (canonical owner s).Perm s.toList :=
  List.perm_insertionSort _ _
theorem canonical_nodup (owner : Actor) (s : State) : (canonical owner s).Nodup :=
  (canonical_perm owner s).nodup_iff.mpr s.nodup_toList
theorem canonical_sorted (owner : Actor) (s : State) :
    (canonical owner s).Pairwise (RankLE owner s) := List.pairwise_insertionSort _ _

@[simp] theorem mem_canonical (owner : Actor) (s : State) (e : Event) :
    e ∈ canonical owner s ↔ e ∈ s := by
  rw [(canonical_perm owner s).mem_iff, Finset.mem_toList]

theorem admin_owner {owner : Actor} {s : State} (ha : LocallyAdmitted owner s)
    {e : Event} (he : e ∈ s) (had : isAdministrative e.action = true) : e.actor = owner := by
  have h := ha e he
  cases heq : e.action with
  | grant user => simpa only [admitted, authorized, heq] using h
  | revoke gid =>
    simp only [admitted, authorized, heq] at h
    exact h.1
  | assign gid n => simp [heq, isAdministrative] at had

theorem cutRank_le_of_before {owner : Actor} {s : State} (hs : WellFormed s)
    {a b : Event} (ha : a ∈ s) (hb : b ∈ s) (hab : before a b) :
    cutRank owner s a ≤ cutRank owner s b := by
  apply Finset.sup_mono
  intro p hp
  obtain ⟨hps, hpo, hpad, hnot⟩ := Finset.mem_filter.mp hp
  apply Finset.mem_filter.mpr
  refine ⟨hps, hpo, hpad, ?_⟩
  intro hbp
  exact hnot (before_trans hs ha hb hps hab hbp)

theorem cutRank_lt_successor_admin {owner : Actor} {s : State}
    (hs : WellFormed s) (ho : OwnerOrdered owner s) {e b : Event}
    (he : e ∈ s) (hb : b ∈ s) (hbo : b.actor = owner)
    (hbad : isAdministrative b.action = true) (heb : before e b) :
    cutRank owner s e < b.id := by
  have hpositive : 0 < b.id := Nat.zero_lt_of_lt (hs.ranked b hb e.id heb)
  apply (Finset.sup_lt_iff hpositive).mpr
  intro a ha
  obtain ⟨has, hleft⟩ := Finset.mem_filter.mp ha
  exact hs.ranked b hb a.id (cut_is_initial_segment hs ho he has hb hleft hbo hbad heb)

theorem admin_cut_rankLT {owner : Actor} {s : State} {e a : Event}
    (had : isAdministrative a.action = true) (hea : isAdministrative e.action = false)
    (ha : a ∈ s) (hao : a.actor = owner) (hnot : ¬ before e a) :
    RankLT owner s a e := by
  have hm : a ∈ leftAdmins owner s e := Finset.mem_filter.mpr ⟨ha, hao, had, hnot⟩
  have hle : a.id ≤ cutRank owner s e := Finset.le_sup hm
  left
  have hma : major owner s a = 2 * a.id := by simp [major, had]
  have hme : major owner s e = 2 * cutRank owner s e + 1 := by simp [major, hea]
  rw [hma, hme]
  exact Nat.lt_succ_of_le (Nat.mul_le_mul_left 2 hle)

theorem causal_rankLT {owner : Actor} {s : State} (hs : WellFormed s)
    (hl : LocallyAdmitted owner s) (ho : OwnerOrdered owner s)
    {a b : Event} (ha : a ∈ s) (hb : b ∈ s) (hab : before a b) :
    RankLT owner s a b := by
  have hid := hs.ranked b hb a.id hab
  cases hada : isAdministrative a.action <;> cases hadb : isAdministrative b.action
  · have hle := cutRank_le_of_before (owner := owner) hs ha hb hab
    have hmajor : major owner s a ≤ major owner s b := by
      simpa only [major, hada, hadb, Bool.false_eq_true, ↓reduceIte] using
        Nat.add_le_add_right (Nat.mul_le_mul_left 2 hle) 1
    rcases lt_or_eq_of_le hmajor with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hid⟩
  · have hlt := cutRank_lt_successor_admin hs ho ha hb (admin_owner hl hb hadb) hadb hab
    left
    simp only [major, hada, hadb, Bool.false_eq_true, ↓reduceIte]
    omega
  · exact admin_cut_rankLT hada hadb ha (admin_owner hl ha hada) (before_asymm hs ha hb hab)
  · left
    have hma : major owner s a = 2 * a.id := by simp [major, hada]
    have hmb : major owner s b = 2 * b.id := by simp [major, hadb]
    rw [hma, hmb]
    exact Nat.mul_lt_mul_of_pos_left hid (by decide)

/-- A sorted list puts any strictly smaller rank at a strictly smaller index. -/
theorem sorted_index_lt {owner : Actor} {s : State} {π : List Event}
    (hπ : π.Pairwise (RankLE owner s)) {a b : Event}
    (ha : a ∈ π) (hb : b ∈ π) (hab : RankLT owner s a b) :
    π.idxOf a < π.idxOf b := by
  by_contra h
  have haidx := List.idxOf_lt_length_iff.mpr ha
  have hbidx := List.idxOf_lt_length_iff.mpr hb
  have hrev := hπ.rel_get_of_le (a := ⟨π.idxOf b, hbidx⟩) (b := ⟨π.idxOf a, haidx⟩)
    (Nat.le_of_not_gt h)
  have hbget : π.get ⟨π.idxOf b, hbidx⟩ = b := List.getElem_idxOf hbidx
  have haget : π.get ⟨π.idxOf a, haidx⟩ = a := List.getElem_idxOf haidx
  rw [hbget, haget] at hrev
  exact rankLT_not_reverse hab hrev

abbrev Respects (π : List Event) (r : Event → Event → Prop) : Prop :=
  ∀ a ∈ π, ∀ b ∈ π, r a b → π.idxOf a < π.idxOf b

theorem canonical_respects {owner : Actor} {s : State} (hs : WellFormed s)
    (hl : LocallyAdmitted owner s) (ho : OwnerOrdered owner s) :
    Respects (canonical owner s) before := by
  intro a ha b hb hab
  exact sorted_index_lt (canonical_sorted owner s) ha hb
    (causal_rankLT hs hl ho ((mem_canonical owner s a).mp ha)
      ((mem_canonical owner s b).mp hb) hab)

/-- For an assignment, every owner administrative event occurs before it
exactly when that event is not its causal successor. -/
abbrev AdminPrefix (owner : Actor) (s : State) (π : List Event) : Prop :=
  ∀ preEvents e suffix, π = preEvents ++ e :: suffix → isAssignment e →
    ∀ a ∈ s, Admin owner a → (a ∈ preEvents ↔ ¬ before e a)

theorem canonical_adminPrefix {owner : Actor} {s : State}
    (hs : WellFormed s) (hl : LocallyAdmitted owner s) (ho : OwnerOrdered owner s) :
    AdminPrefix owner s (canonical owner s) := by
  intro preEvents e suffix hsplit heassign a ha hadmin
  have hemem : e ∈ canonical owner s := by rw [hsplit]; simp
  have hes := (mem_canonical owner s e).mp hemem
  have hadmem := (mem_canonical owner s a).mpr ha
  have hea : isAdministrative e.action = false := by
    cases heq : e.action <;> simp_all [isAssignment, isAdministrative]
  have hindices : a ∈ preEvents ↔ (canonical owner s).idxOf a < (canonical owner s).idxOf e := by
    have hnodup := canonical_nodup owner s
    rw [hsplit] at hnodup ⊢
    have hepre : e ∉ preEvents := by
      intro hmem
      exact (List.nodup_append.mp hnodup).2.2 e hmem e (by simp) rfl
    rw [List.idxOf_append_of_notMem hepre, List.idxOf_cons_self]
    simp only [Nat.add_zero]
    exact (List.IsPrefix.mem_iff_idxOf_lt_length (List.prefix_append _ _) a)
  rw [hindices]
  constructor
  · intro haidx heb
    have hrank := causal_rankLT hs hl ho hes ha heb
    have heidx := sorted_index_lt (canonical_sorted owner s) hemem hadmem hrank
    omega
  · intro hnot
    exact sorted_index_lt (canonical_sorted owner s) hadmem hemem
      (admin_cut_rankLT hadmin.2 hea ha hadmin.1 hnot)

end Sal.MRDTs.Instances.CapabilityGroup.OwnerLinearization
