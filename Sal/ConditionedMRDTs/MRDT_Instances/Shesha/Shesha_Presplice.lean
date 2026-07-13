import Sal.ConditionedMRDTs.MRDT_Instances.Shesha.Shesha_Coherence
import Sal.ConditionedMRDTs.MRDT_Instances.Shesha.Shesha_Out

/-! # Shesha — the pre-splice assembly (phase 2g)

Reduces the pre-splice obligation (`shesha_presplice`,
`Shesha_Cond.lean`) from the **forest** level to the **row** level: given
a row store `preRows` for the union's inserts that is graded (anchors
precede children in Lamport order), branch-order-extending, and whose
marker expansion matches the merge's output rows (`hK6` — the remaining
merge-correctness core), the pre-splice forest is
`buildF preRows … 0` and every clause of the obligation is discharged
by the builder kit (`Shesha_Out.lean`) plus the witness normal forms:

* (a) WF — `build_WF_raw` (unique addresses from timestamp uniqueness);
* (b) rows = the union's inserts — `build_row_raw` + coverage along the
  anchor chain (`build_cover_raw`, graded by the Lamport id itself);
* (c) anti-`vis` row order — derived from (c′) and the honesty/
  non-commutation kernel: a `vis` same-anchor pair is branch-internal
  (closure), hence ordered by that branch's witness;
* (c′) branch-order extension — `hK4`/`hK5` verbatim through
  `build_row_raw`;
* (d) collapse = merge — `dropF_eq_of_rows` with, per key: live keys by
  `build_collapse_row_raw` + `hK6`, dead keys by matching absence
  (`slots_live_iff`: the merge's live set is exactly the union's
  inserted-not-deleted ids). -/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

/-! ## §0 order plumbing -/

theorem before_of_sublist2 {γ : Type} {u v : γ} :
    ∀ {l : List γ}, List.Sublist [u, v] l → Before l u v
  | [], h => nomatch h
  | a :: l, h => by
      cases h with
      | cons _ h' => exact before_cons (before_of_sublist2 h')
      | cons₂ _ h' =>
          exact before_head (h'.subset (List.mem_cons_self ..))

/-- `precedes` is asymmetric on duplicate-free lists. -/
theorem precedes_asymm {l : List Nat} (hnd : l.Nodup) {u v : Nat}
    (h1 : Shesha.precedes l u v) (h2 : Shesha.precedes l v u) : False :=
  before_asymm hnd (before_of_sublist2 h1) (before_of_sublist2 h2)

/-! ## §1 event bookkeeping over the union -/

/-- Membership unfolding for union delete targets. -/
theorem delIn_union_iff {ev₁ ev₂ : Set (Op SAppOp)} {u : Nat} :
    DelIn (ev₁ ∪ ev₂) u ↔ DelIn ev₁ u ∨ DelIn ev₂ u := by
  constructor
  · rintro ⟨t, r, hm⟩
    rcases (Set.mem_union _ _ _).mp hm with h | h
    · exact Or.inl ⟨t, r, h⟩
    · exact Or.inr ⟨t, r, h⟩
  · rintro (⟨t, r, h⟩ | ⟨t, r, h⟩)
    · exact ⟨t, r, Set.mem_union_left _ h⟩
    · exact ⟨t, r, Set.mem_union_right _ h⟩

/-- Union symmetry transfer for delete targets (feeds the mirror
instances of the branch lemmas). -/
theorem delIn_union_comm {ev₁ ev₂ : Set (Op SAppOp)} {u : Nat} :
    DelIn (ev₂ ∪ ev₁) u ↔ DelIn (ev₁ ∪ ev₂) u := by
  rw [delIn_union_iff, delIn_union_iff]
  exact Or.comm

/-- Union symmetry transfer for inserts. -/
theorem insIn_union_comm {ev₁ ev₂ : Set (Op SAppOp)} {x p : Nat} :
    InsIn (ev₂ ∪ ev₁) x p ↔ InsIn (ev₁ ∪ ev₂) x p := by
  constructor <;>
    (rintro ⟨r, hm⟩
     rcases (Set.mem_union _ _ _).mp hm with h | h
     · exact ⟨r, Set.mem_union_right _ h⟩
     · exact ⟨r, Set.mem_union_left _ h⟩)

/-- A (nonroot) anchor of a union insert is itself a union insert. -/
theorem union_anchor {C' : Configuration SheshaD} (hH : SheshaHonest C')
    {ev₁ ev₂ : Set (Op SAppOp)}
    (hsub₁ : ∀ a ∈ ev₁, a ∈ C'.events) (hsub₂ : ∀ a ∈ ev₂, a ∈ C'.events)
    (hclosed₁ : ∀ a b, C'.vis a b → ¬ SheshaD.toCRDTSig.commutes a b →
      b ∈ ev₁ → a ∈ ev₁)
    (hclosed₂ : ∀ a b, C'.vis a b → ¬ SheshaD.toCRDTSig.commutes a b →
      b ∈ ev₂ → a ∈ ev₂)
    {x p : Nat} (hx : InsIn (ev₁ ∪ ev₂) x p) (hp0 : p ≠ 0) :
    ∃ a, InsIn (ev₁ ∪ ev₂) p a := by
  obtain ⟨r, hr⟩ := hx
  rcases (Set.mem_union _ _ _).mp hr with h | h
  · obtain ⟨r', a', hpe, hpvis⟩ :=
      honest_anchor_sees_ins hH hp0 (hsub₁ _ h)
    have hnc : ¬ SheshaD.toCRDTSig.commutes
        (p, r', SAppOp.insA a') (x, r, SAppOp.insA p) :=
      ncomm_ins_anchor_child hp0 (honest_ins_ne_anchor hH hpe)
    exact ⟨a', r', Set.mem_union_left _ (hclosed₁ _ _ hpvis hnc h)⟩
  · obtain ⟨r', a', hpe, hpvis⟩ :=
      honest_anchor_sees_ins hH hp0 (hsub₂ _ h)
    have hnc : ¬ SheshaD.toCRDTSig.commutes
        (p, r', SAppOp.insA a') (x, r, SAppOp.insA p) :=
      ncomm_ins_anchor_child hp0 (honest_ins_ne_anchor hH hpe)
    exact ⟨a', r', Set.mem_union_right _ (hclosed₂ _ _ hpvis hnc h)⟩

/-- Anchors precede their children in Lamport order. -/
theorem anchor_lt {C' : Configuration SheshaD} (hH : SheshaHonest C')
    {x p : Nat} {r : Replica} (hp0 : p ≠ 0)
    (hx : (x, r, SAppOp.insA p) ∈ C'.events) : p < x := by
  obtain ⟨r', a', hpe, hpvis⟩ := honest_anchor_sees_ins hH hp0 hx
  exact C'.causal_mono hpvis

/-- An id's insert anchor is unique across the configuration. -/
theorem ins_anchor_unique {C' : Configuration SheshaD} {x p q : Nat}
    {rp rq : Replica}
    (hp : (x, rp, SAppOp.insA p) ∈ C'.events)
    (hq : (x, rq, SAppOp.insA q) ∈ C'.events) : p = q := by
  have h := (Configuration.core C').ts_unique hp hq rfl
  injection h with h1 h2
  injection h2 with h3 h4
  injection h4

/-- A delete pulls its target's insert into the (closed) event set. -/
theorem ins_mem_of_del {C' : Configuration SheshaD} (hH : SheshaHonest C')
    {ev : Set (Op SAppOp)}
    (hsub : ∀ a ∈ ev, a ∈ C'.events)
    (hclosed : ∀ a b, C'.vis a b → ¬ SheshaD.toCRDTSig.commutes a b →
      b ∈ ev → a ∈ ev)
    {u p : Nat} {r : Replica} (hi : (u, r, SAppOp.insA p) ∈ C'.events)
    (hd : DelIn ev u) : (u, r, SAppOp.insA p) ∈ ev := by
  obtain ⟨td, rd, hdm⟩ := hd
  have hvis := honest_ins_vis_del hH hi (hsub _ hdm)
  have hnc : ¬ SheshaD.toCRDTSig.commutes
      (u, r, SAppOp.insA p) (td, rd, SAppOp.delA u) :=
    ncomm_ins_del_self (honest_ins_ne_anchor hH hi)
  exact hclosed _ _ hvis hnc hdm

/-! ## §2 the live-set identity

The merge's membership predicate over the three normal-form slots is
exactly the union's inserted-not-deleted set: patterns 2/6/7 collapse to
`InsIn (ev₁ ∪ ev₂) ∧ ¬ DelIn (ev₁ ∪ ev₂)` through the closure facts
(a cross-branch delete pulls the insert across, making it common). -/

open Classical in
theorem slots_live_iff {C' : Configuration SheshaD} (hH : SheshaHonest C')
    {ev₁ ev₂ : Set (Op SAppOp)}
    (hsub₁ : ∀ a ∈ ev₁, a ∈ C'.events) (hsub₂ : ∀ a ∈ ev₂, a ∈ C'.events)
    (hclosed₁ : ∀ a b, C'.vis a b → ¬ SheshaD.toCRDTSig.commutes a b →
      b ∈ ev₁ → a ∈ ev₁)
    (hclosed₂ : ∀ a b, C'.vis a b → ¬ SheshaD.toCRDTSig.commutes a b →
      b ∈ ev₂ → a ∈ ev₂)
    {T₀ T₁ T₂ : Shesha.St}
    (hreads₀ : ∀ u, u ∈ Shesha.read T₀ ↔ ∃ p, InsIn (ev₁ ∩ ev₂) u p)
    (hreads₁ : ∀ u, u ∈ Shesha.read T₁ ↔ ∃ p, InsIn ev₁ u p)
    (hreads₂ : ∀ u, u ∈ Shesha.read T₂ ↔ ∃ p, InsIn ev₂ u p)
    (u : Nat) :
    Shesha.liveMp
        (Shesha.dropF (fun v => decide (DelIn (ev₁ ∩ ev₂) v)) T₀)
        (Shesha.dropF (fun v => decide (DelIn ev₁ v)) T₁)
        (Shesha.dropF (fun v => decide (DelIn ev₂ v)) T₂) u = true
      ↔ ((∃ p, InsIn (ev₁ ∪ ev₂) u p) ∧ ¬ DelIn (ev₁ ∪ ev₂) u) := by
  simp only [Shesha.liveMp, Bool.or_eq_true, Bool.and_eq_true,
    Bool.not_eq_true', Shesha.contains_iff, Shesha.contains_eq_false]
  rw [read_nf hreads₀, read_nf hreads₁, read_nf hreads₂]
  constructor
  · rintro ((h₁ | h₁) | h₂)
    · -- live in both branches
      obtain ⟨⟨⟨p, r, hm⟩, hd₁⟩, ⟨-, hd₂⟩⟩ := h₁
      refine ⟨⟨p, r, Set.mem_union_left _ hm⟩, ?_⟩
      intro hd
      rcases delIn_union_iff.mp hd with h | h
      · exact hd₁ h
      · exact hd₂ h
    · -- A-live, off the LCA
      obtain ⟨⟨⟨p, r, hm⟩, hd₁⟩, hnL⟩ := h₁
      refine ⟨⟨p, r, Set.mem_union_left _ hm⟩, ?_⟩
      intro hd
      rcases delIn_union_iff.mp hd with h | h
      · exact hd₁ h
      · -- a branch-2 delete would make the insert common — LCA-live
        have hm₂ : (u, r, SAppOp.insA p) ∈ ev₂ :=
          ins_mem_of_del hH hsub₂ hclosed₂ (hsub₁ _ hm) h
        refine hnL ⟨⟨p, r, (Set.mem_inter_iff ..).mpr ⟨hm, hm₂⟩⟩, ?_⟩
        rintro ⟨t, r', hdm⟩
        exact hd₁ ⟨t, r', ((Set.mem_inter_iff ..).mp hdm).1⟩
    · -- B-live, off the LCA
      obtain ⟨⟨⟨p, r, hm⟩, hd₂⟩, hnL⟩ := h₂
      refine ⟨⟨p, r, Set.mem_union_right _ hm⟩, ?_⟩
      intro hd
      rcases delIn_union_iff.mp hd with h | h
      · have hm₁ : (u, r, SAppOp.insA p) ∈ ev₁ :=
          ins_mem_of_del hH hsub₁ hclosed₁ (hsub₂ _ hm) h
        refine hnL ⟨⟨p, r, (Set.mem_inter_iff ..).mpr ⟨hm₁, hm⟩⟩, ?_⟩
        rintro ⟨t, r', hdm⟩
        exact hd₂ ⟨t, r', ((Set.mem_inter_iff ..).mp hdm).2⟩
      · exact hd₂ h
  · rintro ⟨⟨p, r, hm⟩, hnd⟩
    have hd₁ : ¬ DelIn ev₁ u := fun h =>
      hnd (delIn_union_iff.mpr (Or.inl h))
    have hd₂ : ¬ DelIn ev₂ u := fun h =>
      hnd (delIn_union_iff.mpr (Or.inr h))
    rcases (Set.mem_union _ _ _).mp hm with h | h
    · by_cases h2 : ∃ q, InsIn ev₂ u q
      · exact Or.inl (Or.inl ⟨⟨⟨p, r, h⟩, hd₁⟩, ⟨h2, hd₂⟩⟩)
      · refine Or.inl (Or.inr ⟨⟨⟨p, r, h⟩, hd₁⟩, ?_⟩)
        rintro ⟨⟨q, r', hq⟩, -⟩
        exact h2 ⟨q, r', ((Set.mem_inter_iff ..).mp hq).2⟩
    · by_cases h1 : ∃ q, InsIn ev₁ u q
      · exact Or.inl (Or.inl ⟨⟨h1, hd₁⟩, ⟨⟨p, r, h⟩, hd₂⟩⟩)
      · refine Or.inr ⟨⟨⟨p, r, h⟩, hd₂⟩, ?_⟩
        rintro ⟨⟨q, r', hq⟩, -⟩
        exact h1 ⟨q, r', ((Set.mem_inter_iff ..).mp hq).1⟩

/-- **The marker bridge**: the merge's *structural* marker predicate
(`markerp` — an LCA-live id killed in exactly one branch) implies the
*event-level* union delete. Consumed by the residue's `hK6`: `merge_row`
expresses the merge output as `expandRow … (markerp …)`, and every id it
splices out is `DelIn (ev₁ ∪ ev₂)` — so the merge's splices are a subset
of the pre-splice store's `DelIn`-union splices (the extra ones being the
ghosts, whose live descendants the collapse re-homes). Stated over the
collapsed-slot read characterizations (`read_nf` instances). -/
theorem markerp_imp_delUnion {ev₁ ev₂ : Set (Op SAppOp)}
    {s₀ s₁ s₂ : Shesha.St}
    (hs₀ : ∀ u, u ∈ Shesha.read s₀ ↔
      (∃ p, InsIn (ev₁ ∩ ev₂) u p) ∧ ¬ DelIn (ev₁ ∩ ev₂) u)
    (hs₁ : ∀ u, u ∈ Shesha.read s₁ ↔ (∃ p, InsIn ev₁ u p) ∧ ¬ DelIn ev₁ u)
    (hs₂ : ∀ u, u ∈ Shesha.read s₂ ↔ (∃ p, InsIn ev₂ u p) ∧ ¬ DelIn ev₂ u)
    (u : Nat) (hm : Shesha.markerp s₀ s₁ s₂ u = true) :
    DelIn (ev₁ ∪ ev₂) u := by
  rw [Shesha.markerp, Bool.and_eq_true] at hm
  obtain ⟨h0, hne⟩ := hm
  obtain ⟨⟨p, r, hmem⟩, -⟩ := (hs₀ u).mp (Shesha.contains_iff.mp h0)
  have hin₁ : ∃ q, InsIn ev₁ u q :=
    ⟨p, r, ((Set.mem_inter_iff ..).mp hmem).1⟩
  have hin₂ : ∃ q, InsIn ev₂ u q :=
    ⟨p, r, ((Set.mem_inter_iff ..).mp hmem).2⟩
  cases h1 : Shesha.contains s₁ u <;> cases h2 : Shesha.contains s₂ u
  · exact absurd (h1 ▸ h2 ▸ hne) (by decide)
  · -- ¬s₁-live, s₂-live: `u` inserted in `ev₁` but not in `read s₁`,
    -- so it was deleted in branch 1.
    have hnr := Shesha.contains_eq_false.mp h1
    by_cases hd : DelIn ev₁ u
    · exact delIn_union_iff.mpr (Or.inl hd)
    · exact absurd ((hs₁ u).mpr ⟨hin₁, hd⟩) hnr
  · have hnr := Shesha.contains_eq_false.mp h2
    by_cases hd : DelIn ev₂ u
    · exact delIn_union_iff.mpr (Or.inr hd)
    · exact absurd ((hs₂ u).mpr ⟨hin₂, hd⟩) hnr
  · exact absurd (h1 ▸ h2 ▸ hne) (by decide)

/-! ## §3 the pre-splice forest, packed

`build_pack` hides the builder: from a graded union row store it
produces the forest `T` with its read set, its rows, and its collapse
rows — everything the assembly consumes. -/

open Classical in
theorem build_pack {C' : Configuration SheshaD} (hH : SheshaHonest C')
    {ev₁ ev₂ : Set (Op SAppOp)}
    (hsub₁ : ∀ a ∈ ev₁, a ∈ C'.events) (hsub₂ : ∀ a ∈ ev₂, a ∈ C'.events)
    (hclosed₁ : ∀ a b, C'.vis a b → ¬ SheshaD.toCRDTSig.commutes a b →
      b ∈ ev₁ → a ∈ ev₁)
    (hclosed₂ : ∀ a b, C'.vis a b → ¬ SheshaD.toCRDTSig.commutes a b →
      b ∈ ev₂ → a ∈ ev₂)
    (preRows : List (Nat × List Nat)) (n : Nat)
    (hK1 : ∀ q x, x ∈ Shesha.alGet preRows q ↔ InsIn (ev₁ ∪ ev₂) x q)
    (hK2 : ∀ q, (Shesha.alGet preRows q).Nodup)
    (hK3 : ∀ q c, c ∈ Shesha.alGet preRows q → q < c ∧ c ≤ n) :
    ∃ T : Shesha.St,
      Shesha.WF T
      ∧ (∀ u, u ∈ Shesha.read T ↔ ∃ p, InsIn (ev₁ ∪ ev₂) u p)
      ∧ (∀ p, (p ∈ Shesha.read T ∨ p = 0) →
          Shesha.row T p = Shesha.alGet preRows p)
      ∧ (∀ q, (q ∈ Shesha.read T ∨ q = 0) →
          decide (DelIn (ev₁ ∪ ev₂) q) = false →
          Shesha.row (Shesha.dropF
              (fun u => decide (DelIn (ev₁ ∪ ev₂) u)) T) q
            = Shesha.expandRow preRows
                (fun u => decide (DelIn (ev₁ ∪ ev₂) u)) n
                (Shesha.alGet preRows q)) := by
  have hedge : ∀ p u, u ∈ Shesha.alGet preRows p → p < u :=
    fun p u hu => (hK3 p u hu).1
  have hbound : ∀ p u, u ∈ Shesha.alGet preRows p → u ≤ n :=
    fun p u hu => (hK3 p u hu).2
  have hnz : ∀ p u, u ∈ Shesha.alGet preRows p → u ≠ 0 := by
    intro p u hu h0
    have := (hK3 p u hu).1
    omega
  have hsubU : ∀ a ∈ ev₁ ∪ ev₂, a ∈ C'.events := fun a ha =>
    ((Set.mem_union _ _ _).mp ha).elim (hsub₁ a) (hsub₂ a)
  have huniq : ∀ v r₁ r₂, v ∈ Shesha.alGet preRows r₁ →
      v ∈ Shesha.alGet preRows r₂ → r₁ = r₂ := by
    intro v r₁ r₂ h₁ h₂
    obtain ⟨ra, hra⟩ := (hK1 r₁ v).mp h₁
    obtain ⟨rb, hrb⟩ := (hK1 r₂ v).mp h₂
    exact ins_anchor_unique (hsubU _ hra) (hsubU _ hrb)
  have hanc : ∀ p u, u ∈ Shesha.alGet preRows p →
      p = 0 ∨ ∃ q, p ∈ Shesha.alGet preRows q := by
    intro p u hu
    by_cases hp0 : p = 0
    · exact Or.inl hp0
    · obtain ⟨a, ha⟩ := union_anchor hH hsub₁ hsub₂ hclosed₁ hclosed₂
        ((hK1 p u).mp hu) hp0
      exact Or.inr ⟨a, (hK1 a p).mpr ha⟩
  have hwfT : Shesha.WF
      (Shesha.buildF preRows (fun _ => false) 0 (n + 1) 0) :=
    Shesha.build_WF_raw preRows _ (fun x => x) hedge hK2 huniq hnz (n + 1)
  refine ⟨Shesha.buildF preRows (fun _ => false) 0 (n + 1) 0,
    hwfT, ?_, ?_, ?_⟩
  · intro u
    constructor
    · intro h
      obtain ⟨r, hr⟩ := Shesha.build_mem_raw preRows _ (n + 1) 0 h
      exact ⟨r, (hK1 r u).mp hr⟩
    · rintro ⟨p, hp⟩
      have hu : u ∈ Shesha.alGet preRows p := (hK1 p u).mpr hp
      exact Shesha.build_cover_raw preRows _ (fun x => x) hedge hanc
        n u p (hbound p u hu) hu
  · intro p hp
    exact Shesha.build_row_raw preRows _ (fun x => x) n hedge hbound hnz
      rfl n (by omega) hwfT.1 hp
  · intro q hq hDq
    exact Shesha.build_collapse_row_raw preRows _
      (fun u => decide (DelIn (ev₁ ∪ ev₂) u)) (fun x => x) n
      hedge hbound rfl n (by omega) hwfT.1 hq hDq

/-! ## §4 the assembly: pre-splice forest from the row store -/

open Classical in
/-- **The forest-level reduction**: every clause of the pre-splice
obligation follows from the row-store package `hK1`–`hK6`. The residue
(`hK6` and the order clauses) is pure row combinatorics. -/
theorem presplice_of_rows
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
    (preRows : List (Nat × List Nat)) (n : Nat)
    (hK1 : ∀ q x, x ∈ Shesha.alGet preRows q ↔ InsIn (ev₁ ∪ ev₂) x q)
    (hK2 : ∀ q, (Shesha.alGet preRows q).Nodup)
    (hK3 : ∀ q c, c ∈ Shesha.alGet preRows q → q < c ∧ c ≤ n)
    (hK4 : ∀ p tx ty rx ry,
      Before ρ₁ (tx, rx, SAppOp.insA p) (ty, ry, SAppOp.insA p) →
      Shesha.precedes (Shesha.alGet preRows p) ty tx)
    (hK5 : ∀ p tx ty rx ry,
      Before ρ₂ (tx, rx, SAppOp.insA p) (ty, ry, SAppOp.insA p) →
      Shesha.precedes (Shesha.alGet preRows p) ty tx)
    (hK6 : ∀ q, q ∈ Shesha.read (SheshaD.mergeL s₀ s₁ s₂) ∨ q = 0 →
      Shesha.expandRow preRows
          (fun u => decide (DelIn (ev₁ ∪ ev₂) u)) n
          (Shesha.alGet preRows q)
        = Shesha.row (SheshaD.mergeL s₀ s₁ s₂) q) :
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
  have hsubU : ∀ a ∈ ev₁ ∪ ev₂, a ∈ C'.events := fun a ha =>
    ((Set.mem_union _ _ _).mp ha).elim (hsub₁ a) (hsub₂ a)
  obtain ⟨T, hwfT, hreadT, hrowT, hcollT⟩ :=
    build_pack hH hsub₁ hsub₂ hclosed₁ hclosed₂ preRows n hK1 hK2 hK3
  -- rows are stored rows at every insert anchor
  have hrow_of_ins : ∀ {p x : Nat}, InsIn (ev₁ ∪ ev₂) x p →
      Shesha.row T p = Shesha.alGet preRows p := by
    intro p x hx
    by_cases hp0 : p = 0
    · exact hrowT p (Or.inr hp0)
    · obtain ⟨a, ha⟩ := union_anchor hH hsub₁ hsub₂ hclosed₁ hclosed₂
        hx hp0
      exact hrowT p (Or.inl ((hreadT p).mpr ⟨a, ha⟩))
  -- (b)
  have hrows : ∀ p x, x ∈ Shesha.row T p ↔ InsIn (ev₁ ∪ ev₂) x p := by
    intro p x
    constructor
    · intro hx
      by_cases hp0 : p = 0
      · subst hp0
        rw [hrowT 0 (Or.inr rfl)] at hx
        exact (hK1 0 x).mp hx
      · rw [hrowT p (Or.inl (Shesha.row_parent_mem hp0 hx))] at hx
        exact (hK1 p x).mp hx
    · intro hx
      rw [hrow_of_ins hx]
      exact (hK1 p x).mpr hx
  -- (c′)
  have hext₁ : ∀ p tx ty rx ry,
      Before ρ₁ (tx, rx, SAppOp.insA p) (ty, ry, SAppOp.insA p) →
      Shesha.precedes (Shesha.row T p) ty tx := by
    intro p tx ty rx ry hbef
    have hmem : (tx, rx, SAppOp.insA p) ∈ ev₁ :=
      (hc₁.1.2 _).mp (before_mem_left hbef)
    rw [hrow_of_ins ⟨rx, Set.mem_union_left _ hmem⟩]
    exact hK4 p tx ty rx ry hbef
  have hext₂ : ∀ p tx ty rx ry,
      Before ρ₂ (tx, rx, SAppOp.insA p) (ty, ry, SAppOp.insA p) →
      Shesha.precedes (Shesha.row T p) ty tx := by
    intro p tx ty rx ry hbef
    have hmem : (tx, rx, SAppOp.insA p) ∈ ev₂ :=
      (hc₂.1.2 _).mp (before_mem_left hbef)
    rw [hrow_of_ins ⟨rx, Set.mem_union_right _ hmem⟩]
    exact hK5 p tx ty rx ry hbef
  refine ⟨T, hwfT, hrows, ?_, hext₁, hext₂, ?_⟩
  · -- (c): a `vis` same-anchor pair is branch-internal; the branch
    -- witness orders it (respects `loOn`), so (c′) pins the row order —
    -- the other way.
    intro p x y rx ry hx hy hprec hvis
    have hxy : x ≠ y := by
      rintro rfl
      have heq := (Configuration.core C').ts_unique
        (hsubU _ hx) (hsubU _ hy) rfl
      rw [heq] at hvis
      exact hirr _ hvis
    have hnc : ¬ SheshaD.toCRDTSig.commutes
        (x, rx, SAppOp.insA p) (y, ry, SAppOp.insA p) :=
      ncomm_ins_ins_same_anchor hxy
        (honest_ins_ne_anchor hH (hsubU _ hx))
        (honest_ins_ne_anchor hH (hsubU _ hy))
    have hndrow : (Shesha.row T p).Nodup := Shesha.row_nodup hwfT p
    have hne : ((x, rx, SAppOp.insA p) : Op SAppOp)
        ≠ (y, ry, SAppOp.insA p) := by
      intro he
      injection he with h1 h2
      exact hxy h1
    rcases (Set.mem_union _ _ _).mp hy with hy1 | hy2
    · have hx1 : (x, rx, SAppOp.insA p) ∈ ev₁ := hclosed₁ _ _ hvis hnc hy1
      rcases before_trichotomy ((hc₁.1.2 _).mpr hx1)
          ((hc₁.1.2 _).mpr hy1) hne with hb | hb
      · exact precedes_asymm hndrow hprec (hext₁ p x y rx ry hb)
      · exact pairwise_before hc₁.2.1 hb (loOn_shesha_iff.mpr ⟨hvis, hnc⟩)
    · have hx2 : (x, rx, SAppOp.insA p) ∈ ev₂ := hclosed₂ _ _ hvis hnc hy2
      rcases before_trichotomy ((hc₂.1.2 _).mpr hx2)
          ((hc₂.1.2 _).mpr hy2) hne with hb | hb
      · exact precedes_asymm hndrow hprec (hext₂ p x y rx ry hb)
      · exact pairwise_before hc₂.2.1 hb (loOn_shesha_iff.mpr ⟨hvis, hnc⟩)
  · -- (d): collapse = merge, row by row
    obtain ⟨T₀, hwf₀, hreads₀, hrows₀, hcompat₀, hfold₀, hrowEq₀⟩ :=
      witness_nf hH hirr
        (fun a ha => hsub₁ a ((Set.mem_inter_iff ..).mp ha).1)
        (fun a b hv hnc hb => (Set.mem_inter_iff ..).mpr
          ⟨hclosed₁ a b hv hnc ((Set.mem_inter_iff ..).mp hb).1,
           hclosed₂ a b hv hnc ((Set.mem_inter_iff ..).mp hb).2⟩)
        hc₀.1 hc₀.2.1 hc₀.2.2.1
    obtain ⟨T₁, hwf₁, hreads₁, hrows₁, hcompat₁, hfold₁, hrowEq₁⟩ :=
      witness_nf hH hirr hsub₁ hclosed₁ hc₁.1 hc₁.2.1 hc₁.2.2.1
    obtain ⟨T₂, hwf₂, hreads₂, hrows₂, hcompat₂, hfold₂, hrowEq₂⟩ :=
      witness_nf hH hirr hsub₂ hclosed₂ hc₂.1 hc₂.2.1 hc₂.2.2.1
    have hs₀ : s₀
        = Shesha.dropF (fun u => decide (DelIn (ev₁ ∩ ev₂) u)) T₀ := by
      rw [← hc₀.2.2.2]
      exact hfold₀
    have hs₁ : s₁ = Shesha.dropF (fun u => decide (DelIn ev₁ u)) T₁ := by
      rw [← hc₁.2.2.2]
      exact hfold₁
    have hs₂ : s₂ = Shesha.dropF (fun u => decide (DelIn ev₂ u)) T₂ := by
      rw [← hc₂.2.2.2]
      exact hfold₂
    have mok := slots_modelOK hsub₁ hsub₂ hwf₀ hwf₁ hwf₂
      hreads₀ hreads₁ hreads₂
    rw [← hs₀, ← hs₁, ← hs₂] at mok
    have hA := slots_LRowsOK hH hsub₁ hclosed₁ hclosed₂ hwf₁
      hreads₀ hrows₁
    rw [← hs₀, ← hs₁] at hA
    have hreads₀' : ∀ u, u ∈ Shesha.read T₀
        ↔ ∃ p, InsIn (ev₂ ∩ ev₁) u p := by
      intro u
      rw [hreads₀ u]
      constructor
      · rintro ⟨p, r, hm⟩
        exact ⟨p, r, (Set.mem_inter_iff ..).mpr
          ⟨((Set.mem_inter_iff ..).mp hm).2,
           ((Set.mem_inter_iff ..).mp hm).1⟩⟩
      · rintro ⟨p, r, hm⟩
        exact ⟨p, r, (Set.mem_inter_iff ..).mpr
          ⟨((Set.mem_inter_iff ..).mp hm).2,
           ((Set.mem_inter_iff ..).mp hm).1⟩⟩
    have hB := slots_LRowsOK hH hsub₂ hclosed₂ hclosed₁ hwf₂
      hreads₀' hrows₂
    have hDcomm : ∀ u, decide (DelIn (ev₂ ∩ ev₁) u)
        = decide (DelIn (ev₁ ∩ ev₂) u) := by
      intro u
      apply decide_eq_decide.mpr
      constructor
      · rintro ⟨t, r, hm⟩
        exact ⟨t, r, (Set.mem_inter_iff ..).mpr
          ⟨((Set.mem_inter_iff ..).mp hm).2,
           ((Set.mem_inter_iff ..).mp hm).1⟩⟩
      · rintro ⟨t, r, hm⟩
        exact ⟨t, r, (Set.mem_inter_iff ..).mpr
          ⟨((Set.mem_inter_iff ..).mp hm).2,
           ((Set.mem_inter_iff ..).mp hm).1⟩⟩
    rw [Shesha.dropF_congr hDcomm T₀, ← hs₀, ← hs₂] at hB
    have hlive0 := slots_live_iff hH hsub₁ hsub₂ hclosed₁ hclosed₂
      hreads₀ hreads₁ hreads₂
    rw [← hs₀, ← hs₁, ← hs₂] at hlive0
    have hlive : ∀ u, u ∈ Shesha.read (SheshaD.mergeL s₀ s₁ s₂)
        ↔ ((∃ p, InsIn (ev₁ ∪ ev₂) u p) ∧ ¬ DelIn (ev₁ ∪ ev₂) u) :=
      fun u => (Shesha.merge_ids mok hA hB u).trans (hlive0 u)
    refine Shesha.dropF_eq_of_rows hwfT (Shesha.merge_WF mok hA hB) _
      (fun p => ?_)
    by_cases hp : p ∈ Shesha.read (SheshaD.mergeL s₀ s₁ s₂) ∨ p = 0
    · have hDp : decide (DelIn (ev₁ ∪ ev₂) p) = false := by
        rcases hp with hp | rfl
        · exact decide_eq_false ((hlive p).mp hp).2
        · refine decide_eq_false ?_
          rintro ⟨t, r, hm⟩
          exact honest_del_nonzero hH (hsubU _ hm) rfl
      have hpT : p ∈ Shesha.read T ∨ p = 0 := by
        rcases hp with hp | rfl
        · exact Or.inl ((hreadT p).mpr ((hlive p).mp hp).1)
        · exact Or.inr rfl
      rw [hcollT p hpT hDp]
      exact hK6 p hp
    · have hp0 : p ≠ 0 := fun h0 => hp (Or.inr h0)
      have hnm : p ∉ Shesha.read (SheshaD.mergeL s₀ s₁ s₂) :=
        fun hm => hp (Or.inl hm)
      have h1 : p ∉ Shesha.read
          (Shesha.dropF (fun u => decide (DelIn (ev₁ ∪ ev₂) u)) T) := by
        intro hmem
        rw [Shesha.read_dropF, List.mem_filter] at hmem
        have hins := (hreadT p).mp hmem.1
        have hnd : ¬ DelIn (ev₁ ∪ ev₂) p := by
          have h2 := hmem.2
          rw [Bool.not_eq_eq_eq_not, Bool.not_true,
            decide_eq_false_iff_not] at h2
          exact h2
        exact hnm ((hlive p).mpr ⟨hins, hnd⟩)
      rw [Shesha.row, if_neg hp0, Shesha.rowF_absent h1,
        Shesha.row, if_neg hp0]
      exact (Shesha.rowF_absent hnm).symm

/-! ## §5 the branch-pure region

Ids inserted in one branch and not common. Below a branch-born anchor
*everything* is branch-pure (anchors of common inserts are common —
closure), the union delete-set restricts to the branch delete-set
(a cross delete would pull the insert across), and hence the subtree
front bridge applies: the ghost expansion of a store agreeing with the
branch forest on the region computes the branch slot's rows — the
branch-born key class of the residue's `hK6`. -/

/-- Inserted in `ev₁`, not common. -/
def BranchPure (ev₁ ev₂ : Set (Op SAppOp)) (u : Nat) : Prop :=
  (∃ p, InsIn ev₁ u p) ∧ ¬ ∃ p, InsIn (ev₁ ∩ ev₂) u p

/-- The region is closed under the branch forest's rows. -/
theorem branchPure_row_closed {C' : Configuration SheshaD}
    (hH : SheshaHonest C') {ev₁ ev₂ : Set (Op SAppOp)}
    (hsub₁ : ∀ a ∈ ev₁, a ∈ C'.events)
    (hclosed₂ : ∀ a b, C'.vis a b → ¬ SheshaD.toCRDTSig.commutes a b →
      b ∈ ev₂ → a ∈ ev₂)
    {T₁ : Shesha.St}
    (hrows₁ : ∀ p x, x ∈ Shesha.row T₁ p ↔ InsIn ev₁ x p) :
    ∀ c, BranchPure ev₁ ev₂ c → ∀ u, u ∈ Shesha.row T₁ c →
      BranchPure ev₁ ev₂ u := by
  intro c hPc u hu
  obtain ⟨r, hue⟩ := (hrows₁ c u).mp hu
  refine ⟨⟨c, r, hue⟩, ?_⟩
  rintro ⟨p', r', hu'⟩
  have hu'₁ : (u, r', SAppOp.insA p') ∈ ev₁ :=
    ((Set.mem_inter_iff ..).mp hu').1
  have heq : ((u, r', SAppOp.insA p') : Op SAppOp)
      = (u, r, SAppOp.insA c) :=
    (Configuration.core C').ts_unique (hsub₁ _ hu'₁) (hsub₁ _ hue) rfl
  rw [heq] at hu'
  obtain ⟨pc, rc, hce₁⟩ := hPc.1
  have hc0 : c ≠ 0 := honest_ins_nonzero hH (hsub₁ _ hce₁)
  obtain ⟨rc', ac', hce, hcvis⟩ :=
    honest_anchor_sees_ins hH hc0 (hsub₁ _ hue)
  have hnc : ¬ SheshaD.toCRDTSig.commutes
      (c, rc', SAppOp.insA ac') (u, r, SAppOp.insA c) :=
    ncomm_ins_anchor_child hc0 (honest_ins_ne_anchor hH hce)
  have hc₂ : (c, rc', SAppOp.insA ac') ∈ ev₂ :=
    hclosed₂ _ _ hcvis hnc ((Set.mem_inter_iff ..).mp hu').2
  have hceq : ((c, rc, SAppOp.insA pc) : Op SAppOp)
      = (c, rc', SAppOp.insA ac') :=
    (Configuration.core C').ts_unique (hsub₁ _ hce₁) hce rfl
  exact hPc.2 ⟨ac', rc',
    (Set.mem_inter_iff ..).mpr ⟨hceq ▸ hce₁, hc₂⟩⟩

/-- On the region, the union delete-set is the branch delete-set. -/
theorem branchPure_del {C' : Configuration SheshaD}
    (hH : SheshaHonest C') {ev₁ ev₂ : Set (Op SAppOp)}
    (hsub₁ : ∀ a ∈ ev₁, a ∈ C'.events)
    (hsub₂ : ∀ a ∈ ev₂, a ∈ C'.events)
    (hclosed₂ : ∀ a b, C'.vis a b → ¬ SheshaD.toCRDTSig.commutes a b →
      b ∈ ev₂ → a ∈ ev₂) :
    ∀ u, BranchPure ev₁ ev₂ u →
      decide (DelIn (ev₁ ∪ ev₂) u) = decide (DelIn ev₁ u) := by
  intro u hPu
  apply decide_eq_decide.mpr
  constructor
  · intro hd
    rcases delIn_union_iff.mp hd with h | h
    · exact h
    · obtain ⟨p, r, hue⟩ := hPu.1
      have hu₂ : (u, r, SAppOp.insA p) ∈ ev₂ :=
        ins_mem_of_del hH hsub₂ hclosed₂ (hsub₁ _ hue) h
      exact absurd ⟨p, r, (Set.mem_inter_iff ..).mpr ⟨hue, hu₂⟩⟩ hPu.2
  · exact fun h => delIn_union_iff.mpr (Or.inl h)

/-- The region is closed under dead-descent chains. -/
theorem branchPure_chain {C' : Configuration SheshaD}
    (hH : SheshaHonest C') {ev₁ ev₂ : Set (Op SAppOp)}
    (hsub₁ : ∀ a ∈ ev₁, a ∈ C'.events)
    (hclosed₂ : ∀ a b, C'.vis a b → ¬ SheshaD.toCRDTSig.commutes a b →
      b ∈ ev₂ → a ∈ ev₂)
    {T₁ : Shesha.St} {D : Nat → Bool}
    (hrows₁ : ∀ p x, x ∈ Shesha.row T₁ p ↔ InsIn ev₁ x p)
    {q u : Nat} (hch : Shesha.RowChain T₁ D q u)
    (hPq : BranchPure ev₁ ev₂ q) : BranchPure ev₁ ev₂ u := by
  induction hch with
  | direct hwq =>
      exact branchPure_row_closed hH hsub₁ hclosed₂ hrows₁ _ hPq _ hwq
  | @through q' c w hcq hDc hch ih =>
      exact ih (branchPure_row_closed hH hsub₁ hclosed₂ hrows₁ _ hPq _ hcq)

/-- **The branch-born key equation** (`hK6`, branch-born class, branch-1
form; the branch-2 form is the mirror instance): at a live branch-pure
key, the ghost expansion of any store agreeing with the branch forest on
the region *is* the branch slot's row — which is the merge's output row
at branch-born keys (`outRows_alGet_of_bornA` + marker-freeness of the
region). -/
theorem born_key_expand {C' : Configuration SheshaD}
    (hH : SheshaHonest C') {ev₁ ev₂ : Set (Op SAppOp)}
    (hsub₁ : ∀ a ∈ ev₁, a ∈ C'.events)
    (hsub₂ : ∀ a ∈ ev₂, a ∈ C'.events)
    (hclosed₂ : ∀ a b, C'.vis a b → ¬ SheshaD.toCRDTSig.commutes a b →
      b ∈ ev₂ → a ∈ ev₂)
    {T₁ : Shesha.St} (hwf₁ : Shesha.WF T₁)
    (hrows₁ : ∀ p x, x ∈ Shesha.row T₁ p ↔ InsIn ev₁ x p)
    (rows : List (Nat × List Nat)) (lvl : Nat → Nat) (n : Nat)
    (hedge : ∀ p u, u ∈ Shesha.alGet rows p → lvl p < lvl u)
    (hbound : ∀ p u, u ∈ Shesha.alGet rows p → lvl u ≤ n)
    (hagree : ∀ c, BranchPure ev₁ ev₂ c →
      Shesha.alGet rows c = Shesha.row T₁ c)
    {q : Nat} (hPq : BranchPure ev₁ ev₂ q)
    (hqlive : q ∈ Shesha.read
      (Shesha.dropF (fun u => decide (DelIn ev₁ u)) T₁))
    (f : Nat) (hinv : n ≤ lvl q + f) :
    Shesha.expandRow rows (fun u => decide (DelIn (ev₁ ∪ ev₂) u)) f
        (Shesha.alGet rows q)
      = Shesha.row (Shesha.dropF (fun u => decide (DelIn ev₁ u)) T₁) q := by
  rw [Shesha.read_dropF, List.mem_filter] at hqlive
  have hD'q : decide (DelIn ev₁ q) = false := by
    have h2 := hqlive.2
    rw [Bool.not_eq_eq_eq_not, Bool.not_true] at h2
    exact h2
  exact Shesha.expand_eq_row_dropF hwf₁ rows _ _ lvl n
    (BranchPure ev₁ ev₂) hedge hbound hagree
    (branchPure_del hH hsub₁ hsub₂ hclosed₂)
    (branchPure_row_closed hH hsub₁ hclosed₂ hrows₁)
    hqlive.1 hPq hD'q f hinv

/-! ## §6 the row-store residue (the owed core) -/

open Classical in
/-- **The row-store residue** — the merge-correctness core at the *row*
level; everything forest-shaped is discharged (`presplice_of_rows`).
Owed: a store `preRows` of pre-splice rows for the union's inserts with

* `hK1`–`hK3` bookkeeping (exactly the union's inserts per original
  anchor, duplicate-free, Lamport-graded — anchors precede children);
* `hK4`/`hK5` order: each row extends both branch witnesses' same-anchor
  `Before` orders, reversed (rows are newest-first);
* `hK6` **the collapse equation**: the ghost expansion (`expandRow` at
  the union's delete targets) of each live key's row is the merge's
  output row.

Construction plan (per key class of `merge s₀ s₁ s₂`; the classes are
`outRows_alGet_of_skel/of_bornA/of_bornB/none` over the M0 classifiers):

* **branch-born keys** (`q` born in branch `i`): the row is forced,
  `preRow q := row Tᵢ q` (cross-branch inserts at `q` would make `q`
  common — closure). `hK6`: the merge takes the branch row wholesale
  (`outRows_alGet_of_bornA/B`, marker-free by `born_subtree_L_free`-style
  closure, so `expandRow_of_nonmarker` collapses the RHS), and the
  branch slot row is a front (`row_dropF`); the LHS ghost expansion
  matches it by a subtree-front induction over `T₁`/`T₂`, transporting
  `DelIn (ev₁ ∪ ev₂) ↔ DelIn evᵢ` on branch-only ids (`ins_mem_of_del`).
* **skeleton keys** (`q` common-live): the assembled row
  (`outRows_alGet_of_skel`, `rowAssemble`): skeleton entries carry
  `s₀`'s row order (= `T₀` row front, branch-agreed via `SCoh`), runs
  carry branch segments (`runsGo` machinery), same-slot runs interleave
  newest-head-first (`sortRunsDesc`), and `expandRow` splices markers to
  their subtree fronts — the ghosts of `preRow q` placed at their front
  positions. `preRow q` := the merge row's parse: live direct children
  and marker/ghost roots in output order, dead-in-both and LCA-ghost
  ids at their front slots (their expansions are the contiguous blocks
  the collapse leaves). Fronts of distinct dead children are contiguous
  and disjoint (`expandRow_count_le_one`/`base_unique` uniqueness), so
  the parse is well-defined.
* **dead keys** (union inserts absent from the merge): rows of dead
  keys only feed `hK6` through the ghost expansion of their live
  ancestors; take their branch/`T₀` rows verbatim.

`hK4`/`hK5` on common pairs is exactly branch agreement: `SCoh ρ₀ ρᵢ`
plus `witness_nf`'s rows (reversed `anchIds`) make the three slots agree
on every common same-anchor pair, and the merge preserves the skeleton
order (`merge_extends_L`) and run order (M3, owed here).

**Frontier note (this session).** The obligation is *order-dependent*:
`hK6`'s two sides are ordered lists, so `preRows` must carry the merge's
*exact* display order (`sortRunsDesc` tiebreak included) — a wrong-order
witness would make `hK6` a *false* `sorry`. Hence `hK4`/`hK5` for the
forced construction are entangled with the M3 run-order theorem, which is
still owed (`merge_extends_L` only settles the skeleton/`L`-projection,
not the branch-born run interleaving). There is thus no order-free prefix
to split off. What *is* now isolated: via `merge_row` the RHS is
`expandRow (outRows …) (markerp …)`, and `markerp_imp_delUnion` (§2)
shows every id the merge splices is `DelIn (ev₁ ∪ ev₂)` — so on the
merge-present ids the two marker predicates agree and the merge's splices
are a sub-multiset of `preRows`' `DelIn`-union splices. The *entire*
residual difficulty is therefore the **ghost re-homing**: the extra
`DelIn`-union splices (dead-in-both and born-and-died ids, absent from
`outRows`) must promote their live descendants to exactly the slots the
merge algorithm re-homed them to. That is M3 proper + the delete-splice
correctness, ≈1.5k lines concentrated in the skeleton-key parse. -/
theorem shesha_rows_residue
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
            = Shesha.row (SheshaD.mergeL s₀ s₁ s₂) q) := by
  sorry

end Sal.ConditionedMRDTs
