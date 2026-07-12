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

end Sal.ConditionedMRDTs
