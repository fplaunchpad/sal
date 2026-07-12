import Sal.ConditionedMRDTs.MRDT_Instances.Shesha.Shesha_Witness

/-! # Shesha — the coherence relation and the plan-order bridge

The Shesha instance of the coherent-witness route
(`Metatheory/WitnessCoherence.lean`):

* `SCoh` — **same-anchor insert coherence**: two same-anchor insert events
  common to two witnesses keep their relative (`Before`) order. This is
  exactly the branch-agreement datum whose absence refutes the plain
  `W`-join (`Shesha_Presplice_Refuted.lean`): the display order of
  concurrent same-anchor inserts is a `loOn`-free choice that survives in
  the state, so the three slots must inherit it coherently.
* the three `K`-bookkeeping facts (`scoh_refl`, `scoh_ext`, `scoh_sub`);
* `anchIds_planF_row` — **the plan-order bridge**: the `p`-anchored ids of
  a WF forest's plan are `p`'s row reversed (the plan builds rows by
  head-insertion). Through `anchIds_sublist2_before` this converts row
  order of the pre-splice forest into `Before` order of the assembled
  witness — how the join hook discharges its output-coherence obligation. -/

namespace Sal.ConditionedMRDTs

open Sal.Emulation

/-- `a` strictly before `b` in a prefix stays strictly before in any
extension on the right. -/
theorem before_append_left {γ : Type} {l l' : List γ} {a b : γ}
    (h : Before l a b) : Before (l ++ l') a b := by
  obtain ⟨l₁, l₂, hl, hb⟩ := h
  exact ⟨l₁, l₂ ++ l', by rw [hl, List.append_assoc, List.cons_append],
    List.mem_append_left _ hb⟩

/-- **Same-anchor insert coherence**: same-anchor insert events common to
both lists keep their relative order (one direction suffices — see
`before_asymm`). -/
def SCoh (ρ σ : List (Op SAppOp)) : Prop :=
  ∀ (p tx ty : Nat) (rx ry : Replica),
    (tx, rx, SAppOp.insA p) ∈ σ → (ty, ry, SAppOp.insA p) ∈ σ →
    Before ρ (tx, rx, SAppOp.insA p) (ty, ry, SAppOp.insA p) →
    Before σ (tx, rx, SAppOp.insA p) (ty, ry, SAppOp.insA p)

theorem scoh_refl (ρ : List (Op SAppOp)) : SCoh ρ ρ :=
  fun _ _ _ _ _ _ _ h => h

/-- A fresh event appended on the right preserves coherence. -/
theorem scoh_ext (ρ σ : List (Op SAppOp)) (e : Op SAppOp)
    (h : SCoh ρ σ) (he : e ∉ ρ) : SCoh ρ (σ ++ [e]) := by
  intro p tx ty rx ry hx hy hbef
  have hxρ : (tx, rx, SAppOp.insA p) ∈ ρ := before_mem_left hbef
  have hyρ : (ty, ry, SAppOp.insA p) ∈ ρ := before_mem_right hbef
  have hxσ : (tx, rx, SAppOp.insA p) ∈ σ := by
    rcases List.mem_append.mp hx with h' | h'
    · exact h'
    · rw [List.mem_singleton] at h'
      exact absurd (h' ▸ hxρ) he
  have hyσ : (ty, ry, SAppOp.insA p) ∈ σ := by
    rcases List.mem_append.mp hy with h' | h'
    · exact h'
    · rw [List.mem_singleton] at h'
      exact absurd (h' ▸ hyρ) he
  exact before_append_left (h p tx ty rx ry hxσ hyσ hbef)

/-- Coherence composes through a middleman containing the left list. -/
theorem scoh_sub (α β γ : List (Op SAppOp))
    (h₁ : SCoh α β) (h₂ : SCoh β γ) (hsub : ∀ x ∈ α, x ∈ β) :
    SCoh α γ := by
  intro p tx ty rx ry hx hy hbef
  refine h₂ p tx ty rx ry hx hy ?_
  exact h₁ p tx ty rx ry (hsub _ (before_mem_left hbef))
    (hsub _ (before_mem_right hbef)) hbef

end Sal.ConditionedMRDTs

namespace Shesha

/-! ## The plan-order bridge -/

theorem anchIds_append :
    ∀ (l₁ l₂ : List Op) (p : Nat),
      anchIds (l₁ ++ l₂) p = anchIds l₁ p ++ anchIds l₂ p
  | [], _, _ => rfl
  | .ins x a :: l₁, l₂, p => by
      rw [List.cons_append, anchIds, anchIds]
      by_cases hap : a = p
      · rw [if_pos hap, if_pos hap, anchIds_append l₁ l₂ p, List.cons_append]
      · rw [if_neg hap, if_neg hap, anchIds_append l₁ l₂ p]
  | .del d :: l₁, l₂, p => by
      rw [List.cons_append, anchIds, anchIds, anchIds_append l₁ l₂ p]

mutual
  /-- The `p`-anchored ids of a subtree's plan: the root (if planned at
  `p`) after the reversed row of `p` inside the subtree. -/
  theorem anchIds_planT_row {q : Nat} :
      ∀ {t : Tree}, (readT t).Nodup → q ∉ readT t → ∀ p,
        anchIds (planT q t) p
          = ((if q = p then [topId t] else []) ++ rowT p t).reverse
    | .node i cs, hnd, hq, p => by
        have hndT : i ∉ readF cs ∧ (readF cs).Nodup := by
          have : (i :: readF cs).Nodup := by
            rw [← readT]
            exact hnd
          exact List.nodup_cons.mp this
        have hi_ne : i ≠ q := fun he =>
          hq (by rw [readT, he]; exact List.mem_cons_self ..)
        have hq_cs : q ∉ readF cs := fun hm =>
          hq (by rw [readT]; exact List.mem_cons_of_mem _ hm)
        have ih := anchIds_planF_row' (F := cs) hndT.2 (q := i) hndT.1 p
        rw [planT, anchIds, ih, rowT]
        by_cases hqp : q = p
        · have hip : ¬ i = p := fun he => hi_ne (he.trans hqp.symm)
          rw [if_pos hqp, if_pos hqp, if_neg hip, if_neg hip,
            rowF_absent (hqp ▸ hq_cs), List.nil_append,
            show topId (Tree.node i cs) = i from rfl]
          rfl
        · rw [if_neg hqp, if_neg hqp, List.nil_append]
          by_cases hip : i = p
          · rw [if_pos hip, if_pos hip,
              rowF_absent (hip ▸ hndT.1), List.append_nil]
          · rw [if_neg hip, if_neg hip, List.nil_append]
  /-- Forest form. -/
  theorem anchIds_planF_row' {q : Nat} :
      ∀ {F : List Tree}, (readF F).Nodup → q ∉ readF F → ∀ p,
        anchIds (planF q F) p
          = ((if q = p then F.map topId else []) ++ rowF p F).reverse
    | [], _, _, p => by
        rw [planF, anchIds, List.map_nil, rowF]
        by_cases hqp : q = p
        · rw [if_pos hqp]
          rfl
        · rw [if_neg hqp]
          rfl
    | t :: ts, hnd, hq, p => by
        have hnd' : (readT t ++ readF ts).Nodup := by
          rw [← readF_cons]
          exact hnd
        have hqt : q ∉ readT t := fun h =>
          hq (by rw [readF_cons]; exact List.mem_append_left _ h)
        have hqts : q ∉ readF ts := fun h =>
          hq (by rw [readF_cons]; exact List.mem_append_right _ h)
        rw [planF, anchIds_append,
          anchIds_planF_row' (nodup_append_right hnd') hqts p,
          anchIds_planT_row (nodup_append_left hnd') hqt p,
          rowF, List.map_cons]
        by_cases hqp : q = p
        · rw [if_pos hqp, if_pos hqp, if_pos hqp,
            rowT_absent (hqp ▸ hqt), rowF_absent (hqp ▸ hqts),
            List.append_nil, List.append_nil, List.append_nil,
            List.append_nil, List.reverse_cons, List.reverse_cons,
            List.reverse_nil, List.nil_append]
        · rw [if_neg hqp, if_neg hqp, if_neg hqp, List.nil_append,
            List.nil_append, List.nil_append, List.reverse_append]
end

/-- **The plan-order bridge, state form**: for a WF forest, the plan's
`p`-anchored ids are `p`'s row reversed. -/
theorem anchIds_planF_row {T : St} (hwf : WF T) (p : Nat) :
    anchIds (planF 0 T) p = (row T p).reverse := by
  rw [anchIds_planF_row' hwf.1 hwf.2 p, row]
  by_cases hp : p = 0
  · rw [if_pos hp, if_pos hp.symm,
      rowF_absent (show p ∉ readF T from hp ▸ hwf.2), List.append_nil]
  · rw [if_neg hp, if_neg (fun h : (0 : Nat) = p => hp h.symm),
      List.nil_append]

/-! ## Forest extensionality

A WF forest is determined by its row function: two WF states with the same
rows (at every key, `0` included) are equal. This is the tool that reduces
the collapse equation of the pre-splice obligation
(`dropF (deleted) T = merge s₀ s₁ s₂`) to **per-row front equations**: by
`row_dropF`, each side's row at a live key is a front / an assembled-and-
expanded output row, and extensionality discharges the state equality once
the rows agree. -/

mutual
  /-- Subtrees of row-equal WF states with equal roots are equal. -/
  theorem extT {S₁ S₂ : St} (hwf₁ : WF S₁) (hwf₂ : WF S₂)
      (hrows : ∀ p, row S₁ p = row S₂ p) :
      ∀ (t₁ t₂ : Tree), t₁ ∈ subF S₁ → t₂ ∈ subF S₂ →
        topId t₁ = topId t₂ → t₁ = t₂
    | .node i cs, .node j ds, h₁, h₂, htop => by
        have hij : i = j := htop
        have hcs : cs.map topId = ds.map topId := by
          rw [← row_subtree hwf₁ h₁, ← row_subtree hwf₂ h₂, ← hij, hrows i]
        rw [hij, extF hwf₁ hwf₂ hrows cs ds
          (fun t ht => child_mem_subF h₁ ht)
          (fun t ht => child_mem_subF h₂ ht) hcs]
  /-- Forests of subtrees with equal top-id lists are equal. -/
  theorem extF {S₁ S₂ : St} (hwf₁ : WF S₁) (hwf₂ : WF S₂)
      (hrows : ∀ p, row S₁ p = row S₂ p) :
      ∀ (F₁ F₂ : List Tree), (∀ t ∈ F₁, t ∈ subF S₁) →
        (∀ t ∈ F₂, t ∈ subF S₂) → F₁.map topId = F₂.map topId → F₁ = F₂
    | [], [], _, _, _ => rfl
    | [], t₂ :: F₂, _, _, htop => by
        rw [List.map_nil, List.map_cons] at htop
        cases htop
    | t₁ :: F₁, [], _, _, htop => by
        rw [List.map_nil, List.map_cons] at htop
        cases htop
    | t₁ :: F₁, t₂ :: F₂, hs₁, hs₂, htop => by
        rw [List.map_cons, List.map_cons] at htop
        injection htop with hh ht
        rw [extT hwf₁ hwf₂ hrows t₁ t₂ (hs₁ _ (List.mem_cons_self ..))
            (hs₂ _ (List.mem_cons_self ..)) hh,
          extF hwf₁ hwf₂ hrows F₁ F₂
            (fun t ht => hs₁ _ (List.mem_cons_of_mem _ ht))
            (fun t ht => hs₂ _ (List.mem_cons_of_mem _ ht)) ht]
end

/-- **Forest extensionality**: WF states with the same rows are equal. -/
theorem forest_ext {S₁ S₂ : St} (hwf₁ : WF S₁) (hwf₂ : WF S₂)
    (hrows : ∀ p, row S₁ p = row S₂ p) : S₁ = S₂ := by
  refine extF hwf₁ hwf₂ hrows S₁ S₂
    (fun t ht => mem_subF_of_mem ht) (fun t ht => mem_subF_of_mem ht) ?_
  have h0 := hrows 0
  rw [row, if_pos rfl, row, if_pos rfl] at h0
  exact h0

/-- **The collapse-equation reduction**: to prove
`dropF D T = M` for a WF pre-splice forest `T` and a WF target `M`, it
suffices to match the rows — by `row_dropF`, fronts against `M`'s rows. -/
theorem dropF_eq_of_rows {T M : St} (hwfT : WF T) (hwfM : WF M)
    (D : Nat → Bool)
    (hrows : ∀ p, row (dropF D T) p = row M p) : dropF D T = M :=
  forest_ext (wf_dropF hwfT D) hwfM hrows

end Shesha
