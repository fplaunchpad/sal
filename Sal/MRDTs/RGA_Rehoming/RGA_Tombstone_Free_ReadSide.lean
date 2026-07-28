import Sal.MRDTs.RGA_Rehoming.RGA_Tombstone_Free_MRDT

open Classical

set_option maxHeartbeats 1000000

/-! # Tombstone-free RGA: read-side projection and intent-preservation theorems

The conditioned commutation/merge results in `RGA_Tombstone_Free_MRDT.lean`
prove convergence of the *state*. They say nothing about the sequence a user
actually reads. This file defines the canonical RGA read, the depth-first
forest traversal from the root sentinel `0`, siblings ordered newest-first,
and proves the intent-preservation theorems behind
`doc/why-the-path-matters.pdf`.

## The read

The state is an abstract map (`domain : ℕ → Bool`), so live identities are
not enumerable from the state alone. As with the operational oracle `dump`,
the read takes an explicit candidate list `ids`; the traversal is fueled
(`climb`-style), with fuel `max ids + 1`. Callers pass `ids` sorted
descending, which realises the RGA newest-sibling-first convention (the same
tiebreak as `RGA_CRDT`'s `opid_max`); the general theorems that need the
convention take sortedness as an explicit hypothesis, the rest are
order-agnostic in `ids`.

The honest caveat of the design note applies verbatim: adequacy of the fuel
rests on *id-monotone* anchors (`anc t < t`, the `mono` predicate below),
which holds under monotone timestamp allocation. Theorems that need it say
so.

## What is proved (general theorems, kernel-checked)

1. `document_sound`, **soundness**: the read shows only live identities (no
   ghosts). No hypotheses.
2. `mem_document_of_live` / `mem_document_iff`, **completeness / membership**:
   on `wf`+`mono` states with a covering candidate list, the read shows
   *exactly* the live set. Soundness + completeness are the tombstone-free
   membership headline: no tombstone read, no live element hidden.
3. `document_convergent` / `readText_convergent`, **convergence at the read**:
   states converged up to the framework's `eq` produce the same visible
   sequence (the read-side analogue of the merge-convergence VCs).
4. `del_not_in_document`: **delete erases its target** from the read (fully
   general, from soundness).
5. `del_document_mem`, **delete's read membership**: the survivor set of the
   read after `Del x` is exactly the old read minus `x`.

All the above are kernel-checked (axioms ⊆ [propext, Classical.choice,
Quot.sound]; several need only [propext]).

The **order**-level facts, that a leaf delete preserves survivor order, that
the fully general order-preservation claim is *false* (rehoming re-sorts a
deleted node's children among its siblings by timestamp, a genuine read-side
cost of tombstone-freedom the tombstoned RGA avoids by keeping a position
holder), and that a fresh insert lands immediately after its anchor, are
established as concrete executions in the companion
`RGA_Tombstone_Free_SPOT.lean`.
-/

namespace RGA_TF_Read

/-! ## The traversal -/

/-- Id-monotone anchors: every live record's anchor is strictly older.
Holds under monotone timestamp allocation; the same hypothesis the design
note's merge-convergence caveat rests on. -/
def mono (s : concrete_st) : Prop := ∀ t, contains s t = true → anc s t < t

/-- The live children of `p` among the candidate ids, in `ids` order
(callers pass `ids` sorted descending = newest sibling first). -/
def children (s : concrete_st) (ids : List ℕ) (p : ℕ) : List ℕ :=
  ids.filter (fun c => contains s c && anc s c == p)

/-- Fueled depth-first traversal: emit each child of `p`, then its subtree. -/
def docAux (s : concrete_st) (ids : List ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, p => (children s ids p).flatMap (fun c => c :: docAux s ids fuel c)

/-- Fuel adequate for any `mono` state whose ids are drawn from `ids`. -/
def fuelOf (ids : List ℕ) : ℕ := ids.foldr max 0 + 1

/-- **The read**: the visible sequence of identities, depth-first from the
root sentinel `0`, siblings in `ids` order (descending = newest first). -/
def document (s : concrete_st) (ids : List ℕ) : List ℕ :=
  docAux s ids (fuelOf ids) 0

/-- The visible text: the elements along the read. -/
def readText (s : concrete_st) (ids : List ℕ) : List ℕ :=
  (document s ids).map (el s)

theorem docAux_zero (s : concrete_st) (ids : List ℕ) (p : ℕ) :
    docAux s ids 0 p = [] := rfl

theorem docAux_succ (s : concrete_st) (ids : List ℕ) (f p : ℕ) :
    docAux s ids (f + 1) p
      = (children s ids p).flatMap (fun c => c :: docAux s ids f c) := rfl

theorem mem_children (s : concrete_st) (ids : List ℕ) (p c : ℕ) :
    c ∈ children s ids p
      ↔ (c ∈ ids ∧ contains s c = true ∧ anc s c = p) := by
  simp [children, List.mem_filter]

/-! ## List plumbing -/

theorem flatMap_congr {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h a (List.mem_cons_self ..),
        ih (fun b hb => h b (List.mem_cons.mpr (Or.inr hb)))]

theorem filter_flatMap {α β : Type} (l : List α) (g : α → List β) (p : β → Bool) :
    (l.flatMap g).filter p = l.flatMap (fun c => (g c).filter p) := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    rw [List.flatMap_cons, List.filter_append, ih, List.flatMap_cons]

theorem filter_eq_nil_of {α : Type} (p : α → Bool) (l : List α)
    (h : ∀ c ∈ l, p c = false) : l.filter p = [] := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    rw [List.filter_cons, h c (List.mem_cons_self ..), if_neg (by simp)]
    exact ih (fun d hd => h d (List.mem_cons.mpr (Or.inr hd)))

theorem filter_eq_self_of {α : Type} (p : α → Bool) (l : List α)
    (h : ∀ c ∈ l, p c = true) : l.filter p = l := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    rw [List.filter_cons, h c (List.mem_cons_self ..), if_pos (by simp),
        ih (fun d hd => h d (List.mem_cons.mpr (Or.inr hd)))]

theorem le_foldr_max (ids : List ℕ) : ∀ c ∈ ids, c ≤ ids.foldr max 0 := by
  induction ids with
  | nil => intro c h; cases h
  | cons d ds ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih c h) (le_max_right _ _)

theorem foldr_max_lt (t : ℕ) (ht : 0 < t) (ids : List ℕ)
    (h : ∀ c ∈ ids, c < t) : ids.foldr max 0 < t := by
  induction ids with
  | nil => exact ht
  | cons c cs ih =>
    have h1 : cs.foldr max 0 < t :=
      ih (fun d hd => h d (List.mem_cons.mpr (Or.inr hd)))
    have h2 : c < t := h c (List.mem_cons_self ..)
    exact max_lt h2 h1

/-! ## Soundness of the read: only live identities are shown -/

/-- Everything the read emits is a live identity from the candidate list.
This is the tombstone-free headline in its "no ghosts" direction: the read
cannot show a deleted (or never-inserted) element. No hypotheses at all. -/
theorem docAux_mem_sound (s : concrete_st) (ids : List ℕ) :
    ∀ f p c, c ∈ docAux s ids f p → contains s c = true ∧ c ∈ ids := by
  intro f
  induction f with
  | zero => intro p c h; rw [docAux_zero] at h; cases h
  | succ f ih =>
    intro p c h
    rw [docAux_succ] at h
    rcases List.mem_flatMap.mp h with ⟨d, hd, hc⟩
    obtain ⟨hdi, hdc, _⟩ := (mem_children s ids p d).mp hd
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact ⟨hdc, hdi⟩
    · exact ih d c hc'

theorem document_sound (s : concrete_st) (ids : List ℕ) (c : ℕ)
    (h : c ∈ document s ids) : contains s c = true ∧ c ∈ ids :=
  docAux_mem_sound s ids _ 0 c h

/-- **Delete erases its target from the read**: the tombstone-free
headline. Immediate from soundness: after `Del x` the identity `x` is not
live, so no traversal can show it. Fully general (any state, any path, any
candidate list). -/
theorem del_not_in_document (s : concrete_st) (t r x : ℕ)
    (pre ids : List ℕ) :
    x ∉ document (do_ s (t, r, app_op_t.Del pre x)) ids := by
  intro h
  have hc := (document_sound _ _ _ h).1
  rw [contains_doDel] at hc
  simp at hc

/-! ## Structure of the traversal on `mono` states -/

/-- On a `mono` state every element of a subtree is strictly newer than the
subtree's root. -/
theorem docAux_gt (s : concrete_st) (ids : List ℕ) (hmono : mono s) :
    ∀ f p c, c ∈ docAux s ids f p → p < c := by
  intro f
  induction f with
  | zero => intro p c h; rw [docAux_zero] at h; cases h
  | succ f ih =>
    intro p c h
    rw [docAux_succ] at h
    rcases List.mem_flatMap.mp h with ⟨d, hd, hc⟩
    obtain ⟨_, hdc, hda⟩ := (mem_children s ids p d).mp hd
    have hpd : p < d := hda ▸ hmono d hdc
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact hpd
    · exact lt_trans hpd (ih d c hc')

/-- Every emitted element's parent is either the traversal root or itself
emitted (the DFS never orphans). -/
theorem docAux_parent (s : concrete_st) (ids : List ℕ) :
    ∀ f p c, c ∈ docAux s ids f p →
      anc s c = p ∨ anc s c ∈ docAux s ids f p := by
  intro f
  induction f with
  | zero => intro p c h; rw [docAux_zero] at h; cases h
  | succ f ih =>
    intro p c h
    rw [docAux_succ] at h
    rcases List.mem_flatMap.mp h with ⟨d, hd, hc⟩
    obtain ⟨_, _, hda⟩ := (mem_children s ids p d).mp hd
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact Or.inl hda
    · rcases ih d c hc' with h1 | h1
      · refine Or.inr (List.mem_flatMap.mpr ⟨d, hd, ?_⟩)
        exact h1 ▸ List.mem_cons_self ..
      · exact Or.inr (List.mem_flatMap.mpr ⟨d, hd, List.mem_cons.mpr (Or.inr h1)⟩)

theorem children_nil_of_ge (s : concrete_st) (ids : List ℕ) (hmono : mono s)
    (B : ℕ) (hB : ∀ c ∈ ids, c ≤ B) (p : ℕ) (hp : B ≤ p) :
    children s ids p = [] := by
  cases h : children s ids p with
  | nil => rfl
  | cons c cs =>
    exfalso
    have hc : c ∈ children s ids p := h ▸ List.mem_cons_self ..
    obtain ⟨hci, hcc, hca⟩ := (mem_children s ids p c).mp hc
    have h1 : p < c := hca ▸ hmono c hcc
    have h2 : c ≤ B := hB c hci
    omega

/-- Fuel stability: on a `mono` state, any two adequate fuels produce the
same traversal. `B` bounds the candidate ids; fuel `f` is adequate at root
`p` when `B < f + p`. -/
theorem docAux_stable (s : concrete_st) (ids : List ℕ) (hmono : mono s)
    (B : ℕ) (hB : ∀ c ∈ ids, c ≤ B) :
    ∀ f₁ f₂ p, B < f₁ + p → B < f₂ + p →
      docAux s ids f₁ p = docAux s ids f₂ p := by
  intro f₁
  induction f₁ with
  | zero =>
    intro f₂ p h₁ h₂
    have hp : B ≤ p := by omega
    cases f₂ with
    | zero => rfl
    | succ g =>
      rw [docAux_zero, docAux_succ, children_nil_of_ge s ids hmono B hB p hp]
      rfl
  | succ f ih =>
    intro f₂ p h₁ h₂
    cases f₂ with
    | zero =>
      have hp : B ≤ p := by omega
      rw [docAux_zero, docAux_succ, children_nil_of_ge s ids hmono B hB p hp]
      rfl
    | succ g =>
      rw [docAux_succ, docAux_succ]
      apply flatMap_congr
      intro c hc
      obtain ⟨hci, hcc, hca⟩ := (mem_children s ids p c).mp hc
      have hpc : p < c := hca ▸ hmono c hcc
      have hcB : c ≤ B := hB c hci
      show c :: docAux s ids f c = c :: docAux s ids g c
      rw [ih g c (by omega) (by omega)]

/-! ## Convergence at the read -/

theorem children_congr_of_eq {s₁ s₂ : concrete_st} (h : eq s₁ s₂)
    (ids : List ℕ) (p : ℕ) : children s₁ ids p = children s₂ ids p := by
  unfold children
  apply List.filter_congr
  intro c _
  obtain ⟨hc, hs⟩ := h c
  by_cases h1 : contains s₁ c = true
  · have h2 : contains s₂ c = true := hc ▸ h1
    have hanc : anc s₁ c = anc s₂ c := congrArg Prod.snd (hs h1)
    simp only [h1, h2, hanc]
  · simp only [Bool.not_eq_true] at h1
    have h2 : contains s₂ c = false := hc ▸ h1
    simp only [h1, h2, Bool.false_and]

theorem docAux_congr_of_eq {s₁ s₂ : concrete_st} (h : eq s₁ s₂)
    (ids : List ℕ) : ∀ f p, docAux s₁ ids f p = docAux s₂ ids f p := by
  intro f
  induction f with
  | zero => intro p; rfl
  | succ f ih =>
    intro p
    rw [docAux_succ, docAux_succ, children_congr_of_eq h ids p]
    apply flatMap_congr
    intro c _
    show c :: docAux s₁ ids f c = c :: docAux s₂ ids f c
    rw [ih c]

/-- **Convergence at the read**: states converged up to the framework's
`eq` produce the *same* visible sequence. The read-side analogue of the
merge-convergence VCs. -/
theorem document_convergent {s₁ s₂ : concrete_st} (h : eq s₁ s₂)
    (ids : List ℕ) : document s₁ ids = document s₂ ids :=
  docAux_congr_of_eq h ids (fuelOf ids) 0

/-- Convergence of the visible *text* (elements, not just identities). -/
theorem readText_convergent {s₁ s₂ : concrete_st} (h : eq s₁ s₂)
    (ids : List ℕ) : readText s₁ ids = readText s₂ ids := by
  unfold readText
  rw [document_convergent h ids]
  apply List.map_congr_left
  intro c hc
  have hlive : contains s₂ c = true := (document_sound s₂ ids c hc).1
  obtain ⟨hcc, hcs⟩ := h c
  show (sel s₁ c).1 = (sel s₂ c).1
  rw [hcs (by rw [hcc]; exact hlive)]

/-! ## Completeness of the read: every live identity is shown

Soundness (`document_sound`) says the read shows nothing dead. Completeness
is the converse, the read misses nothing live. Together they are the
tombstone-free membership headline: the read is *exactly* the live set. It
needs `wf` (every live node's parent is live or the root), `mono` (anchors
strictly older, the design note's caveat), and a candidate list `ids` that
covers the live identities (callers pass the full id set). -/

/-- A live child from the candidate list sits at the head of its own block,
so it is emitted directly from its parent's traversal. -/
theorem mem_docAux_of_child (s : concrete_st) (ids : List ℕ) (hmono : mono s)
    (B : ℕ) (hB : ∀ c ∈ ids, c ≤ B) (f p c : ℕ) (hf : B < f + p)
    (hc : c ∈ children s ids p) : c ∈ docAux s ids f p := by
  cases f with
  | zero =>
    exfalso
    have hp : B ≤ p := by omega
    rw [children_nil_of_ge s ids hmono B hB p hp] at hc
    cases hc
  | succ f =>
    rw [docAux_succ]
    exact List.mem_flatMap.mpr ⟨c, hc, List.mem_cons_self ..⟩

/-- Nesting: once a node `p` is emitted, its whole subtree is too. On a
`mono` state with adequate fuel, every live child of an emitted `p` is
itself emitted (from the same traversal root `q`). -/
theorem docAux_nest (s : concrete_st) (ids : List ℕ) (hmono : mono s)
    (B : ℕ) (hB : ∀ c ∈ ids, c ≤ B) :
    ∀ f q p c, B < f + q → p ∈ docAux s ids f q → c ∈ children s ids p →
      c ∈ docAux s ids f q := by
  intro f
  induction f with
  | zero => intro q p c _ hp _; rw [docAux_zero] at hp; cases hp
  | succ f ih =>
    intro q p c hfq hp hc
    rw [docAux_succ] at hp ⊢
    rcases List.mem_flatMap.mp hp with ⟨d, hd, hpd⟩
    obtain ⟨hdi, hdc, hda⟩ := (mem_children s ids q d).mp hd
    have hqd : q < d := hda ▸ hmono d hdc
    have hfd : B < f + d := by omega
    refine List.mem_flatMap.mpr ⟨d, hd, ?_⟩
    rcases List.mem_cons.mp hpd with hpd' | hpd'
    · -- p = d: c is a live child of d, emitted in d's block
      have hcd : c ∈ children s ids d := hpd' ▸ hc
      have : c ∈ docAux s ids f d := mem_docAux_of_child s ids hmono B hB f d c hfd hcd
      exact List.mem_cons.mpr (Or.inr this)
    · -- p deeper in d's subtree: recurse
      have : c ∈ docAux s ids f d := ih d p c hfd hpd' hc
      exact List.mem_cons.mpr (Or.inr this)

/-- **Completeness of the read**: on a `wf`, `mono` state with a covering
candidate list, every live identity appears in the read. With
`document_sound`, the read is exactly the live set, no tombstones, and no
live element hidden. -/
theorem mem_document_of_live (s : concrete_st) (ids : List ℕ)
    (hmono : mono s) (hwf : wf s)
    (hids : ∀ t, contains s t = true → t ∈ ids) :
    ∀ c, contains s c = true → c ∈ document s ids := by
  have hB : ∀ c ∈ ids, c ≤ ids.foldr max 0 := le_foldr_max ids
  set B := ids.foldr max 0 with hBdef
  have hfuel : fuelOf ids = B + 1 := rfl
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro hc
    have hcid : c ∈ ids := hids c hc
    have hchild : c ∈ children s ids (anc s c) :=
      (mem_children s ids (anc s c) c).mpr ⟨hcid, hc, rfl⟩
    unfold document
    rcases hwf c hc with h0 | hplive
    · -- parent is the root: c is a root child
      rw [h0] at hchild
      exact mem_docAux_of_child s ids hmono B hB (fuelOf ids) 0 c (by omega) hchild
    · -- parent live and strictly older: emitted by IH, then nest c into it
      have hplt : anc s c < c := hmono c hc
      have hpdoc : anc s c ∈ docAux s ids (fuelOf ids) 0 := ih (anc s c) hplt hplive
      exact docAux_nest s ids hmono B hB (fuelOf ids) 0 (anc s c) c (by omega)
        hpdoc hchild

/-- **The read is exactly the live set** (both directions), on `wf`+`mono`
states with a covering candidate list. -/
theorem mem_document_iff (s : concrete_st) (ids : List ℕ)
    (hmono : mono s) (hwf : wf s)
    (hids : ∀ t, contains s t = true → t ∈ ids) (c : ℕ) :
    c ∈ document s ids ↔ contains s c = true :=
  ⟨fun h => (document_sound s ids c h).1, mem_document_of_live s ids hmono hwf hids c⟩

/-! ## Delete at the read (membership) -/

/-- **Delete removes exactly its target from the read's membership**: the
survivor set of the read after `Del x` is the old survivor set minus `x`.
Fully general on `wf`+`mono` states with a covering candidate list (the
covering `ids` for the post-delete state is inherited: deletion only shrinks
the live set). -/
theorem del_document_mem (s : concrete_st) (t r x : ℕ) (pre ids : List ℕ)
    (hmono : mono (do_ s (t, r, .Del pre x)))
    (hwf : wf (do_ s (t, r, .Del pre x)))
    (hids : ∀ k, contains (do_ s (t, r, .Del pre x)) k = true → k ∈ ids)
    (c : ℕ) :
    c ∈ document (do_ s (t, r, .Del pre x)) ids
      ↔ (c ∈ ids ∧ contains s c = true ∧ c ≠ x) := by
  rw [mem_document_iff _ ids hmono hwf hids c, contains_doDel]
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨hids c (by rw [contains_doDel, h1, Bool.true_and]; exact bne_iff_ne.mpr h2), h1, h2⟩
  · rintro ⟨_, h2, h3⟩; exact ⟨h2, h3⟩

end RGA_TF_Read

section AxiomAudit
open RGA_TF_Read
#print axioms document_sound
#print axioms del_not_in_document
#print axioms document_convergent
#print axioms mem_document_of_live
#print axioms del_document_mem
end AxiomAudit
