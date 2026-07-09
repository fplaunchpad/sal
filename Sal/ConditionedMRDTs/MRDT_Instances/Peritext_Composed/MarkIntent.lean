import Sal.ConditionedMRDTs.MRDT_Instances.Peritext_Composed.MarkHonesty

/-!
# Peritext gap 2 — what the frozen-path read actually guarantees (and does not)

Gap 1 (`MarkHonesty.lean`) showed mark-anchor honesty *composes* but is
decorative for the linearizability capstone — any payoff must be on the read
layer. This file states, honestly, what the frozen-path resolution buys and —
importantly — what it does **not**: it is **not** the paper's positional
semantics, and it does **not** prevent formatting from leaking under deletion.

**The correction (read this first).** The Peritext promise (Litt et al.,
CSCW 2022) is that formatting stays put: deleting an anchored character does
not move a mark boundary, because the paper's sequence keeps that character as
a **tombstone** at its exact position. Our sequence is tombstone-free — the
deleted character's position is destroyed — so we recover a boundary by
climbing its frozen recorded path with the RGA's `resolve`, which climbs
**tree ancestry**. Tree ancestry is *not* document position: an ancestor sits
*earlier* in the reading order (a parent precedes its children in the DFS),
and climbing can skip surviving siblings. So under deletion of its anchor a
boundary **migrates backward in the document** — formatting extends to text
that was never in the span. That is a genuine leak, not staleness, and it
means the frozen-path design does **not** match the paper's positional
semantics. (An earlier version of this file named the theorems below
`mark_*_no_leak` and the note claimed a "formatting does not leak" guarantee;
both overclaimed and are corrected here.)

What the theorems below *do* establish is weaker and honest:

* **Containment, not stasis** (`mark_start_within_recorded_ancestry` /
  `_end_`): under accuracy the resolved endpoint is the document root, the
  anchored character, or one of its *issue-time ancestors*. So the boundary
  can drift, but only **along its own recorded ancestor chain** — it cannot
  jump to unrelated text. This *bounds* the leak (no wild drift); it does not
  *prevent* it (backward drift within the chain is exactly what happens when
  the anchor dies).
* **Structural containment** (`mark_start_in_recorded` / `_end_`): with no
  hypotheses at all, resolution returns the root or a member of the recorded
  chain — never an outside character.
* **Surviving endpoint** (`mark_start_live` / `mark_end_live`): a non-root
  resolved endpoint is live at read time — the mark attaches to a surviving
  character, not a ghost.
* **Faithful at issue** (`markAccurate_resolveMark`, `MarkHonesty.lean`):
  before any deletion the mark renders to its exact recorded endpoints.

The one genuine intent guarantee — that a mark's span is exactly the surviving
image of its original span, with no backward leak — is **not proved here and
does not hold for the frozen-path design**. It needs document-order rehoming
(the boundary moving to its nearest surviving *neighbour in reading order*,
gravity-respecting), which is what the *fused* boundary-node design provides
via the RGA's own live rehoming — at the cost of atomicity (the trilemma).
This is recorded as the remaining Peritext read-model work.

(The containment facts are purely structural — `resolve` returns a live member
of its candidate list or the root, `resolve_eq_zero_or_mem` /
`resolve_live_of_ne_zero` — so they hold at every read state with no
reachability invariant. It is precisely the *positional correctness* the
structure cannot supply.)
-/

set_option maxHeartbeats 400000

open Classical

namespace Sal.ConditionedMRDTs.Peritext_Composed

/-! ## §1  `resolve` returns a live candidate, or the root -/

/-- The defining `cons` equation of `resolve` (definitional). -/
theorem resolve_cons_eq (σ : concrete_st) (c : ℕ) (rest : List ℕ) :
    resolve σ (c :: rest) = if contains σ c = true then c else resolve σ rest := rfl

/-- Path resolution returns the document root or a member of its candidate
list — never an outside character. Structural (no accuracy, no reachability). -/
theorem resolve_eq_zero_or_mem (σ : concrete_st) :
    ∀ cands : List ℕ, resolve σ cands = 0 ∨ resolve σ cands ∈ cands := by
  intro cands
  induction cands with
  | nil => exact Or.inl rfl
  | cons c rest ih =>
    rw [resolve_cons_eq]
    by_cases hc : contains σ c = true
    · rw [if_pos hc]; exact Or.inr (List.mem_cons_self ..)
    · rw [if_neg hc]; exact ih.imp id (List.mem_cons_of_mem _)

/-- A non-root resolved endpoint is live at the state it was resolved against —
the resolved character survives. Structural. -/
theorem resolve_live_of_ne_zero (σ : concrete_st) :
    ∀ cands : List ℕ, resolve σ cands ≠ 0 → contains σ (resolve σ cands) = true := by
  intro cands
  induction cands with
  | nil => intro h; exact absurd rfl h
  | cons c rest ih =>
    intro h
    rw [resolve_cons_eq] at h ⊢
    by_cases hc : contains σ c = true
    · rw [if_pos hc]; exact hc
    · rw [if_neg hc]; rw [if_neg hc] at h; exact ih h

/-! ## §2  Structural containment: a rendered endpoint stays in its recorded chain

`resolveMark σ m` = `(markId, markType, resolvedStart, resolvedEnd)`, with the
resolved start/end obtained by `resolve` on the recorded chains
`startChar :: startPath` and `endChar :: endPath`. -/

/-- The recorded start chain of a mark: its start character id followed by its
recorded start path. Immutable data. -/
def startChain (m : MarkPayload) : List ℕ := m.2.2.1.1 :: m.2.2.1.2

/-- The recorded end chain of a mark. -/
def endChain (m : MarkPayload) : List ℕ := m.2.2.2.1 :: m.2.2.2.2

/-- **Containment (start)**: at any read state, the rendered start endpoint is
the document root or a member of the recorded start chain — resolution cannot
escape to an outside character. (Bounds where the boundary can land; says
nothing about whether it moved.) -/
theorem mark_start_in_recorded (σ : concrete_st) (m : MarkPayload) :
    (resolveMark σ m).2.2.1 = 0 ∨ (resolveMark σ m).2.2.1 ∈ startChain m := by
  show resolve σ (startChain m) = 0 ∨ resolve σ (startChain m) ∈ startChain m
  exact resolve_eq_zero_or_mem σ (startChain m)

/-- **Containment (end)**. -/
theorem mark_end_in_recorded (σ : concrete_st) (m : MarkPayload) :
    (resolveMark σ m).2.2.2 = 0 ∨ (resolveMark σ m).2.2.2 ∈ endChain m := by
  show resolve σ (endChain m) = 0 ∨ resolve σ (endChain m) ∈ endChain m
  exact resolve_eq_zero_or_mem σ (endChain m)

/-- **Surviving endpoint (start)**: a non-root rendered start is live at read
time — the mark attaches to a surviving character. -/
theorem mark_start_live (σ : concrete_st) (m : MarkPayload)
    (h : (resolveMark σ m).2.2.1 ≠ 0) :
    contains σ (resolveMark σ m).2.2.1 = true :=
  resolve_live_of_ne_zero σ (startChain m) h

/-- **Surviving endpoint (end)**. -/
theorem mark_end_live (σ : concrete_st) (m : MarkPayload)
    (h : (resolveMark σ m).2.2.2 ≠ 0) :
    contains σ (resolveMark σ m).2.2.2 = true :=
  resolve_live_of_ne_zero σ (endChain m) h

/-! ## §3  Under accuracy, the chain is genuine issue-time ancestry

Under `MarkAccurate` at the issue state, the recorded chains ARE the true
ancestor chains of the endpoint characters. So the resolved endpoint is the
document root, the anchored character itself, or one of its genuine issue-time
ancestors. This bounds the boundary's drift to its own ancestry — it cannot
reach unrelated text — but note an ancestor is *earlier in document order*, so
this is exactly the statement that under deletion the boundary drifts
**backward** (a leak), confined to the recorded chain. Containment, not
stasis. -/

/-- Every member of an accurate chain is `anc`-reachable from the leaf at the
issue state: the head is the leaf, and each tail member is the parent of the
previous. So chain membership is ancestry. -/
theorem isAncPath_mem_is_ancestor {σ₀ : concrete_st} :
    ∀ (leaf : ℕ) (path : List ℕ), IsAncPath σ₀ leaf path →
      ∀ x ∈ path, contains σ₀ x = true := by
  intro leaf path
  induction path generalizing leaf with
  | nil => intro _ x hx; cases hx
  | cons p ps ih =>
    intro hchain x hx
    obtain ⟨_, hpl, hrest⟩ := hchain
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hpl
    · exact ih p hrest x hx'

/-- **Drift is confined to the issue-time ancestry (start)**: under
mark-anchor accuracy, the rendered start endpoint is the root, the anchored
start character, or one of its genuine ancestors at the issue state. This is a
*containment* bound — the boundary cannot drift to unrelated text — NOT a
no-leak guarantee: an ancestor is earlier in reading order, so this is
precisely where the boundary migrates backward when the anchor is deleted. -/
theorem mark_start_within_recorded_ancestry {σ₀ σ' : concrete_st} {m : MarkPayload}
    (hacc : MarkAccurate σ₀ m) :
    (resolveMark σ' m).2.2.1 = 0 ∨
    (resolveMark σ' m).2.2.1 = m.2.2.1.1 ∨
    (contains σ₀ (resolveMark σ' m).2.2.1 = true ∧
     (resolveMark σ' m).2.2.1 ∈ m.2.2.1.2) := by
  rcases mark_start_in_recorded σ' m with h0 | hmem
  · exact Or.inl h0
  · rcases List.mem_cons.mp hmem with hhead | htail
    · exact Or.inr (Or.inl hhead)
    · refine Or.inr (Or.inr ⟨?_, htail⟩)
      rcases hacc.1 with ⟨_, hpnil⟩ | ⟨_, hpath⟩
      · rw [hpnil] at htail; cases htail
      · exact isAncPath_mem_is_ancestor m.2.2.1.1 m.2.2.1.2 hpath _ htail

/-- **Drift is confined to the issue-time ancestry (end)**. -/
theorem mark_end_within_recorded_ancestry {σ₀ σ' : concrete_st} {m : MarkPayload}
    (hacc : MarkAccurate σ₀ m) :
    (resolveMark σ' m).2.2.2 = 0 ∨
    (resolveMark σ' m).2.2.2 = m.2.2.2.1 ∨
    (contains σ₀ (resolveMark σ' m).2.2.2 = true ∧
     (resolveMark σ' m).2.2.2 ∈ m.2.2.2.2) := by
  rcases mark_end_in_recorded σ' m with h0 | hmem
  · exact Or.inl h0
  · rcases List.mem_cons.mp hmem with hhead | htail
    · exact Or.inr (Or.inl hhead)
    · refine Or.inr (Or.inr ⟨?_, htail⟩)
      rcases hacc.2 with ⟨_, hpnil⟩ | ⟨_, hpath⟩
      · rw [hpnil] at htail; cases htail
      · exact isAncPath_mem_is_ancestor m.2.2.2.1 m.2.2.2.2 hpath _ htail

/-! ## §4  What remains: recorded chain stays ancestral at read time

`mark_*_within_recorded_ancestry` only *bounds* the resolved endpoint by the
issue-time ancestry; it does not give the intended positional guarantee. The
guarantee the paper has — the mark's span is exactly the surviving image of
its original span, no backward leak — requires **document-order** rehoming:
the boundary moving to its nearest surviving *neighbour in reading order*
(gravity-respecting), not to a tree ancestor. The RGA's `resolve` climbs tree
ancestry, which is the wrong notion, so no strengthening of the theorems above
recovers it for the frozen-path design. The fused boundary-node design gets it
(boundaries are RGA nodes, rehomed to preserve reading order) — modulo the
`del_can_reorder_survivors` caveat proved for characters — at the cost of
atomicity. Providing a genuine document-order intent spec, against which the
frozen-path leak would be *visible as a failure*, is the remaining
Peritext-specific work. -/

#print axioms mark_start_within_recorded_ancestry
#print axioms mark_end_within_recorded_ancestry
#print axioms mark_start_live

end Sal.ConditionedMRDTs.Peritext_Composed
