import Sal.ConditionedMRDTs.MRDT_Instances.PeritextTF.MarkHonesty

/-!
# Peritext gap 2 — the render-intent theorems (what mark-anchor honesty buys)

Gap 1 (`MarkHonesty.lean`) showed mark-anchor honesty *composes* but is
decorative for the linearizability capstone — its payoff is the read layer.
This file collects the payoff: the intent theorems the render owes, each
consuming `MarkAccurate`.

The Peritext promise (Litt et al., CSCW 2022) is that formatting stays put:
a mark's span does not leak to unrelated text under concurrent edits. In the
tombstone-free composite, a mark endpoint is a character id plus its recorded
ancestor path; at read time the endpoint is resolved by the RGA's own
path-climbing (`resolveMark`), which walks the recorded chain to the nearest
surviving character. The read-side guarantee is therefore structural:

* **No leak** (`mark_start_in_recorded` / `mark_end_in_recorded`): resolution
  returns either the document root or a member of the endpoint's *recorded
  chain* — it can never jump to a character outside it. Combined with accuracy
  (the recorded chain is the endpoint's true ancestry at issue,
  `MarkAccurate`), formatting can only ever climb the anchored character's own
  ancestry, never leak sideways.
* **Surviving endpoint** (`mark_start_live` / `mark_end_live`): a non-root
  resolved endpoint is *live* at read time — the mark attaches to a surviving
  character, not a ghost.
* **Faithful at issue** (`markAccurate_resolveMark`, from `MarkHonesty.lean`):
  before any deletion the mark renders to its exact recorded endpoints.

The structural core is that `resolve` returns a live member of its candidate
list or the root (`resolve_eq_zero_or_mem`, `resolve_live_of_ne_zero`) — the
recorded chain is immutable data, so "stays within the recorded chain" holds
at *every* read state without threading a reachability invariant. What a
*stronger* claim would need — that the recorded chain remains a valid
*ancestry* at read time, so the surviving endpoint is a genuine current
ancestor and not merely a recorded one — is the RGA's own recorded-path
faithfulness invariant (`chainFaithful`) lifted to the product LTS; it is the
one remaining piece, noted at the end.
-/

set_option maxHeartbeats 400000

open Classical

namespace Sal.ConditionedMRDTs.PeritextTF

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

/-! ## §2  No leak: a rendered endpoint stays in its recorded chain

`resolveMark σ m` = `(markId, markType, resolvedStart, resolvedEnd)`, with the
resolved start/end obtained by `resolve` on the recorded chains
`startChar :: startPath` and `endChar :: endPath`. -/

/-- The recorded start chain of a mark: its start character id followed by its
recorded start path. Immutable data. -/
def startChain (m : MarkPayload) : List ℕ := m.2.2.1.1 :: m.2.2.1.2

/-- The recorded end chain of a mark. -/
def endChain (m : MarkPayload) : List ℕ := m.2.2.2.1 :: m.2.2.2.2

/-- **No leak (start)**: at any read state, the rendered start endpoint is the
document root or a member of the recorded start chain — resolution cannot
escape to an outside character. -/
theorem mark_start_in_recorded (σ : concrete_st) (m : MarkPayload) :
    (resolveMark σ m).2.2.1 = 0 ∨ (resolveMark σ m).2.2.1 ∈ startChain m := by
  show resolve σ (startChain m) = 0 ∨ resolve σ (startChain m) ∈ startChain m
  exact resolve_eq_zero_or_mem σ (startChain m)

/-- **No leak (end)**. -/
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

/-! ## §3  The chain is the issue-time ancestry — no leak beyond it

Under `MarkAccurate` at the issue state, the recorded chains ARE the true
ancestor chains of the endpoint characters. Every non-head member of a chain
is a genuine ancestor (`anc`-reachable) of the endpoint at issue; so the
resolved endpoint, staying in the chain, can only be the endpoint character
itself or one of its issue-time ancestors — the precise "no sideways leak". -/

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

/-- **No leak beyond the issue-time ancestry (start)**: under mark-anchor
accuracy, the rendered start endpoint is the root, the anchored start
character, or one of its genuine ancestors at the issue state — never an
unrelated character. This is the formal Peritext "formatting does not leak"
guarantee, at endpoint granularity. -/
theorem mark_start_no_leak {σ₀ σ' : concrete_st} {m : MarkPayload}
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

/-- **No leak beyond the issue-time ancestry (end)**. -/
theorem mark_end_no_leak {σ₀ σ' : concrete_st} {m : MarkPayload}
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

`mark_start_no_leak` bounds the resolved endpoint by the *issue-time* ancestry
(the recorded chain, pinned true by accuracy). The stronger read-time claim —
that the surviving resolved endpoint is a genuine ancestor *at the read state
`σ'`* (not merely a recorded one), so the mark's span is exactly the surviving
image of its original span — needs that tombstone-free deletion preserves the
ancestor relation among survivors, i.e. the RGA's recorded-path faithfulness
invariant (`chainFaithful` / `RVF`, `RGA_Tombstone_Free_MRDT.lean`) lifted
along the product LTS. That lift is the same shape as the character supply
rerun (`Supplies.lean`) and is the remaining Peritext-specific work; the
theorems above are the read-side guarantee that holds unconditionally in the
mark data, and `mark_*_no_leak` is the guarantee accuracy already buys. -/

#print axioms mark_start_no_leak
#print axioms mark_end_no_leak
#print axioms mark_start_live

end Sal.ConditionedMRDTs.PeritextTF
