import Sal.MRDTs.Metatheory.Development.RGA_BirthBridge_Bundle

/-!
# Splitting the recorded chain at the birth anchor

*Additive; modifies no existing file; 0 `sorry`.*

The list-surgery foundation for the `hRc` producer (#39, case B). The birth anchor
`bw = anc(branch) k = resolve(branch)(a::p)` is the FIRST branch-live entry of the recorded chain
`a::p`. `split_at_firstLive` turns that into the split `a::p = rcPre ++ bw :: rcSuf` with `rcPre` the
branch-dead prefix, and — crucially — `liveSub s (a::p) = bw :: liveSub s rcSuf`, so `bw` is the head
of the branch `LiveChain`'s live sublist and `liveSub s rcSuf` is exactly `bw`'s branch-forest tail.
Branch-agnostic; case B-i instantiates it at `s := σ₀'` (no `BranchInv`), case B-ii at `s := σ₁'/σ₂'`
(the σ→σ₀' transport is `BranchInv`, kept separate).
-/

set_option maxHeartbeats 1000000

open Classical

namespace Sal.Metatheory.RGABirthBridgeSplit

open Sal.Emulation

/-- **Split at the first live entry.**  If `resolve s L ≠ 0` (there is a live entry), `L` splits at it:
`L = rcPre ++ resolve s L :: rcSuf` with `rcPre` all-dead, and the live sublist factors as
`liveSub s L = resolve s L :: liveSub s rcSuf`. -/
theorem split_at_firstLive (s : concrete_st) :
    ∀ (L : List ℕ), resolve s L ≠ 0 →
    ∃ rcPre rcSuf : List ℕ, L = rcPre ++ resolve s L :: rcSuf
      ∧ (∀ c ∈ rcPre, contains s c = false)
      ∧ liveSub s L = resolve s L :: liveSub s rcSuf := by
  intro L
  induction L with
  | nil => intro h; exact (h rfl).elim
  | cons c cs ih =>
    intro h
    by_cases hc : contains s c = true
    · have hr : resolve s (c :: cs) = c := if_pos hc
      refine ⟨[], cs, ?_, ?_, ?_⟩
      · rw [hr, List.nil_append]
      · intro c' hc'; simp at hc'
      · rw [hr]
        show liveSub s (c :: cs) = c :: liveSub s cs
        simp only [liveSub]
        exact List.filter_cons_of_pos hc
    · have hcf : contains s c = false := by
        cases h' : contains s c with
        | true => exact absurd h' hc
        | false => rfl
      have hres : resolve s (c :: cs) = resolve s cs := if_neg hc
      obtain ⟨rcPre, rcSuf, hsp, hpd, hls⟩ := ih (hres ▸ h)
      refine ⟨c :: rcPre, rcSuf, ?_, ?_, ?_⟩
      · rw [hres, List.cons_append, ← hsp]
      · intro c' hc'
        rcases List.mem_cons.mp hc' with h1 | h1
        · rw [h1]; exact hcf
        · exact hpd c' h1
      · rw [hres]
        show liveSub s (c :: cs) = resolve s cs :: liveSub s rcSuf
        rw [show liveSub s (c :: cs) = liveSub s cs from by
          simp only [liveSub]; exact List.filter_cons_of_neg hc]
        exact hls

#print axioms split_at_firstLive

/-- **Split a `LiveChain` at its birth anchor.**  From the branch `LiveChain s k (a::p)` (carried by
`CanonInv`) and `anc s k ≠ 0`, split the recorded chain at `bw = anc s k = resolve s (a::p)` and read
off `bw`'s forest tail: `a::p = rcPre ++ bw :: rcSuf` with `rcPre` all `s`-dead and — the carrier —
`IsAncPath s bw (liveSub s rcSuf)` (the tail of the `LiveChain`'s `IsAncPath`). Branch-agnostic:
case B-i uses it at `s := σ₀'` (this `IsAncPath` IS `hlive`, no `BranchInv`); case B-ii at `s := σ₁'/σ₂'`
(the σ→σ₀' transport of this `IsAncPath` is `BranchInv`). -/
theorem split_liveChain (s : concrete_st) (k a : ℕ) (p : List ℕ)
    (hlc : LiveChain s k (a :: p)) (hbw : anc s k ≠ 0) :
    ∃ rcPre rcSuf : List ℕ,
      (a :: p) = rcPre ++ anc s k :: rcSuf
      ∧ (∀ c ∈ rcPre, contains s c = false)
      ∧ IsAncPath s (anc s k) (liveSub s rcSuf) := by
  have hres : resolve s (a :: p) = anc s k := liveChain_resolve s k (a :: p) hlc
  have hne : resolve s (a :: p) ≠ 0 := by rw [hres]; exact hbw
  obtain ⟨rcPre, rcSuf, hsp, hpd, hls⟩ := split_at_firstLive s (a :: p) hne
  rw [hres] at hsp hls
  refine ⟨rcPre, rcSuf, hsp, hpd, ?_⟩
  obtain ⟨_, _, hpath⟩ := hlc
  rw [hls] at hpath
  obtain ⟨-, -, h3⟩ := hpath
  exact h3

#print axioms split_liveChain

end Sal.Metatheory.RGABirthBridgeSplit
