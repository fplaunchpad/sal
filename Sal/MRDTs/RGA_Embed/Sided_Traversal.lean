import Sal.MRDTs.RGA_Embed.Sided_ChainLex

/-!
# The sided traversal theory, interval form

The display order of the sided kernel IS the depth-first in-order
traversal of the origin tree implicit in the chains: L-subtrees, node,
R-subtrees, siblings by `sEntryBefore`. The marker theorem
(`sdisplay_iff_schainBefore`) already identifies display with the chain
order; this file adds the INTERVAL lemmas that make the traversal reading
usable: which side of a node an extension falls on
(`schain_ext_after_is_R`, `schain_ext_before_is_L`, packaged as
`schain_ext_side`), shared-prefix strip and lift
(`schainBefore_append_strip` / `_lift`), and transitivity on positive
chains (`schainBefore_trans`). Together with the kernel's
`schain_subtree_convex` these say: the subtree of a prefix `p` is a
contiguous display interval, split by the node into an L-headed left part
and an R-headed right part.

A recursive traversal EMISSION function was designed and deliberately not
built here: every Lean consumer (the non-interleaving discharges in
`MRDT_Instances/SidedRGA/SidedRGA_NonInterleaving.lean`) needs only the
interval form, and the executable statement traversal(state) = display is
machine-checked in `whiteboard/litmus/traversal_check.py` (12 directed
cases, 1800 randomized states, both kernels, all clean). Design:
`whiteboard/fugue-maximal-noninterleaving.md` section 9.
-/

namespace Sal.EmbedRGA

set_option linter.unusedVariables false

/-! ## Shared-prefix strip and lift -/

theorem schainBefore_append_lift : ∀ (p : SChain) {u v : SChain},
    schainBefore u v → schainBefore (p ++ u) (p ++ v)
  | [], _, _, h => h
  | x :: p', u, v, h =>
      schainBefore_cons x (schainBefore_append_lift p' h)

theorem schainBefore_append_strip : ∀ (p : SChain) {u v : SChain},
    schainBefore (p ++ u) (p ++ v) → schainBefore u v
  | [], _, _, h => h
  | x :: p', u, v, h =>
      schainBefore_append_strip p' (schainBefore_cons_strip h)

/-! ## The side of an extension -/

/-- A subtree member strictly after the node extends it on the R side. -/
theorem schain_ext_after_is_R {p ext : SChain}
    (h : schainBefore p (p ++ ext)) :
    ∃ d rest, ext = (Side.R, d) :: rest := by
  rcases schainBefore_inv h with ⟨d, rest, heq⟩ | ⟨d, rest, heq⟩ |
    ⟨q, e1, e2, t1, t2, hlt, h1, h2⟩
  · exfalso
    have := congrArg List.length heq
    simp at this
  · exact ⟨d, rest, List.append_cancel_left heq⟩
  · exfalso
    rw [h1, List.append_assoc] at h2
    have h3 := List.append_cancel_left h2
    injection h3 with h4 h5
    subst h4
    exact sEntryBefore_irrefl e1 hlt

/-- A subtree member strictly before the node extends it on the L side. -/
theorem schain_ext_before_is_L {p ext : SChain}
    (h : schainBefore (p ++ ext) p) :
    ∃ d rest, ext = (Side.L, d) :: rest := by
  rcases schainBefore_inv h with ⟨d, rest, heq⟩ | ⟨d, rest, heq⟩ |
    ⟨q, e1, e2, t1, t2, hlt, h1, h2⟩
  · exact ⟨d, rest, List.append_cancel_left heq⟩
  · exfalso
    have := congrArg List.length heq
    simp at this
  · exfalso
    rw [h2, List.append_assoc] at h1
    have h3 := List.append_cancel_left h1
    injection h3 with h4 h5
    subst h4
    exact sEntryBefore_irrefl _ hlt

/-- **The interval split**: a nonempty extension of `p` displays before
the node iff it is L-headed and after iff it is R-headed. With
`schain_subtree_convex` this is the traversal theorem in interval form:
the subtree of `p` is the contiguous display interval [L-part, node,
R-part]. -/
theorem schain_ext_side (p : SChain) {ext : SChain} (hne : ext ≠ []) :
    (schainBefore (p ++ ext) p ↔ ∃ d rest, ext = (Side.L, d) :: rest) ∧
    (schainBefore p (p ++ ext) ↔ ∃ d rest, ext = (Side.R, d) :: rest) := by
  constructor
  · constructor
    · exact schain_ext_before_is_L
    · rintro ⟨d, rest, rfl⟩
      exact schainBefore.extL p d rest
  · constructor
    · exact schain_ext_after_is_R
    · rintro ⟨d, rest, rfl⟩
      exact schainBefore.extR p d rest

/-! ## Transitivity on positive chains -/

/-- The chain order is transitive on positive chains, via the marker
theorem: the display comparison is lexicographic, hence transitive, and
the marker theorem transports it back. -/
theorem schainBefore_trans {c1 c2 c3 : SChain}
    (h1 : PosSChain c1) (h2 : PosSChain c2) (h3 : PosSChain c3)
    (hb1 : schainBefore c1 c2) (hb2 : schainBefore c2 c3) :
    schainBefore c1 c3 := by
  have k1 := schainBefore_display unaryCode h1 h2 hb1
  have k2 := schainBefore_display unaryCode h2 h3 hb2
  have k13 := keyLt_trans k2 k1
  have hne : c1 ≠ c3 := by
    rintro rfl
    rw [keyLt_irrefl] at k13
    exact Bool.noConfusion k13
  exact (sdisplay_iff_schainBefore unaryCode h1 h3 hne).mp k13

/-! ## Cross-validation (Python twin: traversal_check.py, directed rows)

At the anchor `[(R,1)]` (element 1 of the L19 family): the L-child
displays before the node, the node before its R-child; the deeper
L-subtree stays inside the interval. -/

example : keyLt (sKey (sidedCoordOf unaryCode [(Side.R, 1)]))
    (sKey (sidedCoordOf unaryCode [(Side.R, 1), (Side.L, 9)])) = true := by
  decide
example : keyLt (sKey (sidedCoordOf unaryCode [(Side.R, 1), (Side.R, 9)]))
    (sKey (sidedCoordOf unaryCode [(Side.R, 1)])) = true := by decide
/-- FAIL pin: the R-child does NOT display before the node. -/
example : ¬ (keyLt (sKey (sidedCoordOf unaryCode [(Side.R, 1)]))
    (sKey (sidedCoordOf unaryCode [(Side.R, 1), (Side.R, 9)])) = true) := by
  decide

#print axioms schainBefore_append_strip
#print axioms schain_ext_side
#print axioms schainBefore_trans

end Sal.EmbedRGA
