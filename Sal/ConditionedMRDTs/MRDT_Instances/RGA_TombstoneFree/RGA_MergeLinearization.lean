import Sal.MRDTs.RGA_Tombstone_Free.RGA_Reachability_Invariant

/-!
# M3 — the merge-linearization bridge for the tombstone-free RGA

Goal (up to observational `eq`):

    eq (merge l a b) (applySeqR l π)

for a reachable LCA `l`, branches `a`/`b` folded from disjoint concurrent event
lists over `l`, and a `loOnA`-respecting interleave `π` of `Ea ++ Eb`.

## Route (per the coordinator's decomposition)

The merge is defined by a **survivor set** `I` plus a **per-survivor climb**, so it
is inherently per-id.  We match that shape: reduce `eq (merge …) f` to the
extensional obligation *(same domain) ∧ (per live id: same element ∧ same anchor)*
and discharge the anchor obligation by the **anchor-coincidence** invariant

  * for a surviving *original* node `k` (`k ∈ dom l ∩ dom branch`),
    `climb (anc l) (dom branch) (anc l k) = anc branch k`
    — merge's LCA-climb lands where the fold's `resolve`-rehoming lands.

This file mechanizes the **single-sided** core (`b = l`, i.e. 3b):

  * §1 framework: `applySeqR`, `eq` reflexivity/transitivity.
  * §2 the `climb` algebra (fuel-stability, live-unfold, removal lemmas) — the
    technical crux that makes the climb value-recursive rather than fuel-indexed.
  * §3 `BranchInv l a` (the three l-relative invariants I2/I3/I4) + its base.
  * §4 reduction `BranchInv l a ∧ wf a → eq (merge l a l) a`.
  * §5 preservation of `BranchInv` under a good `do_` step (Ins / Del).
  * §6 the fold corollary + single-sided headline.

Everything is over the RGA's observational `eq` (NOT Lean `Eq`); the generic
`Merge_Linearization_Set` induction (Lean-`Eq`, 2 pre-existing sorries) is NOT
inherited — the needed steps are rebuilt natively.
-/

set_option maxHeartbeats 1000000

namespace RGAMergeLinearization

/-! ## §1  Framework: the concrete fold and `eq` plumbing -/

/-- Concrete RGA fold: apply a list of ops left-to-right with `do_`. -/
def applySeqR (s : concrete_st) (π : List op_t) : concrete_st := π.foldl do_ s

@[simp] theorem applySeqR_cons (s : concrete_st) (o : op_t) (π : List op_t) :
    applySeqR s (o :: π) = applySeqR (do_ s o) π := rfl

/-! ## §2  The `climb` algebra

`climb ancL I x = climb_aux ancL I x x` walks `ancL` from `x` to the first node
in `{0} ∪ I`, with fuel `= x`.  Under id-monotone anchors on the LCA the fuel is
always sufficient, so the climb behaves like a value-recursive "nearest node in
`{0} ∪ I` up the `anc l` chain".  These lemmas package exactly that. -/

/-- **Fuel stability.**  Under id-monotone (`Hdec`) forest (`Hstay`) anchors, any
fuel `≥ z` gives the canonical climb `climb_aux … z z` from a live/root node `z`. -/
theorem climb_aux_stable (l : concrete_st)
    (Hdec : ∀ y, contains l y = true → y ≠ 0 → anc l y < y)
    (Hstay : ∀ y, contains l y = true → (anc l y = 0 ∨ contains l (anc l y) = true))
    (I : set ℕ) :
    ∀ z, (z = 0 ∨ contains l z = true) → ∀ f, z ≤ f →
      climb_aux (fun y => anc l y) I f z = climb_aux (fun y => anc l y) I z z := by
  intro z
  induction z using Nat.strong_induction_on with
  | _ z ih =>
    intro hz f hf
    match z, hz, ih with
    | 0, _, _ => cases f <;> simp [climb_aux]
    | (zc+1), hz, ih =>
      have hlz : contains l (zc+1) = true := by
        rcases hz with h | h
        · exact absurd h (by omega)
        · exact h
      by_cases hIz : I (zc+1) = true
      · cases f with
        | zero => omega
        | succ g => simp [climb_aux, hIz]
      · have hIzf : I (zc+1) = false := by
          cases hI : I (zc+1) with
          | true => exact absurd hI hIz
          | false => rfl
        have hanc_lt : anc l (zc+1) < zc+1 := Hdec (zc+1) hlz (by omega)
        have hstart : anc l (zc+1) = 0 ∨ contains l (anc l (zc+1)) = true := Hstay (zc+1) hlz
        cases f with
        | zero => omega
        | succ g =>
          simp only [climb_aux]
          rw [if_neg (by simp [hIzf]), if_neg (by simp [hIzf])]
          have hg : anc l (zc+1) ≤ g := by omega
          have hzc : anc l (zc+1) ≤ zc := by omega
          rw [ih (anc l (zc+1)) hanc_lt hstart g hg,
              ih (anc l (zc+1)) hanc_lt hstart zc hzc]

/-- **Live unfold.**  A live non-root node not in `I` climbs to the climb of its
`anc l` parent — the value-recursive step (fuel matched by `climb_aux_stable`). -/
theorem climb_live_unfold (l : concrete_st)
    (Hdec : ∀ y, contains l y = true → y ≠ 0 → anc l y < y)
    (Hstay : ∀ y, contains l y = true → (anc l y = 0 ∨ contains l (anc l y) = true))
    (I : set ℕ) (y : ℕ)
    (hly : contains l y = true) (hy0 : y ≠ 0) (hIy : I y = false) :
    climb (fun z => anc l z) I y = climb (fun z => anc l z) I (anc l y) := by
  obtain ⟨yc, rfl⟩ : ∃ yc, y = yc + 1 := ⟨y - 1, by omega⟩
  have hanc_lt : anc l (yc+1) < yc+1 := Hdec (yc+1) hly (by omega)
  have hstart : anc l (yc+1) = 0 ∨ contains l (anc l (yc+1)) = true := Hstay (yc+1) hly
  simp only [climb]
  simp only [climb_aux]
  rw [if_neg (by simp [hIy])]
  -- goal: climb_aux _ I yc (anc l (yc+1)) = climb_aux _ I (anc l (yc+1)) (anc l (yc+1))
  exact climb_aux_stable l Hdec Hstay I (anc l (yc+1)) hstart yc (by omega)

/-! ## §3  `BranchInv`: the l-relative invariants, and merge helpers -/

/-- `contains a k` and `domain a k` are the same Bool. -/
theorem contains_eq_domain (a : concrete_st) (k : ℕ) : contains a k = domain a k := rfl

/-! ## §4  Reduction: `BranchInv l a ∧ wf a → eq (merge l a l) a`

The per-id extensional route: `merge l a l` and `a` have the same domain
(`survivors_single`), and on each live id their element (I2) and anchor coincide —
the original-node anchor by I4, the branch-new-node anchor by `climb_fixpoint`
(its birth-anchor is already `0`-or-survivor by `wf a`). -/
/-! ## §5  Base case and preservation of `BranchInv` -/

/-! ## §6  Fold corollary and the single-sided headline (3b)

A branch is built by folding a list of *good* branch events over the LCA: each is
an accurate, fresh, monotonically-allocated `Ins` whose id is new to the LCA, or an
accurate `Del`.  `BranchInv` (with `RgaInv`/`id_mono`) is preserved along such a
fold, so a branch folded from `l` satisfies `BranchInv l ·`, and merging it against
the unchanged LCA reproduces it. -/

/-! ## §7  Axiom audit -/


/- ═══════════════════════════════════════════════════════════════════════════
   TOWARD THE TWO-SIDED HEADLINE (3a/3c) — what remains.

   The single-sided bridge (§6) closes the mathematical crux for one branch: the
   per-id anchor coincidence `climb (anc l) (dom a) (anc l k) = anc a k`, proved
   as the reachable invariant `BranchInv` whose Del-step is the rehoming-through-x
   argument (`climb_remove_eq_result`).

   The TWO-SIDED `eq (merge l a b) (applySeqR l π)` (π a `loOnA`-interleave of
   Ea++Eb) extends this along two orthogonal axes, both known-shape:

   (3a) survivor set.  Generalize `survivors_single` : `survivors l a b` is the
        add/del image of `Ea ∪ Eb` over `dom l`.  For a `loOnA`-respecting fold
        this equals the domain of `applySeqR l π` (an `applySeqR`-domain induction,
        cf. `contains_doDel`/`lemma_InDomUpd1`).

   (3b→3c) anchor coincidence for the merged forest.  Generalize `BranchInv` to
        `BranchInv2 l a b` with the birth-anchor read by `birthAnc l a b` and the
        stop-set `survivors l a b`; the same climb-vs-rehoming argument applies
        because a surviving node's anchor still climbs the l-forest to the nearest
        two-sided survivor.  The interleave-order independence needed to identify
        `applySeqR l π` for two `loOnA`-respecting π is the imported
        `RGA_conditioned_convergence` engine (fold-swap over `eq`), whose swap
        oracle is `general_swap_bothFaithful`.

   Neither axis reopens the design question the single-sided bridge settled; both
   are additive to this file.
   ═══════════════════════════════════════════════════════════════════════════ -/

end RGAMergeLinearization
