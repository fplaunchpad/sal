import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_MergeFoldChain

/-!
# `CanonBirthBridge` — the last merge-side residual, on the applied SET

`RGA_MergeFoldChain` reduced the two-sided merge bridge to the pure event-set /
LCA-forest predicate `CanonBirthBridge l F bw rc` (no fold state):

    (contains l bw = true → ∃ cw, IsAncPath l bw cw ∧ canonAnc F (bw::cw) = canonAnc F rc)
  ∧ (contains l bw = false → canonAnc F rc = bw)

with `bw = birthAnc l a b k` (`k`'s branch-final anchor) and `rc = a_k :: p_k`
(`k`'s recorded ancestor chain).  Both sides are `canonAnc F` — the nearest
`F`-survivor up a recorded/forest chain.

This file supplies the clean `canonAnc` climb algebra (§1) and closes
`canonBirthBridge_holds` (§2) from the sharpened birth-anchor↔recorded-chain
reconciliation.  See the STATUS block (§3) for exactly which part is clean set
bookkeeping and which is the located branch-canonical residual.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
open Classical

namespace RGACanonBirthBridge

variable {α : Type} [DecidableEq α] [Inhabited α]

open Sal.Emulation
open RGACanonConvergence
open RGAMergeFoldChain (CanonBirthBridge)

/-! ## §1  The `canonAnc` climb algebra (pure, clean)

`canonAnc F L` is the first entry of `L` that survives `F` (else `0`).  These
three facts — skip a non-survivor head, stop at a survivor head, and skip a
whole non-surviving prefix — are the algebra the reconciliation runs on. -/

/-- A surviving head is the canonical anchor. -/
theorem canonAnc_pos (F : List (op_t α)) (c : ℕ) (cs : List ℕ) (h : survP F c) :
    canonAnc F (c :: cs) = c := by
  simp only [canonAnc]; rw [if_pos h]

/-- A non-surviving head is skipped. -/
theorem canonAnc_neg (F : List (op_t α)) (c : ℕ) (cs : List ℕ) (h : ¬ survP F c) :
    canonAnc F (c :: cs) = canonAnc F cs := by
  simp only [canonAnc]; rw [if_neg h]

/-- A non-surviving prefix is dropped entirely. -/
theorem canonAnc_append_dead (F : List (op_t α)) :
    ∀ (pre L : List ℕ), (∀ c ∈ pre, ¬ survP F c) →
      canonAnc F (pre ++ L) = canonAnc F L := by
  intro pre
  induction pre with
  | nil => intro L _; rfl
  | cons c cs ih =>
    intro L h
    have hc : ¬ survP F c := h c (by simp)
    have hcs : ∀ d ∈ cs, ¬ survP F d := fun d hd => h d (by simp [hd])
    rw [List.cons_append, canonAnc_neg F c (cs ++ L) hc, ih L hcs]

/-- Two chains that share a head and reach the same canonical anchor on their
tails reach the same canonical anchor overall (the tail is only consulted when
the head is a non-survivor). -/
theorem canonAnc_cons_congr (F : List (op_t α)) (c : ℕ) (L M : List ℕ)
    (h : canonAnc F L = canonAnc F M) : canonAnc F (c :: L) = canonAnc F (c :: M) := by
  by_cases hc : survP F c
  · rw [canonAnc_pos F c L hc, canonAnc_pos F c M hc]
  · rw [canonAnc_neg F c L hc, canonAnc_neg F c M hc, h]

/-! ## §2  `canonBirthBridge_holds`

The bridge closes from three reconciliation facts about how `k`'s recorded chain
`rc` relates to its branch-final anchor `bw`, each a pure `survP F` / `IsAncPath l`
statement (NO fold state):

* `hsplit`+`hpreDead` — `bw` sits on `rc` (`rc = rcPre ++ bw :: rcSuf`) with every
  recorded entry *nearer* than `bw` a non-`F`-survivor.  This is the branch
  resolution (`bw = anc (owning branch) k = resolve · rc`) composed with the
  OR-set survivor reconciliation (a branch-dead recorded ancestor cannot survive
  the merge).  It says the `F`-climb of `rc` reaches `bw`'s recorded position.
* `hout` — an off-forest `bw` (branch-new anchor) survives `F` (it lies in a
  branch's `difference` set, hence in `survivors l a b`).
* `hin` — for an in-forest `bw` (an original `l`-node), `bw`'s `l`-ancestor chain
  and its recorded rootward tail `rcSuf` reach the *same* nearest `F`-survivor.

Given these, the two `canonAnc` obligations are pure climb algebra (§1): strip the
dead prefix, then stop at `bw` (off-forest) or push the head `bw` through and match
tails (in-forest). -/
theorem canonBirthBridge_holds
    (l : concrete_st α) (F : List (op_t α)) (bw : ℕ) (rc : List ℕ)
    (rcPre rcSuf : List ℕ)
    (hsplit : rc = rcPre ++ bw :: rcSuf)
    (hpreDead : ∀ c ∈ rcPre, ¬ survP F c)
    (hout : contains l bw = false → survP F bw)
    (hin : contains l bw = true →
        ∃ cw, IsAncPath l bw cw ∧ canonAnc F cw = canonAnc F rcSuf) :
    CanonBirthBridge l F bw rc := by
  -- strip the dead recorded prefix: `rc` climbs like `bw :: rcSuf`
  have hstrip : canonAnc F rc = canonAnc F (bw :: rcSuf) := by
    rw [hsplit]; exact canonAnc_append_dead F rcPre (bw :: rcSuf) hpreDead
  refine ⟨?_, ?_⟩
  · -- in-forest: produce `bw`'s `l`-chain; both climb to the same `F`-survivor
    intro hlw
    obtain ⟨cw, hpath, hcweq⟩ := hin hlw
    refine ⟨cw, hpath, ?_⟩
    rw [hstrip]
    exact canonAnc_cons_congr F bw cw rcSuf hcweq
  · -- off-forest: `bw` is itself the nearest `F`-survivor on `rc`
    intro hlwf
    rw [hstrip, canonAnc_pos F bw rcSuf (hout hlwf)]

#print axioms canonBirthBridge_holds

/-! ## §3  STATUS — clean bookkeeping vs. the located branch residual

**Both cases close, sorry-free, kernel-clean** (`canonBirthBridge_holds`:
`[propext, Classical.choice, Quot.sound]` only).  What each half needed:

* The `canonAnc` **climb algebra** (§1) — skip a non-survivor, stop at a
  survivor, drop a dead prefix, push a shared head — is genuinely clean pure
  set bookkeeping, and does all the assembly.
* The **off-forest** case reduces to `survP F bw` (`hout`) after the dead-prefix
  strip: clean.
* The **in-forest** case reduces to `hin`: `bw`'s `l`-chain `cw` and the recorded
  tail `rcSuf` reach the same `F`-survivor.  When `survP F bw`, both climbs stop
  at `bw` and `hin` is trivial; the residual bites only when `bw ∈ l` is deleted
  in the *other* branch (`¬ survP F bw`), where `canonAnc F cw = canonAnc F rcSuf`
  asserts that `bw`'s recorded rootward tail is `bw`'s `l`-chain modulo splicing
  across recorded ancestors that do not survive `F`.

**The honest reading.**  `hsplit`/`hpreDead`/`hin` are NOT clean set/LCA
bookkeeping in isolation: they are exactly GAP-1 (`hBN`, the branch-new anchor
coincidence) re-expressed on the applied SET `F` instead of the fold STATE.
`bw = anc (owning branch) k` is `k`'s *branch-final* anchor, while `rc`'s head is
its *recorded* anchor; that `bw` lies on `rc`'s post-rehoming chain and that its
`l`-chain and recorded tail share an `F`-survivor climb are the branch-canonical /
event-list facts flagged in `RGA_MergeBranchNew`'s OBSTRUCTION block
(`foldChain_of_goodFold`).  The `RGA_MergeFoldChain` reduction **relocated** the
crux from the fold state to `F`'s survivor set; it did not dissolve it into clean
bookkeeping.  The remaining supply obligation is the branch-canonical
characterization of `rc` relative to `birthAnc` — an induction over `Ea ++ Eb`,
strictly below `FoldBirthChain`, and the sole input `canonBirthBridge_holds`
still consumes. -/

end RGACanonBirthBridge
