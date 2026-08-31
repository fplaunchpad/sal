import Sal.MRDTs.Instances.SidedEmbedRGA
import Sal.MRDTs.Instances.EmbedRGA

/-!
# Sided RGA: per-policy intent theorems

The capstone (`SidedEmbedRGA.replayAdequacy`) is policy-free: sides are
payload to convergence. This file is the other half of "one kernel, two
policies", what ordering intent each side-selection policy buys:

* **§1 The all-R fragment, at the instance** (`sFold_liftOp`,
  `sided_allR_read_eq`): under the always-R policy the sided instance IS
  the one-sided embed instance, fold for fold, an UNCONDITIONAL
  simulation, no honesty hypotheses: the all-R sided coordinate is the
  one-sided coordinate under the symbol map, and the sort keys coincide
  definitionally (`sym = symR`), so every insert lands in the same slot.
  Through the one-sided instance's own theorems this chains onward: the
  all-R sided read = the naive text buffer (tier 3) = the published
  tombstoned RGA's read (the compaction theorem, standalone target).

* **§2 Non-interleaving at the instance**
  (`sided_fold_subtree_convex`): in any fold whose inserts are
  chain-generated (the honesty layer's `chain_gen` shape), everything
  the display places strictly between two members of a subtree is
  itself in the subtree. A replica's run whose ops chain (each anchored
  at the previous, what the Fugue policy produces for forward AND
  backward typing) is a subtree, so no concurrent survivor can ever
  interleave into it. This is the datatype half of the L19 discharge as
  a theorem; the SPOT replays the L19 trace and watches the blocks stay
  contiguous.

**The re-derivation decision (recorded).** The one-sided instance file
stays as-is rather than being re-derived from the sided kernel: its
downstream ecosystem (SeqSpec, ReadEquiv/compaction, EliasDelta,
Peritext_Embed) consumes it directly, and §1 makes the duplication
harmless, the all-R fragment equality transports any one-sided theorem
to the sided instance when needed, at zero proof debt.

**What remains of the Fugue half (deliberately out of scope here).**
`sided_fold_subtree_convex` gives non-interleaving to any policy that
keeps a run inside one subtree. Proving that the FUGUE RULE does so for
backward runs ("right child of the left neighbor when it has no right
children, else left child of the successor") needs a generation model
the framework does not yet have: intent-level ops ("insert before
position i"), the policy as a function of the replica-local tree, and a
per-replica run notion. That layer, and the maximal-non-interleaving
statement of Weidner & Kleppmann, is not covered by this file.
-/

namespace Sal.MRDTs.Instances.SidedEmbedRGA

open Sal.MRDTs.Foundation
open Sal.MRDTs.Instances.EmbedRGA
open Sal.EmbedRGA (OrderedPrefixCode keyLt key sym unaryCode
  Side SChain PosSChain PosChain sKey sBlock symR sidedCoordOf
  schain_subtree_convex sdisplay_iff_schainBefore keyLt_irrefl)

set_option linter.unusedSectionVars false

/-! ## §1  The all-R fragment at the instance -/

/-- Lift a one-sided op to the sided instance: inserts take side `R` and
carry the symbol-mapped prefix; deletes are unchanged. -/
def liftOp : Op (EOp ℕ) → Op SOp
  | (t, r, .ins e π a) => (t, r, .ins e (π.map symR) a Side.R)
  | (t, r, .del x)     => (t, r, .del x)

/-- Lift a one-sided record: the coordinate goes through the R-band
symbol map. -/
def liftRec (r : ERec ℕ) : SRec := (r.1, r.2.1, r.2.2.map symR)

/-- The lifted sort key IS the one-sided sort key (`sym = symR`
definitionally). -/
theorem liftRec_key (x : ERec ℕ) : sKey (liftRec x).2.2 = key x.2.2 := rfl

theorem sIds_map_liftRec (s : EState ℕ) : sIds (s.map liftRec) = eIds s := by
  induction s with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons, sIds, eIds, List.map_cons] at ih ⊢; rw [ih]; rfl

/-- Sorted insertion commutes with the lift: the guards are the same
`keyLt` calls. -/
theorem sInsert_liftRec (r : ERec ℕ) : ∀ (s : EState ℕ),
    sInsert (liftRec r) (s.map liftRec) = (eInsert r s).map liftRec
  | [] => rfl
  | x :: xs => by
      by_cases h : keyLt (key x.2.2) (key r.2.2) = true
      · rw [show eInsert r (x :: xs) = r :: x :: xs from by simp [eInsert, h],
          show sInsert (liftRec r) ((x :: xs).map liftRec)
              = liftRec r :: (x :: xs).map liftRec from by
            simp [sInsert, liftRec_key, h]]
        rfl
      · rw [show eInsert r (x :: xs) = x :: eInsert r xs from by
            simp [eInsert, h],
          show sInsert (liftRec r) ((x :: xs).map liftRec)
              = liftRec x :: sInsert (liftRec r) (xs.map liftRec) from by
            simp [sInsert, liftRec_key, h],
          List.map_cons, sInsert_liftRec r xs]

/-- Deletion commutes with the lift. -/
theorem filter_map_liftRec (s : EState ℕ) (x : ℕ) :
    (s.map liftRec).filter (fun r => decide (r.1 ≠ x))
      = (s.filter (fun r => decide (r.1 ≠ x))).map liftRec := by
  induction s with
  | nil => rfl
  | cons a as ih =>
      simp only [ne_eq, decide_not] at ih
      by_cases h : a.1 = x <;>
        simp [liftRec, List.filter_cons, h, ih]

/-- **The all-R fragment, at the instance**: the sided fold of a lifted
history IS the one-sided fold, record for record. Unconditional, no
honesty, no sortedness hypotheses: a pure simulation. -/
theorem sFold_liftOp (Γ : OrderedPrefixCode) : ∀ (ρ : List (Op (EOp ℕ))),
    sFold Γ (ρ.map liftOp) = (eFold Γ ρ).map liftRec := by
  intro ρ
  induction ρ using List.reverseRecOn with
  | nil => rfl
  | append_singleton ρ o ih =>
      rw [show (ρ ++ [o]).map liftOp = ρ.map liftOp ++ [liftOp o] from by
          simp,
        sFold_snoc, eFold_snoc, ih]
      obtain ⟨ts, r, op⟩ := o
      cases op with
      | del x =>
          show ((eFold Γ ρ).map liftRec).filter _ = _
          exact filter_map_liftRec (eFold Γ ρ) x
      | ins e π a =>
          show sUpdate Γ ((eFold Γ ρ).map liftRec)
              (ts, r, .ins e (π.map symR) a Side.R) = _
          simp only [sUpdate, eUpdate]
          rw [sIds_map_liftRec]
          by_cases hmem : ts ∈ eIds (eFold Γ ρ)
          · rw [if_pos hmem, if_pos hmem]
          · rw [if_neg hmem, if_neg hmem,
              show ((ts, e, π.map symR ++ sBlock Γ (Side.R, ts - a)) : SRec)
                  = liftRec (ts, e, π ++ Γ.enc (ts - a)) from by
                simp [liftRec, sBlock, List.map_append]]
            exact sInsert_liftRec _ _

/-- The reads agree: id-and-element sequence for id-and-element
sequence. Chained with tier 3 and the compaction theorem, the all-R
sided instance = the naive text buffer = the published tombstoned RGA. -/
theorem sided_allR_read_eq (Γ : OrderedPrefixCode) (ρ : List (Op (EOp ℕ))) :
    (sFold Γ (ρ.map liftOp)).map (fun r => (r.1, r.2.1))
      = (eFold Γ ρ).map (fun r => (r.1, r.2.1)) := by
  rw [sFold_liftOp, List.map_map]
  rfl

#print axioms sFold_liftOp

/-! ## §2  Non-interleaving at the instance -/

/-- **Subtrees display as contiguous blocks, at the fold.** In any fold
whose inserts are chain-generated (`chain_gen`'s shape: every insert's
coordinate is a positive sided chain's coordinate with telescoping sum),
a record `z` displaying strictly between two members `x, y` of the
subtree rooted at `p` is itself in that subtree. `keyLt (sKey ·) (sKey ·)`
is the display order of the canonical sorted state, so "between" is
between in what the user reads. A replica's run whose ops chain, what
the Fugue policy generates for forward and backward typing alike, is a
subtree, so nothing concurrent ever interleaves into it. -/
theorem sided_fold_subtree_convex (Γ : OrderedPrefixCode)
    {ρ : List (Op SOp)} (chainOf : ℕ → SChain)
    (hch : ∀ o ∈ ρ, sIsIns o = true →
      PosSChain (chainOf o.1) ∧ sCoord Γ o = sidedCoordOf Γ (chainOf o.1) ∧
      ((chainOf o.1).map Prod.snd).sum = o.1)
    {p : SChain} {x z y : SRec}
    (hx : x ∈ sFold Γ ρ) (hz : z ∈ sFold Γ ρ) (hy : y ∈ sFold Γ ρ)
    (hpx : ∃ ex, chainOf x.1 = p ++ ex) (hpy : ∃ ey, chainOf y.1 = p ++ ey)
    (hzx : keyLt (sKey z.2.2) (sKey x.2.2) = true)
    (hyz : keyLt (sKey y.2.2) (sKey z.2.2) = true) :
    ∃ ez, chainOf z.1 = p ++ ez := by
  obtain ⟨ox, hox, hix, hrx⟩ := s_fold_rec_sub Γ ρ x hx
  obtain ⟨oz, hoz, hiz, hrz⟩ := s_fold_rec_sub Γ ρ z hz
  obtain ⟨oy, hoy, hiy, hry⟩ := s_fold_rec_sub Γ ρ y hy
  obtain ⟨hpox, hcox, -⟩ := hch ox hox hix
  obtain ⟨hpoz, hcoz, -⟩ := hch oz hoz hiz
  obtain ⟨hpoy, hcoy, -⟩ := hch oy hoy hiy
  have ex1 : x.1 = ox.1 := by rw [hrx]; rfl
  have ez1 : z.1 = oz.1 := by rw [hrz]; rfl
  have ey1 : y.1 = oy.1 := by rw [hry]; rfl
  have ex2 : x.2.2 = sidedCoordOf Γ (chainOf x.1) := by
    rw [hrx]; exact hcox
  have ez2 : z.2.2 = sidedCoordOf Γ (chainOf z.1) := by
    rw [hrz]; exact hcoz
  have ey2 : y.2.2 = sidedCoordOf Γ (chainOf y.1) := by
    rw [hry]; exact hcoy
  have hpx1 : PosSChain (chainOf x.1) := ex1.symm ▸ hpox
  have hpz1 : PosSChain (chainOf z.1) := ez1.symm ▸ hpoz
  have hpy1 : PosSChain (chainOf y.1) := ey1.symm ▸ hpoy
  have hnexz : chainOf x.1 ≠ chainOf z.1 := by
    intro he
    rw [ex2, ez2, he, keyLt_irrefl] at hzx
    exact Bool.noConfusion hzx
  have hnezy : chainOf z.1 ≠ chainOf y.1 := by
    intro he
    rw [ez2, ey2, he, keyLt_irrefl] at hyz
    exact Bool.noConfusion hyz
  have hbxz : Sal.EmbedRGA.schainBefore (chainOf x.1) (chainOf z.1) :=
    (sdisplay_iff_schainBefore Γ hpx1 hpz1 hnexz).mp
      (by rw [← ex2, ← ez2]; exact hzx)
  have hbzy : Sal.EmbedRGA.schainBefore (chainOf z.1) (chainOf y.1) :=
    (sdisplay_iff_schainBefore Γ hpz1 hpy1 hnezy).mp
      (by rw [← ez2, ← ey2]; exact hyz)
  exact schain_subtree_convex p hpx hpy hbxz hbzy

#print axioms sided_fold_subtree_convex

/-! ## §3  SPOT: L19, contiguous, PASS and FAIL shaped

The L19 trace under the Fugue policy's anchor choices, replayed through
the datatype's own fold: two concurrent backward runs become L-chains
and display as contiguous blocks, `[50, 30, 10, 61, 41, 21, 1]`. The
FAIL pin is the one-sided fan's interleaved verdict on the same
stamps. -/

namespace SidedSPOT

/-- Anchor chains of the L19 trace (Fugue anchoring, unary code). -/
def ch1 : SChain := [(Side.R, 1)]
def ch10 : SChain := ch1 ++ [(Side.L, 9)]
def ch30 : SChain := ch10 ++ [(Side.L, 20)]
def ch21 : SChain := ch1 ++ [(Side.L, 20)]
def ch41 : SChain := ch21 ++ [(Side.L, 20)]

def cOf (ch : SChain) : List ℕ := sidedCoordOf unaryCode ch

/-- The L19 history: `1` at the root, then replica A types backward
`10, 30, 50` (each an L-entry at the successor) while replica B types
backward `21, 41, 61`. Elements = ids for readability; every insert
carries its anchor's stored coordinate as the prefix. -/
def opsL19 : List (Op SOp) :=
  [ (1, 0, .ins 1 [] 0 Side.R)
  , (10, 0, .ins 10 (cOf ch1) 1 Side.L)
  , (30, 0, .ins 30 (cOf ch10) 10 Side.L)
  , (50, 0, .ins 50 (cOf ch30) 30 Side.L)
  , (21, 1, .ins 21 (cOf ch1) 1 Side.L)
  , (41, 1, .ins 41 (cOf ch21) 21 Side.L)
  , (61, 1, .ins 61 (cOf ch41) 41 Side.L) ]

/-- PASS: the display keeps each run contiguous. -/
theorem l19_blocks_contiguous :
    (sFold unaryCode opsL19).map (fun r => r.2.1)
      = [50, 30, 10, 61, 41, 21, 1] := by native_decide

/-- Should-FAIL pin: the one-sided fan's interleaved verdict on the same
stamps, `[61, 50, 41, 30, 21, 10, 1]`, is exactly what this datatype
does NOT display. -/
theorem l19_not_interleaved :
    (sFold unaryCode opsL19).map (fun r => r.2.1)
      ≠ [61, 50, 41, 30, 21, 10, 1] := by native_decide

end SidedSPOT

end Sal.MRDTs.Instances.SidedEmbedRGA
