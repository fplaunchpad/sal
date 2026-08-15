import Sal.ConditionedMRDTs.MRDT_Instances.SidedRGA.SidedRGA_Fugue

/-!
# Fugue mint-policy collection: live state is insufficient

The runtime migration needs a collectable issuer summary for Fugue's
generation-time `fugueChoose`. This file pins the first design boundary:
projecting knowledge to the live sided-RGA fold loses information needed by a
later mint.

The two worlds below have the same live state. One world has only the live
anchor `1`. The other minted its right child `2` and then deleted it. Fugue
chooses `(R, 1)` after the anchor in the first world, but the tombstone-visible
policy tree makes it choose `(L, 2)` in the second.
-/

namespace Sal.ConditionedMRDTs.FuguePolicyGC

open Sal.EmbedRGA (Side SChain unaryCode)
open Sal.ConditionedMRDTs

abbrev Γ := unaryCode

/-- World A: one live anchor. -/
def onlyAnchor : Know := FugueSPOT.gIns [] 0 1 0

/-- World B before deletion: the anchor and its right child. -/
def withRightChild : Know := FugueSPOT.gIns onlyAnchor 0 2 1

/-- World B after deleting the right child at visible index 1. -/
def deadRightChild : Know :=
  withRightChild ++ [genDelAt Γ withRightChild 0 3 1]

/-- PASS: deletion makes the live sided-RGA states identical. -/
theorem live_projection_equal :
    gFold Γ onlyAnchor = gFold Γ deadRightChild := by native_decide

/-- PASS: the simpler world chooses a new right child of the anchor. -/
theorem choose_without_dead_child :
    fugueChoose Γ onlyAnchor 1 = (Side.R, 1) := by native_decide

/-- PASS: the dead right child remains the tombstone-visible successor, so
the same user intent chooses a left child of that dead node. -/
theorem choose_with_dead_child :
    fugueChoose Γ deadRightChild 1 = (Side.L, 2) := by native_decide

/-- FAIL companion for live-state sufficiency: equal live folds do not imply
equal Fugue mint decisions. -/
theorem live_projection_does_not_determine_choose :
    gFold Γ onlyAnchor = gFold Γ deadRightChild ∧
    fugueChoose Γ onlyAnchor 1 ≠ fugueChoose Γ deadRightChild 1 := by
  exact ⟨live_projection_equal, by native_decide⟩

/-! ## A sufficient but unbounded summary

Delete records do not affect `fugueChoose`. Keeping every insert record is
therefore sufficient, but it retains one policy record per inserted element.
The counterexample above shows that filtering this summary to live inserts is
not sufficient.
-/

/-- Drop delete events but retain every minted insert and its chain/origins. -/
def fullMintSummary (K : Know) : Know := gMinted K

theorem gMinted_idem (K : Know) :
    gMinted (gMinted K) = gMinted K := by
  simp only [gMinted, List.filter_filter]
  apply List.filter_congr
  intro g hg
  simp

theorem gRecOfId_fullMintSummary (K : Know) (x : ℕ) :
    gRecOfId (fullMintSummary K) x = gRecOfId K x := by
  simp [gRecOfId, fullMintSummary, gMinted_idem]

theorem gChainOf_fullMintSummary (K : Know) (x : ℕ) :
    gChainOf (fullMintSummary K) x = gChainOf K x := by
  simp [gChainOf, gRecOfId_fullMintSummary]

theorem gKeys_fullMintSummary (K : Know) :
    gKeys Γ (fullMintSummary K) = gKeys Γ K := by
  simp [gKeys, fullMintSummary, gMinted_idem]

theorem hasRChild_fullMintSummary (K : Know) (a : ℕ) :
    hasRChild (fullMintSummary K) a = hasRChild K a := by
  induction K with
  | nil => rfl
  | cons g K ih =>
      rcases g with ⟨⟨t, r, op⟩, lo, ro, chain⟩
      cases op with
      | ins x p sd side =>
          change (gAnchorR a ⟨(t, r, SOp.ins x p sd side), lo, ro, chain⟩ ||
              hasRChild (fullMintSummary K) a) =
            (gAnchorR a ⟨(t, r, SOp.ins x p sd side), lo, ro, chain⟩ ||
              hasRChild K a)
          rw [ih]
      | del x =>
          change hasRChild (fullMintSummary K) a =
            (false || hasRChild K a)
          simpa using ih

theorem succOf_fullMintSummary (K : Know) (a : ℕ) :
    succOf Γ (fullMintSummary K) a = succOf Γ K a := by
  simp [succOf, succCand, gKeys_fullMintSummary, gChainOf_fullMintSummary,
    gKey]

/-- Machine-checked upper bound: all minted inserts, without delete events,
preserve every future Fugue choice. This summary is not bounded. -/
theorem fullMintSummary_preserves_choose (K : Know) (a : ℕ) :
    fugueChoose Γ (fullMintSummary K) a = fugueChoose Γ K a := by
  simp [fugueChoose, succOf_fullMintSummary, hasRChild_fullMintSummary]

/-! ## The finite information consumed at one live gap

The policy does not consume the whole tree when minting at a particular live
anchor.  It consumes the anchor chain, one monotone bit, and at most one
successor id and chain.  `LiveGap` makes that boundary explicit.  A runtime
may keep one such record for start and for every live anchor, sharing the
chains between records.
-/

structure LiveGap where
  anchorChain : SChain
  hasR : Bool
  succ : Option ℕ
  succChain : Option SChain

def liveGapOf (K : Know) (a : ℕ) : LiveGap where
  anchorChain := gChainOf K a
  hasR := hasRChild K a
  succ := succOf Γ K a
  succChain := (succOf Γ K a).map (gChainOf K)

def liveGapChoose (g : LiveGap) (a : ℕ) : Side × ℕ :=
  match g.succ with
  | some n => if g.hasR then (Side.L, n) else (Side.R, a)
  | none => (Side.R, a)

def liveGapParentChain (g : LiveGap) : SChain :=
  match g.succ with
  | some _ => if g.hasR then g.succChain.getD [] else g.anchorChain
  | none => g.anchorChain

/-- The per-gap summary makes exactly the same side/parent decision as the
full tombstone-visible Fugue policy tree. -/
theorem liveGapChoose_exact (K : Know) (a : ℕ) :
    liveGapChoose (liveGapOf K a) a = fugueChoose Γ K a := by
  rfl

/-- It also retains exactly the parent chain needed to mint the coordinate.
This is the complete generation-time observation used by `genInsAfter`. -/
theorem liveGapParentChain_exact (K : Know) (a : ℕ) :
    liveGapParentChain (liveGapOf K a) =
      gChainOf K (fugueChoose Γ K a).2 := by
  simp only [liveGapParentChain, liveGapOf, fugueChoose]
  cases hsucc : succOf Γ K a with
  | none => simp [hsucc]
  | some n =>
      cases hr : hasRChild K a <;> simp [hsucc, hr]

/-! Delete transitions are already fully congruent. A delete changes the live
fold but contributes no policy information, so every surviving gap fact is
literally unchanged. -/

def policyDelete (t : Emulation.Timestamp) (rep : Emulation.Replica)
    (x : ℕ) : GRec where
  op := (t, rep, SOp.del x)
  lo := 0
  ro := none
  chain := []

theorem fullMintSummary_append_delete (K : Know) (t : Emulation.Timestamp)
    (rep : Emulation.Replica) (x : ℕ) :
    fullMintSummary (K ++ [policyDelete t rep x]) = fullMintSummary K := by
  simp [fullMintSummary, gMinted, policyDelete, sIsIns]

/-- Exact delete-transition congruence for every anchor retained by the
collector. Removing the deleted anchor's own map entry is therefore the only
runtime action required. -/
theorem liveGapOf_append_delete (K : Know) (t : Emulation.Timestamp)
    (rep : Emulation.Replica) (x a : ℕ) :
    liveGapOf (K ++ [policyDelete t rep x]) a = liveGapOf K a := by
  have hs := fullMintSummary_append_delete K t rep x
  have hc : ∀ y, gChainOf (K ++ [policyDelete t rep x]) y = gChainOf K y := by
    intro y
    rw [← gChainOf_fullMintSummary (K ++ [policyDelete t rep x]) y,
      hs, gChainOf_fullMintSummary]
  have hr : hasRChild (K ++ [policyDelete t rep x]) a = hasRChild K a := by
    rw [← hasRChild_fullMintSummary (K ++ [policyDelete t rep x]) a,
      hs, hasRChild_fullMintSummary]
  have hn : succOf Γ (K ++ [policyDelete t rep x]) a = succOf Γ K a := by
    rw [← succOf_fullMintSummary (K ++ [policyDelete t rep x]) a,
      hs, succOf_fullMintSummary]
  have hcfun : gChainOf (K ++ [policyDelete t rep x]) = gChainOf K :=
    funext hc
  simp [liveGapOf, hc, hr, hn, hcfun]

/-! ## Stable deletion is still continuation-observable

Assume every replica has observed `deadRightChild`; the deletion is therefore
stable. Two replicas then concurrently insert ids `5` and `4` after anchor `1`.
Without policy collection, both inserts are L children of dead `2`, and the
mirrored L band displays the older id first. If collection replaces the common
knowledge with `onlyAnchor`, both become R children of `1`, and the R band
displays the newer id first. The merged reads differ.
-/

def fullA : Know :=
  deadRightChild ++ [genInsAfter Γ deadRightChild 0 5 1]

def fullB : Know :=
  deadRightChild ++ [genInsAfter Γ deadRightChild 1 4 1]

def fullMerged : Know := syncK fullA fullB

def collectedA : Know :=
  onlyAnchor ++ [genInsAfter Γ onlyAnchor 0 5 1]

def collectedB : Know :=
  onlyAnchor ++ [genInsAfter Γ onlyAnchor 1 4 1]

def collectedMerged : Know := syncK collectedA collectedB

/-- PASS: the uncollected policy tree orders the concurrent L siblings oldest
first. -/
theorem uncollected_continuation_view :
    gView Γ fullMerged = [1, 4, 5] := by native_decide

/-- FAIL companion: forgetting the stable dead child changes both operations
to R children and reverses the concurrent pair. -/
theorem collected_continuation_view :
    gView Γ collectedMerged = [1, 5, 4] := by native_decide

/-- Checked counterexample: stable dead-leaf erasure is not
continuation-equivalent under the unchanged Fugue policy. -/
theorem stable_dead_leaf_collection_changes_future_read :
    gView Γ fullMerged ≠ gView Γ collectedMerged := by native_decide

#print axioms live_projection_equal
#print axioms choose_without_dead_child
#print axioms choose_with_dead_child
#print axioms live_projection_does_not_determine_choose
#print axioms fullMintSummary_preserves_choose
#print axioms liveGapChoose_exact
#print axioms liveGapParentChain_exact
#print axioms liveGapOf_append_delete
#print axioms stable_dead_leaf_collection_changes_future_read

end Sal.ConditionedMRDTs.FuguePolicyGC
