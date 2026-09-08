import Sal.MRDTs.Instances.FugueMaxReplay

namespace Sal.MRDTs.Instances.SidedEmbedRGA.FugueMaxContractSPOT

open Sal.MRDTs.Foundation
open Sal.EmbedRGA (unaryCode FMEntry PosFMChain TagsOK fmTagOK TagOK fmδ)

/-- One live root insertion. -/
def shortHistory : KnowM := [mGenInsAt unaryCode [] 0 1 0]

/-- The same insertion, followed by a child that is then deleted. -/
def withChild : KnowM := shortHistory ++ [mGenInsAt unaryCode shortHistory 0 2 1]
def deletedChild : KnowM := withChild ++ [mGenDelAt unaryCode withChild 0 3 1]

def next (K : KnowM) := fOpOfM unaryCode (mGenInsAt unaryCode K 0 4 1)

def atZero (K : KnowM) : ℕ → KnowM := fun r => if r = 0 then K else []

@[simp] theorem atZero_zero (K : KnowM) : atZero K 0 = K := by simp [atZero]

@[simp] theorem atZero_update (K L : KnowM) : Function.update (atZero K) 0 L = atZero L := by
  funext r
  by_cases hr : r = 0
  · subst r; simp [atZero]
  · simp [atZero, hr]

private theorem fresh_atZero {K : KnowM} {t : ℕ}
    (h : ∀ g ∈ K, g.ts ≠ t) : ∀ q, ∀ g ∈ atZero K q, g.ts ≠ t := by
  intro q g hg
  by_cases hq : q = 0
  · exact h g (by simpa [atZero, hq] using hg)
  · simp [atZero, hq] at hg

theorem short_reachable : MaxReach unaryCode (atZero shortHistory) := by
  have h := MaxReach.ins (Γ := unaryCode) (G := fun _ => []) 0 1 0 (.init) (by decide)
    (by simp) (by simp [mMintedIds, mMinted])
  convert h using 1
  funext r
  by_cases hr : r = 0
  · subst r; simp [atZero, shortHistory]
  · simp [atZero, hr]

theorem child_reachable : MaxReach unaryCode (atZero withChild) := by
  have hf : ∀ g ∈ shortHistory, g.ts ≠ 2 := by
    simp only [shortHistory, List.mem_singleton]
    intro g hg
    subst g
    decide
  have h := MaxReach.ins (G := atZero shortHistory) 0 2 1 short_reachable (by decide)
    (fresh_atZero hf) (by
      change ∀ m ∈ mMintedIds shortHistory, m < 2
      have hm : mMintedIds shortHistory = [1] := by decide
      simp [hm])
  simpa only [atZero_zero, atZero_update, withChild] using h

theorem deleted_reachable : MaxReach unaryCode (atZero deletedChild) := by
  have hf : ∀ g ∈ withChild, g.ts ≠ 3 := by
    simp only [withChild, shortHistory, List.mem_append, List.mem_singleton]
    intro g hg
    rcases hg with rfl | rfl <;> decide
  have h := MaxReach.del (G := atZero withChild) 0 3 1 child_reachable (by decide)
    (fresh_atZero hf)
  simpa only [atZero_zero, atZero_update, deletedChild] using h

theorem same_materialized_state :
    mFold unaryCode shortHistory = mFold unaryCode deletedChild := by decide

theorem distinct_required_operations : next shortHistory ≠ next deletedChild := by decide

theorem wrong_operation_not_generated : ∀ i,
    next deletedChild ≠ fOpOfM unaryCode (mGenInsAt unaryCode shortHistory 0 4 i) := by
  intro i
  cases i with
  | zero => decide
  | succ i =>
    cases i with
    | zero => exact Ne.symm distinct_required_operations
    | succ i =>
      have hv : mView unaryCode shortHistory = [1] := by decide
      simp only [mGenInsAt, mAnchorAt, hv]
      simp
      decide

theorem weak_guard_accepts_short :
    fApplicable unaryCode (next shortHistory) (mFold unaryCode shortHistory) := by
  constructor
  · decide
  · refine ⟨[FMEntry.R [0] 1, .R [0] 3], ?_, ?_, ?_, ?_⟩
    · simp [PosFMChain, fmδ]
    · simp [TagsOK, fmTagOK, TagOK]
    · decide
    · decide

/-- The current guard also accepts an operation that this issuer cannot
generate at any client position: it names the missing child's coordinate. -/
theorem weak_guard_accepts_wrong :
    fApplicable unaryCode (next deletedChild) (mFold unaryCode shortHistory) := by
  constructor
  · decide
  · refine ⟨[FMEntry.R [0] 1, .R [0] 1, .L 2], ?_, ?_, ?_, ?_⟩
    · simp [PosFMChain, fmδ]
    · simp [TagsOK, fmTagOK, TagOK]
    · decide
    · decide

theorem same_visible_insertion :
    mView unaryCode (shortHistory ++ [mGenInsAt unaryCode shortHistory 0 4 1]) = [1, 4] ∧
    mView unaryCode (deletedChild ++ [mGenInsAt unaryCode deletedChild 0 4 1]) = [1, 4] := by decide

/-- The exact prepared operation is not a function of the replay signature's
live state, even with fixed replica, timestamp, and client position. -/
theorem exact_generator_not_state_function :
    ¬ ∃ mint : SState → Op FOp,
      mint (mFold unaryCode shortHistory) = next shortHistory ∧
      mint (mFold unaryCode deletedChild) = next deletedChild := by
  rintro ⟨mint, hshort, hdeleted⟩
  exact distinct_required_operations (hshort.symm.trans
    ((congrArg mint same_materialized_state).trans hdeleted))

/-- Allowing a relational guard instead of a deterministic preparer does
not recover the missing information: even the set of legal insertions differs. -/
theorem exact_issuance_not_state_predicate :
    ¬ ∃ allowed : SState → Op FOp → Prop,
      (∀ o, allowed (mFold unaryCode shortHistory) o ↔
        ∃ i, o = fOpOfM unaryCode (mGenInsAt unaryCode shortHistory 0 4 i)) ∧
      (∀ o, allowed (mFold unaryCode deletedChild) o ↔
        ∃ i, o = fOpOfM unaryCode (mGenInsAt unaryCode deletedChild 0 4 i)) := by
  rintro ⟨allowed, hs, hd⟩
  have accepted := (hd (next deletedChild)).mpr ⟨1, rfl⟩
  rw [← same_materialized_state] at accepted
  obtain ⟨i, hi⟩ := (hs (next deletedChild)).mp accepted
  exact wrong_operation_not_generated i hi

#print axioms exact_generator_not_state_function
#print axioms short_reachable
#print axioms deleted_reachable
#print axioms weak_guard_accepts_wrong
#print axioms exact_issuance_not_state_predicate

end Sal.MRDTs.Instances.SidedEmbedRGA.FugueMaxContractSPOT
