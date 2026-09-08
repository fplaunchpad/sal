import Sal.MRDTs.Instances.FugueMaxReplay
import Mathlib.Data.List.GetD

/-!
# FugueMax issuer metadata

The implementation retains its live coordinate list and all insertion records.
Deletion events are not retained in the issuer summary. The public sequential
state remains a plain list; this is implementation-side minting information.

`prepareInsert_exact` proves equality with the existing positional generator,
including its parent, origins, and tagged chain. This is a representation
refinement, not yet a public correctness certificate.
-/

namespace Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax

open Sal.MRDTs.Foundation
open Sal.EmbedRGA (OrderedPrefixCode Side)

structure IssuerState where
  live : SState
  births : KnowM
  deriving DecidableEq

def summarize (Γ : OrderedPrefixCode) (K : KnowM) : IssuerState :=
  ⟨mFold Γ K, mMinted K⟩

theorem minted_idem (K : KnowM) : mMinted (mMinted K) = mMinted K := by
  simp only [mMinted, List.filter_filter]
  apply List.filter_congr
  intro g hg
  simp

@[simp] theorem recOf_minted (K : KnowM) (x : ℕ) :
    mRecOfId (mMinted K) x = mRecOfId K x := by
  simp [mRecOfId, minted_idem]

@[simp] theorem chainOf_minted (K : KnowM) (x : ℕ) :
    mChainOf (mMinted K) x = mChainOf K x := by
  simp [mChainOf]

@[simp] theorem keys_minted (Γ : OrderedPrefixCode) (K : KnowM) :
    mKeys Γ (mMinted K) = mKeys Γ K := by
  simp [mKeys, mMintedIds, minted_idem, mKey]

@[simp] theorem hasRChild_minted (K : KnowM) (a : ℕ) :
    hasRChildM (mMinted K) a = hasRChildM K a := by
  induction K with
  | nil => rfl
  | cons g K ih =>
      cases hop : g.op with
      | ins p sd =>
          simpa [mMinted, mIsIns, hop, hasRChildM] using
            (congrArg (fun b => isRChildOf a g || b) ih)
      | del x => simpa [mMinted, mIsIns, hop, hasRChildM, isRChildOf] using ih

@[simp] theorem successor_minted (Γ : OrderedPrefixCode) (K : KnowM) (a : ℕ) :
    succOfM Γ (mMinted K) a = succOfM Γ K a := by
  simp [succOfM, succCandM, mKey]

theorem genAfter_minted (Γ : OrderedPrefixCode) (K : KnowM) (r t a : ℕ) :
    mGenInsAfter Γ (mMinted K) r t a = mGenInsAfter Γ K r t a := by
  simp [mGenInsAfter]

/-- Positional intent comes from the live list; tree placement uses births,
including deleted births. Out-of-range behavior agrees with `mAnchorAt`. -/
def prepareInsert (Γ : OrderedPrefixCode) (s : IssuerState) (r t i : ℕ) : MRec :=
  mGenInsAfter Γ s.births r t (if i = 0 then 0 else (sIds s.live).getD (i - 1) 0)

def prepareDelete (s : IssuerState) (r t i : ℕ) : MRec :=
  { ts := t, rep := r, op := .del ((sIds s.live).getD i 0),
    lo := 0, ro := none, chain := [] }

theorem prepareInsert_exact (Γ : OrderedPrefixCode) (K : KnowM) (r t i : ℕ) :
    prepareInsert Γ (summarize Γ K) r t i = mGenInsAt Γ K r t i := by
  unfold prepareInsert summarize mGenInsAt mAnchorAt mView
  exact genAfter_minted Γ K r t _

theorem prepareDelete_exact (Γ : OrderedPrefixCode) (K : KnowM) (r t i : ℕ) :
    prepareDelete (summarize Γ K) r t i = mGenDelAt Γ K r t i := rfl

/-- Insertions add one immutable birth; deletions change only the live list. -/
def update (Γ : OrderedPrefixCode) (s : IssuerState) (g : MRec) : IssuerState :=
  ⟨mStep Γ s.live g, s.births ++ mMinted [g]⟩

theorem update_exact (Γ : OrderedPrefixCode) (K : KnowM) (g : MRec) :
    update Γ (summarize Γ K) g = summarize Γ (K ++ [g]) := by
  simp [update, summarize, mFold_snoc, mMinted_append]

theorem insert_exact (Γ : OrderedPrefixCode) (K : KnowM) (r t i : ℕ) :
    update Γ (summarize Γ K) (prepareInsert Γ (summarize Γ K) r t i) =
      summarize Γ (K ++ [mGenInsAt Γ K r t i]) := by
  rw [prepareInsert_exact, update_exact]

theorem delete_exact (Γ : OrderedPrefixCode) (K : KnowM) (r t i : ℕ) :
    update Γ (summarize Γ K) (prepareDelete (summarize Γ K) r t i) =
      summarize Γ (K ++ [mGenDelAt Γ K r t i]) := by
  rw [prepareDelete_exact, update_exact]

theorem delete_preserves_births (Γ : OrderedPrefixCode) (s : IssuerState) (r t i : ℕ) :
    (update Γ s (prepareDelete s r t i)).births = s.births := by
  simp [update, prepareDelete, mMinted, mIsIns]

/-- Filtering out deletion records commutes with the generation layer's
knowledge union, including its duplicate suppression and list order. -/
theorem minted_sync (K L : KnowM) :
    mMinted (syncM K L) = syncM (mMinted K) (mMinted L) := by
  simp only [syncM, mMinted, List.filter_append, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro g hg
  by_cases hi : mIsIns g = true <;> simp [hi]

/-- Three-way live-state merge, with monotone union of issuer births. Birth
list order is an issuer representation detail, not a released MRDT state. -/
def merge (ancestor left right : IssuerState) : IssuerState :=
  ⟨sMerge ancestor.live left.live right.live, syncM left.births right.births⟩

theorem merge_births_exact (Γ : OrderedPrefixCode) (A K L : KnowM) :
    (merge (summarize Γ A) (summarize Γ K) (summarize Γ L)).births =
      (summarize Γ (syncM K L)).births := (minted_sync K L).symm

/-- Every positional insertion is represented by a finite in-range choice:
the historical generator maps out-of-range positions back to the root. -/
theorem insert_position_finite (Γ : OrderedPrefixCode) (s : IssuerState) (r t i : ℕ) :
    ∃ j < s.live.length + 1, prepareInsert Γ s r t i = prepareInsert Γ s r t j := by
  by_cases hi : i < s.live.length + 1
  · exact ⟨i, hi, rfl⟩
  · refine ⟨0, by omega, ?_⟩
    have hlen : (sIds s.live).length ≤ i - 1 := by simp [sIds]; omega
    unfold prepareInsert
    rw [List.getD_eq_default _ _ hlen]
    simp

/-- One additional delete position represents the existing generator's
out-of-range delete of the root sentinel (a no-op), without changing its API. -/
theorem delete_position_finite (s : IssuerState) (r t i : ℕ) :
    ∃ j < s.live.length + 1, prepareDelete s r t i = prepareDelete s r t j := by
  by_cases hi : i < s.live.length + 1
  · exact ⟨i, hi, rfl⟩
  · refine ⟨s.live.length, by omega, ?_⟩
    have hlen : (sIds s.live).length ≤ i := by simp [sIds]; omega
    unfold prepareDelete
    rw [List.getD_eq_default _ _ hlen,
      List.getD_eq_default _ _ (show (sIds s.live).length ≤ s.live.length by simp [sIds])]

/-- An executable exact-generator check. Global timestamp freshness remains
the execution framework's responsibility. This check enforces positive times
and the generator's local Lamport condition for insertions. -/
def canIssue (Γ : OrderedPrefixCode) (s : IssuerState) (g : MRec) : Bool :=
  decide (0 < g.ts) &&
    if mIsIns g then
      s.births.all (fun b => decide (b.ts < g.ts)) &&
        (List.range (s.live.length + 1)).any
          (fun i => decide (g = prepareInsert Γ s g.rep g.ts i))
    else
      (List.range (s.live.length + 1)).any
        (fun i => decide (g = prepareDelete s g.rep g.ts i))

theorem canIssue_insert_iff (Γ : OrderedPrefixCode) (s : IssuerState) (g : MRec)
    (hi : mIsIns g = true) :
    canIssue Γ s g = true ↔ 0 < g.ts ∧
      (∀ b ∈ s.births, b.ts < g.ts) ∧ ∃ i, g = prepareInsert Γ s g.rep g.ts i := by
  simp only [canIssue, hi, if_true, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true, List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨hp, hb, i, hi, he⟩
    exact ⟨hp, hb, i, he⟩
  · rintro ⟨hp, hb, i, he⟩
    obtain ⟨j, hj, heq⟩ := insert_position_finite Γ s g.rep g.ts i
    exact ⟨hp, hb, j, hj, he.trans heq⟩

theorem canIssue_delete_iff (Γ : OrderedPrefixCode) (s : IssuerState) (g : MRec)
    (hi : mIsIns g = false) :
    canIssue Γ s g = true ↔ 0 < g.ts ∧ ∃ i, g = prepareDelete s g.rep g.ts i := by
  simp only [canIssue, hi, Bool.false_eq_true, if_false, Bool.and_eq_true,
    decide_eq_true_eq, List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨hp, i, hi, he⟩
    exact ⟨hp, i, he⟩
  · rintro ⟨hp, i, he⟩
    obtain ⟨j, hj, heq⟩ := delete_position_finite s g.rep g.ts i
    exact ⟨hp, j, hj, he.trans heq⟩

theorem canIssue_insert_exact (Γ : OrderedPrefixCode) (K : KnowM) (g : MRec)
    (hi : mIsIns g = true) :
    canIssue Γ (summarize Γ K) g = true ↔ 0 < g.ts ∧
      (∀ t ∈ mMintedIds K, t < g.ts) ∧ ∃ i, g = mGenInsAt Γ K g.rep g.ts i := by
  rw [canIssue_insert_iff Γ _ _ hi]
  simp only [prepareInsert_exact]
  simp [summarize, mMintedIds]

theorem canIssue_delete_exact (Γ : OrderedPrefixCode) (K : KnowM) (g : MRec)
    (hi : mIsIns g = false) :
    canIssue Γ (summarize Γ K) g = true ↔
      0 < g.ts ∧ ∃ i, g = mGenDelAt Γ K g.rep g.ts i := by
  rw [canIssue_delete_iff Γ _ _ hi]
  simp only [prepareDelete_exact]

#print axioms prepareInsert_exact
#print axioms update_exact
#print axioms minted_sync
#print axioms canIssue_insert_exact
#print axioms canIssue_delete_exact

end Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax
