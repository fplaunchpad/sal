import Sal.MRDTs.Instances.FugueMaxIssuerSet

/-!
# FugueMax implementation with issuer births

The raw state contains a live coordinate list and a finite set of insertion
records. Its query returns a plain list. Birth-set union is independent of
delivery order. The executable issuer in `FugueMaxIssuer` can use any list
enumeration of that set; `applicable_exact` connects its check to the original
generator on coherent histories.

`FugueMaxContract` supplies the public plain-list specification and the
same-witness maximal-non-interleaving certificate for this exact signature.
-/

namespace Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax

open Sal.MRDTs.Foundation
open Sal.EmbedRGA (OrderedPrefixCode FMChain)

/-- The event envelope supplies timestamp and replica exactly once. -/
structure Payload where
  op : MOp
  lo : ℕ
  ro : Option ℕ
  chain : FMChain
  deriving DecidableEq

def recordOf (e : Op Payload) : MRec :=
  ⟨e.1, e.2.1, e.2.2.op, e.2.2.lo, e.2.2.ro, e.2.2.chain⟩

def eventOf (g : MRec) : Op Payload :=
  (g.ts, g.rep, ⟨g.op, g.lo, g.ro, g.chain⟩)

@[simp] theorem recordOf_eventOf (g : MRec) : recordOf (eventOf g) = g := rfl
@[simp] theorem eventOf_recordOf (e : Op Payload) : eventOf (recordOf e) = e := rfl

structure State where
  live : SState
  births : Finset MRec
  deriving DecidableEq

def stateOf (Γ : OrderedPrefixCode) (K : KnowM) : State :=
  ⟨mFold Γ K, (mMinted K).toFinset⟩

/-- Forget the executable issuer's storage order and duplicate records. -/
def toState (s : IssuerState) : State := ⟨s.live, s.births.toFinset⟩

@[simp] theorem toState_summarize (Γ : OrderedPrefixCode) (K : KnowM) :
    toState (summarize Γ K) = stateOf Γ K := rfl

def rawUpdate (Γ : OrderedPrefixCode) (s : State) (e : Op Payload) : State :=
  let g := recordOf e
  ⟨mStep Γ s.live g, if mIsIns g then insert g s.births else s.births⟩

def rawMerge (ancestor left right : State) : State :=
  ⟨sMerge ancestor.live left.live right.live, left.births ∪ right.births⟩

def datatype (Γ : OrderedPrefixCode) : MRDTSig where
  State := State
  dec_state := inferInstance
  init := ⟨[], ∅⟩
  AppOp := Payload
  dec_op := inferInstance
  Query := Unit
  Value := List ℕ
  update := rawUpdate Γ
  query := fun s _ => sIds s.live
  merge := rawMerge

/-- The same insertion-before-own-deletion relation as coordinate replay. -/
def rc (Γ : OrderedPrefixCode) : ReplayPolicy (datatype Γ).toUpdateSig where
  order a b := fRcOrder (fOpOfM Γ (recordOf a)) (fOpOfM Γ (recordOf b))

/-- Enumeration is only a representation witness, not additional history or
an assumed execution. The guard reads the stored births and live list. -/
def applicable (Γ : OrderedPrefixCode) (e : Op Payload) (s : State) : Prop :=
  ∃ births : KnowM, births.toFinset = s.births ∧
    canIssue Γ ⟨s.live, births⟩ (recordOf e) = true

def generation (Γ : OrderedPrefixCode) : Issuance (datatype Γ) where
  CanIssue := applicable Γ

theorem rawUpdate_exact (Γ : OrderedPrefixCode) (K : KnowM) (g : MRec) :
    rawUpdate Γ (stateOf Γ K) (eventOf g) = stateOf Γ (K ++ [g]) := by
  cases hi : mIsIns g <;>
    simp [rawUpdate, stateOf, mFold_snoc, mMinted, hi,
      Finset.union_comm]

theorem issuer_update_refines (Γ : OrderedPrefixCode) (s : IssuerState) (g : MRec) :
    rawUpdate Γ (toState s) (eventOf g) = toState (update Γ s g) := by
  cases hi : mIsIns g <;>
    simp [rawUpdate, toState, update, mMinted, hi]

theorem issuer_merge_refines (a l r : IssuerState) :
    rawMerge (toState a) (toState l) (toState r) = toState (merge a l r) := by
  unfold rawMerge toState merge
  congr 1
  ext g
  simp only [Finset.mem_union, List.mem_toFinset, syncM, List.mem_append,
    List.mem_filter, decide_eq_true_eq]
  tauto

theorem rawFold_exact (Γ : OrderedPrefixCode) (K : KnowM) :
    applySeq (datatype Γ).toUpdateSig (datatype Γ).init (K.map eventOf) = stateOf Γ K := by
  induction K using List.reverseRecOn with
  | nil => rfl
  | append_singleton K g ih =>
      simp only [List.map_append, List.map_singleton, applySeq, List.foldl_append] at *
      change rawUpdate Γ _ (eventOf g) = _
      rw [ih, rawUpdate_exact]

theorem rawMerge_births_exact (Γ : OrderedPrefixCode) (A K L : KnowM) :
    (rawMerge (stateOf Γ A) (stateOf Γ K) (stateOf Γ L)).births =
      (stateOf Γ (syncM K L)).births := by
  ext g
  simp only [rawMerge, stateOf, Finset.mem_union, List.mem_toFinset, mMinted,
    syncM, List.mem_filter, List.mem_append, decide_eq_true_eq]
  tauto

private theorem issuer_check_eq {Γ : OrderedPrefixCode} {K L : KnowM}
    (inv : KInv Γ K) (hL : L.toFinset = (mMinted K).toFinset) (g : MRec) :
    canIssue Γ ⟨mFold Γ K, L⟩ g = canIssue Γ (summarize Γ K) g := by
  have hm : ∀ b, b ∈ L ↔ b ∈ mMinted K := by
    intro b
    simpa using (Finset.ext_iff.mp hL b)
  have hmint : ∀ b, b ∈ mMinted K ↔ b ∈ mMinted L := by
    intro b
    simp only [mMinted, List.mem_filter] at hm ⊢
    constructor
    · intro h
      exact ⟨(hm b).mpr h, h.2⟩
    · intro h
      exact (hm b).mp h.1
  have hp : ∀ r t i, prepareInsert Γ ⟨mFold Γ K, L⟩ r t i =
      prepareInsert Γ (summarize Γ K) r t i := by
    intro r t i
    rw [prepareInsert_exact]
    unfold prepareInsert mGenInsAt mAnchorAt mView
    exact (genAfter_eq_of_births inv hmint r t _).symm
  apply Bool.eq_iff_iff.mpr
  cases hi : mIsIns g with
  | false =>
      rw [canIssue_delete_iff Γ _ _ hi, canIssue_delete_iff Γ _ _ hi]
      rfl
  | true =>
      rw [canIssue_insert_iff Γ _ _ hi, canIssue_insert_iff Γ _ _ hi]
      simp only [hp, summarize, hm]

/-- The finite-set signature's issuance accepts exactly the same prepared
records as the executable sufficient summary; no choice of enumeration can
authorize another operation. -/
theorem applicable_exact {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) (g : MRec) :
    applicable Γ (eventOf g) (stateOf Γ K) ↔
      canIssue Γ (summarize Γ K) g = true := by
  constructor
  · rintro ⟨L, hL, hg⟩
    change canIssue Γ ⟨mFold Γ K, L⟩ g = true at hg
    rwa [issuer_check_eq inv hL] at hg
  · intro hg
    exact ⟨mMinted K, rfl, hg⟩

theorem insertion_issuance_exact {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) (g : MRec) (hi : mIsIns g = true) :
    applicable Γ (eventOf g) (stateOf Γ K) ↔ 0 < g.ts ∧
      (∀ t ∈ mMintedIds K, t < g.ts) ∧ ∃ i, g = mGenInsAt Γ K g.rep g.ts i := by
  rw [applicable_exact inv, canIssue_insert_exact Γ K g hi]

theorem deletion_issuance_exact {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) (g : MRec) (hi : mIsIns g = false) :
    applicable Γ (eventOf g) (stateOf Γ K) ↔
      0 < g.ts ∧ ∃ i, g = mGenDelAt Γ K g.rep g.ts i := by
  rw [applicable_exact inv, canIssue_delete_exact Γ K g hi]

#print axioms insertion_issuance_exact
#print axioms deletion_issuance_exact
#print axioms rawUpdate_exact
#print axioms rawFold_exact
#print axioms issuer_merge_refines

end Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax
