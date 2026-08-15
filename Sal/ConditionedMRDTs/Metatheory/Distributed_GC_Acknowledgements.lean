import Sal.ConditionedMRDTs.Metatheory.Distributed_GC

/-!
# Fetch-aligned epoch acknowledgements

An acknowledgement is protocol metadata. It does not mint an RDT operation or
change a replica's commit holding, head, or state. The receiver accepts a
receipt only for a version it holds and that the sender advertised as its
current head. A transport authentication layer binds `peer` to the sender.

`PruneEvidence` is datatype-independent. It accepts the existing authored
frontier evidence or a checked fetch receipt whose advertised head is past the
candidate epoch cut. The caller supplies `pastCut`; the cut-keyed runtime uses
`EpochDag.subcut`.
-/

namespace Sal.ConditionedMRDTs

open Classical
open Sal.Emulation

section Acknowledgements

variable {parents : Version → List Version}

/-- Receipts observed locally: observer, authenticated peer, advertised head. -/
abbrev ReceiptBook := Replica → Replica → Set Version

/-- A receipt is accepted only when the observer holds the advertised current
head. This is the formal boundary corresponding to the runtime's content-id and
epoch recomputation checks. -/
def ValidFetchReceipt (W : DistributedWorld)
    (observer peer : Replica) (v : Version) : Prop :=
  v = (W peer).head ∧ v ∈ (W observer).commits

/-- Add one authenticated receipt. Receipt storage is monotone. -/
def acknowledge (B : ReceiptBook) (observer peer : Replica) (v : Version) :
    ReceiptBook :=
  Function.update B observer
    (Function.update (B observer) peer (B observer peer ∪ {v}))

theorem acknowledge_contains (B : ReceiptBook) (observer peer : Replica)
    (v : Version) : v ∈ acknowledge B observer peer v observer peer := by
  simp [acknowledge]

theorem acknowledge_mono (B : ReceiptBook) (observer peer : Replica)
    (v : Version) :
    B observer peer ⊆ acknowledge B observer peer v observer peer := by
  intro x hx
  simpa [acknowledge] using (show x ∈ B observer peer ∪ {v} from Or.inl hx)

/-- The protocol state separates semantic execution from receipt metadata. -/
structure AcknowledgedWorld where
  core : DistributedWorld
  receipts : ReceiptBook

/-- A checked acknowledgement step changes only protocol metadata. -/
def acknowledgeStep (S : AcknowledgedWorld) (observer peer : Replica)
    (v : Version) (_valid : ValidFetchReceipt S.core observer peer v) :
    AcknowledgedWorld where
  core := S.core
  receipts := acknowledge S.receipts observer peer v

/-- Machine-checked refinement: acknowledgement is silent in the basic no-GC
semantics. It cannot change any datatype state, head, commit, merge, or read. -/
theorem acknowledge_erases (S : AcknowledgedWorld)
    (observer peer : Replica) (v : Version)
    (h : ValidFetchReceipt S.core observer peer v) :
    (acknowledgeStep S observer peer v h).core = S.core := rfl

/-- The combined protocol either advances the existing distributed semantics
or records one checked fetch receipt. -/
inductive AcknowledgedStep (parents : Version → List Version) :
    AcknowledgedWorld → AcknowledgedWorld → Prop where
  | core (S : AcknowledgedWorld) {W' : DistributedWorld}
      (step : DistributedStep parents S.core W') :
      AcknowledgedStep parents S ⟨W', S.receipts⟩
  | receipt (S : AcknowledgedWorld) (observer peer : Replica) (v : Version)
      (valid : ValidFetchReceipt S.core observer peer v) :
      AcknowledgedStep parents S (acknowledgeStep S observer peer v valid)

/-- One combined step refines the no-GC semantics. A core step reuses the
existing theorem; a receipt step stutters. -/
theorem acknowledgedStep_refines_noGC {F : DistributedWorld}
    {S S' : AcknowledgedWorld} (hSim : WorldSim F S.core)
    (hStep : AcknowledgedStep parents S S') :
    ∃ F', NoGCMatch F F' ∧ WorldSim F' S'.core := by
  cases hStep with
  | core step => exact distributed_refines_noGC parents hSim step
  | receipt observer peer v valid =>
      exact ⟨F, NoGCMatch.refl F, hSim⟩

/-- Finite executions of core and receipt steps. -/
inductive AcknowledgedSteps (parents : Version → List Version) :
    AcknowledgedWorld → AcknowledgedWorld → Prop where
  | refl (S : AcknowledgedWorld) : AcknowledgedSteps parents S S
  | tail {S₀ S₁ S₂ : AcknowledgedWorld}
      (run : AcknowledgedSteps parents S₀ S₁)
      (last : AcknowledgedStep parents S₁ S₂) :
      AcknowledgedSteps parents S₀ S₂

/-- Execution-level refinement. Any finite interleaving of fetch, head-sync,
local GC, and acknowledgements has a no-GC execution with a related final
core. Receipt traffic is erased and cannot affect reads. -/
theorem acknowledged_execution_refines_noGC {F₀ : DistributedWorld}
    {S₀ S₁ : AcknowledgedWorld} (hSim : WorldSim F₀ S₀.core)
    (hRun : AcknowledgedSteps parents S₀ S₁) :
    ∃ F₁, NoGCSteps F₀ F₁ ∧ WorldSim F₁ S₁.core := by
  induction hRun generalizing F₀ with
  | refl => exact ⟨F₀, NoGCSteps.refl F₀, hSim⟩
  | tail run last ih =>
      rcases ih hSim with ⟨F₁, hSteps, hSim₁⟩
      rcases acknowledgedStep_refines_noGC (parents := parents) hSim₁ last with
        ⟨F₂, hMatch, hSim₂⟩
      exact ⟨F₂, hSteps.append_match hMatch, hSim₂⟩

/-- Evidence that licenses history pruning at `cut`. Existing authored
frontier evidence remains sufficient. A quiescent peer can instead supply a
checked fetch receipt for an advertised head past the cut. -/
def PruneEvidence (pastCut : Version → Version → Prop)
    (L : DistributedLocal) (B : ReceiptBook)
    (cut : Version) : Prop :=
  ∀ peer ∈ L.roster, peer = L.self ∨
    (∃ v, v ∈ DerivedEvidence parents L peer ∧ pastCut cut v) ∨
    (∃ v, v ∈ B L.self peer ∧ v ∈ L.commits ∧ pastCut cut v)

theorem pruneEvidence_of_authored (pastCut : Version → Version → Prop)
    (L : DistributedLocal) (B : ReceiptBook) (cut : Version)
    (h : ∀ peer ∈ L.roster, peer = L.self ∨
      ∃ v, v ∈ DerivedEvidence parents L peer ∧ pastCut cut v) :
    PruneEvidence (parents := parents) pastCut L B cut := by
  intro peer hp
  rcases h peer hp with hs | ⟨v, hv, hcut⟩
  · exact Or.inl hs
  · exact Or.inr (Or.inl ⟨v, hv, hcut⟩)

/-- Liveness step: once every non-self roster member has a locally held receipt
past the cut, pruning evidence is complete without requiring a new RDT op. -/
theorem pruneEvidence_of_receipts (pastCut : Version → Version → Prop)
    (L : DistributedLocal) (B : ReceiptBook) (cut : Version)
    (h : ∀ peer ∈ L.roster, peer ≠ L.self →
      ∃ v, v ∈ B L.self peer ∧ v ∈ L.commits ∧ pastCut cut v) :
    PruneEvidence (parents := parents) pastCut L B cut := by
  intro peer hp
  by_cases hs : peer = L.self
  · exact Or.inl hs
  · exact Or.inr (Or.inr (h peer hp hs))

/-- FAIL control: an empty receipt book cannot manufacture evidence for a
non-self member when no authored evidence exists. -/
theorem no_pruneEvidence_without_authored_or_receipt
    (pastCut : Version → Version → Prop)
    (L : DistributedLocal) (cut : Version)
    (peer : Replica) (hp : peer ∈ L.roster) (hne : peer ≠ L.self)
    (ha : ¬ ∃ v, v ∈ DerivedEvidence parents L peer ∧ pastCut cut v) :
    ¬ PruneEvidence (parents := parents) pastCut L (fun _ _ => ∅) cut := by
  intro h
  rcases h peer hp with hs | ha' | hr
  · exact hne hs
  · exact ha ha'
  · rcases hr with ⟨v, hv, _⟩
    exact hv

end Acknowledgements

end Sal.ConditionedMRDTs
