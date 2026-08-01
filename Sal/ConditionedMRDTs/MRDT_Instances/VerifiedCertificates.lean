import Sal.ConditionedMRDTs.Metatheory.VerifiedMRDT
import Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA_SeqSpec
import Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA_MultiEpoch
import Sal.ConditionedMRDTs.MRDT_Instances.SidedRGA.SidedRGA_SeqSpec
import Sal.ConditionedMRDTs.MRDT_Instances.MergeableQueue.MergeableQueue_SeqSpec

/-!
# Production verified-datatype certificates

These packages connect the reusable metatheory to three nontrivial instances.
Their sequential claims are history-conditioned because freshness and
applicability are properties of the issuing prefix, not of an arbitrary raw
update.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Sal.EmbedRGA (OrderedPrefixCode)

section Embed

variable {α : Type} [DecidableEq α] [Inhabited α]

def embedSequentialSpec : SequentialSpec (Op (EOp α)) where
  State := List (ℕ × α)
  init := []
  step := eSpecStep

def embedSequentialRefinement (Γ : OrderedPrefixCode) :
    HistorySequentialRefinement (E Γ α) embedSequentialSpec where
  Honest := eSeqOK Γ
  Rel s q := s.map eProj = q
  init := rfl
  sound := by
    intro ops h
    simpa [embedSequentialSpec, SequentialSpec.run, eSpecFold, eFold] using
      (embed_seq_sound (Γ := Γ) h)

/-- End-to-end convergence and sequential-intent certificate for EmbedRGA. -/
def embedVerified (Γ : OrderedPrefixCode) : VerifiedMRDT (E Γ α) where
  Honest := EHonestCore Γ
  initInv := trivial
  join := fun _ h => e_join_kit_at h
  Spec := embedSequentialSpec
  seq := embedSequentialRefinement Γ

/-- The production runtime callback for EmbedRGA.  Its admissibility contract
is precisely the at-rest-domain and future-mint discipline used by the recoding
theorem; old operations are translated together with the compacted state. -/
def embedRuntime (Γ : OrderedPrefixCode) :
    RuntimeRecoding (E Γ α) (StablePrefixMap Γ) where
  Obs := List α
  compact F := eRemapSt F.f
  translate F := eRemapOp F.f
  observe s := (E Γ α).query s ()
  Admissible F (s : EState α) ops :=
    (∀ x ∈ s, F.Dom x.2.2) ∧
    (∀ o ∈ ops, ∀ (e : α) (π : List Bool) (a : ℕ),
      o.2.2 = EOp.ins e π a → F.MintAt π (o.1 - a))
  sound := by
    intro F s ops h
    exact eRecode_reads_identical F s ops h.1 h.2

/-- EmbedRGA with convergence, sequential intent, and runtime recoding in one
certificate. -/
def embedVerifiedRuntime (Γ : OrderedPrefixCode) :
    VerifiedRuntimeMRDT (E Γ α) (StablePrefixMap Γ) where
  toVerifiedMRDT := embedVerified Γ
  runtime := embedRuntime Γ

/-- The concrete n-epoch use of the packaged runtime certificate: a compatible
chain is collapsed to its certified composite recoding. -/
theorem embedVerifiedRuntime_multiEpoch (Γ : OrderedPrefixCode)
    (F : StablePrefixMap Γ) (Fs : List (StablePrefixMap Γ))
    (hchain : CompatChain (F :: Fs)) (s : EState α)
    (ops : List (Op (EOp α)))
    (hrest : ∀ x ∈ s, F.Dom x.2.2)
    (hops : ∀ o ∈ ops, ∀ (e : α) (π : List Bool) (a : ℕ),
      o.2.2 = EOp.ins e π a → F.MintAt π (o.1 - a)) :
    (E Γ α).query
        (applySeq (E Γ α).toCRDTSig
          (eRemapSt (chainSPM F Fs hchain).f s)
          (ops.map (eRemapOp (chainSPM F Fs hchain).f))) () =
      (E Γ α).query (applySeq (E Γ α).toCRDTSig s ops) () := by
  apply (embedVerifiedRuntime Γ).compact_continuation
  exact ⟨hrest, hops⟩

end Embed

section Sided

def sidedSequentialSpec : SequentialSpec (Op SOp) where
  State := List (ℕ × ℕ)
  init := [(0, 0)]
  step := sSpecStep

def sidedSequentialRefinement (Γ : OrderedPrefixCode) :
    HistorySequentialRefinement (S Γ) sidedSequentialSpec where
  Honest := sSeqOK Γ
  Rel s q := s.map sProj = q.filter (fun p => decide (p.1 ≠ 0))
  init := rfl
  sound := by
    intro ops h
    simpa [sidedSequentialSpec, SequentialSpec.run, sSpecFold, sFold] using
      (sided_seq_read (Γ := Γ) h)

/-- End-to-end certificate for the two-sided embedded-chain RGA. -/
def sidedVerified (Γ : OrderedPrefixCode) : VerifiedMRDT (S Γ) where
  Honest := SHonestCore Γ
  initInv := trivial
  join := fun C h => (joinKitAt_plain_iff (S Γ) C).2 (s_join_at h)
  Spec := sidedSequentialSpec
  seq := sidedSequentialRefinement Γ

end Sided

section Queue

def queueSequentialSpec : SequentialSpec (Op QOp) where
  State := List ℕ
  init := []
  step := qSpecStep

def queueSequentialRefinement :
    HistorySequentialRefinement Q queueSequentialSpec where
  Honest := qOK
  Rel s q := s.map Prod.snd = q
  init := rfl
  sound := by
    intro ops h
    simpa [queueSequentialSpec, SequentialSpec.run, qSpecFold, seqFold] using
      (queue_seq_sound h)

/-- End-to-end certificate for the mergeable FIFO queue. -/
def queueVerified : VerifiedMRDT Q where
  Honest := QHonestCore
  initInv := trivial
  join := fun C h => (joinKitAt_plain_iff Q C).2 (q_join_at h)
  Spec := queueSequentialSpec
  seq := queueSequentialRefinement

end Queue

section ProductDemo

variable {α : Type} [DecidableEq α] [Inhabited α]

/-- A concrete reusable product certificate: an EmbedRGA document and a FIFO
queue share one interleaved operation history. -/
def embedQueueVerified (Γ : OrderedPrefixCode) :
    VerifiedMRDT (prodSig (E Γ α) Q) :=
  VerifiedMRDT.prod (embedVerified Γ) queueVerified

end ProductDemo

#print axioms embedVerified
#print axioms embedVerifiedRuntime
#print axioms embedVerifiedRuntime_multiEpoch
#print axioms sidedVerified
#print axioms queueVerified
#print axioms embedQueueVerified

end Sal.ConditionedMRDTs
