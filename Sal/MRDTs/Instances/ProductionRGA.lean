import Sal.MRDTs.Instances.EmbedRGASequential
import Sal.MRDTs.Instances.SidedEmbedRGASequential

/-! Complete paper-facing certificates for the one- and two-sided embedded
RGAs. -/

namespace Sal.MRDTs.Instances.ProductionRGA

open Sal.Emulation
open Sal.EmbedRGA (OrderedPrefixCode)

variable {α : Type} [DecidableEq α] [Inhabited α]

def embedSpec : SequentialSpec (Op (Sal.MRDTs.Instances.EmbedRGA.EOp α)) where
  State := List (ℕ × α)
  init := []
  step := Sal.MRDTs.Instances.EmbedRGA.eSpecStep

def embedSequential (Γ : OrderedPrefixCode) :
    SequentialRefinement (Sal.MRDTs.Instances.EmbedRGA.E Γ α) embedSpec where
  Honest := Sal.MRDTs.Instances.EmbedRGA.eSeqOK Γ
  Rel s q := s.map Sal.MRDTs.Instances.EmbedRGA.eProj = q
  init := rfl
  sound := by
    intro ops h
    simpa [embedSpec, SequentialSpec.run, Sal.MRDTs.Instances.EmbedRGA.eSpecFold, Sal.MRDTs.Instances.EmbedRGA.eFold] using
      (Sal.MRDTs.Instances.EmbedRGA.embed_seq_sound (Γ := Γ) h)

theorem embedSequential_of_mint {Γ : OrderedPrefixCode}
    {ops : List (Op (Sal.MRDTs.Instances.EmbedRGA.EOp α))}
    (h : LinearMintHistory (Sal.MRDTs.Instances.EmbedRGA.E Γ α) Sal.MRDTs.Instances.EmbedRGA.eApplicable ops) : Sal.MRDTs.Instances.EmbedRGA.eSeqOK Γ ops := by
  intro pre e post heq
  refine ⟨?_, h.guarded pre e post heq⟩
  intro x hx
  obtain ⟨old, hold, _hins, htime⟩ := Sal.MRDTs.Instances.EmbedRGA.mem_eInsIds.mp hx
  rw [← htime]
  exact h.clocked pre e post heq old hold

noncomputable def embed (Γ : OrderedPrefixCode) : VerifiedMRDT (Sal.MRDTs.Instances.EmbedRGA.E Γ α) where
  generation := Sal.MRDTs.Instances.EmbedRGA.generation Γ
  convergence := Sal.MRDTs.Instances.EmbedRGA.convergence Γ
  Spec := embedSpec
  sequential := embedSequential Γ
  sequential_of_mint := fun _ h => embedSequential_of_mint h
  safety := SafetyCertificate.trivial (Sal.MRDTs.Instances.EmbedRGA.generation Γ)

def sidedSpec : SequentialSpec (Op Sal.MRDTs.Instances.SidedEmbedRGA.SOp) where
  State := List (ℕ × ℕ)
  init := [(0, 0)]
  step := Sal.MRDTs.Instances.SidedEmbedRGA.sSpecStep

def sidedSequential (Γ : OrderedPrefixCode) :
    SequentialRefinement (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ) sidedSpec where
  Honest := Sal.MRDTs.Instances.SidedEmbedRGA.sSeqOK Γ
  Rel s q := s.map Sal.MRDTs.Instances.SidedEmbedRGA.sProj = q.filter (fun p => decide (p.1 ≠ 0))
  init := rfl
  sound := by
    intro ops h
    simpa [sidedSpec, SequentialSpec.run, Sal.MRDTs.Instances.SidedEmbedRGA.sSpecFold, Sal.MRDTs.Instances.SidedEmbedRGA.sFold] using
      (Sal.MRDTs.Instances.SidedEmbedRGA.sided_seq_read (Γ := Γ) h)

theorem sidedSequential_of_mint {Γ : OrderedPrefixCode}
    {ops : List (Op Sal.MRDTs.Instances.SidedEmbedRGA.SOp)}
    (h : LinearMintHistory (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ) Sal.MRDTs.Instances.SidedEmbedRGA.sApplicable ops) : Sal.MRDTs.Instances.SidedEmbedRGA.sSeqOK Γ ops := by
  intro pre e post heq
  refine ⟨?_, h.guarded pre e post heq⟩
  intro x hx
  obtain ⟨old, hold, _hins, htime⟩ := Sal.MRDTs.Instances.SidedEmbedRGA.mem_sInsIds.mp hx
  rw [← htime]
  exact h.clocked pre e post heq old hold

noncomputable def sided (Γ : OrderedPrefixCode) : VerifiedMRDT (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ) where
  generation := Sal.MRDTs.Instances.SidedEmbedRGA.generation Γ
  convergence := Sal.MRDTs.Instances.SidedEmbedRGA.convergence Γ
  Spec := sidedSpec
  sequential := sidedSequential Γ
  sequential_of_mint := fun _ h => sidedSequential_of_mint h
  safety := SafetyCertificate.trivial (Sal.MRDTs.Instances.SidedEmbedRGA.generation Γ)

#print axioms embed
#print axioms sided

end Sal.MRDTs.Instances.ProductionRGA

