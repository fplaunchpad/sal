import Sal.MRDTs.Metatheory.CertifiedAdequacy
import Sal.MRDTs.Metatheory.Join.RA_Lin_Of_Join

/-! Observable correctness target for ternary MRDT configurations. -/

namespace Sal.MRDTs

open Sal.MRDTs.Foundation

/-- Every registered version is the datatype fold of a linearization of its
event set respecting one proof-local replay policy.

This is an internal replay/convergence property.  It does not say that the
witness is prefix-legal for a client-facing sequential specification. -/
def IsRALinearizableWith (D : MRDTSig)
    (P : ReplayPolicy D.toCRDTSig) (C : Configuration D) : Prop :=
  ∀ (v : Version) (s : D.State) (E : Set (Op D.AppOp)),
    C.ver v = some (s, E) →
    ∃ π : List (Op D.AppOp),
      listPermOf π E ∧
      respects π (@Sal.MRDTs.Foundation.lo D.toCRDTSig P C.core) ∧
      applySeq D.toCRDTSig D.init π = s

/-- Certified internal replay convergence uses the generic Join development's
unconstrained policy. Datatype intent is stated independently by
`InteractionSpec`; `IsRALinearizableWith` remains available as an internal
research hook for alternative replay proofs. -/
abbrev IsRALinearizable (D : MRDTSig) (C : Configuration D) : Prop :=
  IsRALinearizableWith D (ReplayPolicy.default D.toCRDTSig) C

/-- Explicit name for the replay theorem supplied by the existing Join
metatheory.  Keep `IsRALinearizable` as a compatibility alias while datatype
certificates migrate to `IsSpecRALinearizable`. -/
abbrev IsInternallyRALinearizable := IsRALinearizable

/-- Every internal global replay order extends the raw semantic interaction
constraints. The public relation is set-relative and drops the internal
resolver's concurrent edges; causal concrete conflicts are retained. -/
theorem respects_interactionLoOn_raw_of_lo {D : MRDTSig}
    {C : Configuration D} {E : Set (Op D.AppOp)}
    {π : List (Op D.AppOp)}
    (h : respects π (Sal.MRDTs.Foundation.lo C.core)) :
    respects π (interactionLoOn (InteractionSpec.raw D) C.core E) := by
  unfold respects at h ⊢
  exact h.imp fun {a b} hab hba => hab (Or.inl
    ((InteractionSpec.interactionLoOn_raw D C.core E b a).mp hba))

/-- Client-facing RA correctness.  The witness contains exactly the events
of the version, respects the framework order, is accepted by the independent
sequential specification, and agrees with its state and observations. -/
def IsSpecRALinearizable (D : MRDTSig) (A : InteractionSpec D)
    (S : SequentialSpec D)
    (Rel : D.State → S.State → Prop)
    (C : Configuration D) : Prop :=
  ∀ (v : Version) (s : D.State) (E : Set (Op D.AppOp)),
    C.ver v = some (s, E) →
    ∃ π : List (Op D.AppOp),
      listPermOf π E ∧
      respects π (interactionLoOn A C.core E) ∧
      S.Legal π ∧
      Rel s (S.run π) ∧
      ∀ query, D.query s query = S.query (S.run π) query

/-- Lift internal replay when every candidate history is legal and the
sequential relation holds for every raw fold.  This discharges flat/total
datatypes and is also a useful control: genuinely conditioned datatypes
cannot use it unless they prove its two explicit premises. -/
theorem IsRALinearizable.toSpec {D : MRDTSig} {C : Configuration D}
    {S : SequentialSpec D} {Rel : D.State → S.State → Prop}
    (h : IsRALinearizable D C)
    (legal : ∀ ops, S.Legal ops)
    (refines : ∀ ops,
      Rel (applySeq D.toCRDTSig D.init ops) (S.run ops))
    (observes : ∀ ops query,
      D.query (applySeq D.toCRDTSig D.init ops) query =
        S.query (S.run ops) query) :
    IsSpecRALinearizable D (InteractionSpec.raw D) S Rel C := by
  intro v s E hver
  obtain ⟨π, hperm, hresp, hfold⟩ := h v s E hver
  have hsemantic := respects_interactionLoOn_raw_of_lo (E := E) hresp
  refine ⟨π, hperm, hsemantic, legal π, ?_, ?_⟩
  · simpa [hfold] using refines π
  · intro query
    simpa [hfold] using observes π query

/-- The generic Join development uses the unconstrained replay policy. An
internal experiment may prove `IsRALinearizableWith` for another policy
directly; this bridge deliberately makes no stronger claim. -/
theorem isRALinearizableWith_iff_join (D : MRDTSig)
    (C : Configuration D) :
    IsRALinearizableWith D (ReplayPolicy.default D.toCRDTSig) C ↔
      IsRALinearizableJoin C := Iff.rfl

/-- Package the generic Join theorem behind the internal replay interface. The
chosen default is an implementation detail and does not enter the public
interaction order or sequential-correctness statement. -/
theorem isRALinearizable_of_join {D : MRDTSig} {C : Configuration D}
    (h : IsRALinearizableJoin C) : IsRALinearizable D C :=
  (isRALinearizableWith_iff_join D C).mpr h

/-- Internal replay convergence for issuance-certified widened execution.
Ordinary execution embeds in this semantics, so its theorem is derived.
Datatype-specific Join proofs derive any history facts they need directly from
`MintHonest`. -/
structure ConvergenceCertificate (D : MRDTSig) (I : Issuance D) where
  soundV : ∀ {C},
    MintCertifiedReachV D (canonicalVirtualLCA D) I C →
      IsRALinearizable D C

namespace ConvergenceCertificate

/-- Ordinary convergence is the base case of widened convergence. -/
theorem sound {D : MRDTSig} {I : Issuance D}
    (K : ConvergenceCertificate D I) {C : Configuration D}
    (h : MintCertifiedReach D I C) : IsRALinearizable D C :=
  K.soundV h.toV

end ConvergenceCertificate

/-- The two execution modes accepted by the public theorem.  Datatype
legalization needs operational facts (most importantly, causal closure of
each stored version) that do not follow from an arbitrary replay witness.
Packaging the modes here lets one datatype theorem serve both semantics. -/
inductive CertifiedExecution (D : MRDTSig) (I : Issuance D)
    (C : Configuration D) : Prop where
  | ordinary : MintCertifiedReach D I C → CertifiedExecution D I C
  | virtual : MintCertifiedReachV D (canonicalVirtualLCA D) I C →
      CertifiedExecution D I C

theorem CertifiedExecution.mintHonest {D : MRDTSig} {I : Issuance D}
    {C : Configuration D} (h : CertifiedExecution D I C) :
    MintHonest D I.CanIssue C := by
  cases h with
  | ordinary reach => exact reach.mintHonest
  | virtual reach => exact reach.mintHonest

theorem CertifiedExecution.goodConfig {D : MRDTSig}
    {I : Issuance D} {C : Configuration D}
    (join : ∀ C, MintHonest D I.CanIssue C → JoinLemma3At D C.core)
    (h : CertifiedExecution D I C) : GoodConfig3 C := by
  cases h with
  | ordinary reach => exact goodConfig_of_mintCertified join reach
  | virtual reach => exact goodConfig_of_mintCertifiedV join reach

/-- Datatype-specific bridge from internal replay to client-facing
correctness. The framework applies this one theorem to both ordinary and virtual-LCA
executions, so the verification package does not store duplicate proofs. -/
structure SequentialCorrectnessCertificate (D : MRDTSig)
    (I : Issuance D) (A : InteractionSpec D)
    (S : SequentialSpec D)
    (Rel : D.State → S.State → Prop) where
  sound : ∀ C, CertifiedExecution D I C → IsRALinearizable D C →
    IsSpecRALinearizable D A S Rel C

/-- Total datatypes discharge legalization directly: every list is legal and
every raw fold refines the sequential state and its observations. -/
def SequentialCorrectnessCertificate.ofTotal {D : MRDTSig}
    {I : Issuance D} {S : SequentialSpec D}
    {Rel : D.State → S.State → Prop}
    (legal : ∀ ops, S.Legal ops)
    (refines : ∀ ops,
      Rel (applySeq D.toCRDTSig D.init ops) (S.run ops))
    (observes : ∀ ops query,
      D.query (applySeq D.toCRDTSig D.init ops) query =
        S.query (S.run ops) query) :
    SequentialCorrectnessCertificate D I (InteractionSpec.raw D) S Rel where
  sound _ _ replay := replay.toSpec legal refines observes

/-- Internal compatibility package for raw-fold refinement. It remains while
older instances migrate, but it is not the public sequential-correctness API. -/
structure ReplayVerifiedMRDT (D : MRDTSig) where
  issuance : Issuance D
  convergence : ConvergenceCertificate D issuance
  Machine : SequentialMachine (Op D.AppOp)
  sequential : SequentialRefinement D Machine
  sequential_of_mint : ∀ ops,
    LinearMintHistory D issuance.CanIssue ops → sequential.Honest ops

/-- Complete public sequential-correctness package. Issuance constrains only origin
operation creation; `Spec.Legal` independently defines acceptable sequential
histories. Reachable-state arbitration is a separate certificate; it does not
leak implementation state into the sequential specification. Safety and state
GC remain separate optional certificates. -/
structure VerifiedMRDT (D : MRDTSig) where
  issuance : Issuance D
  interaction : InteractionSpec D
  convergence : ConvergenceCertificate D issuance
  Spec : SequentialSpec D
  Rel : D.State → Spec.State → Prop
  sequentialCorrectness :
    SequentialCorrectnessCertificate D issuance interaction Spec Rel

/-- The only admissible production-registry entry. Raw signatures,
replay-only packages, SPOTs, and countermodels cannot inhabit this type unless
they supply the complete public certificate for the exact signature. -/
structure PackagedMRDT where
  name : String
  D : MRDTSig
  certificate : VerifiedMRDT D

namespace PackagedMRDT

noncomputable def of (name : String) {D : MRDTSig}
    (certificate : VerifiedMRDT D) : PackagedMRDT :=
  ⟨name, D, certificate⟩

end PackagedMRDT

namespace ReplayVerifiedMRDT

variable {D : MRDTSig} (V : ReplayVerifiedMRDT D)

theorem converges {C : Configuration D}
    (h : MintCertifiedReach D V.issuance C) :
    IsRALinearizable D C :=
  V.convergence.sound h

theorem convergesV {C : Configuration D}
    (h : MintCertifiedReachV D (canonicalVirtualLCA D) V.issuance C) :
    IsRALinearizable D C :=
  V.convergence.soundV h

theorem sequentially_correct (ops : List (Op D.AppOp))
    (h : LinearMintHistory D V.issuance.CanIssue ops) :
    V.sequential.Rel (applySeq D.toCRDTSig D.init ops) (V.Machine.run ops) :=
  V.sequential.sound ops (V.sequential_of_mint ops h)

end ReplayVerifiedMRDT

namespace VerifiedMRDT

variable {D : MRDTSig} (V : VerifiedMRDT D)

theorem converges {C : Configuration D}
    (h : MintCertifiedReach D V.issuance C) :
    IsSpecRALinearizable D V.interaction V.Spec V.Rel C :=
  V.sequentialCorrectness.sound C
    (.ordinary h)
    (V.convergence.sound h)

theorem convergesV {C : Configuration D}
    (h : MintCertifiedReachV D (canonicalVirtualLCA D) V.issuance C) :
    IsSpecRALinearizable D V.interaction V.Spec V.Rel C :=
  V.sequentialCorrectness.sound C
    (.virtual h)
    (V.convergence.soundV h)

end VerifiedMRDT

end Sal.MRDTs
