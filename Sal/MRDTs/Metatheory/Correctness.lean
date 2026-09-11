import Sal.MRDTs.Metatheory.CertifiedAdequacy
import Sal.MRDTs.Metatheory.Safety

/-! Replay adequacy and client-facing correctness for ternary MRDT configurations. -/

namespace Sal.MRDTs

open Sal.MRDTs.Foundation

/-- Every registered version is the datatype fold of a linearization of its
event set respecting one proof-local replay policy.

This is an internal replay-adequacy property. It does not say that the
witness is prefix-legal for a client-facing sequential specification. -/
def HasReplayWitnessWith (D : MRDTSig)
    (P : ReplayPolicy D.toUpdateSig) (C : Configuration D) : Prop :=
  ∀ (v : Version) (s : D.State) (E : Set (Op D.AppOp)),
    C.ver v = some (s, E) →
    ∃ π : List (Op D.AppOp),
      listPermOf π E ∧
      respects π (@loOn D.toUpdateSig P C.replayContext E) ∧
      applySeq D.toUpdateSig D.init π = s

/-- Acyclic `rc` plus the absorber clause yields a finite witness for the sole
visibility-plus-`rc` order. -/
theorem exists_loOn_respecting_perm_of_rcAcyclic {D : MRDTSig}
    (P : ReplayPolicy D.toUpdateSig) (hRc : @RcAcyclic D.toUpdateSig P)
    {C : ReplayContext D.toUpdateSig}
    (h_vis_trans : ∀ {a b c : Op D.AppOp},
      C.vis a b → C.vis b c → C.vis a c)
    (h_vis_irrefl : ∀ a : Op D.AppOp, ¬ C.vis a a)
    {E : Set (Op D.AppOp)} {l : List (Op D.AppOp)}
    (hperm : listPermOf l E) (h_in_C : ∀ a ∈ E, a ∈ C.events) :
    ∃ ρ, listPermOf ρ E ∧ respects ρ (@loOn D.toUpdateSig P C E) := by
  letI : ReplayPolicy D.toUpdateSig := P
  exact exists_loOn_respecting_perm_of_acyclic hperm
    (loOnNe_acyclic_of_rcAcyclic hRc h_vis_trans h_vis_irrefl h_in_C)

/-- Client-facing sequential correctness. The witness contains exactly the events
of the version, respects the framework order, is accepted by the independent
sequential specification, and agrees with its state and observations. -/
def IsSpecLinearizable (D : MRDTSig) (P : ReplayPolicy D.toUpdateSig)
    (S : SequentialSpec D)
    (Rel : D.State → S.State → Prop)
    (C : Configuration D) : Prop :=
  ∀ (v : Version) (s : D.State) (E : Set (Op D.AppOp)),
    C.ver v = some (s, E) →
    ∃ π : List (Op D.AppOp),
      listPermOf π E ∧
      respects π (@loOn D.toUpdateSig P C.replayContext E) ∧
      S.Legal π ∧
      Rel s (S.run π) ∧
      ∀ query, D.query s query = S.query (S.run π) query

/-- Lift internal replay when every candidate history is legal and the
sequential relation holds for every raw fold.  This discharges flat/total
datatypes and is also a useful control: genuinely conditioned datatypes
cannot use it unless they prove its two explicit premises. -/
theorem CausalCanonical.toSpec {D : MRDTSig} {C : Configuration D}
    {S : SequentialSpec D} {Rel : D.State → S.State → Prop}
    (h : CausalCanonical C)
    (legal : ∀ ops, S.Legal ops)
    (refines : ∀ ops,
      Rel (applySeq D.toUpdateSig D.init ops) (S.run ops))
    (observes : ∀ ops query,
      D.query (applySeq D.toUpdateSig D.init ops) query =
        S.query (S.run ops) query) :
    IsSpecLinearizable D (ReplayPolicy.unconstrained D.toUpdateSig) S Rel C := by
  intro v s E hver
  obtain ⟨π, hperm, hvis, hlo, hfold⟩ := h v s E hver
  refine ⟨π, hperm, hlo, legal π, ?_, ?_⟩
  · simpa [hfold] using refines π
  · intro query
    simpa [hfold] using observes π query

/-- The generic Join development uses the unconstrained replay policy. An
internal experiment may prove `HasReplayWitnessWith` for another policy
directly; this bridge deliberately makes no stronger claim. -/
theorem hasReplayWitnessWith_default (D : MRDTSig)
    (C : Configuration D) :
    HasReplayWitnessWith D (ReplayPolicy.default D.toUpdateSig) C ↔
      HasReplayWitness C := Iff.rfl

/-- Internal replay adequacy for issuance-certified widened execution.
Ordinary execution embeds in this semantics, so its theorem is derived.
Datatype-specific Join proofs derive any history facts they need directly from
`MintHonest`. -/
structure ReplayAdequacyCertificate (D : MRDTSig) (I : Issuance D)
    [P : ReplayPolicy D.toUpdateSig] where
  soundV : ∀ {C},
    MintCertifiedReachV D (canonicalVirtualMergeBase D) I C →
      @HasReplayWitness D P C

namespace ReplayAdequacyCertificate

/-- An all-context Join yields replay adequacy for any issuance policy. Issuance
evidence is erased before applying the raw widened adequacy theorem. -/
def ofJoin {D : MRDTSig} (I : Issuance D) {P : ReplayPolicy D.toUpdateSig}
    (hJoin : @Join D P) : @ReplayAdequacyCertificate D I P where
  soundV := fun h => replayWitnessV_of_join hJoin _ h.toReachable

/-- A Join theorem restricted by `Good` yields replay adequacy when issuance
consistency establishes that replay-context predicate. -/
def ofJoinOn {D : MRDTSig} {I : Issuance D} {P : ReplayPolicy D.toUpdateSig}
    {Good : Sal.MRDTs.Foundation.ReplayContext D.toUpdateSig → Prop}
    (hJoin : @JoinOn D P Good)
    (hEstablishes : IssuanceEstablishes D I Good) :
    @ReplayAdequacyCertificate D I P where
  soundV := fun h => replayWitness_of_mintCertifiedV
    (fun C hMint => hJoin C.replayContext (hEstablishes C hMint)) h

/-- Ordinary replay adequacy is the base case of widened replay adequacy. -/
theorem sound {D : MRDTSig} {I : Issuance D} {P : ReplayPolicy D.toUpdateSig}
    (K : @ReplayAdequacyCertificate D I P) {C : Configuration D}
    (h : MintCertifiedReach D I C) : @HasReplayWitness D P C :=
  K.soundV h.toV

end ReplayAdequacyCertificate

/-- The two execution modes accepted by the public theorem.  Datatype
legalization needs operational facts (most importantly, causal closure of
each stored version) that do not follow from an arbitrary replay witness.
Packaging the modes here lets one datatype theorem serve both semantics. -/
inductive CertifiedExecution (D : MRDTSig) (I : Issuance D)
    (C : Configuration D) : Prop where
  | ordinary : MintCertifiedReach D I C → CertifiedExecution D I C
  | virtual : MintCertifiedReachV D (canonicalVirtualMergeBase D) I C →
      CertifiedExecution D I C

theorem CertifiedExecution.mintHonest {D : MRDTSig} {I : Issuance D}
    {C : Configuration D} (h : CertifiedExecution D I C) :
    MintHonest D I.CanIssue C := by
  cases h with
  | ordinary reach => exact reach.mintHonest
  | virtual reach => exact reach.mintHonest

theorem CertifiedExecution.canonicalConfig {D : MRDTSig}
    {I : Issuance D} {P : ReplayPolicy D.toUpdateSig} {C : Configuration D}
    (join : ∀ C, MintHonest D I.CanIssue C → @JoinAt D P C.replayContext)
    (h : CertifiedExecution D I C) : @CanonicalConfig D P C := by
  cases h with
  | ordinary reach => exact canonicalConfig_of_mintCertified join reach
  | virtual reach => exact canonicalConfig_of_mintCertifiedV join reach

/-- Datatype-specific bridge from internal replay to client-facing
correctness. The framework applies this one theorem to both ordinary and virtual-merge-base
executions, so the verification package does not store duplicate proofs. -/
structure SequentialCorrectnessCertificate (D : MRDTSig)
    (I : Issuance D) (P : ReplayPolicy D.toUpdateSig)
    (S : SequentialSpec D)
    (Rel : D.State → S.State → Prop) where
  sound : ∀ C, CertifiedExecution D I C → @HasReplayWitness D P C →
    IsSpecLinearizable D P S Rel C

/-- Total datatypes discharge legalization directly: every list is legal and
every raw fold refines the sequential state and its observations. -/
def SequentialCorrectnessCertificate.ofTotal {D : MRDTSig}
    {I : Issuance D} {S : SequentialSpec D}
    {Rel : D.State → S.State → Prop}
    (join : ∀ C, MintHonest D I.CanIssue C → JoinAt D C.replayContext)
    (hcomm : ∀ a b : Op D.AppOp, D.toUpdateSig.commutes a b)
    (hrc : ∀ a b : Op D.AppOp,
      D.toUpdateSig.replayOrder a b = RcRes.Either)
    (legal : ∀ ops, S.Legal ops)
    (refines : ∀ ops,
      Rel (applySeq D.toUpdateSig D.init ops) (S.run ops))
    (observes : ∀ ops query,
      D.query (applySeq D.toUpdateSig D.init ops) query =
        S.query (S.run ops) query) :
    SequentialCorrectnessCertificate D I
      (ReplayPolicy.unconstrained D.toUpdateSig) S Rel where
  sound _ exec _ := by
    have hG := exec.canonicalConfig join
    have hCC := causalCanonical_of_all_comm_rc_either hcomm hrc hG
    exact hCC.toSpec legal refines observes

/-- Internal compatibility package for raw-fold refinement. It remains while
older instances migrate, but it is not the public sequential-correctness API. -/
structure ReplayAdequateMRDT (D : MRDTSig) where
  issuance : Issuance D
  rc : ReplayPolicy D.toUpdateSig
  replayAdequacy : @ReplayAdequacyCertificate D issuance rc
  Machine : SequentialMachine (Op D.AppOp)
  sequential : SequentialRefinement D Machine
  sequential_of_mint : ∀ ops,
    LinearMintHistory D issuance.CanIssue ops → sequential.Honest ops

/-- Complete public sequential-correctness package. Issuance constrains only origin
operation creation; `Spec.Legal` independently defines acceptable sequential
histories. The `rc` policy supplies the sole event-ordering direction; it does
not leak implementation state into the sequential specification. Safety and state
GC remain separate optional certificates. -/
structure VerifiedMRDT (D : MRDTSig) where
  issuance : Issuance D
  rc : ReplayPolicy D.toUpdateSig
  replayAdequacy : @ReplayAdequacyCertificate D issuance rc
  Spec : SequentialSpec D
  Rel : D.State → Spec.State → Prop
  sequentialCorrectness :
    SequentialCorrectnessCertificate D issuance rc Spec Rel

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

namespace ReplayAdequateMRDT

variable {D : MRDTSig} (V : ReplayAdequateMRDT D)

theorem replay {C : Configuration D}
    (h : MintCertifiedReach D V.issuance C) :
    @HasReplayWitness D V.rc C :=
  @ReplayAdequacyCertificate.sound D V.issuance V.rc
    V.replayAdequacy C h

theorem replayV {C : Configuration D}
    (h : MintCertifiedReachV D (canonicalVirtualMergeBase D) V.issuance C) :
    @HasReplayWitness D V.rc C :=
  @ReplayAdequacyCertificate.soundV D V.issuance V.rc
    V.replayAdequacy C h

theorem sequentially_correct (ops : List (Op D.AppOp))
    (h : LinearMintHistory D V.issuance.CanIssue ops) :
    V.sequential.Rel (applySeq D.toUpdateSig D.init ops) (V.Machine.run ops) :=
  V.sequential.sound ops (V.sequential_of_mint ops h)

end ReplayAdequateMRDT

namespace VerifiedMRDT

variable {D : MRDTSig} (V : VerifiedMRDT D)

theorem correct {C : Configuration D}
    (h : MintCertifiedReach D V.issuance C) :
    IsSpecLinearizable D V.rc V.Spec V.Rel C :=
  V.sequentialCorrectness.sound C
    (.ordinary h)
    (@ReplayAdequacyCertificate.sound D V.issuance V.rc
      V.replayAdequacy C h)

theorem correctV {C : Configuration D}
    (h : MintCertifiedReachV D (canonicalVirtualMergeBase D) V.issuance C) :
    IsSpecLinearizable D V.rc V.Spec V.Rel C :=
  V.sequentialCorrectness.sound C
    (.virtual h)
    (@ReplayAdequacyCertificate.soundV D V.issuance V.rc
      V.replayAdequacy C h)

end VerifiedMRDT

end Sal.MRDTs
