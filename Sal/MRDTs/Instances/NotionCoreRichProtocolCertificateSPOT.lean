import Sal.MRDTs.Instances.NotionCoreRichProtocolNonempty
import Sal.MRDTs.Instances.NotionCoreRichProtocolCertificate

/-! The public derived certificate on an actual nonempty prepared caller and
version-DAG execution. Expected observations are the hand-derived `ab` fixture,
including identified characters and rich flags. -/
namespace Sal.MRDTs.Instances.NotionCoreRichProtocolCertificateSPOT
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT
open NotionCoreRichPayload (Transaction)
open NotionCoreRichProtocolCarrier (D)
open NotionCoreRichProtocolNonempty

theorem versions_certificate :
    VersionsWitness (commutingPolicy Transaction) NotionCoreRichSequentialInputs.spec config :=
  NotionCoreRichProtocolCertificate.versions_witness sessions_injective reachable

theorem specification_ra :
    EventSpecificationRALinearizable D (commutingPolicy Transaction)
      NotionCoreRichSequentialInputs.spec config :=
  NotionCoreRichProtocolCertificate.specification_ra sessions_injective reachable

/-- PASS+FAIL: the final public certificate applies to a real formatted
observation, excluding renderer failure, empty output and the plain rival. -/
theorem certificate_control :
    EventSpecificationRALinearizable D (commutingPolicy Transaction)
      NotionCoreRichSequentialInputs.spec config ∧
      D.query log () = some (expected true) ∧ D.query log () ≠ none ∧
      D.query log () ≠ some [] ∧ D.query log () ≠ some (expected false) :=
  ⟨specification_ra,query_control⟩

/-- The public source-coordinate endpoint applies to the same actual caller
that prepared the whole-format transaction in the framework fixture. -/
theorem actual_selection_control :
    ∃ actual abstract rich,
      NotionCoreRichProtocolNetwork.reconstruct sourceBase [65] = some actual ∧
      NotionCoreRichSequential.Refinement.Related actual abstract ∧
      NotionCoreRichSequential.Selection.selectRich abstract 0 0 2 = some rich ∧
      rich ≠ [] ∧ rich.all (·.bold) = false := by
  have sourceReach : NotionCoreRichProtocolNetwork.Reach sourceBase := .bootstrap [97,98]
  obtain ⟨actual,abstract,reconstructed,related,independent⟩ :=
    NotionCoreRichProtocolCertificate.source_reconstruction sourceBase sourceReach [65]
  have prepared : NotionCoreRichProtocolNetwork.formatPayload actual .initial 0 2 = some formatPayload := by
    have original := actual_preparation.1
    simp only [NotionCoreRichProtocolNetwork.prepareAt,reconstructed,
      Bind.bind,Option.bind,NotionCoreRichProtocolNetwork.prepare] at original
    exact original
  obtain ⟨abstract,rich,related,selected,nonempty,verdict,addresses,chosen,coverage⟩ :=
    NotionCoreRichProtocolCertificate.selection_exact sourceBase sourceReach [65] actual reconstructed
      .initial 0 2 _ true formatting.id prepared
  refine ⟨actual,abstract,rich,reconstructed,related,selected,nonempty,?_⟩
  cases marked : rich.all (·.bold) <;> simp_all

#print axioms certificate_control
#print axioms actual_selection_control
end Sal.MRDTs.Instances.NotionCoreRichProtocolCertificateSPOT
