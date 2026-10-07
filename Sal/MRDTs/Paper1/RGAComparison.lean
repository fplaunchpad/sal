import Sal.MRDTs.Paper1.RGACrossedEvidence
import Sal.MRDTs.Paper1.RGAIdentified
import Sal.MRDTs.Paper1.RGAAllocatingCounterexample

/-! A reachable nonvacuity comparison. The concrete datatype, issuer, execution,
and returned list are identical. Application insertion identities are made
explicit only by `Identified.project`; the appendix criterion is retained. -/
namespace Sal.MRDTs.Paper1.RGA.Comparison
open Foundation
open Sal.MRDTs.Instances.RGA
open CrossedExecution

/-- Explicit insertion identities admit the stronger strict criterion on the
same honestly certified endpoint that refutes its operation-only counterpart. -/
theorem identified_strict :
    ProjectedSpecificationRALinearizable RGAM emptyPolicy Identified.project
      Identified.strictSpec (config 10) :=
  Identified.certifiedStrictRA _ Evidence.mint_certified

theorem identified_missing_noop :
    ProjectedSpecificationRALinearizable RGAM emptyPolicy Identified.project
      Identified.missingNoopSpec (config 10) :=
  Identified.certifiedMissingNoopRA _ Evidence.mint_certified

theorem strict_alphabet_comparison :
    MintCertifiedReach RGAM generation (config 10) ∧
    RGAM.query (records 10).1 () = [5,4,8,7] ∧
    ¬ SpecificationRALinearizable RGAM emptyPolicy Strict.spec (config 10) ∧
    ProjectedSpecificationRALinearizable RGAM emptyPolicy Identified.project
      Identified.strictSpec (config 10) :=
  ⟨Evidence.mint_certified,Evidence.final_read,Evidence.strict_failure,identified_strict⟩

/-- PASS+FAIL: the accepted explicit-ID result concerns a real nonempty read,
not an unreachable or constantly empty implementation. -/
example :
    ProjectedSpecificationRALinearizable RGAM emptyPolicy Identified.project
      Identified.strictSpec (config 10) ∧
    RGAM.query (records 10).1 () ≠ [] := by
  exact ⟨identified_strict, by rw [Evidence.final_read]; change ([5,4,8,7] : List Nat) ≠ []; decide⟩

#print axioms strict_alphabet_comparison
#print axioms identified_missing_noop

/-- The primary operation-only language is refuted at the identical certified
endpoint explained by the explicit-identity missing-anchor specification. -/
theorem allocating_alphabet_comparison :
    MintCertifiedReach RGAM generation (config 10) ∧
    ¬ SpecificationRALinearizable RGAM emptyPolicy listHistorySpec (config 10) ∧
    ProjectedSpecificationRALinearizable RGAM emptyPolicy Identified.project
      Identified.missingNoopSpec (config 10) :=
  ⟨Evidence.mint_certified,AllocatingCounterexample.not_specificationRA,
    identified_missing_noop⟩

theorem not_every_certified_allocating :
    ¬ (∀ C, MintCertifiedReach RGAM generation C →
      SpecificationRALinearizable RGAM emptyPolicy listHistorySpec C) := by
  intro h
  exact AllocatingCounterexample.not_specificationRA
    (h (config 10) Evidence.mint_certified)

/-- The same concrete execution separates both operation-only variants from
both explicitly identified variants, without changing datatype or issuer. -/
theorem same_execution_comparison :
    MintCertifiedReach RGAM generation (config 10) ∧
    RGAM.query (records 10).1 () = [5,4,8,7] ∧
    ¬ SpecificationRALinearizable RGAM emptyPolicy listHistorySpec (config 10) ∧
    ¬ SpecificationRALinearizable RGAM emptyPolicy Strict.spec (config 10) ∧
    ProjectedSpecificationRALinearizable RGAM emptyPolicy Identified.project
      Identified.strictSpec (config 10) ∧
    ProjectedSpecificationRALinearizable RGAM emptyPolicy Identified.project
      Identified.missingNoopSpec (config 10) :=
  ⟨Evidence.mint_certified,Evidence.final_read,
    AllocatingCounterexample.not_specificationRA,Evidence.strict_failure,
    identified_strict,identified_missing_noop⟩

#print axioms same_execution_comparison
#print axioms not_every_certified_allocating
end Sal.MRDTs.Paper1.RGA.Comparison
