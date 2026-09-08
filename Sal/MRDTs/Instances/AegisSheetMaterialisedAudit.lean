import Sal.MRDTs.Instances.AegisSheetMaterialisedConverse
import Sal.MRDTs.Instances.AegisSheetMaterialisedRetirement

/-! The research branch's explicit axiom gate; no executable fixtures are
dependencies of these declarations. -/
namespace Sal.MRDTs.Instances.AegisSheet.Materialised
#print axioms joinTarget
#print axioms replayAdequacy
#print axioms observationEquivalence
#print axioms update_preserves_canon_of_past
#print axioms Issued.fold
#print axioms cross_model
#print axioms converse
#print axioms verified
#print axioms retirement
#print axioms Represents.applicable_iff
#print axioms retire_applicable_iff
#print axioms update_represents_of_compact
end Sal.MRDTs.Instances.AegisSheet.Materialised
