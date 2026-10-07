import Sal.MRDTs.Paper1.FutureModel
import Sal.MRDTs.Paper1.PolicyObstructions

/-! Obstructions at the actual query boundary. These hold for every sound
abstraction, including the complete future-query quotient. They concern the
globally quantified operation-only laws, not production correctness or the
issuability of the individual raw witnesses. -/
namespace Sal.MRDTs.Paper1.ObservationalObstructions
open Foundation AbstractMRDT

theorem not_commutes_of_query {D : MRDTSig} (A : Model D)
    (a b : Op D.AppOp) (s : D.State) (q : D.Query)
    (bad : D.query (D.update (D.update s a) b) q ≠
      D.query (D.update (D.update s b) a) q) : ¬ Commutes A a b :=
  fun h => bad (equivalent_query (h s) q)

theorem no_laws_same_label {D : MRDTSig} (A : Model D)
    (a b : Op D.AppOp) (same : a.op = b.op) (bad : ¬ Commutes A a b) :
    ¬ ∃ P : OperationPolicy D.AppOp, Laws A P := by
  rintro ⟨P,laws⟩
  have conflict := (laws.noncomm_exact a b).mp bad
  have diagonal : ¬ Commutes A a a := (laws.noncomm_exact a a).mpr (by
    simpa [same] using conflict)
  exact diagonal (fun _ => rfl)

/-- Three pairwise observable conflicts cannot be oriented without a chain.
No statement about hidden concrete fields is used. -/
theorem no_laws_triangle {D : MRDTSig} (A : Model D)
    (a b c : Op D.AppOp)
    (ab : ¬ Commutes A a b) (bc : ¬ Commutes A b c)
    (ac : ¬ Commutes A a c) :
    ¬ ∃ P : OperationPolicy D.AppOp, Laws A P := by
  rintro ⟨P,laws⟩
  have hab := (laws.noncomm_exact a b).mp ab
  have hbc := (laws.noncomm_exact b c).mp bc
  have hac := (laws.noncomm_exact a c).mp ac
  have h := laws.no_chain
  rcases hab with hab | hba <;> rcases hbc with hbc | hcb <;>
    rcases hac with hac | hca
  · exact h a.op b.op c.op ⟨hab,hbc⟩
  · exact h a.op b.op c.op ⟨hab,hbc⟩
  · exact h a.op c.op b.op ⟨hac,hcb⟩
  · exact h c.op a.op b.op ⟨hca,hab⟩
  · exact h b.op a.op c.op ⟨hba,hac⟩
  · exact h b.op c.op a.op ⟨hbc,hca⟩
  · exact h c.op b.op a.op ⟨hcb,hba⟩
  · exact h c.op b.op a.op ⟨hcb,hba⟩

namespace Queue
open Instances.Queue PolicyObstructions.Queue

/-- Hand-derived PASS+FAIL: equal enqueue values still expose distinct tags
at the production head query. -/
theorem query_control :
    Q.query (Q.update (Q.update [] left) right) () = some (1,7) ∧
    Q.query (Q.update (Q.update [] right) left) () = some (2,7) ∧
    Q.query (Q.update (Q.update [] left) right) () ≠
      Q.query (Q.update (Q.update [] right) left) () := by
  change _root_.List.head? (qUpdate (qUpdate [] left) right) = some (1,7) ∧
    _root_.List.head? (qUpdate (qUpdate [] right) left) = some (2,7) ∧
    _root_.List.head? (qUpdate (qUpdate [] left) right) ≠
      _root_.List.head? (qUpdate (qUpdate [] right) left)
  decide

theorem noncommute (A : Model Q) : ¬ Commutes A left right :=
  not_commutes_of_query A left right [] () query_control.2.2

theorem diagonal_control (A : Model Q) :
    Commutes A left left ∧ ¬ Commutes A left right :=
  ⟨fun _ => rfl,noncommute A⟩

theorem no_laws (A : Model Q) : ¬ ∃ P : OperationPolicy QOp, Laws A P :=
  no_laws_same_label A left right rfl (noncommute A)
end Queue

namespace MVR
open Instances.MVRLive PolicyObstructions.MVR
open Instances.MVR (MVROp clientStep queryValues writeValue overwrites)

/-- The overwrite removes value 10 only when delivered after its birth. -/
theorem query_control :
    10 ∉ queryValues (Instances.MVRLive.update (Instances.MVRLive.update ∅ birth) overwrite) ∧
    10 ∈ queryValues (Instances.MVRLive.update (Instances.MVRLive.update ∅ overwrite) birth) := by
  simp [Instances.MVRLive.update, clientStep, queryValues, writeValue, overwrites, birth, overwrite]

theorem noncommute (A : Model D) : ¬ Commutes A birth overwrite := by
  apply not_commutes_of_query A birth overwrite (∅ : Instances.MVRLive.State) ()
  intro eq
  change queryValues (Instances.MVRLive.update (Instances.MVRLive.update ∅ birth) overwrite) =
    queryValues (Instances.MVRLive.update (Instances.MVRLive.update ∅ overwrite) birth) at eq
  exact query_control.1 (eq ▸ query_control.2)

/-- Positive control: the same application labels commute when the birth's
timestamp is outside the overwritten set; this holds in every raw state. -/
theorem metadata_control (A : Model D) :
    Commutes A unrelatedBirth unrelatedOverwrite ∧
    ¬ Commutes A birth overwrite ∧
    birth.op = unrelatedBirth.op ∧ overwrite.op = unrelatedOverwrite.op :=
  ⟨of_state_commutes unrelated_commute,noncommute A,rfl,rfl⟩

theorem no_laws (A : Model D) :
    ¬ ∃ P : OperationPolicy MVROp, Laws A P := by
  rintro ⟨P,laws⟩
  have conflict := (laws.noncomm_exact birth overwrite).mp (noncommute A)
  have invalid := (laws.noncomm_exact unrelatedBirth unrelatedOverwrite).mpr conflict
  exact invalid (of_state_commutes unrelated_commute)
end MVR

#print axioms Queue.no_laws
#print axioms MVR.no_laws
#print axioms Queue.query_control
#print axioms Queue.diagonal_control
#print axioms MVR.query_control
#print axioms MVR.metadata_control
end Sal.MRDTs.Paper1.ObservationalObstructions
