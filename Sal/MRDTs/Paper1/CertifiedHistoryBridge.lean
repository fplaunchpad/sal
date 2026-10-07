import Sal.MRDTs.Paper1.GuardedRawModel
import Sal.MRDTs.Paper1.AbstractMerge

/-! The history witness can be transported through a concrete representation
whose uniqueness is justified only in certified contexts. This bridge does not
assume the global guarded-law contract, and does not claim to discharge VCs.
Its conclusion is explicitly `VersionsWitness`; callers must separately expose
and prove their scoped algebraic assumptions. -/
namespace Sal.MRDTs.Paper1.CertifiedHistory
open Foundation AbstractMRDT
variable {D : MRDTSig}

/-- An admitted replay with representation evidence. The query in this premise
is answered by the merge-free fold, independently of the stored state. -/
def RepresentedHistory (R : Representation D) (P : OperationPolicy D.AppOp)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value) (I : Issuance D) : Prop :=
  ∀ C, CertifiedExecution D I C → ∀ v s E, C.ver v = some (s,E) →
    ∀ q, ∃ π : List (Op D.AppOp),
      listPermOf π E ∧ respects π (paperOrder P C.replayContext E) ∧
      respects π (projectedSpecVisibility id S C.replayContext) ∧
      R C.replayContext E (applySeq D.toUpdateSig D.init π) ∧
      S.admits (projectedLabels id π ++
        [.query q (D.query (applySeq D.toUpdateSig D.init π) q)])

/-- Uniqueness is required only for histories of stored versions in a certified
configuration. Illegal origins and arbitrary replay contexts are outside it. -/
def CertifiedUnique (R : Representation D) (I : Issuance D) : Prop :=
  ∀ C, CertifiedExecution D I C → ∀ v s E, C.ver v = some (s,E) →
    ∀ a b, R C.replayContext E a → R C.replayContext E b → a = b

theorem versions_of_representation {R : Representation D}
    {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (unique : CertifiedUnique R I) (history : RepresentedHistory R P S I)
    {C : Configuration D} (execution : CertifiedExecution D I C)
    (represented : ∀ v s E, C.ver v = some (s,E) → R C.replayContext E s) :
    VersionsWitness (Raw.model D) P S C := by
  intro v s E hv q
  obtain ⟨π,hp,ho,hs,hr,accepted⟩ := history C execution v s E hv q
  have same := unique C execution v s E hv _ _ hr (represented v s E hv)
  exact ⟨π,hp,ho,hs,by simpa only [same] using accepted⟩

/-- Stored canonicality is exact equality with an admitted full-event replay.
The witness can be chosen using any query; it preserves both semantic order
and specification-conflict visibility. -/
theorem storedCanonical {R : Representation D} {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (unique : CertifiedUnique R I) (history : RepresentedHistory R P S I)
    {C : Configuration D} (execution : CertifiedExecution D I C)
    {v : Version} {s : D.State} {E : Set (Op D.AppOp)}
    (hv : C.ver v = some (s,E)) (represented : R C.replayContext E s) (q : D.Query) :
    ∃ π, listPermOf π E ∧ respects π (paperOrder P C.replayContext E) ∧
      respects π (projectedSpecVisibility id S C.replayContext) ∧
      applySeq D.toUpdateSig D.init π = s := by
  obtain ⟨π,hp,ho,hs,hr,_⟩ := history C execution v s E hv q
  exact ⟨π,hp,ho,hs,unique C execution v s E hv _ _ hr represented⟩

/-- Existing merge-free history proofs can be reused once replay eligibility
is proved. This adapter leaves that preservation obligation visible. -/
theorem representedHistory_of_adequacy {R : Representation D}
    {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (history : ExecutionHistoryAdequacy (Raw.model D) P S I)
    (replay : ∀ C, CertifiedExecution D I C → ∀ v s E,
      C.ver v = some (s,E) → ∀ π, listPermOf π E →
      respects π (paperOrder P C.replayContext E) →
      respects π (projectedSpecVisibility id S C.replayContext) →
      R C.replayContext E (applySeq D.toUpdateSig D.init π)) :
    RepresentedHistory R P S I := by
  intro C execution v s E hv q
  obtain ⟨π,hp,ho,hs,accepted⟩ := history C execution v s E hv q
  exact ⟨π,hp,ho,hs,replay C execution v s E hv π hp ho hs,accepted⟩

end Sal.MRDTs.Paper1.CertifiedHistory
