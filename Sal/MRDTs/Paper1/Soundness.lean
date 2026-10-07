import Sal.MRDTs.Paper1.SequentialSimulation

/-! Sufficient conditions and finite-execution guarantees for the paper
criterion. Issuance and mint provenance remain explicit in certified traces. -/

namespace Sal.MRDTs.Paper1
open Foundation

/-- Exactly the five merge obligations. Replay restrictions are supplied
separately, so an implementer does not provide a second, weaker policy contract.
`delta` contains canonical init, local redistribution, and shared redistribution. -/
structure PaperMergeVCs (D : MRDTSig) (P : OperationPolicy D.AppOp) : Prop where
  merge_comm : ∀ l a b, D.merge l a b = D.merge l b a
  delta : @FeasibleDeltaLaws D P.lift
  causal_delta : @CausalDeltaLaw D P.lift

def PaperMergeVCs.toCanonical {D : MRDTSig} {P : OperationPolicy D.AppOp}
    (vcs : PaperMergeVCs D P) (restricted : RestrictedLaws D.toUpdateSig P) :
    @CanonicalJoinLaws D P.lift := by
  letI : ReplayPolicy D.toUpdateSig := P.lift
  exact ⟨⟨restricted.replayLaws, vcs.merge_comm⟩, vcs.delta, vcs.causal_delta⟩

private theorem execution_invariant (T : LabeledTS) (Good : T.State → Prop)
    (preserved : ∀ s l t, Good s → T.step s l t → Good t)
    {initial : T.State} {trace : List (T.Label × T.State)}
    (execution : T.Execution initial trace) (start : Good initial) :
    Good initial ∧ ∀ entry ∈ trace, Good entry.2 := by
  induction execution with
  | nil => exact ⟨start, by simp⟩
  | @cons s t l rest step _ ih =>
      have tail := ih (preserved s l t start step)
      refine ⟨start, ?_⟩
      intro entry he
      rcases List.mem_cons.mp he with rfl | he
      · exact tail.1
      · exact tail.2 entry he

theorem raImplementation_of_reachable {D : MRDTSig} {P : OperationPolicy D.AppOp}
    {S : HistorySpec D.AppOp D.Query D.Value}
    (h : RALinearizableOn D P S
      (fun C => (labeledTS D).ReachableFrom (initConfig D) C)) :
    RAImplementation D P S := by
  intro trace execution
  have visited := execution_invariant (labeledTS D)
    (fun C => (labeledTS D).ReachableFrom (initConfig D) C)
    (fun _ l _ pre step => pre.tail ⟨l, step⟩)
    execution Relation.ReflTransGen.refl
  exact ⟨h _ visited.1, fun entry he => h _ (visited.2 entry he)⟩

/-- Total sequential soundness and all-context Join also cover raw executions.
This route does not erase necessary issuance premises for guarded datatypes. -/
theorem rawRA_of_join_total {D : MRDTSig} {P : OperationPolicy D.AppOp}
    {S : HistorySpec D.AppOp D.Query D.Value}
    (laws : RestrictedLaws D.toUpdateSig P) (join : @Join D P.lift)
    (sound : FoldHistorySound D S) : RAImplementation D P S := by
  letI : ReplayPolicy D.toUpdateSig := P.lift
  apply raImplementation_of_reachable
  intro C reach
  exact (ra_of_replay_total laws (replayWitness_of_join join C reach) sound).heads

/-- The finite-trace semantics corresponding to `MintCertifiedReach`. Each
apply carries its issuer guard; each step retains before/after mint provenance. -/
def certifiedTS (D : MRDTSig) (I : Issuance D) : LabeledTS where
  State := Configuration D
  Label := Label D
  step C l C' := MintHonest D I.CanIssue C ∧ IssuedStep D I C l C' ∧
    MintHonest D I.CanIssue C'
  silent := fun _ => False

theorem CertifiedRA.executions {D : MRDTSig} {P : OperationPolicy D.AppOp}
    {S : HistorySpec D.AppOp D.Query D.Value} {I : Issuance D}
    (h : CertifiedRA D P S I) (trace : List (Label D × Configuration D))
    (execution : (certifiedTS D I).Execution (initConfig D) trace) :
    RAExecution D P S (initConfig D) trace := by
  have visited := execution_invariant (certifiedTS D I) (MintCertifiedReach D I)
    (fun _ _ _ pre step => .step pre step.1 step.2.1 step.2.2)
    execution MintCertifiedReach.init
  exact ⟨h _ visited.1, fun entry he => h _ (visited.2 entry he)⟩

def certifiedTSV (D : MRDTSig) (I : Issuance D) : LabeledTS where
  State := Configuration D
  Label := Label D
  step C l C' := MintHonest D I.CanIssue C ∧
    IssuedStepV D (canonicalVirtualMergeBase D) I C l C' ∧
    MintHonest D I.CanIssue C'
  silent := fun _ => False

theorem CertifiedRAV.executions {D : MRDTSig} {P : OperationPolicy D.AppOp}
    {S : HistorySpec D.AppOp D.Query D.Value} {I : Issuance D}
    (h : CertifiedRAV D P S I) (trace : List (Label D × Configuration D))
    (execution : (certifiedTSV D I).Execution (initConfig D) trace) :
    RAExecution D P S (initConfig D) trace := by
  have visited := execution_invariant (certifiedTSV D I)
    (MintCertifiedReachV D (canonicalVirtualMergeBase D) I)
    (fun _ _ _ pre step => .step pre step.1 step.2.1 step.2.2)
    execution MintCertifiedReachV.init
  exact ⟨h _ visited.1, fun entry he => h _ (visited.2 entry he)⟩

/-- Restricted replay laws and the five merge VCs give canonical correctness.
The independent sequential premise is additionally required to derive the
history-language criterion; it is not one of the merge obligations. -/
theorem certifiedRA_of_fiveVCs {D : MRDTSig} {P : OperationPolicy D.AppOp}
    {S : HistorySpec D.AppOp D.Query D.Value} {I : Issuance D}
    (restricted : RestrictedLaws D.toUpdateSig P)
    (vcs : PaperMergeVCs D P)
    (sequential : FoldHistorySound D S) : CertifiedRAV D P S I := by
  letI : ReplayPolicy D.toUpdateSig := P.lift
  exact certifiedRA_of_join_total restricted
    (fun C _ => (vcs.toCanonical restricted).join C.replayContext) sequential

theorem certifiedRA_of_fiveVCs_issued {D : MRDTSig} {P : OperationPolicy D.AppOp}
    {S : HistorySpec D.AppOp D.Query D.Value} {I : Issuance D}
    (restricted : RestrictedLaws D.toUpdateSig P)
    (vcs : PaperMergeVCs D P)
    (sequential : IssuedHistoryAdequacy D P S I) : CertifiedRAV D P S I := by
  letI : ReplayPolicy D.toUpdateSig := P.lift
  exact certifiedRA_of_join restricted
    (fun C _ => (vcs.toCanonical restricted).join C.replayContext) sequential

theorem certified_convergence_of_join {D : MRDTSig} {P : OperationPolicy D.AppOp}
    {I : Issuance D} (laws : RestrictedLaws D.toUpdateSig P)
    (join : ∀ C, MintHonest D I.CanIssue C → @JoinAt D P.lift C.replayContext)
    {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) I C)
    {v w : Version} {s t : D.State} {E : Set (Op D.AppOp)}
    (hv : C.ver v = some (s, E)) (hw : C.ver w = some (t, E)) : s = t := by
  letI : ReplayPolicy D.toUpdateSig := P.lift
  have canonical := canonicalConfig_of_mintCertifiedV join reach
  exact isCanonicalState_unique_of_replayLaws laws.replayLaws
    (canonical.version_events_supported v s E hv)
    (canonical.canonical v s E hv) (canonical.canonical w t E hw)

end Sal.MRDTs.Paper1
