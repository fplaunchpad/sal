import Sal.MRDTs.Paper1.CommutationBridge

/-! Full-input sufficient conditions. Every sequential update retains its
original timestamp, replica, and application operation. Specifications are
independent history languages. Simulations and issuance predicates are proof
premises, not part of the public correctness criterion. -/
namespace Sal.MRDTs.Paper1
open Foundation

def commutingPolicy (U : Type) : OperationPolicy U := ⟨fun _ _ => False⟩

theorem restricted_of_all_commute {D : UpdateSig}
    (commute : ∀ a b, D.commutes a b) : RestrictedLaws D (commutingPolicy D.AppOp) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    simp [commutingPolicy, commute a b]
  · simp [commutingPolicy]
  · simp [commutingPolicy]

theorem paperOrder_false_of_all_commute {D : UpdateSig}
    (commute : ∀ a b, D.commutes a b) (C : ReplayContext D)
    (E : Set (Op D.AppOp)) (a b : Op D.AppOp) :
    ¬ paperOrder (commutingPolicy D.AppOp) C E a b := by
  simp [paperOrder, commutingPolicy, commute a b]

/-- A merge-free simulation into an independent full-input abstract machine. -/
structure EventSequentialSimulation (D : MRDTSig)
    (M : DeterministicSpec (Op D.AppOp) D.Query D.Value) where
  Rel : D.State → M.State → Prop
  initial : Rel D.init M.initial
  update : ∀ s a, Rel s a → ∀ e, Rel (D.update s e) (M.update a e)
  observes : ∀ s a, Rel s a → ∀ q, D.query s q = M.query a q

def EventFoldHistorySound (D : MRDTSig)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value) : Prop :=
  ∀ π q, S.admits (projectedLabels id π ++
    [.query q (D.query (applySeq D.toUpdateSig D.init π) q)])

theorem EventSequentialSimulation.fold_rel {D : MRDTSig}
    {M : DeterministicSpec (Op D.AppOp) D.Query D.Value}
    (H : EventSequentialSimulation D M) (π : List (Op D.AppOp))
    (s : D.State) (a : M.State) (h : H.Rel s a) :
    H.Rel (applySeq D.toUpdateSig s π) (π.foldl M.update a) := by
  induction π generalizing s a with
  | nil => exact h
  | cons e π ih => exact ih _ _ (H.update s a h e)

theorem EventSequentialSimulation.sound {D : MRDTSig}
    {M : DeterministicSpec (Op D.AppOp) D.Query D.Value}
    (H : EventSequentialSimulation D M) : EventFoldHistorySound D M.toSpec := by
  intro π q
  change M.toSpec.admits (DeterministicSpec.updateLabels π ++
    [.query q (D.query (applySeq D.toUpdateSig D.init π) q)])
  rw [M.updates_query_iff]
  exact H.observes _ _ (H.fold_rel π D.init M.initial H.initial) q

/-- Lift existing operation-only simulation without changing concrete inputs. -/
def SequentialSimulation.withInputs {D : MRDTSig}
    {M : DeterministicSpec D.AppOp D.Query D.Value} (H : SequentialSimulation D M) :
    EventSequentialSimulation D
      { State := M.State, initial := M.initial,
        update := fun s e => M.update s e.op, query := M.query } :=
  ⟨H.Rel, H.initial, H.update, H.observes⟩

/-- Stronger guarantee for every allocated version, including old ancestors. -/
def EventVersionsSpecificationRA (D : MRDTSig) (P : OperationPolicy D.AppOp)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value) (C : Configuration D) : Prop :=
  ∀ v s E, C.ver v = some (s,E) → ∀ q, ∃ π : List (Op D.AppOp),
    listPermOf π E ∧ respects π (paperOrder P C.replayContext E) ∧
    respects π (projectedSpecVisibility id S C.replayContext) ∧
    S.admits (projectedLabels id π ++ [.query q (D.query s q)])

theorem EventVersionsSpecificationRA.heads {D : MRDTSig}
    {P : OperationPolicy D.AppOp} {S : HistorySpec (Op D.AppOp) D.Query D.Value}
    {C : Configuration D} (h : EventVersionsSpecificationRA D P S C) :
    EventSpecificationRALinearizable D P S C := by
  intro r v s E _ hv q
  exact h v s E hv q

/-- Mint and supported/causal event-set evidence select an admissible replay.
No assertion is made that issuance survives arbitrary reordering. -/
def EventIssuedHistoryAdequacy (D : MRDTSig) (P : OperationPolicy D.AppOp)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value) (I : Issuance D) : Prop :=
  ∀ C, MintHonest D I.CanIssue C → ∀ E : Set (Op D.AppOp),
    (∀ e ∈ E, e ∈ C.events) →
    (∀ a b, C.vis a b → b ∈ E → a ∈ E) →
    (∃ π, listPermOf π E) → ∀ q, ∃ π : List (Op D.AppOp),
      listPermOf π E ∧ respects π (paperOrder P C.replayContext E) ∧
      respects π (projectedSpecVisibility id S C.replayContext) ∧
      S.admits (projectedLabels id π ++
        [.query q (D.query (applySeq D.toUpdateSig D.init π) q)])

/-- Execution-scoped variant for datatypes needing certified birth/version
provenance in addition to honest mint records. The conclusion explains a fold,
not the query of the stored state. -/
def EventExecutionHistoryAdequacy (D : MRDTSig) (P : OperationPolicy D.AppOp)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value) (I : Issuance D) : Prop :=
  ∀ C, CertifiedExecution D I C → ∀ v s E, C.ver v = some (s,E) →
    ∀ q, ∃ π : List (Op D.AppOp),
      listPermOf π E ∧ respects π (paperOrder P C.replayContext E) ∧
      respects π (projectedSpecVisibility id S C.replayContext) ∧
      S.admits (projectedLabels id π ++
        [.query q (D.query (applySeq D.toUpdateSig D.init π) q)])

theorem event_versions_of_canonical_total {D : MRDTSig}
    {P : OperationPolicy D.AppOp} {S : HistorySpec (Op D.AppOp) D.Query D.Value}
    {C : Configuration D} (laws : RestrictedLaws D.toUpdateSig P)
    (canonical : @CanonicalConfig D P.lift C)
    (compatible : CommutationCompatibility D id S) (sound : EventFoldHistorySound D S) :
    EventVersionsSpecificationRA D P S C := by
  letI : ReplayPolicy D.toUpdateSig := P.lift
  intro v s E hv q
  obtain ⟨π, hp, hr, hf⟩ := hasReplayWitness_of_canonical canonical v s E hv
  have ho : respects π (paperOrder P C.replayContext E) :=
    hr.imp (fun {_ _} h => h ∘ (paperOrder_iff_loOn laws _ _ _ _).mp)
  refine ⟨π, hp, ho, ?_, ?_⟩
  · exact ho.imp (fun {_ _} h => h ∘
      projectedSpecVisibility_sub_paperOrder compatible C.replayContext E _ _)
  · simpa [hf] using sound π q

theorem event_versions_of_canonical_issued {D : MRDTSig}
    {P : OperationPolicy D.AppOp} {S : HistorySpec (Op D.AppOp) D.Query D.Value}
    {I : Issuance D} {C : Configuration D}
    (laws : RestrictedLaws D.toUpdateSig P) (canonical : @CanonicalConfig D P.lift C)
    (honest : MintHonest D I.CanIssue C) (history : EventIssuedHistoryAdequacy D P S I) :
    EventVersionsSpecificationRA D P S C := by
  letI : ReplayPolicy D.toUpdateSig := P.lift
  intro v s E hv q
  have hs := canonical.canonical v s E hv
  obtain ⟨π,hp,ho,hvSpec,accepted⟩ := history C honest E
    (canonical.version_events_supported v s E hv)
    (canonical.version_events_causal v s E hv)
    (by obtain ⟨w,hw,_,_⟩ := hs; exact ⟨w,hw⟩) q
  have hr : respects π (@loOn D.toUpdateSig P.lift C.replayContext E) :=
    ho.imp (fun {_ _} h => h ∘ (paperOrder_iff_loOn laws _ _ _ _).mpr)
  have heq := isCanonicalState_unique_of_replayLaws laws.replayLaws
    (canonical.version_events_supported v s E hv) hs ⟨π,hp,hr,rfl⟩
  exact ⟨π,hp,ho,hvSpec,by simpa [heq] using accepted⟩

theorem event_versions_of_canonical_execution {D : MRDTSig}
    {P : OperationPolicy D.AppOp} {S : HistorySpec (Op D.AppOp) D.Query D.Value}
    {I : Issuance D} {C : Configuration D}
    (laws : RestrictedLaws D.toUpdateSig P) (canonical : @CanonicalConfig D P.lift C)
    (exec : CertifiedExecution D I C) (history : EventExecutionHistoryAdequacy D P S I) :
    EventVersionsSpecificationRA D P S C := by
  letI : ReplayPolicy D.toUpdateSig := P.lift
  intro v s E hv q
  obtain ⟨π,hp,ho,hs,accepted⟩ := history C exec v s E hv q
  have hr : respects π (@loOn D.toUpdateSig P.lift C.replayContext E) :=
    ho.imp (fun {_ _} h => h ∘ (paperOrder_iff_loOn laws _ _ _ _).mpr)
  have heq := isCanonicalState_unique_of_replayLaws laws.replayLaws
    (canonical.version_events_supported v s E hv)
    (canonical.canonical v s E hv) ⟨π,hp,hr,rfl⟩
  exact ⟨π,hp,ho,hs,by simpa [heq] using accepted⟩

def EventCertifiedSpecificationRA (D : MRDTSig) (P : OperationPolicy D.AppOp)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value) (I : Issuance D) : Prop :=
  ∀ C, MintCertifiedReach D I C → EventVersionsSpecificationRA D P S C

def EventCertifiedSpecificationRAV (D : MRDTSig) (P : OperationPolicy D.AppOp)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value) (I : Issuance D) : Prop :=
  ∀ C, MintCertifiedReachV D (canonicalVirtualMergeBase D) I C →
    EventVersionsSpecificationRA D P S C

theorem EventCertifiedSpecificationRAV.ordinary {D : MRDTSig}
    {P : OperationPolicy D.AppOp} {S : HistorySpec (Op D.AppOp) D.Query D.Value}
    {I : Issuance D} (h : EventCertifiedSpecificationRAV D P S I) :
    EventCertifiedSpecificationRA D P S I := fun C reach => h C reach.toV

theorem event_certified_of_join_total {D : MRDTSig}
    {P : OperationPolicy D.AppOp} {S : HistorySpec (Op D.AppOp) D.Query D.Value}
    {I : Issuance D} (laws : RestrictedLaws D.toUpdateSig P)
    (join : ∀ C, MintHonest D I.CanIssue C → @JoinAt D P.lift C.replayContext)
    (compatible : CommutationCompatibility D id S) (sound : EventFoldHistorySound D S) :
    EventCertifiedSpecificationRAV D P S I := by
  letI : ReplayPolicy D.toUpdateSig := P.lift
  intro C reach
  exact event_versions_of_canonical_total laws
    (canonicalConfig_of_mintCertifiedV join reach) compatible sound

theorem event_certified_of_join_issued {D : MRDTSig}
    {P : OperationPolicy D.AppOp} {S : HistorySpec (Op D.AppOp) D.Query D.Value}
    {I : Issuance D} (laws : RestrictedLaws D.toUpdateSig P)
    (join : ∀ C, MintHonest D I.CanIssue C → @JoinAt D P.lift C.replayContext)
    (history : EventIssuedHistoryAdequacy D P S I) :
    EventCertifiedSpecificationRAV D P S I := by
  letI : ReplayPolicy D.toUpdateSig := P.lift
  intro C reach
  exact event_versions_of_canonical_issued laws
    (canonicalConfig_of_mintCertifiedV join reach) reach.mintHonest history

theorem event_certified_of_join_execution {D : MRDTSig}
    {P : OperationPolicy D.AppOp} {S : HistorySpec (Op D.AppOp) D.Query D.Value}
    {I : Issuance D} (laws : RestrictedLaws D.toUpdateSig P)
    (join : ∀ C, MintHonest D I.CanIssue C → @JoinAt D P.lift C.replayContext)
    (history : EventExecutionHistoryAdequacy D P S I) :
    EventCertifiedSpecificationRAV D P S I := by
  letI : ReplayPolicy D.toUpdateSig := P.lift
  intro C reach
  exact event_versions_of_canonical_execution laws
    (canonicalConfig_of_mintCertifiedV join reach) (.virtual reach) history

theorem event_certified_of_fiveVCs_total {D : MRDTSig}
    {P : OperationPolicy D.AppOp} {S : HistorySpec (Op D.AppOp) D.Query D.Value}
    {I : Issuance D} (laws : RestrictedLaws D.toUpdateSig P) (vcs : PaperMergeVCs D P)
    (compatible : CommutationCompatibility D id S) (sound : EventFoldHistorySound D S) :
    EventCertifiedSpecificationRAV D P S I := by
  letI : ReplayPolicy D.toUpdateSig := P.lift
  exact event_certified_of_join_total laws
    (fun C _ => (vcs.toCanonical laws).join C.replayContext) compatible sound

theorem event_certified_of_fiveVCs_issued {D : MRDTSig}
    {P : OperationPolicy D.AppOp} {S : HistorySpec (Op D.AppOp) D.Query D.Value}
    {I : Issuance D} (laws : RestrictedLaws D.toUpdateSig P) (vcs : PaperMergeVCs D P)
    (history : EventIssuedHistoryAdequacy D P S I) :
    EventCertifiedSpecificationRAV D P S I := by
  letI : ReplayPolicy D.toUpdateSig := P.lift
  exact event_certified_of_join_issued laws
    (fun C _ => (vcs.toCanonical laws).join C.replayContext) history

theorem event_certified_of_fiveVCs_execution {D : MRDTSig}
    {P : OperationPolicy D.AppOp} {S : HistorySpec (Op D.AppOp) D.Query D.Value}
    {I : Issuance D} (laws : RestrictedLaws D.toUpdateSig P) (vcs : PaperMergeVCs D P)
    (history : EventExecutionHistoryAdequacy D P S I) :
    EventCertifiedSpecificationRAV D P S I := by
  letI : ReplayPolicy D.toUpdateSig := P.lift
  exact event_certified_of_join_execution laws
    (fun C _ => (vcs.toCanonical laws).join C.replayContext) history

theorem EventCertifiedSpecificationRA.executions {D : MRDTSig}
    {P : OperationPolicy D.AppOp} {S : HistorySpec (Op D.AppOp) D.Query D.Value}
    {I : Issuance D} (h : EventCertifiedSpecificationRA D P S I)
    (trace : List (Label D × Configuration D))
    (execution : (certifiedTS D I).Execution (initConfig D) trace) :
    ProjectedSpecificationExecution D P id S (initConfig D) trace :=
  projected_certified_executions (fun C reach => (h C reach).heads) trace execution

theorem EventCertifiedSpecificationRAV.executions {D : MRDTSig}
    {P : OperationPolicy D.AppOp} {S : HistorySpec (Op D.AppOp) D.Query D.Value}
    {I : Issuance D} (h : EventCertifiedSpecificationRAV D P S I)
    (trace : List (Label D × Configuration D))
    (execution : (certifiedTSV D I).Execution (initConfig D) trace) :
    ProjectedSpecificationExecution D P id S (initConfig D) trace :=
  projected_certified_executionsV (fun C reach => (h C reach).heads) trace execution

end Sal.MRDTs.Paper1
