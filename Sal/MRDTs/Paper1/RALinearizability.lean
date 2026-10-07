import Sal.MRDTs.Paper1.HistorySpec
import Sal.MRDTs.Paper1.RestrictedReplay
import Sal.MRDTs.Metatheory.Correctness

/-!
# Explicit replication-aware linearizability

The public criterion is per head and per query, as in the manuscript. It asks
for an admitted projected history, not for implementation replay or an abstract
state relation. Execution/issuance assumptions occur in guarantees and their
proofs, rather than in the configuration predicate.
-/

namespace Sal.MRDTs.Paper1
open Foundation

def projectedUpdates {D : MRDTSig} (events : List (Op D.AppOp)) :
    List (SeqLabel D.AppOp D.Query D.Value) :=
  events.map (fun e => .update e.op)

/-- The paper's configuration-level criterion: `∀ replica query, ∃ history`.
Heads are represented by their allocated version rather than by a partial
query, so no default value is introduced for inactive replicas. -/
def RALinearizable (D : MRDTSig) (P : OperationPolicy D.AppOp)
    (S : HistorySpec D.AppOp D.Query D.Value) (C : Configuration D) : Prop :=
  ∀ r v s E, C.head r = some v → C.ver v = some (s, E) →
    ∀ q, ∃ π : List (Op D.AppOp),
      listPermOf π E ∧ respects π (paperOrder P C.replayContext E) ∧
      S.admits (projectedUpdates π ++ [.query q (D.query s q)])

/-- Stronger than the public criterion, but still permits a different witness
for each query. Historical allocated versions are included. -/
def VersionsRALinearizable (D : MRDTSig) (P : OperationPolicy D.AppOp)
    (S : HistorySpec D.AppOp D.Query D.Value) (C : Configuration D) : Prop :=
  ∀ v s E, C.ver v = some (s, E) → ∀ q,
    ∃ π : List (Op D.AppOp),
      listPermOf π E ∧ respects π (paperOrder P C.replayContext E) ∧
      S.admits (projectedUpdates π ++ [.query q (D.query s q)])

/-- A stronger quantifier order: one update history explains every query at
each allocated version. This is not required by the manuscript criterion. -/
def UniformVersionsRALinearizable (D : MRDTSig) (P : OperationPolicy D.AppOp)
    (S : HistorySpec D.AppOp D.Query D.Value) (C : Configuration D) : Prop :=
  ∀ v s E, C.ver v = some (s, E) →
    ∃ π : List (Op D.AppOp),
      listPermOf π E ∧ respects π (paperOrder P C.replayContext E) ∧
      ∀ q, S.admits (projectedUpdates π ++ [.query q (D.query s q)])

theorem UniformVersionsRALinearizable.versions
    {D : MRDTSig} {P : OperationPolicy D.AppOp}
    {S : HistorySpec D.AppOp D.Query D.Value} {C : Configuration D}
    (h : UniformVersionsRALinearizable D P S C) :
    VersionsRALinearizable D P S C := by
  intro v s E hv q
  obtain ⟨π, hp, hr, accepted⟩ := h v s E hv
  exact ⟨π, hp, hr, accepted q⟩

theorem VersionsRALinearizable.heads {D : MRDTSig} {P : OperationPolicy D.AppOp}
    {S : HistorySpec D.AppOp D.Query D.Value} {C : Configuration D}
    (h : VersionsRALinearizable D P S C) : RALinearizable D P S C := by
  intro r v s E _ hv q
  exact h v s E hv q

/-- An execution satisfies the criterion at its initial configuration and
every successor configuration recorded in the labelled finite trace. Validity
of the execution is a separate premise in implementation guarantees. -/
def RAExecution (D : MRDTSig) (P : OperationPolicy D.AppOp)
    (S : HistorySpec D.AppOp D.Query D.Value) (initial : Configuration D)
    (trace : List (Label D × Configuration D)) : Prop :=
  RALinearizable D P S initial ∧
    ∀ entry ∈ trace, RALinearizable D P S entry.2

def RAImplementation (D : MRDTSig) (P : OperationPolicy D.AppOp)
    (S : HistorySpec D.AppOp D.Query D.Value) : Prop :=
  ∀ trace, (labeledTS D).Execution (initConfig D) trace →
    RAExecution D P S (initConfig D) trace

def RALinearizableOn (D : MRDTSig) (P : OperationPolicy D.AppOp)
    (S : HistorySpec D.AppOp D.Query D.Value)
    (Reach : Configuration D → Prop) : Prop :=
  ∀ C, Reach C → RALinearizable D P S C

def CertifiedRA (D : MRDTSig) (P : OperationPolicy D.AppOp)
    (S : HistorySpec D.AppOp D.Query D.Value) (I : Issuance D) : Prop :=
  RALinearizableOn D P S (MintCertifiedReach D I)

def CertifiedRAV (D : MRDTSig) (P : OperationPolicy D.AppOp)
    (S : HistorySpec D.AppOp D.Query D.Value) (I : Issuance D) : Prop :=
  RALinearizableOn D P S
    (MintCertifiedReachV D (canonicalVirtualMergeBase D) I)

theorem CertifiedRAV.ordinary {D : MRDTSig} {P : OperationPolicy D.AppOp}
    {S : HistorySpec D.AppOp D.Query D.Value} {I : Issuance D}
    (h : CertifiedRAV D P S I) : CertifiedRA D P S I :=
  fun C reach => h C reach.toV

/-- The paper's unrestricted sequential premise. It compares update alone
with an independent language and never mentions merge. -/
def FoldHistorySound (D : MRDTSig) (S : HistorySpec D.AppOp D.Query D.Value) : Prop :=
  ∀ π q, S.admits (projectedUpdates π ++
    [.query q (D.query (applySeq D.toUpdateSig D.init π) q)])

theorem uniform_ra_of_replay_total
    {D : MRDTSig} {P : OperationPolicy D.AppOp}
    {S : HistorySpec D.AppOp D.Query D.Value} {C : Configuration D}
    (laws : RestrictedLaws D.toUpdateSig P)
    (replay : @HasReplayWitness D P.lift C) (sound : FoldHistorySound D S) :
    UniformVersionsRALinearizable D P S C := by
  letI : ReplayPolicy D.toUpdateSig := P.lift
  intro v s E hv
  obtain ⟨π, hp, hr, hf⟩ := replay v s E hv
  refine ⟨π, hp, ?_, ?_⟩
  · exact hr.imp (fun {_ _} h => h ∘ (paperOrder_iff_loOn laws _ _ _ _).mp)
  · intro q
    simpa [hf] using sound π q

theorem ra_of_replay_total {D : MRDTSig} {P : OperationPolicy D.AppOp}
    {S : HistorySpec D.AppOp D.Query D.Value} {C : Configuration D}
    (laws : RestrictedLaws D.toUpdateSig P)
    (replay : @HasReplayWitness D P.lift C) (sound : FoldHistorySound D S) :
    VersionsRALinearizable D P S C := by
  letI : ReplayPolicy D.toUpdateSig := P.lift
  intro v s E hv q
  obtain ⟨π, hp, hr, hf⟩ := replay v s E hv
  refine ⟨π, hp, ?_, ?_⟩
  · exact hr.imp (fun {_ _} h => h ∘ (paperOrder_iff_loOn laws _ _ _ _).mp)
  · simpa [hf] using sound π q

theorem ra_of_canonical_total {D : MRDTSig} {P : OperationPolicy D.AppOp}
    {S : HistorySpec D.AppOp D.Query D.Value} {C : Configuration D}
    (laws : RestrictedLaws D.toUpdateSig P)
    (canonical : @CanonicalConfig D P.lift C) (sound : FoldHistorySound D S) :
    VersionsRALinearizable D P S C := by
  letI : ReplayPolicy D.toUpdateSig := P.lift
  exact ra_of_replay_total laws (hasReplayWitness_of_canonical canonical) sound

/-- An issuance-sensitive bridge can select a suitable replay of a supported,
causally closed event set. It explains the update fold, not a materialized store
state. Canonical uniqueness later identifies that fold with the stored state.
The premise is per query, matching the public criterion. -/
def HistoryAdequate (D : MRDTSig) (P : OperationPolicy D.AppOp)
    (S : HistorySpec D.AppOp D.Query D.Value) (C : ReplayContext D.toUpdateSig)
    (E : Set (Op D.AppOp)) : Prop :=
  ∀ q, ∃ π : List (Op D.AppOp),
    listPermOf π E ∧ respects π (paperOrder P C E) ∧
    S.admits (projectedUpdates π ++
      [.query q (D.query (applySeq D.toUpdateSig D.init π) q)])

def IssuedHistoryAdequacy (D : MRDTSig) (P : OperationPolicy D.AppOp)
    (S : HistorySpec D.AppOp D.Query D.Value) (I : Issuance D) : Prop :=
  ∀ C, MintHonest D I.CanIssue C →
    ∀ E : Set (Op D.AppOp),
      (∀ e ∈ E, e ∈ C.events) →
      (∀ a b, C.vis a b → b ∈ E → a ∈ E) →
      (∃ π, listPermOf π E) → HistoryAdequate D P S C.replayContext E

theorem ra_of_canonical_history {D : MRDTSig} {P : OperationPolicy D.AppOp}
    {S : HistorySpec D.AppOp D.Query D.Value} {I : Issuance D} {C : Configuration D}
    (laws : RestrictedLaws D.toUpdateSig P)
    (canonical : @CanonicalConfig D P.lift C)
    (honest : MintHonest D I.CanIssue C) (adequacy : IssuedHistoryAdequacy D P S I) :
    VersionsRALinearizable D P S C := by
  letI : ReplayPolicy D.toUpdateSig := P.lift
  intro v s E hv q
  have hs := canonical.canonical v s E hv
  obtain ⟨π, hp, hr, accepted⟩ := adequacy C honest E
    (canonical.version_events_supported v s E hv)
    (canonical.version_events_causal v s E hv)
    (by obtain ⟨w, hw, _, _⟩ := hs; exact ⟨w, hw⟩) q
  have hresp : respects π (@loOn D.toUpdateSig P.lift C.replayContext E) :=
    hr.imp (fun {_ _} h => h ∘ (paperOrder_iff_loOn laws _ _ _ _).mpr)
  have heq := isCanonicalState_unique_of_replayLaws laws.replayLaws
    (canonical.version_events_supported v s E hv) hs ⟨π, hp, hresp, rfl⟩
  exact ⟨π, hp, hr, by simpa [heq] using accepted⟩

/-- End-to-end sufficient conditions: contextual Join justified by honest
issuance, restricted replay laws, and projected-history adequacy. -/
theorem certifiedRA_of_join {D : MRDTSig} {P : OperationPolicy D.AppOp}
    {S : HistorySpec D.AppOp D.Query D.Value} {I : Issuance D}
    (laws : RestrictedLaws D.toUpdateSig P)
    (join : ∀ C, MintHonest D I.CanIssue C → @JoinAt D P.lift C.replayContext)
    (history : IssuedHistoryAdequacy D P S I) : CertifiedRAV D P S I := by
  letI : ReplayPolicy D.toUpdateSig := P.lift
  intro C reach
  exact (ra_of_canonical_history laws
    (canonicalConfig_of_mintCertifiedV join reach) reach.mintHonest history).heads

theorem certifiedRA_of_join_total {D : MRDTSig} {P : OperationPolicy D.AppOp}
    {S : HistorySpec D.AppOp D.Query D.Value} {I : Issuance D}
    (laws : RestrictedLaws D.toUpdateSig P)
    (join : ∀ C, MintHonest D I.CanIssue C → @JoinAt D P.lift C.replayContext)
    (sound : FoldHistorySound D S) : CertifiedRAV D P S I := by
  letI : ReplayPolicy D.toUpdateSig := P.lift
  intro C reach
  exact (ra_of_canonical_total laws
    (canonicalConfig_of_mintCertifiedV join reach) sound).heads

end Sal.MRDTs.Paper1
