import Sal.MRDTs.Instances.MVRLiveContract
import Mathlib.Data.Finset.Sort

/-! Value-only local write requests for MVR. Preparation captures exactly the
currently observed write identities. It does not turn the concurrent global
multi-value contract into a singleton-register contract. -/
namespace Sal.MRDTs.Paper1.MVRClient
open Foundation
open Instances

abbrev Metadata := Timestamp × Replica

def observedIds (s : MVRLive.State) : List Nat :=
  (s.image Prod.fst).sort (· ≤ ·)

def prepare (s : MVRLive.State) (value : Nat) (metadata : Metadata) : MVRLive.Event :=
  (metadata.1, metadata.2, .write value (observedIds s))

@[simp] theorem observedIds_toFinset (s : MVRLive.State) :
    (observedIds s).toFinset = s.image Prod.fst := Finset.sort_toFinset _ _

@[simp] theorem mem_observedIds (s : MVRLive.State) (id : Nat) :
    id ∈ observedIds s ↔ ∃ value, (id, value) ∈ s := by
  rw [← List.mem_toFinset, observedIds_toFinset, Finset.mem_image]
  constructor
  · rintro ⟨⟨id', value⟩, member, rfl⟩
    exact ⟨value, member⟩
  · rintro ⟨value, member⟩
    exact ⟨(id, value), member, rfl⟩

/-- Preparation depends on write identities, including distinct writes of
the same value, rather than merely on the displayed value set. -/
theorem prepared_targets_exact (s : MVRLive.State) (value : Nat)
    (metadata : Metadata) (id : Nat) :
    id ∈ MVR.overwrites (prepare s value metadata) ↔
      ∃ oldValue, (id, oldValue) ∈ s := by
  simpa [prepare, MVR.overwrites] using mem_observedIds s id

/-- The prepared payload satisfies the exact source issuer, leaving precisely
the source's local freshness check as an obligation on allocated metadata. -/
theorem canIssue_prepare_iff (s : MVRLive.State) (value : Nat) (metadata : Metadata) :
    MVRLive.canIssue (prepare s value metadata) s ↔
      ∀ p ∈ s, p.1 ≠ metadata.1 := by
  simp [MVRLive.canIssue, prepare, MVR.overwrites]

theorem issuance_prepare_iff (s : MVRLive.State) (value : Nat) (metadata : Metadata) :
    MVRLive.issuance.CanIssue (prepare s value metadata) s ↔
      ∀ p ∈ s, p.1 ≠ metadata.1 := canIssue_prepare_iff s value metadata

theorem prepared_replaces (s : MVRLive.State) (value : Nat) (metadata : Metadata)
    (fresh : ∀ p ∈ s, p.1 ≠ metadata.1) :
    MVRLive.update s (prepare s value metadata) = {(metadata.1, value)} := by
  simpa [prepare, MVR.writeValue] using
    MVRLive.issued_write_singleton (prepare s value metadata) s
      ((canIssue_prepare_iff s value metadata).mpr fresh)

theorem prepared_read (s : MVRLive.State) (value : Nat) (metadata : Metadata)
    (fresh : ∀ p ∈ s, p.1 ≠ metadata.1) :
    MVRLive.query (MVRLive.update s (prepare s value metadata)) = {value} := by
  rw [prepared_replaces s value metadata fresh]
  simp [MVRLive.query]

theorem prepared_public_read (s : MVRLive.State) (value : Nat) (metadata : Metadata)
    (fresh : ∀ p ∈ s, p.1 ≠ metadata.1) :
    MVRLive.D.query (MVRLive.update s (prepare s value metadata)) () =
      ({value} : Set Nat) := by
  rw [prepared_replaces s value metadata fresh]
  change MVR.queryValues {(metadata.1, value)} = ({value} : Set Nat)
  ext v
  simp [MVR.queryValues]

/-- The historical representation observes exactly these same identities.
Its freshness test additionally excludes already dead historical writes. -/
theorem historical_issuance_prepare_iff (historical : MVR.MVR.State)
    (s : MVRLive.State) (rel : MVR.stateRel historical s)
    (value : Nat) (metadata : Metadata) :
    MVR.generation.CanIssue (prepare s value metadata) historical ↔
      ∀ v, historical.1 (metadata.1, v) = false := by
  have observed (id : Nat) : id ∈ observedIds s ↔ MVR.mvrVis historical id := by
    rw [mem_observedIds]
    simp only [MVR.mvrVis, MVR.mvrTag]
    constructor
    · rintro ⟨v, member⟩
      obtain ⟨born, alive⟩ := (rel (id, v)).mp member
      exact ⟨⟨v, born⟩, alive⟩
    · rintro ⟨⟨v, born⟩, alive⟩
      exact ⟨v, (rel (id, v)).mpr ⟨born, alive⟩⟩
  change MVR.mvrApplicable (prepare s value metadata) historical ↔ _
  constructor
  · exact fun h => h.1
  · intro fresh
    refine ⟨fresh, ?_⟩
    intro v ids eq id
    have fields : value = v ∧ observedIds s = ids := by
      simpa [prepare] using eq
    rw [← fields.2]
    exact observed id

/-- A certified historical source has no overwritten identity without a
prior birth. This is derived from original issuance and causal closure. -/
theorem historical_dead_has_birth {C : Configuration MVR.MVR}
    (execution : CertifiedExecution MVR.MVR MVR.generation C)
    {version : Version} {historical : MVR.MVR.State} {events : Set (Op MVR.MVROp)}
    (stored : C.ver version = some (historical,events)) {id : Nat}
    (dead : historical.2 id = true) : ∃ value, historical.1 (id,value) = true := by
  letI := MVR.replayOrder
  have good := execution.canonicalConfig (fun C _ => MVR.mvrJoin C.replayContext)
  obtain ⟨ops,enumerates,_,fold⟩ := good.canonical version historical events stored
  have supported := good.version_events_supported version historical events stored
  have closed := good.version_events_causal version historical events stored
  rw [← fold] at dead
  obtain ⟨deletion,member,target⟩ := (MVR.fold_overwrite_iff ops id).mp dead
  obtain ⟨birth,_,causal,same⟩ := MVR.issued_overwrite execution
    (supported deletion ((enumerates.2 deletion).mp member)) target
  have birthMember := (enumerates.2 birth).mpr
    (closed birth deletion causal ((enumerates.2 deletion).mp member))
  refine ⟨MVR.writeValue birth,?_⟩
  rw [← fold]
  exact (MVR.fold_write_iff ops (id,MVR.writeValue birth)).mpr ⟨birth,birthMember,same,rfl⟩

/-- Historical preparation has the same local singleton effect as compact
preparation. The source invariant is obtained from its certified stored view. -/
theorem historical_prepared_replaces {C : Configuration MVR.MVR}
    (execution : CertifiedExecution MVR.MVR MVR.generation C)
    {version : Version} {historical : MVR.MVR.State} {events : Set (Op MVR.MVROp)}
    (stored : C.ver version = some (historical,events))
    (s : MVRLive.State) (rel : MVR.stateRel historical s)
    (value : Nat) (metadata : Metadata)
    (fresh : ∀ oldValue, historical.1 (metadata.1,oldValue) = false) :
    MVR.stateRel (MVR.MVR.update historical (prepare s value metadata))
      {(metadata.1,value)} := by
  have undeleted : historical.2 metadata.1 = false := by
    cases dead : historical.2 metadata.1 with
    | false => rfl
    | true =>
      obtain ⟨oldValue,born⟩ := historical_dead_has_birth execution stored dead
      rw [fresh oldValue] at born
      contradiction
  have notObserved : metadata.1 ∉ observedIds s := by
    intro member
    obtain ⟨oldValue,oldMember⟩ := (mem_observedIds s metadata.1).mp member
    have born := ((rel (metadata.1,oldValue)).mp oldMember).1
    rw [fresh oldValue] at born
    contradiction
  intro pair
  by_cases same : pair = (metadata.1,value)
  · subst pair
    simp [MVR.MVR,MVR.mvrUpdate,prepare,undeleted,notObserved]
  · simp only [Finset.mem_singleton,same,false_iff]
    intro live
    change (historical.1 pair || decide (pair = (metadata.1,value))) = true ∧
      (historical.2 pair.1 || decide (pair.1 ∈ observedIds s)) = false at live
    have oldLive : historical.1 pair = true ∧ historical.2 pair.1 = false := by
      exact ⟨by simpa [same] using live.1,(Bool.or_eq_false_iff.mp live.2).1⟩
    have oldMember := (rel pair).mpr oldLive
    have target : pair.1 ∈ observedIds s :=
      (mem_observedIds s pair.1).mpr ⟨pair.2,oldMember⟩
    simp [target] at live

theorem historical_prepared_public_read {C : Configuration MVR.MVR}
    (execution : CertifiedExecution MVR.MVR MVR.generation C)
    {version : Version} {historical : MVR.MVR.State} {events : Set (Op MVR.MVROp)}
    (stored : C.ver version = some (historical,events))
    (s : MVRLive.State) (rel : MVR.stateRel historical s)
    (value : Nat) (metadata : Metadata)
    (fresh : ∀ oldValue, historical.1 (metadata.1,oldValue) = false) :
    MVR.MVR.query (MVR.MVR.update historical (prepare s value metadata)) () =
      ({value} : Set Nat) := by
  have replacement := historical_prepared_replaces execution stored s rel value metadata fresh
  apply Set.ext
  intro answer
  change (∃ id, (MVR.MVR.update historical (prepare s value metadata)).1 (id,answer) = true ∧
    (MVR.MVR.update historical (prepare s value metadata)).2 id = false) ↔ answer = value
  unfold MVR.stateRel at replacement
  simp only [← replacement]
  simp

theorem historical_issued_prepared_public_read {C : Configuration MVR.MVR}
    (execution : CertifiedExecution MVR.MVR MVR.generation C)
    {version : Version} {historical : MVR.MVR.State} {events : Set (Op MVR.MVROp)}
    (stored : C.ver version = some (historical,events))
    (s : MVRLive.State) (rel : MVR.stateRel historical s)
    (value : Nat) (metadata : Metadata)
    (issued : MVR.generation.CanIssue (prepare s value metadata) historical) :
    MVR.MVR.query (MVR.MVR.update historical (prepare s value metadata)) () =
      ({value} : Set Nat) :=
  historical_prepared_public_read execution stored s rel value metadata
    ((historical_issuance_prepare_iff historical s rel value metadata).mp issued)

/-! Hand-derived PASS+FAIL controls. Equal values do not identify writes;
preparation must capture both tags, including after a concurrent merge. -/
example : observedIds {(1, 10), (2, 10)} = [1, 2] ∧
    observedIds {(1, 10), (2, 10)} ≠ [1] := by
  simp [observedIds, Finset.sort_insert]

example : MVRLive.query {(1, 10)} = MVRLive.query {(1, 10), (2, 10)} ∧
    prepare {(1, 10)} 20 (3, 0) ≠ prepare {(1, 10), (2, 10)} 20 (3, 0) := by
  simp [MVRLive.query, prepare, observedIds, Finset.sort_insert]

example : MVRLive.canIssue (prepare {(1, 10), (2, 20)} 30 (3, 0)) {(1, 10), (2, 20)} ∧
    ¬ MVRLive.canIssue (3, 0, .write 30 [1]) {(1, 10), (2, 20)} := by
  simp only [canIssue_prepare_iff]
  simp [MVRLive.canIssue, MVR.overwrites]
  decide +kernel

example : MVRLive.update {(1, 10), (2, 20)} (prepare {(1, 10), (2, 20)} 30 (3, 0)) =
      {(3, 30)} ∧
    MVRLive.update {(1, 10), (2, 20)} (prepare {(1, 10), (2, 20)} 30 (3, 0)) ≠
      {(2, 20), (3, 30)} := by
  rw [prepared_replaces _ _ _ (by decide)]
  decide +kernel

example : ¬ MVRLive.canIssue (prepare {(1, 10)} 20 (1, 0)) {(1, 10)} ∧
    MVRLive.canIssue (prepare {(1, 10)} 20 (2, 0)) {(1, 10)} := by
  simp only [canIssue_prepare_iff]
  decide +kernel

example : MVRLive.query (MVRLive.merge ∅
      (MVRLive.update ∅ (prepare ∅ 10 (1, 0)))
      (MVRLive.update ∅ (prepare ∅ 20 (2, 1)))) = {10, 20} ∧
    MVRLive.query (MVRLive.merge ∅
      (MVRLive.update ∅ (prepare ∅ 10 (1, 0)))
      (MVRLive.update ∅ (prepare ∅ 20 (2, 1)))) ≠ {20} := by decide

#print axioms issuance_prepare_iff
#print axioms prepared_targets_exact
#print axioms historical_issuance_prepare_iff
#print axioms prepared_replaces
#print axioms prepared_public_read
#print axioms historical_prepared_replaces
#print axioms historical_prepared_public_read
#print axioms historical_issued_prepared_public_read
end Sal.MRDTs.Paper1.MVRClient
