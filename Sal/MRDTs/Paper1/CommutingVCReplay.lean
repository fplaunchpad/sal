import Sal.MRDTs.Paper1.FutureModel
import Sal.MRDTs.Paper1.ScopedHistoryBridge

/-! Reuse concrete VC proofs for the commuting class without assuming Join.
Representation retains exact replay metadata; semantic equality remains the
chosen future-complete abstraction. -/
namespace Sal.MRDTs.Paper1.AbstractMRDT.CommutingPort
open Foundation
variable {D : MRDTSig}

theorem policy_eq (D : MRDTSig) :
    (commutingPolicy D.AppOp).lift = ReplayPolicy.default D.toUpdateSig := by
  unfold OperationPolicy.lift ReplayPolicy.default ReplayPolicy.unconstrained
  congr 1
  funext a b
  simp [commutingPolicy]

abbrev representation (D : MRDTSig) : Representation D :=
  fun C E s => @IsCanonicalState D.toUpdateSig (ReplayPolicy.default _) C E s

def scheme (A : Model D) (commute : ∀ a b, D.toUpdateSig.commutes a b)
    (C : ReplayContext D.toUpdateSig) : MetadataDependencies A C where
  before := fun _ _ => False
  causal := fun _ _ h => h.elim
  covers := fun a b _ h => h (of_state_commutes (commute a b))

theorem raw_order_empty (C : ReplayContext D.toUpdateSig) (E : Set (Op D.AppOp))
    (a b : Op D.AppOp) :
    ¬ @loOn D.toUpdateSig (ReplayPolicy.default _) C E a b := by
  simp [loOn, UpdateSig.rc, UpdateSig.replayOrder,
    ReplayPolicy.default, ReplayPolicy.unconstrained]

theorem order_empty (A : Model D) (commute : ∀ a b, D.toUpdateSig.commutes a b)
    (C : ReplayContext D.toUpdateSig) (E : Set (Op D.AppOp)) (a b : Op D.AppOp) :
    ¬ order A (commutingPolicy D.AppOp) C E a b := by
  simp [order, commutingPolicy, of_state_commutes (A := A) (commute a b)]

theorem past_eq (A : Model D) (commute : ∀ a b, D.toUpdateSig.commutes a b)
    (C : ReplayContext D.toUpdateSig) (e : Op D.AppOp) :
    (scheme A commute C).Past e = {e} := by
  ext x
  constructor
  · rintro (eq | path)
    · exact eq
    · cases path with
      | single h => exact h.elim
      | tail _ h => exact h.elim
  · exact fun h => Or.inl h

theorem raw_downset_eq (commute : ∀ a b, D.toUpdateSig.commutes a b)
    (C : ReplayContext D.toUpdateSig) (e : Op D.AppOp) : downset C e = {e} := by
  ext x
  constructor
  · rintro (eq | path)
    · exact eq
    · cases path with
      | single h => exact (h.2 (commute _ _)).elim
      | tail _ h => exact (h.2 (commute _ _)).elim
  · exact fun h => Or.inl h

theorem canonical (A : Model D) (commute : ∀ a b, D.toUpdateSig.commutes a b) :
    RepresentsCanonical A (commutingPolicy D.AppOp) (representation D) := by
  intro C E s h
  apply canonical_of_concrete (restricted_of_all_commute commute)
    (laws_of_all_commute A commute) C E s
  simpa only [policy_eq] using h

theorem replaySupply (A : Model D) (commute : ∀ a b, D.toUpdateSig.commutes a b)
    (C : ReplayContext D.toUpdateSig) :
    ReplaySupply A (commutingPolicy D.AppOp) (representation D) (scheme A commute) C := by
  classical
  have represented : ∀ E π, listPermOf π E → ∃ s, representation D C E s := by
    intro E π hp
    exact ⟨applySeq D.toUpdateSig D.init π, π, hp,
      hp.1.imp (fun {_ _} _ => raw_order_empty _ _ _ _), rfl⟩
  refine ⟨fun E π hp _ => represented E π hp, ?_⟩
  intro E s hs _ nonempty _
  obtain ⟨e,he⟩ := nonempty
  obtain ⟨π,hp,_,_⟩ := hs
  obtain ⟨pre,hpre⟩ := enumeration_subset hp (show E \ {e} ⊆ E from fun _ h => h.1)
  obtain ⟨t,ht⟩ := represented _ pre hpre
  have hi : representation D C ∅ D.init :=
    ⟨[], by simp [listPermOf], by simp [respects], rfl⟩
  refine ⟨⟨e,he,fun x _ _ => order_empty A commute C E e x,
    fun _ _ _ h => h.elim,t,D.init,⟨canonical A commute _ _ _ ht,ht⟩,
    ?_,?_,?_⟩⟩
  · rw [past_eq, Set.diff_self]
    exact ⟨canonical A commute _ _ _ hi,hi⟩
  · rw [past_eq]
    exact ⟨[e], by simp [listPermOf], by simp [respects], rfl⟩
  · apply isCanonicalState_snoc he (fun x _ _ => raw_order_empty C E e x) ht

theorem mergeVCs (A : Model D) (commute : ∀ a b, D.toUpdateSig.commutes a b)
    (merge : MergeLaws D) (delta : DeltaLaws D) (peel : CommutingPeelLaw D) :
    DependencyMergeVCs A (commutingPolicy D.AppOp) (representation D) (scheme A commute) := by
  have causal := causalDeltaLaw_of_all_comm merge peel commute
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro l a b
    change A.abs _ = A.abs _
    rw [merge.merge_comm]
  · intro C E s _ _
    change A.abs _ = A.abs _
    rw [merge.merge_init]
  · intro C E₁ E₂ s₀ B t₁ s₂ e _ _ _ _ _ _ _ _ _ _ _ _ _
    change A.abs _ = A.abs _
    rw [delta.local_redistribute]
  · intro C E₁ E₂ t₀ t₁ t₂ B e _ _ _ _ _ _ _ _ _ _ _ _ _
    change A.abs _ = A.abs _
    rw [delta.redistribute]
  · intro C U s t e trans irrefl sup _ he _ hs ht
    have ht' : representation D C (downset C e \ {e}) t := by
      simpa only [raw_downset_eq commute, past_eq] using ht.2
    have eq := causal C U s t e (fun {_ _ _} h k => trans h k) irrefl sup
      (fun a b _ nc _ => (nc (commute a b)).elim) he
      (fun x _ _ => raw_order_empty C U e x) hs.2 ht'
    change A.abs _ = A.abs _
    rw [eq]

theorem substitution (A : Model D) (commute : ∀ a b, D.toUpdateSig.commutes a b) :
    MetadataSubstitution A (representation D) := by
  apply metadataSubstitution_of_unique
  intro C E s t supported hs ht
  have replay := (restricted_of_all_commute commute).replayLaws
  rw [policy_eq] at replay
  exact isCanonicalState_unique_of_replayLaws replay supported hs ht

theorem initial : InitialMetadata (representation D) := by
  intro C _ _ _
  exact ⟨[], by simp [listPermOf], by simp [respects], rfl⟩

theorem initMetadata (merge : MergeLaws D) : InitMetadata (representation D) := by
  intro C E s _ hs
  simpa only [merge.merge_init] using hs

theorem symmetry (merge : MergeLaws D) : MergeCommMetadata (representation D) := by
  intro C E₁ E₂ l a b h
  simpa only [merge.merge_comm l a b] using h

theorem causalMetadata (A : Model D) (commute : ∀ a b, D.toUpdateSig.commutes a b)
    (merge : MergeLaws D) (peel : CommutingPeelLaw D) :
    CausalMetadata A (commutingPolicy D.AppOp) (representation D) (scheme A commute) := by
  intro C U s t e trans irrefl sup _ he _ _ hs ht target
  have ht' : representation D C (downset C e \ {e}) t := by
    simpa only [raw_downset_eq commute, past_eq] using ht.2
  have eq := causalDeltaLaw_of_all_comm merge peel commute C U s t e
    (fun {_ _ _} h k => trans h k) irrefl sup
    (fun a b _ nc _ => (nc (commute a b)).elim) he
    (fun x _ _ => raw_order_empty C U e x) hs.2 ht'
  simpa only [eq] using target

theorem localMetadata (A : Model D) (commute : ∀ a b, D.toUpdateSig.commutes a b)
    (delta : DeltaLaws D) :
    LocalMetadata A (commutingPolicy D.AppOp) (representation D) (scheme A commute) := by
  intro C E₁ E₂ s₀ B t₁ s₂ e _ _ _ _ _ _ _ target
  simpa only [delta.local_redistribute] using target

theorem sharedMetadata (A : Model D) (commute : ∀ a b, D.toUpdateSig.commutes a b)
    (delta : DeltaLaws D) :
    SharedMetadata A (commutingPolicy D.AppOp) (representation D) (scheme A commute) := by
  intro C E₁ E₂ t₀ t₁ t₂ B e _ _ _ _ _ _ _ target
  simpa only [delta.redistribute] using target

/-- This Join is derived by the observational metadata induction, not by the
old concrete Join theorem. The raw VC equations discharge its obligations. -/
theorem vcJoinAt (A : Model D) (commute : ∀ a b, D.toUpdateSig.commutes a b)
    (merge : MergeLaws D) (delta : DeltaLaws D) (peel : CommutingPeelLaw D)
    (C : ReplayContext D.toUpdateSig) : JoinAt D C := by
  intro E₁ E₂ l a b trans irrefl sup₁ sup₂ _ _ hl ha hb
  have transitive : Transitive C.vis := fun _ _ _ h k => trans h k
  have kit := replaySupply A commute C
  obtain ⟨π₁,hp₁,_,_⟩ := ha
  obtain ⟨π₂,hp₂,_,_⟩ := hb
  have perm := listPermOf_union (D := D.toUpdateSig) hp₁ hp₂
  have sizes := join_at_sizes (laws_of_all_commute A commute)
    (mergeVCs A commute merge delta peel) (canonical A commute)
    (substitution A commute) initial (initMetadata merge) (symmetry merge)
    (causalMetadata A commute merge peel) (localMetadata A commute delta)
    (sharedMetadata A commute delta) C transitive irrefl kit.represented kit.peel
  exact (sizes _ E₁ E₂ l a b _ perm rfl sup₁ sup₂
    (fun _ _ h _ => h.elim) (fun _ _ h _ => h.elim) hl
    ⟨π₁,hp₁,by assumption,by assumption⟩ ⟨π₂,hp₂,by assumption,by assumption⟩).2

theorem vcCanonicalConfig (A : Model D) (commute : ∀ a b, D.toUpdateSig.commutes a b)
    (merge : MergeLaws D) (delta : DeltaLaws D) (peel : CommutingPeelLaw D)
    {I : Issuance D} {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) I C) : CanonicalConfig C :=
  canonicalConfig_of_mintCertifiedV (fun C _ => vcJoinAt A commute merge delta peel C.replayContext) reach

def vcReplayConditions (A : Model D) (complete : A.QueryComplete)
    (commute : ∀ a b, D.toUpdateSig.commutes a b)
    (merge : MergeLaws D) (delta : DeltaLaws D) (peel : CommutingPeelLaw D)
    (I : Issuance D) : VCReplayConditions A (commutingPolicy D.AppOp) I where
  representation := representation D
  scheme := scheme A commute
  queryComplete := complete
  laws := laws_of_all_commute A commute
  vcs := mergeVCs A commute merge delta peel
  canonical := canonical A commute
  substitute := substitution A commute
  initial := initial
  initMetadata := initMetadata merge
  symmetry := symmetry merge
  causal := causalMetadata A commute merge peel
  localMetadata := localMetadata A commute delta
  sharedMetadata := sharedMetadata A commute delta
  replaySupply := fun C _ _ _ _ _ _ _ _ _ _ => replaySupply A commute C
  representedVersions := fun _ reach => (vcCanonicalConfig A commute merge delta peel reach).canonical

theorem vcSupportedVersions (A : Model D) (commute : ∀ a b, D.toUpdateSig.commutes a b)
    (merge : MergeLaws D) (delta : DeltaLaws D) (peel : CommutingPeelLaw D)
    {I : Issuance D} {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) I C) :
    ∀ v s E, C.ver v = some (s,E) → Supported C.replayContext E :=
  (vcCanonicalConfig A commute merge delta peel reach).version_events_supported

theorem scopedHistory (A : Model D) (commute : ∀ a b, D.toUpdateSig.commutes a b)
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (history : EventExecutionHistoryAdequacy D (commutingPolicy D.AppOp) S I) :
    ExecutionHistoryAdequacy A (commutingPolicy D.AppOp) S I := by
  intro C execution v s E hv q
  obtain ⟨π,hp,_,hs,accepted⟩ := history C execution v s E hv q
  exact ⟨π,hp,hp.1.imp (fun {_ _} _ => order_empty A commute C.replayContext E _ _),hs,accepted⟩

def scopedConditions (A : Model D) (complete : A.QueryComplete)
    (commute : ∀ a b, D.toUpdateSig.commutes a b)
    (merge : MergeLaws D) (delta : DeltaLaws D) (peel : CommutingPeelLaw D)
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} (I : Issuance D)
    (history : EventExecutionHistoryAdequacy D (commutingPolicy D.AppOp) S I) :
    ScopedVCConditions A (commutingPolicy D.AppOp) S I where
  toVCReplayConditions := vcReplayConditions A complete commute merge delta peel I
  supportedVersions := fun _ reach => vcSupportedVersions A commute merge delta peel reach
  history := scopedHistory A commute history

end Sal.MRDTs.Paper1.AbstractMRDT.CommutingPort
