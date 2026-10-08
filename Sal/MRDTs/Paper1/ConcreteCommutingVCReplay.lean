import Sal.MRDTs.Paper1.ConcreteVCExecution

/-! The commuting production ports instantiate the five concrete merge VCs.
Their Join theorem is derived by the shared metadata induction. -/
namespace Sal.MRDTs.Paper1.ConcreteMRDT.CommutingPort
open Foundation
variable {D : MRDTSig}

abbrev representation (D : MRDTSig) : Representation D := fun C E s =>
  Supported C E ∧ ∃ π : List (Op D.AppOp), listPermOf π E ∧ applySeq D.toUpdateSig D.init π = s

def scheme (commute : ∀ a b, D.toUpdateSig.commutes a b)
    (C : ReplayContext D.toUpdateSig) : MetadataDependencies C where
  before := fun _ _ => False
  causal := fun _ _ h => h.elim
  covers := fun a b _ h => (h (commute a b)).elim

theorem order_empty (commute : ∀ a b, D.toUpdateSig.commutes a b)
    (C : ReplayContext D.toUpdateSig) (E : Set (Op D.AppOp)) (a b : Op D.AppOp) :
    ¬ paperOrder (commutingPolicy D.AppOp) C E a b :=
  paperOrder_false_of_all_commute commute C E a b

theorem past_eq (commute : ∀ a b, D.toUpdateSig.commutes a b)
    (C : ReplayContext D.toUpdateSig) (e : Op D.AppOp) :
    (scheme commute C).Past e = {e} := by
  ext x
  constructor
  · rintro (eq | path)
    · exact eq
    · cases path with
      | single h => exact h.elim
      | tail _ h => exact h.elim
  · exact fun h => Or.inl h

theorem canonical (commute : ∀ a b, D.toUpdateSig.commutes a b)
    (C : ReplayContext D.toUpdateSig) (E : Set (Op D.AppOp)) (s : D.State)
    (h : representation D C E s) : Canonical (commutingPolicy D.AppOp) C E s := by
  obtain ⟨sup,π,hp,hf⟩ := h
  exact ⟨π,hp,hp.1.imp (fun {_ _} _ => order_empty commute C E _ _),hf⟩

theorem unique (commute : ∀ a b, D.toUpdateSig.commutes a b) : Raw.Unique (representation D) := by
  intro C E s t hs ht
  exact canonical_unique (GuardedReplay.ofUniform (restricted_of_all_commute commute)) C E hs.1
    (canonical commute C E s hs) (canonical commute C E t ht)

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

theorem initial : ∀ C E s, representation D C E s → representation D C ∅ D.init := by
  intro C E s _
  exact ⟨fun _ h => h.elim, [], by simp [listPermOf], rfl⟩

theorem finite : ∀ C E s, representation D C E s → ∃ π, listPermOf π E := by
  rintro C E s ⟨_,π,hp,_⟩
  exact ⟨π,hp⟩

theorem replaySupply (commute : ∀ a b, D.toUpdateSig.commutes a b)
    (C : ReplayContext D.toUpdateSig) :
    Raw.ReplaySupply (commutingPolicy D.AppOp) (representation D) (scheme commute) C := by
  classical
  have represented : ∀ E π, listPermOf π E → Supported C E → ∃ s, representation D C E s := by
    intro E π hp sup
    exact ⟨applySeq D.toUpdateSig D.init π,sup,π,hp,rfl⟩
  refine ⟨represented,?_⟩
  intro E s hs sup nonempty _
  obtain ⟨e,he⟩ := nonempty
  obtain ⟨π,hp,_⟩ := hs.2
  obtain ⟨pre,hpre⟩ := enumeration_subset hp (show E \ {e} ⊆ E from fun _ h => h.1)
  obtain ⟨t,ht⟩ := represented _ pre hpre (fun x hx => sup x hx.1)
  have hi : representation D C ∅ D.init := initial C E s hs
  refine ⟨⟨e,he,fun x _ _ => order_empty commute C E e x,
    fun _ _ _ h => h.elim,t,D.init,ht,?_,?_,?_⟩⟩
  · rw [past_eq,Set.diff_self]
    exact hi
  · rw [past_eq]
    exact ⟨fun x hx => sup x (by simpa only [Set.mem_singleton_iff] using hx ▸ he),[e],by simp [listPermOf],rfl⟩
  · obtain ⟨_,pre,hpre,hfold⟩ := ht
    refine ⟨sup,pre ++ [e],?_,?_⟩
    · constructor
      · apply List.Nodup.append hpre.1 (by simp)
        intro x hx hy
        have old := (hpre.2 x).mp hx
        simp only [List.mem_singleton] at hy
        exact old.2 (by simpa only [Set.mem_singleton_iff] using hy)
      · intro x
        simp only [List.mem_append,List.mem_singleton]
        rw [hpre.2]
        simp only [Set.mem_diff,Set.mem_singleton_iff]
        constructor
        · rintro (h | rfl)
          · exact h.1
          · exact he
        · intro hx
          by_cases eq : x = e
          · exact Or.inr eq
          · exact Or.inl ⟨hx,eq⟩
    · rw [applySeq_append_single,hfold]

theorem mergeVCs (commute : ∀ a b, D.toUpdateSig.commutes a b)
    (merge : MergeLaws D) (delta : DeltaLaws D) (peel : CommutingPeelLaw D) :
    Raw.MergeVCs (commutingPolicy D.AppOp) (representation D) (scheme commute) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro C E₁ E₂ l a b _ _ _ _ _ _ _
    exact merge.merge_comm l a b
  · intro C E s _ _ _
    exact merge.merge_init s
  · intro C U s B e trans irrefl sup _ he max _ hs ht _ _
    have hs' : @IsCanonicalState D.toUpdateSig (ReplayPolicy.default _) C (U \ {e}) s := by
      obtain ⟨_,π,hp,hf⟩ := hs
      exact ⟨π,hp,hp.1.imp (fun {_ _} _ => by simp [loOn,UpdateSig.rc,UpdateSig.replayOrder,ReplayPolicy.default,ReplayPolicy.unconstrained]),hf⟩
    have ht' : @IsCanonicalState D.toUpdateSig (ReplayPolicy.default _) C (downset C e \ {e}) B := by
      obtain ⟨_,π,hp,hf⟩ := ht
      rw [past_eq] at hp
      rw [raw_downset_eq commute]
      exact ⟨π,hp,hp.1.imp (fun {_ _} _ => by simp [loOn,UpdateSig.rc,UpdateSig.replayOrder,ReplayPolicy.default,ReplayPolicy.unconstrained]),hf⟩
    exact causalDeltaLaw_of_all_comm merge peel commute C U s B e
      (fun {_ _ _} h k => trans h k) irrefl sup
      (fun a b _ nc _ => (nc (commute a b)).elim) he
      (fun _ _ _ => by simp [loOn,UpdateSig.rc,UpdateSig.replayOrder,ReplayPolicy.default,ReplayPolicy.unconstrained]) hs' ht'
  · intro C E₁ E₂ l B t b e _ _ _ _ _ _ _ _ _ _
    exact delta.local_redistribute l B t (D.update B e) b
  · intro C E₁ E₂ t₀ t₁ t₂ B e _ _ _ _ _ _ _ _ _ _ _ _
    exact delta.redistribute B t₀ t₁ t₂ (D.update B e)

theorem vcJoinAt (commute : ∀ a b, D.toUpdateSig.commutes a b)
    (merge : MergeLaws D) (delta : DeltaLaws D) (peel : CommutingPeelLaw D)
    (C : ReplayContext D.toUpdateSig) : JoinAt D C := by
  intro E₁ E₂ l a b trans irrefl sup₁ sup₂ closed₁ closed₂ hl ha hb
  have rep : ∀ E s, Supported C E → @IsCanonicalState D.toUpdateSig (ReplayPolicy.default _) C E s → representation D C E s := by
    rintro E s sup ⟨π,hp,_,hf⟩
    exact ⟨sup,π,hp,hf⟩
  obtain ⟨π₁,hp₁,_,_⟩ := ha
  obtain ⟨π₂,hp₂,_,_⟩ := hb
  have perm := listPermOf_union (D := D.toUpdateSig) hp₁ hp₂
  have kit := replaySupply commute C
  have sizes := Raw.join_at_sizes (mergeVCs commute merge delta peel)
    (unique commute) initial finite C (fun _ _ _ h k => trans h k) irrefl
    kit.represented kit.peel
  have joined := sizes _ E₁ E₂ l a b _ perm rfl sup₁ sup₂
    (fun _ _ h _ => h.elim) (fun _ _ h _ => h.elim)
    (rep _ _ (fun e h => sup₁ e h.1) hl)
    (rep _ _ sup₁ ⟨π₁,hp₁,by assumption,by assumption⟩)
    (rep _ _ sup₂ ⟨π₂,hp₂,by assumption,by assumption⟩)
  obtain ⟨_,π,hp,hf⟩ := joined
  exact ⟨π,hp,hp.1.imp (fun {_ _} _ => by simp [loOn,UpdateSig.rc,UpdateSig.replayOrder,ReplayPolicy.default,ReplayPolicy.unconstrained]),hf⟩

theorem vcCanonicalConfig (commute : ∀ a b, D.toUpdateSig.commutes a b)
    (merge : MergeLaws D) (delta : DeltaLaws D) (peel : CommutingPeelLaw D)
    {I : Issuance D} {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) I C) : CanonicalConfig C :=
  canonicalConfig_of_mintCertifiedV (fun C _ => vcJoinAt commute merge delta peel C.replayContext) reach

def vcReplayConditions (commute : ∀ a b, D.toUpdateSig.commutes a b)
    (merge : MergeLaws D) (delta : DeltaLaws D) (peel : CommutingPeelLaw D)
    (I : Issuance D) : VCReplayConditions (commutingPolicy D.AppOp) I where
  representation := representation D
  scheme := scheme commute
  laws := GuardedReplay.ofUniform (restricted_of_all_commute commute)
  vcs := mergeVCs commute merge delta peel
  unique := unique commute
  initial := initial
  finite := finite
  canonical := canonical commute
  supported := fun _ _ _ h => h.1
  replaySupply := fun C _ _ _ _ _ _ _ _ _ _ => replaySupply commute C
  representedVersions := by
    intro C reach v s E hv
    have good := vcCanonicalConfig commute merge delta peel reach
    obtain ⟨π,hp,_,hf⟩ := good.canonical v s E hv
    exact ⟨good.version_events_supported v s E hv,π,hp,hf⟩

def scopedConditions (commute : ∀ a b, D.toUpdateSig.commutes a b)
    (merge : MergeLaws D) (delta : DeltaLaws D) (peel : CommutingPeelLaw D)
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} (I : Issuance D)
    (history : EventExecutionHistoryAdequacy D (commutingPolicy D.AppOp) S I) :
    ScopedVCConditions (commutingPolicy D.AppOp) S I where
  toVCReplayConditions := vcReplayConditions commute merge delta peel I
  history := history

end Sal.MRDTs.Paper1.ConcreteMRDT.CommutingPort
