import Sal.ConditionedMRDTs.MRDT_Instances.Peritext_Sided.PeritextSided_StateGC

/-!
# Distributed Sided Peritext state-GC interaction

This module starts the heterogeneous simulation between the uncollected
`Core` state used by the semantic execution and the compact state held by the
runtime.  Render equality alone is deliberately not the simulation relation:
the relation also retains the Fugue knowledge and exact gap map required by a
future mint.
-/

namespace Sal.ConditionedMRDTs.PeritextSided.Interaction

open Sal.Emulation
open Sal.ConditionedMRDTs
open Sal.ConditionedMRDTs.PeritextSided.StateGC
open Sal.ConditionedMRDTs.FuguePolicyGC
open Sal.ConditionedMRDTs.PeritextEmbed.MarkDoc
open Sal.EmbedRGA (OrderedPrefixCode)
open Classical

/-- Embed an uncollected semantic state in the compact runtime carrier.  The
gap map is explicit because it is derived from mint provenance, not from the
visible `SState` alone. -/
def snapshotOfCore (gaps : Finset GapEntry) (s : (Core Γ).State) : CompactState where
  sided := ⟨s.1, gaps⟩
  deleted := osPayloads s.2.1
  marks := osPayloads s.2.2

/-- Rich-text observation of the uncollected semantic state, routed through
the same renderer as the compact carrier. -/
noncomputable def renderCore (gaps : Finset GapEntry) (s : (Core Γ).State)
    (mt : MType) : List (ℕ × Bool) :=
  renderCompact (snapshotOfCore gaps s) mt

/-- The load-bearing full/compact relation.  `source` prevents an arbitrary
gap map from witnessing the relation; `gapExact` connects every lookup to the
same Fugue knowledge whose fold produced the full text.  The structural
fields support future apply/merge proofs, while `renderEq` exposes queries. -/
structure StateRel (Γ : OrderedPrefixCode) (K : Know)
    (full : (Core Γ).State) (compact : CompactState) : Prop where
  source : full.1 = gFold Γ K
  gapExact : GapMapOK K compact.sided.gaps
  textProjection : ∃ keep : ℕ → Bool,
    compact.sided.text =
      (show SState from full.1).filter (fun r => keep r.1)
  textSubset : ∀ r ∈ (show SState from compact.sided.text),
    r ∈ (show SState from full.1)
  liveRetained : ∀ r ∈ (show SState from full.1),
    r.1 ∉ osPayloads full.2.1 →
    r ∈ (show SState from compact.sided.text)
  deletedKnown : ∀ x ∈ osPayloads full.2.1,
    x ∈ sIds (show SState from full.1)
  compactDeletedKnown : ∀ x ∈ compact.deleted,
    x ∈ sIds compact.sided.text
  deleteAgreement : ∀ x ∈ compact.sided.text.map Prod.fst,
    (x ∈ compact.deleted ↔ x ∈ osPayloads full.2.1)
  marksSubset : compact.marks ⊆ osPayloads full.2.2
  marksExact : compact.marks = osPayloads full.2.2
  renderEq : ∀ mt,
    renderCompact compact mt = renderCore compact.sided.gaps full mt

/-- The uncollected embedding is related to itself whenever its gap map is
exact.  This is the non-vacuous initial/PASS constructor used before the first
state-GC transition. -/
theorem StateRel.snapshot {Γ : OrderedPrefixCode} {K : Know}
    {full : (Core Γ).State} {gaps : Finset GapEntry}
    (hsource : full.1 = gFold Γ K) (hgap : GapMapOK K gaps)
    (hdeleted : ∀ x ∈ osPayloads full.2.1,
      x ∈ sIds (show SState from full.1)) :
    StateRel Γ K full (snapshotOfCore gaps full) where
  source := hsource
  gapExact := hgap
  textProjection := ⟨fun _ => true, by simp [snapshotOfCore]⟩
  textSubset := by simp [snapshotOfCore]
  liveRetained := by
    intro r hr _
    exact hr
  deletedKnown := hdeleted
  compactDeletedKnown := by
    simpa [snapshotOfCore] using hdeleted
  deleteAgreement := by simp [snapshotOfCore]
  marksSubset := by simp [snapshotOfCore]
  marksExact := by simp [snapshotOfCore]
  renderEq := by intro mt; rfl

/-- Every related compact state answers the same rich-text query as its
uncollected semantic state. -/
theorem StateRel.query_eq {Γ : OrderedPrefixCode} {K : Know}
    {full : (Core Γ).State} {compact : CompactState}
    (h : StateRel Γ K full compact) (mt : MType) :
    renderCompact compact mt = renderCore compact.sided.gaps full mt :=
  h.renderEq mt

/-- Exact compact gap lookup is a consequence of the simulation relation,
not an independent oracle supplied at each future mint. -/
theorem StateRel.gapObservation_exact {K : Know}
    {full : (Core FuguePolicyGC.Γ).State} {compact : CompactState}
    (h : StateRel FuguePolicyGC.Γ K full compact) {a : ℕ}
    (hret : ∃ g, retainedLiveGap K a = some g) :
    compactGapObservation compact.sided a =
      (fugueChoose FuguePolicyGC.Γ K a,
        gChainOf K (fugueChoose FuguePolicyGC.Γ K a).2) := by
  obtain ⟨g, hg⟩ := hret
  unfold compactGapObservation
  rw [h.gapExact, gapEntryOf_exact, hg]
  rfl

/-- Compact minting agrees with the uncollected Fugue generator for every
anchor whose gap is retained by the simulation relation. -/
theorem StateRel.compactInsertOp_exact {K : Know}
    {full : (Core FuguePolicyGC.Γ).State} {compact : CompactState}
    (h : StateRel FuguePolicyGC.Γ K full compact) {a : ℕ}
    (hret : ∃ g, retainedLiveGap K a = some g) (rep x : ℕ) :
    compactInsertOp FuguePolicyGC.Γ compact.sided rep x a =
      (genInsAfter FuguePolicyGC.Γ K rep x a).op := by
  unfold compactInsertOp
  rw [h.gapObservation_exact hret]
  rfl

/-- Text application preserves the exact projection shape. This is the
mixed-apply algebra needed by the eventual distributed step simulation; the
new insert must be fresh in the full state and retained by the projection. -/
theorem StateRel.textProjection_apply {Γ : OrderedPrefixCode} {K : Know}
    {full : (Core Γ).State} {compact : CompactState}
    (h : StateRel Γ K full compact) (o : Op SOp)
    (hsort : SSorted (show SState from full.1))
    (hfresh : ∀ e π a sd, o.2.2 = SOp.ins e π a sd →
      o.1 ∉ sIds (show SState from full.1)) :
    ∃ keep : ℕ → Bool,
      (∀ e π a sd, o.2.2 = SOp.ins e π a sd → keep o.1 = true) →
      sUpdate Γ compact.sided.text o =
        (sUpdate Γ (show SState from full.1) o).filter
          (fun r => keep r.1) := by
  obtain ⟨keep, hkeep⟩ := h.textProjection
  refine ⟨keep, ?_⟩
  intro hnew
  rw [hkeep]
  exact sUpdate_filter keep (show SState from full.1) o hsort hfresh hnew

/-- A common epoch projection commutes with ternary SidedRGA merge. This is
the same-epoch merge case; differently compacted epochs first need translation
to a common projection. -/
theorem sMergeL_filter (keep : ℕ → Bool) (l a b : SState)
    (ha : SSorted a) (hb : SSorted b)
    (hdisj : ∀ x ∈ a, ∀ y ∈ b,
      Sal.EmbedRGA.sKey x.2.2 = Sal.EmbedRGA.sKey y.2.2 → x = y) :
    sMergeL (l.filter fun r => keep r.1)
        (a.filter fun r => keep r.1) (b.filter fun r => keep r.1) =
      (sMergeL l a b).filter fun r => keep r.1 := by
  apply ssorted_ext
  · apply sMergeL_sorted (List.Pairwise.filter _ ha)
      (List.Pairwise.filter _ hb)
    intro x hx y hy hkey
    exact hdisj x (List.mem_of_mem_filter hx) y
      (List.mem_of_mem_filter hy) hkey
  · exact List.Pairwise.filter _ (sMergeL_sorted ha hb hdisj)
  · intro x
    simp only [sMergeL, mem_sMerge2, List.mem_filter, decide_eq_true_eq,
      sIds, List.mem_map]
    aesop

/-- The epoch-translation boundary for one ternary merge.  All three physical
inputs must represent one common retention predicate before the ordinary
compact merge is allowed to interpret absence relative to the LCA. -/
structure CommonProjectionFrame (l a b : SState)
    (ĉl ĉa ĉb : CompactState) where
  keep : ℕ → Bool
  lproj : ĉl.sided.text = l.filter (fun r => keep r.1)
  aproj : ĉa.sided.text = a.filter (fun r => keep r.1)
  bproj : ĉb.sided.text = b.filter (fun r => keep r.1)

/-- After epoch translation establishes a common projection, physical
ternary text merge is exactly the projection of the uncollected merge. -/
theorem CommonProjectionFrame.merge_text_exact
    {l a b : SState} {ĉl ĉa ĉb : CompactState}
    (F : CommonProjectionFrame l a b ĉl ĉa ĉb)
    (ha : SSorted a) (hb : SSorted b)
    (hdisj : ∀ x ∈ a, ∀ y ∈ b,
      Sal.EmbedRGA.sKey x.2.2 = Sal.EmbedRGA.sKey y.2.2 → x = y) :
    sMergeL ĉl.sided.text ĉa.sided.text ĉb.sided.text =
      (sMergeL l a b).filter (fun r => F.keep r.1) := by
  rw [F.lproj, F.aproj, F.bproj]
  exact sMergeL_filter F.keep l a b ha hb hdisj

/-- An epoch constrains an id only when that id occurs in its semantic text.
This matters for concurrent branches: an old epoch must not veto a fresh id
that exists only in another branch. -/
def epochFactor (s : SState) (keep : ℕ → Bool) (x : ℕ) : Bool :=
  decide (x ∉ sIds s) || keep x

def commonEpochKeep (l a b : SState)
    (kl ka kb : ℕ → Bool) (x : ℕ) : Bool :=
  epochFactor l kl x && epochFactor a ka x && epochFactor b kb x

/-- Drop only the constraints contributed by the other two epochs. The
current epoch's own factor is already represented by its exact projection. -/
def translateText (compact : CompactState) (s₁ s₂ : SState)
    (k₁ k₂ : ℕ → Bool) : CompactState :=
  { compact with sided :=
    { compact.sided with text := compact.sided.text.filter (fun q =>
      epochFactor s₁ k₁ q.1 && epochFactor s₂ k₂ q.1) } }

theorem translateText_exact {full own₁ own₂ : SState}
    {compact : CompactState} {keep k₁ k₂ : ℕ → Bool}
    (hexact : compact.sided.text = full.filter (fun q => keep q.1)) :
    (translateText compact own₁ own₂ k₁ k₂).sided.text =
      full.filter (fun q =>
        keep q.1 && epochFactor own₁ k₁ q.1 && epochFactor own₂ k₂ q.1) := by
  unfold translateText
  simp only
  rw [hexact, List.filter_filter]
  apply List.filter_congr
  intro q hq
  cases keep q.1 <;> cases epochFactor own₁ k₁ q.1 <;>
    cases epochFactor own₂ k₂ q.1 <;> decide

/-- The delete and mark stores are grow-only on guarded Peritext histories.
For grow-only branches, their ternary OR-set merge reduces to union. -/
theorem osMergeL_eq_union {α : Type} [DecidableEq α]
    {l a b : OSState α} (hla : l ⊆ a) (hlb : l ⊆ b) :
    osMergeL l a b = a ∪ b := by
  apply Finset.ext
  intro q
  simp only [mem_osMergeL, Finset.mem_union]
  constructor
  · tauto
  · intro h
    rcases h with ha | hb
    · by_cases hl : q ∈ l
      · exact Or.inl ⟨hl, ha, hlb hl⟩
      · exact Or.inr (Or.inl ⟨ha, hl⟩)
    · by_cases hl : q ∈ l
      · exact Or.inl ⟨hl, hla hl, hb⟩
      · exact Or.inr (Or.inr ⟨hb, hl⟩)

theorem osPayloads_union {α : Type} [DecidableEq α]
    (a b : OSState α) :
    osPayloads (a ∪ b) = osPayloads a ∪ osPayloads b := by
  apply Finset.ext
  intro x
  simp only [osPayloads, Finset.mem_image, Finset.mem_union]
  aesop

/-- State-GC evidence used by the distributed simulation.  The earlier
`AtomicBaseCertificate.gapEvidence : ∃ K, ...` is insufficient here: the
existential could describe a different history.  `sameKnowledge` pins the
post-GC gap map to the exact `K` that generated the semantic source state. -/
structure InteractionGCCertificate {Γ : OrderedPrefixCode} {K : Know}
    {C : Configuration (Core Γ)} {v : Version}
    (full : (Core Γ).State) (compact : CompactState)
    (p : Plan) (newGaps : Finset GapEntry) where
  frontier : FrontierAtomicCertificate C v compact p newGaps
  sameKnowledge : GapMapOK K newGaps
  keepsFullLive : ∀ r ∈ (show SState from full.1),
    r.1 ∉ osPayloads full.2.1 → p.keepText r.1 = true

/-- Collection preserves the structural half of the heterogeneous relation.
The remaining theorem obligation is contextual closure under mixed future
mark/delete delivery and ternary merge; it is intentionally not hidden inside
this constructor. -/
theorem StateRel.collect_structural {Γ : OrderedPrefixCode} {K : Know}
    {C : Configuration (Core Γ)} {v : Version}
    {full : (Core Γ).State} {compact : CompactState}
    {p : Plan} {newGaps : Finset GapEntry}
    (h : StateRel Γ K full compact)
    (cert : InteractionGCCertificate (Γ := Γ) (K := K)
      (C := C) (v := v) full compact p newGaps) :
    let compact' := collectStableBase compact p newGaps
    (GapMapOK K compact'.sided.gaps) ∧
    (∀ r ∈ (show SState from compact'.sided.text),
      r ∈ (show SState from full.1)) ∧
    (∀ r ∈ (show SState from full.1),
      r.1 ∉ osPayloads full.2.1 →
      r ∈ (show SState from compact'.sided.text)) := by
  dsimp only
  constructor
  · exact cert.sameKnowledge
  constructor
  · intro r hr
    apply h.textSubset r
    exact List.mem_of_mem_filter
      (show r ∈ compact.sided.text.filter (fun q => p.keepText q.1) from hr)
  · intro r hr hlive
    have hkeep := cert.keepsFullLive r hr hlive
    have hin := h.liveRetained r hr hlive
    exact List.mem_filter.mpr ⟨hin, by simpa [hkeep]⟩

/-- A frontier-certified atomic base collection preserves the full
heterogeneous relation. This closes the GC transition itself; apply and merge
closure are proved separately so they cannot be smuggled in through the
certificate. -/
theorem StateRel.collect {Γ : OrderedPrefixCode} {K : Know}
    {C : Configuration (Core Γ)} {v : Version}
    {full : (Core Γ).State} {compact : CompactState}
    {p : Plan} {newGaps : Finset GapEntry}
    (h : StateRel Γ K full compact)
    (cert : InteractionGCCertificate (Γ := Γ) (K := K)
      (C := C) (v := v) full compact p newGaps) :
    StateRel Γ K full (collectStableBase compact p newGaps) := by
  have hs := h.collect_structural cert
  refine
    { source := h.source
      gapExact := hs.1
      textProjection := ?_
      textSubset := hs.2.1
      liveRetained := hs.2.2
      deletedKnown := h.deletedKnown
      compactDeletedKnown := ?_
      deleteAgreement := ?_
      marksSubset := ?_
      marksExact := ?_
      renderEq := ?_ }
  · obtain ⟨keep, hkeep⟩ := h.textProjection
    refine ⟨fun x => keep x && p.keepText x, ?_⟩
    unfold collectStableBase trimDeleted StateGC.collect
    simp only
    rw [hkeep, List.filter_filter]
    apply List.filter_congr
    intro r hr
    exact Bool.and_comm _ _
  · intro x hx
    unfold collectStableBase trimDeleted StateGC.collect at hx ⊢
    simp only [Finset.mem_filter] at hx
    exact hx.2
  · intro x hx
    have hxOld : x ∈ compact.sided.text.map Prod.fst := by
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
      exact List.mem_map.mpr
        ⟨r, List.mem_of_mem_filter
          (show r ∈ compact.sided.text.filter (fun q => p.keepText q.1) from hr),
          rfl⟩
    unfold collectStableBase trimDeleted StateGC.collect
    simp only [Finset.mem_filter]
    constructor
    · intro hd
      exact (h.deleteAgreement x hxOld).mp hd.1.1
    · intro hd
      have hdc := (h.deleteAgreement x hxOld).mpr hd
      refine ⟨⟨hdc, ?_⟩, hx⟩
      simpa [cert.frontier.base.keepDeletes x hdc]
  · intro m hm
    unfold collectStableBase trimDeleted StateGC.collect at hm
    simp only at hm
    have hmOld : m ∈ compact.marks := (Finset.mem_filter.mp hm).1
    exact h.marksSubset hmOld
  · unfold collectStableBase trimDeleted StateGC.collect
    simp only
    rw [Finset.filter_eq_self.mpr]
    · exact h.marksExact
    · intro m hm
      simpa [cert.frontier.base.keepMarks m hm]
  · intro mt
    calc
      renderCompact (collectStableBase compact p newGaps) mt =
          renderCompact compact mt :=
        collectStableBase_render_preserved compact p newGaps
          cert.frontier.base mt
      _ = renderCore compact.sided.gaps full mt := h.renderEq mt
      _ = renderCore newGaps full mt := by
        rfl

/-- A materialization at a named epoch projection. Keeping `keep` outside the
existential in `StateRel.textProjection` lets merge require three inputs to be
translated to the same epoch before interpreting absence relative to the LCA. -/
structure StateRelAt (Γ : OrderedPrefixCode) (K : Know) (keep : ℕ → Bool)
    (full : (Core Γ).State) (compact : CompactState) : Prop where
  rel : StateRel Γ K full compact
  exact : compact.sided.text =
    (show SState from full.1).filter (fun r => keep r.1)
  markAnchors : ∀ m ∈ osPayloads full.2.2,
    keep m.start_id = true ∧ keep m.end_id = true

theorem StateRelAt.collect {Γ : OrderedPrefixCode} {K : Know}
    {C : Configuration (Core Γ)} {v : Version}
    {full : (Core Γ).State} {compact : CompactState}
    {keep : ℕ → Bool} {p : Plan} {newGaps : Finset GapEntry}
    (h : StateRelAt Γ K keep full compact)
    (cert : InteractionGCCertificate (Γ := Γ) (K := K)
      (C := C) (v := v) full compact p newGaps) :
    StateRelAt Γ K (fun x => keep x && p.keepText x) full
      (collectStableBase compact p newGaps) := by
  refine ⟨h.rel.collect cert, ?_, ?_⟩
  · unfold collectStableBase trimDeleted StateGC.collect
    simp only
    rw [h.exact, List.filter_filter]
    apply List.filter_congr
    intro r hr
    exact Bool.and_comm _ _
  · intro m hm
    have hmCompact : m ∈ compact.marks := by
      rw [h.rel.marksExact]
      exact hm
    have hp := cert.frontier.base.keepAnchors m hmCompact
    exact ⟨by simp [h.markAnchors m hm, hp.1],
      by simp [h.markAnchors m hm, hp.2]⟩

/-- Three independently compacted versions can always be translated to one
common projection without requiring an absent branch to remember future ids.
This constructs the frame that `merge_text_exact` previously accepted only as
an external premise. -/
noncomputable def commonProjectionFrame_of_epochs
    {Γ : OrderedPrefixCode} {Kl Ka Kb : Know}
    {kl ka kb : ℕ → Bool}
    {l a b : (Core Γ).State} {ĉl ĉa ĉb : CompactState}
    (hl : StateRelAt Γ Kl kl l ĉl)
    (ha : StateRelAt Γ Ka ka a ĉa)
    (hb : StateRelAt Γ Kb kb b ĉb) :
    CommonProjectionFrame (show SState from l.1)
      (show SState from a.1) (show SState from b.1)
      (translateText ĉl a.1 b.1 ka kb)
      (translateText ĉa l.1 b.1 kl kb)
      (translateText ĉb l.1 a.1 kl ka) := by
  let common := commonEpochKeep (show SState from l.1)
    (show SState from a.1) (show SState from b.1) kl ka kb
  refine ⟨common, ?_, ?_, ?_⟩
  · rw [translateText_exact hl.exact]
    apply List.filter_congr
    intro q hq
    have hid : q.1 ∈ sIds (show SState from l.1) :=
      List.mem_map.mpr ⟨q, hq, rfl⟩
    simp [common, commonEpochKeep, epochFactor, hid]
  · rw [translateText_exact ha.exact]
    apply List.filter_congr
    intro q hq
    have hid : q.1 ∈ sIds (show SState from a.1) :=
      List.mem_map.mpr ⟨q, hq, rfl⟩
    simp [common, commonEpochKeep, epochFactor, hid, Bool.and_assoc,
      Bool.and_left_comm, Bool.and_comm]
  · rw [translateText_exact hb.exact]
    apply List.filter_congr
    intro q hq
    have hid : q.1 ∈ sIds (show SState from b.1) :=
      List.mem_map.mpr ⟨q, hq, rfl⟩
    simp [common, commonEpochKeep, epochFactor, hid, Bool.and_assoc,
      Bool.and_left_comm, Bool.and_comm]

theorem merge_text_after_epoch_translation
    {Γ : OrderedPrefixCode} {Kl Ka Kb : Know}
    {kl ka kb : ℕ → Bool}
    {l a b : (Core Γ).State} {ĉl ĉa ĉb : CompactState}
    (hl : StateRelAt Γ Kl kl l ĉl)
    (hra : StateRelAt Γ Ka ka a ĉa)
    (hrb : StateRelAt Γ Kb kb b ĉb)
    (ha : SSorted (show SState from a.1))
    (hb : SSorted (show SState from b.1))
    (hdisj : ∀ x ∈ (show SState from a.1),
      ∀ y ∈ (show SState from b.1),
      Sal.EmbedRGA.sKey x.2.2 = Sal.EmbedRGA.sKey y.2.2 → x = y) :
    sMergeL (translateText ĉl a.1 b.1 ka kb).sided.text
      (translateText ĉa l.1 b.1 kl kb).sided.text
      (translateText ĉb l.1 a.1 kl ka).sided.text =
    (sMergeL (show SState from l.1) (show SState from a.1)
      (show SState from b.1)).filter
        (commonEpochKeep (show SState from l.1)
          (show SState from a.1) (show SState from b.1) kl ka kb ∘ Prod.fst) := by
  exact (commonProjectionFrame_of_epochs hl hra hrb).merge_text_exact
    ha hb hdisj

/-- Rendering depends only on structural projection facts. This placement
lets both merge and apply closure derive query equivalence. -/
theorem render_projection {keep : ℕ → Bool} {fullText compactText : SState}
    {fullDeleted compactDeleted : Finset ℕ}
    (marks : Finset MarkD) (mt : MType)
    (hexact : compactText = fullText.filter (fun r => keep r.1))
    (hlive : ∀ r ∈ fullText, r.1 ∉ fullDeleted → r ∈ compactText)
    (hdelete : ∀ x ∈ compactText.map Prod.fst,
      x ∈ compactDeleted ↔ x ∈ fullDeleted)
    (hnd : fullText.map Prod.fst |>.Nodup)
    (hanchors : ∀ m ∈ marks,
      keep m.start_id = true ∧ keep m.end_id = true) :
    renderMarksDoc (docOfS compactText compactDeleted) marks.toList mt =
      renderMarksDoc (docOfS fullText fullDeleted) marks.toList mt := by
  have hdead : ∀ c ∈ (docOfS fullText fullDeleted).birthIds,
      keep c = false →
      (docOfS fullText fullDeleted).deleted.contains c = true := by
    intro c hc hk
    have hcS : c ∈ fullText.map Prod.fst := by
      simpa [docOfS, DocD.birthIds, List.map_map] using hc
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hcS
    have hd : r.1 ∈ fullDeleted := by
      by_contra hn
      have hmem := hlive r hr hn
      rw [hexact] at hmem
      have hktrue := (List.mem_filter.mp hmem).2
      rw [hk] at hktrue
      contradiction
    simpa [docOfS] using hd
  have hdel : ∀ c ∈ (docOfS (fullText.filter (fun r => keep r.1))
      fullDeleted).birthIds,
      compactDeleted.toList.contains c =
        (docOfS (fullText.filter (fun r => keep r.1))
          fullDeleted).deleted.contains c := by
    intro c hc
    have hcS : c ∈ (fullText.filter
        (fun r => keep r.1)).map Prod.fst := by
      simpa [docOfS, DocD.birthIds, List.map_map] using hc
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hcS
    have hrCompact : r ∈ compactText := by
      rw [hexact]
      exact hr
    have hx : r.1 ∈ compactText.map Prod.fst :=
      List.mem_map.mpr ⟨r, hrCompact, rfl⟩
    simp [docOfS, hdelete r.1 hx]
  rw [hexact]
  let d := docOfS (fullText.filter (fun r => keep r.1)) fullDeleted
  have hdelEq := PeritextEmbed.MarksGC.renderMarksDoc_deleted_congr
    d compactDeleted.toList marks.toList mt hdel
  rw [show docOfS (fullText.filter (fun r => keep r.1))
      compactDeleted = { d with deleted := compactDeleted.toList } by rfl,
    hdelEq]
  dsimp [d]
  rw [docOfS_filter]
  apply PeritextEmbed.MarksGC.renderMarksDoc_dropDoc
  · simpa [docOfS, DocD.birthIds] using hnd
  · exact hdead
  · intro m hm
    exact hanchors m (by simpa using hm)

/-! ## Certified cross-epoch merge -/

noncomputable def compactMergeAt (keep : ℕ → Bool)
    (l a b : CompactState) (newGaps : Finset GapEntry) : CompactState :=
  let text := sMergeL l.sided.text a.sided.text b.sided.text
  { sided := ⟨text, newGaps⟩
    deleted := (a.deleted ∪ b.deleted).filter fun x => x ∈ sIds text
    marks := a.marks ∪ b.marks }

/-- Evidence supplied by epoch lineage and the delayed-reference protocol.
The certificate does not assume `StateRelAt` for the result. It records the
specific coverage facts needed when a concurrent mark makes an old endpoint
relevant again. -/
structure MergeCoverageCertificate (keep : ℕ → Bool)
    (fullText : SState) (fullDeleted : Finset ℕ)
    (compact : CompactState) : Prop where
  liveKept : ∀ q ∈ fullText, q.1 ∉ fullDeleted → keep q.1 = true
  deleteAgreement : ∀ x ∈ compact.sided.text.map Prod.fst,
    (x ∈ compact.deleted ↔ x ∈ fullDeleted)
  markAnchors : ∀ m ∈ compact.marks,
    keep m.start_id = true ∧ keep m.end_id = true

/-- The runtime-facing form of merge coverage.  Unlike
`MergeCoverageCertificate`, it mentions only inspectable materialized state:
live records and mark endpoints are physically present, and delete bits agree
for every physically present record.  Epoch translation establishes `exact`;
this lemma turns those concrete checks into the abstract keep-predicate facts
used by the simulation proof. -/
structure PhysicalMergeEvidence (fullText : SState)
    (fullDeleted : Finset ℕ) (compact : CompactState) : Prop where
  livePresent : ∀ q ∈ fullText, q.1 ∉ fullDeleted →
    q ∈ compact.sided.text
  deleteAgreement : ∀ x ∈ compact.sided.text.map Prod.fst,
    (x ∈ compact.deleted ↔ x ∈ fullDeleted)
  markEndpointsPresent : ∀ m ∈ compact.marks,
    m.start_id ∈ compact.sided.text.map Prod.fst ∧
      m.end_id ∈ compact.sided.text.map Prod.fst

theorem PhysicalMergeEvidence.toCoverage {keep : ℕ → Bool}
    {fullText : SState} {fullDeleted : Finset ℕ}
    {compact : CompactState}
    (h : PhysicalMergeEvidence fullText fullDeleted compact)
    (hexact : compact.sided.text =
      fullText.filter (fun q => keep q.1)) :
    MergeCoverageCertificate keep fullText fullDeleted compact := by
  refine ⟨?_, h.deleteAgreement, ?_⟩
  · intro q hq hlive
    have hp := h.livePresent q hq hlive
    rw [hexact] at hp
    exact (List.mem_filter.mp hp).2
  · intro m hm
    have endpointKept : ∀ x, x ∈ compact.sided.text.map Prod.fst →
        keep x = true := by
      intro x hx
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
      rw [hexact] at hq
      exact (List.mem_filter.mp hq).2
    exact ⟨endpointKept m.start_id (h.markEndpointsPresent m hm).1,
      endpointKept m.end_id (h.markEndpointsPresent m hm).2⟩

/-- Construct the live-record part of physical coverage from the two source
relations and the add-only birth-shadow merge used by the runtime.  Only the
two genuinely frontier-sensitive facts remain explicit: deletion evidence and
mark-endpoint availability. -/
theorem PhysicalMergeEvidence.of_sources {Γ : OrderedPrefixCode}
    {Ka Kb : Know} {ka kb : ℕ → Bool}
    {a b : (Core Γ).State} {ĉa ĉb out : CompactState}
    (ha : StateRelAt Γ Ka ka a ĉa)
    (hb : StateRelAt Γ Kb kb b ĉb)
    (birthOrigin : ∀ q ∈ sMergeL ([] : SState) a.1 b.1,
      q ∈ (show SState from a.1) ∨ q ∈ (show SState from b.1))
    (birthsFromA : ∀ q ∈ ĉa.sided.text, q ∈ out.sided.text)
    (birthsFromB : ∀ q ∈ ĉb.sided.text, q ∈ out.sided.text)
    (deleteAgreement : ∀ x ∈ out.sided.text.map Prod.fst,
      (x ∈ out.deleted ↔ x ∈ (osPayloads a.2.1 ∪ osPayloads b.2.1)))
    (markEndpointsPresent : ∀ m ∈ out.marks,
      m.start_id ∈ out.sided.text.map Prod.fst ∧
        m.end_id ∈ out.sided.text.map Prod.fst) :
    PhysicalMergeEvidence (sMergeL ([] : SState) a.1 b.1)
      (osPayloads a.2.1 ∪ osPayloads b.2.1) out := by
  refine ⟨?_, deleteAgreement, markEndpointsPresent⟩
  intro q hq hlive
  rcases birthOrigin q hq with hqa | hqb
  · apply birthsFromA q
    apply ha.rel.liveRetained q hqa
    exact fun hdel => hlive (Finset.mem_union_left _ hdel)
  · apply birthsFromB q
    apply hb.rel.liveRetained q hqb
    exact fun hdel => hlive (Finset.mem_union_right _ hdel)

/-- Evidence for a compact result computed from the two branch heads.  The
semantic LCA (ordinary or virtual) remains ghost state: no compact LCA
materialization occurs in this certificate. -/
structure HeadOnlyMergeCertificate {Γ : OrderedPrefixCode} (Km : Know)
    (keep : ℕ → Bool) (full : (Core Γ).State) (out : CompactState) : Prop where
  source : full.1 = gFold Γ Km
  gapExact : GapMapOK Km out.sided.gaps
  exact : out.sided.text =
    (show SState from full.1).filter (fun r => keep r.1)
  liveRetained : ∀ r ∈ (show SState from full.1),
    r.1 ∉ osPayloads full.2.1 → r ∈ out.sided.text
  deletedKnown : ∀ x ∈ osPayloads full.2.1,
    x ∈ sIds (show SState from full.1)
  compactDeletedKnown : ∀ x ∈ out.deleted, x ∈ sIds out.sided.text
  deleteAgreement : ∀ x ∈ out.sided.text.map Prod.fst,
    (x ∈ out.deleted ↔ x ∈ osPayloads full.2.1)
  marksExact : out.marks = osPayloads full.2.2
  markAnchors : ∀ m ∈ osPayloads full.2.2,
    keep m.start_id = true ∧ keep m.end_id = true
  fullNodup : (show SState from full.1).map Prod.fst |>.Nodup

/-- A head-only physical merge certificate constructs the complete
continuation relation.  In particular, this theorem does not assume or
produce a materialization of an ordinary or virtual LCA. -/
theorem HeadOnlyMergeCertificate.related {Γ : OrderedPrefixCode}
    {Km : Know} {keep : ℕ → Bool} {full : (Core Γ).State}
    {out : CompactState}
    (c : HeadOnlyMergeCertificate Km keep full out) :
    StateRelAt Γ Km keep full out := by
  refine ⟨{
    source := c.source
    gapExact := c.gapExact
    textProjection := ⟨keep, c.exact⟩
    textSubset := ?_
    liveRetained := c.liveRetained
    deletedKnown := c.deletedKnown
    compactDeletedKnown := c.compactDeletedKnown
    deleteAgreement := c.deleteAgreement
    marksSubset := ?_
    marksExact := c.marksExact
    renderEq := ?_ }, c.exact, c.markAnchors⟩
  · intro r hr
    rw [c.exact] at hr
    exact List.mem_of_mem_filter hr
  · rw [c.marksExact]
  · intro mt
    unfold renderCompact renderCore
    simp only [snapshotOfCore]
    rw [c.marksExact]
    exact render_projection (osPayloads full.2.2) mt c.exact
      c.liveRetained c.deleteAgreement c.fullNodup c.markAnchors

private theorem osMergeL_union_of_subset {α : Type} [DecidableEq α]
    {l a b : OSState α} (hla : l ⊆ a) (hlb : l ⊆ b) :
    osMergeL l a b = a ∪ b := by
  apply Finset.ext
  intro q
  simp only [mem_osMergeL, Finset.mem_union]
  constructor
  · tauto
  · intro h
    rcases h with ha | hb
    · by_cases hl : q ∈ l
      · exact Or.inl ⟨hl, ha, hlb hl⟩
      · exact Or.inr (Or.inl ⟨ha, hl⟩)
    · by_cases hl : q ∈ l
      · exact Or.inl ⟨hl, hla hl, hb⟩
      · exact Or.inr (Or.inr ⟨hb, hl⟩)

set_option maxHeartbeats 800000 in
/-- Full heterogeneous merge closure. Text alignment is proved by
`CommonProjectionFrame`; stability supplies deletion and delayed mark-anchor
coverage. The theorem reconstructs every field of the post-merge relation and
derives rendering rather than accepting it as certificate data. -/
theorem StateRelAt.merge {Γ : OrderedPrefixCode}
    {Kl Ka Kb Km : Know} {kl ka kb keep : ℕ → Bool}
    {l a b : (Core Γ).State} {ĉl ĉa ĉb : CompactState}
    (hl : StateRelAt Γ Kl kl l ĉl)
    (ha : StateRelAt Γ Ka ka a ĉa)
    (hb : StateRelAt Γ Kb kb b ĉb)
    (F : CommonProjectionFrame (show SState from l.1)
      (show SState from a.1) (show SState from b.1) ĉl ĉa ĉb)
    (hkeep : F.keep = keep)
    (hsubDelA : (show OSState ℕ from l.2.1) ⊆ a.2.1)
    (hsubDelB : (show OSState ℕ from l.2.1) ⊆ b.2.1)
    (hsubMarkA : (show OSState MarkD from l.2.2) ⊆ a.2.2)
    (hsubMarkB : (show OSState MarkD from l.2.2) ⊆ b.2.2)
    (hsortA : SSorted (show SState from a.1))
    (hsortB : SSorted (show SState from b.1))
    (hdisj : ∀ x ∈ (show SState from a.1),
      ∀ y ∈ (show SState from b.1),
      Sal.EmbedRGA.sKey x.2.2 = Sal.EmbedRGA.sKey y.2.2 → x = y)
    (hmergeA : ∀ q ∈ (show SState from a.1),
      q ∈ sMergeL (show SState from l.1) a.1 b.1)
    (hmergeB : ∀ q ∈ (show SState from b.1),
      q ∈ sMergeL (show SState from l.1) a.1 b.1)
    (newGaps : Finset GapEntry)
    (hsource : sMergeL (show SState from l.1)
      (show SState from a.1) (show SState from b.1) = gFold Γ Km)
    (hgap : GapMapOK Km newGaps)
    (hcoverage : MergeCoverageCertificate keep
      (sMergeL (show SState from l.1) (show SState from a.1)
        (show SState from b.1))
      (osPayloads a.2.1 ∪ osPayloads b.2.1)
      (compactMergeAt keep ĉl ĉa ĉb newGaps))
    (hmarks : (compactMergeAt keep ĉl ĉa ĉb newGaps).marks =
      osPayloads a.2.2 ∪ osPayloads b.2.2)
    (hnd : (sMergeL (show SState from l.1)
      (show SState from a.1) (show SState from b.1)).map Prod.fst |>.Nodup) :
    StateRelAt Γ Km keep
      (sMergeL (show SState from l.1) (show SState from a.1)
          (show SState from b.1),
        (osMergeL (show OSState ℕ from l.2.1)
            (show OSState ℕ from a.2.1) (show OSState ℕ from b.2.1),
          osMergeL (show OSState MarkD from l.2.2)
            (show OSState MarkD from a.2.2) (show OSState MarkD from b.2.2)))
      (compactMergeAt keep ĉl ĉa ĉb newGaps) := by
  let fullText := sMergeL (show SState from l.1)
    (show SState from a.1) (show SState from b.1)
  let fullDeleted := osPayloads a.2.1 ∪ osPayloads b.2.1
  let compact' := compactMergeAt keep ĉl ĉa ĉb newGaps
  have hexact : compact'.sided.text =
      fullText.filter (fun q => keep q.1) := by
    dsimp [compact', fullText, compactMergeAt]
    rw [← hkeep]
    exact F.merge_text_exact hsortA hsortB hdisj
  have hdelMerge : osMergeL (show OSState ℕ from l.2.1)
      (show OSState ℕ from a.2.1) (show OSState ℕ from b.2.1) =
      (show OSState ℕ from a.2.1) ∪ (show OSState ℕ from b.2.1) :=
    osMergeL_union_of_subset hsubDelA hsubDelB
  have hmarkMerge : osMergeL (show OSState MarkD from l.2.2)
      (show OSState MarkD from a.2.2) (show OSState MarkD from b.2.2) =
      (show OSState MarkD from a.2.2) ∪ (show OSState MarkD from b.2.2) :=
    osMergeL_union_of_subset hsubMarkA hsubMarkB
  have hdelPayload : osPayloads (osMergeL
      (show OSState ℕ from l.2.1) a.2.1 b.2.1) = fullDeleted := by
    rw [hdelMerge]
    apply Finset.ext
    intro z
    simp only [osPayloads, Finset.mem_image, Finset.mem_union, fullDeleted]
    aesop
  have hmarkPayload : osPayloads (osMergeL
      (show OSState MarkD from l.2.2) a.2.2 b.2.2) = compact'.marks := by
    rw [hmarkMerge]
    have : osPayloads ((show OSState MarkD from a.2.2) ∪ b.2.2) =
        osPayloads a.2.2 ∪ osPayloads b.2.2 := by
      apply Finset.ext
      intro z
      simp only [osPayloads, Finset.mem_image, Finset.mem_union]
      aesop
    rw [this]
    exact hmarks.symm
  have hsubset : ∀ q ∈ compact'.sided.text, q ∈ fullText := by
    intro q hq
    rw [hexact] at hq
    exact (List.mem_filter.mp hq).1
  have hlive : ∀ q ∈ fullText, q.1 ∉ fullDeleted →
      q ∈ compact'.sided.text := by
    intro q hq hn
    rw [hexact]
    exact List.mem_filter.mpr ⟨hq, hcoverage.liveKept q hq hn⟩
  have hdeletedKnown : ∀ x ∈ fullDeleted, x ∈ sIds fullText := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (ha.rel.deletedKnown x hx)
      exact List.mem_map.mpr ⟨q, hmergeA q hq, rfl⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (hb.rel.deletedKnown x hx)
      exact List.mem_map.mpr ⟨q, hmergeB q hq, rfl⟩
  refine
    { rel :=
        { source := hsource
          gapExact := hgap
          textProjection := ⟨keep, hexact⟩
          textSubset := hsubset
          liveRetained := ?_
          deletedKnown := ?_
          compactDeletedKnown := ?_
          deleteAgreement := ?_
          marksSubset := by rw [hmarkPayload]
          marksExact := hmarkPayload.symm
          renderEq := ?_ }
      exact := hexact
      markAnchors := ?_ }
  · simpa [fullText, fullDeleted, hdelPayload] using hlive
  · simpa [fullText, fullDeleted, hdelPayload] using hdeletedKnown
  · intro x hx
    unfold compactMergeAt at hx ⊢
    simp only [Finset.mem_filter] at hx
    exact hx.2
  · intro x hx
    simpa [fullDeleted, hdelPayload] using hcoverage.deleteAgreement x hx
  · intro mt
    unfold renderCompact renderCore
    simp only [snapshotOfCore]
    rw [hmarkPayload, hdelPayload]
    exact render_projection compact'.marks mt hexact hlive
      hcoverage.deleteAgreement hnd hcoverage.markAnchors
  · intro m hm
    change m ∈ osPayloads (osMergeL (show OSState MarkD from l.2.2)
      a.2.2 b.2.2) at hm
    rw [hmarkPayload] at hm
    exact hcoverage.markAnchors m hm

/-! ## Distributed physical materializations -/

/-- A compact epoch may discard only identifiers at or below its Lamport
frontier.  This is proof metadata: the runtime stores the frontier and the
compacted state, not a permanent set of reclaimed identifiers. -/
structure FrontierProjection (keep : ℕ → Bool) where
  frontier : ℕ
  dropped_below : ∀ x, keep x = false → x ≤ frontier

theorem FrontierProjection.keep_future {keep : ℕ → Bool}
    (h : FrontierProjection keep) {x : ℕ} (hx : h.frontier < x) :
    keep x = true := by
  cases hk : keep x with
  | false => exact absurd (h.dropped_below x hk) (Nat.not_le_of_lt hx)
  | true => rfl

/-- Frontier projections compose across repeated state GC. The later frontier
must dominate the earlier one, and the new plan may reject only ids below the
later frontier. -/
def FrontierProjection.andPlan {keep plan : ℕ → Bool}
    (h : FrontierProjection keep) (next : ℕ)
    (hmono : h.frontier ≤ next)
    (hplan : ∀ x, plan x = false → x ≤ next) :
    FrontierProjection (fun x => keep x && plan x) := by
  refine ⟨next, ?_⟩
  intro x hx
  simp only [Bool.and_eq_false_iff] at hx
  rcases hx with hx | hx
  · exact Nat.le_trans (h.dropped_below x hx) hmono
  · exact hplan x hx

/-- Timestamp freshness alone is too weak for the frontier argument. A fresh
scalar can still be below an old scalar. This FAIL control prevents the proof
from silently replacing Lamport monotonicity with mere inequality. -/
theorem fresh_timestamp_need_not_exceed_frontier :
    (50 : ℕ) ≠ 100 ∧ ¬(100 : ℕ) < 50 := by decide

/-- The runtime Lamport contract needed after a settled cut. `after` is
separate from `Step3`'s store-wide freshness because the latter states only
non-collision. -/
def MintAfterFrontier (frontier timestamp : ℕ) : Prop :=
  frontier < timestamp

/-- The scalar frontier is the maximum timestamp of a settled cut. The empty
cut uses zero. -/
structure CutFrontier {D : ConditionedMRDTSig}
    (cut : Set (Op D.AppOp)) (frontier : ℕ) : Prop where
  upper : ∀ e ∈ cut, e.1 ≤ frontier
  zero_or_attained : frontier = 0 ∨ ∃ e ∈ cut, e.1 = frontier

/-- Causal Lamport minting turns a cut frontier into the exact
`MintAfterFrontier` fact consumed by compact application. -/
theorem mintAfterFrontier_of_causalClock {D : ConditionedMRDTSig}
    {C : Configuration D} {r : Replica} {t : Timestamp}
    {cut : Set (Op D.AppOp)} {frontier : ℕ}
    (hclock : CausalClockedAt D C r t)
    (hcut : CutFrontier cut frontier)
    (hcutHead : ∀ v s E, C.head r = some v → C.ver v = some (s, E) →
      cut ⊆ E)
    (hpos : 0 < t) : MintAfterFrontier frontier t := by
  rcases hclock with ⟨v, s, E, hhead, hver, hbefore⟩
  rcases hcut.zero_or_attained with rfl | ⟨e, he, het⟩
  · exact hpos
  · rw [← het]
    exact hbefore e (hcutHead v s E hhead hver he)

/-- A physical version owns its compact state and the exact mint knowledge
used by its gap summary. -/
structure Materialized where
  state : CompactState
  knowledge : Know
  keep : ℕ → Bool
  projection : FrontierProjection keep

/-- A Lamport-future insert is retained without recording its identifier in a
tombstone or allowlist. -/
theorem Materialized.keep_mint {m : Materialized} {timestamp : ℕ}
    (hclock : MintAfterFrontier m.projection.frontier timestamp) :
    m.keep timestamp = true :=
  m.projection.keep_future hclock

/-- Discharge the formerly-missing apply premise from the epoch frontier and
the runtime Lamport contract. -/
theorem StateRelAt.text_apply_after_frontier {Γ : OrderedPrefixCode}
    {K : Know} {keep : ℕ → Bool} {full : (Core Γ).State}
    {compact : CompactState} (h : StateRelAt Γ K keep full compact)
    (hp : FrontierProjection keep) (o : Op SOp)
    (hclock : MintAfterFrontier hp.frontier o.1)
    (hsort : SSorted (show SState from full.1))
    (hfresh : ∀ e π a sd, o.2.2 = SOp.ins e π a sd →
      o.1 ∉ sIds (show SState from full.1)) :
    sUpdate Γ compact.sided.text o =
      (sUpdate Γ (show SState from full.1) o).filter
        (fun r => keep r.1) := by
  rw [h.exact]
  apply sUpdate_filter keep (show SState from full.1) o hsort hfresh
  intro _ _ _ _ _
  exact hp.keep_future hclock

/-- The lineage fact retained by an epoch until it is used for apply: its
settled cut is included in the actor's current semantic head. This is not a
post-state simulation assumption. It is the causal bridge supplied by fetch
and descendant-head evolution. -/
structure ApplyEpochFrame {Γ : OrderedPrefixCode}
    (C : Configuration (Core Γ)) (r : Replica) (m : Materialized)
    (cut : Set (Op (Core Γ).AppOp)) : Prop where
  summary : CutFrontier cut m.projection.frontier
  cutAtHead : ∀ v s E, C.head r = some v → C.ver v = some (s, E) → cut ⊆ E

theorem ApplyEpochFrame.mintAfter {Γ : OrderedPrefixCode}
    {C C' : Configuration (Core Γ)} {r : Replica} {m : Materialized}
    {cut : Set (Op (Core Γ).AppOp)} {t : Timestamp}
    {o : (Core Γ).AppOp}
    (F : ApplyEpochFrame C r m cut)
    (hs : ClockedGuardedStep3 (Core Γ) (coreGeneration Γ)
      C (.apply t r o) C') (hpos : 0 < t) :
    MintAfterFrontier m.projection.frontier t :=
  mintAfterFrontier_of_causalClock hs.apply_clock F.summary F.cutAtHead hpos

/-! ## Compact mixed application -/

/-- Execute one product operation on the compact carrier. Text insertion may
change every live-gap observation, so the caller supplies the freshly derived
finite gap encoding. Delete and mark operations use the same grow-only payload
semantics as the corresponding `OSCore` components. -/
noncomputable def compactApply {Γ : OrderedPrefixCode} (s : CompactState)
    (e : Op (Core Γ).AppOp) (newGaps : Finset GapEntry) : CompactState :=
  match e.2.2 with
  | Sum.inl textOp =>
      { s with sided := ⟨sUpdate Γ s.sided.text (e.1, e.2.1, textOp), newGaps⟩ }
  | Sum.inr (Sum.inl deleteOp) =>
      match deleteOp with
      | OSOp.add x => { s with deleted := insert x s.deleted }
      | OSOp.rem x => { s with deleted := s.deleted.erase x }
  | Sum.inr (Sum.inr markOp) =>
      match markOp with
      | OSOp.add m => { s with marks := insert m s.marks }
      | OSOp.rem mid => { s with marks := s.marks.filter (fun m => m.mid ≠ mid) }

@[simp] theorem compactApply_text (s : CompactState) (o : Op SOp)
    (gaps : Finset GapEntry) :
    compactApply (Γ := Γ) s (inlOp o) gaps =
      { s with sided := ⟨sUpdate Γ s.sided.text o, gaps⟩ } := rfl

@[simp] theorem compactApply_delete_add (s : CompactState)
    (t r x : ℕ) (gaps : Finset GapEntry) :
    compactApply (Γ := Γ) s
      (inrOp (A₁ := SOp) (inlOp (A₂ := OSOp PeritextEmbed.MarkDoc.MarkD)
        (t, r, OSOp.add x))) gaps =
      { s with deleted := insert x s.deleted } := rfl

@[simp] theorem compactApply_mark_add (s : CompactState)
    (t r : ℕ) (m : PeritextEmbed.MarkDoc.MarkD)
    (gaps : Finset GapEntry) :
    compactApply (Γ := Γ) s
      (inrOp (A₁ := SOp) (inrOp (A₁ := OSOp ℕ)
        (t, r, OSOp.add m))) gaps =
      { s with marks := insert m s.marks } := rfl

theorem osPayloads_update_add {α : Type} [DecidableEq α]
    (key : α → ℕ) (s : OSState α) (t r : ℕ) (x : α) :
    osPayloads (osUpdate key s (t, r, OSOp.add x)) =
      insert x (osPayloads s) := by
  unfold osPayloads osUpdate
  ext y
  simp

/-- Mark application preserves the exact physical/semantic mark payload set.
This is the algebraic part of future mark closure; rendered closure then sees
identical text, deletions, and marks on both sides. -/
theorem marksExact_update_add {Γ : OrderedPrefixCode} {K : Know}
    {full : (Core Γ).State} {compact : CompactState}
    (h : StateRel Γ K full compact) (t r : ℕ)
    (m : PeritextEmbed.MarkDoc.MarkD) :
    insert m compact.marks =
      osPayloads (osUpdate MarkD.mid full.2.2 (t, r, OSOp.add m)) := by
  rw [osPayloads_update_add, h.marksExact]

/-- The structural relation is contextual in the mark list: any mark set whose
boundaries are retained renders identically on the compact projection and the
full text. -/
theorem StateRelAt.render_with_marks {Γ : OrderedPrefixCode} {K : Know}
    {keep : ℕ → Bool} {full : (Core Γ).State} {compact : CompactState}
    (h : StateRelAt Γ K keep full compact)
    (marks : Finset MarkD) (mt : MType)
    (hnd : (show SState from full.1).map Prod.fst |>.Nodup)
    (hanchors : ∀ m ∈ marks,
      keep m.start_id = true ∧ keep m.end_id = true) :
    renderCompact { compact with marks := marks } mt =
      renderCompact { snapshotOfCore compact.sided.gaps full with
        marks := marks } mt := by
  unfold renderCompact
  simp only [snapshotOfCore]
  exact render_projection marks mt h.exact h.rel.liveRetained
    h.rel.deleteAgreement hnd hanchors

/-- Adding one runtime mark preserves the full heterogeneous relation when
the guarded endpoints are retained. -/
theorem StateRelAt.mark_add {Γ : OrderedPrefixCode} {K : Know}
    {keep : ℕ → Bool} {full : (Core Γ).State} {compact : CompactState}
    (h : StateRelAt Γ K keep full compact) (t r : ℕ) (m : MarkD)
    (hnd : (show SState from full.1).map Prod.fst |>.Nodup)
    (hmanchors : keep m.start_id = true ∧ keep m.end_id = true) :
    StateRelAt Γ K keep
      (full.1, (full.2.1, osUpdate MarkD.mid full.2.2
        (t, r, OSOp.add m)))
      { compact with marks := insert m compact.marks } := by
  let full' : (Core Γ).State :=
    (full.1, (full.2.1, osUpdate MarkD.mid full.2.2
      (t, r, OSOp.add m)))
  let compact' : CompactState := { compact with marks := insert m compact.marks }
  have hmarks : compact'.marks = osPayloads full'.2.2 := by
    dsimp [compact', full']
    exact marksExact_update_add h.rel t r m
  refine
    { rel :=
        { source := h.rel.source
          gapExact := h.rel.gapExact
          textProjection := h.rel.textProjection
          textSubset := h.rel.textSubset
          liveRetained := h.rel.liveRetained
          deletedKnown := h.rel.deletedKnown
          compactDeletedKnown := h.rel.compactDeletedKnown
          deleteAgreement := h.rel.deleteAgreement
          marksSubset := by rw [hmarks]
          marksExact := hmarks
          renderEq := ?_ }
      exact := h.exact
      markAnchors := ?_ }
  · intro mt
    have hr := h.render_with_marks compact'.marks mt hnd (by
      intro q hq
      rw [hmarks] at hq
      rw [osPayloads_update_add] at hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact hmanchors
      · exact h.markAnchors q hq)
    change renderCompact compact' mt =
      renderCompact { snapshotOfCore compact'.sided.gaps full' with
        marks := osPayloads full'.2.2 } mt
    rw [← hmarks]
    exact hr
  · intro q hq
    rw [osPayloads_update_add] at hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hmanchors
    · exact h.markAnchors q hq

/-- Deleting a known character updates the semantic and compact deletion sets
in lockstep. The text projection and mark endpoints do not change. -/
theorem StateRelAt.delete_add {Γ : OrderedPrefixCode} {K : Know}
    {keep : ℕ → Bool} {full : (Core Γ).State} {compact : CompactState}
    (h : StateRelAt Γ K keep full compact) (t r x : ℕ)
    (hxknown : x ∈ sIds (show SState from full.1))
    (hxnotdeleted : x ∉ osPayloads full.2.1)
    (hnd : (show SState from full.1).map Prod.fst |>.Nodup) :
    StateRelAt Γ K keep
      (full.1, (osUpdate id full.2.1 (t, r, OSOp.add x), full.2.2))
      { compact with deleted := insert x compact.deleted } := by
  let full' : (Core Γ).State :=
    (full.1, (osUpdate id full.2.1 (t, r, OSOp.add x), full.2.2))
  let compact' : CompactState :=
    { compact with deleted := insert x compact.deleted }
  have hdeleted : osPayloads full'.2.1 =
      insert x (osPayloads full.2.1) := by
    dsimp [full']
    exact osPayloads_update_add id full.2.1 t r x
  have hlive : ∀ q ∈ (show SState from full'.1),
      q.1 ∉ osPayloads full'.2.1 → q ∈ compact'.sided.text := by
    intro q hq hn
    apply h.rel.liveRetained q hq
    rw [hdeleted] at hn
    exact fun hold => hn (Finset.mem_insert_of_mem hold)
  have hdelete : ∀ y ∈ compact'.sided.text.map Prod.fst,
      y ∈ compact'.deleted ↔ y ∈ osPayloads full'.2.1 := by
    intro y hy
    dsimp [compact'] at hy ⊢
    rw [hdeleted]
    simp only [Finset.mem_insert]
    exact or_congr_right (h.rel.deleteAgreement y hy)
  have hxcompact : x ∈ sIds compact.sided.text := by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hxknown
    exact List.mem_map.mpr
      ⟨q, h.rel.liveRetained q hq hxnotdeleted, rfl⟩
  refine
    { rel :=
        { source := h.rel.source
          gapExact := h.rel.gapExact
          textProjection := h.rel.textProjection
          textSubset := h.rel.textSubset
          liveRetained := hlive
          deletedKnown := by
            intro y hy
            rw [hdeleted] at hy
            rcases Finset.mem_insert.mp hy with rfl | hy
            · exact hxknown
            · exact h.rel.deletedKnown y hy
          compactDeletedKnown := by
            intro y hy
            dsimp [compact'] at hy ⊢
            rcases Finset.mem_insert.mp hy with rfl | hy
            · exact hxcompact
            · exact h.rel.compactDeletedKnown y hy
          deleteAgreement := hdelete
          marksSubset := h.rel.marksSubset
          marksExact := h.rel.marksExact
          renderEq := ?_ }
      exact := h.exact
      markAnchors := h.markAnchors }
  intro mt
  unfold renderCompact renderCore
  rw [h.rel.marksExact]
  exact render_projection (osPayloads full'.2.2) mt h.exact hlive hdelete
    hnd h.markAnchors

theorem mem_sUpdate_insert_of_fresh {Γ : OrderedPrefixCode}
    {s : SState} {t r e : ℕ} {π : List ℕ} {a : ℕ}
    {sd : Sal.EmbedRGA.Side} (hfresh : t ∉ sIds s) (q : SRec) :
    q ∈ sUpdate Γ s (t, r, SOp.ins e π a sd) ↔
      q ∈ s ∨ q = sRecOf Γ (t, r, SOp.ins e π a sd) := by
  simp [sUpdate, hfresh, mem_sInsert, sRecOf, sCoord]

/-- A frontier-future Fugue insertion preserves the complete compact/full
relation. `newGaps` is recomputed from the extended mint knowledge; this is
the only representation component whose update is not a direct set/list
operation. -/
theorem StateRelAt.text_insert {Γ : OrderedPrefixCode} {K : Know}
    {keep : ℕ → Bool} {full : (Core Γ).State} {compact : CompactState}
    (h : StateRelAt Γ K keep full compact)
    (hp : FrontierProjection keep) (rep x anchor : ℕ)
    (hclock : MintAfterFrontier hp.frontier x)
    (hsort : SSorted (show SState from full.1))
    (hxfresh : x ∉ sIds (show SState from full.1))
    (newGaps : Finset GapEntry)
    (hgap : GapMapOK (K ++ [genInsAfter Γ K rep x anchor]) newGaps)
    (hndPost : (sUpdate Γ (show SState from full.1)
      (genInsAfter Γ K rep x anchor).op).map Prod.fst |>.Nodup) :
    StateRelAt Γ (K ++ [genInsAfter Γ K rep x anchor]) keep
      (sUpdate Γ (show SState from full.1)
          (genInsAfter Γ K rep x anchor).op, full.2)
      { compact with sided :=
        ⟨sUpdate Γ compact.sided.text
          (genInsAfter Γ K rep x anchor).op, newGaps⟩ } := by
  let o := (genInsAfter Γ K rep x anchor).op
  let fullText' := sUpdate Γ (show SState from full.1) o
  let compact' : CompactState :=
    { compact with sided := ⟨sUpdate Γ compact.sided.text o, newGaps⟩ }
  have ho : o = (x, rep, SOp.ins x
      (Sal.EmbedRGA.sidedCoordOf Γ
        (gChainOf K (fugueChoose Γ K anchor).2))
      (fugueChoose Γ K anchor).2 (fugueChoose Γ K anchor).1) :=
    genInsAfter_op Γ K rep x anchor
  have hexact : compact'.sided.text =
      fullText'.filter (fun q => keep q.1) := by
    dsimp [compact', fullText']
    apply h.text_apply_after_frontier hp o hclock hsort
    intro _ _ _ _ _
    simpa [ho] using hxfresh
  have hfullMem : ∀ q, q ∈ fullText' ↔
      q ∈ (show SState from full.1) ∨ q = sRecOf Γ o := by
    intro q
    rw [show o = (x, rep, SOp.ins x
        (Sal.EmbedRGA.sidedCoordOf Γ
          (gChainOf K (fugueChoose Γ K anchor).2))
        (fugueChoose Γ K anchor).2 (fugueChoose Γ K anchor).1) from ho]
    exact mem_sUpdate_insert_of_fresh hxfresh q
  have hlive : ∀ q ∈ fullText', q.1 ∉ osPayloads full.2.1 →
      q ∈ compact'.sided.text := by
    intro q hq hqdel
    rw [hexact]
    apply List.mem_filter.mpr
    refine ⟨hq, ?_⟩
    rcases (hfullMem q).mp hq with hold | hnew
    · have hc := h.rel.liveRetained q hold hqdel
      rw [h.exact] at hc
      exact (List.mem_filter.mp hc).2
    · subst q
      simpa [sRecOf, ho] using hp.keep_future hclock
  have hsubset : ∀ q ∈ compact'.sided.text, q ∈ fullText' := by
    intro q hq
    rw [hexact] at hq
    exact (List.mem_filter.mp hq).1
  have hdelKnown : ∀ y ∈ osPayloads full.2.1, y ∈ sIds fullText' := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (h.rel.deletedKnown y hy)
    exact List.mem_map.mpr ⟨q, (hfullMem q).mpr (Or.inl hq), rfl⟩
  have hcompactDelKnown : ∀ y ∈ compact'.deleted,
      y ∈ sIds compact'.sided.text := by
    intro y hy
    have hold := h.rel.compactDeletedKnown y hy
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hold
    have hq' : q ∈ compact'.sided.text := by
      rw [hexact]
      have hfull : q ∈ fullText' := (hfullMem q).mpr
        (Or.inl (h.rel.textSubset q hq))
      have hqKeep := hq
      rw [h.exact] at hqKeep
      exact List.mem_filter.mpr ⟨hfull, (List.mem_filter.mp hqKeep).2⟩
    exact List.mem_map.mpr ⟨q, hq', rfl⟩
  have hdelete : ∀ y ∈ compact'.sided.text.map Prod.fst,
      y ∈ compact'.deleted ↔ y ∈ osPayloads full.2.1 := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
    rcases (hfullMem q).mp (hsubset q hq) with hold | hnew
    · have holdCompact : q ∈ compact.sided.text := by
        rw [h.exact]
        rw [hexact] at hq
        exact List.mem_filter.mpr ⟨hold, (List.mem_filter.mp hq).2⟩
      exact h.rel.deleteAgreement q.1
        (List.mem_map.mpr ⟨q, holdCompact, rfl⟩)
    · subst q
      have hnfull : x ∉ osPayloads full.2.1 := fun hd =>
        hxfresh (h.rel.deletedKnown x hd)
      have hncompact : x ∉ compact.deleted := by
        intro hd
        obtain ⟨q, hq, heq⟩ := List.mem_map.mp
          (h.rel.compactDeletedKnown x hd)
        apply hxfresh
        exact List.mem_map.mpr ⟨q, h.rel.textSubset q hq, heq⟩
      simpa [compact', sRecOf, ho, hnfull, hncompact]
  refine
    { rel :=
        { source := ?_
          gapExact := hgap
          textProjection := ⟨keep, hexact⟩
          textSubset := hsubset
          liveRetained := hlive
          deletedKnown := hdelKnown
          compactDeletedKnown := hcompactDelKnown
          deleteAgreement := hdelete
          marksSubset := h.rel.marksSubset
          marksExact := h.rel.marksExact
          renderEq := ?_ }
      exact := hexact
      markAnchors := h.markAnchors }
  · dsimp [fullText', o]
    rw [h.rel.source]
    simp [gFold, gOps, sFold_snoc]
  · intro mt
    unfold renderCompact renderCore
    rw [h.rel.marksExact]
    exact render_projection (osPayloads full.2.2) mt hexact hlive hdelete
      hndPost h.markAnchors

/-- Operation-specific proof obligations produced by the compact runtime
mint path. Unlike a post-state simulation hypothesis, each constructor names
only facts checked before or during the concrete operation. -/
inductive CompactApplyCertificate (Γ : OrderedPrefixCode) (K : Know)
    (keep : ℕ → Bool) (full : (Core Γ).State) (compact : CompactState)
    (hp : FrontierProjection keep) :
    (e : Op (Core Γ).AppOp) → Know → Finset GapEntry → Prop
  | text (rep x anchor : ℕ)
      (hclock : MintAfterFrontier hp.frontier x)
      (hsort : SSorted (show SState from full.1))
      (hxfresh : x ∉ sIds (show SState from full.1))
      (newGaps : Finset GapEntry)
      (hgap : GapMapOK (K ++ [genInsAfter Γ K rep x anchor]) newGaps)
      (hndPost : (sUpdate Γ (show SState from full.1)
        (genInsAfter Γ K rep x anchor).op).map Prod.fst |>.Nodup) :
      CompactApplyCertificate Γ K keep full compact hp
        (inlOp (genInsAfter Γ K rep x anchor).op)
        (K ++ [genInsAfter Γ K rep x anchor]) newGaps
  | delete (t rep x : ℕ)
      (hxknown : x ∈ sIds (show SState from full.1))
      (hxnotdeleted : x ∉ osPayloads full.2.1)
      (hnd : (show SState from full.1).map Prod.fst |>.Nodup)
      (newGaps : Finset GapEntry) :
      CompactApplyCertificate Γ K keep full compact hp
        (inrOp (A₁ := SOp)
          (inlOp (A₂ := OSOp MarkD) (t, rep, OSOp.add x))) K newGaps
  | mark (t rep : ℕ) (m : MarkD)
      (hnd : (show SState from full.1).map Prod.fst |>.Nodup)
      (hanchors : keep m.start_id = true ∧ keep m.end_id = true)
      (newGaps : Finset GapEntry) :
      CompactApplyCertificate Γ K keep full compact hp
        (inrOp (A₁ := SOp)
          (inrOp (A₁ := OSOp ℕ) (t, rep, OSOp.add m))) K newGaps

/-- The compact interpreter simulates every certified mixed apply. This is
the local transition theorem needed by the distributed/state-GC interaction
simulation. -/
theorem StateRelAt.compact_apply {Γ : OrderedPrefixCode} {K K' : Know}
    {keep : ℕ → Bool} {full : (Core Γ).State} {compact : CompactState}
    (h : StateRelAt Γ K keep full compact)
    (hp : FrontierProjection keep) {e : Op (Core Γ).AppOp}
    {newGaps : Finset GapEntry}
    (cert : CompactApplyCertificate Γ K keep full compact hp e K' newGaps) :
    StateRelAt Γ K' keep
      ((Core Γ).toCRDTSig.update full e)
      (compactApply compact e newGaps) := by
  cases cert with
  | text rep x anchor hclock hsort hxfresh newGaps hgap hndPost =>
      simpa [Core, Stores, S_core_update] using
        h.text_insert hp rep x anchor hclock hsort hxfresh newGaps hgap hndPost
  | delete t rep x hxknown hxnotdeleted hnd newGaps =>
      simpa [Core, Stores] using
        h.delete_add t rep x hxknown hxnotdeleted hnd
  | mark t rep m hnd hanchors newGaps =>
      simpa [Core, Stores] using h.mark_add t rep m hnd hanchors

/-- Physical materializations are local: commit fetch can add them at one
replica without changing another replica's holding. -/
abbrev MaterializedWorld := Replica → Version → Option Materialized

/-- Combined execution state. `semantic` is the ghost, uncollected reference;
`materialized` is the representation on which runtime operations execute. -/
structure CombinedConfig (Γ : OrderedPrefixCode) where
  semantic : DistributedConfig (Core Γ)
  materialized : MaterializedWorld

/-- Every physically held commit has a related local materialization. This is
the invariant that was absent from `DistributedConfig`: its physical store
tracked commit identifiers but no representation-changing datatype state. -/
def CombinedConfig.WellFormed {Γ : OrderedPrefixCode}
    (S : CombinedConfig Γ) : Prop :=
  S.semantic.WellFormed ∧
  ∀ r v, v ∈ (S.semantic.stores r).commits →
    ∃ full E m,
      S.semantic.core.ver v = some (full, E) ∧
      S.materialized r v = some m ∧
      StateRelAt Γ m.knowledge m.keep full m.state

/-- A held physical version answers the same rich-text query as the ghost
uncollected version. -/
theorem CombinedConfig.query_eq {Γ : OrderedPrefixCode}
    {S : CombinedConfig Γ} (hWF : S.WellFormed)
    {r : Replica} {v : Version}
    (hheld : v ∈ (S.semantic.stores r).commits)
    (mt : MType) :
    ∃ full E m,
      S.semantic.core.ver v = some (full, E) ∧
      S.materialized r v = some m ∧
      renderCompact m.state mt =
        renderCore m.state.sided.gaps full mt := by
  obtain ⟨full, E, m, hv, hm, hrel⟩ := hWF.2 r v hheld
  exact ⟨full, E, m, hv, hm, hrel.rel.query_eq mt⟩

def updateMaterialized (M : MaterializedWorld) (r : Replica) (v : Version)
    (m : Materialized) : MaterializedWorld :=
  Function.update M r (Function.update (M r) v (some m))

/-- Fetch transfers the sender's immutable materialization together with each
new commit.  An already-held destination materialization is retained: it may
be at a different, but still related, local state-GC epoch. -/
noncomputable def fetchMaterialized {Γ : OrderedPrefixCode} (S : CombinedConfig Γ)
    (src dst : Replica) :
    MaterializedWorld :=
  Function.update S.materialized dst (fun v =>
    if v ∈ (S.semantic.stores dst).commits
    then S.materialized dst v
    else S.materialized src v)

noncomputable def fetchResult {Γ : OrderedPrefixCode} (S : CombinedConfig Γ)
    (src dst : Replica) : CombinedConfig Γ where
  semantic := ⟨S.semantic.core, Function.update S.semantic.stores dst
    (receive (S.semantic.stores dst) (advertise (S.semantic.stores src)))⟩
  materialized := fetchMaterialized S src dst

/-- Asynchronous fetch preserves the heterogeneous simulation.  The only
semantic premise is the same post-state well-formedness required by the
generic distributed fetch rule. -/
theorem fetchResult_wellFormed {Γ : OrderedPrefixCode}
    {S : CombinedConfig Γ} (hWF : S.WellFormed) (src dst : Replica)
    (hsem : (fetchResult S src dst).semantic.WellFormed) :
    (fetchResult S src dst).WellFormed := by
  refine ⟨hsem, ?_⟩
  intro r v hheld
  by_cases hr : r = dst
  · subst r
    simp [fetchResult] at hheld
    rcases hheld with hdst | hsrc
    · obtain ⟨full, E, m, hv, hm, hrel⟩ := hWF.2 dst v hdst
      refine ⟨full, E, m, hv, ?_, hrel⟩
      simp [fetchResult, fetchMaterialized, hdst, hm]
    · obtain ⟨full, E, m, hv, hm, hrel⟩ := hWF.2 src v hsrc
      by_cases hdst : v ∈ (S.semantic.stores dst).commits
      · obtain ⟨full', E', m', hv', hm', hrel'⟩ := hWF.2 dst v hdst
        refine ⟨full', E', m', hv', ?_, hrel'⟩
        simp [fetchResult, fetchMaterialized, hdst, hm']
      · refine ⟨full, E, m, hv, ?_, hrel⟩
        simp [fetchResult, fetchMaterialized, hdst, hm]
  · simp [fetchResult, hr] at hheld
    obtain ⟨full, E, m, hv, hm, hrel⟩ := hWF.2 r v hheld
    refine ⟨full, E, m, hv, ?_, hrel⟩
    simp [fetchResult, fetchMaterialized, hr, hm]

/-- Fetching from a semantic MCA-repair source also transfers a related
compact Peritext materialization for every member of the recursive MCA
closure.  Thus repair supplies runtime fold inputs, not only commit ids. -/
theorem fetchResult_materializes_mcaClosure {Γ : OrderedPrefixCode}
    {S : CombinedConfig Γ} (hWF : S.WellFormed) {src dst : Replica}
    (hsrc : MCARepairSource S.semantic src)
    (hsem : (fetchResult S src dst).semantic.WellFormed) :
    ∀ m, InMcasClosure S.semantic.core m →
      ∃ full E mat,
        (fetchResult S src dst).semantic.core.ver m = some (full, E) ∧
        (fetchResult S src dst).materialized dst m = some mat ∧
        StateRelAt Γ mat.knowledge mat.keep full mat.state := by
  intro m hm
  have hheld : m ∈ ((fetchResult S src dst).semantic.stores dst).commits := by
    simpa [fetchResult] using
      (fetch_from_mcaSource_keeps_closure S.semantic hsrc m hm)
  exact (fetchResult_wellFormed hWF src dst hsem).2 dst m hheld

/-- One repair fetch makes a virtual merge physically ready at the acting
replica and supplies related compact inputs for its entire recursive fold. -/
theorem fetchResult_virtualMerge_ready {Γ : OrderedPrefixCode}
    {S : CombinedConfig Γ} (hWF : S.WellFormed)
    {src actor other : Replica}
    (hsrc : MCARepairSource S.semantic src)
    (hsem : (fetchResult S src actor).semantic.WellFormed) :
    StepAvailableV (fetchResult S src actor).semantic (.merge actor other) ∧
      ∀ m, InMcasClosure S.semantic.core m →
        ∃ full E mat,
          (fetchResult S src actor).semantic.core.ver m = some (full, E) ∧
          (fetchResult S src actor).materialized actor m = some mat ∧
          StateRelAt Γ mat.knowledge mat.keep full mat.state := by
  constructor
  · simpa [fetchResult] using
      (stepAvailableV_merge_after_repair S.semantic hWF.1 hsrc
        (actor := actor) (other := other))
  · exact fetchResult_materializes_mcaClosure hWF hsrc hsem

/-- Commit-history GC changes holdings only. State materializations need not be
rewritten; unreachable entries are ignored by `WellFormed`. -/
def commitGCResult {Γ : OrderedPrefixCode} (S : CombinedConfig Γ)
    (r : Replica)
    (cert : LocalGCCertificate S.semantic.core.parents
      (S.semantic.stores r)) : CombinedConfig Γ where
  semantic := ⟨S.semantic.core, Function.update S.semantic.stores r
    (collect S.semantic.core.parents (S.semantic.stores r) cert)⟩
  materialized := S.materialized

theorem commitGCResult_wellFormed {Γ : OrderedPrefixCode}
    {S : CombinedConfig Γ} (hWF : S.WellFormed) (r : Replica)
    (cert : LocalGCCertificate S.semantic.core.parents
      (S.semantic.stores r))
    (hsem : (commitGCResult S r cert).semantic.WellFormed) :
    (commitGCResult S r cert).WellFormed := by
  refine ⟨hsem, ?_⟩
  intro r' v hheld
  by_cases hr : r' = r
  · subst r'
    have hold : v ∈ (S.semantic.stores r).commits := by
      apply cert.support
      simpa [commitGCResult] using hheld
    simpa [commitGCResult] using hWF.2 r v hold
  · have hold : v ∈ (S.semantic.stores r').commits := by
      simpa [commitGCResult, hr] using hheld
    simpa [commitGCResult, hr] using hWF.2 r' v hold

/-- Complete evidence for one local state-GC transition at a physically held
version. The semantic distributed configuration stutters. -/
structure StateGCAction {Γ : OrderedPrefixCode}
    (S : CombinedConfig Γ) (r : Replica) (v : Version)
    (p : Plan) (newGaps : Finset GapEntry) where
  full : (Core Γ).State
  events : Set (Op (Core Γ).AppOp)
  before : Materialized
  held : v ∈ (S.semantic.stores r).commits
  versionAt : S.semantic.core.ver v = some (full, events)
  materializedAt : S.materialized r v = some before
  related : StateRelAt Γ before.knowledge before.keep full before.state
  newFrontier : ℕ
  frontierMono : before.projection.frontier ≤ newFrontier
  planDropsBelow : ∀ x, p.keepText x = false → x ≤ newFrontier
  certificate : InteractionGCCertificate (Γ := Γ)
    (K := before.knowledge) (C := S.semantic.core) (v := v)
    full before.state p newGaps

noncomputable def StateGCAction.after {Γ : OrderedPrefixCode}
    {S : CombinedConfig Γ} {r : Replica} {v : Version}
    {p : Plan} {newGaps : Finset GapEntry}
    (a : StateGCAction S r v p newGaps) : Materialized where
  state := collectStableBase a.before.state p newGaps
  knowledge := a.before.knowledge
  keep := fun x => a.before.keep x && p.keepText x
  projection := a.before.projection.andPlan a.newFrontier
    a.frontierMono a.planDropsBelow

noncomputable def stateGCResult {Γ : OrderedPrefixCode}
    {S : CombinedConfig Γ} {r : Replica} {v : Version}
    {p : Plan} {newGaps : Finset GapEntry}
    (a : StateGCAction S r v p newGaps) : CombinedConfig Γ where
  semantic := S.semantic
  materialized := updateMaterialized S.materialized r v a.after

/-- A certified local state-GC step preserves all held-version
materializations while stuttering in the no-GC semantic world. -/
theorem StateGCAction.wellFormed {Γ : OrderedPrefixCode}
    {S : CombinedConfig Γ} (hWF : S.WellFormed)
    {r : Replica} {v : Version} {p : Plan}
    {newGaps : Finset GapEntry}
    (a : StateGCAction S r v p newGaps) : (stateGCResult a).WellFormed := by
  constructor
  · exact hWF.1
  · intro r' v' hheld
    by_cases hr : r' = r
    · subst r'
      by_cases hv : v' = v
      · subst v'
        refine ⟨a.full, a.events, a.after, a.versionAt, ?_, ?_⟩
        · simp [stateGCResult, updateMaterialized]
        · exact a.related.collect a.certificate
      · obtain ⟨full, E, m, hversion, hmat, hrel⟩ := hWF.2 r v' hheld
        refine ⟨full, E, m, hversion, ?_, hrel⟩
        simp [stateGCResult, updateMaterialized, hv, hmat]
    · obtain ⟨full, E, m, hversion, hmat, hrel⟩ := hWF.2 r' v' hheld
      refine ⟨full, E, m, hversion, ?_, hrel⟩
      simp [stateGCResult, updateMaterialized, hr, hmat]

@[simp] theorem StateGCAction.semantic_stutters {Γ : OrderedPrefixCode}
    {S : CombinedConfig Γ} {r : Replica} {v : Version} {p : Plan}
    {newGaps : Finset GapEntry}
    (a : StateGCAction S r v p newGaps) :
    (stateGCResult a).semantic = S.semantic := rfl

/-! ## Combined operational semantics and trace erasure -/

/-- Physical effect of one visible semantic step. Existing commits keep their
materializations and immutable semantic versions. Only commits newly installed
by the visible store evolution require fresh relation evidence. -/
structure MaterializationDelta {Γ : OrderedPrefixCode}
    (before after : DistributedConfig (Core Γ))
    (M M' : MaterializedWorld) : Prop where
  preserveMaterialized : ∀ r v, v ∈ (before.stores r).commits →
    M' r v = M r v
  preserveVersion : ∀ r v, v ∈ (before.stores r).commits →
    after.core.ver v = before.core.ver v
  introduced : ∀ r v, v ∈ (after.stores r).commits →
    v ∉ (before.stores r).commits →
    ∃ full E m, after.core.ver v = some (full, E) ∧
      M' r v = some m ∧
      StateRelAt Γ m.knowledge m.keep full m.state

/-- Store facts for the one-version installation performed by a visible apply
or merge.  `onlyNew` is discharged from `VisibleStoreEvolution`; it prevents a
physical step from smuggling in unrelated materializations. -/
structure SingleInstallFrame {Γ : OrderedPrefixCode}
    (before after : DistributedConfig (Core Γ))
    (actor : Replica) (fresh : Version)
    (full : (Core Γ).State) (events : Set (Op (Core Γ).AppOp)) : Prop where
  freshAtActor : fresh ∉ (before.stores actor).commits
  onlyNew : ∀ r v, v ∈ (after.stores r).commits →
    v ∉ (before.stores r).commits → r = actor ∧ v = fresh
  preserveVersion : ∀ r v, v ∈ (before.stores r).commits →
    after.core.ver v = before.core.ver v
  versionAt : after.core.ver fresh = some (full, events)

theorem MaterializationDelta.singleInstall {Γ : OrderedPrefixCode}
    {before after : DistributedConfig (Core Γ)} {M : MaterializedWorld}
    {actor : Replica} {fresh : Version} {full : (Core Γ).State}
    {events : Set (Op (Core Γ).AppOp)} {m : Materialized}
    (frame : SingleInstallFrame before after actor fresh full events)
    (related : StateRelAt Γ m.knowledge m.keep full m.state) :
    MaterializationDelta before after M
      (updateMaterialized M actor fresh m) := by
  refine ⟨?_, frame.preserveVersion, ?_⟩
  · intro r v hold
    by_cases hr : r = actor
    · subst r
      have hv : v ≠ fresh := by
        intro h
        subst v
        exact frame.freshAtActor hold
      simp [updateMaterialized, hv]
    · simp [updateMaterialized, hr]
  · intro r v hnew hold
    obtain ⟨rfl, rfl⟩ := frame.onlyNew r v hnew hold
    exact ⟨full, events, m, frame.versionAt, by simp [updateMaterialized], related⟩

/-- Concrete apply installation.  The post-state relation is computed by the
compact interpreter theorem, not accepted as a field of the store delta. -/
theorem MaterializationDelta.compactApplyInstall {Γ : OrderedPrefixCode}
    {before after : DistributedConfig (Core Γ)} {M : MaterializedWorld}
    {actor : Replica} {fresh : Version} {K K' : Know}
    {keep : ℕ → Bool} {full : (Core Γ).State} {compact : CompactState}
    {events : Set (Op (Core Γ).AppOp)} {e : Op (Core Γ).AppOp}
    {newGaps : Finset GapEntry}
    (source : StateRelAt Γ K keep full compact)
    (projection : FrontierProjection keep)
    (cert : CompactApplyCertificate Γ K keep full compact projection
      e K' newGaps)
    (frame : SingleInstallFrame before after actor fresh
      ((Core Γ).toCRDTSig.update full e) events) :
    MaterializationDelta before after M
      (updateMaterialized M actor fresh
        ⟨compactApply compact e newGaps, K', keep, projection⟩) := by
  apply MaterializationDelta.singleInstall frame
  exact source.compact_apply projection cert

/-- Install a merge result computed from branch-head materializations.  The
proof may refer to the semantic result (whose LCA can be virtual), but the
installed runtime state contains no LCA materialization. -/
theorem MaterializationDelta.headOnlyMergeInstall {Γ : OrderedPrefixCode}
    {before after : DistributedConfig (Core Γ)} {M : MaterializedWorld}
    {actor : Replica} {fresh : Version} {Km : Know}
    {keep : ℕ → Bool} {full : (Core Γ).State}
    {events : Set (Op (Core Γ).AppOp)} {out : CompactState}
    (projection : FrontierProjection keep)
    (cert : HeadOnlyMergeCertificate Km keep full out)
    (frame : SingleInstallFrame before after actor fresh full events) :
    MaterializationDelta before after M
      (updateMaterialized M actor fresh ⟨out, Km, keep, projection⟩) := by
  apply MaterializationDelta.singleInstall frame
  exact cert.related

theorem MaterializationDelta.introduced_isSome {Γ : OrderedPrefixCode}
    {before after : DistributedConfig (Core Γ)} {M M' : MaterializedWorld}
    (d : MaterializationDelta before after M M')
    {r : Replica} {v : Version} (hnew : v ∈ (after.stores r).commits)
    (hold : v ∉ (before.stores r).commits) : (M' r v).isSome := by
  obtain ⟨full, E, m, hv, hm, hrel⟩ := d.introduced r v hnew hold
  simp [hm]

/-- Combined physical semantics. Fetch, commit-history GC, and state GC are
silent. A visible step carries a genuine `DistributedConfigStep` plus only its
physical materialization delta. -/
inductive CombinedStep (Γ : OrderedPrefixCode) :
    CombinedConfig Γ → Option (Label3 (Core Γ)) → CombinedConfig Γ → Prop where
  | fetch (S : CombinedConfig Γ) (src dst : Replica)
      (hWF : S.WellFormed)
      (hsem : (fetchResult S src dst).semantic.WellFormed) :
      CombinedStep Γ S none (fetchResult S src dst)
  | commitGC (S : CombinedConfig Γ) (r : Replica)
      (cert : LocalGCCertificate S.semantic.core.parents
        (S.semantic.stores r))
      (hWF : S.WellFormed)
      (hsem : (commitGCResult S r cert).semantic.WellFormed) :
      CombinedStep Γ S none (commitGCResult S r cert)
  | stateGC {S : CombinedConfig Γ} {r : Replica} {v : Version}
      {p : Plan} {newGaps : Finset GapEntry}
      (hWF : S.WellFormed) (a : StateGCAction S r v p newGaps) :
      CombinedStep Γ S none (stateGCResult a)
  | visible {S : CombinedConfig Γ} {semantic' : DistributedConfig (Core Γ)}
      {M' : MaterializedWorld} {ℓ : Label3 (Core Γ)}
      (hWF : S.WellFormed)
      (hstep : DistributedConfigStep (Core Γ) S.semantic (some ℓ) semantic')
      (delta : MaterializationDelta S.semantic semantic'
        S.materialized M') :
      CombinedStep Γ S (some ℓ) ⟨semantic', M'⟩

private theorem distributedStep_target_wf {D : ConditionedMRDTSig}
    {S T : DistributedConfig D} {ℓ : Option (Label3 D)}
    (h : DistributedConfigStep D S ℓ T) : T.WellFormed := by
  cases h <;> assumption

private theorem distributedStep_source_wf {D : ConditionedMRDTSig}
    {S T : DistributedConfig D} {ℓ : Option (Label3 D)}
    (h : DistributedConfigStep D S ℓ T) : S.WellFormed := by
  cases h <;> assumption

theorem CombinedStep.wellFormed {Γ : OrderedPrefixCode}
    {S T : CombinedConfig Γ} {ℓ : Option (Label3 (Core Γ))}
    (h : CombinedStep Γ S ℓ T) : T.WellFormed := by
  cases h with
  | fetch src dst hWF hsem =>
      exact fetchResult_wellFormed hWF src dst hsem
  | commitGC r cert hWF hsem =>
      exact commitGCResult_wellFormed hWF r cert hsem
  | stateGC hWF a => exact a.wellFormed hWF
  | visible hWF hstep delta =>
      refine ⟨distributedStep_target_wf hstep, ?_⟩
      intro r v hheld
      by_cases hold : v ∈ (S.semantic.stores r).commits
      · obtain ⟨full, E, m, hv, hm, hrel⟩ :=
          hWF.2 r v hold
        refine ⟨full, E, m, ?_, ?_, hrel⟩
        · rw [delta.preserveVersion r v hold]
          exact hv
        · exact (delta.preserveMaterialized r v hold).trans hm
      · exact delta.introduced r v hheld hold

/-- A silent combined transition leaves the semantic core unchanged; a
visible transition contains the exact `Step3` derivation named by its label. -/
theorem CombinedStep.core_step {Γ : OrderedPrefixCode}
    {S T : CombinedConfig Γ} {ℓ : Option (Label3 (Core Γ))}
    (h : CombinedStep Γ S ℓ T) :
    match ℓ with
    | none => T.semantic.core = S.semantic.core
    | some label => Step3 (Core Γ) S.semantic.core label T.semantic.core := by
  cases h with
  | fetch => rfl
  | commitGC => rfl
  | stateGC => rfl
  | visible hWF hstep delta =>
      cases hstep with
      | visible _ _ hCore _ _ => exact hCore

inductive CombinedSteps (Γ : OrderedPrefixCode) :
    CombinedConfig Γ → List (Option (Label3 (Core Γ))) →
      CombinedConfig Γ → Prop where
  | nil (S : CombinedConfig Γ) : CombinedSteps Γ S [] S
  | cons {S T U : CombinedConfig Γ} {ℓ : Option (Label3 (Core Γ))}
      {ℓs : List (Option (Label3 (Core Γ)))} :
      CombinedStep Γ S ℓ T → CombinedSteps Γ T ℓs U →
      CombinedSteps Γ S (ℓ :: ℓs) U

def eraseCombinedLabels {Γ : OrderedPrefixCode} :
    List (Option (Label3 (Core Γ))) → List (Label3 (Core Γ)) :=
  List.filterMap id

theorem CombinedSteps.wellFormed {Γ : OrderedPrefixCode}
    {S T : CombinedConfig Γ} {labels : List (Option (Label3 (Core Γ)))}
    (run : CombinedSteps Γ S labels T) (hWF : S.WellFormed) : T.WellFormed := by
  induction run with
  | nil => exact hWF
  | cons step tail ih => exact ih step.wellFormed

/-- End-to-end erasure: every finite execution with arbitrary interleavings of
fetch, commit GC, local state GC, and visible operations refines the original
uncollected `Step3` semantics. -/
theorem combinedSteps_refines_Step3 {Γ : OrderedPrefixCode}
    {S T : CombinedConfig Γ} {labels : List (Option (Label3 (Core Γ)))}
    (run : CombinedSteps Γ S labels T) :
    Steps (Core Γ) S.semantic.core (eraseCombinedLabels labels)
      T.semantic.core := by
  induction run with
  | nil => exact Steps.nil _
  | @cons S T U label labels step tail ih =>
      cases label with
      | none =>
          change Steps (Core Γ) S.semantic.core
            (eraseCombinedLabels labels) U.semantic.core
          have hc := step.core_step
          rw [hc] at ih
          exact ih
      | some label =>
          change Steps (Core Γ) S.semantic.core
            (label :: eraseCombinedLabels labels) U.semantic.core
          exact Steps.cons step.core_step ih

/-- Every query at the end of a well-formed combined trace agrees with the
uncollected semantic version that the erased `Step3` trace reaches. -/
theorem combinedTrace_query_eq {Γ : OrderedPrefixCode}
    {S T : CombinedConfig Γ} {labels : List (Option (Label3 (Core Γ)))}
    (run : CombinedSteps Γ S labels T) (hWF : S.WellFormed)
    {r : Replica} {v : Version} (hheld : v ∈ (T.semantic.stores r).commits)
    (mt : MType) :
    ∃ full E m, T.semantic.core.ver v = some (full, E) ∧
      T.materialized r v = some m ∧
      renderCompact m.state mt = renderCore m.state.sided.gaps full mt :=
  CombinedConfig.query_eq (run.wellFormed hWF) hheld mt

/-! ## Widened interaction semantics with virtual LCAs -/

/-- The same physical interaction system over `DistributedConfigStepV`.
Virtual merges are admitted only with `StepAvailableV` and a genuine
`MaterializationDelta`; neither MCA availability nor the compact post-state is
manufactured by this wrapper. -/
inductive CombinedStepV (Γ : OrderedPrefixCode) :
    CombinedConfig Γ → Option (Label3 (Core Γ)) → CombinedConfig Γ → Prop where
  | fetch (S : CombinedConfig Γ) (src dst : Replica)
      (hWF : S.WellFormed)
      (hsem : (fetchResult S src dst).semantic.WellFormed) :
      CombinedStepV Γ S none (fetchResult S src dst)
  | commitGC (S : CombinedConfig Γ) (r : Replica)
      (cert : LocalGCCertificate S.semantic.core.parents
        (S.semantic.stores r))
      (hWF : S.WellFormed)
      (hsem : (commitGCResult S r cert).semantic.WellFormed) :
      CombinedStepV Γ S none (commitGCResult S r cert)
  | stateGC {S : CombinedConfig Γ} {r : Replica} {v : Version}
      {p : Plan} {newGaps : Finset GapEntry}
      (hWF : S.WellFormed) (a : StateGCAction S r v p newGaps) :
      CombinedStepV Γ S none (stateGCResult a)
  | visible {S : CombinedConfig Γ} {semantic' : DistributedConfig (Core Γ)}
      {M' : MaterializedWorld} {ℓ : Label3 (Core Γ)}
      (hWF : S.WellFormed)
      (hstep : DistributedConfigStepV (Core Γ) S.semantic (some ℓ) semantic')
      (delta : MaterializationDelta S.semantic semantic'
        S.materialized M') :
      CombinedStepV Γ S (some ℓ) ⟨semantic', M'⟩

theorem CombinedStepV.wellFormed {Γ : OrderedPrefixCode}
    {S T : CombinedConfig Γ} {ℓ : Option (Label3 (Core Γ))}
    (h : CombinedStepV Γ S ℓ T) : T.WellFormed := by
  cases h with
  | fetch src dst hWF hsem =>
      exact fetchResult_wellFormed hWF src dst hsem
  | commitGC r cert hWF hsem =>
      exact commitGCResult_wellFormed hWF r cert hsem
  | stateGC hWF a => exact a.wellFormed hWF
  | visible hWF hstep delta =>
      refine ⟨?_, ?_⟩
      · cases hstep with
        | visible _ _ _ _ hTarget => exact hTarget
      · intro r v hheld
        by_cases hold : v ∈ (S.semantic.stores r).commits
        · obtain ⟨full, E, m, hv, hm, hrel⟩ := hWF.2 r v hold
          refine ⟨full, E, m, ?_, ?_, hrel⟩
          · rw [delta.preserveVersion r v hold]
            exact hv
          · exact (delta.preserveMaterialized r v hold).trans hm
        · exact delta.introduced r v hheld hold

theorem CombinedStepV.core_step {Γ : OrderedPrefixCode}
    {S T : CombinedConfig Γ} {ℓ : Option (Label3 (Core Γ))}
    (h : CombinedStepV Γ S ℓ T) :
    match ℓ with
    | none => T.semantic.core = S.semantic.core
    | some label => Step3V (Core Γ) S.semantic.core label T.semantic.core := by
  cases h with
  | fetch => rfl
  | commitGC => rfl
  | stateGC => rfl
  | visible hWF hstep delta =>
      cases hstep with
      | visible _ _ hCore _ _ => exact hCore

inductive CombinedStepsV (Γ : OrderedPrefixCode) :
    CombinedConfig Γ → List (Option (Label3 (Core Γ))) →
      CombinedConfig Γ → Prop where
  | nil (S : CombinedConfig Γ) : CombinedStepsV Γ S [] S
  | cons {S T U : CombinedConfig Γ} {ℓ : Option (Label3 (Core Γ))}
      {ℓs : List (Option (Label3 (Core Γ)))} :
      CombinedStepV Γ S ℓ T → CombinedStepsV Γ T ℓs U →
      CombinedStepsV Γ S (ℓ :: ℓs) U

theorem CombinedStepsV.wellFormed {Γ : OrderedPrefixCode}
    {S T : CombinedConfig Γ} {labels : List (Option (Label3 (Core Γ)))}
    (run : CombinedStepsV Γ S labels T) (hWF : S.WellFormed) : T.WellFormed := by
  induction run with
  | nil => exact hWF
  | cons step tail ih => exact ih step.wellFormed

/-- Finite traces with fetch, both collectors, ordinary steps, and virtual
merges erase to the widened uncollected semantics. -/
theorem combinedStepsV_refines_Step3V {Γ : OrderedPrefixCode}
    {S T : CombinedConfig Γ} {labels : List (Option (Label3 (Core Γ)))}
    (run : CombinedStepsV Γ S labels T) :
    StepsV (Core Γ) S.semantic.core (eraseCombinedLabels labels)
      T.semantic.core := by
  induction run with
  | nil => exact StepsV.nil _
  | @cons S T U label labels step tail ih =>
      cases label with
      | none =>
          change StepsV (Core Γ) S.semantic.core
            (eraseCombinedLabels labels) U.semantic.core
          have hc := step.core_step
          rw [hc] at ih
          exact ih
      | some label =>
          change StepsV (Core Γ) S.semantic.core
            (label :: eraseCombinedLabels labels) U.semantic.core
          exact StepsV.cons step.core_step ih

theorem combinedTraceV_query_eq {Γ : OrderedPrefixCode}
    {S T : CombinedConfig Γ} {labels : List (Option (Label3 (Core Γ)))}
    (run : CombinedStepsV Γ S labels T) (hWF : S.WellFormed)
    {r : Replica} {v : Version} (hheld : v ∈ (T.semantic.stores r).commits)
    (mt : MType) :
    ∃ full E m, T.semantic.core.ver v = some (full, E) ∧
      T.materialized r v = some m ∧
      renderCompact m.state mt = renderCore m.state.sided.gaps full mt :=
  CombinedConfig.query_eq (run.wellFormed hWF) hheld mt

#print axioms StateRel.snapshot
#print axioms StateRel.query_eq
#print axioms StateRel.gapObservation_exact
#print axioms StateRel.compactInsertOp_exact
#print axioms StateRel.textProjection_apply
#print axioms sMergeL_filter
#print axioms CommonProjectionFrame.merge_text_exact
#print axioms translateText_exact
#print axioms commonProjectionFrame_of_epochs
#print axioms merge_text_after_epoch_translation
#print axioms StateRelAt.merge
#print axioms PhysicalMergeEvidence.toCoverage
#print axioms PhysicalMergeEvidence.of_sources
#print axioms osMergeL_eq_union
#print axioms osPayloads_union
#print axioms StateRel.collect_structural
#print axioms StateRel.collect
#print axioms StateRelAt.collect
#print axioms FrontierProjection.keep_future
#print axioms FrontierProjection.andPlan
#print axioms fresh_timestamp_need_not_exceed_frontier
#print axioms mintAfterFrontier_of_causalClock
#print axioms StateRelAt.text_apply_after_frontier
#print axioms ApplyEpochFrame.mintAfter
#print axioms compactApply_text
#print axioms compactApply_delete_add
#print axioms compactApply_mark_add
#print axioms render_projection
#print axioms StateRelAt.render_with_marks
#print axioms StateRelAt.mark_add
#print axioms StateRelAt.delete_add
#print axioms mem_sUpdate_insert_of_fresh
#print axioms StateRelAt.text_insert
#print axioms StateRelAt.compact_apply
#print axioms combinedStepsV_refines_Step3V
#print axioms combinedTraceV_query_eq
#print axioms CombinedConfig.query_eq
#print axioms fetchResult_wellFormed
#print axioms commitGCResult_wellFormed
#print axioms StateGCAction.wellFormed
#print axioms StateGCAction.semantic_stutters
#print axioms MaterializationDelta.introduced_isSome
#print axioms MaterializationDelta.singleInstall
#print axioms MaterializationDelta.compactApplyInstall
#print axioms CombinedStep.wellFormed
#print axioms CombinedStep.core_step
#print axioms CombinedSteps.wellFormed
#print axioms combinedSteps_refines_Step3
#print axioms combinedTrace_query_eq

end Sal.ConditionedMRDTs.PeritextSided.Interaction
