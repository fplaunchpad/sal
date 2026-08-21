import Sal.ConditionedMRDTs.MRDT_Instances.Peritext_Sided.PeritextSided_Flagship
import Sal.ConditionedMRDTs.MRDT_Instances.SidedRGA.SidedRGA_FuguePolicyGC
import Sal.ConditionedMRDTs.MRDT_Instances.Peritext_Embed.PeritextEmbed_MarksGC_A3
import Sal.ConditionedMRDTs.Metatheory.EvidenceDischarge

/-!
# Sided Peritext local state GC

The first result is a checked design gate: the three visible product fields
cannot be collected independently. A stable dead sided node remains
observable through Fugue's next-mint policy. Consequently compact
SidedEmbedRGA owns a derived subcomponent: one `LiveGap` observation for the
start gap and each retained anchor. This is policy evidence, not another copy
of the document tree or a fourth logical Peritext component.
-/

namespace Sal.ConditionedMRDTs.PeritextSided.StateGC

open Sal.Emulation
open Sal.ConditionedMRDTs
open Sal.ConditionedMRDTs.FuguePolicyGC
open Sal.EmbedRGA (OrderedPrefixCode)

/-- Refutation of naive componentwise collection.  Even after a deletion is
stable, erasing its text-shadow node while leaving only the live projection
changes a legal future continuation's visible order. -/
theorem naive_three_component_gc_is_not_continuation_safe :
    gView FuguePolicyGC.Γ FuguePolicyGC.fullMerged ≠
      gView FuguePolicyGC.Γ FuguePolicyGC.collectedMerged :=
  FuguePolicyGC.stable_dead_leaf_collection_changes_future_read

/-- The compact policy entry stored for one logical insertion gap. -/
structure GapEntry where
  anchor : ℕ
  observation : (Sal.EmbedRGA.Side × ℕ) × Sal.EmbedRGA.SChain
  deriving DecidableEq

/-- Persistent compact SidedEmbedRGA state. Fugue policy metadata belongs to
the text datatype because it is required to mint and merge future text
operations; it is not a fourth logical Peritext datatype. -/
structure CompactSidedState where
  text : SState
  gaps : Finset GapEntry

/-- Peritext retains three logical components. The compact text component
internally owns both its retained shadow and its Fugue gap summary. -/
structure CompactState where
  sided : CompactSidedState
  deleted : Finset ℕ
  marks : Finset PeritextEmbed.MarkDoc.MarkD

def CompactState.text (s : CompactState) : SState := s.sided.text

def CompactState.gaps (s : CompactState) : Finset GapEntry := s.sided.gaps

def CompactState.withText (s : CompactState) (text : SState) : CompactState :=
  { s with sided := { s.sided with text := text } }

/-- Atomic collection plan.  A real frontier discharge will construct this
plan; keeping it separate prevents stability evidence from being confused
with the pure collector. -/
structure Plan where
  keepText : ℕ → Bool
  keepDelete : ℕ → Bool
  keepMark : ℕ → Bool

/-- Cross-component retention obligations.  Live characters and mark
boundaries remain materialized. Every materialized insertion gap retains the
exact Fugue observation consumed by the next mint. Delete and mark evidence
may be removed only under the later frontier/delayed-operation premises. -/
def Plan.WellFormed {Γ : OrderedPrefixCode} (p : Plan) (s : (Core Γ).State)
    (K : Know) : Prop :=
  (∀ r ∈ (show SState from s.1),
    (∀ d : OSElem ℕ, d ∈ (show OSState ℕ from s.2.1) → d.2.2 ≠ r.1) →
      p.keepText r.1 = true) ∧
  (∀ m : OSElem PeritextEmbed.MarkDoc.MarkD,
    m ∈ (show OSState PeritextEmbed.MarkDoc.MarkD from s.2.2) →
    p.keepMark m.2.2.mid = true →
      p.keepText m.2.2.start_id = true ∧ p.keepText m.2.2.end_id = true) ∧
  ∀ a, a = 0 ∨ p.keepText a = true →
    ∃ g, retainedLiveGap K a = some g ∧
      gapObservation g a = (liveGapChoose g a, liveGapParentChain g)

/-- Extract the compact observation forced by a retained gap. -/
def gapEntryOf (K : Know) (a : ℕ) : Option GapEntry :=
  (retainedLiveGap K a).map fun g =>
    ⟨a, gapObservation g a⟩

theorem gapEntryOf_exact (K : Know) (a : ℕ) :
    (gapEntryOf K a).map GapEntry.observation =
      (retainedLiveGap K a).map (fun g =>
        (fugueChoose FuguePolicyGC.Γ K a,
          gChainOf K (fugueChoose FuguePolicyGC.Γ K a).2)) := by
  unfold gapEntryOf
  rw [Option.map_map]
  cases h : retainedLiveGap K a with
  | none => simp [h]
  | some g =>
      have hg : g = liveGapOf K a := by
        unfold retainedLiveGap at h
        split at h
        · exact Option.some.inj h.symm
        · contradiction
      subst g
      simp only [h, Option.map_some, Function.comp_apply]
      simp only [Option.some.injEq]
      change gapObservation (liveGapOf K a) a =
        (fugueChoose FuguePolicyGC.Γ K a,
          gChainOf K (fugueChoose FuguePolicyGC.Γ K a).2)
      unfold gapObservation
      exact Prod.ext (liveGapChoose_exact K a)
        (liveGapParentChain_exact K a)

/-! ## Compact minting -/

noncomputable def gapLookup (gaps : Finset GapEntry) (a : ℕ) :
    Option ((Sal.EmbedRGA.Side × ℕ) × Sal.EmbedRGA.SChain) :=
  ((gaps.toList.find? fun e => e.anchor = a).map GapEntry.observation)

/-- Functional-map invariant for the finite persisted encoding. It also rules
out duplicate/conflicting observations for an anchor. -/
def GapMapOK (K : Know) (gaps : Finset GapEntry) : Prop :=
  ∀ a, gapLookup gaps a = (gapEntryOf K a).map GapEntry.observation

noncomputable def compactGapObservation (s : CompactSidedState) (a : ℕ) :
    (Sal.EmbedRGA.Side × ℕ) × Sal.EmbedRGA.SChain :=
  (gapLookup s.gaps a).getD ((Sal.EmbedRGA.Side.R, a), [])

/-- Mint directly from compact policy metadata. The raw parent need not remain
in `text`; its chain is supplied by the retained gap observation. -/
noncomputable def compactInsertOp (Γ : OrderedPrefixCode) (s : CompactSidedState)
    (rep x a : ℕ) : Op SOp :=
  let choice := (compactGapObservation s a).1
  let parentChain := (compactGapObservation s a).2
  (x, rep, SOp.ins x (Sal.EmbedRGA.sidedCoordOf Γ parentChain)
    choice.2 choice.1)

theorem compactGapObservation_exact {K : Know} {gaps : Finset GapEntry}
    (hmap : GapMapOK K gaps) {a : ℕ}
    (hret : ∃ g, retainedLiveGap K a = some g) :
    compactGapObservation ⟨gFold FuguePolicyGC.Γ K, gaps⟩ a =
      (fugueChoose FuguePolicyGC.Γ K a,
        gChainOf K (fugueChoose FuguePolicyGC.Γ K a).2) := by
  obtain ⟨g, hg⟩ := hret
  unfold compactGapObservation
  rw [hmap, gapEntryOf_exact, hg]
  rfl

/-- Compact minting emits exactly the same sided operation as the uncollected
Fugue generator whenever the requested live gap is retained. -/
theorem compactInsertOp_exact {K : Know} {gaps : Finset GapEntry}
    (hmap : GapMapOK K gaps) {a : ℕ}
    (hret : ∃ g, retainedLiveGap K a = some g) (rep x : ℕ) :
    compactInsertOp FuguePolicyGC.Γ
      ⟨gFold FuguePolicyGC.Γ K, gaps⟩ rep x a =
      (genInsAfter FuguePolicyGC.Γ K rep x a).op := by
  rw [compactInsertOp]
  rw [compactGapObservation_exact hmap hret]
  rfl

/-- Issuer guard over the compact text representation. The inserted parent
may be absent from the retained raw shadow; a matching persisted gap is the
authority for its side, parent id, and coordinate prefix. -/
def compactSApplicable (Γ : OrderedPrefixCode) (e : Op SOp)
    (s : CompactSidedState) : Prop :=
  match e.2.2 with
  | .ins _ π parent side =>
      e.1 ≠ 0 ∧ e.1 ∉ sIds s.text ∧
      ∃ ge ∈ s.gaps, ge.observation.1 = (side, parent) ∧
        π = Sal.EmbedRGA.sidedCoordOf Γ ge.observation.2
  | .del x => x ∈ sIds s.text

theorem compactInsertOp_applicable {K : Know} {gaps : Finset GapEntry}
    (hmap : GapMapOK K gaps) {a : ℕ}
    (hret : ∃ g, retainedLiveGap K a = some g) {rep x : ℕ}
    (hx0 : x ≠ 0) (hxfresh : x ∉ sIds (gFold FuguePolicyGC.Γ K))
    (hstored : ∃ ge ∈ gaps,
      ge.observation =
        (fugueChoose FuguePolicyGC.Γ K a,
          gChainOf K (fugueChoose FuguePolicyGC.Γ K a).2)) :
    compactSApplicable FuguePolicyGC.Γ
      (compactInsertOp FuguePolicyGC.Γ
        ⟨gFold FuguePolicyGC.Γ K, gaps⟩ rep x a)
      ⟨gFold FuguePolicyGC.Γ K, gaps⟩ := by
  obtain ⟨ge, hge, hobs⟩ := hstored
  rw [compactInsertOp]
  rw [compactGapObservation_exact hmap hret]
  refine ⟨hx0, hxfresh, ge, hge, ?_, ?_⟩
  · exact congrArg Prod.fst hobs
  · exact congrArg (fun z => Sal.EmbedRGA.sidedCoordOf FuguePolicyGC.Γ z.2)
      hobs.symm

/-- Existing merge theory discharges the compact policy observation: merging
two optional retained gaps yields exactly the observation of their full
uncollected union under the reachable Fugue invariants. -/
theorem compactGapMerge_exact {K K' : Know}
    (invK : FugueFwd.FInv FuguePolicyGC.Γ K)
    (invK' : FugueFwd.FInv FuguePolicyGC.Γ K')
    (invU : FugueFwd.FInv FuguePolicyGC.Γ (syncK K K'))
    (hwfK : SWf FuguePolicyGC.Γ (gOps K))
    (hwfK' : SWf FuguePolicyGC.Γ (gOps K'))
    (hwfU : SWf FuguePolicyGC.Γ (gOps (syncK K K')))
    (hembedK : ∀ {x}, x ∈ gMintedIds K → x ∈ gMintedIds (syncK K K'))
    (hembedK' : ∀ {x}, x ∈ gMintedIds K' → x ∈ gMintedIds (syncK K K'))
    (hchainK : ∀ {x}, x = 0 ∨ x ∈ gMintedIds K →
      gChainOf K x = gChainOf (syncK K K') x)
    (hchainK' : ∀ {x}, x = 0 ∨ x ∈ gMintedIds K' →
      gChainOf K' x = gChainOf (syncK K K') x)
    (a : ℕ) :
    (mergeRetainedGap K K' a).map (fun g => gapObservation g a) =
      (retainedLiveGap (syncK K K') a).map
        (fun g => gapObservation g a) :=
  mergeRetainedGap_observation_exact invK invK' invU hwfK hwfK' hwfU
    hembedK hembedK' hchainK hchainK' a

/-! ## Atomic Peritext collection: text-shadow layer -/

open Sal.ConditionedMRDTs.PeritextEmbed.MarkDoc
open Sal.ConditionedMRDTs.PeritextEmbed.MarksGC

/-- Mark rendering consumes document order, ids, and codepoints, but not the
sided coordinate representation. This view embeds a sided shadow into the
existing document-order renderer with dummy coordinates. -/
noncomputable def docOfS (s : SState) (deleted : Finset ℕ) : DocD where
  shadow := s.map fun r => (r.1, r.2.1, ([] : List Bool))
  deleted := deleted.toList

noncomputable def renderCompact (s : CompactState) (mt : MType) :
    List (ℕ × Bool) :=
  renderMarksDoc (docOfS s.sided.text s.deleted) s.marks.toList mt

/-- Pure atomic collector. `newGaps` must separately satisfy `GapMapOK`; it is
supplied by the frontier/policy-evidence layer rather than guessed here. -/
noncomputable def collect (p : Plan) (newGaps : Finset GapEntry)
    (s : CompactState) : CompactState where
  sided :=
    { text := s.sided.text.filter fun r => p.keepText r.1
      gaps := newGaps }
  deleted := s.deleted.filter fun x => p.keepDelete x
  marks := s.marks.filter fun m => p.keepMark m.mid

theorem docOfS_filter (s : SState) (deleted : Finset ℕ) (kp : ℕ → Bool) :
    docOfS (s.filter fun r => kp r.1) deleted =
      dropDoc (docOfS s deleted) kp := by
  unfold docOfS dropDoc
  congr 1
  rw [List.filter_map]
  rfl

/-- Text collection is immediately render-invisible when it drops only
logically deleted nodes and retains every boundary of every retained mark.
This theorem is coordinate-encoding independent and therefore applies to the
sided shadow through `docOfS`. -/
theorem collectText_render_preserved (s : CompactState) (p : Plan)
    (newGaps : Finset GapEntry) (mt : MType)
    (hkeepDel : ∀ x ∈ s.deleted, p.keepDelete x = true)
    (hkeepMark : ∀ m ∈ s.marks, p.keepMark m.mid = true)
    (hnd : (s.sided.text.map Prod.fst).Nodup)
    (hdead : ∀ r ∈ s.sided.text, p.keepText r.1 = false →
      r.1 ∈ s.deleted)
    (hanchor : ∀ m ∈ s.marks,
      p.keepText m.start_id = true ∧ p.keepText m.end_id = true) :
    renderCompact (collect p newGaps s) mt = renderCompact s mt := by
  have hdel : (s.deleted.filter fun x => p.keepDelete x) = s.deleted := by
    apply Finset.filter_eq_self.mpr
    intro x hx
    simpa [hkeepDel x hx]
  have hmarks : (s.marks.filter fun m => p.keepMark m.mid) = s.marks := by
    apply Finset.filter_eq_self.mpr
    intro m hm
    simpa [hkeepMark m hm]
  unfold renderCompact collect
  simp only [hdel, hmarks]
  rw [docOfS_filter]
  apply renderMarksDoc_dropDoc
  · simpa [docOfS, DocD.birthIds] using hnd
  · intro c hc hdrop
    have hcS : c ∈ s.sided.text.map Prod.fst := by
      simpa [docOfS, DocD.birthIds] using hc
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hcS
    have hd := hdead r hr hdrop
    simpa [docOfS] using hd
  · intro m hm
    apply hanchor
    simpa using hm

/-! ## Continuation through a collected sided shadow -/

theorem sInsert_below {r : SRec} : ∀ {s : SState},
    (∀ x ∈ s, Sal.EmbedRGA.keyLt (Sal.EmbedRGA.sKey x.2.2)
      (Sal.EmbedRGA.sKey r.2.2) = true) → sInsert r s = r :: s
  | [], _ => rfl
  | x :: xs, h => by
      simp only [sInsert]
      rw [if_pos (h x List.mem_cons_self)]

theorem sInsert_filter (kp : ℕ → Bool) (r : SRec) (hr : kp r.1 = true) :
    ∀ s : SState, SSorted s →
      sInsert r (s.filter fun x => kp x.1) =
        (sInsert r s).filter fun x => kp x.1
  | [], _ => by simp [sInsert, hr]
  | x :: xs, hs => by
      have hxs := (List.pairwise_cons.mp hs).2
      have hbelow := (List.pairwise_cons.mp hs).1
      by_cases hx : kp x.1 = true
      · by_cases hlt : Sal.EmbedRGA.keyLt (Sal.EmbedRGA.sKey x.2.2)
            (Sal.EmbedRGA.sKey r.2.2)
        · simp [sInsert, hlt, hr, hx]
        · simp [sInsert, hlt, hr, hx, sInsert_filter kp r hr xs hxs]
      · by_cases hlt : Sal.EmbedRGA.keyLt (Sal.EmbedRGA.sKey x.2.2)
            (Sal.EmbedRGA.sKey r.2.2)
        · rw [show (x :: xs).filter (fun y => kp y.1) =
              xs.filter (fun y => kp y.1) by simp [hx]]
          rw [show sInsert r (x :: xs) = r :: x :: xs by
            simp [sInsert, hlt]]
          rw [show (r :: x :: xs).filter (fun y => kp y.1) =
            r :: xs.filter (fun y => kp y.1) by simp [hr, hx]]
          exact sInsert_below (fun y hy =>
            Sal.EmbedRGA.keyLt_trans
              (hbelow y (List.mem_of_mem_filter hy)) hlt)
        · simp [sInsert, hlt, hr, hx, sInsert_filter kp r hr xs hxs]

theorem sUpdate_filter {Γ : OrderedPrefixCode} (kp : ℕ → Bool)
    (s : SState) (o : Op SOp)
    (hsort : SSorted s)
    (hfresh : ∀ e π a sd, o.2.2 = SOp.ins e π a sd → o.1 ∉ sIds s)
    (hkeep : ∀ e π a sd, o.2.2 = SOp.ins e π a sd → kp o.1 = true) :
    sUpdate Γ (s.filter fun r => kp r.1) o =
      (sUpdate Γ s o).filter fun r => kp r.1 := by
  rcases o with ⟨t, rep, op⟩
  cases op with
  | del x =>
      simp only [sUpdate]
      rw [List.filter_filter, List.filter_filter]
      apply List.filter_congr
      intro r hr
      exact Bool.and_comm _ _
  | ins e π a sd =>
      have hfr := hfresh e π a sd rfl
      have hfr' : t ∉ sIds (s.filter fun r => kp r.1) := by
        intro ht
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ht
        exact hfr (List.mem_map.mpr ⟨r, List.mem_of_mem_filter hr, rfl⟩)
      simp only [sUpdate]
      rw [if_neg hfr', if_neg hfr]
      exact sInsert_filter kp _ (hkeep e π a sd rfl) s hsort

/-- A continuation is fresh at every prefix and retains every newly minted
text id. This is the exact operational condition needed for collection to
commute with later text delivery. -/
def TextContOK (Γ : OrderedPrefixCode) (s : SState)
    (kp : ℕ → Bool) (τ : List (Op SOp)) : Prop :=
  ∀ (pre : List (Op SOp)) (o : Op SOp) (post : List (Op SOp)),
    τ = pre ++ o :: post →
    (∀ e π a sd, o.2.2 = SOp.ins e π a sd →
      o.1 ∉ sIds (applySeq (S Γ).toCRDTSig s pre) ∧ kp o.1 = true ∧
      ∀ r ∈ (show SState from applySeq (S Γ).toCRDTSig s pre),
        Sal.EmbedRGA.sKey r.2.2 ≠ Sal.EmbedRGA.sKey (sCoord Γ o))

theorem applySeq_s_filter {Γ : OrderedPrefixCode} (kp : ℕ → Bool) :
    ∀ (τ : List (Op SOp)) (s : SState), SSorted s → TextContOK Γ s kp τ →
      applySeq (S Γ).toCRDTSig (s.filter fun r => kp r.1) τ =
        (applySeq (S Γ).toCRDTSig s τ).filter fun r => kp r.1
  | [], s, _, _ => rfl
  | o :: τ, s, hsort, hok => by
      have hhead := hok [] o τ (by simp)
      rw [show applySeq (S Γ).toCRDTSig (s.filter fun r => kp r.1) (o :: τ) =
        applySeq (S Γ).toCRDTSig
          (sUpdate Γ (s.filter fun r => kp r.1) o) τ from rfl]
      rw [show applySeq (S Γ).toCRDTSig s (o :: τ) =
        applySeq (S Γ).toCRDTSig (sUpdate Γ s o) τ from rfl]
      rw [sUpdate_filter kp s o hsort
        (fun e π a sd h => (hhead e π a sd h).1)
        (fun e π a sd h => (hhead e π a sd h).2.1)]
      have hsort' : SSorted (sUpdate Γ s o) := by
        rcases o with ⟨t, rep, op⟩
        cases op with
        | del x => exact List.Pairwise.filter _ hsort
        | ins e π a sd =>
            apply sUpdate_sorted hsort
            intro r hr
            exact (hhead e π a sd rfl).2.2 r hr
      apply applySeq_s_filter kp τ (sUpdate Γ s o)
        hsort'
      intro pre e post heq x π a sd hins
      have hall := hok (o :: pre) e post (by simpa [List.append_assoc] using heq)
        x π a sd hins
      simpa [applySeq] using hall

/-- Post-GC continuation theorem for the text-shadow layer. The compact and
uncollected twins process the same delayed/future text operations and retain
identical rich-text rendering. -/
theorem collectedText_continuation_render {Γ : OrderedPrefixCode}
    (s : CompactState) (kp : ℕ → Bool) (τ : List (Op SOp)) (mt : MType)
    (hsort : SSorted s.sided.text)
    (hok : TextContOK Γ s.sided.text kp τ)
    (hnd : (sIds (applySeq (S Γ).toCRDTSig s.sided.text τ)).Nodup)
    (hdead : ∀ r ∈ (show SState from
        applySeq (S Γ).toCRDTSig s.sided.text τ),
      kp r.1 = false → r.1 ∈ s.deleted)
    (hanchor : ∀ m ∈ s.marks,
      kp m.start_id = true ∧ kp m.end_id = true) :
    renderCompact (s.withText (applySeq (S Γ).toCRDTSig
      (s.sided.text.filter fun r => kp r.1) τ)) mt =
    renderCompact (s.withText
      (applySeq (S Γ).toCRDTSig s.sided.text τ)) mt := by
  rw [applySeq_s_filter kp τ s.sided.text hsort hok]
  unfold renderCompact
  simp only [CompactState.withText]
  rw [docOfS_filter]
  apply renderMarksDoc_dropDoc
  · simpa [docOfS, DocD.birthIds] using hnd
  · intro c hc hdrop
    have hcS : c ∈ sIds (applySeq (S Γ).toCRDTSig s.sided.text τ) := by
      simpa [docOfS, DocD.birthIds, sIds] using hc
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hcS
    have hd := hdead r hr hdrop
    simpa [docOfS] using hd
  · intro m hm
    apply hanchor
    simpa using hm

/-! ## Deleted-id and mark-event layers -/

/-- Once the text shadow has been collected, deletion evidence for ids with
no retained birth record is unobservable and can be removed. -/
noncomputable def trimDeleted (s : CompactState) : CompactState :=
  { s with deleted := s.deleted.filter fun x => x ∈ s.sided.text.map Prod.fst }

theorem trimDeleted_render_preserved (s : CompactState) (mt : MType) :
    renderCompact (trimDeleted s) mt = renderCompact s mt := by
  unfold renderCompact trimDeleted
  change renderMarksDoc
      { (docOfS s.sided.text s.deleted) with deleted :=
          (s.deleted.filter fun x => x ∈ s.sided.text.map Prod.fst).toList }
      s.marks.toList mt = _
  apply renderMarksDoc_deleted_congr
  intro c hc
  have hcS : c ∈ s.sided.text.map Prod.fst := by
    simpa [docOfS, DocD.birthIds] using hc
  simp [List.contains_eq_mem, hcS, docOfS]

/-- One frontier-guarded add/remove mark-pair collection step. This is the
existing A3 theorem instantiated at the sided document-order view; coordinate
encoding is irrelevant to the renderer. -/
theorem dropMarkPair_render_preserved (s : CompactState)
    (marks : List MarkD) (m r : MarkD) (mt : MType)
    (hm : m ∈ marks) (hr : r ∈ marks)
    (hopm : m.op = MarkOp.add) (hopr : r.op = MarkOp.remove)
    (hty : r.mtype = m.mtype) (hlt : m.mid < r.mid)
    (hsid : r.start_id = m.start_id) (heid : r.end_id = m.end_id)
    (hss : r.startSide = m.startSide) (hes : r.endSide = m.endSide)
    (hnodup : (marks.map MarkD.mid).Nodup)
    (hothers : ∀ o ∈ marks, o.mtype = m.mtype → o.mid ≠ m.mid →
      o.mid ≠ r.mid → r.mid < o.mid)
    (hwindow : ∀ c ∈ (docOfS s.sided.text s.deleted).birthIds,
      c ≤ m.mid ∨ r.mid < c) :
    renderMarksDoc (docOfS s.sided.text s.deleted)
      (marks.filter (fun o => !(o.mid == m.mid || o.mid == r.mid))) mt =
    renderMarksDoc (docOfS s.sided.text s.deleted) marks mt :=
  a3_guarded_drop _ marks m r mt hm hr hopm hopr hty hlt hsid heid hss hes
    hnodup hothers hwindow

/-! ## Atomic certificate and repeated collection -/

/-- Frontier evidence after its transport into datatype-specific retention
facts. `stable` records the evidence boundary explicitly; the preservation
proof consumes its consequences (`dead`, anchors, and gap-map exactness). -/
structure AtomicBaseCertificate (s : CompactState) (p : Plan)
    (newGaps : Finset GapEntry) where
  stable : ℕ → Prop
  sorted : SSorted s.sided.text
  nodup : (s.sided.text.map Prod.fst).Nodup
  keepDeletes : ∀ x ∈ s.deleted, p.keepDelete x = true
  keepMarks : ∀ m ∈ s.marks, p.keepMark m.mid = true
  droppedStable : ∀ r ∈ s.sided.text, p.keepText r.1 = false → stable r.1
  droppedDead : ∀ r ∈ s.sided.text, p.keepText r.1 = false → r.1 ∈ s.deleted
  keepAnchors : ∀ m ∈ s.marks,
    p.keepText m.start_id = true ∧ p.keepText m.end_id = true
  gapEvidence : ∃ K : Know, GapMapOK K newGaps

/-! ## Frontier discharge and delayed delivery

The collector does not manufacture stability.  The runtime's gossip/fetch
receipts establish `AllHeardSince`; the generic metatheory turns that
observable frontier into semantic `SettledAt`.  The remaining fields below
are the datatype-specific transport from events in the settled cut to the
ids that the pure collector drops. -/

/-- A frontier-backed atomic certificate.  `droppedInCut` and
`delayedReferencesKept` are the Peritext-specific audit boundary; stability
itself is derived, rather than assumed, from all-heads evidence. -/
structure FrontierAtomicCertificate {Γ : OrderedPrefixCode}
    (C : Configuration (Core Γ)) (v : Version)
    (s : CompactState) (p : Plan) (newGaps : Finset GapEntry) where
  base : AtomicBaseCertificate s p newGaps
  versionState : (Core Γ).State
  versionEvents : Set (Op (Core Γ).AppOp)
  cut : Set (Op (Core Γ).AppOp)
  versionAt : C.ver v = some (versionState, versionEvents)
  reachInvariant : ReachInvE C
  downwardClosed : ∀ a b, C.vis a b → b ∈ cut → a ∈ cut
  allHeard : AllHeardSince C v cut
  droppedInCut : ∀ r ∈ s.sided.text, p.keepText r.1 = false →
    ∃ e ∈ cut, e.1 = r.1
  /-- No operation that can still arrive names a reclaimed character id.
  Text insertions also retain their anchor; marks retain both boundaries. -/
  delayedReferencesKept : ∀ e : Op (Core Γ).AppOp,
    e ∉ cut →
    match e.2.2 with
    | Sum.inl (.ins _ _ parent _) =>
        parent = 0 ∨ p.keepText parent = true
    | Sum.inl (.del x) => p.keepText x = true
    | Sum.inr (Sum.inl (OSOp.add x)) => p.keepText x = true
    | Sum.inr (Sum.inl (OSOp.rem x)) => p.keepText x = true
    | Sum.inr (Sum.inr (OSOp.add m)) =>
        p.keepText m.start_id = true ∧ p.keepText m.end_id = true
    | Sum.inr (Sum.inr (OSOp.rem _)) => True

/-- The semantic stability premise used by state GC follows from the same
gossip/fetch frontier evidence used by distributed history GC. -/
theorem FrontierAtomicCertificate.settled {Γ : OrderedPrefixCode}
    {C : Configuration (Core Γ)} {v : Version}
    {s : CompactState} {p : Plan} {newGaps : Finset GapEntry}
    (cert : FrontierAtomicCertificate C v s p newGaps) :
    SettledAt C v cert.cut :=
  settledAt_of_allHeard cert.reachInvariant cert.versionAt
    cert.downwardClosed cert.allHeard

/-- Atomic text-shadow and deletion-evidence collection. Marks are retained in
this base step; guarded mark-pair steps compose afterward as independently
checked frontier actions. -/
noncomputable def collectStableBase (s : CompactState) (p : Plan)
    (newGaps : Finset GapEntry) : CompactState :=
  trimDeleted (collect p newGaps s)

theorem collectStableBase_render_preserved (s : CompactState) (p : Plan)
    (newGaps : Finset GapEntry) (cert : AtomicBaseCertificate s p newGaps)
    (mt : MType) :
    renderCompact (collectStableBase s p newGaps) mt = renderCompact s mt := by
  unfold collectStableBase
  calc
    renderCompact (trimDeleted (collect p newGaps s)) mt =
        renderCompact (collect p newGaps s) mt :=
      trimDeleted_render_preserved _ _
    _ = renderCompact s mt :=
      collectText_render_preserved s p newGaps mt cert.keepDeletes
        cert.keepMarks cert.nodup cert.droppedDead cert.keepAnchors

/-- Paper-facing state-GC capstone for one epoch: observable frontier
evidence establishes semantic stability, and the resulting atomic collection
preserves the rich-text rendering.  The certificate also retains the
`delayedReferencesKept` field needed before subsequent delivery. -/
theorem frontier_collectStableBase_safe {Γ : OrderedPrefixCode}
    {C : Configuration (Core Γ)} {v : Version}
    (s : CompactState) (p : Plan) (newGaps : Finset GapEntry)
    (cert : FrontierAtomicCertificate C v s p newGaps) (mt : MType) :
    SettledAt C v cert.cut ∧
      renderCompact (collectStableBase s p newGaps) mt = renderCompact s mt :=
  ⟨cert.settled,
    collectStableBase_render_preserved s p newGaps cert.base mt⟩

/-- Explicit operational boundary for delayed delivery. No event outside the
settled cut may name a reclaimed text id. -/
theorem frontier_delayed_references_kept {Γ : OrderedPrefixCode}
    {C : Configuration (Core Γ)} {v : Version}
    {s : CompactState} {p : Plan} {newGaps : Finset GapEntry}
    (cert : FrontierAtomicCertificate C v s p newGaps) :
    ∀ e : Op (Core Γ).AppOp, e ∉ cert.cut →
      match e.2.2 with
      | Sum.inl (.ins _ _ parent _) =>
          parent = 0 ∨ p.keepText parent = true
      | Sum.inl (.del x) => p.keepText x = true
      | Sum.inr (Sum.inl (OSOp.add x)) => p.keepText x = true
      | Sum.inr (Sum.inl (OSOp.rem x)) => p.keepText x = true
      | Sum.inr (Sum.inr (OSOp.add m)) =>
          p.keepText m.start_id = true ∧ p.keepText m.end_id = true
      | Sum.inr (Sum.inr (OSOp.rem _)) => True :=
  cert.delayedReferencesKept

/-- Two collection epochs compose without strengthening either epoch's
frontier certificate. -/
theorem collectStableBase_twoEpoch
    (s : CompactState) (p₁ p₂ : Plan) (g₁ g₂ : Finset GapEntry)
    (c₁ : AtomicBaseCertificate s p₁ g₁)
    (c₂ : AtomicBaseCertificate (collectStableBase s p₁ g₁) p₂ g₂)
    (mt : MType) :
    renderCompact
      (collectStableBase (collectStableBase s p₁ g₁) p₂ g₂) mt =
      renderCompact s mt := by
  rw [collectStableBase_render_preserved _ _ _ c₂,
    collectStableBase_render_preserved _ _ _ c₁]

#print axioms naive_three_component_gc_is_not_continuation_safe
#print axioms gapEntryOf_exact
#print axioms compactGapObservation_exact
#print axioms compactInsertOp_exact
#print axioms compactInsertOp_applicable
#print axioms compactGapMerge_exact
#print axioms collectText_render_preserved
#print axioms applySeq_s_filter
#print axioms collectedText_continuation_render
#print axioms trimDeleted_render_preserved
#print axioms dropMarkPair_render_preserved
#print axioms collectStableBase_render_preserved
#print axioms FrontierAtomicCertificate.settled
#print axioms frontier_collectStableBase_safe
#print axioms frontier_delayed_references_kept
#print axioms collectStableBase_twoEpoch

end Sal.ConditionedMRDTs.PeritextSided.StateGC
