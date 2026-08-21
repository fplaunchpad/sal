import Sal.MRDTs.Framework.StateGC
import Sal.MRDTs.Instances.SidedPeritext
import Sal.MRDTs.Instances.FuguePolicyGC
import Sal.MRDTs.Instances.PeritextRenderGC
import Sal.MRDTs.Instances.PeritextMarkPairGC

/-! # Sided Peritext datatype-state collection

The three logical components remain text, logical deletions, and immutable
mark events.  The compact text representation additionally owns a `LiveGap`
summary because future Fugue minting cannot be reconstructed from the live
text projection alone.
-/

namespace Sal.MRDTs.Instances.SidedPeritext.StateGC

open Sal.MRDTs.Foundation
open Sal.EmbedRGA (OrderedPrefixCode Side SChain)
open Sal.MRDTs.Instances.SidedEmbedRGA
open Sal.MRDTs.Instances.SidedEmbedRGA.FuguePolicyGC
open Sal.MRDTs.Instances.PeritextRender

noncomputable section

structure GapEntry where
  anchor : Nat
  observation : (Sal.EmbedRGA.Side × Nat) × SChain
  deriving DecidableEq

structure CompactSidedState where
  text : SState
  gaps : Finset GapEntry

structure CompactState where
  sided : CompactSidedState
  deleted : Finset Nat
  marks : List MarkEvent
  /-- Lamport frontier below which absent identifiers are certified old.
  Fresh mints must be strictly above this cutoff. -/
  stableCut : Nat

def snapshot (gaps : Finset GapEntry) (s : (Core Γ).State) : CompactState where
  sided := ⟨s.1, gaps⟩
  deleted := s.2.1
  marks := s.2.2.toList
  stableCut := 0

def compactDocument (s : CompactState) : DocD where
  shadow := s.sided.text.map fun r => (r.1, r.2.1, ([] : List Bool))
  deleted := s.deleted.toList

def query (s : CompactState) (kind : MType) : List (Nat × Bool) :=
  renderMarksDoc (compactDocument s) s.marks kind

def gapEntryOf (K : Know) (a : Nat) : Option GapEntry :=
  (retainedLiveGap K a).map fun g => ⟨a, gapObservation g a⟩

theorem gapEntryOf_exact (K : Know) (a : Nat) :
    (gapEntryOf K a).map GapEntry.observation =
      (retainedLiveGap K a).map (fun _ =>
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
      simp only [h, Option.map_some, Function.comp_apply, Option.some.injEq]
      unfold gapObservation
      exact Prod.ext (liveGapChoose_exact K a)
        (liveGapParentChain_exact K a)

def gapLookup (gaps : Finset GapEntry) (a : Nat) :
    Option ((Sal.EmbedRGA.Side × Nat) × SChain) :=
  ((gaps.toList.find? fun e => e.anchor = a).map GapEntry.observation)

def GapMapOK (K : Know) (gaps : Finset GapEntry) : Prop :=
  ∀ a, gapLookup gaps a = (gapEntryOf K a).map GapEntry.observation

def compactGapObservation (s : CompactSidedState) (a : Nat) :
    (Sal.EmbedRGA.Side × Nat) × SChain :=
  (gapLookup s.gaps a).getD ((Sal.EmbedRGA.Side.R, a), [])

def compactInsertOp (Γ : OrderedPrefixCode)
    (s : CompactSidedState) (rep x a : Nat) : Op SOp :=
  let choice := (compactGapObservation s a).1
  let parentChain := (compactGapObservation s a).2
  (x, rep, .ins x (Sal.EmbedRGA.sidedCoordOf Γ parentChain)
    choice.2 choice.1)

theorem compactGapObservation_exact {K : Know} {gaps : Finset GapEntry}
    (hmap : GapMapOK K gaps) {a : Nat}
    (hret : ∃ g, retainedLiveGap K a = some g) :
    compactGapObservation ⟨gFold FuguePolicyGC.Γ K, gaps⟩ a =
      (fugueChoose FuguePolicyGC.Γ K a,
        gChainOf K (fugueChoose FuguePolicyGC.Γ K a).2) := by
  obtain ⟨g, hg⟩ := hret
  unfold compactGapObservation
  rw [hmap, gapEntryOf_exact, hg]
  rfl

theorem compactInsertOp_exact {K : Know} {gaps : Finset GapEntry}
    (hmap : GapMapOK K gaps) {a : Nat}
    (hret : ∃ g, retainedLiveGap K a = some g) (rep x : Nat) :
    compactInsertOp FuguePolicyGC.Γ
      ⟨gFold FuguePolicyGC.Γ K, gaps⟩ rep x a =
      (genInsAfter FuguePolicyGC.Γ K rep x a).op := by
  rw [compactInsertOp, compactGapObservation_exact hmap hret]
  rfl

structure TextPlan where
  keep : Nat → Bool
  gaps : Finset GapEntry
  stableCut : Nat
  drop_below : ∀ x, keep x = false → x ≤ stableCut

def collectText (p : TextPlan) (s : CompactState) : CompactState :=
  { sided :=
      { text := s.sided.text.filter (fun r => p.keep r.1)
        gaps := p.gaps }
    deleted := s.deleted
    marks := s.marks
    stableCut := max s.stableCut p.stableCut }

theorem stableCut_mono_collectText (p : TextPlan) (s : CompactState) :
    s.stableCut ≤ (collectText p s).stableCut := by
  simp [collectText]

theorem dropped_below_stableCut (p : TextPlan) (s : CompactState)
    {r : SRec} (_hr : r ∈ s.sided.text) (hdrop : p.keep r.1 = false) :
    r.1 ≤ (collectText p s).stableCut := by
  exact le_trans (p.drop_below r.1 hdrop) (Nat.le_max_right _ _)

theorem TextPlan.keeps_fresh (p : TextPlan) {x : Nat}
    (hfresh : p.stableCut < x) : p.keep x = true := by
  cases h : p.keep x with
  | false => exact False.elim (Nat.not_le_of_lt hfresh (p.drop_below x h))
  | true => rfl

/-- A Lamport-fresh identifier cannot belong to the collected stable cut. -/
theorem fresh_above_stableCut {s : CompactState} {x : Nat}
    (hfresh : s.stableCut < x) : ¬x ≤ s.stableCut :=
  Nat.not_le_of_lt hfresh

theorem compactDocument_collectText (p : TextPlan) (s : CompactState) :
    compactDocument (collectText p s) =
      PeritextRender.GC.dropDoc (compactDocument s) p.keep := by
  unfold compactDocument collectText PeritextRender.GC.dropDoc
  congr 1
  rw [List.filter_map]
  rfl

/-- Atomic state collection preserves every rich-text query.  The hypotheses
are the implementer obligations discharged from the settled frontier: only
logically deleted text is removed, and all boundaries of retained marks stay.
The separate gap map is irrelevant to the current read but required for legal
future insertions. -/
theorem collectText_query_preserved (p : TextPlan) (s : CompactState)
    (hnd : (compactDocument s).birthIds.Nodup)
    (hdead : ∀ c ∈ (compactDocument s).birthIds,
      p.keep c = false → (compactDocument s).deleted.contains c = true)
    (hanchor : ∀ m ∈ s.marks,
      p.keep m.start_id = true ∧ p.keep m.end_id = true) :
    ∀ kind, query (collectText p s) kind = query s kind := by
  intro kind
  unfold query
  rw [compactDocument_collectText]
  exact PeritextRender.GC.renderMarksDoc_dropDoc
    (compactDocument s) p.keep s.marks kind hnd hdead hanchor

/-! ## Continuation after collection -/

def CompactState.withText (s : CompactState) (text : SState) : CompactState :=
  { s with sided := { s.sided with text := text } }

theorem sInsert_below {r : SRec} : ∀ {s : SState},
    (∀ x ∈ s, Sal.EmbedRGA.keyLt (Sal.EmbedRGA.sKey x.2.2)
      (Sal.EmbedRGA.sKey r.2.2) = true) → sInsert r s = r :: s
  | [], _ => rfl
  | x :: xs, h => by
      simp only [sInsert]
      rw [if_pos (h x List.mem_cons_self)]

theorem sInsert_filter (kp : Nat → Bool) (r : SRec) (hr : kp r.1 = true) :
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
          rw [show sInsert r (x :: xs) = r :: x :: xs by simp [sInsert, hlt]]
          rw [show (r :: x :: xs).filter (fun y => kp y.1) =
            r :: xs.filter (fun y => kp y.1) by simp [hr, hx]]
          exact sInsert_below (fun y hy =>
            Sal.EmbedRGA.keyLt_trans
              (hbelow y (List.mem_of_mem_filter hy)) hlt)
        · simp [sInsert, hlt, hr, hx, sInsert_filter kp r hr xs hxs]

theorem sUpdate_filter {Γ : OrderedPrefixCode} (kp : Nat → Bool)
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

/-- Every future insertion is fresh and retained at the prefix where it is
delivered. This is the continuation condition supplied by an epoch/frontier
certificate. -/
def TextContOK (Γ : OrderedPrefixCode) (s : SState)
    (kp : Nat → Bool) (τ : List (Op SOp)) : Prop :=
  ∀ (pre : List (Op SOp)) (o : Op SOp) (post : List (Op SOp)),
    τ = pre ++ o :: post →
    (∀ e π a sd, o.2.2 = SOp.ins e π a sd →
      o.1 ∉ sIds (applySeq (S Γ).toCRDTSig s pre) ∧ kp o.1 = true ∧
      ∀ r ∈ (show SState from applySeq (S Γ).toCRDTSig s pre),
        Sal.EmbedRGA.sKey r.2.2 ≠ Sal.EmbedRGA.sKey (sCoord Γ o))

/-- Runtime-facing continuation evidence. The epoch clock supplies retention
of every future insertion; the remaining clauses are the ordinary freshness
and immutable-key obligations. -/
def TextEpochContOK (Γ : OrderedPrefixCode) (s : SState)
    (p : TextPlan) (τ : List (Op SOp)) : Prop :=
  ∀ (pre : List (Op SOp)) (o : Op SOp) (post : List (Op SOp)),
    τ = pre ++ o :: post →
    ∀ e π a sd, o.2.2 = SOp.ins e π a sd →
      o.1 ∉ sIds (applySeq (S Γ).toCRDTSig s pre) ∧
      p.stableCut < o.1 ∧
      ∀ r ∈ (show SState from applySeq (S Γ).toCRDTSig s pre),
        Sal.EmbedRGA.sKey r.2.2 ≠ Sal.EmbedRGA.sKey (sCoord Γ o)

theorem textContOK_of_epoch {Γ : OrderedPrefixCode} {s : SState}
    {p : TextPlan} {τ : List (Op SOp)}
    (h : TextEpochContOK Γ s p τ) : TextContOK Γ s p.keep τ := by
  intro pre o post heq e π a sd hins
  obtain ⟨hfresh, habove, hkey⟩ := h pre o post heq e π a sd hins
  exact ⟨hfresh, p.keeps_fresh habove, hkey⟩

theorem applySeq_s_filter {Γ : OrderedPrefixCode} (kp : Nat → Bool) :
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
      apply applySeq_s_filter kp τ (sUpdate Γ s o) hsort'
      intro pre e post heq x π a sd hins
      have hall := hok (o :: pre) e post (by simpa [List.append_assoc] using heq)
        x π a sd hins
      simpa [applySeq] using hall

theorem collectedText_continuation_query {Γ : OrderedPrefixCode}
    (s : CompactState) (kp : Nat → Bool) (τ : List (Op SOp)) (kind : MType)
    (hsort : SSorted s.sided.text)
    (hok : TextContOK Γ s.sided.text kp τ)
    (hnd : (sIds (applySeq (S Γ).toCRDTSig s.sided.text τ)).Nodup)
    (hdead : ∀ r ∈ (show SState from
        applySeq (S Γ).toCRDTSig s.sided.text τ),
      kp r.1 = false → r.1 ∈ s.deleted)
    (hanchor : ∀ m ∈ s.marks,
      kp m.start_id = true ∧ kp m.end_id = true) :
    query (s.withText (applySeq (S Γ).toCRDTSig
      (s.sided.text.filter fun r => kp r.1) τ)) kind =
    query (s.withText
      (applySeq (S Γ).toCRDTSig s.sided.text τ)) kind := by
  rw [applySeq_s_filter kp τ s.sided.text hsort hok]
  unfold query CompactState.withText compactDocument
  simp only
  have hdoc :
      ({ shadow := (applySeq (S Γ).toCRDTSig s.sided.text τ).filter
            (fun r => kp r.1) |>.map (fun r => (r.1, r.2.1, ([] : List Bool)))
         deleted := s.deleted.toList } : DocD) =
        PeritextRender.GC.dropDoc
          { shadow := (applySeq (S Γ).toCRDTSig s.sided.text τ).map
              (fun r => (r.1, r.2.1, ([] : List Bool)))
            deleted := s.deleted.toList } kp := by
    unfold PeritextRender.GC.dropDoc
    congr 1
    rw [List.filter_map]
    rfl
  rw [hdoc]
  apply PeritextRender.GC.renderMarksDoc_dropDoc
  · simpa [DocD.birthIds, sIds] using hnd
  · intro c hc hdrop
    have hcS : c ∈ sIds (applySeq (S Γ).toCRDTSig s.sided.text τ) := by
      simpa [DocD.birthIds, sIds] using hc
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hcS
    have hd := hdead r hr hdrop
    simpa using hd
  · exact hanchor

/-! ## Deletion and mark-event collection -/

/-- Deletion evidence for ids whose birth records have already been removed
is unobservable and can be discarded. -/
def trimDeleted (s : CompactState) : CompactState :=
  { s with deleted := s.deleted.filter fun x => x ∈ s.sided.text.map Prod.fst }

theorem trimDeleted_query_preserved (s : CompactState) (kind : MType) :
    query (trimDeleted s) kind = query s kind := by
  unfold query trimDeleted compactDocument
  simp only
  change renderMarksDoc
      { (compactDocument s) with deleted :=
          (s.deleted.filter fun x => x ∈ s.sided.text.map Prod.fst).toList }
      s.marks kind =
    renderMarksDoc (compactDocument s) s.marks kind
  apply PeritextRender.GC.renderMarksDoc_deleted_congr
  intro c hc
  have hcS : c ∈ sIds s.sided.text := by
    simpa [compactDocument, DocD.birthIds, sIds, List.map_map] using hc
  have hmem : c ∈ s.sided.text.map Prod.fst := by
    simpa [sIds] using hcS
  rw [List.contains_eq_mem, List.contains_eq_mem]
  simp only [Finset.mem_toList, Finset.mem_filter]
  simp [compactDocument, hmem]

def dropMarkPair (s : CompactState) (m r : MarkEvent) : CompactState :=
  { s with marks := s.marks.filter fun o =>
      !(o.mid == m.mid || o.mid == r.mid) }

/-- A frontier-guarded add/remove mark-pair collection step. The alpha and
beta premises are necessary: the native SPOTs exhibit observable failures if
either delayed marks or the Lamport growth window is ignored. -/
theorem dropMarkPair_query_preserved (s : CompactState)
    (m r : MarkEvent) (kind : MType)
    (hm : m ∈ s.marks) (hr : r ∈ s.marks)
    (hopm : m.op = MarkOp.add) (hopr : r.op = MarkOp.remove)
    (hty : r.mtype = m.mtype) (hlt : m.mid < r.mid)
    (hsid : r.start_id = m.start_id) (heid : r.end_id = m.end_id)
    (hss : r.startSide = m.startSide) (hes : r.endSide = m.endSide)
    (hnodup : (s.marks.map MarkD.mid).Nodup)
    (hothers : ∀ o ∈ s.marks, o.mtype = m.mtype →
      o.mid ≠ m.mid → o.mid ≠ r.mid → r.mid < o.mid)
    (hwindow : ∀ c ∈ (compactDocument s).birthIds,
      c ≤ m.mid ∨ r.mid < c) :
    query (dropMarkPair s m r) kind = query s kind := by
  unfold query dropMarkPair
  simp only [compactDocument]
  exact PeritextRender.GC.a3_guarded_drop
    (compactDocument s) s.marks m r kind hm hr hopm hopr hty hlt
    hsid heid hss hes hnodup hothers hwindow

#print axioms gapEntryOf_exact
#print axioms compactInsertOp_exact
#print axioms collectText_query_preserved
#print axioms dropped_below_stableCut
#print axioms TextPlan.keeps_fresh
#print axioms fresh_above_stableCut
#print axioms applySeq_s_filter
#print axioms textContOK_of_epoch
#print axioms collectedText_continuation_query
#print axioms trimDeleted_query_preserved
#print axioms dropMarkPair_query_preserved

end

end Sal.MRDTs.Instances.SidedPeritext.StateGC
