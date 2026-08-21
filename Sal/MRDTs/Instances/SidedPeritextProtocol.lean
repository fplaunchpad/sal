import Sal.MRDTs.Instances.SidedPeritextInteraction

/-! # Sided Peritext state-GC protocol

This module packages the component theorems as one physical transition
system. A physical version carries a compact materialization; the no-GC
configuration remains ghost state. Every materialization records the exact
retained text projection, its Fugue policy summary, LiveGap correctness, the
Lamport cutoff for omitted identifiers, and equality of every rich-text query.

Collection and epoch translation are silent. Ordinary and virtual-LCA steps
are visible. In particular, a virtual merge requires compact branch heads but
does not require a compact materialization of its semantic virtual LCA.
-/

namespace Sal.MRDTs.Instances.SidedPeritext.StateGC.Protocol

open Sal.MRDTs Foundation
open Sal.EmbedRGA (OrderedPrefixCode)
open Sal.MRDTs.Instances.SidedEmbedRGA
open Sal.MRDTs.Instances.SidedEmbedRGA.FuguePolicyGC
open Sal.MRDTs.Instances.SidedPeritext.StateGC
open Sal.MRDTs.Instances.SidedPeritext.StateGC.Interaction

noncomputable section

variable (Γ : OrderedPrefixCode)

abbrev D := SidedPeritext.RichCore Γ

/-- Complete evidence attached to one compact materialization. The query field
also covers deletion trimming and guarded mark-pair removal; those structures
need not be equal to the grow-only semantic stores. -/
structure Represents (full : (D Γ).State) (compact : CompactState) where
  keep : Nat → Bool
  knowledge : Know
  semanticText : full.1 = gFold FuguePolicyGC.Γ knowledge
  textProjection : compact.sided.text = full.1.filter (fun r => keep r.1)
  gapMap : GapMapOK knowledge compact.sided.gaps
  omittedOld : ∀ x, keep x = false → x ≤ compact.stableCut
  queryCorrect : ∀ kind, query compact kind = SidedPeritext.renderState full kind

def Represents.collectText {full : (D Γ).State} {compact : CompactState}
    (h : Represents Γ full compact) (plan : TextPlan)
    (hgap : GapMapOK h.knowledge plan.gaps)
    (hnd : (compactDocument compact).birthIds.Nodup)
    (hdead : ∀ c ∈ (compactDocument compact).birthIds,
      plan.keep c = false → (compactDocument compact).deleted.contains c = true)
    (hanchor : ∀ m ∈ compact.marks,
      plan.keep m.start_id = true ∧ plan.keep m.end_id = true) :
    Represents Γ full (StateGC.collectText plan compact) := by
  let keep' := fun x => h.keep x && plan.keep x
  refine ⟨keep', h.knowledge, h.semanticText, ?_, hgap, ?_, ?_⟩
  · rw [StateGC.collectText]
    simp only
    rw [h.textProjection, List.filter_filter]
    apply List.filter_congr
    intro r _
    simp [keep', Bool.and_comm]
  · intro x hx
    cases hk : h.keep x with
    | false =>
        exact le_trans (h.omittedOld x hk)
          (Nat.le_max_left compact.stableCut plan.stableCut)
    | true =>
        have hp : plan.keep x = false := by simpa [keep', hk] using hx
        exact le_trans (plan.drop_below x hp)
          (Nat.le_max_right compact.stableCut plan.stableCut)
  · intro kind
    rw [StateGC.collectText_query_preserved plan compact hnd hdead hanchor]
    exact h.queryCorrect kind

def Represents.trimDeleted {full : (D Γ).State} {compact : CompactState}
    (h : Represents Γ full compact) :
    Represents Γ full (StateGC.trimDeleted compact) := by
  refine ⟨h.keep, h.knowledge, h.semanticText, ?_, h.gapMap, ?_, ?_⟩
  · exact h.textProjection
  · exact h.omittedOld
  · intro kind
    rw [StateGC.trimDeleted_query_preserved compact kind]
    exact h.queryCorrect kind

def Represents.dropMarkPair {full : (D Γ).State} {compact : CompactState}
    (h : Represents Γ full compact) (m r : SidedPeritext.MarkEvent)
    (hm : m ∈ compact.marks) (hr : r ∈ compact.marks)
    (hopm : m.op = PeritextRender.MarkOp.add)
    (hopr : r.op = PeritextRender.MarkOp.remove)
    (hty : r.mtype = m.mtype) (hlt : m.mid < r.mid)
    (hsid : r.start_id = m.start_id) (heid : r.end_id = m.end_id)
    (hss : r.startSide = m.startSide) (hes : r.endSide = m.endSide)
    (hnodup : (compact.marks.map PeritextRender.MarkD.mid).Nodup)
    (hothers : ∀ o ∈ compact.marks, o.mtype = m.mtype →
      o.mid ≠ m.mid → o.mid ≠ r.mid → r.mid < o.mid)
    (hwindow : ∀ c ∈ (compactDocument compact).birthIds,
      c ≤ m.mid ∨ r.mid < c) :
    Represents Γ full (StateGC.dropMarkPair compact m r) := by
  refine ⟨h.keep, h.knowledge, h.semanticText, ?_, h.gapMap, ?_, ?_⟩
  · exact h.textProjection
  · exact h.omittedOld
  · intro kind
    rw [StateGC.dropMarkPair_query_preserved compact m r kind hm hr hopm
      hopr hty hlt hsid heid hss hes hnodup hothers hwindow]
    exact h.queryCorrect kind

/-- Physical execution state. `compact v = none` is permitted for an
unmaterialized historical version. Every replica head must be materialized. -/
structure Physical where
  semantic : Configuration (D Γ)
  compact : Version → Option CompactState
  sound : ∀ {v full events compactState},
    semantic.ver v = some (full, events) →
    compact v = some compactState → Represents Γ full compactState
  headCovered : ∀ {r v}, semantic.head r = some v → ∃ c, compact v = some c

def replace (P : Physical Γ) (v : Version) (c : CompactState) :
    Version → Option CompactState :=
  fun w => if w = v then some c else P.compact w

/-- Runtime Lamport obligation at an apply boundary. Fetch advances the local
clock before minting, so the new timestamp lies above the compact head's
stable cut. Other labels mint no datatype identifier. -/
def FreshAbove (P : Physical Γ) (label : Label (D Γ)) : Prop :=
  match label with
  | .apply t r _ => ∀ v c, P.semantic.head r = some v →
      P.compact v = some c → c.stableCut < t
  | _ => True

/-- Physical state-GC and execution steps. The component-specific silent
constructors expose exactly which collector ran. `reframe` is the atomic
cross-epoch translation justified by `merge_text_after_epoch_translation` and
the corresponding deletion/mark evidence stored in the target's `sound`
certificate. -/
inductive PhysicalStep (V : VirtualLCAResolver (D Γ)) :
    Physical Γ → Option (Label (D Γ)) → Physical Γ → Prop where
  | collectText {P P' : Physical Γ} {v : Version} {old : CompactState}
      (plan : TextPlan)
      (oldAt : P.compact v = some old)
      (semantic : P'.semantic = P.semantic)
      (compact : P'.compact = replace Γ P v (StateGC.collectText plan old)) :
      PhysicalStep V P none P'
  | trimDeleted {P P' : Physical Γ} {v : Version} {old : CompactState}
      (oldAt : P.compact v = some old)
      (semantic : P'.semantic = P.semantic)
      (compact : P'.compact = replace Γ P v (StateGC.trimDeleted old)) :
      PhysicalStep V P none P'
  | dropMarkPair {P P' : Physical Γ} {v : Version} {old : CompactState}
      (m r : SidedPeritext.MarkEvent)
      (oldAt : P.compact v = some old)
      (semantic : P'.semantic = P.semantic)
      (compact : P'.compact = replace Γ P v (StateGC.dropMarkPair old m r)) :
      PhysicalStep V P none P'
  | reframe {P P' : Physical Γ}
      (semantic : P'.semantic = P.semantic) :
      PhysicalStep V P none P'
  | ordinary {P P' : Physical Γ} {label : Label (D Γ)}
      (fresh : FreshAbove Γ P label)
      (step : Step (D Γ) P.semantic label P'.semantic) :
      PhysicalStep V P (some label) P'
  | virtual {P P' : Physical Γ} {label : Label (D Γ)}
      (fresh : FreshAbove Γ P label)
      (step : StepV (D Γ) V P.semantic label P'.semantic) :
      PhysicalStep V P (some label) P'

/-- Concrete Peritext datatype-state protocol. Validity is structural: invalid
materializations cannot inhabit `Physical`, so preservation is immediate. -/
def protocol (V : VirtualLCAResolver (D Γ)) : StateGCProtocol (D Γ) V where
  Physical := Physical Γ
  semantic := Physical.semantic
  Valid := fun _ => True
  PhysicalStep := PhysicalStep Γ V
  valid_preserved := by simp
  silent_stutters := by
    intro P P' _ step
    cases step with
    | collectText _ _ h _ => exact h
    | trimDeleted _ h _ => exact h
    | dropMarkPair _ _ _ h _ => exact h
    | reframe h => exact h
  visible_refines := by
    intro P P' label _ step
    cases step with
    | ordinary _ h => exact .base h
    | virtual _ h => exact h

/-- A silent physical trace, including independent cross-epoch reframing,
cannot change the semantic configuration. -/
theorem silent_semantic_eq {V : VirtualLCAResolver (D Γ)}
    {P P' : Physical Γ}
    (h : PhysicalStep Γ V P none P') : P'.semantic = P.semantic := by
  exact (protocol Γ V).silent_stutters True.intro h

/-- The generic direct-refinement theorem specialized to Sided Peritext. -/
theorem refines {V : VirtualLCAResolver (D Γ)} {P P' : Physical Γ} {labels}
    (run : StateGCProtocol.Steps (protocol Γ V) P labels P') :
    StateGCProtocol.SemanticSteps V P.semantic
      (StateGCProtocol.eraseLabels labels) P'.semantic :=
  StateGCProtocol.refines (protocol Γ V) True.intro run

#check merge_text_after_epoch_translation
#check collectText_query_preserved
#check collectedText_continuation_query
#check trimDeleted_query_preserved
#check dropMarkPair_query_preserved
#print axioms silent_semantic_eq
#print axioms refines

end

end Sal.MRDTs.Instances.SidedPeritext.StateGC.Protocol
