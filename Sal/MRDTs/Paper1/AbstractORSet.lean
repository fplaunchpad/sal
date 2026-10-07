import Sal.MRDTs.Paper1.AbstractCompatibility
import Sal.MRDTs.Paper1.AbstractMerge
import Sal.MRDTs.Paper1.AbstractSoundness
import Sal.MRDTs.Paper1.QueryExactORSet
import Sal.MRDTs.Paper1.QueryORSet

/-! Exact and efficient OR-set inhabit the explicit abstraction formalism.
Both use independent ordinary-set semantic states. Their representation
relations retain the metadata needed by merge and are proved to imply
abstract canonicality; neither uses an abstract merge operation. -/
namespace Sal.MRDTs.Paper1
open Foundation
open Classical

namespace ORSet.AbstractSpec
variable {α : Type} [DecidableEq α]

def model : AbstractMRDT.Model (D α) := AbstractMRDT.Model.ofQuery QuerySpec.abstraction

theorem laws : AbstractMRDT.Laws (model (α := α)) (conflict α) :=
  AbstractMRDT.Laws.ofQuery QuerySpec.laws

theorem compatibility : AbstractMRDT.SpecificationCompatibility (model (α := α)) (EventSpec.spec α) :=
  fun a b h => QuerySpec.specificationCompatibility a b
    ((AbstractMRDT.ofQuery_commutes QuerySpec.abstraction a b).mp h)

/-- Exact history-indexed tag evidence, stronger than equality of views. -/
def representation : AbstractMRDT.Representation (D α) :=
  fun C E s => @IsCanonicalState (D α).toUpdateSig (conflict α).lift C E s

theorem representsCanonical : AbstractMRDT.RepresentsCanonical (model (α := α))
    (conflict α) representation := by
  intro C E s h
  exact AbstractMRDT.canonical_ofQuery QuerySpec.laws C E s
    (QueryReplay.canonical_of_concrete restrictedLaws QuerySpec.laws C E s h)

theorem representationJoin : AbstractMRDT.RepresentationJoin (representation (α := α)) := by
  intro C E₁ E₂ l a b trans irrefl sup₁ sup₂ closed₁ closed₂ hl ha hb
  have hjoin : @JoinAt (D α) (conflict α).lift C := by
    rw [conflict_lift_eq]
    exact @Join.at (D α) policy join C
  exact hjoin E₁ E₂ l a b (fun {_ _ _} h k => trans h k) irrefl sup₁ sup₂
    (fun e f vis _ hf => closed₁ e f vis hf)
    (fun e f vis _ hf => closed₂ e f vis hf) hl ha hb

theorem representedVersions {C : Configuration (D α)}
    (reach : MintCertifiedReachV (D α) (canonicalVirtualMergeBase (D α)) (issuance α) C) :
    ∀ v s E, C.ver v = some (s,E) → representation C.replayContext E s := by
  letI : ReplayPolicy (D α).toUpdateSig := (conflict α).lift
  have hjoin : ∀ C, MintHonest (D α) (issuance α).CanIssue C →
      @JoinAt (D α) (conflict α).lift C.replayContext := by
    intro C _
    rw [conflict_lift_eq]
    exact @Join.at (D α) policy join C.replayContext
  exact (canonicalConfig_of_mintCertifiedV hjoin reach).canonical

theorem certifiedVersionsRAV {C : Configuration (D α)}
    (reach : MintCertifiedReachV (D α) (canonicalVirtualMergeBase (D α)) (issuance α) C) :
    AbstractMRDT.VersionsRALinearizable (model (α := α)) (conflict α) (EventSpec.spec α) C :=
  AbstractMRDT.of_representation laws (representedVersions reach)
    representsCanonical compatibility EventSpec.foldHistorySound

theorem certifiedVersionsRA {C : Configuration (D α)}
    (reach : MintCertifiedReach (D α) (issuance α) C) :
    AbstractMRDT.VersionsRALinearizable (model (α := α)) (conflict α) (EventSpec.spec α) C :=
  certifiedVersionsRAV reach.toV

def certificate : AbstractMRDT.Certificate (model (α := α)) (conflict α)
    (EventSpec.spec α) (issuance α) where
  queryComplete := AbstractMRDT.ofQuery_complete QuerySpec.abstraction
  laws := laws
  representation := representation
  representsCanonical := representsCanonical
  representationJoin := representationJoin
  representedVersions _ := representedVersions
  compatibility := compatibility
  historySound := EventSpec.foldHistorySound

end ORSet.AbstractSpec

namespace EfficientORSet.AbstractSpec
open Sal.MRDTs.Instances.EfficientORSet
variable {α : Type} [DecidableEq α]
local instance : ReplayPolicy (D α).toUpdateSig := rc

def model : AbstractMRDT.Model (D α) := AbstractMRDT.Model.ofQuery QuerySpec.abstraction

theorem laws : AbstractMRDT.Laws (model (α := α)) (EventSpec.conflict α) :=
  AbstractMRDT.Laws.ofQuery QuerySpec.laws

theorem compatibility : AbstractMRDT.SpecificationCompatibility (model (α := α)) (EventSpec.spec α) :=
  fun a b h => QuerySpec.specificationCompatibility a b
    ((AbstractMRDT.ofQuery_commutes QuerySpec.abstraction a b).mp h)

def representation : AbstractMRDT.Representation (D α) := fun C E s =>
  Represents C.vis E s ∧ (∃ π : List (Event α), listPermOf π E) ∧
  (∀ e ∈ E, e ∈ C.events) ∧ Transitive C.vis ∧
  (∀ a b, C.vis a b → a.time < b.time)

private theorem replica_total (C : ReplayContext (D α).toUpdateSig) (E : Set (Event α))
    (supported : ∀ e ∈ E, e ∈ C.events) :
    ∀ a ∈ E, ∀ b ∈ E, a ≠ b → a.2.1 = b.2.1 → C.vis a b ∨ C.vis b a := by
  intro a ha b hb hne hr
  obtain ⟨r,er,hhead,hea⟩ := supported a ha
  obtain ⟨r',er',hhead',heb⟩ := supported b hb
  exact C.vis_total_same_replica hhead hea hhead' heb hne hr

theorem representsCanonical : AbstractMRDT.RepresentsCanonical (model (α := α))
    (EventSpec.conflict α) representation := by
  intro C E s h
  obtain ⟨π,hp⟩ := h.2.1
  have concrete := canonical_of_represents C E h.2.2.2.1 h.2.2.2.2
    (replica_total C E h.2.2.1) π hp h.1
  exact AbstractMRDT.canonical_ofQuery QuerySpec.laws C E s
    (QuerySpec.canonical_of_representation C E s concrete h.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)

theorem representationJoin : AbstractMRDT.RepresentationJoin (representation (α := α)) := by
  intro C E₁ E₂ l a b trans irrefl sup₁ sup₂ closed₁ closed₂ hl ha hb
  have rep := represents_merge C.vis E₁ E₂ closed₁ closed₂ hl.1 ha.1 hb.1
  have supported : ∀ e ∈ E₁ ∪ E₂, e ∈ C.events := by
    intro e he
    exact he.elim (sup₁ e) (sup₂ e)
  obtain ⟨π₁,hp₁⟩ := ha.2.1
  obtain ⟨π₂,hp₂⟩ := hb.2.1
  have perm : listPermOf (π₁ ++ π₂).dedup (E₁ ∪ E₂) :=
    ⟨List.nodup_dedup _,fun e => by simp [hp₁.2 e,hp₂.2 e]⟩
  exact ⟨rep,⟨_,perm⟩,supported,trans,ha.2.2.2.2⟩

theorem representedVersions {C : Configuration (D α)}
    (reach : MintCertifiedReachV (D α) (canonicalVirtualMergeBase (D α)) issuance C) :
    ∀ v s E, C.ver v = some (s,E) → representation C.replayContext E s := by
  obtain ⟨_,good,represented⟩ := represented_of_mintCertifiedV reach
  intro v s E hv
  obtain ⟨π,hp,_⟩ := good.canonical v s E hv
  exact ⟨represented v s E hv,⟨π,hp⟩,
    good.version_events_supported v s E hv,
    (fun _ _ _ hab hbc => good.vis_trans hab hbc),(fun _ _ h => C.causal_mono h)⟩

theorem certifiedVersionsRAV {C : Configuration (D α)}
    (reach : MintCertifiedReachV (D α) (canonicalVirtualMergeBase (D α)) issuance C) :
    AbstractMRDT.VersionsRALinearizable (model (α := α))
      (EventSpec.conflict α) (EventSpec.spec α) C :=
  AbstractMRDT.of_representation laws (representedVersions reach)
    representsCanonical compatibility EventSpec.foldHistorySound

theorem certifiedVersionsRA {C : Configuration (D α)}
    (reach : MintCertifiedReach (D α) issuance C) :
    AbstractMRDT.VersionsRALinearizable (model (α := α))
      (EventSpec.conflict α) (EventSpec.spec α) C :=
  certifiedVersionsRAV reach.toV

def certificate : AbstractMRDT.Certificate (model (α := α)) (EventSpec.conflict α)
    (EventSpec.spec α) issuance where
  queryComplete := AbstractMRDT.ofQuery_complete QuerySpec.abstraction
  laws := laws
  representation := representation
  representsCanonical := representsCanonical
  representationJoin := representationJoin
  representedVersions _ := representedVersions
  compatibility := compatibility
  historySound := EventSpec.foldHistorySound

end EfficientORSet.AbstractSpec
end Sal.MRDTs.Paper1
