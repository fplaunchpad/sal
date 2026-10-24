import Sal.MRDTs.Instances.NotionCoreRichProtocolCarrier
import Sal.MRDTs.Framework.FiniteEvents
import Sal.MRDTs.Framework.Base.FiniteOrder

/-! Raw finite Sal executions have the permissive carrier certificate. This
supplies the five-VC storage invariant; actual source issuance remains the
separate ordinary/factory protocol, never a consequence of the True guard. -/
namespace Sal.MRDTs.Instances.NotionCoreRichProtocolExecution
open Sal.MRDTs Sal.MRDTs.Foundation
open NotionCoreRichProtocolCarrier (D issuance)

theorem finite_mint_honest (config : Configuration D) (finite : config.events.Finite) :
    MintHonest D issuance.CanIssue config := by
  classical
  intro event _member
  let past : Set (Op D.AppOp) := {old ∈ config.events | config.vis old event}
  have finitePast : past.Finite := finite.subset (fun _ member => member.1)
  let enumeration := finitePast.toFinset.toList
  have enumerates : listPermOf enumeration past := by
    constructor
    · exact Finset.nodup_toList _
    · intro old
      simp [enumeration]
  obtain ⟨ordered, permutation, order⟩ := exists_respecting_perm
    (R := fun a b : Op D.AppOp => a.time < b.time)
    (fun ab bc => Nat.lt_trans ab bc) (fun a => Nat.lt_irrefl a.time) enumeration
  refine ⟨ordered, ?_, ?_, True.intro⟩
  · exact ⟨permutation.nodup_iff.mp enumerates.1,
      fun old => (permutation.mem_iff.symm).trans (enumerates.2 old)⟩
  · exact order.imp (fun {_ _} before edge => before (config.causal_mono edge))

theorem raw_issued {config next : Configuration D} {label : Label D}
    (step : Step D config label next) : IssuedStep D issuance config label next := by
  cases step with
  | fork fresh sourceHead sourceVersion freshVersion rank next vis store heads parents =>
    exact .nonApply (.fork fresh sourceHead sourceVersion freshVersion rank next vis store heads parents)
      (by intros; simp)
  | apply headAt versionAt freshTime freshStore freshVersion rank next vis store heads parents =>
    exact .apply headAt (congrArg (Option.map Prod.fst) versionAt) True.intro
      (.apply headAt versionAt freshTime freshStore freshVersion rank next vis store heads parents)
  | merge targetHead sourceHead targetVersion sourceVersion gca baseVersion freshVersion rank₁ rank₂ next vis store heads parents =>
    exact .nonApply (.merge targetHead sourceHead targetVersion sourceVersion gca baseVersion
      freshVersion rank₁ rank₂ next vis store heads parents) (by intros; simp)
  | query headAt versionAt =>
    exact .nonApply (.query headAt versionAt) (by intros; simp)

theorem raw_issuedV {config next : Configuration D} {label : Label D}
    (step : StepV D (canonicalVirtualMergeBase D) config label next) :
    IssuedStepV D (canonicalVirtualMergeBase D) issuance config label next := by
  classical
  by_cases ordinary : Step D config label next
  · exact .base (raw_issued ordinary)
  · exact .virtual step ordinary

theorem certify {config : Configuration D}
    (reachable : (labeledTSV D (canonicalVirtualMergeBase D)).ReachableFrom (initConfig D) config) :
    MintCertifiedReachV D (canonicalVirtualMergeBase D) issuance config := by
  induction reachable with
  | refl => exact .init
  | @tail next final before one ih =>
    obtain ⟨label, step⟩ := one
    have finite := ih.events_finite
    exact .step ih (finite_mint_honest next finite) (raw_issuedV step)
      (finite_mint_honest final (step.events_finite finite))

#print axioms finite_mint_honest
#print axioms certify
end Sal.MRDTs.Instances.NotionCoreRichProtocolExecution
