import Sal.MRDTs.Paper1.RestrictedReplay
import Sal.MRDTs.Instances.ProductionRGA
import Sal.MRDTs.Instances.FugueMaxReplay
import Sal.MRDTs.Instances.Peritext
import Sal.MRDTs.Instances.RGASequential
import Sal.MRDTs.Instances.SidedPeritext
import Sal.MRDTs.Instances.FugueMaxImplementation

/-! Exact raw commutation and an operation-only no-chain resolver cannot
coexist for the existing embedded sequence carriers. This is stronger than
failure of their particular production resolver. The witnesses are raw input
controls; they are deliberately not asserted to be honestly issuable. -/
namespace Sal.MRDTs.Paper1.RGA.EmbeddingObstructions
open Foundation
open Sal.EmbedRGA

/-- Noncommuting events with the same application label force a reflexive
policy edge. The no-chain condition excludes that edge. -/
theorem no_restricted_policy_of_same_label {D : UpdateSig}
    (a b : Op D.AppOp) (same : a.op = b.op) (bad : ¬ D.commutes a b) :
    ¬ ∃ P : OperationPolicy D.AppOp, RestrictedLaws D P := by
  rintro ⟨P,laws⟩
  have edge : P.before a.op a.op := by
    rcases (laws.noncomm_exact a b).mp bad with h | h
    · simpa [same] using h
    · simpa [same] using h
  exact laws.no_chain a.op a.op a.op ⟨edge,edge⟩

namespace Plain
open Sal.MRDTs.Instances.RGA

/-- The production sibling resolver has a chain on three ordinary root
insertions, although their concrete grow-only updates commute. -/
theorem production_chain_control :
    @UpdateSig.rc RGAM.toUpdateSig Sal.MRDTs.Instances.RGA.rc
      (1,0,.addAfter 0) (2,0,.addAfter 0) ∧
    @UpdateSig.rc RGAM.toUpdateSig Sal.MRDTs.Instances.RGA.rc
      (2,0,.addAfter 0) (3,0,.addAfter 0) ∧
    RGAM.toUpdateSig.commutes (1,0,.addAfter 0) (2,0,.addAfter 0) := by
  refine ⟨?_,?_,RGAM_all_comm _ _⟩ <;>
    simp [UpdateSig.rc, ReplayPolicy.Before, Sal.MRDTs.Instances.RGA.rc, rcOrder]

end Plain

namespace Embedded
open Sal.MRDTs.Instances.EmbedRGA
variable {α : Type} [DecidableEq α] [Inhabited α]

/-- Saturating subtraction makes two distinct timestamps write the same
coordinate. Stable tie insertion preserves opposite event orders. -/
theorem same_label_not_commute (Γ : OrderedPrefixCode) (el : α) :
    ¬ (E Γ α).toUpdateSig.commutes
      (1,0,.ins el [] 3) (2,0,.ins el [] 3) := by
  intro h
  have bad := h []
  simp [E, eUpdate, eInsert, eIds, keyLt_irrefl] at bad

theorem no_restricted_policy (Γ : OrderedPrefixCode) :
    ¬ ∃ P : OperationPolicy (EOp α), RestrictedLaws (E Γ α).toUpdateSig P :=
  no_restricted_policy_of_same_label
    (D := (E Γ α).toUpdateSig)
    (1,0,.ins (default : α) [] 3) (2,0,.ins (default : α) [] 3)
    rfl (same_label_not_commute Γ default)

/-- The actual production resolver has no chains, despite failing the exact
raw commutation restriction. -/
theorem production_no_chain (Γ : OrderedPrefixCode)
    (a b c : Op (EOp α)) :
    ¬ (@UpdateSig.rc (E Γ α).toUpdateSig (EReplayPolicy Γ) a b ∧
       @UpdateSig.rc (E Γ α).toUpdateSig (EReplayPolicy Γ) b c) := by
  obtain ⟨ats,ar,ao⟩ := a
  obtain ⟨bt,br,bo⟩ := b
  obtain ⟨ct,cr,co⟩ := c
  cases ao <;> cases bo <;> cases co <;>
    simp [UpdateSig.rc, ReplayPolicy.Before, EReplayPolicy, eRcOrder] <;>
      split_ifs <;> simp_all

end Embedded

namespace Sided
open Sal.MRDTs.Instances.SidedEmbedRGA

theorem same_label_not_commute (Γ : OrderedPrefixCode) :
    ¬ (S Γ).toUpdateSig.commutes
      (1,0,.ins 9 [] 3 .R) (2,0,.ins 9 [] 3 .R) := by
  intro h
  have bad := h []
  simp [S, sUpdate, sInsert, sIds, keyLt_irrefl] at bad

theorem no_restricted_policy (Γ : OrderedPrefixCode) :
    ¬ ∃ P : OperationPolicy SOp, RestrictedLaws (S Γ).toUpdateSig P :=
  no_restricted_policy_of_same_label
    (D := (S Γ).toUpdateSig)
    (1,0,.ins 9 [] 3 .R) (2,0,.ins 9 [] 3 .R)
    rfl (same_label_not_commute Γ)

theorem production_no_chain (Γ : OrderedPrefixCode) (a b c : Op SOp) :
    ¬ (@UpdateSig.rc (S Γ).toUpdateSig (SReplayPolicy Γ) a b ∧
       @UpdateSig.rc (S Γ).toUpdateSig (SReplayPolicy Γ) b c) := by
  obtain ⟨ats,ar,ao⟩ := a
  obtain ⟨bt,br,bo⟩ := b
  obtain ⟨ct,cr,co⟩ := c
  cases ao <;> cases bo <;> cases co <;>
    simp [UpdateSig.rc, ReplayPolicy.Before, SReplayPolicy, sRcOrder] <;>
      split_ifs <;> simp_all

end Sided

namespace FugueMax
open Sal.MRDTs.Instances.SidedEmbedRGA

/-- Here even subtraction is unnecessary: the full immutable coordinate
entry is in the application label, while the record ID is the timestamp. -/
theorem same_label_not_commute (Γ : OrderedPrefixCode) :
    ¬ (FMSig Γ).toUpdateSig.commutes
      (1,0,.ins 9 [] (.R [] 1)) (2,0,.ins 9 [] (.R [] 1)) := by
  intro h
  have bad := h []
  simp [FMSig, fUpdate, sInsert, sIds, keyLt_irrefl] at bad

theorem no_restricted_policy (Γ : OrderedPrefixCode) :
    ¬ ∃ P : OperationPolicy FOp, RestrictedLaws (FMSig Γ).toUpdateSig P :=
  no_restricted_policy_of_same_label
    (D := (FMSig Γ).toUpdateSig)
    (1,0,.ins 9 [] (.R [] 1)) (2,0,.ins 9 [] (.R [] 1))
    rfl (same_label_not_commute Γ)

theorem production_no_chain (Γ : OrderedPrefixCode) (a b c : Op FOp) :
    ¬ (@UpdateSig.rc (FMSig Γ).toUpdateSig (FMReplayPolicy Γ) a b ∧
       @UpdateSig.rc (FMSig Γ).toUpdateSig (FMReplayPolicy Γ) b c) := by
  obtain ⟨ats,ar,ao⟩ := a
  obtain ⟨bt,br,bo⟩ := b
  obtain ⟨ct,cr,co⟩ := c
  cases ao <;> cases bo <;> cases co <;>
    simp [UpdateSig.rc, ReplayPolicy.Before, FMReplayPolicy, fRcOrder] <;>
      split_ifs <;> simp_all

end FugueMax

theorem peritext_no_restricted_policy (Γ : OrderedPrefixCode) :
    ¬ ∃ P : OperationPolicy (Sal.MRDTs.Instances.Peritext.D Γ).AppOp,
      RestrictedLaws (Sal.MRDTs.Instances.Peritext.D Γ).toUpdateSig P :=
  Embedded.no_restricted_policy Γ

namespace SidedPeritext
open Sal.MRDTs.Instances.SidedEmbedRGA
open Sal.MRDTs.Instances.SidedPeritext

/-- Projection to the exact text component lifts the obstruction to the
production mixed core; the two evidence stores can remain initially empty. -/
theorem same_label_not_commute (Γ : OrderedPrefixCode) :
    ¬ (Core Γ).toUpdateSig.commutes
      (inlOp (A₂ := Nat ⊕ MarkEvent) (1,0,.ins 9 [] 3 .R))
      (inlOp (A₂ := Nat ⊕ MarkEvent) (2,0,.ins 9 [] 3 .R)) := by
  intro h
  exact Sided.same_label_not_commute Γ
    ((commutes_prod_inl_iff (D₁ := S Γ) (D₂ := Stores) _ _).mp h)

theorem core_no_restricted_policy (Γ : OrderedPrefixCode) :
    ¬ ∃ P : OperationPolicy (Core Γ).AppOp,
      RestrictedLaws (Core Γ).toUpdateSig P :=
  no_restricted_policy_of_same_label (D := (Core Γ).toUpdateSig)
    (inlOp (A₂ := Nat ⊕ MarkEvent) (1,0,.ins 9 [] 3 .R))
    (inlOp (A₂ := Nat ⊕ MarkEvent) (2,0,.ins 9 [] 3 .R))
    rfl (same_label_not_commute Γ)

/-- Narrowing the query to rendered rich text changes no update carrier,
so the exact same impossibility applies to the rich registry entry. -/
theorem rich_no_restricted_policy (Γ : OrderedPrefixCode) :
    ¬ ∃ P : OperationPolicy (RichCore Γ).AppOp,
      RestrictedLaws (RichCore Γ).toUpdateSig P :=
  core_no_restricted_policy Γ

end SidedPeritext

namespace RegisteredFugueMax
open Sal.MRDTs.Instances.SidedEmbedRGA
open Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax

def tiedPayload : Payload := ⟨.ins 0 .R,0,none,[]⟩

/-- This targets the actual registered datatype with issuer births, rather
than the auxiliary coordinate replay signature `FMSig`. -/
theorem same_label_not_commute (Γ : OrderedPrefixCode) :
    ¬ (datatype Γ).toUpdateSig.commutes
      (1,0,tiedPayload) (2,0,tiedPayload) := by
  intro h
  have bad := congrArg State.live (h (datatype Γ).init)
  simp [datatype, rawUpdate, recordOf, tiedPayload, mStep,
    sIds, sInsert, keyLt_irrefl] at bad

theorem no_restricted_policy (Γ : OrderedPrefixCode) :
    ¬ ∃ P : OperationPolicy Payload,
      RestrictedLaws (datatype Γ).toUpdateSig P :=
  no_restricted_policy_of_same_label (D := (datatype Γ).toUpdateSig)
    (1,0,tiedPayload) (2,0,tiedPayload)
    rfl (same_label_not_commute Γ)

end RegisteredFugueMax

#print axioms Embedded.no_restricted_policy
#print axioms Plain.production_chain_control
#print axioms Sided.no_restricted_policy
#print axioms FugueMax.no_restricted_policy
#print axioms peritext_no_restricted_policy
#print axioms SidedPeritext.core_no_restricted_policy
#print axioms SidedPeritext.rich_no_restricted_policy
#print axioms RegisteredFugueMax.no_restricted_policy
end Sal.MRDTs.Paper1.RGA.EmbeddingObstructions
