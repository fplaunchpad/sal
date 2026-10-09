import Sal.MRDTs.Paper1.Automation.GenericTaggedPrefixCodes
import Sal.MRDTs.Paper1.Automation.OrderedInputDerivation
import Sal.MRDTs.Paper1.Automation.OrderedKitAutomation
import Sal.MRDTs.Paper1.Automation.CommonVerification
import Sal.MRDTs.Paper1.CertifiedRGAVCReplay
import Mathlib.Tactic
import Sal.MRDTs.Paper1.Automation.GenericOrderedRecords
import Sal.MRDTs.Paper1.Automation.OrderedRecordAutomation

/-! Finite raw obligations for ordered immutable records. The supplied list
primitives are membership, sorted insertion, sorted merge, and sorted-list
extensionality; they are explicitly counted helper lemmas, not replay adapters.
No datatype history induction or old datatype correctness proof is used. -/
namespace Sal.MRDTs.Paper1.Automation.AutomatedRGA
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.EmbedRGA

private theorem id_mem {R : Type} (id : R → Nat) {s t : List R} {p : R}
    (hp : p ∈ s) (coherent : ∀ x ∈ s, ∀ y ∈ t, id x = id y → x = y) :
    id p ∈ t.map id ↔ p ∈ t := by
  constructor
  · intro h
    obtain ⟨q,hq,equal⟩ := List.mem_map.mp h
    exact coherent p hp q hq equal.symm ▸ hq
  · intro h; exact List.mem_map.mpr ⟨p,h,rfl⟩

namespace Embedded
open Instances.EmbedRGA
variable {α : Type} [DecidableEq α] [Inhabited α]
def Born (Γ : OrderedPrefixCode) (e : Op (EOp α)) (p : ERec α) :=
  eIsIns e = true ∧ p = eRecOf Γ e
def Kill (e : Op (EOp α)) (p : ERec α) := e.2.2 = .del p.1

theorem provenance_step (Γ : OrderedPrefixCode) (s : EState α)
    (e : Op (EOp α)) (p : ERec α) :
    p ∈ eUpdate Γ s e → Born Γ e p ∨ p ∈ s := by
  rcases e with ⟨t,r,op⟩
  cases op <;> simp only [eUpdate]
  · split <;> simp_all [Born,eIsIns,eRecOf,eCoord]
    all_goals (ordered_record_simp; tauto)
  · simp only [List.mem_filter]; tauto

theorem membership_step (Γ : OrderedPrefixCode) (s : EState α)
    (e : Op (EOp α)) (fresh : ∀ p ∈ s, p.1 ≠ e.1) (p : ERec α) :
    p ∈ eUpdate Γ s e ↔ Born Γ e p ∨ (p ∈ s ∧ ¬Kill e p) := by
  have absent : e.1 ∉ eIds s := by
    intro h; obtain ⟨p,hp,id⟩ := List.mem_map.mp h; exact fresh p hp id
  rcases e with ⟨t,r,op⟩
  cases op <;> simp [eUpdate,absent,Born,Kill,eIsIns,eRecOf,eCoord]
  all_goals (ordered_record_simp; grind)

theorem ordered_step (Γ : OrderedPrefixCode) (s : EState α) (e : Op (EOp α))
    (ordered : ESorted s)
    (keys : ∀ p ∈ s, eIsIns e = true → key p.2.2 ≠ key (eRecOf Γ e).2.2) :
    ESorted (eUpdate Γ s e) := by
  rcases e with ⟨t,r,op⟩
  cases op with
  | ins el pref anchor =>
    simp only [eUpdate]
    split
    · exact ordered
    · ordered_record
  | del target => exact List.Pairwise.filter _ ordered

theorem merge_cell (l a b : EState α)
    (al : ∀ x ∈ a, ∀ y ∈ l, x.1 = y.1 → x = y)
    (bl : ∀ x ∈ b, ∀ y ∈ l, x.1 = y.1 → x = y)
    (ab : ∀ x ∈ a, ∀ y ∈ b, x.1 = y.1 → x = y)
    (ba : ∀ x ∈ b, ∀ y ∈ a, x.1 = y.1 → x = y) (p : ERec α) :
    p ∈ eMerge l a b ↔ (p ∈ l ∧ p ∈ a ∧ p ∈ b) ∨
      (p ∈ a ∧ p ∉ l) ∨ (p ∈ b ∧ p ∉ l) := by
  have al' := fun h : p ∈ a => id_mem Prod.fst h al
  have bl' := fun h : p ∈ b => id_mem Prod.fst h bl
  have ab' := fun h : p ∈ a => id_mem Prod.fst h ab
  have ba' := fun h : p ∈ b => id_mem Prod.fst h ba
  simp only [eMerge]
  ordered_record_simp
  tauto
end Embedded

namespace Sided
open Instances.SidedEmbedRGA
def Born (Γ : OrderedPrefixCode) (e : Op SOp) (p : SRec) :=
  sIsIns e = true ∧ p = sRecOf Γ e
def Kill (e : Op SOp) (p : SRec) := e.2.2 = .del p.1

theorem provenance_step (Γ : OrderedPrefixCode) (s : SState) (e : Op SOp) (p : SRec) :
    p ∈ sUpdate Γ s e → Born Γ e p ∨ p ∈ s := by
  rcases e with ⟨t,r,op⟩
  cases op <;> simp only [sUpdate]
  · split <;> simp_all [Born,sIsIns,sRecOf,sCoord]
    all_goals (ordered_record_simp; tauto)
  · simp only [List.mem_filter]; tauto

theorem membership_step (Γ : OrderedPrefixCode) (s : SState)
    (e : Op SOp) (fresh : ∀ p ∈ s, p.1 ≠ e.1) (p : SRec) :
    p ∈ sUpdate Γ s e ↔ Born Γ e p ∨ (p ∈ s ∧ ¬Kill e p) := by
  have absent : e.1 ∉ sIds s := by
    intro h; obtain ⟨p,hp,id⟩ := List.mem_map.mp h; exact fresh p hp id
  rcases e with ⟨t,r,op⟩
  cases op <;> simp [sUpdate,absent,Born,Kill,sIsIns,sRecOf,sCoord]
  all_goals (ordered_record_simp; grind)

theorem ordered_step (Γ : OrderedPrefixCode) (s : SState) (e : Op SOp)
    (ordered : SSorted s)
    (keys : ∀ p ∈ s, sIsIns e = true → sKey p.2.2 ≠ sKey (sRecOf Γ e).2.2) :
    SSorted (sUpdate Γ s e) := by
  rcases e with ⟨t,r,op⟩
  cases op with
  | ins el pref anchor side =>
    simp only [sUpdate]
    split
    · exact ordered
    · ordered_record
  | del target => exact List.Pairwise.filter _ ordered

theorem merge_cell (l a b : SState)
    (al : ∀ x ∈ a, ∀ y ∈ l, x.1 = y.1 → x = y)
    (bl : ∀ x ∈ b, ∀ y ∈ l, x.1 = y.1 → x = y)
    (ab : ∀ x ∈ a, ∀ y ∈ b, x.1 = y.1 → x = y)
    (ba : ∀ x ∈ b, ∀ y ∈ a, x.1 = y.1 → x = y) (p : SRec) :
    p ∈ sMerge l a b ↔ (p ∈ l ∧ p ∈ a ∧ p ∈ b) ∨
      (p ∈ a ∧ p ∉ l) ∨ (p ∈ b ∧ p ∉ l) := by
  have al' := fun h : p ∈ a => id_mem Prod.fst h al
  have bl' := fun h : p ∈ b => id_mem Prod.fst h bl
  have ab' := fun h : p ∈ a => id_mem Prod.fst h ab
  have ba' := fun h : p ∈ b => id_mem Prod.fst h ba
  simp only [sMerge]
  ordered_record_simp
  tauto
end Sided
end Sal.MRDTs.Paper1.Automation.AutomatedRGA

namespace Sal.MRDTs.Paper1.Automation.AutomatedRGA.Embedded
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.EmbedRGA
open Instances.EmbedRGA
open Sal.MRDTs.Paper1.Automation.OrderedRecords
variable {α : Type} [DecidableEq α] [Inhabited α]
/-- The author supplies only the implementation's finite data projections. -/
def description (Γ : OrderedPrefixCode) : Description (E Γ α) (ERec α) where
  carrier := List.toFinset
  id := Prod.fst
  Key := List Nat
  key := fun p => key p.2.2
  insertion := eIsIns
  written := eRecOf Γ
  target := fun e n => e.2.2 = .del n
  ordered := ESorted

def kit (Γ : OrderedPrefixCode) : Kit (E Γ α) (ERec α) := by
  derive_ordered_kit (description Γ) unfolding
    [description, E, eUpdate, eIds, eIsIns, eRecOf, eCoord, ESorted, eMerge]

/-- Chain and key data specialize the generic prefix-code decoder. -/
def chainMapping (Γ : OrderedPrefixCode) : ChainMapping (List Nat) (List Bool) (List Nat) where
  valid := PosChain
  coordinate := coordOf Γ
  key := key
  stamp := List.sum
  injective := by
    intro a b va vb equal
    have symbols : Function.Injective (fun b : Bool => if b then (2 : Nat) else 1) := by
      intro x y; cases x <;> cases y <;> simp
    have coordinates := PrefixCodes.map_suffix_injective _ symbols [3] equal
    have code : PrefixCodes.Code (fun d : Nat => 1 ≤ d) Γ.enc := {
      nonempty := PrefixCodes.nonempty_of_prefixFree _ _
        (fun _ _ hd he ne => Γ.prefixFree hd he ne)
        (by intro d hd; exact ⟨d + 1, by omega, by omega⟩)
      prefixFree := fun _ _ hd he ne => Γ.prefixFree hd he ne }
    have equations := PrefixCodes.encode_eq Γ.enc (coordOf Γ) rfl (by intros; rfl)
    exact PrefixCodes.encode_injective code a b va vb
      (by simpa only [equations] using coordinates)

def issuer (Γ : OrderedPrefixCode) (C : ReplayContext (E Γ α).toUpdateSig)
    (honest : EHonestCore Γ C) : IssuerEvidence (kit Γ) C := by
  derive_ordered_issuer (chainMapping Γ) at (eCoord Γ)
    using honest.del_has_ins, honest.chain_gen
end Sal.MRDTs.Paper1.Automation.AutomatedRGA.Embedded

namespace Sal.MRDTs.Paper1.Automation.AutomatedRGA.Sided
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.EmbedRGA
open Instances.SidedEmbedRGA
open Sal.MRDTs.Paper1.Automation.OrderedRecords
def description (Γ : OrderedPrefixCode) : Description (S Γ) SRec where
  carrier := List.toFinset
  id := Prod.fst
  Key := List Nat
  key := fun p => sKey p.2.2
  insertion := sIsIns
  written := sRecOf Γ
  target := fun e n => e.2.2 = .del n
  ordered := SSorted

def kit (Γ : OrderedPrefixCode) : Kit (S Γ) (SRec) := by
  derive_ordered_kit (description Γ) unfolding
    [description, S, sUpdate, sIds, sIsIns, sRecOf, sCoord, SSorted, sMerge]

def chainMapping (Γ : OrderedPrefixCode) : ChainMapping SChain (List Nat) (List Nat) where
  valid := PosSChain
  coordinate := sidedCoordOf Γ
  key := sKey
  stamp := fun c => (c.map Prod.snd).sum
  injective := by
    intro a b va vb equal
    have coordinates : sidedCoordOf Γ a = sidedCoordOf Γ b :=
      List.append_inj_left' equal (by simp)
    have code : PrefixCodes.Code (fun d : Nat => 1 ≤ d) Γ.enc := {
      nonempty := PrefixCodes.nonempty_of_prefixFree _ _
        (fun _ _ hd he ne => Γ.prefixFree hd he ne)
        (by intro d hd; exact ⟨d + 1, by omega, by omega⟩)
      prefixFree := fun _ _ hd he ne => Γ.prefixFree hd he ne }
    let symbol : Side → Bool → Nat := fun sd bit =>
      match sd with | .R => symR bit | .L => symL (!bit)
    have tagged := code.tagged symbol
      (by intro sd x y; cases sd <;> cases x <;> cases y <;> simp [symbol, symR, symL])
      (by intro sd td ne x y; cases sd <;> cases td <;> cases x <;> cases y <;>
          simp_all [symbol, symR, symL])
    have equations := PrefixCodes.encode_eq (fun e : SEntry => (Γ.enc e.2).map (symbol e.1))
      (sidedCoordOf Γ) rfl (by
        rintro ⟨sd,d⟩ ts; cases sd <;> simp [sidedCoordOf,sBlock,Sal.EmbedRGA.compl,symbol,List.map_map])
    exact PrefixCodes.encode_injective tagged a b va vb
      (by simpa only [equations] using coordinates)

def issuer (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (honest : SHonestCore Γ C) : IssuerEvidence (kit Γ) C := by
  derive_ordered_issuer (chainMapping Γ) at (sCoord Γ)
    using honest.del_has_ins, honest.chain_gen

end Sal.MRDTs.Paper1.Automation.AutomatedRGA.Sided

namespace Sal.MRDTs.Paper1.Automation.AutomatedRGA.Embedded
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.EmbedRGA
open Instances.EmbedRGA Sal.MRDTs.Paper1.Automation.OrderedRecords
variable {α : Type} [DecidableEq α] [Inhabited α]
theorem adapter (Γ : OrderedPrefixCode) (C : ReplayContext (E Γ α).toUpdateSig)
    (H : Set (Op (E Γ α).AppOp)) (s : (E Γ α).State)
    (rep : CertifiedRGAVCReplay.Embedded.representation (α := α) Γ C H s) :
    IssuerEvidence (kit Γ) C ∧ ReplayEvidence C H s :=
  by derive_ordered_adapter rep with (issuer Γ C) unfolding [CertifiedRGAVCReplay.Embedded.representation, eFold, E]

def input (Γ : OrderedPrefixCode) : Sal.MRDTs.Paper1.Automation.CommonVerification.Input (E Γ α)
    CertifiedRGAVCReplay.Embedded.policy (CertifiedRGAVCReplay.Embedded.representation (α := α) Γ) (CertifiedRGAVCReplay.Embedded.scheme Γ) :=
  by derive_ordered_input (kit Γ) with (issuer Γ) unfolding [CertifiedRGAVCReplay.Embedded.representation, eFold, E]
register_mrdt_input input

theorem automated_vcs (Γ : OrderedPrefixCode) : ConcreteMRDT.Raw.MergeVCs
    CertifiedRGAVCReplay.Embedded.policy (CertifiedRGAVCReplay.Embedded.representation (α := α) Γ) (CertifiedRGAVCReplay.Embedded.scheme Γ) := by
  mrdt_verify using input Γ

#print axioms automated_vcs
end Sal.MRDTs.Paper1.Automation.AutomatedRGA.Embedded

namespace Sal.MRDTs.Paper1.Automation.AutomatedRGA.Sided
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.EmbedRGA
open Instances.SidedEmbedRGA Sal.MRDTs.Paper1.Automation.OrderedRecords
theorem adapter (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (H : Set (Op (S Γ).AppOp)) (s : (S Γ).State)
    (rep : CertifiedRGAVCReplay.Sided.representation Γ C H s) :
    IssuerEvidence (kit Γ) C ∧ ReplayEvidence C H s :=
  by derive_ordered_adapter rep with (issuer Γ C) unfolding [CertifiedRGAVCReplay.Sided.representation, sFold, S]

def input (Γ : OrderedPrefixCode) : Sal.MRDTs.Paper1.Automation.CommonVerification.Input (S Γ)
    CertifiedRGAVCReplay.Sided.policy (CertifiedRGAVCReplay.Sided.representation Γ) (CertifiedRGAVCReplay.Sided.scheme Γ) :=
  by derive_ordered_input (kit Γ) with (issuer Γ) unfolding [CertifiedRGAVCReplay.Sided.representation, sFold, S]
register_mrdt_input input

theorem automated_vcs (Γ : OrderedPrefixCode) : ConcreteMRDT.Raw.MergeVCs
    CertifiedRGAVCReplay.Sided.policy (CertifiedRGAVCReplay.Sided.representation Γ) (CertifiedRGAVCReplay.Sided.scheme Γ) := by
  mrdt_verify using input Γ

#print axioms automated_vcs
end Sal.MRDTs.Paper1.Automation.AutomatedRGA.Sided
