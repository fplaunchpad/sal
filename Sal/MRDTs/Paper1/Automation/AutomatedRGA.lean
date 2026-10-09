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
def kit (Γ : OrderedPrefixCode) : Kit (E Γ α) (ERec α) where
  carrier := List.toFinset
  id := Prod.fst
  Key := List Nat
  key := fun p => key p.2.2
  insertion := eIsIns
  written := eRecOf Γ
  target := fun e n => e.2.2 = .del n
  ordered := ESorted
  init_carrier := rfl
  init_ordered := List.Pairwise.nil
  written_id := fun _ => rfl
  update_provenance := by
    intro s e p hp
    simpa only [List.mem_toFinset,Born] using provenance_step Γ s e p (List.mem_toFinset.mp hp)
  update_mem := by
    intro s e fresh p
    simpa only [List.mem_toFinset,Born,Kill] using membership_step Γ s e
      (fun p hp => fresh p (List.mem_toFinset.mpr hp)) p
  update_ordered := by
    intro s e hs keys
    exact ordered_step Γ s e hs (fun p hp => keys p (List.mem_toFinset.mpr hp))
  birth_not_killed := by
    rintro ⟨t,r,op⟩ ins
    cases op <;> simp_all [eIsIns]
  merge_mem := by
    intro l a b al bl ab ba p
    simpa only [List.mem_toFinset,Certified.cell] using merge_cell l a b
      (fun p hp q hq => al p (List.mem_toFinset.mpr hp) q (List.mem_toFinset.mpr hq))
      (fun p hp q hq => bl p (List.mem_toFinset.mpr hp) q (List.mem_toFinset.mpr hq))
      (fun p hp q hq => ab p (List.mem_toFinset.mpr hp) q (List.mem_toFinset.mpr hq))
      (fun p hp q hq => ba p (List.mem_toFinset.mpr hp) q (List.mem_toFinset.mpr hq)) p
  merge_ordered := by
    intro l a b ha hb coherent
    change ESorted (eMerge l a b)
    ordered_record
  ext := by
    intro s t hs ht same
    change @Eq (EState α) s t
    ordered_record

def issuer (Γ : OrderedPrefixCode) (C : ReplayContext (E Γ α).toUpdateSig)
    (honest : EHonestCore Γ C) : IssuerEvidence (kit Γ) C := by
  refine ⟨?_,?_⟩
  · intro d hd n target
    obtain ⟨a,ha,vis,time,ins⟩ := honest.del_has_ins d hd n target
    exact ⟨a,ha,vis,ins,time⟩
  · obtain ⟨chainOf,generated⟩ := honest.chain_gen
    apply ChainCertificate.key_unique (Chain := List Nat)
    refine ⟨PosChain,fun c => key (coordOf Γ c),fun c => c.sum,?_,?_⟩
    · intro a b va vb equal
      exact coordOf_inj Γ va vb (key_inj equal)
    · intro e he ins
      obtain ⟨valid,shape,sum⟩ := generated e he ins
      refine ⟨chainOf e.1,valid,?_,sum⟩
      change key (eRecOf Γ e).2.2 = _
      have written : (eRecOf Γ e).2.2 = eCoord Γ e := by
        rcases e with ⟨t,r,op⟩
        cases op <;> simp_all [eIsIns,eRecOf,eCoord]
      rw [written,shape]
end Sal.MRDTs.Paper1.Automation.AutomatedRGA.Embedded

namespace Sal.MRDTs.Paper1.Automation.AutomatedRGA.Sided
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.EmbedRGA
open Instances.SidedEmbedRGA
open Sal.MRDTs.Paper1.Automation.OrderedRecords
def kit (Γ : OrderedPrefixCode) : Kit (S Γ) (SRec) where
  carrier := List.toFinset
  id := Prod.fst
  Key := List Nat
  key := fun p => sKey p.2.2
  insertion := sIsIns
  written := sRecOf Γ
  target := fun e n => e.2.2 = .del n
  ordered := SSorted
  init_carrier := rfl
  init_ordered := List.Pairwise.nil
  written_id := fun _ => rfl
  update_provenance := by
    intro s e p hp
    simpa only [List.mem_toFinset,Born] using provenance_step Γ s e p (List.mem_toFinset.mp hp)
  update_mem := by
    intro s e fresh p
    simpa only [List.mem_toFinset,Born,Kill] using membership_step Γ s e
      (fun p hp => fresh p (List.mem_toFinset.mpr hp)) p
  update_ordered := by
    intro s e hs keys
    exact ordered_step Γ s e hs (fun p hp => keys p (List.mem_toFinset.mpr hp))
  birth_not_killed := by
    rintro ⟨t,r,op⟩ ins
    cases op <;> simp_all [sIsIns]
  merge_mem := by
    intro l a b al bl ab ba p
    simpa only [List.mem_toFinset,Certified.cell] using merge_cell l a b
      (fun p hp q hq => al p (List.mem_toFinset.mpr hp) q (List.mem_toFinset.mpr hq))
      (fun p hp q hq => bl p (List.mem_toFinset.mpr hp) q (List.mem_toFinset.mpr hq))
      (fun p hp q hq => ab p (List.mem_toFinset.mpr hp) q (List.mem_toFinset.mpr hq))
      (fun p hp q hq => ba p (List.mem_toFinset.mpr hp) q (List.mem_toFinset.mpr hq)) p
  merge_ordered := by
    intro l a b ha hb coherent
    change SSorted (sMerge l a b)
    ordered_record
  ext := by
    intro s t hs ht same
    change @Eq (SState) s t
    ordered_record

def issuer (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (honest : SHonestCore Γ C) : IssuerEvidence (kit Γ) C := by
  refine ⟨?_,?_⟩
  · intro d hd n target
    obtain ⟨a,ha,vis,time,ins⟩ := honest.del_has_ins d hd n target
    exact ⟨a,ha,vis,ins,time⟩
  · obtain ⟨chainOf,generated⟩ := honest.chain_gen
    apply ChainCertificate.key_unique (Chain := SChain)
    refine ⟨PosSChain,fun c => sKey (sidedCoordOf Γ c),fun c => (c.map Prod.snd).sum,?_,?_⟩
    · intro a b va vb equal
      exact sidedCoordOf_inj Γ va vb (sKey_inj equal)
    · intro e he ins
      obtain ⟨valid,shape,sum⟩ := generated e he ins
      refine ⟨chainOf e.1,valid,?_,sum⟩
      change sKey (sRecOf Γ e).2.2 = _
      have written : (sRecOf Γ e).2.2 = sCoord Γ e := by
        rcases e with ⟨t,r,op⟩
        cases op <;> simp_all [sIsIns,sRecOf,sCoord]
      rw [written,shape]
end Sal.MRDTs.Paper1.Automation.AutomatedRGA.Sided

namespace Sal.MRDTs.Paper1.Automation.AutomatedRGA.Embedded
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.EmbedRGA
open Instances.EmbedRGA Sal.MRDTs.Paper1.Automation.OrderedRecords
variable {α : Type} [DecidableEq α] [Inhabited α]
theorem adapter (Γ : OrderedPrefixCode) (C : ReplayContext (E Γ α).toUpdateSig)
    (H : Set (Op (E Γ α).AppOp)) (s : (E Γ α).State)
    (rep : CertifiedRGAVCReplay.Embedded.representation (α := α) Γ C H s) :
    IssuerEvidence (kit Γ) C ∧ ReplayEvidence C H s :=
  ⟨issuer Γ C rep.1,rep.2.2.2.1,rep.2.2.2.2⟩

def input (Γ : OrderedPrefixCode) : Sal.MRDTs.Paper1.Automation.CommonVerification.Input (E Γ α)
    CertifiedRGAVCReplay.Embedded.policy (CertifiedRGAVCReplay.Embedded.representation (α := α) Γ) (CertifiedRGAVCReplay.Embedded.scheme Γ) :=
  .ordered (kit Γ) (fun _ _ _ => Iff.rfl) (adapter Γ)
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
  ⟨issuer Γ C rep.1,rep.2.2.2.1,rep.2.2.2.2⟩

def input (Γ : OrderedPrefixCode) : Sal.MRDTs.Paper1.Automation.CommonVerification.Input (S Γ)
    CertifiedRGAVCReplay.Sided.policy (CertifiedRGAVCReplay.Sided.representation Γ) (CertifiedRGAVCReplay.Sided.scheme Γ) :=
  .ordered (kit Γ) (fun _ _ _ => Iff.rfl) (adapter Γ)
register_mrdt_input input

theorem automated_vcs (Γ : OrderedPrefixCode) : ConcreteMRDT.Raw.MergeVCs
    CertifiedRGAVCReplay.Sided.policy (CertifiedRGAVCReplay.Sided.representation Γ) (CertifiedRGAVCReplay.Sided.scheme Γ) := by
  mrdt_verify using input Γ

#print axioms automated_vcs
end Sal.MRDTs.Paper1.Automation.AutomatedRGA.Sided
