import Sal.MRDTs.Paper1.CertifiedFugueVCReplay
import Sal.MRDTs.Paper1.CertifiedRGASidedVCAlgebra

namespace Sal.MRDTs.Paper1.CertifiedFugueVCAlgebra
open Foundation Sal.EmbedRGA
open Instances.SidedEmbedRGA Instances.SidedEmbedRGA.FugueMax
open CertifiedFugueVCReplay
attribute [local instance] Instances.SidedEmbedRGA.FugueMax.rc

theorem membership (Γ : OrderedPrefixCode) (C : ReplayContext (datatype Γ).toUpdateSig)
    (H : Set (Op Payload)) (s : State) (rep : representation Γ C H s) (p : SRec) :
    p ∈ s.live ↔ (∃ e ∈ H, mIsIns (recordOf e) = true ∧ p = written Γ e) ∧
      ∀ d ∈ H, d.2.2.op ≠ .del p.1 := by
  obtain ⟨K,mint,rfl⟩ := rep.1
  obtain ⟨xs,perm,ordered,fold⟩ := rep.2.2.2.2
  rw [← fold,rawFold_records]
  exact live_membership K mint rep.2.1 perm (fun _ h => rep.2.2.2.1 h)
    (CertifiedFugueVCReplay.respects_lo Γ K mint rep.2.1 H xs perm rep.2.2.2.1 ordered) p

theorem births_membership (Γ : OrderedPrefixCode) (C : ReplayContext (datatype Γ).toUpdateSig)
    (H : Set (Op Payload)) (s : State) (rep : representation Γ C H s) (g : MRec) :
    g ∈ s.births ↔ ∃ e ∈ H, recordOf e = g ∧ mIsIns g = true := by
  obtain ⟨xs,perm,_,fold⟩ := rep.2.2.2.2
  rw [← fold,rawFold_records]
  simp only [stateOf,List.mem_toFinset,mMinted,List.mem_filter,List.mem_map]
  constructor
  · rintro ⟨⟨e,he,eq⟩,hi⟩
    exact ⟨e,(perm.2 e).mp he,eq,hi⟩
  · rintro ⟨e,he,eq,hi⟩
    exact ⟨⟨e,(perm.2 e).mpr he,eq⟩,hi⟩

theorem compatible (Γ : OrderedPrefixCode) (C : ReplayContext (datatype Γ).toUpdateSig)
    (H K : Set (Op Payload)) (s t : State)
    (hs : representation Γ C H s) (ht : representation Γ C K t) :
    ∀ x ∈ s.live, ∀ y ∈ t.live, x.1 = y.1 → x = y := by
  intro x hx y hy ids
  obtain ⟨⟨a,ha,_,rx⟩,_⟩ := (membership Γ C H s hs x).mp hx
  obtain ⟨⟨b,hb,_,ry⟩,_⟩ := (membership Γ C K t ht y).mp hy
  have stamps : a.1 = b.1 := by simpa only [rx,ry,written] using ids
  have eq := C.ts_unique (hs.2.2.2.1 ha) (ht.2.2.2.1 hb) stamps
  simpa only [rx,ry,eq]

theorem merge_toFinset (Γ : OrderedPrefixCode) (C : ReplayContext (datatype Γ).toUpdateSig)
    (L A B : Set (Op Payload)) (l a b : State)
    (hl : representation Γ C L l) (ha : representation Γ C A a)
    (hb : representation Γ C B b) :
    (rawMerge l a b).live.toFinset =
      SetMergeAlgebra.merge l.live.toFinset a.live.toFinset b.live.toFinset := by
  ext p
  simp only [rawMerge,List.mem_toFinset,SetMergeAlgebra.merge,Finset.mem_union,
    Finset.mem_inter,Finset.mem_sdiff]
  simpa only [and_assoc,or_assoc] using CertifiedRGAVCAlgebra.Sided.merge_membership
    (compatible Γ C A L a l ha hl) (compatible Γ C B L b l hb hl)
    (compatible Γ C A B a b ha hb) (compatible Γ C B A b a hb ha) p

theorem sorted (Γ : OrderedPrefixCode) (C : ReplayContext (datatype Γ).toUpdateSig)
    (H : Set (Op Payload)) (s : State) (rep : representation Γ C H s) : SSorted s.live := by
  obtain ⟨K,mint,rfl⟩ := rep.1
  obtain ⟨xs,perm,ordered,fold⟩ := rep.2.2.2.2
  rw [← fold,rawFold_records]
  exact live_sorted K mint rep.2.1 perm (fun _ h => rep.2.2.2.1 h)
    (CertifiedFugueVCReplay.respects_lo Γ K mint rep.2.1 H xs perm rep.2.2.2.1 ordered)

theorem keys_compatible (Γ : OrderedPrefixCode) (C : ReplayContext (datatype Γ).toUpdateSig)
    (H K : Set (Op Payload)) (s t : State)
    (hs : representation Γ C H s) (ht : representation Γ C K t) :
    ∀ x ∈ s.live, ∀ y ∈ t.live, sKey x.2.2 = sKey y.2.2 → x = y := by
  intro x hx y hy keys
  obtain ⟨⟨a,ha,ia,rx⟩,_⟩ := (membership Γ C H s hs x).mp hx
  obtain ⟨⟨b,hb,ib,ry⟩,_⟩ := (membership Γ C K t ht y).mp hy
  obtain ⟨K₀,mint,eq⟩ := hs.1
  subst C
  have same : a = b := by
    apply same_written_of_key K₀ mint
      hs.2.1
      (hs.2.2.2.1 ha)
      (ht.2.2.2.1 hb) ia ib
    simpa only [rx,ry] using keys
  simpa only [rx,ry,same]

theorem merge_sorted (Γ : OrderedPrefixCode) (C : ReplayContext (datatype Γ).toUpdateSig)
    (H K : Set (Op Payload)) (l a b : State)
    (ha : representation Γ C H a) (hb : representation Γ C K b) :
    SSorted (rawMerge l a b).live :=
  sMerge_sorted (sorted Γ C H a ha) (sorted Γ C K b hb)
    (keys_compatible Γ C H K a b ha hb)
theorem fresh_id (Γ : OrderedPrefixCode) (C : ReplayContext (datatype Γ).toUpdateSig)
    (H : Set (Op Payload)) (s : State) (rep : representation Γ C H s)
    (e : Op Payload) (eligible : e ∈ C.events) (absent : e ∉ H) : e.1 ∉ sIds s.live := by
  intro mem
  obtain ⟨p,hp,id⟩ := List.mem_map.mp mem
  obtain ⟨⟨o,ho,_,record⟩,_⟩ := (membership Γ C H s rep p).mp hp
  have same : o.1 = e.1 := by simpa only [record,sRecOf] using id
  have eq := C.ts_unique (rep.2.2.2.1 ho) eligible same
  exact absent (eq ▸ ho)

def killed (e : Op Payload) (p : SRec) : Prop :=
  match e.2.2.op with | .ins _ _ => False | .del target => p.1 = target

def born (Γ : OrderedPrefixCode) (e : Op Payload) (p : SRec) : Prop :=
  mIsIns (recordOf e) = true ∧ p = written Γ e

def recordStep (Γ : OrderedPrefixCode) (e : Op Payload) (s : Finset (SRec)) : Finset (SRec) :=
  match e.2.2.op with
  | .ins _ _ => insert (written Γ e) s
  | .del target => s.filter (fun p => p.1 ≠ target)

theorem recordStep_mem (Γ : OrderedPrefixCode) (e : Op Payload) (s : Finset (SRec)) (p : SRec) :
    p ∈ recordStep Γ e s ↔ born Γ e p ∨ (p ∈ s ∧ ¬ killed e p) := by
  rcases e with ⟨et,er,⟨op,lo,ro,chain⟩⟩
  cases op <;> simp [recordStep,born,killed,mIsIns,recordOf,written]

theorem update_toFinset (Γ : OrderedPrefixCode) (C : ReplayContext (datatype Γ).toUpdateSig)
    (H : Set (Op Payload)) (s : State) (rep : representation Γ C H s)
    (e : Op Payload) (eligible : e ∈ C.events) (absent : e ∉ H) :
    ((rawUpdate Γ s e).live).toFinset = recordStep Γ e s.live.toFinset := by
  have fresh := fresh_id Γ C H s rep e eligible absent
  ext p
  rcases e with ⟨et,er,⟨op,lo,ro,chain⟩⟩
  cases op <;> simp only [rawUpdate,mStep,recordOf,if_neg fresh,List.mem_toFinset,mem_sInsert,
    recordStep,Finset.mem_insert,List.mem_filter,Finset.mem_filter,decide_eq_true_eq]
  · tauto


theorem killed_covered (Γ : OrderedPrefixCode) (C : ReplayContext (datatype Γ).toUpdateSig)
    (U : Set (Op Payload)) (a b : State) (e : Op Payload)
    (member : e ∈ U) (eligible : e ∈ C.events) (closed : (scheme Γ C).Closed U)
    (ha : representation Γ C (U \ {e}) a)
    (hb : representation Γ C ((scheme Γ C).Past e \ {e}) b) :
    ∀ p ∈ a.live, killed e p → p ∈ b.live := by
  intro p hp kill
  obtain ⟨⟨o,ho,ins,rec⟩,noDelete⟩ := (membership Γ C _ a ha p).mp hp
  obtain ⟨K,mint,eq⟩ := ha.1
  subst C
  have shape : e.2.2.op = .del o.1 := by
    cases he : e.2.2.op with
    | ins parent sd => simp [killed,he] at kill
    | del target =>
      have stamp : o.1 = target := by simpa only [killed,he,rec,written] using kill
      simpa only [stamp] using he
  have vis := rc_visible K mint ha.2.1 (ha.2.2.2.1 ho) eligible
    ((rc_before Γ o e).mpr ⟨ins,shape⟩)
  apply (membership Γ K.replayContext _ b hb p).mpr
  refine ⟨⟨o,⟨Or.inr (.single vis),ho.2⟩,ins,rec⟩,?_⟩
  intro d hd
  have subset := (scheme Γ K.replayContext).past_subset U e closed member
  exact noDelete d ⟨subset hd.1,hd.2⟩
theorem fresh_born (Γ : OrderedPrefixCode) (C : ReplayContext (datatype Γ).toUpdateSig)
    (H : Set (Op Payload)) (s : State) (rep : representation Γ C H s)
    (e : Op Payload) (eligible : e ∈ C.events) (absent : e ∉ H) :
    ∀ p, born Γ e p → p ∉ s.live := by
  intro p birth mem
  have ids : p.1 = e.1 := by rw [birth.2]; rfl
  exact fresh_id Γ C H s rep e eligible absent (List.mem_map.mpr ⟨p,mem,ids⟩)

theorem eq_of_toFinset {s t : SState} (hs : SSorted s) (ht : SSorted t)
    (eq : s.toFinset = t.toFinset) : s = t := by
  apply ssorted_ext hs ht
  intro p
  exact (List.mem_toFinset (l := s) (a := p)).symm.trans
    ((congrArg (fun f : Finset (SRec) => p ∈ f) eq).to_iff.trans List.mem_toFinset)

theorem finite_causal (Γ : OrderedPrefixCode) (e : Op Payload) (a b : Finset (SRec))
    (fresh : ∀ p, born Γ e p → p ∉ b)
    (covered : ∀ p ∈ a, killed e p → p ∈ b) :
    SetMergeAlgebra.merge b a (recordStep Γ e b) = recordStep Γ e a := by
  ext p
  have hf := fresh p
  have hc := covered p
  simp only [SetMergeAlgebra.merge,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff,recordStep_mem]
  tauto

theorem common_record (Γ : OrderedPrefixCode) (C : ReplayContext (datatype Γ).toUpdateSig)
    (E₁ E₂ : Set (Op Payload)) (l B s : State) (e : Op Payload)
    (member : e ∈ E₁) (closed : (scheme Γ C).Closed E₁)
    (base : representation Γ C (E₁ ∩ E₂) l)
    (past : representation Γ C ((scheme Γ C).Past e \ {e}) B)
    (other : representation Γ C E₂ s) : ∀ p ∈ B.live, p ∈ s.live → p ∈ l.live := by
  intro p hp hs
  obtain ⟨⟨a,ha,ia,recA⟩,_⟩ := (membership Γ C _ B past p).mp hp
  obtain ⟨⟨b,hb,ib,recB⟩,noDelete⟩ := (membership Γ C _ s other p).mp hs
  have same : a = b := C.ts_unique (past.2.2.2.1 ha) (other.2.2.2.1 hb)
    (by have h := congrArg Prod.fst (recA.symm.trans recB); exact h)
  have subset := (scheme Γ C).past_subset E₁ e closed member
  apply (membership Γ C _ l base p).mpr
  refine ⟨⟨a,⟨subset ha.1,same ▸ hb⟩,ia,recA⟩,?_⟩
  intro d hd
  exact noDelete d hd.2

end Sal.MRDTs.Paper1.CertifiedFugueVCAlgebra
