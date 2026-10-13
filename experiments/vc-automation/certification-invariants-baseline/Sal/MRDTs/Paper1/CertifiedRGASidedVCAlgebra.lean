import Sal.MRDTs.Paper1.CertifiedRGAVCReplay
import Sal.MRDTs.Paper1.ConcreteORSetAlgebra

/-! Independent raw merge algebra for certified immutable records. These
lemmas normalize a merge by membership; they assume no merge correctness. -/
namespace Sal.MRDTs.Paper1.CertifiedRGAVCAlgebra
open Foundation Sal.EmbedRGA
namespace Sided
open Instances.SidedEmbedRGA
open CertifiedRGAVCReplay.Sided

theorem provenance (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (H : Set (Op SOp)) (s : SState) (rep : representation Γ C H s)
    (p : SRec) (mem : p ∈ s) :
    ∃ o ∈ H, sIsIns o = true ∧ p = sRecOf Γ o := by
  obtain ⟨xs,perm,_,fold⟩ := rep.2.2.2.2
  rw [← fold] at mem
  obtain ⟨o,ho,ins,rec⟩ := s_fold_rec_sub Γ xs p mem
  exact ⟨o,(perm.2 o).mp ho,ins,rec⟩

theorem compatible (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (H K : Set (Op SOp)) (s t : SState)
    (hs : representation Γ C H s) (ht : representation Γ C K t) :
    ∀ x ∈ s, ∀ y ∈ t, x.1 = y.1 → x = y := by
  intro x hx y hy ids
  obtain ⟨a,ha,_,rx⟩ := provenance Γ C H s hs x hx
  obtain ⟨b,hb,_,ry⟩ := provenance Γ C K t ht y hy
  have stamps : a.1 = b.1 := by simpa only [rx,ry,sRecOf] using ids
  have eq := C.ts_unique (hs.2.2.2.1 ha) (ht.2.2.2.1 hb) stamps
  simpa only [rx,ry,eq]

private theorem id_iff_mem {s t : SState} {p : SRec} (hp : p ∈ s)
    (compat : ∀ x ∈ s, ∀ y ∈ t, x.1 = y.1 → x = y) : p.1 ∈ sIds t ↔ p ∈ t := by
  constructor
  · intro ids
    obtain ⟨q,hq,equal⟩ := List.mem_map.mp ids
    exact (compat p hp q hq equal.symm) ▸ hq
  · intro mem
    exact List.mem_map.mpr ⟨p,mem,rfl⟩

/-- The identifier tests become ordinary record membership under immutable
birth coherence. The result is a ternary Boolean equation, not Join. -/
theorem merge_membership {l a b : SState}
    (al : ∀ x ∈ a, ∀ y ∈ l, x.1 = y.1 → x = y)
    (bl : ∀ x ∈ b, ∀ y ∈ l, x.1 = y.1 → x = y)
    (ab : ∀ x ∈ a, ∀ y ∈ b, x.1 = y.1 → x = y)
    (ba : ∀ x ∈ b, ∀ y ∈ a, x.1 = y.1 → x = y) (p : SRec) :
    p ∈ sMerge l a b ↔
      (p ∈ l ∧ p ∈ a ∧ p ∈ b) ∨ (p ∈ a ∧ p ∉ l) ∨ (p ∈ b ∧ p ∉ l) := by
  have hlA := fun h : p ∈ a => id_iff_mem h al
  have hlB := fun h : p ∈ b => id_iff_mem h bl
  have hab := fun h : p ∈ a => id_iff_mem h ab
  have hba := fun h : p ∈ b => id_iff_mem h ba
  simp only [sMerge,mem_sMerge2,List.mem_filter,Bool.or_eq_true,Bool.and_eq_true,
    decide_eq_true_eq]
  tauto

/-- Finite set normalization of the actual list merge, justified by birth
coherence. It supports equation proofs independently of replay Join. -/
theorem merge_toFinset (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (L A B : Set (Op SOp)) (l a b : SState)
    (hl : representation Γ C L l) (ha : representation Γ C A a)
    (hb : representation Γ C B b) :
    (sMerge l a b).toFinset = SetMergeAlgebra.merge l.toFinset a.toFinset b.toFinset := by
  ext p
  simp only [List.mem_toFinset,SetMergeAlgebra.merge,Finset.mem_union,
    Finset.mem_inter,Finset.mem_sdiff]
  simpa only [and_assoc,or_assoc] using merge_membership (compatible Γ C A L a l ha hl)
    (compatible Γ C B L b l hb hl) (compatible Γ C A B a b ha hb)
    (compatible Γ C B A b a hb ha) p

theorem sorted (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (H : Set (Op SOp)) (s : SState) (rep : representation Γ C H s) : SSorted s := by
  obtain ⟨xs,perm,ordered,fold⟩ := rep.2.2.2.2
  rw [← fold]
  exact s_fold_sorted Γ (wellformed_supported Γ C rep.1 xs perm.1
    (fun o ho => rep.2.2.2.1 ((perm.2 o).mp ho)) ordered)

theorem keys_compatible (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (H K : Set (Op SOp)) (s t : SState)
    (hs : representation Γ C H s) (ht : representation Γ C K t) :
    ∀ x ∈ s, ∀ y ∈ t, sKey x.2.2 = sKey y.2.2 → x = y := by
  intro x hx y hy keys
  obtain ⟨a,ha,ia,rx⟩ := provenance Γ C H s hs x hx
  obtain ⟨b,hb,ib,ry⟩ := provenance Γ C K t ht y hy
  have ids : a.1 = b.1 := by
    by_contra ne
    exact s_keys_inj_events hs.1 a (hs.2.2.2.1 ha) b (ht.2.2.2.1 hb) ia ib ne
      (by simpa only [rx,ry,sRecOf] using keys)
  have eq := C.ts_unique (hs.2.2.2.1 ha) (ht.2.2.2.1 hb) ids
  simpa only [rx,ry,eq]

theorem merge_sorted (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (H K : Set (Op SOp)) (l a b : SState)
    (ha : representation Γ C H a) (hb : representation Γ C K b) : SSorted (sMerge l a b) :=
  sMerge_sorted (sorted Γ C H a ha) (sorted Γ C K b hb) (keys_compatible Γ C H K a b ha hb)

theorem fresh_id (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (H : Set (Op SOp)) (s : SState) (rep : representation Γ C H s)
    (e : Op SOp) (eligible : e ∈ C.events) (absent : e ∉ H) : e.1 ∉ sIds s := by
  intro mem
  obtain ⟨p,hp,id⟩ := List.mem_map.mp mem
  obtain ⟨o,ho,_,record⟩ := provenance Γ C H s rep p hp
  have same : o.1 = e.1 := by simpa only [record,sRecOf] using id
  have eq := C.ts_unique (rep.2.2.2.1 ho) eligible same
  exact absent (eq ▸ ho)

def killed (e : Op SOp) (p : SRec) : Prop :=
  match e.2.2 with | .ins _ _ _ _ => False | .del target => p.1 = target

def born (Γ : OrderedPrefixCode) (e : Op SOp) (p : SRec) : Prop :=
  sIsIns e = true ∧ p = sRecOf Γ e

def recordStep (Γ : OrderedPrefixCode) (e : Op SOp) (s : Finset (SRec)) : Finset (SRec) :=
  match e.2.2 with
  | .ins _ _ _ _ => insert (sRecOf Γ e) s
  | .del target => s.filter (fun p => p.1 ≠ target)

theorem recordStep_mem (Γ : OrderedPrefixCode) (e : Op SOp) (s : Finset (SRec)) (p : SRec) :
    p ∈ recordStep Γ e s ↔ born Γ e p ∨ (p ∈ s ∧ ¬ killed e p) := by
  rcases e with ⟨et,er,op⟩
  cases op <;> simp [recordStep,born,killed,sIsIns]

theorem update_toFinset (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (H : Set (Op SOp)) (s : SState) (rep : representation Γ C H s)
    (e : Op SOp) (eligible : e ∈ C.events) (absent : e ∉ H) :
    (sUpdate Γ s e).toFinset = recordStep Γ e s.toFinset := by
  have fresh := fresh_id Γ C H s rep e eligible absent
  ext p
  rcases e with ⟨et,er,op⟩
  cases op <;> simp only [sUpdate,if_neg fresh,List.mem_toFinset,mem_sInsert,
    recordStep,sRecOf,Finset.mem_insert,List.mem_filter,Finset.mem_filter,decide_eq_true_eq]
  · tauto

theorem membership (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (H : Set (Op SOp)) (s : SState) (rep : representation Γ C H s) (p : SRec) :
    p ∈ s ↔ (∃ o ∈ H, sIsIns o = true ∧ p = sRecOf Γ o) ∧
      (∀ d ∈ H, d.2.2 ≠ SOp.del p.1) := by
  obtain ⟨xs,perm,ordered,fold⟩ := rep.2.2.2.2
  have wf := wellformed_supported Γ C rep.1 xs perm.1 (fun o ho => rep.2.2.2.1 ((perm.2 o).mp ho)) ordered
  rw [← fold,s_fold_mem Γ wf]
  constructor
  · rintro ⟨⟨o,ho,ins,rec⟩,noDelete⟩
    refine ⟨⟨o,(perm.2 o).mp ho,ins,rec⟩,?_⟩
    intro d hd shape
    exact noDelete (mem_sDels.mpr ⟨d,(perm.2 d).mpr hd,shape⟩)
  · rintro ⟨⟨o,ho,ins,rec⟩,noDelete⟩
    refine ⟨⟨o,(perm.2 o).mpr ho,ins,rec⟩,?_⟩
    intro deleted
    obtain ⟨d,hd,shape⟩ := mem_sDels.mp deleted
    exact noDelete d ((perm.2 d).mp hd) shape

/-- The causal past covers every remainder record removed by an eligible
step. This uses its actual issued delete birth and immutable tag uniqueness. -/
theorem killed_covered (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (U : Set (Op SOp)) (a b : SState) (e : Op SOp)
    (member : e ∈ U) (eligible : e ∈ C.events) (closed : (scheme Γ C).Closed U)
    (ha : representation Γ C (U \ {e}) a)
    (hb : representation Γ C ((scheme Γ C).Past e \ {e}) b) :
    ∀ p ∈ a, killed e p → p ∈ b := by
  intro p hp kill
  obtain ⟨⟨o,ho,ins,rec⟩,noDelete⟩ := (membership Γ C _ a ha p).mp hp
  rcases e with ⟨et,er,op⟩
  cases op with
  | ins x pref anchor sd => exact False.elim kill
  | del target =>
    change p.1 = target at kill
    obtain ⟨birth,hbirth,vis,time,_⟩ := ha.1.del_has_ins (et,er,.del target)
      eligible target rfl
    have stamp : o.1 = target := by simpa only [rec,sRecOf] using kill
    have same := C.ts_unique hbirth (ha.2.2.2.1 ho) (time.trans stamp.symm)
    subst birth
    apply (membership Γ C _ b hb p).mpr
    refine ⟨⟨o,⟨Or.inr (.single vis),ho.2⟩,ins,rec⟩,?_⟩
    intro d hd
    have subset := (scheme Γ C).past_subset U (et,er,.del target) closed member
    exact noDelete d ⟨subset hd.1,hd.2⟩

theorem fresh_born (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (H : Set (Op SOp)) (s : SState) (rep : representation Γ C H s)
    (e : Op SOp) (eligible : e ∈ C.events) (absent : e ∉ H) :
    ∀ p, born Γ e p → p ∉ s := by
  intro p birth mem
  have ids : p.1 = e.1 := by rw [birth.2]; rfl
  exact fresh_id Γ C H s rep e eligible absent (List.mem_map.mpr ⟨p,mem,ids⟩)

theorem eq_of_toFinset {s t : SState} (hs : SSorted s) (ht : SSorted t)
    (eq : s.toFinset = t.toFinset) : s = t := by
  apply ssorted_ext hs ht
  intro p
  exact (List.mem_toFinset (l := s) (a := p)).symm.trans
    ((congrArg (fun f : Finset (SRec) => p ∈ f) eq).to_iff.trans List.mem_toFinset)

theorem finite_causal (Γ : OrderedPrefixCode) (e : Op SOp) (a b : Finset (SRec))
    (fresh : ∀ p, born Γ e p → p ∉ b)
    (covered : ∀ p ∈ a, killed e p → p ∈ b) :
    SetMergeAlgebra.merge b a (recordStep Γ e b) = recordStep Γ e a := by
  ext p
  have hf := fresh p
  have hc := covered p
  simp only [SetMergeAlgebra.merge,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff,recordStep_mem]
  tauto

theorem common_record (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (E₁ E₂ : Set (Op SOp)) (l B s : SState) (e : Op SOp)
    (member : e ∈ E₁) (closed : (scheme Γ C).Closed E₁)
    (base : representation Γ C (E₁ ∩ E₂) l)
    (past : representation Γ C ((scheme Γ C).Past e \ {e}) B)
    (other : representation Γ C E₂ s) : ∀ p ∈ B, p ∈ s → p ∈ l := by
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

end Sided
end Sal.MRDTs.Paper1.CertifiedRGAVCAlgebra
