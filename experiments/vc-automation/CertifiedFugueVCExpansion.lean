import CertifiedFugueNormalization
import CertifiedFugueEvidence
import Sal.MRDTs.Paper1.CertifiedFugueVCAlgebra

set_option maxHeartbeats 2000000

namespace NeemExpansion.CertifiedFugueVCExpansion
open Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.EmbedRGA
open Sal.MRDTs.Instances.SidedEmbedRGA Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax
open CertifiedFugueVCReplay CertifiedFugueVCAlgebra

theorem evidence (Γ : OrderedPrefixCode) (C : ReplayContext (datatype Γ).toUpdateSig)
    (H : Set (Op Payload)) (s : State) (rep : representation Γ C H s) :
    CertifiedFugue.HistoryEvidence Γ C := by
  obtain ⟨K,mint,rfl⟩ := rep.1
  exact ⟨CertifiedFugue.chain_of_mint K mint rep.2.1,
    CertifiedFugue.delete_birth_of_mint K mint rep.2.1⟩

theorem membership (Γ : OrderedPrefixCode) (C : ReplayContext (datatype Γ).toUpdateSig)
    (H : Set (Op Payload)) (s : State) (rep : representation Γ C H s) (p : SRec) :
    p∈s.live ↔ (∃e∈H,mIsIns (recordOf e)=true ∧ p=written Γ e) ∧ ∀d∈H,d.2.2.op≠.del p.1 :=
  CertifiedFugue.replay_membership Γ C (evidence Γ C H s rep) H s rep p

theorem sorted (Γ : OrderedPrefixCode) (C : ReplayContext (datatype Γ).toUpdateSig)
    (H : Set (Op Payload)) (s : State) (rep : representation Γ C H s) : SSorted s.live :=
  CertifiedFugue.sorted Γ C (evidence Γ C H s rep) H s rep
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

theorem keys_compatible (Γ : OrderedPrefixCode) (C : ReplayContext (datatype Γ).toUpdateSig)
    (H K : Set (Op Payload)) (s t : State)
    (hs : representation Γ C H s) (ht : representation Γ C K t) :
    ∀ x ∈ s.live, ∀ y ∈ t.live, sKey x.2.2 = sKey y.2.2 → x = y := by
  intro x hx y hy keys
  obtain ⟨⟨a,ha,ia,rx⟩,_⟩ := (membership Γ C H s hs x).mp hx
  obtain ⟨⟨b,hb,ib,ry⟩,_⟩ := (membership Γ C K t ht y).mp hy
  have same : a = b := by
    apply C.ts_unique (hs.2.2.2.1 ha) (ht.2.2.2.1 hb)
    by_contra different
    exact CertifiedFugue.keys_distinct Γ C (evidence Γ C H s hs) a b
      (hs.2.2.2.1 ha) (ht.2.2.2.1 hb) ia ib different
      (by simpa only [rx,ry,written] using keys)
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
  have shape : e.2.2.op = .del p.1 := by
    cases he : e.2.2.op with
    | ins a sd => simp [killed,he] at kill
    | del target =>
      have kp : p.1=target := by simpa only [killed,he] using kill
      simpa only [kp] using he
  rcases (evidence Γ C _ a ha).delete e eligible p.1 shape with zero | ⟨birth,hbirth,vis,_,time⟩
  · have pos : 0<o.1 := ((evidence Γ C _ a ha).chain o (ha.2.2.2.1 ho)).1
    have ids : p.1=o.1 := congrArg Prod.fst rec
    exact False.elim ((Nat.ne_of_gt pos) (ids.symm.trans zero))
  · have same := C.ts_unique hbirth (ha.2.2.2.1 ho) (time.trans (congrArg Prod.fst rec))
    subst birth
    apply (membership Γ C _ b hb p).mpr
    refine ⟨⟨o,⟨Or.inr (.single vis),ho.2⟩,ins,rec⟩,?_⟩
    intro d hd
    have subset := (scheme Γ C).past_subset U e closed member
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

theorem finite_causal (Γ : OrderedPrefixCode) (e : Op Payload) (a b : Finset SRec)
    (fresh : ∀p,born Γ e p→p∉b) (covered : ∀p∈a,killed e p→p∈b) :
    SetMergeAlgebra.merge b a (recordStep Γ e b)=recordStep Γ e a :=
  Certified.causal b a _ _ (born Γ e) (killed e) ⟨fresh,covered⟩
    (recordStep_mem Γ e b) (recordStep_mem Γ e a)

theorem finite_local (l B t b d : Finset SRec)
    (common : ∀p∈B,p∉d→p∈b→p∈l) (newborn : ∀p,p∉B→p∈d→p∉l) :
    SetMergeAlgebra.merge l (SetMergeAlgebra.merge B t d) b=
      SetMergeAlgebra.merge B (SetMergeAlgebra.merge l t b) d :=
  Certified.local_redistribute l B t b d ⟨common,newborn⟩

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

private theorem state_ext {s t : State} (live : s.live = t.live) (births : s.births = t.births) : s = t := by
  cases s; cases t; cases live; cases births; rfl

theorem expanded_vcs (Γ : OrderedPrefixCode) : ConcreteMRDT.Raw.MergeVCs
    policy (representation Γ) (scheme Γ) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro C E₁ E₂ l a b _ _ _ _ hl ha hb
    dsimp only [datatype] at *
    apply state_ext
    · apply eq_of_toFinset (merge_sorted Γ C _ _ l a b ha hb)
        (merge_sorted Γ C _ _ l b a hb ha)
      rw [merge_toFinset Γ C _ _ _ l a b hl ha hb,
        merge_toFinset Γ C _ _ _ l b a hl hb ha]
      ext p
      simp only [SetMergeAlgebra.merge,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
      tauto
    · simp [rawMerge,Finset.union_comm]
  · intro C H s _ _ rep
    dsimp only [datatype] at *
    apply state_ext
    · apply eq_of_toFinset (merge_sorted Γ C _ _ (datatype Γ).init (datatype Γ).init s (initial Γ C H s rep) rep) (sorted Γ C H s rep)
      rw [merge_toFinset Γ C _ _ _ (datatype Γ).init (datatype Γ).init s
        (initial Γ C H s rep) (initial Γ C H s rep) rep]
      simp [SetMergeAlgebra.merge,datatype]
    · simp [rawMerge]
  · intro C U s B e _ _ supported closed member _ _ hs hB hD hu
    have he : e ∈ C.events := hu.2.2.2.1 member
    dsimp only [datatype] at *
    apply state_ext
    · apply eq_of_toFinset (merge_sorted Γ C _ _ B s (rawUpdate Γ B e) hs hD)
        (sorted Γ C U (rawUpdate Γ s e) hu)
      rw [merge_toFinset Γ C _ _ _ B s (rawUpdate Γ B e) hB hs hD,
        update_toFinset Γ C _ B hB e he (by simp),
        update_toFinset Γ C _ s hs e he (by simp)]
      apply finite_causal Γ e
      · intro p hp mem
        exact fresh_born Γ C _ B hB e he (by simp) p hp (List.mem_toFinset.mp mem)
      · intro p mem kill
        exact List.mem_toFinset.mpr
          (killed_covered Γ C U s B e member he closed hs hB p (List.mem_toFinset.mp mem) kill)
    · change s.births ∪ (rawUpdate Γ B e).births = (rawUpdate Γ s e).births
      simp only [rawUpdate]
      have sub : B.births ⊆ s.births := by
        intro g hg
        obtain ⟨o,ho,eq,hi⟩ := (CertifiedFugue.represented_births Γ C _ B hB g).mp hg
        apply (CertifiedFugue.represented_births Γ C _ s hs g).mpr
        exact ⟨o,⟨(scheme Γ C).past_subset U e closed member ho.1,ho.2⟩,eq,hi⟩
      split <;> ext g <;> simp only [Finset.mem_union,Finset.mem_insert]
      · have h := sub (a := g); tauto
      · exact or_iff_left_of_imp (sub (a := g))
  · intro C E₁ E₂ l B t b e ctx member absent hl hB ht hb hD hi hm
    dsimp only [datatype] at *
    apply state_ext
    · apply eq_of_toFinset (merge_sorted Γ C _ _ l _ b hi hb)
        (merge_sorted Γ C _ _ B _ _ hm hD)
      rw [merge_toFinset Γ C _ _ _ l _ b hl hi hb,
        merge_toFinset Γ C _ _ _ B _ _ hB hm hD,
        merge_toFinset Γ C _ _ _ B t _ hB ht hD,
        merge_toFinset Γ C _ _ _ l t b hl ht hb]
      apply finite_local
      · intro p hp _ other
        exact List.mem_toFinset.mpr (common_record Γ C E₁ E₂ l B b e member ctx.closed₁
          hl hB hb p (List.mem_toFinset.mp hp) (List.mem_toFinset.mp other))
      · intro p notpast updated
        have he := hi.2.2.2.1 member
        rw [update_toFinset Γ C _ B hB e he (by simp),recordStep_mem] at updated
        have birth : born Γ e p := updated.resolve_right (fun h => notpast h.1)
        intro base
        exact fresh_born Γ C _ l hl e he (fun h => absent h.2) p birth
          (List.mem_toFinset.mp base)
    · change _ ∪ b.births = _ ∪ (rawUpdate Γ B e).births
      simp only [rawMerge]
      ext g
      simp only [Finset.mem_union]
      tauto
  · intro C E₁ E₂ t₀ t₁ t₂ B e _ _ _ h₀ hB h₁ h₂ hD hi₀ hi₁ hi₂ hm
    dsimp only [datatype] at *
    apply state_ext
    · apply eq_of_toFinset (merge_sorted Γ C _ _ _ _ _ hi₁ hi₂)
        (merge_sorted Γ C _ _ B _ _ hm hD)
      rw [merge_toFinset Γ C _ _ _ _ _ _ hi₀ hi₁ hi₂,
        merge_toFinset Γ C _ _ _ B _ _ hB hm hD,
        merge_toFinset Γ C _ _ _ B t₀ _ hB h₀ hD,
        merge_toFinset Γ C _ _ _ B t₁ _ hB h₁ hD,
        merge_toFinset Γ C _ _ _ B t₂ _ hB h₂ hD,
        merge_toFinset Γ C _ _ _ t₀ t₁ t₂ h₀ h₁ h₂]
      ext p
      simp only [SetMergeAlgebra.merge,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
      tauto
    · change _ ∪ _ = _ ∪ (rawUpdate Γ B e).births
      simp only [rawMerge]
      ext g
      simp only [Finset.mem_union]
      tauto

end NeemExpansion.CertifiedFugueVCExpansion
