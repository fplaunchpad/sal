import Sal.MRDTs.Paper1.OptionalRegisterReplay

/-! Payload coherence is derived from supported, visibility-closed Set prefixes
at each issuer. Equal counts identify the same latest Set; strict count growth
forces a later timestamp. No source merge equation is a premise. -/
namespace Sal.MRDTs.Paper1.OptionalRegister
open Foundation ConcreteMRDT Instances.OptionalRegister OptionalRegisterCounts
open Classical

private theorem winner_mem {E : Set Event}
    {F : Finset Event} (hF : (↑F : Set Event) = E) {w : Event} (hw : w ∈ E)
    {r : Nat} (own : w.rep = r) (set : w.op.isSet = true) : w ∈ winners F r := by
  have hf : w ∈ F := by rw [← hF] at hw; exact hw
  exact Finset.mem_filter.mpr ⟨hf,own,set⟩

private theorem latest_growth (C : ReplayContext D.toUpdateSig)
    (E₁ E₂ : Set Event) (F G : Finset Event)
    (hF : (↑F : Set Event) = E₁) (hG : (↑G : Set Event) = E₂)
    (good : GoodContext C) (sup₁ : Supported C E₁) (sup₂ : Supported C E₂)
    (closed₁ : ∀ x y, C.vis x y → y ∈ E₁ → x ∈ E₁)
    (r : Nat) (w v : Event) (hw : w ∈ E₁) (hv : v ∈ E₂)
    (ownW : w.rep = r) (ownV : v.rep = r) (setW : w.op.isSet = true)
    (latestV : ∀ x ∈ E₂, x.rep = r → x.op.isSet = true → x.time ≤ v.time)
    (growth : count F r < count G r) : w.time < v.time := by
  have notsub : ¬ winners G r ⊆ winners F r := by
    intro sub
    have bound := Finset.card_le_card sub
    unfold count at growth
    omega
  obtain ⟨x,hx,absent⟩ := Finset.not_subset.mp notsub
  obtain ⟨hxG,ownX,setX⟩ := Finset.mem_filter.mp hx
  have hxE : x ∈ E₂ := by rw [← hG]; exact hxG
  have ne : w ≠ x := by
    intro same
    exact absent (same ▸ winner_mem hF hw ownW setW)
  obtain ⟨rw,Sw,hLw,hwS⟩ := sup₁ w hw
  obtain ⟨rx,Sx,hLx,hxS⟩ := sup₂ x hxE
  have forward : C.vis w x := by
    rcases C.vis_total_same_replica hLw hwS hLx hxS ne (ownW.trans ownX.symm) with h | h
    · exact h
    · have inF := closed₁ x w h hw
      exact (absent (winner_mem hF inF ownX setX)).elim
  exact lt_of_lt_of_le (good.mono forward) (latestV x hxE ownX setX)

/-- All payload side conditions used by the source averaging branch are
proved from the represented histories, rather than assumed as invariants. -/
theorem represented_coherent (C : ReplayContext D.toUpdateSig)
    (E₁ E₂ : Set Event) (a b : State)
    (closed₁ : ∀ x y, C.vis x y → y ∈ E₁ → x ∈ E₁)
    (closed₂ : ∀ x y, C.vis x y → y ∈ E₂ → x ∈ E₂)
    (ha : representation C E₁ a) (hb : representation C E₂ b) (r : Nat) :
    CoherentCells (a.cells r) (b.cells r) := by
  refine ⟨?_,ha.inactive r,hb.inactive r⟩
  intro af bf
  obtain ⟨F,hF⟩ := ha.finite
  obtain ⟨G,hG⟩ := hb.finite
  obtain ⟨w,hw,ownW,liveW,payloadW,latestW⟩ := ha.payload r af
  obtain ⟨v,hv,ownV,liveV,payloadV,latestV⟩ := hb.payload r bf
  have countA := ha.counts F hF r
  have countB := hb.counts G hG r
  refine ⟨?_,?_,?_⟩
  · intro growth
    rw [payloadW,payloadV]
    exact latest_growth C E₁ E₂ F G hF hG ha.good ha.supported hb.supported closed₁
      r w v hw hv ownW ownV liveW.1 latestV (by simpa only [← countA,← countB] using growth)
  · intro growth
    rw [payloadW,payloadV]
    exact latest_growth C E₂ E₁ G F hG hF hb.good hb.supported ha.supported closed₂
      r v w hv hw ownV ownW liveV.1 latestW (by simpa only [← countA,← countB] using growth)
  · intro equal
    have cards : (winners F r).card = (winners G r).card := by
      have eq : count F r = count G r := countA.symm.trans (equal.trans countB)
      unfold count at eq
      exact_mod_cast eq
    have same : winners F r = winners G r := by
      rcases prefixes_comparable C E₁ E₂ F G hF hG ha.supported hb.supported closed₁ closed₂ r with sub | sub
      · exact Finset.eq_of_subset_of_card_le sub (by omega)
      · exact (Finset.eq_of_subset_of_card_le sub (by omega)).symm
    have wG : w ∈ G := (Finset.mem_filter.mp (same ▸ winner_mem hF hw ownW liveW.1)).1
    have vF : v ∈ F := (Finset.mem_filter.mp (same.symm ▸ winner_mem hG hv ownV liveV.1)).1
    have wE : w ∈ E₂ := by rw [← hG]; exact wG
    have vE : v ∈ E₁ := by rw [← hF]; exact vF
    have times : w.time = v.time := le_antisymm (latestV w wE ownW liveW.1)
      (latestW v vE ownV liveV.1)
    have sameEvent : w = v := C.ts_unique (ha.supported w hw) (hb.supported v hv) times
    rw [payloadW,payloadV,sameEvent]

/-- A full represented intersection contains exactly the minimum Set count
at each issuer, independently of payloads or flag values. -/
theorem intersection_counts (C : ReplayContext D.toUpdateSig)
    (E₁ E₂ : Set Event) (l a b : State)
    (closed₁ : ∀ x y, C.vis x y → y ∈ E₁ → x ∈ E₁)
    (closed₂ : ∀ x y, C.vis x y → y ∈ E₂ → x ∈ E₂)
    (hl : representation C (E₁ ∩ E₂) l)
    (ha : representation C E₁ a) (hb : representation C E₂ b) :
    ∀ r, (l.cells r).1.1 = min (a.cells r).1.1 (b.cells r).1.1 := by
  obtain ⟨F,hF⟩ := ha.finite
  obtain ⟨G,hG⟩ := hb.finite
  have hI : (↑(F ∩ G) : Set Event) = E₁ ∩ E₂ := by simp [hF,hG]
  intro r
  rw [hl.counts (F ∩ G) hI,ha.counts F hF,hb.counts G hG]
  exact count_min_of_comparable F G r
    (prefixes_comparable C E₁ E₂ F G hF hG ha.supported hb.supported closed₁ closed₂ r)

/-- Comparison join is a proof algebra, while the executable merge remains
Neem's arithmetic and averaging algorithm. -/
def join (a b : State) : State :=
  ⟨a.domain ∪ b.domain,fun r => joinCell (a.cells r) (b.cells r),by
    intro r absent
    have absent' : r ∉ a.domain ∧ r ∉ b.domain := by simpa using absent
    change joinCell (a.cells r) (b.cells r) = zero
    rw [a.outside r absent'.1,b.outside r absent'.2]
    simp⟩

theorem join_comm (a b : State) : join a b = join b a := by
  apply State.ext
  · simp [join,Finset.union_comm]
  · intro r; exact joinCell_comm _ _
theorem join_assoc (a b c : State) : join (join a b) c = join a (join b c) := by
  apply State.ext
  · simp [join,Finset.union_assoc]
  · intro r; exact joinCell_assoc _ _ _
@[simp] theorem join_idem (a : State) : join a a = a := by
  apply State.ext
  · simp [join]
  · intro r; exact joinCell_idem _

theorem join_local (t b d : State) : join (join t d) b = join (join t b) d := by
  rw [join_assoc,join_comm d b,← join_assoc]

theorem join_shared (a b d : State) : join (join a d) (join b d) = join (join a b) d := by
  rw [join_assoc,← join_assoc d b d,join_comm d b,join_assoc b d d,join_idem,← join_assoc]

/-- The represented ancestor contributes no extra domain entries; each row
uses the derived count minimum and payload coherence. -/
theorem source_as_join (C : ReplayContext D.toUpdateSig)
    (E₁ E₂ : Set Event) (l a b : State)
    (closed₁ : ∀ x y, C.vis x y → y ∈ E₁ → x ∈ E₁)
    (closed₂ : ∀ x y, C.vis x y → y ∈ E₂ → x ∈ E₂)
    (hl : representation C (E₁ ∩ E₂) l)
    (ha : representation C E₁ a) (hb : representation C E₂ b) :
    merge l a b = join a b := by
  obtain ⟨F,hF⟩ := ha.finite
  obtain ⟨G,hG⟩ := hb.finite
  have hI : (↑(F ∩ G) : Set Event) = E₁ ∩ E₂ := by simp [hF,hG]
  have dom : l.domain ⊆ a.domain := by
    rw [hl.domain (F ∩ G) hI,ha.domain F hF]
    unfold rows
    exact Finset.image_subset_image (Finset.filter_subset_filter _ Finset.inter_subset_left)
  apply State.ext
  · change l.domain ∪ (a.domain ∪ b.domain) = a.domain ∪ b.domain
    exact Finset.union_eq_right.mpr (dom.trans Finset.subset_union_left)
  · intro r
    exact sourceCell_as_join _ _ _ (intersection_counts C E₁ E₂ l a b closed₁ closed₂ hl ha hb r)
      (represented_coherent C E₁ E₂ a b closed₁ closed₂ ha hb r)

#print axioms represented_coherent
#print axioms source_as_join
end Sal.MRDTs.Paper1.OptionalRegister
