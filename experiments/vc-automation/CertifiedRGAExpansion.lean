import CertifiedExpansion
import CertifiedReplayExpansion
import Sal.MRDTs.Paper1.CertifiedRGASidedVCAlgebra

/-! The actual insert/delete sided RGA route. Issuer and replay representation
are unchanged. We reuse only raw replay-to-record normalization, not a
production datatype VC, representation Join or invariant certificate. -/
namespace NeemExpansion.CertifiedRGA
open Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.EmbedRGA
open Sal.MRDTs.Instances.SidedEmbedRGA
open CertifiedRGAVCReplay.Sided CertifiedRGAVCAlgebra.Sided

/-- Recover immutable record provenance directly from the concrete replay. -/
theorem replay_membership (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (H : Set (Op SOp)) (s : SState) (rep : representation Γ C H s) (p : SRec) :
    p ∈ s ↔ (∃ o ∈ H, sIsIns o = true ∧ p = sRecOf Γ o) ∧
      (∀ d ∈ H, d.2.2 ≠ SOp.del p.1) := by
  obtain ⟨xs,perm,ordered,fold⟩ := rep.2.2.2.2
  rw [←fold,CertifiedSidedReplay.membership Γ C rep.1 xs perm.1
    (fun o ho => rep.2.2.2.1 ((perm.2 o).mp ho)) ordered p]
  simp only [CertifiedSidedReplay.Born,CertifiedSidedReplay.Kill]
  constructor
  · rintro ⟨⟨o,ho,ins,rec⟩,noDelete⟩
    exact ⟨⟨o,(perm.2 o).mp ho,ins,rec⟩,fun d hd => noDelete d ((perm.2 d).mpr hd)⟩
  · rintro ⟨⟨o,ho,ins,rec⟩,noDelete⟩
    exact ⟨⟨o,(perm.2 o).mpr ho,ins,rec⟩,fun d hd => noDelete d ((perm.2 d).mp hd)⟩

/-- Provenance is obtained from the newly expanded concrete replay formula. -/
theorem provenance (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (H : Set (Op SOp)) (s : SState) (rep : representation Γ C H s)
    (p : SRec) (mem : p ∈ s) : ∃ o ∈ H, sIsIns o = true ∧ p = sRecOf Γ o :=
  ((replay_membership Γ C H s rep p).mp mem).1

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

theorem fresh_id (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (H : Set (Op SOp)) (s : SState) (rep : representation Γ C H s)
    (e : Op SOp) (eligible : e ∈ C.events) (absent : e ∉ H) : e.1 ∉ sIds s := by
  intro mem
  obtain ⟨p,hp,id⟩ := List.mem_map.mp mem
  obtain ⟨o,ho,_,record⟩ := provenance Γ C H s rep p hp
  have same : o.1 = e.1 := by simpa only [record,sRecOf] using id
  exact absent ((C.ts_unique (rep.2.2.2.1 ho) eligible same) ▸ ho)

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

theorem keys_distinct (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (honest : SHonestCore Γ C) :
    ∀ a ∈ C.events, ∀ b ∈ C.events, sIsIns a = true → sIsIns b = true →
      a.1 ≠ b.1 → sKey (sCoord Γ a) ≠ sKey (sCoord Γ b) := by
  obtain ⟨chainOf,chain⟩ := honest.chain_gen
  intro a ha b hb ia ib different keys
  obtain ⟨pa,ca,sa⟩ := chain a ha ia
  obtain ⟨pb,cb,sb⟩ := chain b hb ib
  apply different
  have coords : sidedCoordOf Γ (chainOf a.1) = sidedCoordOf Γ (chainOf b.1) := by
    rw [←ca,←cb]
    exact sKey_inj keys
  have equal := sidedCoordOf_inj Γ pa pb coords
  calc a.1 = ((chainOf a.1).map Prod.snd).sum := sa.symm
       _ = ((chainOf b.1).map Prod.snd).sum := by rw [equal]
       _ = b.1 := sb

/-- Replay provenance via the generic one-step projection, also covering the
actual duplicate-identifier guard. No history well-formedness lemma is used. -/
theorem raw_provenance (Γ : OrderedPrefixCode) (xs : List (Op SOp)) (p : SRec) :
    p ∈ sFold Γ xs → ∃ e ∈ xs, sIsIns e = true ∧ p = sRecOf Γ e := by
  apply CertifiedReplay.provenance (sUpdate Γ) [] (fun p s => p ∈ s)
    (fun e p => sIsIns e = true ∧ p = sRecOf Γ e) (by simp)
  intro s e p hp
  rcases e with ⟨t,r,op⟩
  cases op with
  | ins x pref anchor sd =>
    simp only [sUpdate] at hp
    split at hp
    · exact Or.inr hp
    · rcases mem_sInsert.mp hp with old | birth
      · exact Or.inr old
      · exact Or.inl ⟨rfl,birth⟩
  | del target => exact Or.inr (List.mem_of_mem_filter hp)

theorem replay_sorted (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (honest : SHonestCore Γ C) (xs : List (Op SOp))
    (support : ∀ e ∈ xs, e ∈ C.events) : SSorted (sFold Γ xs) := by
  induction xs using List.reverseRecOn with
  | nil => exact List.Pairwise.nil
  | append_singleton xs e ih =>
    have prior := ih (fun o ho => support o (List.mem_append_left _ ho))
    rw [sFold_snoc]
    rcases e with ⟨t,r,op⟩
    cases op with
    | del target => exact List.Pairwise.filter _ prior
    | ins x pref anchor sd =>
      simp only [sUpdate]
      split
      · exact prior
      · rename_i fresh
        apply sInsert_sorted prior
        intro p hp
        obtain ⟨o,ho,ins,record⟩ := raw_provenance Γ xs p hp
        have diff : o.1 ≠ t := by
          intro same
          exact fresh (List.mem_map.mpr ⟨p,hp,by rw [record]; exact same⟩)
        have keys := keys_distinct Γ C honest o
          (support o (List.mem_append_left _ ho)) (t,r,SOp.ins x pref anchor sd)
          (support _ (by simp)) ins rfl diff
        simpa only [record,sRecOf,sCoord] using keys

theorem sorted (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (H : Set (Op SOp)) (s : SState) (rep : representation Γ C H s) : SSorted s := by
  obtain ⟨xs,perm,_,fold⟩ := rep.2.2.2.2
  rw [←fold]
  exact replay_sorted Γ C rep.1 xs (fun o ho => rep.2.2.2.1 ((perm.2 o).mp ho))

theorem keys_compatible (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (H K : Set (Op SOp)) (s t : SState)
    (hs : representation Γ C H s) (ht : representation Γ C K t) :
    ∀ x ∈ s, ∀ y ∈ t, sKey x.2.2 = sKey y.2.2 → x = y := by
  intro x hx y hy keys
  obtain ⟨a,ha,ia,rx⟩ := provenance Γ C H s hs x hx
  obtain ⟨b,hb,ib,ry⟩ := provenance Γ C K t ht y hy
  have ids : a.1 = b.1 := by
    by_contra different
    exact keys_distinct Γ C hs.1 a (hs.2.2.2.1 ha) b (ht.2.2.2.1 hb) ia ib different
      (by simpa only [rx,ry,sRecOf] using keys)
  have eq := C.ts_unique (hs.2.2.2.1 ha) (ht.2.2.2.1 hb) ids
  simpa only [rx,ry,eq]

theorem merge_sorted (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (H K : Set (Op SOp)) (l a b : SState)
    (ha : representation Γ C H a) (hb : representation Γ C K b) : SSorted (sMerge l a b) :=
  sMerge_sorted (sorted Γ C H a ha) (sorted Γ C K b hb) (keys_compatible Γ C H K a b ha hb)

/-- Freshness from eligible timestamp uniqueness and actual birth provenance. -/
theorem birth_fresh (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (H : Set (Op SOp)) (s : SState) (rep : representation Γ C H s)
    (e : Op SOp) (eligible : e ∈ C.events) (absent : e ∉ H) :
    ∀ p, born Γ e p → p ∉ s := by
  intro p birth mem
  obtain ⟨⟨o,ho,_,record⟩,_⟩ := (replay_membership Γ C H s rep p).mp mem
  have stamp : o.1 = e.1 := by
    have eq := congrArg Prod.fst (record.symm.trans birth.2)
    exact eq
  exact absent ((C.ts_unique (rep.2.2.2.1 ho) eligible stamp) ▸ ho)

/-- Issued deletion has a visible birth. Closure puts that birth in the causal
past; timestamp uniqueness identifies it with the remainder's actual record. -/
theorem delta_evidence (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (U : Set (Op SOp)) (a B : SState) (e : Op SOp)
    (member : e ∈ U) (eligible : e ∈ C.events) (closed : (scheme Γ C).Closed U)
    (ha : representation Γ C (U \ {e}) a)
    (hB : representation Γ C ((scheme Γ C).Past e \ {e}) B) :
    Certified.DeltaEvidence B.toFinset a.toFinset (born Γ e) (killed e) := by
  constructor
  · intro p birth mem
    exact birth_fresh Γ C _ B hB e eligible (by simp) p birth (List.mem_toFinset.mp mem)
  · intro p hp kill
    obtain ⟨⟨o,ho,ins,rec⟩,noDelete⟩ :=
      (replay_membership Γ C _ a ha p).mp (List.mem_toFinset.mp hp)
    rcases e with ⟨et,er,op⟩
    cases op with
    | ins x pref anchor sd => exact False.elim kill
    | del target =>
      change p.1 = target at kill
      obtain ⟨birth,hbirth,vis,time,_⟩ := ha.1.del_has_ins (et,er,.del target) eligible target rfl
      have stamp : o.1 = target := by simpa only [rec,sRecOf] using kill
      have same := C.ts_unique hbirth (ha.2.2.2.1 ho) (time.trans stamp.symm)
      subst birth
      apply List.mem_toFinset.mpr
      apply (replay_membership Γ C _ B hB p).mpr
      refine ⟨⟨o,⟨Or.inr (.single vis),ho.2⟩,ins,rec⟩,?_⟩
      intro d hd
      have subset := (scheme Γ C).past_subset U (et,er,.del target) closed member
      exact noDelete d ⟨subset hd.1,hd.2⟩

/-- Common membership is reconstructed from two concrete births and the
closed first branch; newborn exclusion uses eligible timestamp freshness. -/
theorem local_evidence (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (E₁ E₂ : Set (Op SOp)) (l B b : SState) (e : Op SOp)
    (member : e ∈ E₁) (absent : e ∉ E₁ ∩ E₂) (eligible : e ∈ C.events)
    (closed : (scheme Γ C).Closed E₁)
    (hl : representation Γ C (E₁ ∩ E₂) l)
    (hB : representation Γ C ((scheme Γ C).Past e \ {e}) B)
    (hb : representation Γ C E₂ b) :
    Certified.LocalEvidence l.toFinset B.toFinset b.toFinset (recordStep Γ e B.toFinset) := by
  constructor
  · intro p hp _ other
    obtain ⟨⟨a,ha,ia,recA⟩,_⟩ :=
      (replay_membership Γ C _ B hB p).mp (List.mem_toFinset.mp hp)
    obtain ⟨⟨b,hb',ib,recB⟩,noDelete⟩ :=
      (replay_membership Γ C _ b hb p).mp (List.mem_toFinset.mp other)
    have same : a = b := C.ts_unique (hB.2.2.2.1 ha) (hb.2.2.2.1 hb')
      (by have stamps := congrArg Prod.fst (recA.symm.trans recB); exact stamps)
    have subset := (scheme Γ C).past_subset E₁ e closed member
    apply List.mem_toFinset.mpr
    apply (replay_membership Γ C _ l hl p).mpr
    refine ⟨⟨a,⟨subset ha.1,same ▸ hb'⟩,ia,recA⟩,?_⟩
    intro d hd
    exact noDelete d hd.2
  · intro p notpast updated base
    rw [recordStep_mem] at updated
    have birth := updated.resolve_right (fun h => notpast h.1)
    exact birth_fresh Γ C _ l hl e eligible absent p birth (List.mem_toFinset.mp base)

/-- Definitionally identify the generic finite merge with the raw normalized
carrier. No theorem about a production datatype's merge VC is used. -/
theorem finite_merge (l a b : Finset SRec) :
    SetMergeAlgebra.merge l a b = Certified.merge l a b := rfl

set_option maxHeartbeats 2000000

theorem expanded_vcs (Γ : OrderedPrefixCode) : ConcreteMRDT.Raw.MergeVCs
    policy (representation Γ) (scheme Γ) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro C E₁ E₂ l a b _ _ _ _ hl ha hb
    simp only [S] at *
    apply eq_of_toFinset (merge_sorted Γ C _ _ l a b ha hb)
      (merge_sorted Γ C _ _ l b a hb ha)
    rw [merge_toFinset Γ C _ _ _ l a b hl ha hb,
      merge_toFinset Γ C _ _ _ l b a hl hb ha,finite_merge,finite_merge]
    exact Certified.comm _ _ _
  · intro C H s _ _ rep
    simp only [S] at *
    apply eq_of_toFinset (merge_sorted Γ C _ _ [] [] s (initial Γ C H s rep) rep)
      (sorted Γ C H s rep)
    rw [merge_toFinset Γ C _ _ _ [] [] s
      (initial Γ C H s rep) (initial Γ C H s rep) rep,finite_merge]
    exact Certified.initial _
  · intro C U s B e _ _ supported closed member _ _ hs hB hD hu
    have he : e ∈ C.events := hu.2.2.2.1 member
    simp only [S] at *
    apply eq_of_toFinset (merge_sorted Γ C _ _ B s (sUpdate Γ B e) hs hD)
      (sorted Γ C U (sUpdate Γ s e) hu)
    rw [merge_toFinset Γ C _ _ _ B s (sUpdate Γ B e) hB hs hD,
      update_toFinset Γ C _ B hB e he (by simp),
      update_toFinset Γ C _ s hs e he (by simp),finite_merge]
    exact Certified.causal _ _ _ _ (born Γ e) (killed e)
      (delta_evidence Γ C U s B e member he closed hs hB)
      (recordStep_mem Γ e B.toFinset) (recordStep_mem Γ e s.toFinset)
  · intro C E₁ E₂ l B t b e ctx member absent hl hB ht hb hD hi hm
    simp only [S] at *
    apply eq_of_toFinset (merge_sorted Γ C _ _ l _ b hi hb)
      (merge_sorted Γ C _ _ B _ _ hm hD)
    rw [merge_toFinset Γ C _ _ _ l _ b hl hi hb,
      merge_toFinset Γ C _ _ _ B _ _ hB hm hD,
      merge_toFinset Γ C _ _ _ B t _ hB ht hD,
      merge_toFinset Γ C _ _ _ l t b hl ht hb]
    have he := hi.2.2.2.1 member
    rw [update_toFinset Γ C _ B hB e he (by simp)]
    simp only [finite_merge]
    exact Certified.local_redistribute _ _ _ _ _ (local_evidence Γ C E₁ E₂ l B b e member
      (fun h => absent h.2) he ctx.closed₁ hl hB hb)
  · intro C E₁ E₂ t₀ t₁ t₂ B e _ _ _ h₀ hB h₁ h₂ hD hi₀ hi₁ hi₂ hm
    simp only [S] at *
    apply eq_of_toFinset (merge_sorted Γ C _ _ _ _ _ hi₁ hi₂)
      (merge_sorted Γ C _ _ B _ _ hm hD)
    rw [merge_toFinset Γ C _ _ _ _ _ _ hi₀ hi₁ hi₂,
      merge_toFinset Γ C _ _ _ B _ _ hB hm hD,
      merge_toFinset Γ C _ _ _ B t₀ _ hB h₀ hD,
      merge_toFinset Γ C _ _ _ B t₁ _ hB h₁ hD,
      merge_toFinset Γ C _ _ _ B t₂ _ hB h₂ hD,
      merge_toFinset Γ C _ _ _ t₀ t₁ t₂ h₀ h₁ h₂]
    simp only [finite_merge]
    exact Certified.shared _ _ _ _ _

#print axioms expanded_vcs
end NeemExpansion.CertifiedRGA
