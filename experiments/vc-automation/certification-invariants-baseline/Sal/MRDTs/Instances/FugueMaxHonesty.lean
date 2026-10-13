import Sal.MRDTs.Instances.FugueMaxImplementation

namespace Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax

open Sal.MRDTs.Foundation
open Sal.EmbedRGA (OrderedPrefixCode Side FMEntry PosFMChain TagsOK fmδ)

theorem events_records (ops : List (Op Payload)) :
    (ops.map recordOf).map eventOf = ops := by
  induction ops with
  | nil => rfl
  | cons e ops ih => simp only [List.map_cons, eventOf_recordOf, ih]

theorem rawFold_records (Γ : OrderedPrefixCode) (ops : List (Op Payload)) :
    applySeq (datatype Γ).toUpdateSig (datatype Γ).init ops =
      stateOf Γ (ops.map recordOf) := by
  have h := rawFold_exact Γ (ops.map recordOf)
  rw [events_records] at h
  exact h

private structure MintFacts (Γ : OrderedPrefixCode) (K : KnowM) (g : MRec) : Prop where
  pos : 0 < g.ts
  wf : mIsIns g = true → PosFMChain g.chain ∧ TagsOK g.chain ∧
    (g.chain.map fmδ).sum = g.ts
  right : LinkR Γ K g
  left : LinkL Γ K g
  slc : SLC Γ K g
  rbk : RBk Γ K g

private theorem generated_slc {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) (r t a : ℕ) (ha : a = 0 ∨ a ∈ mMintedIds K) :
    SLC Γ K (mGenInsAfter Γ K r t a) := by
  intro p hop
  cases hs : succOfM Γ K a with
  | none => simp [mGenInsAfter_none hs] at hop
  | some n =>
      cases hr : hasRChildM K a with
      | false => simp [mGenInsAfter_someFalse hs hr] at hop
      | true =>
          rw [mGenInsAfter_someTrue hs hr] at hop ⊢
          have hnp : n = p := by injection hop
          subst p
          exact succ_R_desc_allL inv ha hr hs

private theorem guard_facts {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) (bk : ∀ g ∈ K, RBk Γ K g) (g : MRec)
    (hg : applicable Γ (eventOf g) (stateOf Γ K)) : MintFacts Γ K g := by
  cases hi : mIsIns g with
  | false =>
      obtain ⟨hp, i, heq⟩ := (deletion_issuance_exact inv g hi).mp hg
      refine ⟨hp, by simp [hi], ?_, ?_, ?_, ?_⟩ <;>
        rw [heq] <;> simp [mGenDelAt, LinkR, LinkL, SLC, RBk]
  | true =>
      obtain ⟨hp, ht, i, heq⟩ := (insertion_issuance_exact inv g hi).mp hg
      have ha : mAnchorAt Γ K i = 0 ∨ mAnchorAt Γ K i ∈ mMintedIds K := by
        rcases mAnchorAt_cases Γ K i with hz | hv
        · exact Or.inl hz
        · exact Or.inr (mView_sub_minted Γ K _ hv)
      obtain ⟨_, _, hw, hR, hL⟩ := mGenInsAfter_props Γ inv g.rep hp ht ha
      refine ⟨hp, ?_, ?_, ?_, ?_, ?_⟩
      · rw [heq]
        exact fun _ => hw
      · rw [heq]; exact hR
      · rw [heq]; exact hL
      · rw [heq]; exact generated_slc inv g.rep g.ts _ ha
      · rw [heq]; exact mGenInsAfter_rbk inv bk g.rep ha

private theorem lookup_subset {K L : KnowM}
    (sub : ∀ g ∈ K, g ∈ L)
    (uniq : ∀ g ∈ L, ∀ b ∈ L, g.ts = b.ts → g = b)
    {x : ℕ} (hx : x ∈ mMintedIds K) : mRecOfId L x = mRecOfId K x := by
  obtain ⟨g, hg, hm, hi, ht⟩ := mRecOfId_of_minted hx
  have hxL : x ∈ mMintedIds L :=
    List.mem_map.mpr ⟨g, List.mem_filter.mpr ⟨sub g hm, hi⟩, ht⟩
  obtain ⟨b, hb, hbm, hbi, hbt⟩ := mRecOfId_of_minted hxL
  rw [hb, hg, uniq b hbm g (sub g hm) (hbt.trans ht.symm)]

private theorem chain_subset {K L : KnowM}
    (sub : ∀ g ∈ K, g ∈ L)
    (pos : ∀ g ∈ L, 1 ≤ g.ts)
    (uniq : ∀ g ∈ L, ∀ b ∈ L, g.ts = b.ts → g = b)
    {x : ℕ} (hx : x = 0 ∨ x ∈ mMintedIds K) : mChainOf L x = mChainOf K x := by
  rcases hx with rfl | hx
  · rw [mChainOf_zero pos, mChainOf_zero (fun g hg => pos g (sub g hg))]
  · simp [mChainOf, lookup_subset sub uniq hx]

/-- Mint provenance establishes all three existing non-interleaving invariant
bundles on every causally closed enumeration. This derives them from the
framework's issuance evidence, without assuming `MaxReach`.

Induction is on the finite enumeration length: each event's strict causal
past is smaller. Its own issuer establishes mint facts there, and immutable
birth lookup transports those facts into the larger event set. -/
theorem invariants_of_mint {Γ : OrderedPrefixCode}
    (C : Configuration (datatype Γ))
    (hmint : MintHonest (datatype Γ) (applicable Γ) C)
    (htrans : Transitive C.vis) (hirr : ∀ e, ¬ C.vis e e) :
    ∀ ops : List (Op Payload), ops.Nodup →
      (∀ e ∈ ops, e ∈ C.events) →
      (∀ a b, C.vis a b → b ∈ ops → a ∈ ops) →
      KInv Γ (ops.map recordOf) ∧
      (∀ g ∈ ops.map recordOf, SLC Γ (ops.map recordOf) g) ∧
      (∀ g ∈ ops.map recordOf, RBk Γ (ops.map recordOf) g) := by
  intro ops
  induction n : ops.length using Nat.strong_induction_on generalizing ops with
  | h n ih =>
      intro hnd hsub hclosed
      have localFacts : ∀ g ∈ ops.map recordOf, ∃ past : KnowM,
          (∀ a ∈ past, a ∈ ops.map recordOf) ∧ KInv Γ past ∧ MintFacts Γ past g := by
        intro g hg
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hg
        obtain ⟨π, hp, _, hg⟩ := hmint e (hsub e he)
        have hπsub : ∀ a ∈ π, a ∈ ops := by
          intro a ha
          exact hclosed a e ((hp.2 a).mp ha).2 he
        have hnot : e ∉ π := fun hem => hirr e ((hp.2 e).mp hem).2
        have hle := (List.subperm_of_subset (List.nodup_cons.mpr ⟨hnot, hp.1⟩)
          (show e :: π ⊆ ops from by
            intro a ha
            rcases List.mem_cons.mp ha with rfl | ha
            · exact he
            · exact hπsub a ha)).length_le
        have hlt : π.length < ops.length := by simpa using hle
        have hπclosed : ∀ a b, C.vis a b → b ∈ π → a ∈ π := by
          intro a b hab hb
          have hb' := (hp.2 b).mp hb
          exact (hp.2 a).mpr ⟨hsub a (hclosed a b hab (hπsub b hb)), htrans hab hb'.2⟩
        obtain ⟨inv, slc, bk⟩ := ih π.length (by omega) π rfl hp.1
          (fun a ha => ((hp.2 a).mp ha).1) hπclosed
        rw [rawFold_records] at hg
        refine ⟨π.map recordOf, ?_, inv, guard_facts inv bk (recordOf e) ?_⟩
        · intro a ha
          obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
          exact List.mem_map.mpr ⟨b, hπsub b hb, rfl⟩
        · simpa using hg
      have pos : ∀ g ∈ ops.map recordOf, 1 ≤ g.ts := by
        intro g hg
        obtain ⟨_, _, _, facts⟩ := localFacts g hg
        exact facts.pos
      have uniq : ∀ g ∈ ops.map recordOf, ∀ b ∈ ops.map recordOf,
          g.ts = b.ts → g = b := by
        intro g hg b hb ht
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hg
        obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hb
        exact congrArg recordOf (C.replayContext.ts_unique (hsub e he) (hsub f hf) ht)
      have transported : ∀ g ∈ ops.map recordOf, MintFacts Γ (ops.map recordOf) g := by
        intro g hg
        obtain ⟨past, sub, inv, facts⟩ := localFacts g hg
        have hchain := fun y hy => chain_subset sub pos uniq (x := y) hy
        have hmem : ∀ y ∈ mMintedIds past, y ∈ mMintedIds (ops.map recordOf) := by
          intro y hy
          obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
          exact List.mem_map.mpr ⟨a,
            List.mem_filter.mpr ⟨sub a (List.mem_filter.mp ha).1, (List.mem_filter.mp ha).2⟩, rfl⟩
        exact ⟨facts.pos, facts.wf, linkR_transport facts.right hchain hmem,
          linkL_transport facts.left hchain hmem, slc_transport facts.slc facts.left hchain,
          rbk_transport facts.rbk inv facts.right pos hchain hmem
            (fun y hy => lookup_subset sub uniq hy)⟩
      exact ⟨⟨pos, fun g hg b hb _ _ ht => uniq g hg b hb ht,
        fun g hg => (transported g hg).wf, fun g hg => (transported g hg).right,
        fun g hg => (transported g hg).left⟩,
        fun g hg => (transported g hg).slc, fun g hg => (transported g hg).rbk⟩

#print axioms invariants_of_mint

private theorem event_past {Γ : OrderedPrefixCode}
    (C : Configuration (datatype Γ))
    (hmint : MintHonest (datatype Γ) (applicable Γ) C)
    (htrans : Transitive C.vis) (e : Op Payload) (he : e ∈ C.events) :
    ∃ π : List (Op Payload), listPermOf π {a ∈ C.events | C.vis a e} ∧
      KInv Γ (π.map recordOf) ∧ MintFacts Γ (π.map recordOf) (recordOf e) ∧
      applicable Γ (eventOf (recordOf e)) (stateOf Γ (π.map recordOf)) := by
  obtain ⟨π, hp, _, hg⟩ := hmint e he
  obtain ⟨inv, _, bk⟩ := invariants_of_mint C hmint htrans
    (fun a ha => Nat.lt_irrefl a.1 (C.causal_mono ha)) π hp.1
    (fun a ha => ((hp.2 a).mp ha).1) (by
      intro a b hab hb
      exact (hp.2 a).mpr ⟨C.vis_src hab, htrans hab ((hp.2 b).mp hb).2⟩)
  rw [rawFold_records] at hg
  have hg' : applicable Γ (eventOf (recordOf e)) (stateOf Γ (π.map recordOf)) := by
    simpa using hg
  exact ⟨π, hp, inv, guard_facts inv bk (recordOf e) hg', hg'⟩

theorem event_chain_of_mint {Γ : OrderedPrefixCode}
    (C : Configuration (datatype Γ))
    (hmint : MintHonest (datatype Γ) (applicable Γ) C)
    (htrans : Transitive C.vis) (e : Op Payload) (he : e ∈ C.events) :
    0 < e.1 ∧ (mIsIns (recordOf e) = true →
      PosFMChain e.2.2.chain ∧ TagsOK e.2.2.chain ∧
      (e.2.2.chain.map fmδ).sum = e.1) := by
  obtain ⟨_, _, _, facts, _⟩ := event_past C hmint htrans e he
  exact ⟨facts.pos, facts.wf⟩

/-- Every non-sentinel delete observes its birth. The explicit sentinel case
preserves the original generator's total, no-op out-of-range behavior. -/
theorem delete_birth_of_mint {Γ : OrderedPrefixCode}
    (C : Configuration (datatype Γ))
    (hmint : MintHonest (datatype Γ) (applicable Γ) C)
    (htrans : Transitive C.vis) (e : Op Payload) (he : e ∈ C.events)
    (x : ℕ) (hx : e.2.2.op = .del x) :
    x = 0 ∨ ∃ a ∈ C.events, C.vis a e ∧ mIsIns (recordOf a) = true ∧ a.1 = x := by
  by_cases hz : x = 0
  · exact Or.inl hz
  right
  obtain ⟨π, hp, inv, _, hg⟩ := event_past C hmint htrans e he
  have hi : mIsIns (recordOf e) = false := by simp [mIsIns, recordOf, hx]
  obtain ⟨_, i, hg⟩ := (deletion_issuance_exact inv (recordOf e) hi).mp hg
  have htarget : x = (mView Γ (π.map recordOf)).getD i 0 := by
    have h := congrArg MRec.op hg
    change e.2.2.op = .del _ at h
    rw [hx] at h
    injection h
  have hxview : x ∈ mView Γ (π.map recordOf) := by
    by_cases hlt : i < (mView Γ (π.map recordOf)).length
    · rw [List.getD_eq_getElem _ _ hlt] at htarget
      rw [htarget]
      exact List.getElem_mem hlt
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hlt)] at htarget
      exact False.elim (hz htarget)
  obtain ⟨g, hg, ht⟩ := List.mem_map.mp (mView_sub_minted Γ _ _ hxview)
  have hgi := (List.mem_filter.mp hg).2
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hg).1
  exact ⟨a, ((hp.2 a).mp ha).1, ((hp.2 a).mp ha).2, hgi, ht⟩

theorem noninterleaving_of_mint {Γ : OrderedPrefixCode}
    (C : Configuration (datatype Γ))
    (hmint : MintHonest (datatype Γ) (applicable Γ) C)
    (htrans : Transitive C.vis)
    (ops : List (Op Payload)) (hnd : ops.Nodup)
    (hsub : ∀ e ∈ ops, e ∈ C.events)
    (hclosed : ∀ a b, C.vis a b → b ∈ ops → a ∈ ops) :
    MaxNonInterleavingM Γ (ops.map recordOf) := by
  obtain ⟨inv, slc, bk⟩ := invariants_of_mint C hmint htrans
    (fun a ha => Nat.lt_irrefl a.1 (C.causal_mono ha)) ops hnd hsub hclosed
  exact ⟨forwardNIM_of_inv inv slc, backwardNIM_of_inv inv slc bk,
    sameOriginLowFirst_of_KInv inv⟩

#print axioms noninterleaving_of_mint

end Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax
