import Sal.MRDTs.Instances.AegisSheetMaterialisedCertificates
import Sal.MRDTs.Instances.AegisSheetMaterialisedEquivalence
import Sal.MRDTs.Framework.StateGC

/-!
# Retirement of dead identifiers

The materialised sheet stores live data, one position register entry per
identifier ever positioned, and the `known` entry of every identifier ever
introduced. Removals take their tokens with them and, under decision D2, a
purge is an ordinary operation deleting covered versions, so the only
collectible metadata is the `known` entry of an identifier without tokens.
Dropping it needs no evidence: a stale branch on which the identifier is
still live carries its own `known` entry, `merge` unions `known`, and a token
implies its identifier is known, so the identifier is re-learnt exactly when
it is revived. The position register cannot be collected: range resolution
reads a removed identifier's last position
(`RetentionSPOT.dead_position_load_bearing_for_ranges`).
-/

namespace Sal.MRDTs.Instances.AegisSheet.Materialised

open Sal.MRDTs Sal.MRDTs.Foundation

/-- Every token names a known identifier. -/
def TokensKnown (s : MState) : Prop := ∀ x ∈ s.tokens, (x.1, x.2.1) ∈ s.known

/-- Retire the `known` entries of identifiers without tokens. -/
def retire (s : MState) : MState :=
  { s with known := s.known.filter fun k => ∃ x ∈ s.tokens, x.1 = k.1 ∧ x.2.1 = k.2 }

theorem mem_retire_known {s : MState} {k : Axis × StableId} :
    k ∈ (retire s).known ↔ k ∈ s.known ∧ mLive s k.1 k.2 = true := by
  unfold retire mLive
  simp only [Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hk, h⟩; exact ⟨hk, hk, h⟩
  · rintro ⟨hk, _, h⟩; exact ⟨hk, h⟩

/-- A compact state represents a full state when they agree on tokens,
register, cells, and ranges, the compact `known` is a subset missing only
identifiers without tokens, and every token of the full state names a known
identifier. -/
structure Represents (c f : MState) : Prop where
  tokens : c.tokens = f.tokens
  pos : c.pos = f.pos
  cells : c.cells = f.cells
  ranges : c.ranges = f.ranges
  known_sub : c.known ⊆ f.known
  dead_dropped : ∀ k ∈ f.known, k ∉ c.known → ∀ x ∈ f.tokens, ¬ (x.1 = k.1 ∧ x.2.1 = k.2)
  tokens_known : TokensKnown f

theorem Represents.live_eq {c f : MState} (h : Represents c f) (a : Axis) (id : StableId) :
    mLive c a id = mLive f a id := by
  unfold mLive
  rw [h.tokens]
  by_cases hc : (a, id) ∈ c.known
  · rw [decide_eq_true hc, decide_eq_true (h.known_sub hc)]
  · rw [decide_eq_false hc]
    by_cases hf : (a, id) ∈ f.known
    · rw [decide_eq_true hf, Bool.true_and, Bool.false_and]
      rw [eq_comm, Bool.eq_false_iff]
      intro hd
      rw [decide_eq_true_eq] at hd
      obtain ⟨x, hx, h1, h2⟩ := hd
      exact h.dead_dropped (a, id) hf hc x hx ⟨h1, h2⟩
    · rw [decide_eq_false hf]

theorem Represents.liveIds_eq {c f : MState} (h : Represents c f) (a : Axis) :
    mLiveIds c a = mLiveIds f a := by
  unfold mLiveIds
  ext id
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨k, ⟨hk, h1, hl⟩, rfl⟩
    exact ⟨k, ⟨h.known_sub hk, h1, by rw [← h.live_eq]; exact hl⟩, rfl⟩
  · rintro ⟨k, ⟨hk, h1, hl⟩, rfl⟩
    refine ⟨k, ⟨?_, h1, by rw [h.live_eq]; exact hl⟩, rfl⟩
    by_contra hkc
    unfold mLive at hl
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hl
    obtain ⟨_, x, hx, h1', h2'⟩ := hl
    exact h.dead_dropped k hk hkc x hx ⟨h1'.trans h1.symm, h2'⟩

theorem Represents.view_eq {c f : MState} (h : Represents c f) : mview c = mview f := by
  apply view_ext
  · exact h.liveIds_eq .row
  · exact h.liveIds_eq .column
  · show mPositions c .row = mPositions f .row
    unfold mPositions; rw [h.pos]
  · show mPositions c .column = mPositions f .column
    unfold mPositions; rw [h.pos]
  · show mCellValues c = mCellValues f
    funext r col
    unfold mCellValues
    rw [h.live_eq, h.live_eq, h.cells]
  · show mRangeValues c = mRangeValues f
    funext id
    unfold mRangeValues
    rw [h.ranges]

theorem represents_refl_of {f : MState} (hf : TokensKnown f) : Represents f f :=
  ⟨rfl, rfl, rfl, rfl, Finset.Subset.refl _, fun _ _ hn => absurd (by assumption) hn, hf⟩

theorem retire_represents {c f : MState} (h : Represents c f) : Represents (retire c) f where
  tokens := h.tokens
  pos := h.pos
  cells := h.cells
  ranges := h.ranges
  known_sub := fun k hk => h.known_sub (Finset.mem_filter.mp hk).1
  dead_dropped := by
    intro k hk hkc x hx hxk
    by_cases hc : k ∈ c.known
    · apply hkc
      unfold retire
      rw [Finset.mem_filter]
      exact ⟨hc, x, h.tokens ▸ hx, hxk.1, hxk.2⟩
    · exact h.dead_dropped k hk hc x hx hxk
  tokens_known := h.tokens_known

theorem mem_tokAdds_key {e : MEvent} {x : TokenEntry} (hx : x ∈ tokAdds e) :
    (∃ u : AxisUpdate, MEvent.action e = .axis u ∧ u.after.isSome = true ∧ (x.1, x.2.1) = (u.axis, u.id)) ∨
    (∃ u : CellUpdate, MEvent.action e = .cell u ∧
      ((x.1, x.2.1) = (Axis.row, u.row) ∨ (x.1, x.2.1) = (Axis.column, u.column))) := by
  unfold tokAdds at hx
  cases h : MEvent.action e with
  | axis u =>
    simp only [h] at hx
    by_cases hu : u.after.isSome = true
    · rw [if_pos hu, List.mem_singleton] at hx
      subst hx
      exact Or.inl ⟨u, rfl, hu, rfl⟩
    · rw [if_neg hu] at hx
      simp at hx
  | cell u =>
    simp only [h, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact Or.inr ⟨u, rfl, Or.inl rfl⟩
    · exact Or.inr ⟨u, rfl, Or.inr rfl⟩
  | range _ => simp [h] at hx
  | purge _ => simp [h] at hx

theorem mem_knownAdds {e : MEvent} {k : Axis × StableId} :
    k ∈ knownAdds e ↔ ∃ u : AxisUpdate, MEvent.action e = .axis u ∧ k = (u.axis, u.id) := by
  unfold knownAdds
  cases h : MEvent.action e <;> simp

/-- A live axis at the full state has a token, so its identifier is not
dropped by any representing compact state. -/
theorem known_of_live {c f : MState} (h : Represents c f) {a : Axis} {id : StableId}
    (hl : mLive f a id = true) : (a, id) ∈ c.known := by
  unfold mLive at hl
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hl
  obtain ⟨hk, x, hx, h1, h2⟩ := hl
  by_contra hc
  exact h.dead_dropped (a, id) hk hc x hx ⟨h1, h2⟩

theorem update_represents {c f : MState} {e : MEvent} (h : Represents c f)
    (happ : mApplicable e f) : Represents (mupdate c e) (mupdate f e) := by
  have heff := happ.1
  have hlive_cell : ∀ u : CellUpdate, MEvent.action e = .cell u →
      mLive f .row u.row = true ∧ mLive f .column u.column = true := by
    intro u hu
    unfold mEffect at heff
    simp only [hu] at heff
    exact ⟨heff.1, heff.2.1⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [tokens_step, tokens_step, h.tokens]
  · rw [pos_step, pos_step, h.pos]
  · rw [cells_step, cells_step, h.cells]
  · rw [ranges_step, ranges_step, h.ranges]
  · rw [known_step, known_step]
    exact Finset.union_subset_union h.known_sub (Finset.Subset.refl _)
  · intro k hk hkc x hx hxk
    rw [known_step, Finset.mem_union] at hk hkc
    rw [tokens_step] at hx
    simp only [NR.step, tokNR, Finset.mem_union, Finset.mem_filter, List.mem_toFinset] at hx
    have hkf : k ∈ f.known := by
      rcases hk with hk | hk
      · exact hk
      · exact absurd (Or.inr hk) hkc
    have hkc' : k ∉ c.known := fun hc => hkc (Or.inl hc)
    have hka : k ∉ (knownAdds e).toFinset := fun ha => hkc (Or.inr ha)
    rcases hx with ⟨hx, _⟩ | hx
    · exact h.dead_dropped k hkf hkc' x hx hxk
    · rcases mem_tokAdds_key hx with ⟨u, hu, _, hkey⟩ | ⟨u, hu, hkey⟩
      · apply hka
        rw [List.mem_toFinset, mem_knownAdds]
        refine ⟨u, hu, ?_⟩
        rw [← hkey]
        exact Prod.ext hxk.1.symm hxk.2.symm
      · obtain ⟨hr, hc⟩ := hlive_cell u hu
        rcases hkey with hkey | hkey
        · have : k = (Axis.row, u.row) := by rw [← hkey]; exact Prod.ext hxk.1.symm hxk.2.symm
          subst this
          exact hkc' (known_of_live h hr)
        · have : k = (Axis.column, u.column) := by rw [← hkey]; exact Prod.ext hxk.1.symm hxk.2.symm
          subst this
          exact hkc' (known_of_live h hc)
  · intro x hx
    rw [known_step, Finset.mem_union]
    rw [tokens_step] at hx
    simp only [NR.step, tokNR, Finset.mem_union, Finset.mem_filter, List.mem_toFinset] at hx
    rcases hx with ⟨hx, _⟩ | hx
    · exact Or.inl (h.tokens_known x hx)
    · rcases mem_tokAdds_key hx with ⟨u, hu, _, hkey⟩ | ⟨u, hu, hkey⟩
      · right
        rw [List.mem_toFinset, mem_knownAdds]
        exact ⟨u, hu, hkey⟩
      · left
        obtain ⟨hr, hc⟩ := hlive_cell u hu
        rcases hkey with hkey | hkey
        · rw [hkey]; exact known_of_live (represents_refl_of h.tokens_known) hr
        · rw [hkey]; exact known_of_live (represents_refl_of h.tokens_known) hc

theorem mem_mvr_right {α : Type} [DecidableEq α] {l a b : Finset α} {x : α} (hx : x ∈ mvr l a b) :
    x ∈ a ∨ x ∈ b := by
  unfold mvr at hx
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff] at hx
  rcases hx with (⟨⟨_, ha⟩, _⟩ | ⟨ha, _⟩) | ⟨hb, _⟩
  · exact Or.inl ha
  · exact Or.inl ha
  · exact Or.inr hb

theorem merge_represents {cl ca cb l a b : MState} (hl : Represents cl l) (ha : Represents ca a)
    (hb : Represents cb b) : Represents (mmerge cl ca cb) (mmerge l a b) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show mvr cl.tokens ca.tokens cb.tokens = mvr l.tokens a.tokens b.tokens
    rw [hl.tokens, ha.tokens, hb.tokens]
  · show posMerge cl.pos ca.pos cb.pos = posMerge l.pos a.pos b.pos
    rw [hl.pos, ha.pos, hb.pos]
  · show mvr cl.cells ca.cells cb.cells = mvr l.cells a.cells b.cells
    rw [hl.cells, ha.cells, hb.cells]
  · show mvr cl.ranges ca.ranges cb.ranges = mvr l.ranges a.ranges b.ranges
    rw [hl.ranges, ha.ranges, hb.ranges]
  · show cl.known ∪ ca.known ∪ cb.known ⊆ l.known ∪ a.known ∪ b.known
    exact Finset.union_subset_union (Finset.union_subset_union hl.known_sub ha.known_sub) hb.known_sub
  · intro k _ hkc x hx hxk
    have hkc' : k ∉ cl.known ∪ ca.known ∪ cb.known := hkc
    simp only [Finset.mem_union, not_or] at hkc'
    have hx' : x ∈ mvr l.tokens a.tokens b.tokens := hx
    rcases mem_mvr_right hx' with hxa | hxb
    · have hka : k ∈ a.known := by
        have := ha.tokens_known x hxa
        rwa [show (x.1, x.2.1) = k from Prod.ext hxk.1 hxk.2] at this
      exact ha.dead_dropped k hka hkc'.1.2 x hxa hxk
    · have hkb : k ∈ b.known := by
        have := hb.tokens_known x hxb
        rwa [show (x.1, x.2.1) = k from Prod.ext hxk.1 hxk.2] at this
      exact hb.dead_dropped k hkb hkc'.2 x hxb hxk
  · intro x hx
    have hx' : x ∈ mvr l.tokens a.tokens b.tokens := hx
    show (x.1, x.2.1) ∈ l.known ∪ a.known ∪ b.known
    rcases mem_mvr_right hx' with hxa | hxb
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (ha.tokens_known x hxa))
    · exact Finset.mem_union_right _ (hb.tokens_known x hxb)

/-- **Retirement needs no evidence.** The `known` entries of identifiers
without tokens can be dropped at any time; updates issued under `generation`
and three-way merges preserve the representation, and every observation is
preserved. -/
def retirement : StateGCCertificate M generation where
  CompactState := MState
  Evidence := Unit
  Represents := Represents
  EvidenceValid := fun _ _ _ => True
  Compatible := fun _ _ => True
  init := MState.empty
  collect := fun _ c => retire c
  update := mupdate
  merge := mmerge
  query := fun s _ => mview s
  init_represents := represents_refl_of fun x hx => by simp [MState.empty] at hx
  collect_represents := fun h _ => retire_represents h
  update_represents := fun h happ => update_represents h happ
  merge_represents := fun hl ha hb _ => merge_represents hl ha hb
  query_correct := fun h _ => h.view_eq

/-- The collector removes exactly the dead identifiers: an identifier stays
known after retirement iff it is live. -/
theorem retire_keeps_live (s : MState) (k : Axis × StableId) :
    k ∈ (retire s).known ↔ k ∈ s.known ∧ mLive s k.1 k.2 = true :=
  mem_retire_known

#print axioms retirement

end Sal.MRDTs.Instances.AegisSheet.Materialised
