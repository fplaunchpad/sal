import LeanProofs_no_spec_non_comm.Implementations.EmbeddedRGA.Replay
import Artifact.MRDTs.Paper1.CertifiedClosedExecution

/-!
# Embedded RGA: the replay order, the representation, and the join

The representation the execution induction runs on is the artifact's: a
state **is** a causal replay of an event set, `Replay`.

`birthOrder` is the replay order, and it is the reason this row needs an
**event**-level `EventOrder` rather than the lift of an operation `rc`: the
only pair it has to order is an insertion and the deletion naming it, and
that pair is identified by a timestamp, not by the two operations.
`Negative.lean` is exactly the observation that no operation-level `rc` can
express this.

`canonical_of_replay` and `replay_of_canonical` move between the
framework's `IsCanonicalState` at that order and `Replay`. The first
direction needs `loOn_implies_vis`, that every replay-order edge between
observed events is causal; the second needs `birthFirst_of_lo`, that a
replay-order-respecting enumeration puts a birth before its deletion, and
then convergence identifies the two folds.

`replay_merge` is the join. Both sides are sorted, so by `sortedDown_ext`
it is a membership calculation, and `merge_logic` is its propositional
core: seven implications relating the three event sets, each one either
`vis`-closure of a branch, uniqueness of a writer, or inclusion of the
intersection. No five-VC detour is needed, because the representation is
concrete enough to compute with directly.
-/

namespace LeanProofs.NoSpecNonComm.Implementations.EmbeddedRGA

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface

variable {Γ : Scheme} {α : Type} [DecidableEq α] {Q : QueryOf Γ α}

theorem merge_logic {W₀ W₁ W₂ D₀ D₁ D₂ : Prop}
    (r1 : W₁ → W₂ → W₀) (r2 : D₁ → (W₁ ∨ W₂) → W₁) (r3 : D₂ → (W₁ ∨ W₂) → W₂)
    (r4a : D₀ → D₁) (r4b : D₀ → D₂) (r5a : W₀ → W₁) (r5b : W₀ → W₂) :
    (((W₁ ∧ ¬D₁) ∧ ((W₂ ∧ ¬D₂) ∨ ¬(W₀ ∧ ¬D₀))) ∨
      ((W₂ ∧ ¬D₂) ∧ ¬(W₀ ∧ ¬D₀) ∧ ¬(W₁ ∧ ¬D₁)))
      ↔ ((W₁ ∨ W₂) ∧ ¬D₁ ∧ ¬D₂) := by
  classical
  constructor
  · rintro (⟨⟨hw1, hnd1⟩, hr⟩ | ⟨⟨hw2, hnd2⟩, hnl0, hnl1⟩)
    · rcases hr with ⟨hw2, hnd2⟩ | hnl0
      · exact ⟨Or.inl hw1, hnd1, hnd2⟩
      · refine ⟨Or.inl hw1, hnd1, fun hd2 => ?_⟩
        have hw2 := r3 hd2 (Or.inl hw1)
        have hw0 := r1 hw1 hw2
        by_cases hd0 : D₀
        · exact hnd1 (r4a hd0)
        · exact hnl0 ⟨hw0, hd0⟩
    · refine ⟨Or.inr hw2, fun hd1 => ?_, hnd2⟩
      have hw1 := r2 hd1 (Or.inr hw2)
      have hw0 := r1 hw1 hw2
      by_cases hd0 : D₀
      · exact hnd2 (r4b hd0)
      · exact hnl0 ⟨hw0, hd0⟩
  · rintro ⟨hw, hnd1, hnd2⟩
    by_cases hw1 : W₁
    · refine Or.inl ⟨⟨hw1, hnd1⟩, ?_⟩
      by_cases hl0 : W₀ ∧ ¬D₀
      · exact Or.inl ⟨r5b hl0.1, hnd2⟩
      · exact Or.inr hl0
    · have hw2 : W₂ := hw.resolve_left hw1
      exact Or.inr ⟨⟨hw2, hnd2⟩, fun hl0 => hw1 (r5a hl0.1), fun hl1 => hw1 hl1.1⟩


/-- **The replay order the execution induction runs at.** An insertion
precedes the deletion that names it, and nothing else is ordered.

This is an **event**-level order, not the lift of an operation `rc`,
because the pair it has to order is identified by a timestamp rather than
by the two operations. `Negative.lean` is exactly the observation that no
operation-level `rc` can express it. -/
def birthOrder : Op (AppOp Γ α) → Op (AppOp Γ α) → OrderResult := fun a b =>
  match a.op, b.op with
  | .ins _ _ _ _, .del t => if a.time = t then .Fst_then_snd else .Either
  | .del t, .ins _ _ _ _ => if b.time = t then .Snd_then_fst else .Either
  | _, _ => .Either

def birthEventOrder : EventOrder (Dα Γ α Q).toMRDTSig.toUpdateSig := ⟨birthOrder⟩

attribute [local instance] birthEventOrder

theorem birth_before {e f : Op (AppOp Γ α)} {v : α} {p : List Γ.Sym} {an : Nat}
    {g : Γ.Arg} (hope : e.op = AppOp.ins v p an g) (hopf : f.op = AppOp.del e.time) :
    @UpdateSig.replayBefore (Dα Γ α Q).toMRDTSig.toUpdateSig birthEventOrder e f := by
  show birthOrder e f = OrderResult.Fst_then_snd
  simp [birthOrder, hope, hopf]

/-- Only a birth and its own deletion are ordered. -/
theorem birthOrder_shape {a b : Op (AppOp Γ α)}
    (h : birthOrder a b = OrderResult.Fst_then_snd) :
    (∃ v p an g, a.op = AppOp.ins v p an g) ∧ b.op = AppOp.del a.time := by
  unfold birthOrder at h
  cases hopa : a.op with
  | ins v p an g =>
    cases hopb : b.op with
    | ins v' p' an' g' => rw [hopa, hopb] at h; exact absurd h (by simp)
    | del t =>
      rw [hopa, hopb] at h
      simp only at h
      split_ifs at h with ht
      exact ⟨⟨v, p, an, g, rfl⟩, by rw [ht]⟩
  | del t =>
    cases hopb : b.op with
    | ins v' p' an' g' =>
      rw [hopa, hopb] at h
      simp only at h
      split_ifs at h <;> exact absurd h (by simp)
    | del t' => rw [hopa, hopb] at h; exact absurd h (by simp)

/-- **Every replay-order edge between observed events is a `vis` edge.**
The concurrent disjunct cannot fire: the only ordered pairs are a birth and
its deletion, and `DelBorn` makes those causally related. -/
theorem loOn_implies_vis {C : Ctx (Dα Γ α Q)} (hb : DelBorn C) {E : Set (Op (AppOp Γ α))}
    {a b : Op (AppOp Γ α)} (ha : a ∈ C.events) (hbb : b ∈ C.events)
    (h : @loOn (Dα Γ α Q).toMRDTSig.toUpdateSig birthEventOrder C E a b) : C.vis a b := by
  rcases h with ⟨hv, -⟩ | ⟨hnab, -, hrb, -⟩
  · exact hv
  · obtain ⟨-, hdel⟩ := birthOrder_shape hrb
    obtain ⟨g, hg, hgt, -, hvis⟩ := hb b hbb a.time hdel
    have : g = a := by
      by_contra hne
      exact time_ne hg ha hne hgt
    exact absurd (this ▸ hvis) hnab

/-- A `lo`-respecting enumeration puts a birth before its deletion. -/
theorem birthFirst_of_lo {C : Ctx (Dα Γ α Q)} (hb : DelBorn C) {E : Set (Op (AppOp Γ α))}
    {xs : List (Op (AppOp Γ α))} (hsup : ∀ e ∈ xs, e ∈ C.events)
    (hord : respects xs (@loOn (Dα Γ α Q).toMRDTSig.toUpdateSig birthEventOrder C E)) :
    BirthFirst xs := by
  rintro pre e post rfl ⟨v, p, an, g, hope⟩ ⟨f, hf, hfop⟩
  have hfe : f ∈ pre ++ e :: post := List.mem_append_left _ hf
  have hee : e ∈ pre ++ e :: post := List.mem_append_right _ List.mem_cons_self
  have hedge : @loOn (Dα Γ α Q).toMRDTSig.toUpdateSig birthEventOrder C E e f := by
    obtain ⟨g, hg, hgt, -, hvis⟩ := hb f (hsup f hfe) e.time hfop
    have hge : g = e := by
      by_contra hne
      exact time_ne hg (hsup e hee) hne hgt
    exact Or.inl ⟨hge ▸ hvis, Or.inl (birth_before hope hfop)⟩
  exact (List.pairwise_append.mp hord).2.2 f hf e List.mem_cons_self hedge

/-- A `vis`-respecting enumeration puts a birth before its deletion. -/
theorem birthFirst_of_vis {C : Ctx (Dα Γ α Q)} (hb : DelBorn C)
    {xs : List (Op (AppOp Γ α))} (hsup : ∀ e ∈ xs, e ∈ C.events)
    (hord : respects xs C.vis) : BirthFirst xs := by
  rintro pre e post rfl ⟨v, p, an, g, hope⟩ ⟨f, hf, hfop⟩
  have hfe : f ∈ pre ++ e :: post := List.mem_append_left _ hf
  have hee : e ∈ pre ++ e :: post := List.mem_append_right _ List.mem_cons_self
  obtain ⟨g, hg, hgt, -, hvis⟩ := hb f (hsup f hfe) e.time hfop
  have hge : g = e := by
    by_contra hne
    exact time_ne hg (hsup e hee) hne hgt
  exact (List.pairwise_append.mp hord).2.2 f hf e List.mem_cons_self (hge ▸ hvis)

/-! ## The representation -/

/-- **`s` is a causal replay of `H`.** This is the artifact's
representation, and the predicate the join induction runs on. -/
def Replay (C : Ctx (Dα Γ α Q)) (H : Set (Op (AppOp Γ α))) (s : St Γ α) : Prop :=
  H ⊆ C.events ∧ ∃ xs, listPermOf xs H ∧ respects xs C.vis ∧ xs.foldl step [] = s

theorem replay_exists {C : Ctx (Dα Γ α Q)} (hvs : VisStrict (Dα Γ α Q) C) {H : Set (Op (AppOp Γ α))}
    (hsup : H ⊆ C.events) {π : List (Op (AppOp Γ α))} (hp : listPermOf π H) :
    ∃ s, Replay C H s := by
  obtain ⟨ρ, hperm, hr⟩ := exists_respecting_perm (R := fun a b : Op (AppOp Γ α) => C.vis a b)
    (fun hab hbc => hvs.1 hab hbc) hvs.2 π
  exact ⟨ρ.foldl step [], hsup,
    ρ, ⟨hperm.nodup hp.1, fun a => (hperm.mem_iff (a := a)).symm.trans (hp.2 a)⟩, hr, rfl⟩

theorem canonical_of_replay {C : Ctx (Dα Γ α Q)} (hb : DelBorn C) {H : Set (Op (AppOp Γ α))}
    {s : St Γ α} (h : Replay C H s) :
    @IsCanonicalState (Dα Γ α Q).toMRDTSig.toUpdateSig birthEventOrder C H s := by
  obtain ⟨hsup, xs, hp, hord, hf⟩ := h
  refine ⟨xs, hp, ?_, hf⟩
  refine hord.imp_of_mem (fun {a b} ha hbm hno hedge => ?_)
  exact hno (loOn_implies_vis hb (hsup ((hp.2 b).mp hbm)) (hsup ((hp.2 a).mp ha)) hedge)

theorem replay_of_canonical {C : Ctx (Dα Γ α Q)} (hc : CoordHonest C) (hb : DelBorn C)
    (hvs : VisStrict (Dα Γ α Q) C) {H : Set (Op (AppOp Γ α))} {s : St Γ α} (hsup : H ⊆ C.events)
    (h : @IsCanonicalState (Dα Γ α Q).toMRDTSig.toUpdateSig birthEventOrder C H s) :
    Replay C H s := by
  obtain ⟨xs, hp, hord, hf⟩ := h
  obtain ⟨ρ, hperm, hr⟩ := exists_respecting_perm (R := fun a b : Op (AppOp Γ α) => C.vis a b)
    (fun hab hbc => hvs.1 hab hbc) hvs.2 xs
  have hpρ : listPermOf ρ H :=
    ⟨hperm.nodup hp.1, fun a => (hperm.mem_iff (a := a)).symm.trans (hp.2 a)⟩
  refine ⟨hsup, ρ, hpρ, hr, ?_⟩
  rw [← hf]
  exact fold_congr hc hpρ.1 hp.1 (fun e he => hsup ((hpρ.2 e).mp he))
    (fun e he => hsup ((hp.2 e).mp he))
    (birthFirst_of_vis hb (fun e he => hsup ((hpρ.2 e).mp he)) hr)
    (birthFirst_of_lo hb (fun e he => hsup ((hp.2 e).mp he)) hord)
    (fun e => (hpρ.2 e).trans (hp.2 e).symm)

/-! ## The join -/

/-- `H` deletes identity `t`. -/
def DeletesS (H : Set (Op (AppOp Γ α))) (t : Nat) : Prop := ∃ f ∈ H, f.op = AppOp.del t

/-- The records a replay of `H` leaves live. -/
def LiveS (H : Set (Op (AppOp Γ α))) (z : Record Γ α) : Prop :=
  (∃ e ∈ H, Writes e z) ∧ ¬ DeletesS H z.1

theorem valid_of_replay {C : Ctx (Dα Γ α Q)} (hc : CoordHonest C) {H : Set (Op (AppOp Γ α))}
    {s : St Γ α} (h : Replay C H s) : Valid C s := by
  obtain ⟨hsup, xs, hp, -, rfl⟩ := h
  exact valid_fold hc (fun e he => hsup ((hp.2 e).mp he))

theorem replay_mem {C : Ctx (Dα Γ α Q)} (hb : DelBorn C) {H : Set (Op (AppOp Γ α))} {s : St Γ α}
    (h : Replay C H s) : ∀ z, z ∈ s ↔ LiveS H z := by
  obtain ⟨hsup, xs, hp, hord, rfl⟩ := h
  have hsx : ∀ e ∈ xs, e ∈ C.events := fun e he => hsup ((hp.2 e).mp he)
  intro z
  rw [fold_live (C := C) hp.1 hsx (birthFirst_of_vis hb hsx hord) z]
  constructor
  · rintro ⟨⟨u, hu, hwu⟩, hnd⟩
    exact ⟨⟨u, (hp.2 u).mp hu, hwu⟩, fun ⟨f, hf, hfop⟩ => hnd ⟨f, (hp.2 f).mpr hf, hfop⟩⟩
  · rintro ⟨⟨u, hu, hwu⟩, hnd⟩
    exact ⟨⟨u, (hp.2 u).mpr hu, hwu⟩, fun ⟨f, hf, hfop⟩ => hnd ⟨f, (hp.2 f).mp hf, hfop⟩⟩

/-- Two observed insertions writing the same identity are the same event. -/
theorem writer_unique {C : Ctx (Dα Γ α Q)} {z : Record Γ α} {e g : Op (AppOp Γ α)}
    (he : e ∈ C.events) (hg : g ∈ C.events) (hw : Writes e z) (hgt : g.time = z.1) :
    g = e := by
  by_contra hne
  exact time_ne hg he hne (hgt.trans (writes_fst hw))

theorem mem_ids_iff {C : Ctx (Dα Γ α Q)} (hb : DelBorn C) {H : Set (Op (AppOp Γ α))} {s : St Γ α}
    (h : Replay C H s) {z : Record Γ α} {e : Op (AppOp Γ α)} (he : e ∈ C.events)
    (hw : Writes e z) : z.1 ∈ ids s ↔ LiveS H z := by
  constructor
  · intro hin
    simp only [ids, List.mem_map] at hin
    obtain ⟨w, hwm, hwt⟩ := hin
    obtain ⟨⟨u, hu, hwu⟩, hnd⟩ := (replay_mem hb h w).mp hwm
    have hue : u = e := writer_unique he (h.1 hu) hw ((writes_fst hwu).symm.trans hwt)
    have : w = z := by
      have := writes_funct (hue ▸ hwu) hw
      exact this
    exact this ▸ ⟨⟨u, hu, hwu⟩, hnd⟩
  · intro hlive
    have hzs : z ∈ s := (replay_mem hb h z).mpr hlive
    exact List.mem_map_of_mem hzs

theorem merge_mem {C : Ctx (Dα Γ α Q)} (hb : DelBorn C)
    {E₁ E₂ : Set (Op (AppOp Γ α))} {l a b : St Γ α}
    (hs₁ : E₁ ⊆ C.events) (hs₂ : E₂ ⊆ C.events)
    (hcl₁ : ∀ x y, C.vis x y → y ∈ E₁ → x ∈ E₁)
    (hcl₂ : ∀ x y, C.vis x y → y ∈ E₂ → x ∈ E₂)
    (hl : Replay C (E₁ ∩ E₂) l) (ha : Replay C E₁ a) (hb2 : Replay C E₂ b) :
    ∀ z, z ∈ mergeState l a b ↔ LiveS (E₁ ∪ E₂) z := by
  classical
  intro z
  have hsplit : z ∈ mergeState l a b ↔
      (z ∈ a ∧ (z.1 ∈ ids b ∨ z.1 ∉ ids l)) ∨
        (z ∈ b ∧ (z.1 ∉ ids l ∧ z.1 ∉ ids a)) := by
    simp only [mergeState, mem_mergeDown, List.mem_filter, Bool.or_eq_true,
      Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      decide_eq_false_iff_not]
  rw [hsplit]
  by_cases hwit : ∃ e ∈ C.events, Writes e z
  · obtain ⟨e, he, hw⟩ := hwit
    rw [replay_mem hb ha z, replay_mem hb hb2 z,
      mem_ids_iff hb hb2 he hw, mem_ids_iff hb hl he hw, mem_ids_iff hb ha he hw]
    have hunion : LiveS (E₁ ∪ E₂) z ↔
        (((∃ u ∈ E₁, Writes u z) ∨ (∃ u ∈ E₂, Writes u z)) ∧
          ¬ DeletesS E₁ z.1 ∧ ¬ DeletesS E₂ z.1) := by
      simp only [LiveS, DeletesS, Set.mem_union]
      constructor
      · rintro ⟨⟨u, hu | hu, hwu⟩, hnd⟩
        · exact ⟨Or.inl ⟨u, hu, hwu⟩, fun ⟨f, hf, hfop⟩ => hnd ⟨f, Or.inl hf, hfop⟩,
            fun ⟨f, hf, hfop⟩ => hnd ⟨f, Or.inr hf, hfop⟩⟩
        · exact ⟨Or.inr ⟨u, hu, hwu⟩, fun ⟨f, hf, hfop⟩ => hnd ⟨f, Or.inl hf, hfop⟩,
            fun ⟨f, hf, hfop⟩ => hnd ⟨f, Or.inr hf, hfop⟩⟩
      · rintro ⟨hw', hn1, hn2⟩
        refine ⟨?_, ?_⟩
        · rcases hw' with ⟨u, hu, hwu⟩ | ⟨u, hu, hwu⟩
          · exact ⟨u, Or.inl hu, hwu⟩
          · exact ⟨u, Or.inr hu, hwu⟩
        · rintro ⟨f, hf | hf, hfop⟩
          · exact hn1 ⟨f, hf, hfop⟩
          · exact hn2 ⟨f, hf, hfop⟩
    rw [hunion]
    refine merge_logic ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rintro ⟨u₁, hu₁, hw₁⟩ ⟨u₂, hu₂, hw₂⟩
      have : u₂ = u₁ := writer_unique (hs₁ hu₁) (hs₂ hu₂) hw₁ (writes_fst hw₂).symm
      exact ⟨u₁, ⟨hu₁, this ▸ hu₂⟩, hw₁⟩
    · rintro ⟨f, hf, hfop⟩ -
      obtain ⟨g, hg, hgt, -, hvis⟩ := hb f (hs₁ hf) z.1 hfop
      have hge : g = e := writer_unique he hg hw hgt
      exact ⟨e, hcl₁ e f (hge ▸ hvis) hf, hw⟩
    · rintro ⟨f, hf, hfop⟩ -
      obtain ⟨g, hg, hgt, -, hvis⟩ := hb f (hs₂ hf) z.1 hfop
      have hge : g = e := writer_unique he hg hw hgt
      exact ⟨e, hcl₂ e f (hge ▸ hvis) hf, hw⟩
    · rintro ⟨f, hf, hfop⟩; exact ⟨f, hf.1, hfop⟩
    · rintro ⟨f, hf, hfop⟩; exact ⟨f, hf.2, hfop⟩
    · rintro ⟨u, hu, hwu⟩; exact ⟨u, hu.1, hwu⟩
    · rintro ⟨u, hu, hwu⟩; exact ⟨u, hu.2, hwu⟩
  · constructor
    · rintro (⟨hza, -⟩ | ⟨hzb, -⟩)
      · obtain ⟨⟨u, hu, hwu⟩, -⟩ := (replay_mem hb ha z).mp hza
        exact (hwit ⟨u, hs₁ hu, hwu⟩).elim
      · obtain ⟨⟨u, hu, hwu⟩, -⟩ := (replay_mem hb hb2 z).mp hzb
        exact (hwit ⟨u, hs₂ hu, hwu⟩).elim
    · rintro ⟨⟨u, hu, hwu⟩, -⟩
      rcases hu with hu | hu
      · exact (hwit ⟨u, hs₁ hu, hwu⟩).elim
      · exact (hwit ⟨u, hs₂ hu, hwu⟩).elim

/-- **The join.** Merging replays of `E₁ ∩ E₂`, `E₁` and `E₂` gives a
replay of `E₁ ∪ E₂`. Both sides are sorted and `merge_mem` gives them the
same members. -/
theorem replay_merge {C : Ctx (Dα Γ α Q)} (hc : CoordHonest C) (hb : DelBorn C)
    (hvs : VisStrict (Dα Γ α Q) C) {E₁ E₂ : Set (Op (AppOp Γ α))} {l a b : St Γ α}
    (hs₁ : E₁ ⊆ C.events) (hs₂ : E₂ ⊆ C.events)
    (hcl₁ : ∀ x y, C.vis x y → y ∈ E₁ → x ∈ E₁)
    (hcl₂ : ∀ x y, C.vis x y → y ∈ E₂ → x ∈ E₂)
    (hl : Replay C (E₁ ∩ E₂) l) (ha : Replay C E₁ a) (hb2 : Replay C E₂ b) :
    Replay C (E₁ ∪ E₂) (mergeState l a b) := by
  obtain ⟨xs, hpx, -, -⟩ := ha.2
  obtain ⟨ys, hpy, -, -⟩ := hb2.2
  have hsU : E₁ ∪ E₂ ⊆ C.events := by
    rintro x (hx | hx)
    · exact hs₁ hx
    · exact hs₂ hx
  obtain ⟨t, ht⟩ := replay_exists hvs hsU
    (listPermOf_union (D := (Dα Γ α Q).toMRDTSig.toUpdateSig) hpx hpy)
  have heq : t = mergeState l a b := by
    refine sortedDown_ext (valid_of_replay hc ht).1
      (valid_merge hc (valid_of_replay hc hl) (valid_of_replay hc ha)
        (valid_of_replay hc hb2)).1 (fun z => ?_)
    rw [replay_mem hb ht z, merge_mem hb hs₁ hs₂ hcl₁ hcl₂ hl ha hb2 z]
  exact heq ▸ ht

/-- **The join, as the framework's execution induction consumes it.** -/
theorem closedJoinAt {C : Ctx (Dα Γ α Q)} (hc : CoordHonest C) (hb : DelBorn C) :
    @CertifiedClosedExecution.ClosedJoinAt (Dα Γ α Q).toMRDTSig birthEventOrder C := by
  intro E₁ E₂ l a b htr hirr hsup₁ hsup₂ hcl₁ hcl₂ hl ha hb2
  have hvs : VisStrict (Dα Γ α Q) C := ⟨fun hab hbc => htr hab hbc, hirr⟩
  exact canonical_of_replay hb (replay_merge hc hb hvs hsup₁ hsup₂ hcl₁ hcl₂
    (replay_of_canonical hc hb hvs (fun x hx => hsup₁ x hx.1) hl)
    (replay_of_canonical hc hb hvs hsup₁ ha)
    (replay_of_canonical hc hb hvs hsup₂ hb2))

end LeanProofs.NoSpecNonComm.Implementations.EmbeddedRGA
