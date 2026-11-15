import LeanProofs.Implementations.RemoveWinsSet.Laws
import LeanProofs.Soundness.LinearExtension

/-!
# The remove-wins set: clause 1

What a canonical state is, the issuance guard, and the join lemma proved
directly at mint-honest configurations.
-/

namespace LeanProofs.Implementations.RemoveWinsSet

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.Interface

variable {A : Type} [DecidableEq A] [Fintype A]

/-- The replay order of Section 4: `rc`, lifted to events. -/
noncomputable local instance rcOrder :
    EventOrder (D A).toMRDTSig.toUpdateSig := Interface.rcOrder (D A)

@[simp] theorem replayBefore_iff (a b : (D A).Event) :
    (D A).toMRDTSig.toUpdateSig.replayBefore a b
      ↔ ∃ x, a.op = AppOp.add x ∧ b.op = AppOp.remove x := by
  refine Iff.trans ?_ (rcBefore_iff a.op b.op)
  exact @OperationPolicy.lift_replayOrder_iff (D A).toMRDTSig.toUpdateSig
    (Interface.policy (D A)) a b

/-! ## Canonical states contain exactly the live tags -/

/-- `pi(sigma0)`, the state after replaying a list. -/
abbrev Run (ops : List (D A).Event) : St A :=
  applySeq (D A).toMRDTSig.toUpdateSig (D A).toMRDTSig.init ops

/-- No event in the list adds `x` back. -/
def NoAdd (ops : List (D A).Event) (x : A) : Prop :=
  ∀ e ∈ ops, e.op ≠ AppOp.add x

theorem noAdd_append_singleton {ops : List (D A).Event} {e : (D A).Event} {x : A} :
    NoAdd (ops ++ [e]) x ↔ NoAdd ops x ∧ e.op ≠ AppOp.add x := by
  constructor
  · exact fun h => ⟨fun a ha => h a (by simp [ha]), h e (by simp)⟩
  · rintro ⟨h, he⟩ a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact h a ha
    · rw [List.mem_singleton.mp ha]; exact he

/-- Splitting a list that ends in `e`. -/
theorem append_singleton_split {α : Type} {pi pre post : List α} {w e : α}
    (h : pi ++ [e] = pre ++ w :: post) :
    (w = e ∧ pi = pre)
      ∨ (∃ post', post = post' ++ [e] ∧ pi = pre ++ w :: post') := by
  cases post using List.reverseRecOn with
  | nil =>
      obtain ⟨hpre, hw⟩ := List.append_inj' (h : pi ++ [e] = pre ++ [w]) rfl
      have hew : e = w := by simpa using hw
      exact Or.inl ⟨hew.symm, hpre⟩
  | append_singleton post' x =>
      have h' : pi ++ [e] = (pre ++ w :: post') ++ [x] := by rw [h]; simp
      obtain ⟨hpi, hx⟩ := List.append_inj' h' rfl
      have hex : e = x := by simpa using hx
      exact Or.inr ⟨post', by rw [hex], hpi⟩

/-- A tag is in a replayed state exactly when some `remove` produced it and no
later event added its element back, or it is an initial tag that no `add`
removed. -/
theorem mem_run_iff_suffix (ops : List (D A).Event) (p : A × Timestamp) :
    p ∈ Run ops ↔
      (∃ pre w post, ops = pre ++ w :: post ∧ w.op = AppOp.remove p.1
        ∧ w.time = p.2 ∧ NoAdd post p.1)
      ∨ (p.2 = 0 ∧ NoAdd ops p.1) := by
  induction ops using List.reverseRecOn with
  | nil =>
      constructor
      · intro hm
        exact Or.inr ⟨(mem_sigma0 p).mp hm, by simp [NoAdd]⟩
      · rintro (⟨pre, w, post, hs, -, -, -⟩ | ⟨h, -⟩)
        · exact absurd hs.symm (by simp)
        · exact (mem_sigma0 p).mpr h
  | append_singleton ops e ih =>
      have hrun : Run (ops ++ [e]) = step (Run ops) e := by
        simp [Run, applySeq, List.foldl_append]
        rfl
      rw [hrun]
      rcases hop : e.op with x | x
      · -- `add x`
        rw [mem_step, hop]
        constructor
        · rintro ⟨hm, hpx⟩
          have hne : e.op ≠ AppOp.add p.1 := by
            rw [hop]; intro h; injection h with h'; exact hpx h'.symm
          rcases ih.mp hm with ⟨pre, w, post, hs, hw, ht, hn⟩ | ⟨h0, hn⟩
          · exact Or.inl ⟨pre, w, post ++ [e], by rw [hs]; simp, hw, ht,
              noAdd_append_singleton.mpr ⟨hn, hne⟩⟩
          · exact Or.inr ⟨h0, noAdd_append_singleton.mpr ⟨hn, hne⟩⟩
        · rintro (⟨pre, w, post, hs, hw, ht, hn⟩ | ⟨h0, hn⟩)
          · rcases append_singleton_split hs with ⟨hwe, -⟩ | ⟨post', hpost, hops⟩
            · exact absurd (hwe ▸ hw) (by rw [hop]; simp)
            · obtain ⟨hn', hne⟩ := noAdd_append_singleton.mp (hpost ▸ hn)
              exact ⟨ih.mpr (Or.inl ⟨pre, w, post', hops, hw, ht, hn'⟩),
                fun hpx => hne (by rw [hop, hpx])⟩
          · obtain ⟨hn', hne⟩ := noAdd_append_singleton.mp hn
            exact ⟨ih.mpr (Or.inr ⟨h0, hn'⟩), fun hpx => hne (by rw [hop, hpx])⟩
      · -- `remove x`
        rw [mem_step, hop]
        constructor
        · rintro (heq | hm)
          · have hx : p.1 = x := congrArg Prod.fst heq
            refine Or.inl ⟨ops, e, [], rfl, ?_, (congrArg Prod.snd heq).symm,
              by simp [NoAdd]⟩
            rw [hop, hx]
          · rcases ih.mp hm with ⟨pre, w, post, hs, hw, ht, hn⟩ | ⟨h0, hn⟩
            · exact Or.inl ⟨pre, w, post ++ [e], by rw [hs]; simp, hw, ht,
                noAdd_append_singleton.mpr ⟨hn, by rw [hop]; simp⟩⟩
            · exact Or.inr ⟨h0, noAdd_append_singleton.mpr ⟨hn, by rw [hop]; simp⟩⟩
        · rintro (⟨pre, w, post, hs, hw, ht, hn⟩ | ⟨h0, hn⟩)
          · rcases append_singleton_split hs with ⟨hwe, -⟩ | ⟨post', hpost, hops⟩
            · subst hwe
              have hx : x = p.1 := by
                have h2 : AppOp.remove x = AppOp.remove p.1 := by rw [← hop]; exact hw
                simpa using h2
              exact Or.inl (Prod.ext hx.symm ht.symm)
            · exact Or.inr (ih.mpr (Or.inl ⟨pre, w, post', hops, hw, ht,
                (noAdd_append_singleton.mp (hpost ▸ hn)).1⟩))
          · exact Or.inr (ih.mpr (Or.inr ⟨h0, (noAdd_append_singleton.mp hn).1⟩))

/-! ## Liveness -/

theorem not_edge_to_prefix {R : (D A).Event → (D A).Event → Prop}
    {pre post : List (D A).Event} {a r : (D A).Event}
    (hr : respects (pre ++ a :: post) R) (hm : r ∈ pre) : ¬ R a r :=
  (List.pairwise_append.mp hr).2.2 r hm a (by simp)

theorem not_edge_from_suffix {R : (D A).Event → (D A).Event → Prop}
    {pre post : List (D A).Event} {a r : (D A).Event}
    (hr : respects (pre ++ a :: post) R) (hm : r ∈ post) : ¬ R r a :=
  (List.pairwise_cons.mp (List.pairwise_append.mp hr).2.1).1 r hm

/-- No `add` of `x` in `E` observes `a`. -/
def Survives (C : Configuration (D A).toMRDTSig)
    (E : Set (Event A)) (a : Event A) (x : A) : Prop :=
  ¬ ∃ b ∈ E, b.op = AppOp.add x ∧ C.vis a b

/-- The tag `p` is live in `E`: either the `remove` that created it is in `E`
and no `add` of `E` observes that `remove`, or it is an initial tag and `E`
holds no `add` for its element. -/
def Live (C : Configuration (D A).toMRDTSig)
    (E : Set (Event A)) (p : A × Timestamp) : Prop :=
  (∃ w ∈ E, w.op = AppOp.remove p.1 ∧ w.time = p.2 ∧ Survives C E w p.1)
    ∨ (p.2 = 0 ∧ ¬ ∃ b ∈ E, b.op = AppOp.add p.1)

/-- **Fact 1.** A canonical state contains exactly the live tags. -/
theorem mem_run_iff_live {C : Configuration (D A).toMRDTSig}
    {E : Set (Event A)} {ops : List (D A).Event}
    (hp : listPermOf ops E) (hr : respects ops (loOn C.replayContext E)) (p : A × Timestamp) :
    p ∈ Run ops ↔ Live C E p := by
  rw [mem_run_iff_suffix]
  constructor
  · rintro (⟨pre, w, post, hs, hw, ht, hn⟩ | ⟨h0, hn⟩)
    · subst ops
      refine Or.inl ⟨w, (hp.2 w).mp (by simp), hw, ht, ?_⟩
      rintro ⟨b, hbe, hb, hvis⟩
      have hm : b ∈ pre ++ w :: post := (hp.2 b).mpr hbe
      rcases List.mem_append.mp hm with hm | hm
      · exact not_edge_to_prefix hr hm
          (Or.inl ⟨hvis, Or.inr ((replayBefore_iff b w).mpr ⟨p.1, hb, hw⟩)⟩)
      · rcases List.mem_cons.mp hm with heq | hm
        · rw [heq, hw] at hb; cases hb
        · exact hn b hm hb
    · exact Or.inr ⟨h0, fun ⟨b, hbe, hb⟩ => hn b ((hp.2 b).mpr hbe) hb⟩
  · rintro (⟨w, hwe, hw, ht, hsv⟩ | ⟨h0, hno⟩)
    · obtain ⟨pre, post, hs⟩ := List.append_of_mem ((hp.2 w).mpr hwe)
      refine Or.inl ⟨pre, w, post, hs, hw, ht, ?_⟩
      subst ops
      intro b hm hb
      refine not_edge_from_suffix hr hm ?_
      have hbe : b ∈ E := (hp.2 b).mp (by simp [hm])
      have hrc : (D A).toMRDTSig.toUpdateSig.replayBefore b w :=
        (replayBefore_iff b w).mpr ⟨p.1, hb, hw⟩
      by_cases hvb : C.vis b w
      · exact Or.inl ⟨hvb, Or.inl hrc⟩
      · refine Or.inr ⟨hvb, ?_, hrc, ?_⟩
        · exact fun hv => hsv ⟨b, hbe, hb, hv⟩
        · rintro ⟨c, hce, hvc, hc | hc⟩
          · obtain ⟨y, hwadd, -⟩ := (replayBefore_iff w c).mp hc
            rw [hw] at hwadd; cases hwadd
          · obtain ⟨y, hcadd, hwrem⟩ := (replayBefore_iff c w).mp hc
            rw [hw] at hwrem
            injection hwrem with hy
            subst y
            exact hsv ⟨c, hce, hcadd, hvc⟩
    · exact Or.inr ⟨h0, fun b hm hb => hno ⟨b, (hp.2 b).mp hm, hb⟩⟩

theorem canonical_mem_iff {C : Configuration (D A).toMRDTSig}
    {E : Set (Event A)} {s : St A}
    (hs : Interface.IsCan (D A) C E s) (p : A × Timestamp) : p ∈ s ↔ Live C E p := by
  obtain ⟨ops, hp, hr, hf⟩ := hs
  rw [← hf]
  exact mem_run_iff_live hp hr p

/-- **Fact 2.** Timestamps identify events, and the issuance guard keeps the
reserved timestamp `0` out of them, so a tag has one possible origin. -/
theorem live_iff_fixed_remove {C : Configuration (D A).toMRDTSig}
    {E : Set (Event A)} (hsub : E ⊆ C.events)
    (hpos : ∀ e ∈ C.events, 0 < e.time)
    {p : A × Timestamp} {a : Event A} (hac : a ∈ C.events)
    (ha : a.op = AppOp.remove p.1) (ht : a.time = p.2) :
    Live C E p ↔ a ∈ E ∧ Survives C E a p.1 := by
  constructor
  · rintro (⟨b, hb, -, hbt, hs⟩ | ⟨h0, -⟩)
    · have heq : b = a := C.replayContext.ts_unique (hsub hb) hac (hbt.trans ht.symm)
      subst b
      exact ⟨hb, hs⟩
    · exact absurd (hpos a hac) (by rw [ht, h0]; simp)
  · rintro ⟨he, hs⟩
    exact Or.inl ⟨a, he, ha, ht, hs⟩

/-- **Fact 3.** Liveness over the union is the Boolean that `merge` computes.
The initial tags are handled separately, since no event creates them. -/
theorem live_join {C : Configuration (D A).toMRDTSig}
    {E₁ E₂ : Set (Event A)} (hpos : ∀ e ∈ C.events, 0 < e.time)
    (hsub₁ : E₁ ⊆ C.events) (hsub₂ : E₂ ⊆ C.events)
    (hclosed₁ : ∀ a b, C.vis a b →
      ¬ (D A).toMRDTSig.toUpdateSig.commutes a b → b ∈ E₁ → a ∈ E₁)
    (hclosed₂ : ∀ a b, C.vis a b →
      ¬ (D A).toMRDTSig.toUpdateSig.commutes a b → b ∈ E₂ → a ∈ E₂)
    (p : A × Timestamp) :
    Live C (E₁ ∪ E₂) p ↔
      (Live C (E₁ ∩ E₂) p ∧ Live C E₁ p ∧ Live C E₂ p) ∨
      (Live C E₁ p ∧ ¬ Live C (E₁ ∩ E₂) p) ∨
      (Live C E₂ p ∧ ¬ Live C (E₁ ∩ E₂) p) := by
  have hint : E₁ ∩ E₂ ⊆ C.events := fun e he => hsub₁ he.1
  have huni : E₁ ∪ E₂ ⊆ C.events := fun e he => he.elim (fun h => hsub₁ h) (fun h => hsub₂ h)
  by_cases h0 : p.2 = 0
  · -- an initial tag: no event creates it, so liveness is "no add for `p.1`"
    have key : ∀ E : Set (Event A), E ⊆ C.events →
        (Live C E p ↔ ¬ ∃ b ∈ E, b.op = AppOp.add p.1) := by
      intro E hsub
      constructor
      · rintro (⟨w, hw, -, hwt, -⟩ | ⟨-, h⟩)
        · exact absurd (hpos w (hsub hw)) (by rw [hwt, h0]; simp)
        · exact h
      · exact fun h => Or.inr ⟨h0, h⟩
    rw [key _ huni, key _ hsub₁, key _ hsub₂, key _ hint]
    constructor
    · intro h
      exact Or.inl ⟨fun ⟨b, hb, hba⟩ => h ⟨b, Or.inl hb.1, hba⟩,
        fun ⟨b, hb, hba⟩ => h ⟨b, Or.inl hb, hba⟩,
        fun ⟨b, hb, hba⟩ => h ⟨b, Or.inr hb, hba⟩⟩
    · rintro (⟨-, h₁, h₂⟩ | ⟨h₁, hn0⟩ | ⟨h₂, hn0⟩)
      · rintro ⟨b, hb | hb, hba⟩
        · exact h₁ ⟨b, hb, hba⟩
        · exact h₂ ⟨b, hb, hba⟩
      · exact absurd (fun ⟨b, hb, hba⟩ => h₁ ⟨b, hb.1, hba⟩) hn0
      · exact absurd (fun ⟨b, hb, hba⟩ => h₂ ⟨b, hb.2, hba⟩) hn0
  · -- a minted tag: the OR-set argument
    by_cases hex : ∃ a ∈ E₁ ∪ E₂, a.op = AppOp.remove p.1 ∧ a.time = p.2
    · obtain ⟨a, hae, ha, ht⟩ := hex
      have hac : a ∈ C.events := huni hae
      rw [live_iff_fixed_remove huni hpos hac ha ht,
        live_iff_fixed_remove hint hpos hac ha ht,
        live_iff_fixed_remove hsub₁ hpos hac ha ht,
        live_iff_fixed_remove hsub₂ hpos hac ha ht]
      have hk₁ : ¬ Survives C E₁ a p.1 → a ∈ E₁ := by
        intro hn
        obtain ⟨b, hb, hba, hv⟩ := Classical.not_not.mp hn
        refine hclosed₁ a b hv ?_ hb
        exact (noncomm_iff a b).mpr (Or.inr ((eventRcBefore_iff b a).mpr ⟨p.1, hba, ha⟩))
      have hk₂ : ¬ Survives C E₂ a p.1 → a ∈ E₂ := by
        intro hn
        obtain ⟨b, hb, hba, hv⟩ := Classical.not_not.mp hn
        refine hclosed₂ a b hv ?_ hb
        exact (noncomm_iff a b).mpr (Or.inr ((eventRcBefore_iff b a).mpr ⟨p.1, hba, ha⟩))
      have hu : Survives C (E₁ ∪ E₂) a p.1 ↔
          Survives C E₁ a p.1 ∧ Survives C E₂ a p.1 := by
        simp only [Survives, Set.mem_union]
        constructor
        · intro h
          exact ⟨fun ⟨b, hb, hba, hv⟩ => h ⟨b, Or.inl hb, hba, hv⟩,
            fun ⟨b, hb, hba, hv⟩ => h ⟨b, Or.inr hb, hba, hv⟩⟩
        · rintro ⟨h₁, h₂⟩ ⟨b, hb | hb, hba, hv⟩
          · exact h₁ ⟨b, hb, hba, hv⟩
          · exact h₂ ⟨b, hb, hba, hv⟩
      have hi₁ : Survives C E₁ a p.1 → Survives C (E₁ ∩ E₂) a p.1 :=
        fun h ⟨b, hb, hba, hv⟩ => h ⟨b, hb.1, hba, hv⟩
      have hi₂ : Survives C E₂ a p.1 → Survives C (E₁ ∩ E₂) a p.1 :=
        fun h ⟨b, hb, hba, hv⟩ => h ⟨b, hb.2, hba, hv⟩
      rw [hu]
      simp only [Set.mem_union, Set.mem_inter_iff]
      tauto
    · have hn : ∀ E : Set (Event A), E ⊆ E₁ ∪ E₂ → ¬ Live C E p := by
        rintro E hs (⟨w, hw, hwr, hwt, -⟩ | ⟨hz, -⟩)
        · exact hex ⟨w, hs hw, hwr, hwt⟩
        · exact h0 hz
      have hnU := hn (E₁ ∪ E₂) Set.Subset.rfl
      have hnI := hn (E₁ ∩ E₂) (fun _ h => Or.inl h.1)
      have hn₁ := hn E₁ Set.subset_union_left
      have hn₂ := hn E₂ Set.subset_union_right
      simp [hnU, hnI, hn₁, hn₂]

/-! ## The join lemma -/

/-- Issuance: `G(e, s) <=> 0 < time(e)`. The reserved timestamp `0` belongs to
the initial tags and may not be minted. -/
def issuance (A : Type) [DecidableEq A] [Fintype A] : Issuance (D A).toMRDTSig where
  CanIssue := fun e _ => 0 < e.time

/-- **The join lemma**, proved directly, at every mint-honest configuration.
The issuance guard enters exactly once, through `hpos`. -/
theorem joinAt (C : Configuration (D A).toMRDTSig)
    (hmint : MintHonest (D A).toMRDTSig (issuance A).CanIssue C) :
    Interface.JoinAtConfig (D A) C := by
  have hpos : ∀ e ∈ C.replayContext.events, 0 < e.time := by
    intro e he
    obtain ⟨_, _, _, hg⟩ := hmint e he
    exact hg
  intro E₁ E₂ s₀ s₁ s₂ htr hir hsub₁ hsub₂ hclosed₁ hclosed₂ hs₀ hs₁ hs₂
  obtain ⟨ops₁, hp₁, -, -⟩ := id hs₁
  obtain ⟨ops₂, hp₂, -, -⟩ := id hs₂
  have hpU := listPermOf_union (D := (D A).toMRDTSig.toUpdateSig) hp₁ hp₂
  have hsubU : ∀ a ∈ E₁ ∪ E₂, a ∈ C.replayContext.events :=
    fun a ha => ha.elim (hsub₁ a) (hsub₂ a)
  obtain ⟨sU, hsU⟩ := isCanonicalState_exists_of_replayLaws
    (Metatheory.replayLaws laws payloadDetermined) htr hir hpU hsubU
  have heq : (D A).toMRDTSig.merge s₀ s₁ s₂ = sU := by
    change mergeState s₀ s₁ s₂ = sU
    ext p
    simp only [mergeState, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    rw [canonical_mem_iff hs₀, canonical_mem_iff hs₁, canonical_mem_iff hs₂,
      canonical_mem_iff hsU]
    simpa only [and_assoc, or_assoc] using
      (live_join hpos (fun a ha => hsub₁ a ha) (fun a ha => hsub₂ a ha)
        hclosed₁ hclosed₂ p).symm
  rw [heq]
  exact hsU

/-- **What this row supplies for the direct route**: `Laws(D_type)` proved
by hand, and the join lemma. -/
theorem directObligations : DirectObligations (D A) (issuance A) :=
  ⟨laws, payloadDetermined, joinAt⟩

end LeanProofs.Implementations.RemoveWinsSet
