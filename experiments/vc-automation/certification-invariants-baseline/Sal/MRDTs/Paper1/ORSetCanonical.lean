import Sal.MRDTs.Paper1.ORSet

/-! Direct canonical Join for the exact paper OR-set. The key invariant is
observed removal of individual add events, not a chosen branch ordering. -/
namespace Sal.MRDTs.Paper1.ORSet
open Sal.MRDTs.Foundation
variable {α : Type} [DecidableEq α]

abbrev Run (ops : List (Op (Update α))) : State α :=
  applySeq (D α).toUpdateSig (D α).init ops

def NoRemove (ops : List (Op (Update α))) (x : α) : Prop :=
  ∀ e ∈ ops, e.2.2 ≠ .remove x

theorem pair_preserved {s : State α} {p : α × Timestamp} (hs : p ∈ s)
    (ops : List (Op (Update α))) (hn : NoRemove ops p.1) :
    p ∈ (show State α from applySeq (D α).toUpdateSig s ops) := by
  induction ops generalizing s with
  | nil => exact hs
  | cons e ops ih =>
      have he := hn e (by simp)
      have hn' : NoRemove ops p.1 := fun a ha => hn a (by simp [ha])
      apply ih (s := step s e) _ hn'
      rcases e with ⟨t, r, op⟩
      cases op with
      | add x => simp [step, hs]
      | remove x =>
          have hx : p.1 ≠ x := by intro h; exact he (by simp [h])
          simp [step, hs, hx]

theorem mem_run_iff_suffix (ops : List (Op (Update α))) (p : α × Timestamp) :
    p ∈ Run ops ↔ ∃ pre a post, ops = pre ++ a :: post ∧
      a.2.2 = .add p.1 ∧ a.1 = p.2 ∧ NoRemove post p.1 := by
  constructor
  · induction ops using List.reverseRecOn with
    | nil => simp [Run, applySeq, D]
    | append_singleton ops e ih =>
        intro hm
        change p ∈ (show State α from applySeq (D α).toUpdateSig (D α).init (ops ++ [e])) at hm
        rw [applySeq_append_single] at hm
        change p ∈ step (Run ops) e at hm
        rcases hop : e.2.2 with ⟨x⟩ | ⟨x⟩
        · simp only [step, hop, Finset.mem_insert] at hm
          rcases hm with h | h
          · have hx : x = p.1 := (congrArg Prod.fst h).symm
            have ht : e.1 = p.2 := (congrArg Prod.snd h).symm
            exact ⟨ops, e, [], by simp, hx ▸ hop, ht, by simp [NoRemove]⟩
          · obtain ⟨pre, a, post, hsplit, ha, ht, hn⟩ := ih h
            refine ⟨pre, a, post ++ [e], by simp [hsplit, List.append_assoc], ha, ht, ?_⟩
            intro r hr
            rcases List.mem_append.mp hr with hr | hr
            · exact hn r hr
            · have hre : r = e := List.mem_singleton.mp hr
              subst r
              simp [hop]
        · simp only [step, hop, Finset.mem_filter] at hm
          obtain ⟨pre, a, post, hsplit, ha, ht, hn⟩ := ih hm.1
          refine ⟨pre, a, post ++ [e], by simp [hsplit, List.append_assoc], ha, ht, ?_⟩
          intro r hr
          rcases List.mem_append.mp hr with hr | hr
          · exact hn r hr
          · have hre : r = e := List.mem_singleton.mp hr
            subst r
            intro hrem
            rw [hop] at hrem
            injection hrem with hx
            exact hm.2 hx.symm
  · rintro ⟨pre, a, post, rfl, ha, ht, hn⟩
    have hp : p ∈ step (Run pre) a := by
      have heq : (p.1, a.1) = p := by rw [ht]
      simp [step, ha, heq]
    have hpost := pair_preserved hp post hn
    simpa [Run, applySeq, D, List.foldl_append] using hpost

/-- A relation edge cannot point from a suffix into a preceding position. -/
theorem not_edge_to_prefix {R : Op (Update α) → Op (Update α) → Prop}
    {pre post : List (Op (Update α))} {a r : Op (Update α)}
    (hr : respects (pre ++ a :: post) R) (hm : r ∈ pre) : ¬ R a r := by
  exact (List.pairwise_append.mp hr).2.2 r hm a (by simp)

theorem not_edge_from_suffix {R : Op (Update α) → Op (Update α) → Prop}
    {pre post : List (Op (Update α))} {a r : Op (Update α)}
    (hr : respects (pre ++ a :: post) R) (hm : r ∈ post) : ¬ R r a := by
  exact (List.pairwise_cons.mp (List.pairwise_append.mp hr).2.1).1 r hm

def Survives (C : ReplayContext (D α).toUpdateSig)
    (E : Set (Op (Update α))) (a : Op (Update α)) (x : α) : Prop :=
  ¬ ∃ r ∈ E, C.vis a r ∧ r.2.2 = .remove x

def Live (C : ReplayContext (D α).toUpdateSig)
    (E : Set (Op (Update α))) (p : α × Timestamp) : Prop :=
  ∃ a ∈ E, a.2.2 = .add p.1 ∧ a.1 = p.2 ∧ Survives C E a p.1

theorem mem_run_iff_live {C : ReplayContext (D α).toUpdateSig}
    {E : Set (Op (Update α))} {ops : List (Op (Update α))}
    (hp : listPermOf ops E) (hr : respects ops (loOn C E)) (p : α × Timestamp) :
    p ∈ Run ops ↔ Live C E p := by
  rw [mem_run_iff_suffix]
  constructor
  · rintro ⟨pre, a, post, hs, ha, ht, hn⟩
    subst ops
    refine ⟨a, (hp.2 a).mp (by simp), ha, ht, ?_⟩
    rintro ⟨r, hre, hv, hrem⟩
    have hm : r ∈ pre ++ a :: post := (hp.2 r).mpr hre
    rcases List.mem_append.mp hm with hm | hm
    · apply not_edge_to_prefix hr hm
      exact Or.inl ⟨hv, Or.inr ((rc_iff r a).mpr ⟨p.1, hrem, ha⟩)⟩
    · rcases List.mem_cons.mp hm with heq | hm
      · rw [heq, ha] at hrem; cases hrem
      · exact hn r hm hrem
  · rintro ⟨a, hae, ha, ht, hn⟩
    obtain ⟨pre, post, hs⟩ := List.append_of_mem ((hp.2 a).mpr hae)
    refine ⟨pre, a, post, hs, ha, ht, ?_⟩
    subst ops
    intro r hm hrem
    apply not_edge_from_suffix hr hm
    have hre : r ∈ E := (hp.2 r).mp (by simp [hm])
    have hrc : (D α).toUpdateSig.rc r a := (rc_iff r a).mpr ⟨p.1, hrem, ha⟩
    by_cases hva : C.vis r a
    · exact Or.inl ⟨hva, Or.inl hrc⟩
    · refine Or.inr ⟨hva, ?_, hrc, ?_⟩
      · exact fun hv => hn ⟨r, hre, hv, hrem⟩
      · rintro ⟨c, hce, hvc, hc⟩
        rcases hc with hc | hc
        · obtain ⟨x, ha', _⟩ := (rc_iff a c).mp hc
          rw [ha] at ha'; cases ha'
        · obtain ⟨x, hc, ha'⟩ := (rc_iff c a).mp hc
          rw [ha] at ha'; injection ha' with hx
          subst x
          exact hn ⟨c, hce, hvc, hc⟩

theorem canonical_mem_iff {C : ReplayContext (D α).toUpdateSig}
    {E : Set (Op (Update α))} {s : State α}
    (hs : IsCanonicalState C E s) (p : α × Timestamp) : p ∈ s ↔ Live C E p := by
  obtain ⟨ops, hp, hr, hf⟩ := hs
  rw [← hf]
  exact mem_run_iff_live hp hr p


theorem live_iff_fixed_add {C : ReplayContext (D α).toUpdateSig}
    {E : Set (Op (Update α))} (hsub : E ⊆ C.events)
    {p : α × Timestamp} {a : Op (Update α)}
    (hac : a ∈ C.events) (ha : a.2.2 = .add p.1) (ht : a.1 = p.2) :
    Live C E p ↔ a ∈ E ∧ Survives C E a p.1 := by
  constructor
  · rintro ⟨b, hb, _, hbt, hs⟩
    have heq : b = a := C.ts_unique (hsub hb) hac (hbt.trans ht.symm)
    subst b
    exact ⟨hb, hs⟩
  · rintro ⟨he, hs⟩
    exact ⟨a, he, ha, ht, hs⟩

theorem live_join {C : ReplayContext (D α).toUpdateSig}
    {E₁ E₂ : Set (Op (Update α))}
    (hsub₁ : E₁ ⊆ C.events) (hsub₂ : E₂ ⊆ C.events)
    (hclosed₁ : ∀ a b, C.vis a b → ¬ (D α).toUpdateSig.commutes a b → b ∈ E₁ → a ∈ E₁)
    (hclosed₂ : ∀ a b, C.vis a b → ¬ (D α).toUpdateSig.commutes a b → b ∈ E₂ → a ∈ E₂)
    (p : α × Timestamp) :
    Live C (E₁ ∪ E₂) p ↔
      (Live C (E₁ ∩ E₂) p ∧ Live C E₁ p ∧ Live C E₂ p) ∨
      (Live C E₁ p ∧ ¬ Live C (E₁ ∩ E₂) p) ∨
      (Live C E₂ p ∧ ¬ Live C (E₁ ∩ E₂) p) := by
  by_cases hex : ∃ a ∈ E₁ ∪ E₂, a.2.2 = .add p.1 ∧ a.1 = p.2
  · obtain ⟨a, hae, ha, ht⟩ := hex
    have hac : a ∈ C.events := hae.elim (fun h => hsub₁ h) (fun h => hsub₂ h)
    have huni : E₁ ∪ E₂ ⊆ C.events := fun e he => he.elim (fun h => hsub₁ h) (fun h => hsub₂ h)
    have hint : E₁ ∩ E₂ ⊆ C.events := fun e he => hsub₁ he.1
    rw [live_iff_fixed_add huni hac ha ht, live_iff_fixed_add hint hac ha ht,
      live_iff_fixed_add hsub₁ hac ha ht, live_iff_fixed_add hsub₂ hac ha ht]
    have hk₁ : ¬ Survives C E₁ a p.1 → a ∈ E₁ := by
      intro hn
      obtain ⟨r, hr, hv, hop⟩ := Classical.not_not.mp hn
      exact hclosed₁ a r hv ((noncomm_iff_rc a r).mpr
        (Or.inr ((rc_iff r a).mpr ⟨p.1, hop, ha⟩))) hr
    have hk₂ : ¬ Survives C E₂ a p.1 → a ∈ E₂ := by
      intro hn
      obtain ⟨r, hr, hv, hop⟩ := Classical.not_not.mp hn
      exact hclosed₂ a r hv ((noncomm_iff_rc a r).mpr
        (Or.inr ((rc_iff r a).mpr ⟨p.1, hop, ha⟩))) hr
    have hu : Survives C (E₁ ∪ E₂) a p.1 ↔
        Survives C E₁ a p.1 ∧ Survives C E₂ a p.1 := by
      simp only [Survives, Set.mem_union]
      constructor
      · intro h; exact ⟨fun ⟨r, hr, hv, ho⟩ => h ⟨r, Or.inl hr, hv, ho⟩,
          fun ⟨r, hr, hv, ho⟩ => h ⟨r, Or.inr hr, hv, ho⟩⟩
      · rintro ⟨h₁, h₂⟩ ⟨r, hr | hr, hv, ho⟩
        · exact h₁ ⟨r, hr, hv, ho⟩
        · exact h₂ ⟨r, hr, hv, ho⟩
    have hi₁ : Survives C E₁ a p.1 → Survives C (E₁ ∩ E₂) a p.1 :=
      fun h ⟨r, hr, hv, ho⟩ => h ⟨r, hr.1, hv, ho⟩
    have hi₂ : Survives C E₂ a p.1 → Survives C (E₁ ∩ E₂) a p.1 :=
      fun h ⟨r, hr, hv, ho⟩ => h ⟨r, hr.2, hv, ho⟩
    rw [hu]
    simp only [Set.mem_union, Set.mem_inter_iff]
    tauto
  · have hn (E : Set (Op (Update α))) (hs : E ⊆ E₁ ∪ E₂) : ¬ Live C E p := by
      rintro ⟨a, ha, hop, ht, _⟩
      exact hex ⟨a, hs ha, hop, ht⟩
    have hnU := hn (E₁ ∪ E₂) Set.Subset.rfl
    have hnI := hn (E₁ ∩ E₂) (fun _ h => Or.inl h.1)
    have hn₁ := hn E₁ Set.subset_union_left
    have hn₂ := hn E₂ Set.subset_union_right
    simp [hnU, hnI, hn₁, hn₂]

/-- Honest ancestor merge preserves the canonical union state directly. -/
theorem join : Join (D α) := by
  intro C E₁ E₂ s₀ s₁ s₂ htr hir hsub₁ hsub₂ hclosed₁ hclosed₂ hs₀ hs₁ hs₂
  obtain ⟨ops₁, hp₁, _, _⟩ := id hs₁
  obtain ⟨ops₂, hp₂, _, _⟩ := id hs₂
  have hpU := listPermOf_union (D := (D α).toUpdateSig) hp₁ hp₂
  have hsubU : ∀ a ∈ E₁ ∪ E₂, a ∈ C.events :=
    fun a ha => ha.elim (hsub₁ a) (hsub₂ a)
  obtain ⟨sU, hsU⟩ := isCanonicalState_exists_of_replayLaws replayLaws htr hir hpU hsubU
  have heq : (D α).merge s₀ s₁ s₂ = sU := by
    change merge s₀ s₁ s₂ = sU
    ext p
    simp only [merge, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    rw [canonical_mem_iff hs₀, canonical_mem_iff hs₁, canonical_mem_iff hs₂,
      canonical_mem_iff hsU]
    simpa only [and_assoc, or_assoc] using (live_join hsub₁ hsub₂ hclosed₁ hclosed₂ p).symm
  rw [heq]
  exact hsU

end Sal.MRDTs.Paper1.ORSet
