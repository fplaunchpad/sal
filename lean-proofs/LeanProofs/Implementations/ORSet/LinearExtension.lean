import LeanProofs.Implementations.ORSet.Laws
import LeanProofs.Soundness.LinearExtension

/-!
# The OR-set: clause 1

What a canonical state is, and the join lemma proved directly. VC3 fails for
this row, so the VC route is unavailable.
-/

namespace LeanProofs.Implementations.ORSet

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.Interface

variable {A : Type} [DecidableEq A]

/-- The replay order of Section 4: `rc`, lifted to events. -/
noncomputable local instance replayOrder :
    EventOrder (D A).toMRDTSig.toUpdateSig := Interface.rcOrder (D A)

@[simp] theorem replayBefore_iff (a b : (D A).Event) :
    (D A).toMRDTSig.toUpdateSig.replayBefore a b
      ↔ ∃ x, a.op = Act.remove x ∧ b.op = Act.add x := by
  refine Iff.trans ?_ (rcBefore_iff a.op b.op)
  exact @OperationPolicy.lift_replayOrder_iff (D A).toMRDTSig.toUpdateSig
    (Interface.policy (D A)) a b

theorem noncomm_iff_replayBefore (a b : (D A).Event) :
    ¬ (D A).toMRDTSig.toUpdateSig.commutes a b ↔
      (D A).toMRDTSig.toUpdateSig.replayBefore a b
        ∨ (D A).toMRDTSig.toUpdateSig.replayBefore b a := by
  simpa only [replayBefore_iff] using
    (noncomm_iff a b).trans (by simp only [eventRcBefore_iff])

/-! ## Canonical states contain exactly the live records -/

/-- `pi(sigma0)`, the state after replaying a list. -/
abbrev Run (ops : List (D A).Event) : St A :=
  applySeq (D A).toMRDTSig.toUpdateSig (D A).toMRDTSig.init ops

/-- No event in the list removes `x`. -/
def NoRemove (ops : List (D A).Event) (x : A) : Prop :=
  ∀ e ∈ ops, e.op ≠ Act.remove x

theorem pair_preserved {S : St A} {p : A × Timestamp} (hs : p ∈ S)
    (ops : List (D A).Event) (hn : NoRemove ops p.1) :
    p ∈ (show St A from applySeq (D A).toMRDTSig.toUpdateSig S ops) := by
  induction ops generalizing S with
  | nil => exact hs
  | cons e ops ih =>
      have he := hn e (by simp)
      have hn' : NoRemove ops p.1 := fun a ha => hn a (by simp [ha])
      apply ih (S := step S e) _ hn'
      rcases e with ⟨t, r, o⟩
      cases o with
      | add x => simp [step, Op.op, hs]
      | remove x =>
          have hx : p.1 ≠ x := by intro h; exact he (by simp [Op.op, h])
          simp [step, Op.op, hs, hx]

/-- A record is in a replayed state exactly when some add produced it and no
later event in the list removed its element. -/
theorem mem_run_iff_suffix (ops : List (D A).Event) (p : A × Timestamp) :
    p ∈ Run ops ↔ ∃ pre a post, ops = pre ++ a :: post ∧
      a.op = Act.add p.1 ∧ a.time = p.2 ∧ NoRemove post p.1 := by
  constructor
  · induction ops using List.reverseRecOn with
    | nil => simp [Run, applySeq, Impl.toMRDTSig]
    | append_singleton ops e ih =>
        intro hm
        change p ∈ (show St A from
          applySeq (D A).toMRDTSig.toUpdateSig (D A).toMRDTSig.init (ops ++ [e])) at hm
        rw [applySeq_append_single] at hm
        change p ∈ step (Run ops) e at hm
        rcases hop : e.op with x | x
        · simp only [step, hop, Finset.mem_insert] at hm
          rcases hm with h | h
          · have hx : x = p.1 := (congrArg Prod.fst h).symm
            have ht : e.time = p.2 := (congrArg Prod.snd h).symm
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
      have heq : (p.1, a.time) = p := by rw [ht]
      simp [step, ha, heq]
    have hpost := pair_preserved hp post hn
    simpa [Run, applySeq, List.foldl_append] using hpost

/-- A relation edge cannot point from a suffix into a preceding position. -/
theorem not_edge_to_prefix {R : (D A).Event → (D A).Event → Prop}
    {pre post : List (D A).Event} {a r : (D A).Event}
    (hr : respects (pre ++ a :: post) R) (hm : r ∈ pre) : ¬ R a r :=
  (List.pairwise_append.mp hr).2.2 r hm a (by simp)

theorem not_edge_from_suffix {R : (D A).Event → (D A).Event → Prop}
    {pre post : List (D A).Event} {a r : (D A).Event}
    (hr : respects (pre ++ a :: post) R) (hm : r ∈ post) : ¬ R r a :=
  (List.pairwise_cons.mp (List.pairwise_append.mp hr).2.1).1 r hm

/-- No remove of `x` in `E` sees the add `a`. -/
def Survives (C : Configuration (D A).toMRDTSig)
    (E : Set (D A).Event) (a : (D A).Event) (x : A) : Prop :=
  ¬ ∃ r ∈ E, C.vis a r ∧ r.op = Act.remove x

/-- The record `p` is live in `E`: it was added by an event of `E` that no
remove of `E` observes. -/
def Live (C : Configuration (D A).toMRDTSig)
    (E : Set (D A).Event) (p : A × Timestamp) : Prop :=
  ∃ a ∈ E, a.op = Act.add p.1 ∧ a.time = p.2 ∧ Survives C E a p.1

/-- **Fact 1.** Any replay of `E` that respects `lo^C_E` contains exactly the
live records, so the state does not depend on which replay was taken. -/
theorem mem_run_iff_live {C : Configuration (D A).toMRDTSig}
    {E : Set (D A).Event} {ops : List (D A).Event}
    (hp : listPermOf ops E) (hr : respects ops (loOn C.replayContext E)) (p : A × Timestamp) :
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
      exact Or.inl ⟨hv, Or.inr ((replayBefore_iff r a).mpr ⟨p.1, hrem, ha⟩)⟩
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
    have hrc : (D A).toMRDTSig.toUpdateSig.replayBefore r a :=
      (replayBefore_iff r a).mpr ⟨p.1, hrem, ha⟩
    by_cases hva : C.vis r a
    · exact Or.inl ⟨hva, Or.inl hrc⟩
    · refine Or.inr ⟨hva, ?_, hrc, ?_⟩
      · exact fun hv => hn ⟨r, hre, hv, hrem⟩
      · rintro ⟨c, hce, hvc, hc⟩
        rcases hc with hc | hc
        · obtain ⟨x, ha', -⟩ := (replayBefore_iff a c).mp hc
          rw [ha] at ha'; cases ha'
        · obtain ⟨x, hc, ha'⟩ := (replayBefore_iff c a).mp hc
          rw [ha] at ha'; injection ha' with hx
          subst x
          exact hn ⟨c, hce, hvc, hc⟩

theorem canonical_mem_iff {C : Configuration (D A).toMRDTSig}
    {E : Set (D A).Event} {s : St A}
    (hs : Interface.IsCan (D A) C E s) (p : A × Timestamp) : p ∈ s ↔ Live C E p := by
  obtain ⟨ops, hp, hr, hf⟩ := hs
  rw [← hf]
  exact mem_run_iff_live hp hr p

/-- **Fact 2.** Timestamps identify events, so only one event can add a given
record and liveness is a statement about that event alone. -/
theorem live_iff_fixed_add {C : Configuration (D A).toMRDTSig}
    {E : Set (D A).Event} (hsub : E ⊆ C.events)
    {p : A × Timestamp} {a : (D A).Event}
    (hac : a ∈ C.events) (ha : a.op = Act.add p.1) (ht : a.time = p.2) :
    Live C E p ↔ a ∈ E ∧ Survives C E a p.1 := by
  constructor
  · rintro ⟨b, hb, -, hbt, hs⟩
    have heq : b = a := C.replayContext.ts_unique (hsub hb) hac (hbt.trans ht.symm)
    subst b
    exact ⟨hb, hs⟩
  · rintro ⟨he, hs⟩
    exact ⟨a, he, ha, ht, hs⟩

/-- **Fact 3.** Liveness over the union is the Boolean that `merge` computes.
The two `hk` steps are where causal closure is used: a branch that observes a
remove covering the add must contain the add as well. -/
theorem live_join {C : Configuration (D A).toMRDTSig}
    {E₁ E₂ : Set (D A).Event}
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
  by_cases hex : ∃ a ∈ E₁ ∪ E₂, a.op = Act.add p.1 ∧ a.time = p.2
  · obtain ⟨a, hae, ha, ht⟩ := hex
    have hac : a ∈ C.events := hae.elim (fun h => hsub₁ h) (fun h => hsub₂ h)
    have huni : E₁ ∪ E₂ ⊆ C.events := fun e he => he.elim (fun h => hsub₁ h) (fun h => hsub₂ h)
    have hint : E₁ ∩ E₂ ⊆ C.events := fun e he => hsub₁ he.1
    rw [live_iff_fixed_add huni hac ha ht, live_iff_fixed_add hint hac ha ht,
      live_iff_fixed_add hsub₁ hac ha ht, live_iff_fixed_add hsub₂ hac ha ht]
    have hk₁ : ¬ Survives C E₁ a p.1 → a ∈ E₁ := by
      intro hn
      obtain ⟨r, hr, hv, hop⟩ := Classical.not_not.mp hn
      exact hclosed₁ a r hv ((noncomm_iff_replayBefore a r).mpr
        (Or.inr ((replayBefore_iff r a).mpr ⟨p.1, hop, ha⟩))) hr
    have hk₂ : ¬ Survives C E₂ a p.1 → a ∈ E₂ := by
      intro hn
      obtain ⟨r, hr, hv, hop⟩ := Classical.not_not.mp hn
      exact hclosed₂ a r hv ((noncomm_iff_replayBefore a r).mpr
        (Or.inr ((replayBefore_iff r a).mpr ⟨p.1, hop, ha⟩))) hr
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
  · have hn (E : Set (D A).Event) (hs : E ⊆ E₁ ∪ E₂) : ¬ Live C E p := by
      rintro ⟨a, ha, hop, ht, -⟩
      exact hex ⟨a, hs ha, hop, ht⟩
    have hnU := hn (E₁ ∪ E₂) Set.Subset.rfl
    have hnI := hn (E₁ ∩ E₂) (fun _ h => Or.inl h.1)
    have hn₁ := hn E₁ Set.subset_union_left
    have hn₂ := hn E₂ Set.subset_union_right
    simp [hnU, hnI, hn₁, hn₂]

/-- **The join lemma**, proved directly. Merging canonical states of the
branches yields a canonical state of the union of their event sets. -/
theorem joinLemma : Interface.JoinConfig (D A) := by
  intro C E₁ E₂ s₀ s₁ s₂ htr hir hsub₁ hsub₂ hclosed₁ hclosed₂ hs₀ hs₁ hs₂
  obtain ⟨ops₁, hp₁, -, -⟩ := id hs₁
  obtain ⟨ops₂, hp₂, -, -⟩ := id hs₂
  have hpU := listPermOf_union (D := (D A).toMRDTSig.toUpdateSig) hp₁ hp₂
  have hsubU : ∀ a ∈ E₁ ∪ E₂, a ∈ C.replayContext.events :=
    fun a ha => ha.elim (hsub₁ a) (hsub₂ a)
  obtain ⟨sU, hsU⟩ := isCanonicalState_exists_of_replayLaws
    (Metatheory.replayLaws laws) htr hir hpU hsubU
  have heq : (D A).toMRDTSig.merge s₀ s₁ s₂ = sU := by
    change mergeState s₀ s₁ s₂ = sU
    ext p
    simp only [mergeState, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    rw [canonical_mem_iff hs₀, canonical_mem_iff hs₁, canonical_mem_iff hs₂,
      canonical_mem_iff hsU]
    simpa only [and_assoc, or_assoc] using
      (live_join hsub₁ hsub₂ hclosed₁ hclosed₂ p).symm
  rw [heq]
  exact hsU

/-! ## Issuance -/

variable (A)

/-- Issuance: `G(e, O) <=> true`. The exact OR-set needs no payload and no
side condition on the events a replica may mint. -/
def issuance : Issuance (D A).toMRDTSig where
  CanIssue := fun _ _ => True

variable {A}

/-- **What this row supplies for the direct route**: `Laws(D_type)` proved
by hand, and the join lemma. -/
theorem directObligations : DirectObligations (D A) (issuance A) :=
  ⟨laws, fun C _ => joinLemma C⟩

end LeanProofs.Implementations.ORSet
