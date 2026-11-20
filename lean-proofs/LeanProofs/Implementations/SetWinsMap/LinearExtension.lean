import LeanProofs.Implementations.SetWinsMap.Laws
import LeanProofs.Soundness.LinearExtension

/-!
# The set-wins multimap: clause 1

What a canonical state is, and the join lemma proved directly.
-/

namespace LeanProofs.Implementations.SetWinsMap

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.Interface

variable {K V : Type} [DecidableEq K] [DecidableEq V]

/-- The replay order of Section 4: `rc`, lifted to events. -/
noncomputable local instance rcOrder :
    EventOrder (D K V).toMRDTSig.toUpdateSig := Interface.rcOrder (D K V)

@[simp] theorem replayBefore_iff (a b : (D K V).Event) :
    (D K V).toMRDTSig.toUpdateSig.replayBefore a b
      ↔ ∃ k v, a.op = AppOp.del k ∧ b.op = AppOp.set k v := by
  refine Iff.trans ?_ (rcBefore_iff a.op b.op)
  exact @OperationPolicy.lift_replayOrder_iff (D K V).toMRDTSig.toUpdateSig
    (Interface.policy (D K V)) a b

theorem noncomm_iff_replayBefore (a b : (D K V).Event) :
    ¬ (D K V).toMRDTSig.toUpdateSig.commutes a b ↔
      (D K V).toMRDTSig.toUpdateSig.replayBefore a b
        ∨ (D K V).toMRDTSig.toUpdateSig.replayBefore b a := by
  simpa only [replayBefore_iff] using
    (rc_non_comm a b).trans (by simp only [eventRcBefore_iff])

/-! ## Canonical states contain exactly the live bindings -/

/-- `pi(sigma0)`, the state after replaying a list. -/
abbrev Run (ops : List (D K V).Event) : St K V :=
  applySeq (D K V).toMRDTSig.toUpdateSig (D K V).toMRDTSig.init ops

/-- No event in the list drops key `k`. -/
def NoDel (ops : List (D K V).Event) (k : K) : Prop :=
  ∀ e ∈ ops, e.op ≠ AppOp.del k

theorem binding_preserved {S : St K V} {p : (K × V) × Timestamp} (hs : p ∈ S)
    (ops : List (D K V).Event) (hn : NoDel ops p.1.1) :
    p ∈ (show St K V from applySeq (D K V).toMRDTSig.toUpdateSig S ops) := by
  induction ops generalizing S with
  | nil => exact hs
  | cons e ops ih =>
      have he := hn e (by simp)
      have hn' : NoDel ops p.1.1 := fun a ha => hn a (by simp [ha])
      apply ih (S := step S e) _ hn'
      rcases e with ⟨t, r, o⟩
      cases o with
      | set k v => simp [step, Op.op, hs]
      | del k =>
          have hk : p.1.1 ≠ k := by intro h; exact he (by simp [Op.op, h])
          simp [step, Op.op, hs, hk]

/-- A binding is in a replayed state exactly when some `set` produced it and
no later event in the list dropped its key. -/
theorem mem_run_iff_suffix (ops : List (D K V).Event) (p : (K × V) × Timestamp) :
    p ∈ Run ops ↔ ∃ pre a post, ops = pre ++ a :: post ∧
      a.op = AppOp.set p.1.1 p.1.2 ∧ a.time = p.2 ∧ NoDel post p.1.1 := by
  constructor
  · induction ops using List.reverseRecOn with
    | nil => simp [Run, applySeq, Impl.toMRDTSig]
    | append_singleton ops e ih =>
        intro hm
        change p ∈ (show St K V from
          applySeq (D K V).toMRDTSig.toUpdateSig (D K V).toMRDTSig.init (ops ++ [e])) at hm
        rw [applySeq_append_single] at hm
        change p ∈ step (Run ops) e at hm
        rcases hop : e.op with ⟨k, v⟩ | ⟨k⟩
        · simp only [step, hop, Finset.mem_insert] at hm
          rcases hm with h | h
          · have hx : ((k, v) : K × V) = p.1 := (congrArg Prod.fst h).symm
            refine ⟨ops, e, [], by simp, ?_, (congrArg Prod.snd h).symm,
              by simp [NoDel]⟩
            rw [hop, ← hx]
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
            intro hdel
            rw [hop] at hdel
            injection hdel with hk
            exact hm.2 hk.symm
  · rintro ⟨pre, a, post, rfl, ha, ht, hn⟩
    have hp : p ∈ step (Run pre) a := by
      have heq : (p.1, a.time) = p := by rw [ht]
      simp [step, ha, heq]
    have hpost := binding_preserved hp post hn
    simpa [Run, applySeq, List.foldl_append] using hpost

/-- A relation edge cannot point from a suffix into a preceding position. -/
theorem not_edge_to_prefix {R : (D K V).Event → (D K V).Event → Prop}
    {pre post : List (D K V).Event} {a r : (D K V).Event}
    (hr : respects (pre ++ a :: post) R) (hm : r ∈ pre) : ¬ R a r :=
  (List.pairwise_append.mp hr).2.2 r hm a (by simp)

theorem not_edge_from_suffix {R : (D K V).Event → (D K V).Event → Prop}
    {pre post : List (D K V).Event} {a r : (D K V).Event}
    (hr : respects (pre ++ a :: post) R) (hm : r ∈ post) : ¬ R r a :=
  (List.pairwise_cons.mp (List.pairwise_append.mp hr).2.1).1 r hm

/-- No `del` of key `k` in `E` sees the `set` event `a`. -/
def Survives (C : Configuration (D K V).toMRDTSig)
    (E : Set (D K V).Event) (a : (D K V).Event) (k : K) : Prop :=
  ¬ ∃ r ∈ E, C.vis a r ∧ r.op = AppOp.del k

/-- The binding `p` is live in `E`. -/
def Live (C : Configuration (D K V).toMRDTSig)
    (E : Set (D K V).Event) (p : (K × V) × Timestamp) : Prop :=
  ∃ a ∈ E, a.op = AppOp.set p.1.1 p.1.2 ∧ a.time = p.2 ∧ Survives C E a p.1.1

/-- **Fact 1.** Any replay of `E` that respects `lo^C_E` contains exactly the
live bindings, so the state does not depend on which replay was taken. -/
theorem mem_run_iff_live {C : Configuration (D K V).toMRDTSig}
    {E : Set (D K V).Event} {ops : List (D K V).Event}
    (hp : listPermOf ops E) (hr : respects ops (loOn C.replayContext E))
    (p : (K × V) × Timestamp) : p ∈ Run ops ↔ Live C E p := by
  rw [mem_run_iff_suffix]
  constructor
  · rintro ⟨pre, a, post, hs, ha, ht, hn⟩
    subst ops
    refine ⟨a, (hp.2 a).mp (by simp), ha, ht, ?_⟩
    rintro ⟨r, hre, hv, hdel⟩
    have hm : r ∈ pre ++ a :: post := (hp.2 r).mpr hre
    rcases List.mem_append.mp hm with hm | hm
    · apply not_edge_to_prefix hr hm
      exact Or.inl ⟨hv, Or.inr ((replayBefore_iff r a).mpr ⟨p.1.1, p.1.2, hdel, ha⟩)⟩
    · rcases List.mem_cons.mp hm with heq | hm
      · rw [heq, ha] at hdel; cases hdel
      · exact hn r hm hdel
  · rintro ⟨a, hae, ha, ht, hn⟩
    obtain ⟨pre, post, hs⟩ := List.append_of_mem ((hp.2 a).mpr hae)
    refine ⟨pre, a, post, hs, ha, ht, ?_⟩
    subst ops
    intro r hm hdel
    apply not_edge_from_suffix hr hm
    have hre : r ∈ E := (hp.2 r).mp (by simp [hm])
    have hrc : (D K V).toMRDTSig.toUpdateSig.replayBefore r a :=
      (replayBefore_iff r a).mpr ⟨p.1.1, p.1.2, hdel, ha⟩
    by_cases hva : C.vis r a
    · exact Or.inl ⟨hva, Or.inl hrc⟩
    · refine Or.inr ⟨hva, ?_, hrc, ?_⟩
      · exact fun hv => hn ⟨r, hre, hv, hdel⟩
      · rintro ⟨c, hce, hvc, hc⟩
        rcases hc with hc | hc
        · obtain ⟨j, -, ha', -⟩ := (replayBefore_iff a c).mp hc
          rw [ha] at ha'; cases ha'
        · obtain ⟨j, w, hc, ha'⟩ := (replayBefore_iff c a).mp hc
          rw [ha] at ha'; injection ha' with hk hv
          subst j
          exact hn ⟨c, hce, hvc, hc⟩

theorem canonical_mem_iff {C : Configuration (D K V).toMRDTSig}
    {E : Set (D K V).Event} {s : St K V}
    (hs : Interface.IsCan (D K V) C E s) (p : (K × V) × Timestamp) :
    p ∈ s ↔ Live C E p := by
  obtain ⟨ops, hp, hr, hf⟩ := hs
  rw [← hf]
  exact mem_run_iff_live hp hr p

/-- **Fact 2.** Timestamps identify events, so at most one event can create a
given binding and liveness is a statement about that event alone. -/
theorem live_iff_fixed_set {C : Configuration (D K V).toMRDTSig}
    {E : Set (D K V).Event} (hsub : E ⊆ C.events)
    {p : (K × V) × Timestamp} {a : (D K V).Event}
    (hac : a ∈ C.events) (ha : a.op = AppOp.set p.1.1 p.1.2) (ht : a.time = p.2) :
    Live C E p ↔ a ∈ E ∧ Survives C E a p.1.1 := by
  constructor
  · rintro ⟨b, hb, -, hbt, hs⟩
    have heq : b = a := C.replayContext.ts_unique (hsub hb) hac (hbt.trans ht.symm)
    subst b
    exact ⟨hb, hs⟩
  · rintro ⟨he, hs⟩
    exact ⟨a, he, ha, ht, hs⟩

/-- **Fact 3.** Liveness over the union is the Boolean that `merge` computes.
The two `hk` steps are where causal closure is used. -/
theorem live_join {C : Configuration (D K V).toMRDTSig}
    {E₁ E₂ : Set (D K V).Event}
    (hsub₁ : E₁ ⊆ C.events) (hsub₂ : E₂ ⊆ C.events)
    (hclosed₁ : ∀ a b, C.vis a b →
      ¬ (D K V).toMRDTSig.toUpdateSig.commutes a b → b ∈ E₁ → a ∈ E₁)
    (hclosed₂ : ∀ a b, C.vis a b →
      ¬ (D K V).toMRDTSig.toUpdateSig.commutes a b → b ∈ E₂ → a ∈ E₂)
    (p : (K × V) × Timestamp) :
    Live C (E₁ ∪ E₂) p ↔
      (Live C (E₁ ∩ E₂) p ∧ Live C E₁ p ∧ Live C E₂ p) ∨
      (Live C E₁ p ∧ ¬ Live C (E₁ ∩ E₂) p) ∨
      (Live C E₂ p ∧ ¬ Live C (E₁ ∩ E₂) p) := by
  by_cases hex : ∃ a ∈ E₁ ∪ E₂, a.op = AppOp.set p.1.1 p.1.2 ∧ a.time = p.2
  · obtain ⟨a, hae, ha, ht⟩ := hex
    have hac : a ∈ C.events := hae.elim (fun h => hsub₁ h) (fun h => hsub₂ h)
    have huni : E₁ ∪ E₂ ⊆ C.events := fun e he => he.elim (fun h => hsub₁ h) (fun h => hsub₂ h)
    have hint : E₁ ∩ E₂ ⊆ C.events := fun e he => hsub₁ he.1
    rw [live_iff_fixed_set huni hac ha ht, live_iff_fixed_set hint hac ha ht,
      live_iff_fixed_set hsub₁ hac ha ht, live_iff_fixed_set hsub₂ hac ha ht]
    have hk₁ : ¬ Survives C E₁ a p.1.1 → a ∈ E₁ := by
      intro hn
      obtain ⟨r, hr, hv, hop⟩ := Classical.not_not.mp hn
      exact hclosed₁ a r hv ((noncomm_iff_replayBefore a r).mpr
        (Or.inr ((replayBefore_iff r a).mpr ⟨p.1.1, p.1.2, hop, ha⟩))) hr
    have hk₂ : ¬ Survives C E₂ a p.1.1 → a ∈ E₂ := by
      intro hn
      obtain ⟨r, hr, hv, hop⟩ := Classical.not_not.mp hn
      exact hclosed₂ a r hv ((noncomm_iff_replayBefore a r).mpr
        (Or.inr ((replayBefore_iff r a).mpr ⟨p.1.1, p.1.2, hop, ha⟩))) hr
    have hu : Survives C (E₁ ∪ E₂) a p.1.1 ↔
        Survives C E₁ a p.1.1 ∧ Survives C E₂ a p.1.1 := by
      simp only [Survives, Set.mem_union]
      constructor
      · intro h; exact ⟨fun ⟨r, hr, hv, ho⟩ => h ⟨r, Or.inl hr, hv, ho⟩,
          fun ⟨r, hr, hv, ho⟩ => h ⟨r, Or.inr hr, hv, ho⟩⟩
      · rintro ⟨h₁, h₂⟩ ⟨r, hr | hr, hv, ho⟩
        · exact h₁ ⟨r, hr, hv, ho⟩
        · exact h₂ ⟨r, hr, hv, ho⟩
    have hi₁ : Survives C E₁ a p.1.1 → Survives C (E₁ ∩ E₂) a p.1.1 :=
      fun h ⟨r, hr, hv, ho⟩ => h ⟨r, hr.1, hv, ho⟩
    have hi₂ : Survives C E₂ a p.1.1 → Survives C (E₁ ∩ E₂) a p.1.1 :=
      fun h ⟨r, hr, hv, ho⟩ => h ⟨r, hr.2, hv, ho⟩
    rw [hu]
    simp only [Set.mem_union, Set.mem_inter_iff]
    tauto
  · have hn (E : Set (D K V).Event) (hs : E ⊆ E₁ ∪ E₂) : ¬ Live C E p := by
      rintro ⟨a, ha, hop, ht, -⟩
      exact hex ⟨a, hs ha, hop, ht⟩
    have hnU := hn (E₁ ∪ E₂) Set.Subset.rfl
    have hnI := hn (E₁ ∩ E₂) (fun _ h => Or.inl h.1)
    have hn₁ := hn E₁ Set.subset_union_left
    have hn₂ := hn E₂ Set.subset_union_right
    simp [hnU, hnI, hn₁, hn₂]

/-- **The join lemma**, proved directly. -/
theorem joinLemma : Interface.JoinConfig (D K V) := by
  intro C E₁ E₂ s₀ s₁ s₂ htr hir hsub₁ hsub₂ hclosed₁ hclosed₂ hs₀ hs₁ hs₂
  obtain ⟨ops₁, hp₁, -, -⟩ := id hs₁
  obtain ⟨ops₂, hp₂, -, -⟩ := id hs₂
  have hpU := listPermOf_union (D := (D K V).toMRDTSig.toUpdateSig) hp₁ hp₂
  have hsubU : ∀ a ∈ E₁ ∪ E₂, a ∈ C.replayContext.events :=
    fun a ha => ha.elim (hsub₁ a) (hsub₂ a)
  obtain ⟨sU, hsU⟩ := isCanonicalState_exists_of_replayLaws
    (Metatheory.replayLaws laws rc_non_comm cond_comm) htr hir hpU hsubU
  have heq : (D K V).toMRDTSig.merge s₀ s₁ s₂ = sU := by
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

variable (K V)

/-- Issuance: `G(e, O) <=> true`. -/
def issuance : Issuance (D K V).toMRDTSig where
  CanIssue := fun _ _ => True

variable {K V}

/-- **What this row supplies for the direct route**: `Laws(D_type)` proved
by hand, and the join lemma. -/
theorem directObligations : DirectObligations (D K V) (issuance K V) :=
  ⟨laws, payloadDetermined, cond_comm, rc_non_comm, fun C _ => joinLemma C⟩

end LeanProofs.Implementations.SetWinsMap
