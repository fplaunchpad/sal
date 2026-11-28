import LeanProofs_no_spec_non_comm.Implementations.SetWinsMap.Definition
import LeanProofs_no_spec_non_comm.Metatheory.Adequacy
import LeanProofs_no_spec_non_comm.Soundness.RALinearizability

/-!
**A duplicate, plus one section.** Everything up to the last section is
`Implementations/SetWinsMap/VCs.lean` with the namespace changed. The last section
is what this folder adds: that `Soundness.joint` has no loop, which is all
`Soundness.certifiedSpecRA_any` asks of a row.

# The set-wins map: every obligation

`Laws(D_type, Spec)` of Section 4 and VC1 to VC5 of Section 5, all four laws
and all five conditions, for the tuple of `Definition.lean`. `obligations`
bundles what the metatheory consumes; `spec_non_comm` and `anyOrderSound` are the
two further premises `Soundness.certifiedSpecRA` asks for.
-/

namespace LeanProofs.NoSpecNonComm.Implementations.SetWinsMap

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface

variable {K V : Type} [DecidableEq K] [DecidableEq V]

/-- `rc` relates exactly the pairs `del k`, `set k v`. -/
@[simp] theorem rcBefore_iff (o₁ o₂ : AppOp K V) :
    (D K V).RcBefore o₁ o₂ ↔ ∃ k v, o₁ = .del k ∧ o₂ = .set k v := by
  cases o₁ with
  | set k w =>
      cases o₂ with
      | set j u => simp [Impl.RcBefore, rc]
      | del j => simp only [Impl.RcBefore, rc]; split <;> simp
  | del k =>
      cases o₂ with
      | set j u =>
          simp only [Impl.RcBefore, rc]
          by_cases h : k = j
          · subst h; simp
          · simp [h, Ne.symm h]
      | del j => simp [Impl.RcBefore, rc]

/-- The event-level reading of the same fact. -/
theorem eventRcBefore_iff (e₁ e₂ : (D K V).Event) :
    (D K V).EventRcBefore e₁ e₂ ↔ ∃ k v, e₁.op = .del k ∧ e₂.op = .set k v :=
  rcBefore_iff _ _

@[simp] theorem mem_step (S : St K V) (e : Event K V) (p : (K × V) × Timestamp) :
    p ∈ step S e ↔ match e.op with
    | .set k v => p = ((k, v), e.time) ∨ p ∈ S
    | .del k => p ∈ S ∧ p.1.1 ≠ k := by
  rcases e with ⟨t, r, o⟩; cases o <;> simp [step, Op.op, Op.time]

/-- Everything `rc` leaves unordered really does commute. -/
theorem commute_of_no_rc (e₁ e₂ : (D K V).Event)
    (h : ¬ ((D K V).EventRcBefore e₁ e₂ ∨ (D K V).EventRcBefore e₂ e₁)) :
    (D K V).Commutes e₁ e₂ := by
  simp only [eventRcBefore_iff, not_or] at h
  intro S
  change St K V at S
  rcases e₁ with ⟨t₁, r₁, o₁⟩; rcases e₂ with ⟨t₂, r₂, o₂⟩
  change step (step S _) _ = step (step S _) _
  cases o₁ <;> cases o₂ <;> ext p <;> simp [step, Op.op, Op.time] at h ⊢ <;> grind

/-- **RC-NON-COMM**. -/
theorem rc_non_comm (e₁ e₂ : (D K V).Event) :
    ¬ (D K V).Commutes e₁ e₂ ↔
      (D K V).EventRcBefore e₁ e₂ ∨ (D K V).EventRcBefore e₂ e₁ := by
  constructor
  · exact fun hn => Classical.byContradiction fun h => hn (commute_of_no_rc e₁ e₂ h)
  · intro hr hc
    rcases hr with hr | hr
    · obtain ⟨k, v, hd, hs⟩ := (eventRcBefore_iff _ _).mp hr
      have h := Finset.ext_iff.mp (hc (∅ : St K V)) ((k, v), e₂.time)
      simp [step, hd, hs] at h
    · obtain ⟨k, v, hd, hs⟩ := (eventRcBefore_iff _ _).mp hr
      have h := Finset.ext_iff.mp (hc (∅ : St K V)) ((k, v), e₁.time)
      simp [step, hd, hs] at h

/-- **NO-RC-CHAIN**. A `del` can only start an edge and a `set` can only end
one, so two edges never meet. -/
theorem no_rc_chain (o₁ o₂ o₃ : AppOp K V) :
    ¬ ((D K V).RcBefore o₁ o₂ ∧ (D K V).RcBefore o₂ o₃) := by
  rintro ⟨h₁, h₂⟩
  obtain ⟨k, v, -, hs⟩ := (rcBefore_iff _ _).mp h₁
  obtain ⟨j, -, hd, -⟩ := (rcBefore_iff _ _).mp h₂
  rw [hs] at hd; cases hd

/-! ### The absorber argument for COND-COMM

Swapping `del k` with a concurrent `set k v` changes the state only in the
bindings for `k`. The absorber is another `del k`, which erases exactly those
bindings, so the two orders agree after it. -/

/-- Two states that agree away from key `k`. -/
def EqExcept (k : K) (a b : St K V) : Prop := ∀ p, p.1.1 ≠ k → (p ∈ a ↔ p ∈ b)

theorem eqExcept_step {k : K} {a b : St K V} (h : EqExcept k a b) (e : Event K V) :
    EqExcept k (step a e) (step b e) := by
  intro p hp
  rcases e with ⟨t, r, o⟩; cases o <;> simp [step, Op.op, h p hp]

theorem eqExcept_applyList {k : K} {a b : St K V} (h : EqExcept k a b)
    (pi : List (D K V).Event) :
    EqExcept k ((D K V).applyList a pi) ((D K V).applyList b pi) := by
  induction pi generalizing a b with
  | nil => exact h
  | cons e pi ih => exact ih (eqExcept_step h e)

/-- **COND-COMM**. -/
theorem cond_comm (S : (D K V).Sigma) (e e' e'' : (D K V).Event)
    (pi : List (D K V).Event)
    (hrc : (D K V).EventRcBefore e e') (hnc : ¬ (D K V).Commutes e' e'') :
    (D K V).do_ ((D K V).applyList ((D K V).do_ ((D K V).do_ S e') e) pi) e''
      = (D K V).do_ ((D K V).applyList ((D K V).do_ ((D K V).do_ S e) e') pi) e'' := by
  obtain ⟨k, v, he, he'⟩ := (eventRcBefore_iff _ _).mp hrc
  have habs : e''.op = AppOp.del k := by
    rcases (rc_non_comm e' e'').mp hnc with h | h
    · obtain ⟨j, w, hd, -⟩ := (eventRcBefore_iff _ _).mp h
      rw [he'] at hd; cases hd
    · obtain ⟨j, w, hd, hs⟩ := (eventRcBefore_iff _ _).mp h
      rw [he'] at hs; injection hs with hkj _; subst j; exact hd
  have hbase : EqExcept k (step (step S e') e) (step (step S e) e') := by
    intro p hp; simp [step, he, he', hp]
  have hfold := eqExcept_applyList hbase pi
  change step _ e'' = step _ e''
  ext p
  simp only [step, habs, Finset.mem_filter]
  by_cases hp : p.1.1 = k
  · simp [hp]
  · exact and_congr (hfold p hp) Iff.rfl

/-- `Laws(D_type)`: RC-NON-COMM over concurrent events, NO-RC-CHAIN and
COND-COMM. -/
theorem laws : Laws (D K V) := ⟨rcNonComm_of_exact no_rc_chain (fun e₁ e₂ _ _ => rc_non_comm e₁ e₂),
  no_rc_chain,
  fun S e e' e'' pi _ _ => cond_comm S e e' e'' pi⟩

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
def Survives (C : Ctx (D K V))
    (E : Set (D K V).Event) (a : (D K V).Event) (k : K) : Prop :=
  ¬ ∃ r ∈ E, C.vis a r ∧ r.op = AppOp.del k

/-- The binding `p` is live in `E`. -/
def Live (C : Ctx (D K V))
    (E : Set (D K V).Event) (p : (K × V) × Timestamp) : Prop :=
  ∃ a ∈ E, a.op = AppOp.set p.1.1 p.1.2 ∧ a.time = p.2 ∧ Survives C E a p.1.1

/-- **Fact 1.** Any replay of `E` that respects `lo^C_E` contains exactly the
live bindings, so the state does not depend on which replay was taken. -/
theorem mem_run_iff_live {C : Ctx (D K V)}
    {E : Set (D K V).Event} {ops : List (D K V).Event}
    (hp : listPermOf ops E) (hr : respects ops (loOn C E))
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

theorem canonical_mem_iff {C : Ctx (D K V)}
    {E : Set (D K V).Event} {s : St K V}
    (hs : Interface.IsCanOn (D K V) C E s) (p : (K × V) × Timestamp) :
    p ∈ s ↔ Live C E p := by
  obtain ⟨ops, hp, hr, hf⟩ := hs
  rw [← hf]
  exact mem_run_iff_live hp hr p

/-- **Fact 2.** Timestamps identify events, so at most one event can create a
given binding and liveness is a statement about that event alone. -/
theorem live_iff_fixed_set {C : Ctx (D K V)}
    {E : Set (D K V).Event} (hsub : E ⊆ C.events)
    {p : (K × V) × Timestamp} {a : (D K V).Event}
    (hac : a ∈ C.events) (ha : a.op = AppOp.set p.1.1 p.1.2) (ht : a.time = p.2) :
    Live C E p ↔ a ∈ E ∧ Survives C E a p.1.1 := by
  constructor
  · rintro ⟨b, hb, -, hbt, hs⟩
    have heq : b = a := C.ts_unique (hsub hb) hac (hbt.trans ht.symm)
    subst b
    exact ⟨hb, hs⟩
  · rintro ⟨he, hs⟩
    exact ⟨a, he, ha, ht, hs⟩

/-- **Fact 3.** Liveness over the union is the Boolean that `merge` computes.
The two `hk` steps are where causal closure is used. -/
theorem live_join {C : Ctx (D K V)}
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

/-! ## VC1 and VC2

Two of the five hold at arbitrary states for this `merge`, so they are set
identities with no premises, exactly as a grow-only row's are. -/

/-- `merge(l,a,b) = merge(l,b,a)` at any states. This is **VC1** exactly:
the paper states it over arbitrary states too. -/
theorem vc1_merge_comm (l a b : (D K V).Sigma) :
    (D K V).merge l a b = (D K V).merge l b a := by
  change mergeState l a b = mergeState l b a
  ext p
  simp only [mergeState, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  tauto

/-- `merge(sigma0, sigma0, s) = s` at any `s`. **VC2** asks for it only at a
canonical `s`. -/
theorem vc2_merge_init (s : (D K V).Sigma) :
    (D K V).merge (D K V).sigma0 (D K V).sigma0 s = s := by
  change mergeState ∅ ∅ s = s
  ext p
  simp only [mergeState, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  simp

/-! ## The three canonical conditions

The states VC3, VC4 and VC5 mention are canonical for event sets built from
`E1`, `E2` and `down(e)`. Each nest of merges is read pointwise through
`canonical_mem_iff` and resolved by `live_join`, the row's own description
of liveness over a union.

`mergeProp` below is the Boolean `merge` computes at a record. Writing both
`merge` and `live_join` in that one shape turns VC3 and VC5 into chains of
rewrites with no propositional search at all. -/

/-- The Boolean `merge` computes at a single record: keep it when the base
and both branches have it, or when one branch has it and the base does
not. -/
def mergeProp (L B C : Prop) : Prop := (L ∧ B ∧ C) ∨ (B ∧ ¬ L) ∨ (C ∧ ¬ L)

theorem mem_merge (l a b : (D K V).Sigma) (p : (K × V) × Timestamp) :
    p ∈ (D K V).merge l a b ↔ mergeProp (p ∈ l) (p ∈ a) (p ∈ b) := by
  change p ∈ mergeState l a b ↔ _
  simp only [mergeState, mergeProp, Finset.mem_union, Finset.mem_inter,
    Finset.mem_sdiff]
  tauto

/-- `live_join` in `mergeProp` shape: liveness over a union is exactly the
Boolean `merge` computes from liveness over the intersection and over each
branch. -/
theorem live_merge {C : Ctx (D K V)} {E₁ E₂ : Set (D K V).Event}
    (h₁ : SupportedOn (D K V) C E₁) (h₂ : SupportedOn (D K V) C E₂)
    (c₁ : WeaklyClosed (D K V) C E₁) (c₂ : WeaklyClosed (D K V) C E₂)
    (p : (K × V) × Timestamp) :
    Live C (E₁ ∪ E₂) p
      ↔ mergeProp (Live C (E₁ ∩ E₂) p) (Live C E₁ p) (Live C E₂ p) :=
  live_join h₁ h₂ c₁ c₂ p

/-- `e(can(down(e) \ {e})) = can(down(e))`: the downset's own peel. -/
theorem isCan_downset {C : Ctx (D K V)} {m : (D K V).Sigma} {e : (D K V).Event}
    (htr : ∀ {a b c : (D K V).Event}, C.vis a b → C.vis b c → C.vis a c)
    (hir : ∀ a : (D K V).Event, ¬ C.vis a a)
    (hm : IsCanOn (D K V) C (downset C e \ {e}) m) :
    IsCanOn (D K V) C (downset C e) ((D K V).do_ m e) := by
  letI : EventOrder (D K V).toMRDTSig.toUpdateSig := Interface.rcOrder (D K V)
  exact isCanonicalState_snoc (Or.inl rfl) (downset_max htr hir) hm

/-- **VC3** LOCAL-REDISTRIBUTE, proved for this row.

Both sides are liveness over `E1 u E2`. The left reaches it through
`E1 = (E1 \ {e}) u down(e)` and then `E1 u E2`; the right through
`(E1 u E2) \ {e} = (E1 \ {e}) u E2` and then
`(E1 u E2) = ((E1 u E2) \ {e}) u down(e)`. Four instances of `live_merge`,
and the equation falls out by rewriting. -/
theorem vc3_local_redistribute :
    ∀ (C : Ctx (D K V)) (E₁ E₂ : Set (D K V).Event) (l m x y : (D K V).Sigma)
      (e : (D K V).Event),
      VisStrict (D K V) C →
      SupportedOn (D K V) C E₁ → SupportedOn (D K V) C E₂ →
      WeaklyClosed (D K V) C E₁ → WeaklyClosed (D K V) C E₂ →
      e ∈ E₁ → e ∉ E₂ → MaximalOn (D K V) C (E₁ ∪ E₂) e →
      IsCanOn (D K V) C (E₁ ∩ E₂) l →
      IsCanOn (D K V) C (downset C e \ {e}) m →
      IsCanOn (D K V) C (E₁ \ {e}) x →
      IsCanOn (D K V) C E₂ y →
      (D K V).merge l ((D K V).merge m x ((D K V).do_ m e)) y
        = (D K V).merge m ((D K V).merge l x y) ((D K V).do_ m e) := by
  letI : EventOrder (D K V).toMRDTSig.toUpdateSig := Interface.rcOrder (D K V)
  intro C E₁ E₂ l m x y e hvs h₁ h₂ hc₁ hc₂ he₁ he₂ hmax hl hm hx hy
  obtain ⟨htr, hir⟩ := hvs
  have hcov : ∀ a b : (D K V).Event, ¬ (D K V).toMRDTSig.toUpdateSig.commutes a b →
      ((D K V).toMRDTSig.toUpdateSig.replayBefore a b ∨
        (D K V).toMRDTSig.toUpdateSig.replayBefore b a) :=
    fun a b => (noncomm_iff_replayBefore a b).mp
  have hdsub : downset C e ⊆ E₁ := downset_subset hc₁ he₁
  have hdm := isCan_downset htr hir hm
  have hsupU : SupportedOn (D K V) C (E₁ ∪ E₂) := fun a ha => ha.elim (h₁ a) (h₂ a)
  have hdsupp : SupportedOn (D K V) C (downset C e) := fun a ha => h₁ a (hdsub ha)
  have hcld : WeaklyClosed (D K V) C (downset C e) := fun a b => downset_closed a b
  have hclU : WeaklyClosed (D K V) C (E₁ ∪ E₂) := weaklyClosed_union hc₁ hc₂
  have hclx : WeaklyClosed (D K V) C (E₁ \ {e}) :=
    closure_diff_of_max hcov Set.subset_union_left hc₁ hmax
  have hclU' : WeaklyClosed (D K V) C ((E₁ ∪ E₂) \ {e}) :=
    closure_diff_of_max hcov Set.Subset.rfl hclU hmax
  have i₁ : (E₁ \ {e}) ∩ downset C e = downset C e \ {e} := by
    ext z; exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hdsub h.1, h.2⟩, h.1⟩⟩
  have u₁ : (E₁ \ {e}) ∪ downset C e = E₁ := by
    ext z; constructor
    · rintro (⟨hz, -⟩ | hz); · exact hz
      · exact hdsub hz
    · intro hz; by_cases hze : z = e
      · exact Or.inr (Or.inl hze)
      · exact Or.inl ⟨hz, hze⟩
  have i₂ : (E₁ \ {e}) ∩ E₂ = E₁ ∩ E₂ := by
    ext z
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, fun hq => he₂ (hq ▸ h.2)⟩, h.2⟩⟩
  have u₂ : (E₁ \ {e}) ∪ E₂ = (E₁ ∪ E₂) \ {e} := by
    ext z; constructor
    · rintro (⟨hz, hn⟩ | hz)
      · exact ⟨Or.inl hz, hn⟩
      · exact ⟨Or.inr hz, fun hq => he₂ (hq ▸ hz)⟩
    · rintro ⟨hz | hz, hn⟩
      · exact Or.inl ⟨hz, hn⟩
      · exact Or.inr hz
  have i₃ : ((E₁ ∪ E₂) \ {e}) ∩ downset C e = downset C e \ {e} := by
    ext z
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨Or.inl (hdsub h.1), h.2⟩, h.1⟩⟩
  have u₃ : ((E₁ ∪ E₂) \ {e}) ∪ downset C e = E₁ ∪ E₂ := by
    ext z; constructor
    · rintro (⟨hz, -⟩ | hz); · exact hz
      · exact Or.inl (hdsub hz)
    · intro hz; by_cases hze : z = e
      · exact Or.inr (Or.inl hze)
      · exact Or.inl ⟨hz, hze⟩
  ext p
  have jA := live_merge (fun a ha => h₁ a ha.1) hdsupp hclx hcld p
  rw [i₁, u₁] at jA
  have jB := live_merge h₁ h₂ hc₁ hc₂ p
  have jC := live_merge (fun a ha => h₁ a ha.1) h₂ hclx hc₂ p
  rw [i₂, u₂] at jC
  have jD := live_merge (fun a ha => hsupU a ha.1) hdsupp hclU' hcld p
  rw [i₃, u₃] at jD
  rw [mem_merge, mem_merge, mem_merge, mem_merge,
    canonical_mem_iff hl p, canonical_mem_iff hm p, canonical_mem_iff hx p,
    canonical_mem_iff hy p, canonical_mem_iff hdm p, ← jA, ← jB, ← jC, ← jD]

/-- The one fact about this row that **VC4** needs: in the removal case, a
record that survives `U \ {e}` but not `down(e) \ {e}` cannot carry the
element `e` removes.

The add that produced it must be seen by `e`. If `e` saw nothing of it,
`lo^C_U` would have an edge out of `e`: a visibility edge when `e` sees the
add, and otherwise the `rc` edge `rem x --rc--> add x`, whose absorber
clause can only be met by a second removal of `x` in `U`, which would have
killed the record in `U \ {e}` as well. Either way `e` is not maximal. -/
theorem live_of_removed {C : Ctx (D K V)} {U : Set (D K V).Event}
    {As Bs : (D K V).Sigma} {e : (D K V).Event} {k : K}
    (hUsub : SupportedOn (D K V) C U) (hUcl : WeaklyClosed (D K V) C U)
    (heU : e ∈ U) (hmax : MaximalOn (D K V) C U e) (hex : e.op = AppOp.del k)
    (hA : IsCanOn (D K V) C (U \ {e}) As)
    (hB : IsCanOn (D K V) C (downset C e \ {e}) Bs)
    (p : (K × V) × Timestamp) (hpA : p ∈ As) (hpx : p.1.1 = k) : p ∈ Bs := by
  letI : EventOrder (D K V).toMRDTSig.toUpdateSig := Interface.rcOrder (D K V)
  have hdsub : downset C e ⊆ U := downset_subset hUcl heU
  obtain ⟨α, hαU, hαop, hαt, hαs⟩ := (canonical_mem_iff hA p).mp hpA
  have hrbe : (D K V).toMRDTSig.toUpdateSig.replayBefore e α := by
    rw [replayBefore_iff]; exact ⟨k, p.1.2, hex, by rw [hαop, hpx]⟩
  have hvis : C.vis α e := by
    by_contra hnv
    by_cases hve : C.vis e α
    · exact hmax α hαU.1 hαU.2 (Or.inl ⟨hve, Or.inl hrbe⟩)
    · by_cases habs : ∃ e₃ ∈ U, C.vis α e₃ ∧
          ((D K V).toMRDTSig.toUpdateSig.replayBefore α e₃ ∨
            (D K V).toMRDTSig.toUpdateSig.replayBefore e₃ α)
      · obtain ⟨e₃, he₃U, hv₃, hrb₃⟩ := habs
        have he₃op : e₃.op = AppOp.del p.1.1 := by
          rcases hrb₃ with h | h
          · rw [replayBefore_iff] at h
            obtain ⟨_, _, hy, _⟩ := h
            rw [hαop] at hy; cases hy
          · rw [replayBefore_iff] at h
            obtain ⟨k', v', hy, hy'⟩ := h
            rw [hαop] at hy'
            injection hy' with hk hv
            exact hk ▸ hy
        exact hαs ⟨e₃, ⟨he₃U, by rintro rfl; exact hnv hv₃⟩, hv₃, he₃op⟩
      · exact hmax α hαU.1 hαU.2 (Or.inr ⟨hve, hnv, hrbe, habs⟩)
  have hnc : ¬ (D K V).toMRDTSig.toUpdateSig.commutes α e :=
    (noncomm_iff_replayBefore α e).mpr (Or.inr hrbe)
  rw [canonical_mem_iff hB]
  refine ⟨α, ⟨Or.inr (Relation.TransGen.single ⟨hvis, hnc⟩), hαU.2⟩, hαop, hαt, ?_⟩
  rintro ⟨r, hr, hv, hop⟩
  exact hαs ⟨r, ⟨hdsub hr.1, hr.2⟩, hv, hop⟩

/-- **VC4** CAUSAL-DELTA, proved for this row rather than derived from the
join lemma. The two cases are the two shapes of `do`. -/
theorem vc4_causal_delta :
    ∀ (C : Ctx (D K V)) (U : Set (D K V).Event) (As Bs : (D K V).Sigma) (e : (D K V).Event),
      VisStrict (D K V) C →
      SupportedOn (D K V) C U → WeaklyClosed (D K V) C U →
      e ∈ U → MaximalOn (D K V) C U e →
      IsCanOn (D K V) C (U \ {e}) As →
      IsCanOn (D K V) C (downset C e \ {e}) Bs →
      (D K V).merge Bs As ((D K V).do_ Bs e) = (D K V).do_ As e := by
  letI : EventOrder (D K V).toMRDTSig.toUpdateSig := Interface.rcOrder (D K V)
  intro C U As Bs e hvs hUsub hUcl heU hmax hA hB
  obtain ⟨htr, hir⟩ := hvs
  change St K V at As Bs
  change mergeState Bs As (step Bs e) = step As e
  ext p
  cases hop : e.op with
  | set k v =>
      have hnB : (((k, v) : K × V), e.time) ∉ Bs := by
        intro hmem
        obtain ⟨α, hα, -, hαt, -⟩ := (canonical_mem_iff hB _).mp hmem
        exact hα.2 (C.ts_unique
          (hUsub α (downset_subset hUcl heU hα.1)) (hUsub e heU) hαt)
      have hkey : p = (((k, v) : K × V), e.time) → p ∉ Bs := by rintro rfl; exact hnB
      simp only [mergeState, Finset.mem_union, Finset.mem_inter,
        Finset.mem_sdiff, mem_step, hop]
      tauto
  | del k =>
      have hkey : p ∈ As → p ∉ Bs → p.1.1 ≠ k := fun hpA hpB hq =>
        hpB (live_of_removed hUsub hUcl heU hmax hop hA hB p hpA hq)
      simp only [mergeState, Finset.mem_union, Finset.mem_inter,
        Finset.mem_sdiff, mem_step, hop]
      tauto

/-- **VC5** REDISTRIBUTE, proved for this row.

`e` lies in both branches, so each of `E1 n E2`, `E1` and `E2` is its own
`\ {e}` part joined with `down(e)`: three peels. The left side is then
liveness over `E1 u E2` directly. The right side reaches the same place
through `(E1 u E2) \ {e} = (E1 \ {e}) u (E2 \ {e})` and one further
peel. -/
theorem vc5_redistribute :
    ∀ (C : Ctx (D K V)) (E₁ E₂ : Set (D K V).Event) (x₀ x₁ x₂ m : (D K V).Sigma)
      (e : (D K V).Event),
      VisStrict (D K V) C →
      SupportedOn (D K V) C E₁ → SupportedOn (D K V) C E₂ →
      WeaklyClosed (D K V) C E₁ → WeaklyClosed (D K V) C E₂ →
      e ∈ E₁ → e ∈ E₂ → MaximalOn (D K V) C (E₁ ∪ E₂) e →
      IsCanOn (D K V) C ((E₁ ∩ E₂) \ {e}) x₀ →
      IsCanOn (D K V) C (downset C e \ {e}) m →
      IsCanOn (D K V) C (E₁ \ {e}) x₁ →
      IsCanOn (D K V) C (E₂ \ {e}) x₂ →
      (D K V).merge ((D K V).merge m x₀ ((D K V).do_ m e))
          ((D K V).merge m x₁ ((D K V).do_ m e))
          ((D K V).merge m x₂ ((D K V).do_ m e))
        = (D K V).merge m ((D K V).merge x₀ x₁ x₂) ((D K V).do_ m e) := by
  letI : EventOrder (D K V).toMRDTSig.toUpdateSig := Interface.rcOrder (D K V)
  intro C E₁ E₂ x₀ x₁ x₂ m e hvs h₁ h₂ hc₁ hc₂ he₁ he₂ hmax hx₀ hm hx₁ hx₂
  obtain ⟨htr, hir⟩ := hvs
  have hcov : ∀ a b : (D K V).Event, ¬ (D K V).toMRDTSig.toUpdateSig.commutes a b →
      ((D K V).toMRDTSig.toUpdateSig.replayBefore a b ∨
        (D K V).toMRDTSig.toUpdateSig.replayBefore b a) :=
    fun a b => (noncomm_iff_replayBefore a b).mp
  have hdsub₁ : downset C e ⊆ E₁ := downset_subset hc₁ he₁
  have hdsub₂ : downset C e ⊆ E₂ := downset_subset hc₂ he₂
  have hdm := isCan_downset htr hir hm
  have hsupU : SupportedOn (D K V) C (E₁ ∪ E₂) := fun a ha => ha.elim (h₁ a) (h₂ a)
  have hdsupp : SupportedOn (D K V) C (downset C e) := fun a ha => h₁ a (hdsub₁ ha)
  have hcld : WeaklyClosed (D K V) C (downset C e) := fun a b => downset_closed a b
  have hclU : WeaklyClosed (D K V) C (E₁ ∪ E₂) := weaklyClosed_union hc₁ hc₂
  have hclI : WeaklyClosed (D K V) C (E₁ ∩ E₂) := by
    rintro a b hv hnc ⟨hb₁, hb₂⟩; exact ⟨hc₁ a b hv hnc hb₁, hc₂ a b hv hnc hb₂⟩
  have hcl₀ : WeaklyClosed (D K V) C ((E₁ ∩ E₂) \ {e}) :=
    closure_diff_of_max hcov (fun z hz => Or.inl hz.1) hclI hmax
  have hcl₁ : WeaklyClosed (D K V) C (E₁ \ {e}) :=
    closure_diff_of_max hcov Set.subset_union_left hc₁ hmax
  have hcl₂ : WeaklyClosed (D K V) C (E₂ \ {e}) :=
    closure_diff_of_max hcov Set.subset_union_right hc₂ hmax
  have hclU' : WeaklyClosed (D K V) C ((E₁ ∪ E₂) \ {e}) :=
    closure_diff_of_max hcov Set.Subset.rfl hclU hmax
  have peelI : ∀ F : Set (D K V).Event, downset C e ⊆ F →
      (F \ {e}) ∩ downset C e = downset C e \ {e} := by
    intro F hsub; ext z
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hsub h.1, h.2⟩, h.1⟩⟩
  have peelU : ∀ F : Set (D K V).Event, downset C e ⊆ F →
      (F \ {e}) ∪ downset C e = F := by
    intro F hsub; ext z; constructor
    · rintro (⟨hz, -⟩ | hz); · exact hz
      · exact hsub hz
    · intro hz; by_cases hze : z = e
      · exact Or.inr (Or.inl hze)
      · exact Or.inl ⟨hz, hze⟩
  have hdsubI : downset C e ⊆ E₁ ∩ E₂ := fun z hz => ⟨hdsub₁ hz, hdsub₂ hz⟩
  have hdsubU : downset C e ⊆ E₁ ∪ E₂ := fun z hz => Or.inl (hdsub₁ hz)
  have iM : (E₁ \ {e}) ∩ (E₂ \ {e}) = (E₁ ∩ E₂) \ {e} := by
    ext z
    exact ⟨fun h => ⟨⟨h.1.1, h.2.1⟩, h.1.2⟩, fun h => ⟨⟨h.1.1, h.2⟩, ⟨h.1.2, h.2⟩⟩⟩
  have uM : (E₁ \ {e}) ∪ (E₂ \ {e}) = (E₁ ∪ E₂) \ {e} := by
    ext z; constructor
    · rintro (⟨hz, hn⟩ | ⟨hz, hn⟩)
      · exact ⟨Or.inl hz, hn⟩
      · exact ⟨Or.inr hz, hn⟩
    · rintro ⟨hz | hz, hn⟩
      · exact Or.inl ⟨hz, hn⟩
      · exact Or.inr ⟨hz, hn⟩
  ext p
  have jP₀ := live_merge (fun a ha => h₁ a ha.1.1) hdsupp hcl₀ hcld p
  rw [peelI _ hdsubI, peelU _ hdsubI] at jP₀
  have jP₁ := live_merge (fun a ha => h₁ a ha.1) hdsupp hcl₁ hcld p
  rw [peelI _ hdsub₁, peelU _ hdsub₁] at jP₁
  have jP₂ := live_merge (fun a ha => h₂ a ha.1) hdsupp hcl₂ hcld p
  rw [peelI _ hdsub₂, peelU _ hdsub₂] at jP₂
  have jU := live_merge h₁ h₂ hc₁ hc₂ p
  have jM := live_merge (fun a ha => h₁ a ha.1) (fun a ha => h₂ a ha.1) hcl₁ hcl₂ p
  rw [iM, uM] at jM
  have jD := live_merge (fun a ha => hsupU a ha.1) hdsupp hclU' hcld p
  rw [peelI _ hdsubU, peelU _ hdsubU] at jD
  rw [mem_merge, mem_merge, mem_merge, mem_merge, mem_merge, mem_merge,
    canonical_mem_iff hx₀ p, canonical_mem_iff hm p, canonical_mem_iff hx₁ p,
    canonical_mem_iff hx₂ p, canonical_mem_iff hdm p,
    ← jP₀, ← jP₁, ← jP₂, ← jU, ← jM, ← jD]

/-- **VC1 to VC5** of Section 5, in the paper's form. VC1 and VC2 are
instances of the two equations above; the other three are already stated
canonically. -/
theorem joinLaws : CanonicalJoinLawsOn (D K V) (fun _ => True) where
  vc1_merge_comm := SetWinsMap.vc1_merge_comm
  vc2_merge_init := fun _ _ s _ _ _ => SetWinsMap.vc2_merge_init s
  vc3_local_redistribute := fun C E₁ E₂ l m x y e _ =>
    SetWinsMap.vc3_local_redistribute C E₁ E₂ l m x y e
  vc4_causal_delta := fun C U A B e _ => SetWinsMap.vc4_causal_delta C U A B e
  vc5_redistribute := fun C E₁ E₂ x₀ x₁ x₂ m e _ =>
    SetWinsMap.vc5_redistribute C E₁ E₂ x₀ x₁ x₂ m e

variable {K V : Type} [DecidableEq K] [DecidableEq V]

/-! ## `Spec` and the certificate -/

variable (K V)

variable {K V}

@[simp] theorem view_empty : view (∅ : St K V) = ∅ := by simp [view]

/-- Erasing the timestamps commutes with the update. -/
@[simp] theorem view_step (S : St K V) (e : (D K V).Event) :
    view (step S e) = (specMachine K V).update (view S) e.op := by
  rcases e with ⟨t, r, o⟩
  cases o with
  | set k v => simp [step, view, specMachine, Op.op, Op.time]
  | del k =>
      ext q
      simp only [view, step, specMachine, Op.op, Finset.mem_image,
        Finset.mem_filter]
      constructor
      · rintro ⟨w, ⟨hw, hwk⟩, rfl⟩; exact ⟨⟨w, hw, rfl⟩, hwk⟩
      · rintro ⟨⟨w, hw, hwq⟩, hqk⟩; exact ⟨w, ⟨hw, hwq ▸ hqk⟩, hwq⟩

theorem view_fold (S : St K V) (ops : List (D K V).Event) :
    view (applySeq (D K V).toMRDTSig.toUpdateSig S ops)
      = (ops.map Op.op).foldl (specMachine K V).update (view S) := by
  induction ops generalizing S with
  | nil => rfl
  | cons e ops ih => simpa [applySeq] using ih (step S e)

/-- The sequential premise: every replay of the implementation is explained
by the ordinary multimap language. -/
theorem anyOrderSound : Soundness.AnyOrderSound (D K V) (historySpec K V) := by
  intro pi q
  have hlabels : projectedUpdates (D := (D K V).toMRDTSig) pi
      = DeterministicSpec.updateLabels (pi.map Op.op) := by
    simp [projectedUpdates, DeterministicSpec.updateLabels, List.map_map,
      Function.comp]
  rw [hlabels, historySpec, (specMachine K V).updates_query_iff]
  change ((view (applySeq (D K V).toMRDTSig.toUpdateSig (∅ : St K V) pi)).filter
      (fun w => w.1 = q)).image Prod.snd = _
  rw [view_fold, view_empty]
  rfl

/-! ## `Laws(D_type, Spec)`: the fourth law

SPEC-NON-COMM is the one law of Section 4 that mentions `Spec`. In `Spec` a
`set` is an insertion and a `del` is a filter, so the only pair that can
conflict is a `set` and a `del` at the **same** key. That is exactly the pair
`rc` orders, so RC-NON-COMM read right to left says the implementation does
not commute it either. -/

/-- **SPEC-NON-COMM**: no implementation commutation erases a specification
conflict. -/
theorem spec_non_comm : Interface.spec_non_comm (D K V) (historySpec K V) := by
  intro e₁ e₂ hn hc
  refine hn (DeterministicSpec.language_commutes (specMachine K V) _ _ ?_)
  have hno : ¬ ((D K V).EventRcBefore e₁ e₂ ∨ (D K V).EventRcBefore e₂ e₁) :=
    fun h => (rc_non_comm e₁ e₂).mpr h hc
  simp only [eventRcBefore_iff, not_or, not_exists, not_and] at hno
  intro S
  change Finset (K × V) at S
  rcases h₁ : e₁.op with ⟨k, v⟩ | k <;> rcases h₂ : e₂.op with ⟨j, u⟩ | j <;>
    simp only [specMachine]
  · exact Finset.insert_comm _ _ _
  · have hkj : k ≠ j := fun h => hno.2 j v h₂ (by rw [h₁, h])
    rw [Finset.filter_insert, if_pos hkj]
  · have hkj : k ≠ j := fun h => hno.1 k u h₁ (by rw [h₂, ← h])
    rw [Finset.filter_insert, if_pos (Ne.symm hkj)]
  · ext p
    simp only [Finset.mem_filter]
    tauto

/-- **The bundle the specification route consumes**: the obligations of
Section 5 together with SPEC-NON-COMM, the one law of Section 4 that
mentions `Spec`. -/
theorem obligations : SpecObligations (D K V) (historySpec K V) :=
  SpecObligations.ofUniform laws rc_non_comm cond_comm joinLaws spec_non_comm

/-! # Specification visibility, without SPEC-NON-COMM

`Soundness.certifiedSpecRA_any` asks a row for one thing, that
`Soundness.joint` has no loop. For a row whose events all commute that is
immediate, `lo^C_E` being empty. This row's `rc` is **not** empty, so
`lo^C_E` carries same-time arrows between concurrent events, and such an
arrow is free to point backwards in time. The loop has to be ruled out.

It is ruled out because `rc` here runs a deletion to a write at the same key and nowhere else, so a
same-time arrow's target can start no further arrow, and it absorbs its
non-commuting visible successors by the side condition `lo^C_E` carries. Such
a target is therefore a **dead end**: no edge of `joint` leaves it at all.
Any loop would have to pass through one, and a loop with no same-time arrow
at all is a `vis` loop. That is `no_out` and `joint_acyclic`.

`edge_paperOrder` is where this row differs from the flags, and it is worth
being plain about it. For a row whose `rc` is indexed, like this one,
specification visibility cannot be absorbed into `vis` the way it can when
`rc` splits the alphabet globally: cross-index `vis` arrows would make that
relation loop. It is absorbed into `lo^C_E` instead, and that step is the
row's **own** SPEC-NON-COMM. So this row does not avoid the fourth law; what
it shows is that the law is not needed in the **adequacy theorem**, only in
the row, and that the criterion is reachable through the same `joint`
interface as everything else here.
-/

variable {C : Ctx (D K V)} {E : Set (D K V).Event}

/-- **Every edge of `joint` is a `lo^C_E` edge.** The right disjunct is one
already; the left is one by this row's SPEC-NON-COMM. -/
theorem edge_paperOrder {a b : (D K V).Event} (h : Soundness.joint (D K V) (historySpec K V) C E a b) :
    paperOrder (policy (D K V)) C E a b :=
  h.2.2.elim (fun hs => specVisibility_sub_paperOrder
    (Interface.spec_non_comm.covered spec_non_comm) _ E _ _ hs) id

/-- The target of a same-time arrow, with the side condition `lo^C_E`
carries. -/
def Blocked (C : Ctx (D K V)) (E : Set (D K V).Event) (w : (D K V).Event) : Prop :=
  w ∈ E ∧ (∃ k v, w.op = .set k v) ∧ ¬ ∃ c ∈ E, C.vis w c ∧ ¬ (D K V).Commutes w c

/-- A same-time arrow lands on one. -/
theorem blocked_of_concurrent {a b : (D K V).Event} (hbE : b ∈ E)
    (h : ¬ C.vis a b ∧ ¬ C.vis b a ∧ (D K V).RcBefore a.op b.op ∧
      ¬ ∃ c ∈ E, C.vis b c ∧ ¬ (D K V).Commutes b c) : Blocked C E b := by
  obtain ⟨k, v, -, hb⟩ := (eventRcBefore_iff a b).mp h.2.2.1
  exact ⟨hbE, ⟨k, v, hb⟩, h.2.2.2⟩

/-- **A `Blocked` event is a dead end.** Nothing leaves it: the absorber
kills the causal disjunct, and `rc` starts no arrow here. -/
theorem no_out {w z : (D K V).Event} (hw : Blocked C E w) : ¬ Soundness.joint (D K V) (historySpec K V) C E w z := by
  intro hj
  rcases edge_paperOrder hj with ⟨hv, hnc⟩ | hconc
  · exact hw.2.2 ⟨z, hj.2.1, hv, hnc⟩
  · obtain ⟨k, v, hwx⟩ := hw.2.1
    obtain ⟨k', v', hw', -⟩ := (eventRcBefore_iff w z).mp hconc.2.2.1
    rw [hwx] at hw'
    exact absurd hw' (by simp)

/-- Every path is causal, or has reached a dead end. -/
theorem vis_or_blocked (hvs : VisStrict (D K V) C) :
    ∀ {a b : (D K V).Event}, Relation.TransGen (Soundness.joint (D K V) (historySpec K V) C E) a b →
      C.vis a b ∨ Blocked C E b := by
  intro a b h
  induction h with
  | @single b hedge =>
    rcases edge_paperOrder hedge with ⟨hv, -⟩ | hconc
    · exact Or.inl hv
    · exact Or.inr (blocked_of_concurrent hedge.2.1 hconc)
  | @tail y z _ hedge ih =>
    rcases ih with hv | hb
    · rcases edge_paperOrder hedge with ⟨hv', -⟩ | hconc
      · exact Or.inl (hvs.1 hv hv')
      · exact Or.inr (blocked_of_concurrent hedge.2.1 hconc)
    · exact absurd hedge (no_out hb)

/-- **No loop.** A causal loop is impossible, and a loop through a dead end
would have to leave it. -/
theorem joint_acyclic : Soundness.JointAcyclic (D K V) (historySpec K V) := by
  intro C E hvs a h
  rcases vis_or_blocked hvs h with hv | hb
  · exact hvs.2 a hv
  · obtain ⟨b, hb', -⟩ := Relation.TransGen.head'_iff.mp h
    exact no_out hb hb'

end LeanProofs.NoSpecNonComm.Implementations.SetWinsMap

