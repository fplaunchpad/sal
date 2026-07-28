import Sal.ConditionedMRDTs.Metatheory.GenHonest

/-!
# The escrow safety metatheorem: Route B (counting/abstraction)

A generalization of the `bc_version_inv` proof shape. A datatype is
**measured** if a family of observations is affine under `update`
((B1): `obs k (update s e) = obs k s + μ k e` with ℕ-valued weights); then
folds compute *set* measures: enumeration-independence is free, no
commutativity, no causal witness, no `Inv`-preservation lemma. The escrow
theorem bounds a `{0,1}`-weighted *consuming* observation by a *funding* one
at every version, given: the guard–measure link ((B3): an applicable
consuming event certifies slack), consumption seriality ((B4): consuming
events are pairwise vis-comparable, typically issuer-determined classes via
`class_total_of_same_rep`), and honesty ((B5): each event was `applicable`
at a fold of its causal past, the ∀-enumeration `GenHonest` form, which is
exactly right here because measured guards are fold-order-insensitive). The
guard is an explicit parameter `A`: instance contracts live beside the flat
signature, so the bounded counter's configuration is over `BC`, whose
own `applicable` field is `⊤` and whose contract is `bcApplicable`.

Route B needs neither `CausalCanonical` nor `SafetyStep` and tolerates
arbitrary canonical witnesses; its price is (B1): the state must literally
count (the mergeable queue fails it: `deq` is an idempotent filter, not a
decrement). Neither Route A′ (`GenericSafety.lean`) nor Route B subsumes the
other; they overlap on the bounded counter (`bc_version_inv_escrow` is the
Route B re-derivation).

Also hosted here: the datatype-generic counting toolkit
(`exists_rel_max`, `countP_split`, `countP_le_one_of_unique`), consumed by
the theorem's vis-maximal-event argument.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

/-! ## §1  The counting toolkit -/

/-- Any nonempty duplicate-free list whose elements are pairwise comparable by
a transitive relation `R` has an `R`-maximal element. -/
theorem exists_rel_max {α : Type} (R : α → α → Prop)
    (htrans : ∀ {a b c}, R a b → R b c → R a c) :
    ∀ (l : List α), l ≠ [] → l.Nodup →
      (∀ a ∈ l, ∀ b ∈ l, a ≠ b → R a b ∨ R b a) →
      ∃ e ∈ l, ∀ d ∈ l, d ≠ e → R d e := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons a l ih =>
    intro _ hnd htot
    by_cases hl : l = []
    · subst hl
      refine ⟨a, List.mem_cons_self, ?_⟩
      intro d hd hne
      rcases List.mem_cons.mp hd with rfl | h
      · exact absurd rfl hne
      · exact absurd h List.not_mem_nil
    · have hnd' : l.Nodup := (List.nodup_cons.mp hnd).2
      have hanotin : a ∉ l := (List.nodup_cons.mp hnd).1
      have htot' : ∀ x ∈ l, ∀ y ∈ l, x ≠ y → R x y ∨ R y x := fun x hx y hy =>
        htot x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
      obtain ⟨e, he, hmax⟩ := ih hl hnd' htot'
      have hane : a ≠ e := fun h => hanotin (h ▸ he)
      rcases htot a List.mem_cons_self e (List.mem_cons_of_mem _ he) hane
        with hae | hea
      · refine ⟨e, List.mem_cons_of_mem _ he, ?_⟩
        intro d hd hne
        rcases List.mem_cons.mp hd with rfl | hdl
        · exact hae
        · exact hmax d hdl hne
      · refine ⟨a, List.mem_cons_self, ?_⟩
        intro d hd hne
        rcases List.mem_cons.mp hd with rfl | hdl
        · exact absurd rfl hne
        · by_cases hde : d = e
          · subst hde; exact hea
          · exact htrans (hmax d hdl hde) hea

/-- In a duplicate-free list, a predicate satisfied only by `e` counts at most
once. -/
theorem countP_le_one_of_unique {α : Type} {l : List α} {p : α → Bool} {e : α}
    (hnd : l.Nodup) (h : ∀ x ∈ l, p x = true → x = e) :
    l.countP p ≤ 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hnd' : l.Nodup := (List.nodup_cons.mp hnd).2
    have hanotin : a ∉ l := (List.nodup_cons.mp hnd).1
    rw [List.countP_cons]
    by_cases hpa : p a = true
    · have hae : a = e := h a List.mem_cons_self hpa
      have hzero : l.countP p = 0 := by
        rw [List.countP_eq_zero]
        intro x hx hpx
        have hxe : x = e := h x (List.mem_cons_of_mem _ hx) hpx
        rw [← hae] at hxe
        exact absurd (hxe ▸ hx) hanotin
      simp [hpa, hzero]
    · have hih := ih hnd' (fun x hx hpx => h x (List.mem_cons_of_mem _ hx) hpx)
      have hpa' : p a = false := by
        cases hp : p a
        · rfl
        · exact absurd hp hpa
      simp only [hpa', Bool.false_eq_true, if_false]
      omega

/-- Splitting a count along a second predicate. -/
theorem countP_split {α : Type} (l : List α) (p q : α → Bool) :
    l.countP p
      = l.countP (fun x => p x && q x) + l.countP (fun x => p x && !(q x)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons]
    cases p a <;> cases q a <;> simp <;> omega

/-! ## §2  Measured datatypes ((B1)) and the measure calculus -/

/-- **A measured datatype** ((B1)): a family of observations
`obs k : State → ℤ`, zero initially and affine under `update` with ℕ-valued
per-op weights `μ k`. Folds of measured observations compute set measures:
enumeration-independence is free. -/
structure Measured (D : ConditionedMRDTSig) (κ : Type) where
  /-- The observation family. -/
  obs : κ → D.State → ℤ
  /-- Per-op weights. ℕ-valued: observations only grow. -/
  μ : κ → Op D.AppOp → ℕ
  /-- Observations start at zero. -/
  obs_init : ∀ k, obs k D.init = 0
  /-- (B1) Affine update. -/
  obs_update : ∀ k s e, obs k (D.update s e) = obs k s + μ k e

section
variable {D : ConditionedMRDTSig} {κ : Type}

/-- The measure of an enumeration: the sum of its per-op weights. -/
def mSum (M : Measured D κ) (k : κ) (ρ : List (Op D.AppOp)) : ℕ :=
  (ρ.map (M.μ k)).sum

/-- Folds compute measures: `obs k` after a fold is the start value plus the
enumeration's measure, for *any* enumeration, no order or commutativity
hypotheses. -/
theorem Measured.obs_applySeq (M : Measured D κ) (k : κ) :
    ∀ (ρ : List (Op D.AppOp)) (s : D.State),
      M.obs k (applySeq D.toCRDTSig s ρ) = M.obs k s + (mSum M k ρ : ℤ) := by
  intro ρ
  induction ρ with
  | nil =>
    intro s
    show M.obs k s = M.obs k s + ((List.map (M.μ k) []).sum : ℤ)
    simp
  | cons e ρ ih =>
    intro s
    have hstep : applySeq D.toCRDTSig s (e :: ρ)
        = applySeq D.toCRDTSig (D.update s e) ρ := rfl
    rw [hstep, ih, M.obs_update]
    have hsum : mSum M k (e :: ρ) = M.μ k e + mSum M k ρ := by
      unfold mSum
      rw [List.map_cons, List.sum_cons]
    rw [hsum]
    push_cast
    omega

/-- Measures are monotone under sublists (weights are ℕ-valued). -/
theorem mSum_sublist_le (M : Measured D κ) (k : κ)
    {ρ₁ ρ₂ : List (Op D.AppOp)} (h : ρ₁.Sublist ρ₂) :
    mSum M k ρ₁ ≤ mSum M k ρ₂ := by
  induction h with
  | slnil => exact Nat.le_refl _
  | @cons l₁ l₂ a _ ih =>
    unfold mSum at ih ⊢
    rw [List.map_cons, List.sum_cons]
    omega
  | @cons₂ l₁ l₂ a _ ih =>
    unfold mSum at ih ⊢
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
    omega

/-- A `{0,1}`-weighted measure is a count. -/
theorem mSum_eq_countP (M : Measured D κ) (k : κ)
    (hμ : ∀ e, M.μ k e ≤ 1) :
    ∀ ρ : List (Op D.AppOp),
      mSum M k ρ = ρ.countP (fun e => decide (M.μ k e = 1)) := by
  intro ρ
  induction ρ with
  | nil => rfl
  | cons e ρ ih =>
    unfold mSum at ih ⊢
    rw [List.map_cons, List.sum_cons, List.countP_cons, ih]
    have h1 := hμ e
    by_cases h : M.μ k e = 1 <;> simp [h] <;> omega

/-! ## §3  The (B4) discharge helper and the escrow theorem -/

/-- **(B4) via issuer-determined classes**: a class whose members all carry
the same replica is pairwise vis-comparable (`vis_total_same_replica`). -/
theorem class_total_of_same_rep {C : Configuration D}
    {p : Op D.AppOp → Prop} {r : Replica}
    (hp : ∀ e, p e → e.2.1 = r) :
    ∀ a ∈ C.events, ∀ b ∈ C.events, a ≠ b → p a → p b →
      C.vis a b ∨ C.vis b a := by
  intro a ha b hb hne hpa hpb
  obtain ⟨r₁, s₁, hL₁, hs₁⟩ := ha
  obtain ⟨r₂, s₂, hL₂, hs₂⟩ := hb
  exact C.vis_total_same_replica hL₁ hs₁ hL₂ hs₂ hne
    ((hp a hpa).trans (hp b hpb).symm)

/-- **The escrow safety theorem**: for a measured datatype with a
`{0,1}`-weighted consuming observation `kc` and a funding observation `kf`
linked by the guard ((B3)), serial consumption ((B4)), and honest generation
((B5), the ∀-enumeration `GenHonest` form, measured guards being
fold-order-insensitive), every version satisfies
`0 ≤ obs kc ≤ obs kf`.

Proof = the `bc_version_inv` argument at the measure level: version
observations are set measures of the canonical enumeration; take the
vis-maximal consuming event `ê` ((B4) + `vis_trans` via `exists_rel_max`);
every other consuming event is vis-before `ê`, hence inside `past(ê) ⊆ E`
(`ver_causal`), bounding the strays by `ê` itself; honesty + (B3) at the
past-fold certify slack there; funding only grows from past to version. No
causal witness, no `Inv`-preservation. -/
theorem escrow_version_inv (M : Measured D κ) (kc kf : κ)
    (A : Op D.AppOp → D.State → Prop)
    (hμ01 : ∀ e, M.μ kc e ≤ 1)
    (hguard : ∀ e σ, M.μ kc e = 1 → A e σ →
      M.obs kc σ + 1 ≤ M.obs kf σ)
    {C : Configuration D} (hG : GoodConfig3 C)
    (hserial : ∀ a ∈ C.events, ∀ b ∈ C.events, a ≠ b →
      M.μ kc a = 1 → M.μ kc b = 1 → C.vis a b ∨ C.vis b a)
    (hHon : GenHonest D A C) :
    ∀ (v : Version) (s : D.State) (E : Set (Op D.AppOp)),
      C.ver v = some (s, E) →
      0 ≤ M.obs kc s ∧ M.obs kc s ≤ M.obs kf s := by
  intro v s E hv
  obtain ⟨ρ, hperm, _, hfold⟩ := hG.canonical v s E hv
  -- version observations are set measures
  have hobs : ∀ k, M.obs k s = (mSum M k ρ : ℤ) := by
    intro k
    rw [← hfold, M.obs_applySeq, M.obs_init]
    omega
  refine ⟨by rw [hobs kc]; exact_mod_cast Nat.zero_le _, ?_⟩
  rw [hobs kc, hobs kf]
  suffices h : mSum M kc ρ ≤ mSum M kf ρ by exact_mod_cast h
  have hcount : ∀ l : List (Op D.AppOp),
      mSum M kc l = l.countP (fun e => decide (M.μ kc e = 1)) :=
    mSum_eq_countP M kc hμ01
  by_cases hz : ρ.countP (fun e => decide (M.μ kc e = 1)) = 0
  · rw [hcount ρ, hz]
    exact Nat.zero_le _
  · -- there is a consuming event; take the vis-maximal one
    have hmem_events : ∀ x ∈ ρ, x ∈ C.events := fun x hx =>
      hG.ver_events_sub v s E hv x ((hperm.2 x).mp hx)
    have hne_filter : ρ.filter (fun e => decide (M.μ kc e = 1)) ≠ [] := by
      intro h
      apply hz
      rw [List.countP_eq_length_filter, h]
      rfl
    have hμ_of_mem : ∀ x ∈ ρ.filter (fun e => decide (M.μ kc e = 1)),
        M.μ kc x = 1 := by
      intro x hx
      have h := List.of_mem_filter hx
      exact of_decide_eq_true h
    have hsub_filter : ∀ x ∈ ρ.filter (fun e => decide (M.μ kc e = 1)),
        x ∈ ρ :=
      fun x hx => List.mem_of_mem_filter hx
    have htot : ∀ a ∈ ρ.filter (fun e => decide (M.μ kc e = 1)),
        ∀ b ∈ ρ.filter (fun e => decide (M.μ kc e = 1)), a ≠ b →
          C.vis a b ∨ C.vis b a := by
      intro a ha b hb hne
      exact hserial a (hmem_events a (hsub_filter a ha))
        b (hmem_events b (hsub_filter b hb)) hne
        (hμ_of_mem a ha) (hμ_of_mem b hb)
    obtain ⟨ê, hê_mem, hê_max⟩ :=
      exists_rel_max C.vis (fun hab hbc => hG.vis_trans hab hbc)
        (ρ.filter (fun e => decide (M.μ kc e = 1)))
        hne_filter (hperm.1.filter _) htot
    have hê_ρ : ê ∈ ρ := hsub_filter ê hê_mem
    have hê_E : ê ∈ E := (hperm.2 ê).mp hê_ρ
    have hê_events : ê ∈ C.events := hmem_events ê hê_ρ
    have hμê : M.μ kc ê = 1 := hμ_of_mem ê hê_mem
    -- the causal past of `ê`, enumerated inside the (closed) version
    have hπQ_perm : listPermOf (ρ.filter (fun x => decide (C.vis x ê)))
        {e' ∈ C.events | C.vis e' ê} := by
      constructor
      · exact hperm.1.filter _
      · intro x
        constructor
        · intro hx
          have hxρ : x ∈ ρ := List.mem_of_mem_filter hx
          have hvis : C.vis x ê := by
            have := List.of_mem_filter hx
            simpa using this
          exact ⟨hmem_events x hxρ, hvis⟩
        · rintro ⟨hxev, hvis⟩
          refine List.mem_filter.mpr ⟨?_, by simpa using hvis⟩
          exact (hperm.2 x).mpr (hG.ver_causal v s E hv x ê hvis hê_E)
    -- honesty + the guard–measure link at the past-fold, in measure form
    have happ := hHon ê hê_events _ hπQ_perm
    have hQ : mSum M kc (ρ.filter (fun x => decide (C.vis x ê))) + 1
        ≤ mSum M kf (ρ.filter (fun x => decide (C.vis x ê))) := by
      have h := hguard ê _ hμê happ
      rw [M.obs_applySeq, M.obs_applySeq, M.obs_init, M.obs_init] at h
      exact_mod_cast (by omega :
        (mSum M kc (ρ.filter (fun x => decide (C.vis x ê))) : ℤ) + 1
          ≤ (mSum M kf (ρ.filter (fun x => decide (C.vis x ê))) : ℤ))
    -- every other consuming event of the version is vis-before `ê`
    have hsplit : ρ.countP (fun e => decide (M.μ kc e = 1))
        = ρ.countP (fun x => decide (M.μ kc x = 1) && decide (C.vis x ê))
          + ρ.countP
              (fun x => decide (M.μ kc x = 1) && !(decide (C.vis x ê))) :=
      countP_split ρ _ _
    have hstray : ρ.countP
        (fun x => decide (M.μ kc x = 1) && !(decide (C.vis x ê))) ≤ 1 := by
      refine countP_le_one_of_unique (e := ê) hperm.1 ?_
      intro x hx hpx
      have hpx' : decide (M.μ kc x = 1) = true
          ∧ !(decide (C.vis x ê)) = true := by simpa using hpx
      have hxnvis : ¬ C.vis x ê := by simpa using hpx'.2
      by_contra hne
      exact hxnvis
        (hê_max x (List.mem_filter.mpr ⟨hx, hpx'.1⟩) hne)
    have hfiltQ : (ρ.filter (fun x => decide (C.vis x ê))).countP
          (fun e => decide (M.μ kc e = 1))
        = ρ.countP (fun x => decide (M.μ kc x = 1) && decide (C.vis x ê)) :=
      by rw [List.countP_filter]
    -- funding only grows from the past to the version
    have hfund : mSum M kf (ρ.filter (fun x => decide (C.vis x ê)))
        ≤ mSum M kf ρ :=
      mSum_sublist_le M kf List.filter_sublist
    have hcρ := hcount ρ
    have hcQ := hcount (ρ.filter (fun x => decide (C.vis x ê)))
    omega

end

/-! ## Axiom audit -/

#print axioms escrow_version_inv

end Sal.ConditionedMRDTs
