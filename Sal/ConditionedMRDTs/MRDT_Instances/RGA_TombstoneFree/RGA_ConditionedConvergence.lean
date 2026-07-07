import Sal.ConditionedMRDTs.Framework.ConditionedConvergence
import Sal.MRDTs.RGA_Tombstone_Free.RGA_Tombstone_Free_MRDT
import Sal.MRDTs.RGA_Tombstone_Free.RGA_Reachability_Invariant
import Sal.ConditionedMRDTs.Refutations.G2_Transport_Probe

/-!
# RGA conditioned-convergence assembly (up to observational `eq`)

The headline assembly for the tombstone-free RGA: two `loOnA`-respecting,
`noopFeasible` enumerations of a backward-closed reachable event set fold from
`init_st` to observationally-`eq` states.  Everything here works up to the RGA's
observational `eq` (NOT Lean `Eq`) — the eq-vs-Eq wall (`RGA_BubbleWiring.lean`
§2, `eq_strictly_weaker_than_Eq`) forbids the Lean-`Eq` σ-layer from hosting the
RGA directly, so we rebuild the fold-swap / bubble machinery over `eq`.

Built BOTTOM-UP, each layer 0-sorry:

* **§0 plumbing** — a concrete `applySeqR := foldl do_`, and `eq` as an
  equivalence (`eq_refl`, `eq_trans`; `eq_symm` is imported).
* **§1 eq-congruence of the fold** (`applySeqR_eq_congr`) — from `do_eq_congr`.
* **§2 generation base case** (`chainFaithful_of_accurate`) — an accurate op is
  `ChainFaithful` on its recorded list (the "routine" lift documented in
  `RGA_BubbleWiring` §3.4), using `id_mono` for chain-acyclicity.
* **§3 threading** — `NoFreshClash` for concurrent pairs from monotone
  allocation; `Faithful` along a single fold via base case +
  `chainFaithful_doIns`/`chainFaithful_doDel` + `climbFaithful_of_chain`.
* **§4 swap-at-fold** — `general_swap` discharges an observational swap witness,
  lifted to a fold swap (`applySeqR_swap_of_eqWitness`).
* **§5 eq-bubble** — a generic `eq`-bubble (`bubble_eq`) parameterised by a
  per-step swap-witness supply, mirroring `applySeq_bubble_to_front_loOn_u`.
* **§6 headline** — `RGA_conditioned_convergence` (see the layer's own doc for
  the exact hypotheses it consumes and the located obstruction).
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs.RGAConditionedConvergence

open Sal.Emulation

/-! ## §0  Plumbing: the concrete `eq`-fold and `eq` as an equivalence -/

/-- Concrete RGA fold: apply a list of ops left-to-right with `do_`. -/
def applySeqR (s : concrete_st) (π : List op_t) : concrete_st := π.foldl do_ s

@[simp] theorem applySeqR_nil (s : concrete_st) : applySeqR s [] = s := rfl

@[simp] theorem applySeqR_cons (s : concrete_st) (o : op_t) (π : List op_t) :
    applySeqR s (o :: π) = applySeqR (do_ s o) π := rfl

theorem applySeqR_append (s : concrete_st) (π₁ π₂ : List op_t) :
    applySeqR s (π₁ ++ π₂) = applySeqR (applySeqR s π₁) π₂ := by
  simp only [applySeqR, List.foldl_append]

/-- `eq` is reflexive. -/
theorem eq_refl (s : concrete_st) : eq s s := fun _ => ⟨rfl, fun _ => rfl⟩

/-- `eq` is transitive. -/
theorem eq_trans (a b c : concrete_st) (hab : eq a b) (hbc : eq b c) : eq a c := by
  intro k
  refine ⟨(hab k).1.trans (hbc k).1, ?_⟩
  intro hka
  exact ((hab k).2 hka).trans ((hbc k).2 ((hab k).1 ▸ hka))

/-! ## §1  eq-congruence of `do_` and of the fold -/

/-- `resolve` only reads `contains`, so `eq` states resolve any list identically. -/
theorem resolve_eq_congr (s s' : concrete_st) (h : eq s s') (L : List ℕ) :
    resolve s L = resolve s' L :=
  resolve_dom_eq s s' L (fun c _ => (h c).1)

/-- `upd` is `eq`-congruent in its base state (same key, same value). -/
theorem upd_eq_congr (s s' : concrete_st) (t : ℕ) (v : ℕ × ℕ) (h : eq s s') :
    eq (upd s t v) (upd s' t v) := by
  intro k
  refine ⟨?_, ?_⟩
  · rw [lemma_InDomUpd1, lemma_InDomUpd1, (h k).1]
  · intro hk
    by_cases hkt : t = k
    · subst hkt; rw [lemma_SelUpd1, lemma_SelUpd1]
    · have hne : (t : ℕ) != k := by simp only [bne_iff_ne, ne_eq]; exact hkt
      rw [lemma_SelUpd2 s k t v hne, lemma_SelUpd2 s' k t v hne]
      have hck : contains s k = true := by
        rw [lemma_InDomUpd2 s k t v hne] at hk; exact hk
      exact (h k).2 hck

/-- **eq-congruence of `do_` (the needed form).**  `eq s s' → eq (do_ s o) (do_ s' o)`.
The stored anchor depends only on `resolve` (which reads `contains`), so it agrees
across `eq` states; the `Del` case agrees pointwise via `contains_doDel`/`sel_doDel`. -/
theorem do_eq_congr (s s' : concrete_st) (h : eq s s') (o : op_t) :
    eq (do_ s o) (do_ s' o) := by
  obtain ⟨t, r, op⟩ := o
  cases op with
  | Ins e pre a =>
    simp only [do_]
    rw [resolve_eq_congr s s' h (a :: pre)]
    exact upd_eq_congr s s' t (e, resolve s' (a :: pre)) h
  | Del pre x =>
    intro k
    refine ⟨?_, ?_⟩
    · rw [contains_doDel, contains_doDel, (h k).1]
    · intro hk
      rw [contains_doDel, Bool.and_eq_true] at hk
      obtain ⟨hck, _⟩ := hk
      rw [sel_doDel, sel_doDel]
      have hsel : sel s k = sel s' k := (h k).2 hck
      have hanc : anc s k = anc s' k := by unfold anc; rw [hsel]
      have hel : el s k = el s' k := by unfold el; rw [hsel]
      have hres : resolve s pre = resolve s' pre := resolve_eq_congr s s' h pre
      rw [hanc, hel, hres, hsel]

/-- **eq-congruence of the fold (Layer 1).**  `eq s s' → eq (applySeqR s π) (applySeqR s' π)`. -/
theorem applySeqR_eq_congr (π : List op_t) (s s' : concrete_st) (h : eq s s') :
    eq (applySeqR s π) (applySeqR s' π) := by
  induction π generalizing s s' with
  | nil => exact h
  | cons o rest ih =>
    rw [applySeqR_cons, applySeqR_cons]
    exact ih (do_ s o) (do_ s' o) (do_eq_congr s s' h o)

/-! ## §2  Generation base case: an accurate op is `ChainFaithful`

Documented "routine, omitted" in `RGA_BubbleWiring` §3.4.  We supply it, using
`id_mono` to make the accurate ancestor chain acyclic (`chain_lt`: ids strictly
decrease rootward), which is exactly what lets `L.filter (≠ head)` peel the head
without disturbing the recursive tail. -/

/-- On an accurate chain the ids strictly decrease rootward (from `id_mono` +
`contains 0 = false`).  In particular the head never recurs in its own tail. -/
theorem chain_lt (s : concrete_st) (hmono : id_mono s) (h0 : contains s 0 = false) :
    ∀ (p : List ℕ) (leaf : ℕ), contains s leaf = true → IsAncPath s leaf p →
      ∀ x ∈ p, x < leaf := by
  intro p
  induction p with
  | nil => intro leaf _ _ x hx; simp at hx
  | cons c cs ih =>
    intro leaf hleaf hpath x hx
    simp only [IsAncPath] at hpath
    obtain ⟨hanc, hcc, hrest⟩ := hpath
    have hclt : c < leaf := by
      rcases hmono leaf hleaf with hz | hlt
      · have hc0 : c = 0 := by rw [← hanc]; exact hz
        rw [hc0, h0] at hcc; exact absurd hcc (by simp)
      · rw [hanc] at hlt; exact hlt
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hclt
    · exact lt_trans (ih c hcc hrest x hx') hclt

def GoodStep (s : concrete_st) (L : List ℕ) : op_t → Prop
  | (t, _, .Ins _ _ _) => t ≠ 0 ∧ t ∉ L
  | (_, _, .Del pre x) => contains s 0 = false ∧ accurate (0, 0, .Del pre x) s

def GoodFold (L : List ℕ) : concrete_st → List op_t → Prop
  | _, [] => True
  | s, o :: rest => GoodStep s L o ∧ GoodFold L (do_ s o) rest

def EqSwap (a b : op_t) (s : concrete_st) : Prop :=
  eq (do_ (do_ s a) b) (do_ (do_ s b) a)

/-- **Swap-at-fold (Layer 4).**  A pointwise `EqSwap` at the prefix fold lifts to
an `eq` between the two adjacent orderings of the full fold. -/
theorem applySeqR_swap_of_eqWitness (a b : op_t) (pfx sfx : List op_t) (s : concrete_st)
    (h_sw : EqSwap a b (applySeqR s pfx)) :
    eq (applySeqR s (pfx ++ a :: b :: sfx)) (applySeqR s (pfx ++ b :: a :: sfx)) := by
  rw [applySeqR_append, applySeqR_append]
  simp only [applySeqR_cons]
  exact applySeqR_eq_congr sfx _ _ h_sw

theorem bubble_eq (e : op_t) (σ tail : List op_t) (s : concrete_st)
    (h_sw : ∀ α β y, σ = α ++ y :: β → EqSwap y e (applySeqR s α)) :
    eq (applySeqR s (σ ++ e :: tail)) (applySeqR s (e :: (σ ++ tail))) := by
  induction σ generalizing s with
  | nil => exact eq_refl _
  | cons y σ' ih =>
    -- both sides are defeq to the fold that consumes `y` first:
    --   (y::σ') ++ e::tail  ≡  y :: (σ' ++ e::tail),   e :: ((y::σ')++tail) ≡ e :: y :: (σ'++tail)
    show eq (applySeqR (do_ s y) (σ' ++ e :: tail)) (applySeqR s (e :: y :: (σ' ++ tail)))
    have hih : eq (applySeqR (do_ s y) (σ' ++ e :: tail))
                  (applySeqR (do_ s y) (e :: (σ' ++ tail))) := by
      apply ih (do_ s y)
      intro α β z hσ'
      -- `applySeqR s (y :: α)` is defeq `applySeqR (do_ s y) α`
      exact h_sw (y :: α) β z (by simp [hσ'])
    have hswap : eq (applySeqR s (y :: e :: (σ' ++ tail)))
                    (applySeqR s (e :: y :: (σ' ++ tail))) := by
      have hw := applySeqR_swap_of_eqWitness y e [] (σ' ++ tail) s (h_sw [] σ' y rfl)
      simpa using hw
    -- hih's RHS `applySeqR (do_ s y) (e :: (σ'++tail))` is defeq hswap's LHS
    exact eq_trans _ _ _ hih hswap

/-! ## §6  The headline: RGA conditioned convergence up to `eq`

Two `lo`-respecting enumerations of the same event set fold from a common state to
observationally-`eq` states, GIVEN a swap oracle supplying an `EqSwap` witness for
every `lo`-incomparable pair at every prefix fold.  The proof is the peel-bubble-
recurse of `convergence_on_u` (`Sigma_LoOn3.lean`), up to `eq`, with the bubble of
§5; because the bubble consumes `EqSwap` directly, the overwriter/`h_ov`
machinery is not needed — only the peeled head's `lo`-minimality (from `respects`)
and the σ-elements' incomparability with it.  The oracle self-threads through the
recursion (`applySeqR (do_ s e) pre = applySeqR s (e :: pre)`).

**The oracle is the located obstruction.**  Discharging it means proving `EqSwap`
for every `lo`-incomparable (concurrent) pair at every prefix fold — i.e. running
`eqSwap_of_general` (§4) there.  Its premises `NoFreshClash` (concurrent, §3) and
the reachable-state invariants (`RgaInv`/`id_mono`, imported) transport; but
`general_swap` also needs ONE operand `accurate` and the other `Faithful` at the
swap state, and at a HYBRID fold state (interleaving two enumerations' prefixes) a
concurrent operand may be staled by concurrent deletes so that NEITHER is
`accurate` — the same "swaps visit states no execution visits" wall recorded in
`ConditionedConvergence` §5 and `RGA_BubbleWiring` §3.3, now in the `eq`-route. -/

/-- Generic `eq`-convergence engine: strong induction on `π₁.length`, peeling the
head, bubbling it to the front of `π₂`, and recursing.  Order-agnostic in `lo`.

**The oracle is RESTRICTED (GAP-1 fix).**  Rather than quantifying `pre` over ALL
lists — which is unsatisfiable, since several `EqSwap`-discharge conjuncts are
provably false at junk prefixes (`contains (fold [Ins 0 …]) 0 = false`;
`Faithful a` off `a`'s enablement) — the oracle is supplied only at the prefixes
the bubble actually visits: `pre` is a `nodup`, `respects`-ordered sub-list of the
pending set `evC`, disjoint from the swapped pair, at which BOTH `a` and `b` are
ENABLED (their entire `evC`-`lo`-past already lies in `pre`).  These are exactly the
`loOnA`-respecting delivery prefixes at which M1/M2 supply `Faithful`/`NoFreshClash`
etc.  The restriction SELF-THREADS through the recursion (`evC → evC \ {e}`,
`pre → e :: pre`) with no explicit accumulator — the enablement past shrinks with
`evC` and re-expands with the peeled head `e`. -/
theorem eq_convergence (lo : op_t → op_t → Prop) :
    ∀ (n : Nat) (s : concrete_st) (evC : Set op_t) (π₁ π₂ : List op_t),
      π₁.length = n → listPermOf π₁ evC → listPermOf π₂ evC →
      respects π₁ lo → respects π₂ lo →
      (∀ (pre : List op_t) (a b : op_t),
        (∀ x ∈ pre, x ∈ evC) → pre.Nodup → respects pre lo →
        a ∈ evC → b ∈ evC → a ∉ pre → b ∉ pre → a ≠ b → ¬ lo a b → ¬ lo b a →
        (∀ z ∈ evC, z ≠ a → lo z a → z ∈ pre) →
        (∀ z ∈ evC, z ≠ b → lo z b → z ∈ pre) →
        EqSwap a b (applySeqR s pre)) →
      eq (applySeqR s π₁) (applySeqR s π₂) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s evC π₁ π₂ h_len h₁p h₂p h₁r h₂r hOracle
    match π₁, h_len, h₁p, h₁r with
    | [], _, h₁p, _ =>
      obtain ⟨_, hm₁⟩ := h₁p
      have hev_empty : evC = ∅ := by
        ext a
        exact ⟨fun ha => absurd ((hm₁ a).mpr ha) List.not_mem_nil, fun ha => ha.elim⟩
      subst hev_empty
      obtain ⟨_, hm₂⟩ := h₂p
      have hπ₂_nil : π₂ = [] := by
        match π₂, hm₂ with
        | [], _ => rfl
        | x :: _, hm₂ => exact absurd ((hm₂ x).mp List.mem_cons_self) id
      subst hπ₂_nil
      exact eq_refl _
    | e :: π₁', h_len, h₁p, h₁r =>
      obtain ⟨hnd₁, hmem₁⟩ := h₁p
      obtain ⟨hnd₂, hmem₂⟩ := h₂p
      have he_in_ev : e ∈ evC := (hmem₁ e).mp List.mem_cons_self
      have he_in_π₂ : e ∈ π₂ := (hmem₂ e).mpr he_in_ev
      obtain ⟨σ, τ, hπ₂_split⟩ := List.append_of_mem he_in_π₂
      subst hπ₂_split
      rw [List.nodup_cons] at hnd₁
      have he_notin_π₁' : e ∉ π₁' := hnd₁.1
      rw [List.nodup_append, List.nodup_cons] at hnd₂
      have he_notin_σ : e ∉ σ := fun h => hnd₂.2.2 e h e (by simp) rfl
      have he_notin_τ : e ∉ τ := hnd₂.2.1.1
      have hστ_nodup : (σ ++ τ).Nodup := by
        rw [List.nodup_append]
        refine ⟨hnd₂.1, hnd₂.2.1.2, ?_⟩
        intro a ha b hb
        exact hnd₂.2.2 a ha b (List.mem_cons_of_mem _ hb)
      have h_e_lo_min : ∀ z ∈ evC, z ≠ e → ¬ lo z e := by
        intro z hz hz_ne
        have hz_in_π₁ : z ∈ e :: π₁' := (hmem₁ z).mpr hz
        have hz_in_π₁' : z ∈ π₁' := by
          rcases List.mem_cons.mp hz_in_π₁ with h | h
          · exact absurd h hz_ne
          · exact h
        exact (List.pairwise_cons.mp h₁r).1 z hz_in_π₁'
      have h_σ_sub_ev : ∀ y ∈ σ, y ∈ evC := fun y hy =>
        (hmem₂ y).mp (List.mem_append.mpr (Or.inl hy))
      have h_not_lo_fwd : ∀ y ∈ σ, ¬ lo e y := by
        intro y hy
        have h2 := List.pairwise_append.mp h₂r
        exact h2.2.2 y hy e List.mem_cons_self
      have hbubble : eq (applySeqR s (σ ++ e :: τ)) (applySeqR s (e :: (σ ++ τ))) := by
        apply bubble_eq e σ τ s
        intro α β y hσ_eq
        subst hσ_eq
        have hy_in_σ : y ∈ α ++ y :: β := List.mem_append.mpr (Or.inr List.mem_cons_self)
        have hy_in_ev : y ∈ evC := h_σ_sub_ev y hy_in_σ
        have hy_ne_e : y ≠ e := fun h => he_notin_σ (h ▸ hy_in_σ)
        -- eligibility of the prefix `α` for the swap of `(y, e)`
        have hnd_σ : (α ++ y :: β).Nodup := hnd₂.1
        have hα_sub : ∀ x ∈ α, x ∈ evC :=
          fun x hx => h_σ_sub_ev x (List.mem_append.mpr (Or.inl hx))
        have hα_nd : α.Nodup := (List.nodup_append.mp hnd_σ).1
        have hα_resp : respects α lo :=
          (List.pairwise_append.mp (List.pairwise_append.mp h₂r).1).1
        have hy_notin_α : y ∉ α :=
          fun h => (List.nodup_append.mp hnd_σ).2.2 y h y List.mem_cons_self rfl
        have he_notin_α : e ∉ α := fun h => he_notin_σ (List.mem_append.mpr (Or.inl h))
        have henab_y : ∀ z ∈ evC, z ≠ y → lo z y → z ∈ α := by
          intro z hz hzy hlo
          have hzπ : z ∈ (α ++ y :: β) ++ e :: τ := (hmem₂ z).mpr hz
          rcases List.mem_append.mp hzπ with hz1 | hz2
          · rcases List.mem_append.mp hz1 with hzα | hzyβ
            · exact hzα
            · rcases List.mem_cons.mp hzyβ with rfl | hzβ
              · exact absurd rfl hzy
              · exact absurd hlo
                  ((List.pairwise_cons.mp (List.pairwise_append.mp
                    (List.pairwise_append.mp h₂r).1).2.1).1 z hzβ)
          · exact absurd hlo
              ((List.pairwise_append.mp h₂r).2.2 y hy_in_σ z hz2)
        have henab_e : ∀ z ∈ evC, z ≠ e → lo z e → z ∈ α :=
          fun z hz hze hlo => absurd hlo (h_e_lo_min z hz hze)
        exact hOracle α y e hα_sub hα_nd hα_resp hy_in_ev he_in_ev hy_notin_α he_notin_α
          hy_ne_e (h_e_lo_min y hy_in_ev hy_ne_e) (h_not_lo_fwd y hy_in_σ) henab_y henab_e
      have h_len_new : π₁'.length < n := by
        rw [← h_len]; simp only [List.length_cons]; omega
      have hp₁' : listPermOf π₁' (evC \ {e}) := by
        refine ⟨hnd₁.2, fun a => ?_⟩
        simp only [Set.mem_diff, Set.mem_singleton_iff]
        constructor
        · intro ha
          refine ⟨(hmem₁ a).mp (List.mem_cons_of_mem _ ha), ?_⟩
          intro h_eq; subst h_eq; exact he_notin_π₁' ha
        · rintro ⟨hae, hne⟩
          rcases List.mem_cons.mp ((hmem₁ a).mpr hae) with h | h
          · exact absurd h hne
          · exact h
      have hpστ : listPermOf (σ ++ τ) (evC \ {e}) := by
        refine ⟨hστ_nodup, fun a => ?_⟩
        simp only [Set.mem_diff, Set.mem_singleton_iff, List.mem_append]
        constructor
        · rintro (ha | ha)
          · refine ⟨(hmem₂ a).mp (List.mem_append.mpr (Or.inl ha)), ?_⟩
            rintro rfl; exact he_notin_σ ha
          · refine ⟨(hmem₂ a).mp (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ ha))), ?_⟩
            rintro rfl; exact he_notin_τ ha
        · rintro ⟨hae, hne⟩
          rcases List.mem_append.mp ((hmem₂ a).mpr hae) with h | h
          · exact Or.inl h
          · rcases List.mem_cons.mp h with h' | h'
            · exact absurd h' hne
            · exact Or.inr h'
      have hr₁' : respects π₁' lo := (List.pairwise_cons.mp h₁r).2
      have hrστ : respects (σ ++ τ) lo := by
        have h2split := List.pairwise_append.mp h₂r
        rw [List.pairwise_cons] at h2split
        obtain ⟨hσ, ⟨_, hτ⟩, hcross⟩ := h2split
        rw [respects, List.pairwise_append]
        refine ⟨hσ, hτ, ?_⟩
        intro a ha b hb
        exact hcross a ha b (List.mem_cons_of_mem _ hb)
      have hOracle' : ∀ (pre : List op_t) (a b : op_t),
          (∀ x ∈ pre, x ∈ evC \ {e}) → pre.Nodup → respects pre lo →
          a ∈ evC \ {e} → b ∈ evC \ {e} → a ∉ pre → b ∉ pre → a ≠ b → ¬ lo a b → ¬ lo b a →
          (∀ z ∈ evC \ {e}, z ≠ a → lo z a → z ∈ pre) →
          (∀ z ∈ evC \ {e}, z ≠ b → lo z b → z ∈ pre) →
          EqSwap a b (applySeqR (do_ s e) pre) := by
        intro pre a b hsub hnd hresp ha hb hanp hbnp hab hnab hnba hena henb
        have he_notin_pre : e ∉ pre := fun h => (hsub e h).2 rfl
        -- lift each eligibility field from `pre / evC\{e}` to `e :: pre / evC`
        have hsub' : ∀ x ∈ e :: pre, x ∈ evC := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact he_in_ev
          · exact (hsub x hx').1
        have hnd' : (e :: pre).Nodup := List.nodup_cons.mpr ⟨he_notin_pre, hnd⟩
        have hresp' : respects (e :: pre) lo :=
          List.pairwise_cons.mpr
            ⟨fun x hx => h_e_lo_min x (hsub x hx).1 (fun he => (hsub x hx).2 he), hresp⟩
        have ha_notin : a ∉ e :: pre := by
          rw [List.mem_cons]; rintro (rfl | h)
          · exact ha.2 rfl
          · exact hanp h
        have hb_notin : b ∉ e :: pre := by
          rw [List.mem_cons]; rintro (rfl | h)
          · exact hb.2 rfl
          · exact hbnp h
        have hena' : ∀ z ∈ evC, z ≠ a → lo z a → z ∈ e :: pre := by
          intro z hz hza hlo
          by_cases hze : z = e
          · exact hze ▸ List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hena z ⟨hz, hze⟩ hza hlo)
        have henb' : ∀ z ∈ evC, z ≠ b → lo z b → z ∈ e :: pre := by
          intro z hz hzb hlo
          by_cases hze : z = e
          · exact hze ▸ List.mem_cons_self
          · exact List.mem_cons_of_mem _ (henb z ⟨hz, hze⟩ hzb hlo)
        have hh := hOracle (e :: pre) a b hsub' hnd' hresp' ha.1 hb.1 ha_notin hb_notin
          hab hnab hnba hena' henb'
        rw [applySeqR_cons] at hh
        exact hh
      have hrec : eq (applySeqR (do_ s e) π₁') (applySeqR (do_ s e) (σ ++ τ)) :=
        ih π₁'.length h_len_new (do_ s e) (evC \ {e}) π₁' (σ ++ τ) rfl hp₁' hpστ hr₁' hrστ hOracle'
      rw [applySeqR_cons]
      have hbubble' : eq (applySeqR (do_ s e) (σ ++ τ)) (applySeqR s (σ ++ e :: τ)) := by
        have h := eq_symm _ _ hbubble
        rw [applySeqR_cons] at h
        exact h
      exact eq_trans _ _ _ hrec hbubble'

/-- **RGA conditioned convergence (Layer 6, headline).**  Any two `lo`-respecting
enumerations `π₁ π₂` of a reachable event set `ev` fold from `init_st` to
observationally-`eq` states, given the swap oracle `hSwap` supplying `EqSwap` for
every `lo`-incomparable pair at every prefix fold.  Instantiate `lo` with
`ConditionedConvergence.loOnA RGACondSig C ev`.  `hSwap` is the single obligation
blocking a fully-unconditional close (see the §6 doc): it is exactly the
`eqSwap_of_general`-discharge that stalls at hybrid staled states. -/
theorem RGA_conditioned_convergence (lo : op_t → op_t → Prop) (ev : Set op_t)
    (π₁ π₂ : List op_t)
    (h₁p : listPermOf π₁ ev) (h₂p : listPermOf π₂ ev)
    (h₁r : respects π₁ lo) (h₂r : respects π₂ lo)
    (hSwap : ∀ (pre : List op_t) (a b : op_t),
        (∀ x ∈ pre, x ∈ ev) → pre.Nodup → respects pre lo →
        a ∈ ev → b ∈ ev → a ∉ pre → b ∉ pre → a ≠ b → ¬ lo a b → ¬ lo b a →
        (∀ z ∈ ev, z ≠ a → lo z a → z ∈ pre) → (∀ z ∈ ev, z ≠ b → lo z b → z ∈ pre) →
        EqSwap a b (applySeqR init_st pre)) :
    eq (applySeqR init_st π₁) (applySeqR init_st π₂) :=
  eq_convergence lo π₁.length init_st ev π₁ π₂ rfl h₁p h₂p h₁r h₂r hSwap


end Sal.ConditionedMRDTs.RGAConditionedConvergence
