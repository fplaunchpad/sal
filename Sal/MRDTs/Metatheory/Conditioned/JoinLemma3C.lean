import Sal.MRDTs.Metatheory.VC_Set
import Sal.MRDTs.Metatheory.Conditioned.Reunification_Peel_Obstruction
import Mathlib.Data.Fintype.Prod

/-!
# The closure-indexed Join Lemma (`JoinLemma3C`) and the peel-compatibility boundary

Stage 1 of `Development/CONDITIONED_METATHEORY_PLAN.md` (task #2): one Join
Lemma, indexed by a closure predicate `𝒞`, with the peel step of the
`join_lemma3_of_cd_feasible` induction (`Adequacy.lean:960`) isolated as an
explicit per-`𝒞` obligation — and the machine-checked verdict on which peel
granularities survive the Gate-G1 counterexample
(`Reunification_Peel_Obstruction.lean`).

## What is here

1. **The index** (`ClosurePred`, `weakClosure`, `fullClosure`) and
   **`JoinLemma3C`**. The two instantiation lemmas are *definitional*:
   `joinLemma3C_weak : JoinLemma3C D (weakClosure _) ↔ JoinLemma3 D` and
   `joinLemma3C_full : JoinLemma3C D (fullClosure _) ↔ JoinLemma3F D`, both
   `Iff.rfl`. `JoinLemma3C` is antitone in the index (`JoinLemma3C.anti`);
   in particular `JoinLemma3 D → JoinLemma3F D`
   (`joinLemma3F_of_joinLemma3`) — the hard direction of reunification is
   the converse, which is exactly what the EWFlag route needs and what the
   kill-test obstructs.

2. **`PeelCompatible D 𝒞`** — "every finite nonempty `𝒞`-closed `U` has a
   `loOn(U)`-maximal event whose removal preserves `𝒞` on every `𝒞`-closed
   subset of `U`" — the exact shape of the peel step of the existing
   induction.
   * Weak closure IS peel-compatible for every signature satisfying the
     update-layer VCs (`weakClosure_peelCompatible`, via
     `closure_diff_of_max`): this factors the peel argument out of
     `join_lemma3_of_cd_feasible` unchanged.
   * Full closure is NOT (`K2_fullClosure_not_peelCompatible`,
     `fullClosure_not_peelCompatible`) — direct corollary of the kill-test's
     `no_peelable_event`. The *same* signature `K2` witnesses both sides of
     the boundary: it satisfies `UpdateVCs` (`K2_updateVCs`, including
     `cond_comm_lift`, proved here), so
     `K2_weakClosure_peelCompatible` holds while the full-closure instance
     is refuted.

3. **VERDICT ON BLOCK PEELS (redesign (a) of the plan): DEAD.** The plan
   hoped a *block* peel — remove a vis-upward-closed `B ⊆ U` all of whose
   events are jointly late-placeable — would restore the full-closure
   induction. The two conditions are pinned generically
   (`diff_fullClosure_iff`: removal preserves full closure **iff** `B` is
   vis-upward-closed within `U`; `block_suffix_no_exit`: an enumeration
   ending in `B` forces no `loOn(U)`-edge to leave `B`), and then refuted on
   the kill-test `U`: the union cycle
   `A_y →vis R_x →loOn A_x →vis R_y →loOn A_y` makes every nonempty
   back-block equal to all of `U` (`back_block_forces_all`,
   `no_proper_back_block`), so no block peel makes progress. Front blocks
   (vis-downward-closed, jointly early-placeable) die symmetrically on the
   same cycle (`front_block_forces_all`, `no_proper_front_block`) — the
   asymmetry between fronts and backs does not help, because the cycle is
   direction-agnostic. The single-event obstruction is re-derived as the
   `B = {e}` special case (`no_peelable_event_of_blocks`), so the block
   theorem strictly strengthens the kill-test. Packaged:
   `block_peel_obstruction`.

4. **Redesign (b), the wider induction class**: `AlmostClosed` = fully
   closed set minus a `loOn(U)`-upward-closed peel set. Its
   *order-theoretic* half is mechanized and healthy: the class contains all
   fully closed sets (`almostClosed_of_fullClosure`), is stable under
   peeling any `loOn`-maximal event (`AlmostClosed.peel`), and such a peel
   always exists (`almostClosed_peel_exists`) — so the induction is
   well-founded on the order side, with no analogue of the peel
   obstruction. The kill-test's `U ∖ {A_x}` inhabits the class
   (`peelU_diff_Ax_almostClosed`) while NOT being fully closed
   (`peelU_diff_Ax_not_fullyClosed`): the extension is strict, and the
   first peel on the kill-test `U` itself goes through
   (`killTest_almostClosed_first_peel`).

## What remains open (documented, not sorried)

Since (a) is dead at *every* granularity on this `U`, redesigns (b) and (c)
of the plan doc are the only live routes to reunification:

* **(b)** needs the *state-side* re-founding: the Join statement must carry
  `AlmostClosed` sides (fully-closed-minus-peel-set as data, not just
  prop), and the contextual hypotheses of `CDVC3` /
  `FeasibleDeltaVCs3`-style laws must be restated at `AlmostClosed` sets.
  The downset component `B = σ(↓e ∖ e)` stays fully closed, so the CD
  equation's shape survives; what changes is which closure the sides and
  the union satisfy at re-entry of the IH. A generic `JoinLemma3C`-from-
  `PeelCompatible` induction would also need `𝒞` closed under union
  (`ev₁ ∪ ev₂` must be `𝒞`-closed when the sides are) — true for both
  instances here, an explicit obligation for exotic `𝒞`.
* **(c)** (disjunctive contract) needs no new mathematics: `JoinLemma3C`
  is already the single statement both routes instantiate
  (`joinLemma3C_weak` / `joinLemma3C_full`), so the typeclass packaging
  can dispatch on the index.
-/

namespace Sal.Metatheory

open Sal.Emulation
open Classical

/-! ## §1. The closure index -/

/-- A closure predicate on event sets of a configuration — the index of the
closure-indexed Join Lemma. Stated at the `CRDTSig` level: closure reads only
`vis` and `commutes`, never the merge. -/
abbrev ClosurePred (D : CRDTSig) : Type _ :=
  Sal.Emulation.Configuration D → Set (Op D.AppOp) → Prop

/-- **Weak closure**: closed under vis-predecessors along *non-commuting*
edges — verbatim the closure hypothesis of `JoinLemma3`
(`VC_Set.lean:65`). -/
def weakClosure (D : CRDTSig) : ClosurePred D :=
  fun C ev => ∀ a b, C.vis a b → ¬ D.commutes a b → b ∈ ev → a ∈ ev

/-- **Full causal closure**: closed under *all* vis-predecessors — verbatim
the closure hypothesis of `JoinLemma3F` (`VC_Set.lean:191`), and what
`GoodConfig3.ver_causal` actually supplies. -/
def fullClosure (D : CRDTSig) : ClosurePred D :=
  fun C ev => ∀ a b, C.vis a b → b ∈ ev → a ∈ ev

/-- Full closure implies weak closure (pointwise): the index is a genuine
strength ladder. -/
theorem weakClosure_of_fullClosure {D : CRDTSig}
    {C : Sal.Emulation.Configuration D} {ev : Set (Op D.AppOp)}
    (h : fullClosure D C ev) : weakClosure D C ev :=
  fun a b hv _ hb => h a b hv hb

/-! ## §2. The closure-indexed Join Lemma -/

section JoinLemmaC
variable {D : ConditionedMRDTSig}

/-- **The closure-indexed ternary Join Lemma.** `JoinLemma3`
(`VC_Set.lean:65`) and `JoinLemma3F` (`VC_Set.lean:191`) with the two
side-closure hypotheses abstracted into an index `𝒞`. The weak and full
instantiations below are definitional. -/
def JoinLemma3C (D : ConditionedMRDTSig) (𝒞 : ClosurePred D.toCRDTSig) :
    Prop :=
  ∀ (C : Sal.Emulation.Configuration D.toCRDTSig)
    (ev₁ ev₂ : Set (Op D.AppOp)) (s₀ s₁ s₂ : D.State),
    (∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c) →
    (∀ a : Op D.AppOp, ¬ C.vis a a) →
    (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
    𝒞 C ev₁ → 𝒞 C ev₂ →
    IsCanonicalState C (ev₁ ∩ ev₂) s₀ →
    IsCanonicalState C ev₁ s₁ → IsCanonicalState C ev₂ s₂ →
    IsCanonicalState C (ev₁ ∪ ev₂) (D.mergeL s₀ s₁ s₂)

/-- **Instantiation, weak**: at `weakClosure` the indexed lemma *is*
`JoinLemma3` — definitionally. -/
theorem joinLemma3C_weak (D : ConditionedMRDTSig) :
    JoinLemma3C D (weakClosure D.toCRDTSig) ↔ JoinLemma3 D :=
  Iff.rfl

/-- **Instantiation, full**: at `fullClosure` the indexed lemma *is*
`JoinLemma3F` — definitionally. -/
theorem joinLemma3C_full (D : ConditionedMRDTSig) :
    JoinLemma3C D (fullClosure D.toCRDTSig) ↔ JoinLemma3F D :=
  Iff.rfl

/-- `JoinLemma3C` is antitone in the index: strengthening the closure
demanded of the sides weakens the lemma. -/
theorem JoinLemma3C.anti {𝒞 𝒞' : ClosurePred D.toCRDTSig}
    (h_str : ∀ C ev, 𝒞' C ev → 𝒞 C ev)
    (hJ : JoinLemma3C D 𝒞) : JoinLemma3C D 𝒞' := by
  intro C ev₁ ev₂ s₀ s₁ s₂ h_tr h_ir h_in₁ h_in₂ h_cl₁ h_cl₂ hc₀ hc₁ hc₂
  exact hJ C ev₁ ev₂ s₀ s₁ s₂ h_tr h_ir h_in₁ h_in₂
    (h_str C ev₁ h_cl₁) (h_str C ev₂ h_cl₂) hc₀ hc₁ hc₂

/-- The easy direction of reunification, now a two-liner: the weak-closure
Join Lemma implies the full-closure one. The research problem (Gate G1) is
the *converse* — establishing `JoinLemma3F` for MRDTs whose weak-closure
VCs fail (EWFlag) via a single induction — and the rest of this file
locates exactly where that induction breaks. -/
theorem joinLemma3F_of_joinLemma3 (h : JoinLemma3 D) : JoinLemma3F D :=
  (joinLemma3C_full D).mp
    (JoinLemma3C.anti (fun _ _ h_full => weakClosure_of_fullClosure h_full)
      ((joinLemma3C_weak D).mpr h))

end JoinLemmaC

/-! ## §3. Peel-compatibility: the induction's step as a per-`𝒞` obligation

The `join_lemma3_of_cd_feasible` induction (`Adequacy.lean:960`) makes
progress by (i) selecting a `loOn(U)`-maximal event `e` of the union
(`exists_loOn_maximal_u`) and (ii) re-entering the IH at `U ∖ {e}` with the
sides `evᵢ ∖ {e}` — which requires the side-closure hypotheses to survive
the removal (`closure_diff_of_max`). `PeelCompatible` is exactly that
obligation, indexed by `𝒞`. (A generic `JoinLemma3C 𝒞` induction would
additionally need `𝒞` to be closed under union — sides closed ⇒ union
closed — which holds for both instances here; noted, not formalized.) -/

/-- **Peel-compatibility of a closure predicate.** Every finite
(`listPermOf`-enumerable) nonempty `𝒞`-closed `U` contains a
`loOn(U)`-maximal event whose removal preserves `𝒞` on every `𝒞`-closed
subset of `U` — in particular on `U` itself and on each side of a join. -/
def PeelCompatible (D : CRDTSig) (𝒞 : ClosurePred D) : Prop :=
  ∀ (C : Sal.Emulation.Configuration D) (U : Set (Op D.AppOp))
    (lU : List (Op D.AppOp)),
    (∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c) →
    (∀ a : Op D.AppOp, ¬ C.vis a a) →
    listPermOf lU U →
    (∀ a ∈ U, a ∈ C.events) →
    𝒞 C U → U.Nonempty →
    ∃ e ∈ U,
      (∀ x ∈ U, x ≠ e → ¬ loOn C U e x) ∧
      ∀ ev, ev ⊆ U → 𝒞 C ev → 𝒞 C (ev \ {e})

/-- **(a) Weak closure is peel-compatible** — for *every* signature
satisfying the update-layer VCs. This is the peel step of
`join_lemma3_of_cd_feasible`, factored: a `loOn(U)`-maximal event has no
non-commuting vis-successor inside `U` (such a successor would be a
vis-flavored `loOn`-edge), so its removal preserves `¬commutes`-closure of
every weakly closed subset (`closure_diff_of_max`). -/
theorem weakClosure_peelCompatible {D : CRDTSig} (hU : UpdateVCs D) :
    PeelCompatible D (weakClosure D) := by
  intro C U lU h_tr h_ir hpU h_inU _ h_ne
  obtain ⟨e, heU, h_max⟩ :=
    exists_loOn_maximal_u hU h_tr h_ir hpU h_inU h_ne
  exact ⟨e, heU, h_max,
    fun ev h_sub h_cl => closure_diff_of_max h_sub h_cl h_max⟩

/-! ## §4. Full closure is NOT peel-compatible — the kill-test, imported

The refutation instantiates `PeelCompatible` at the kill-test configuration:
a peel event for `U = peelU` at full closure would be simultaneously
`loOn(U)`-maximal (clause one) and vis-maximal (removal of `e` from the
fully closed `U` itself must keep `U ∖ {e}` fully closed, which forces `e`
to have no vis-successor in `U`) — contradicting `no_peelable_event`.

The witness signature `K2` also satisfies the update-layer VC bundle
(`K2_updateVCs`, with `cond_comm_lift` proved below via the componentwise
action of `k2Eff`), so on the very same signature weak closure is
peel-compatible and full closure is not: the boundary is the *closure
strength*, not the signature class. -/

/-- The kill-test `U`, phrased through the closure index. -/
theorem peelU_fullClosure : fullClosure K2 peelConfig peelU :=
  U_fully_closed

/-- An enumerating list for `peelU`. -/
def peelList : List (Op K2.AppOp) := [eAy, eRx, eAx, eRy]

theorem peelList_permOf : listPermOf peelList peelU := by
  refine ⟨by decide, fun a => ?_⟩
  simp only [peelList, peelU, List.mem_cons, List.not_mem_nil, or_false,
    Set.mem_insert_iff, Set.mem_singleton_iff]

/-- `loOn(peelU)` is irreflexive on `peelU`: no self vis-edge
(irreflexivity) and no self rc-edge (`rc o o = Either` for all four ops). -/
theorem peelU_loOn_irrefl : ∀ e ∈ peelU, ¬ loOn peelConfig peelU e e := by
  rintro e he (⟨hv, -⟩ | ⟨-, -, hrc, -⟩)
  · exact peelConfig_vis_irrefl e hv
  · have hcases : e = eAy ∨ e = eRx ∨ e = eAx ∨ e = eRy := he
    rcases hcases with rfl | rfl | rfl | rfl <;>
      exact absurd hrc (by decide)

/-! ### `K2` satisfies the update-layer VCs

`k2Eff` acts componentwise — each op writes one key's flag and passes the
other through — so (i) equal input components stay equal under any op
sequence, and (ii) a trailing write to the disputed key erases an upstream
same-key transposition. That is exactly `cond_comm_lift`. -/

/-- Componentwise congruence, first component. -/
theorem k2_applySeq_fst_congr :
    ∀ (π : List (Op K2.AppOp)) (σ τ : K2State), σ.1 = τ.1 →
      (applySeq K2 σ π).1 = (applySeq K2 τ π).1 := by
  intro π
  induction π with
  | nil =>
    intro σ τ h
    exact h
  | cons a π ih =>
    intro σ τ h
    have hstep : (K2.update σ a).1 = (K2.update τ a).1 := by
      rcases hop : a.2.2 <;> simp [K2_update, k2Update, k2Eff, hop, h]
    exact ih (K2.update σ a) (K2.update τ a) hstep

/-- Componentwise congruence, second component. -/
theorem k2_applySeq_snd_congr :
    ∀ (π : List (Op K2.AppOp)) (σ τ : K2State), σ.2 = τ.2 →
      (applySeq K2 σ π).2 = (applySeq K2 τ π).2 := by
  intro π
  induction π with
  | nil =>
    intro σ τ h
    exact h
  | cons a π ih =>
    intro σ τ h
    have hstep : (K2.update σ a).2 = (K2.update τ a).2 := by
      rcases hop : a.2.2 <;> simp [K2_update, k2Update, k2Eff, hop, h]
    exact ih (K2.update σ a) (K2.update τ a) hstep

/-- The overwrite core of `cond_comm_lift`, key `x`: with `e'' ` writing
key `x` last, the upstream `remX/addX` transposition is erased. -/
theorem k2_overwrite_x (s : K2State) (e e' e'' : Op K2.AppOp)
    (π : List (Op K2.AppOp))
    (h₁ : e.2.2 = K2Op.remX) (h₂ : e'.2.2 = K2Op.addX)
    (h₃ : e''.2.2 = K2Op.remX) :
    K2.update (applySeq K2 (K2.update (K2.update s e') e) π) e''
      = K2.update (applySeq K2 (K2.update (K2.update s e) e') π) e'' := by
  have h2eq : (K2.update (K2.update s e') e).2
      = (K2.update (K2.update s e) e').2 := by
    simp [K2_update, k2Update, k2Eff, h₁, h₂]
  have hs2 := k2_applySeq_snd_congr π _ _ h2eq
  have houter : ∀ x : K2State, K2.update x e'' = (false, x.2) := by
    intro x
    simp [K2_update, k2Update, k2Eff, h₃]
  simp only [houter]
  rw [hs2]

/-- The overwrite core of `cond_comm_lift`, key `y`. -/
theorem k2_overwrite_y (s : K2State) (e e' e'' : Op K2.AppOp)
    (π : List (Op K2.AppOp))
    (h₁ : e.2.2 = K2Op.remY) (h₂ : e'.2.2 = K2Op.addY)
    (h₃ : e''.2.2 = K2Op.remY) :
    K2.update (applySeq K2 (K2.update (K2.update s e') e) π) e''
      = K2.update (applySeq K2 (K2.update (K2.update s e) e') π) e'' := by
  have h1eq : (K2.update (K2.update s e') e).1
      = (K2.update (K2.update s e) e').1 := by
    simp [K2_update, k2Update, k2Eff, h₁, h₂]
  have hs1 := k2_applySeq_fst_congr π _ _ h1eq
  have houter : ∀ x : K2State, K2.update x e'' = (x.1, false) := by
    intro x
    simp [K2_update, k2Update, k2Eff, h₃]
  simp only [houter]
  rw [hs1]

/-- `cond_comm_lift` holds for `K2`: an rc-edge `e → e'` is a same-key
`rem → add`, and a non-commuting successor `e''` of `e'` writes that same
key, overwriting whichever order the pair was applied in. -/
theorem K2_cond_comm_lift :
    ∀ (s : K2State) (e e' e'' : Op K2.AppOp) (π : List (Op K2.AppOp)),
      distinctOps e e' → distinctOps e e'' → distinctOps e' e'' →
      K2.rc e e' = RcRes.Fst_then_snd →
      ¬ K2.commutes e' e'' →
      K2.update (applySeq K2 (K2.update (K2.update s e') e) π) e''
        = K2.update (applySeq K2 (K2.update (K2.update s e) e') π) e'' := by
  intro s e e' e'' π _ _ _ h_rc h_nc
  have h_rc' : k2RcOp e.2.2 e'.2.2 = RcRes.Fst_then_snd := h_rc
  rcases h₁ : e.2.2 <;> rcases h₂ : e'.2.2 <;>
    rw [h₁, h₂] at h_rc' <;>
    try exact absurd h_rc' (by decide)
  -- Surviving: (remX, addX) and (remY, addY).
  · -- `e ↦ remX`, `e' ↦ addX`: the non-commuting `e''` must be a same-key
    -- remove; the three cross/commuting op cases are dismissed by
    -- exhibiting the commutation `h_nc` denies.
    rcases h₃ : e''.2.2
    · exact absurd (show K2.commutes e' e'' by
        rw [K2_commutes_iff_eff, h₂, h₃]; decide) h_nc
    · exact k2_overwrite_x s e e' e'' π h₁ h₂ h₃
    · exact absurd (show K2.commutes e' e'' by
        rw [K2_commutes_iff_eff, h₂, h₃]; decide) h_nc
    · exact absurd (show K2.commutes e' e'' by
        rw [K2_commutes_iff_eff, h₂, h₃]; decide) h_nc
  · -- `e ↦ remY`, `e' ↦ addY` — mirror.
    rcases h₃ : e''.2.2
    · exact absurd (show K2.commutes e' e'' by
        rw [K2_commutes_iff_eff, h₂, h₃]; decide) h_nc
    · exact absurd (show K2.commutes e' e'' by
        rw [K2_commutes_iff_eff, h₂, h₃]; decide) h_nc
    · exact absurd (show K2.commutes e' e'' by
        rw [K2_commutes_iff_eff, h₂, h₃]; decide) h_nc
    · exact k2_overwrite_y s e e' e'' π h₁ h₂ h₃

/-- `K2` satisfies the full update-layer bundle: the obstruction below is
not an artifact of a signature outside the theory's class. -/
theorem K2_updateVCs : UpdateVCs K2 :=
  ⟨fun o₁ o₂ h_dist _ => K2_rc_non_comm_directional o₁ o₂ h_dist,
   K2_no_rc_chain, K2_cond_comm_lift⟩

/-- Weak closure is peel-compatible **on the kill-test signature itself**. -/
theorem K2_weakClosure_peelCompatible :
    PeelCompatible K2 (weakClosure K2) :=
  weakClosure_peelCompatible K2_updateVCs

/-- **(b) Full closure is NOT peel-compatible** — on the very signature
where weak closure is. A full-closure peel event of `peelU` would have to
be `loOn(U)`-maximal *and* (because `peelU ∖ {e}` must stay fully closed,
with `peelU` itself a fully closed `𝒞`-closed subset) vis-maximal in
`peelU`; `no_peelable_event` says no such event exists. -/
theorem K2_fullClosure_not_peelCompatible :
    ¬ PeelCompatible K2 (fullClosure K2) := by
  intro h
  obtain ⟨e, heU, h_max, h_pres⟩ :=
    h peelConfig peelU peelList peelConfig_vis_trans peelConfig_vis_irrefl
      peelList_permOf peelU_in_C peelU_fullClosure ⟨eAy, eAy_mem_U⟩
  have h_diff : fullClosure K2 peelConfig (peelU \ {e}) :=
    h_pres peelU (Set.Subset.refl _) peelU_fullClosure
  have h_vis_max : ∀ e' ∈ peelU, ¬ peelConfig.vis e e' := by
    intro e' he' hv
    have hne : e' ≠ e := by
      rintro rfl
      exact peelConfig_vis_irrefl e' hv
    exact (h_diff e e' hv ⟨he', hne⟩).2 rfl
  have h_lo_max : ∀ e' ∈ peelU, ¬ loOn peelConfig peelU e e' := by
    intro e' he' hlo
    by_cases hne : e' = e
    · rw [hne] at hlo
      exact peelU_loOn_irrefl e heU hlo
    · exact h_max e' he' hne hlo
  exact no_peelable_event ⟨e, heU, h_lo_max, h_vis_max⟩

/-- Packaged: full closure is not peel-compatible in general. -/
theorem fullClosure_not_peelCompatible :
    ∃ D : CRDTSig, ¬ PeelCompatible D (fullClosure D) :=
  ⟨K2, K2_fullClosure_not_peelCompatible⟩

/-! ## §5. Block peels — redesign (a) — are DEAD

A **back-block peel** removes a set `B ⊆ U` and places its events at the
end of the enumeration. Its two obligations, pinned generically:

* *removal preserves full closure* **iff** `B` is vis-upward-closed within
  `U` — no event of `U ∖ B` has a vis-predecessor in `B`
  (`diff_fullClosure_iff`);
* *jointly late-placeable*: a `loOn(U)`-respecting enumeration ending in
  the events of `B` can exist only if no `loOn(U)`-edge leaves `B` into
  `U ∖ B` (`block_suffix_no_exit`; the converse — such an enumeration
  exists whenever no edge leaves — is the existing re-permutation
  machinery, `perm_ending_in_loOn_max` generalized, not needed for the
  refutation).

On the kill-test `U` the two conditions chase each other around the cycle
`A_y →vis R_x →loOn A_x →vis R_y →loOn A_y`: upward-closure propagates
membership along vis-edges, exit-freeness along the surviving rc-edges, so
any nonempty `B` swallows all of `U` — no *proper* block exists and the
induction cannot make progress. Front blocks (prefix of the enumeration:
vis-*downward*-closed so the block is itself a closed set, and no
`loOn(U)`-edge *entering* `B`) chase the same cycle backwards and die the
same way. -/

/-- **Pin (i)**: removing `B` from a fully closed `U` leaves a fully closed
set iff `B` is vis-upward-closed within `U`. -/
theorem diff_fullClosure_iff {D : CRDTSig}
    {C : Sal.Emulation.Configuration D} {U B : Set (Op D.AppOp)}
    (h_closed : fullClosure D C U) :
    fullClosure D C (U \ B) ↔ ∀ a ∈ B, ∀ b ∈ U, C.vis a b → b ∈ B := by
  constructor
  · intro h a haB b hbU hvis
    by_contra hbB
    exact (h a b hvis ⟨hbU, hbB⟩).2 haB
  · rintro h a b hvis ⟨hbU, hbB⟩
    exact ⟨h_closed a b hvis hbU, fun haB => hbB (h a haB b hbU hvis)⟩

/-- **Pin (ii)**: if an enumeration respecting `R` ends with the events of
a block (`ρ₂`), no `R`-edge leaves the block into the prefix. Instantiated
at `R := loOn C U`, this is the necessity of exit-freeness for joint
late-placement. -/
theorem block_suffix_no_exit {α : Type} {R : α → α → Prop}
    {ρ₁ ρ₂ : List α} (h : respects (ρ₁ ++ ρ₂) R) :
    ∀ b ∈ ρ₂, ∀ a ∈ ρ₁, ¬ R b a := fun b hb a ha =>
  (List.pairwise_append.mp h).2.2 a ha b hb

/-- **Back-blocks force everything**: on the kill-test `U`, any nonempty
`B` that is vis-upward-closed within `U` and `loOn(U)`-exit-free is all of
`U`. Membership chases the cycle: vis-edges propagate it by
upward-closure, the surviving rc-edges by exit-freeness. -/
theorem back_block_forces_all {B : Set (Op K2.AppOp)}
    (h_sub : B ⊆ peelU)
    (h_up : ∀ a ∈ B, ∀ b ∈ peelU, peelConfig.vis a b → b ∈ B)
    (h_exit : ∀ e ∈ B, ∀ x ∈ peelU, x ∉ B → ¬ loOn peelConfig peelU e x)
    (h_ne : B.Nonempty) : B = peelU := by
  have stepAy : eAy ∈ B → eRx ∈ B :=
    fun h => h_up eAy h eRx eRx_mem_U vis_Ay_Rx
  have stepRx : eRx ∈ B → eAx ∈ B := by
    intro h
    by_contra hn
    exact h_exit eRx h eAx eAx_mem_U hn rc_edge_survives_x
  have stepAx : eAx ∈ B → eRy ∈ B :=
    fun h => h_up eAx h eRy eRy_mem_U vis_Ax_Ry
  have stepRy : eRy ∈ B → eAy ∈ B := by
    intro h
    by_contra hn
    exact h_exit eRy h eAy eAy_mem_U hn rc_edge_survives_y
  have h_all : eAy ∈ B ∧ eRx ∈ B ∧ eAx ∈ B ∧ eRy ∈ B := by
    obtain ⟨e, heB⟩ := h_ne
    have hcases : e = eAy ∨ e = eRx ∨ e = eAx ∨ e = eRy := h_sub heB
    rcases hcases with rfl | rfl | rfl | rfl
    · have h1 := stepAy heB
      have h2 := stepRx h1
      exact ⟨heB, h1, h2, stepAx h2⟩
    · have h1 := stepRx heB
      have h2 := stepAx h1
      exact ⟨stepRy h2, heB, h1, h2⟩
    · have h1 := stepAx heB
      have h2 := stepRy h1
      exact ⟨h2, stepAy h2, heB, h1⟩
    · have h1 := stepRy heB
      have h2 := stepAy h1
      exact ⟨h1, h2, stepRx h2, heB⟩
  refine Set.Subset.antisymm h_sub ?_
  intro x hx
  have hcases : x = eAy ∨ x = eRx ∨ x = eAx ∨ x = eRy := hx
  rcases hcases with rfl | rfl | rfl | rfl
  · exact h_all.1
  · exact h_all.2.1
  · exact h_all.2.2.1
  · exact h_all.2.2.2

/-- **Front-blocks force everything too** — fronts and backs are not
symmetric in general, but the cycle is direction-agnostic: vis-*downward*
closure and `loOn(U)`-*entry*-freeness chase the same cycle backwards. -/
theorem front_block_forces_all {B : Set (Op K2.AppOp)}
    (h_sub : B ⊆ peelU)
    (h_down : ∀ b ∈ B, ∀ a ∈ peelU, peelConfig.vis a b → a ∈ B)
    (h_entry : ∀ e ∈ B, ∀ x ∈ peelU, x ∉ B → ¬ loOn peelConfig peelU x e)
    (h_ne : B.Nonempty) : B = peelU := by
  have stepRx : eRx ∈ B → eAy ∈ B :=
    fun h => h_down eRx h eAy eAy_mem_U vis_Ay_Rx
  have stepAy : eAy ∈ B → eRy ∈ B := by
    intro h
    by_contra hn
    exact h_entry eAy h eRy eRy_mem_U hn rc_edge_survives_y
  have stepRy : eRy ∈ B → eAx ∈ B :=
    fun h => h_down eRy h eAx eAx_mem_U vis_Ax_Ry
  have stepAx : eAx ∈ B → eRx ∈ B := by
    intro h
    by_contra hn
    exact h_entry eAx h eRx eRx_mem_U hn rc_edge_survives_x
  have h_all : eAy ∈ B ∧ eRx ∈ B ∧ eAx ∈ B ∧ eRy ∈ B := by
    obtain ⟨e, heB⟩ := h_ne
    have hcases : e = eAy ∨ e = eRx ∨ e = eAx ∨ e = eRy := h_sub heB
    rcases hcases with rfl | rfl | rfl | rfl
    · have h1 := stepAy heB
      have h2 := stepRy h1
      exact ⟨heB, stepAx h2, h2, h1⟩
    · have h1 := stepRx heB
      have h2 := stepAy h1
      exact ⟨h1, heB, stepRy h2, h2⟩
    · have h1 := stepAx heB
      have h2 := stepRx h1
      exact ⟨h2, h1, heB, stepAy h2⟩
    · have h1 := stepRy heB
      have h2 := stepAx h1
      exact ⟨stepRx h2, h2, h1, heB⟩
  refine Set.Subset.antisymm h_sub ?_
  intro x hx
  have hcases : x = eAy ∨ x = eRx ∨ x = eAx ∨ x = eRy := hx
  rcases hcases with rfl | rfl | rfl | rfl
  · exact h_all.1
  · exact h_all.2.1
  · exact h_all.2.2.1
  · exact h_all.2.2.2

/-- No *proper* back-block peel exists on the kill-test `U`. -/
theorem no_proper_back_block :
    ¬ ∃ B : Set (Op K2.AppOp),
        B ⊆ peelU ∧ B.Nonempty ∧ B ≠ peelU ∧
        (∀ a ∈ B, ∀ b ∈ peelU, peelConfig.vis a b → b ∈ B) ∧
        (∀ e ∈ B, ∀ x ∈ peelU, x ∉ B → ¬ loOn peelConfig peelU e x) := by
  rintro ⟨B, h_sub, h_ne, h_proper, h_up, h_exit⟩
  exact h_proper (back_block_forces_all h_sub h_up h_exit h_ne)

/-- No *proper* front-block peel exists on the kill-test `U` either. -/
theorem no_proper_front_block :
    ¬ ∃ B : Set (Op K2.AppOp),
        B ⊆ peelU ∧ B.Nonempty ∧ B ≠ peelU ∧
        (∀ b ∈ B, ∀ a ∈ peelU, peelConfig.vis a b → a ∈ B) ∧
        (∀ e ∈ B, ∀ x ∈ peelU, x ∉ B → ¬ loOn peelConfig peelU x e) := by
  rintro ⟨B, h_sub, h_ne, h_proper, h_down, h_entry⟩
  exact h_proper (front_block_forces_all h_sub h_down h_entry h_ne)

/-- Consistency anchor: the kill-test's single-event obstruction
(`no_peelable_event`) is the `B = {e}` special case of the back-block
theorem — the block result strictly strengthens the kill-test. -/
theorem no_peelable_event_of_blocks :
    ¬ ∃ e ∈ peelU,
        (∀ e' ∈ peelU, ¬ loOn peelConfig peelU e e') ∧
        (∀ e' ∈ peelU, ¬ peelConfig.vis e e') := by
  rintro ⟨e, he, h_lo, h_vis⟩
  have h_eq : {e} = peelU := by
    refine back_block_forces_all (Set.singleton_subset_iff.mpr he)
      ?_ ?_ (Set.singleton_nonempty e)
    · intro a ha b hb hv
      rw [Set.mem_singleton_iff] at ha
      subst ha
      exact absurd hv (h_vis b hb)
    · intro e₀ he₀ x hx _ hlo
      rw [Set.mem_singleton_iff] at he₀
      subst he₀
      exact h_lo x hx hlo
  have h1 : eAy ∈ ({e} : Set (Op K2.AppOp)) := by
    rw [h_eq]; exact eAy_mem_U
  have h2 : eRx ∈ ({e} : Set (Op K2.AppOp)) := by
    rw [h_eq]; exact eRx_mem_U
  rw [Set.mem_singleton_iff] at h1 h2
  have h3 : eAy = eRx := h1.trans h2.symm
  simp [eAy, eRx] at h3

/-- **HEADLINE — the block-peel obstruction, packaged.** There is a CRDT
signature (satisfying the update-layer VCs — `K2_updateVCs`), a
configuration with transitive irreflexive `vis`, and a nonempty fully
closed `U ⊆ C.events` on which every closure-preserving late-placeable
back-block and every closure-shaped early-placeable front-block is the
whole of `U`. Redesign (a) of the plan doc — peel a block instead of an
event — is therefore dead at *every* granularity, for both enumeration
ends: the induction cannot make progress. Redesigns (b) (wider induction
class, §6) and (c) (disjunctive contract) are the only live routes. -/
theorem block_peel_obstruction :
    ∃ (D : CRDTSig) (C : Sal.Emulation.Configuration D)
      (U : Set (Op D.AppOp)),
      (∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c) ∧
      (∀ a : Op D.AppOp, ¬ C.vis a a) ∧
      (∀ a ∈ U, a ∈ C.events) ∧
      (∀ a b, C.vis a b → b ∈ U → a ∈ U) ∧
      U.Nonempty ∧
      (∀ B, B ⊆ U → B.Nonempty →
        (∀ a ∈ B, ∀ b ∈ U, C.vis a b → b ∈ B) →
        (∀ e ∈ B, ∀ x ∈ U, x ∉ B → ¬ loOn C U e x) →
        B = U) ∧
      (∀ B, B ⊆ U → B.Nonempty →
        (∀ b ∈ B, ∀ a ∈ U, C.vis a b → a ∈ B) →
        (∀ e ∈ B, ∀ x ∈ U, x ∉ B → ¬ loOn C U x e) →
        B = U) :=
  ⟨K2, peelConfig, peelU, peelConfig_vis_trans, peelConfig_vis_irrefl,
    peelU_in_C, U_fully_closed, ⟨eAy, eAy_mem_U⟩,
    fun _ h_sub h_ne h_up h_exit =>
      back_block_forces_all h_sub h_up h_exit h_ne,
    fun _ h_sub h_ne h_down h_entry =>
      front_block_forces_all h_sub h_down h_entry h_ne⟩

/-! ## §6. Redesign (b): the `AlmostClosed` induction class

If no set-shaped peel preserves full closure, the induction must stop
demanding it: widen the class to "fully closed minus what has already been
peeled". A peeled prefix of the induction is a union of `loOn(U)`-maximal
events, i.e. a `loOn(U)`-*upward-closed* subset. The class is
order-theoretically self-sustaining — peels exist and stay in the class —
which is exactly the part the full-closure route lacked. What this file
does NOT provide (the open state-side of redesign (b)): a Join statement
over `AlmostClosed` sides and the `CDVC3`/feasible-delta laws restated at
`AlmostClosed` sets. -/

section AlmostClosedSection
variable {D : CRDTSig}

/-- `S` is `loOn(U)`-upward-closed within `U`: no `loOn C U`-edge leaves
`S` into `U`. (The already-peeled events of a maximal-last induction form
such a set.) -/
def loOnUpClosed (C : Sal.Emulation.Configuration D)
    (U S : Set (Op D.AppOp)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ U, loOn C U a b → b ∈ S

/-- **The wider induction class**: `V` is a fully closed `U` minus a
`loOn(U)`-upward-closed peel set `S`. -/
def AlmostClosed (C : Sal.Emulation.Configuration D)
    (V : Set (Op D.AppOp)) : Prop :=
  ∃ U S : Set (Op D.AppOp),
    fullClosure D C U ∧ S ⊆ U ∧ loOnUpClosed C U S ∧ V = U \ S

/-- Every fully closed set is in the class (`S = ∅`): the widened
induction can *start* wherever the full-closure one would. -/
theorem almostClosed_of_fullClosure {C : Sal.Emulation.Configuration D}
    {U : Set (Op D.AppOp)} (h : fullClosure D C U) :
    AlmostClosed C U :=
  ⟨U, ∅, h, Set.empty_subset U,
    fun a ha => absurd ha (Set.notMem_empty a),
    (Set.diff_empty).symm⟩

/-- **The class is peel-stable**: removing any event that is
`loOn`-maximal *within the remainder* stays in the class — the new peel
set `S ∪ {e}` is still `loOn(U)`-upward-closed because `e`'s
`loOn(U)`-successors inside the remainder are excluded by maximality
(`loOn C U ⊆ loOn C V` on `V ⊆ U` by antitonicity) and those inside `S`
are already peeled. This is the step full closure could not take. -/
theorem AlmostClosed.peel {C : Sal.Emulation.Configuration D}
    {V : Set (Op D.AppOp)} (hV : AlmostClosed C V) {e : Op D.AppOp}
    (heV : e ∈ V) (h_max : ∀ x ∈ V, x ≠ e → ¬ loOn C V e x) :
    AlmostClosed C (V \ {e}) := by
  obtain ⟨U, S, h_cl, h_sub, h_up, rfl⟩ := hV
  refine ⟨U, insert e S, h_cl, ?_, ?_, ?_⟩
  · intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hxS
    · exact heV.1
    · exact h_sub hxS
  · intro a haS b hbU hlo
    rcases Set.mem_insert_iff.mp haS with heq | haS'
    · rw [heq] at hlo
      by_cases hbe : b = e
      · exact Set.mem_insert_iff.mpr (Or.inl hbe)
      · by_cases hbS : b ∈ S
        · exact Set.mem_insert_iff.mpr (Or.inr hbS)
        · exact absurd (loOn_mono (fun _ hx => hx.1) hlo)
            (h_max b ⟨hbU, hbS⟩ hbe)
    · exact Set.mem_insert_iff.mpr (Or.inr (h_up a haS' b hbU hlo))
  · rw [Set.diff_diff, Set.union_singleton]

/-- **Peels exist in the class**: every finite nonempty `AlmostClosed` set
admits a `loOn`-maximal event whose removal stays `AlmostClosed`. Together
with `AlmostClosed.peel` this is the order-theoretic half of redesign (b);
no analogue of `no_peelable_event` obstructs it. -/
theorem almostClosed_peel_exists (hU : UpdateVCs D)
    {C : Sal.Emulation.Configuration D}
    (h_tr : ∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c)
    (h_ir : ∀ a : Op D.AppOp, ¬ C.vis a a)
    {V : Set (Op D.AppOp)} {lV : List (Op D.AppOp)}
    (hpV : listPermOf lV V) (h_in : ∀ a ∈ V, a ∈ C.events)
    (hV : AlmostClosed C V) (h_ne : V.Nonempty) :
    ∃ e ∈ V, (∀ x ∈ V, x ≠ e → ¬ loOn C V e x) ∧
      AlmostClosed C (V \ {e}) := by
  obtain ⟨e, heV, h_max⟩ :=
    exists_loOn_maximal_u hU h_tr h_ir hpV h_in h_ne
  exact ⟨e, heV, h_max, hV.peel heV h_max⟩

end AlmostClosedSection

/-- The kill-test's first-peel remainder `U ∖ {A_x}` inhabits the class:
witness `S = {A_x}`, upward-closed by `Ax_loOn_maximal`. This is precisely
the set the full-closure IH could not receive. -/
theorem peelU_diff_Ax_almostClosed :
    AlmostClosed peelConfig (peelU \ {eAx}) := by
  refine ⟨peelU, {eAx}, peelU_fullClosure,
    Set.singleton_subset_iff.mpr eAx_mem_U, ?_, rfl⟩
  intro a haS b hbU hlo
  rw [Set.mem_singleton_iff] at haS
  subst haS
  exact absurd hlo (Ax_loOn_maximal b hbU)

/-- ... and it is NOT fully closed (the vis-edge `A_x → R_y` loses its
source): `AlmostClosed` strictly extends `fullClosure`, on exactly the
configuration that forced the widening. -/
theorem peelU_diff_Ax_not_fullyClosed :
    ¬ fullClosure K2 peelConfig (peelU \ {eAx}) := by
  intro h
  have hRy : eRy ∈ peelU \ {eAx} :=
    ⟨eRy_mem_U, fun hmem => by simp [eRy, eAx] at hmem⟩
  exact (h eAx eRy vis_Ax_Ry hRy).2 rfl

/-- On the kill-test `U` the widened induction *starts*: `U` is in the
class (it is fully closed) and admits a first peel that stays in the class
— in contrast to the full-closure induction, which `no_peelable_event`
stops at this very set. -/
theorem killTest_almostClosed_first_peel :
    ∃ e ∈ peelU, (∀ x ∈ peelU, x ≠ e → ¬ loOn peelConfig peelU e x) ∧
      AlmostClosed peelConfig (peelU \ {e}) :=
  almostClosed_peel_exists K2_updateVCs peelConfig_vis_trans
    peelConfig_vis_irrefl peelList_permOf peelU_in_C
    (almostClosed_of_fullClosure peelU_fullClosure) ⟨eAy, eAy_mem_U⟩

end Sal.Metatheory
