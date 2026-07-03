import Sal.MRDTs.Metatheory.MRDT_Instances
import Sal.MRDTs.Metatheory.Development.JoinLemma3C

/-!
# The full-closure Join Lemma via the wider `AlmostClosed` induction class

Task #6 of `Development/CONDITIONED_METATHEORY_PLAN.md` — redesign (b). The
Gate-G1 kill-test (`Reunification_Peel_Obstruction.lean`) showed the *naive*
reunification (re-run the `join_lemma3_of_cd_feasible` induction with
`JoinLemma3F`'s full-closure hypotheses) is dead: no single-event, and no
set-shaped block, peel preserves full causal closure. Redesign (b) widens the
induction class to `AlmostClosed` = "fully closed minus a `loOn(U)`-upward-closed
peel set" (`JoinLemma3C.lean`, §6). This file carries redesign (b) through the
*state side* and reports the verdict.

## What is settled here (0 sorries in everything kept)

1. **`JoinLemma3A := JoinLemma3C D AlmostClosed`** and the reunification bridge
   `joinLemma3F_of_joinLemma3A` (near-definitional, via `JoinLemma3C.anti` and
   `almostClosed_of_fullClosure`). Deliverable 1.

2. **`AlmostClosed` is a strengthening of weak closure**
   (`weakClosure_of_almostClosed`): every `AlmostClosed` set is
   `weakClosure`-closed, because a vis-non-commuting edge *is* a `loOn(U)`-edge
   (`loOn_of_vis_noncomm`), and the peel set is `loOn(U)`-upward-closed. Two
   consequences pin the VC verdict:
   * `joinLemma3A_of_joinLemma3` — `JoinLemma3A` follows *for free* from
     `JoinLemma3` with the **existing weak VCs**. So restricting the sides to
     `AlmostClosed` adds nothing on its own; the reunification cannot help
     EWFlag by this route unless the *VCs are weakened*.
   * `cdVC3A_of_cdVC3` / `feasibleDeltaVCs3A_of_feasibleDeltaVCs3` — the
     `AlmostClosed`-restated VCs `CDVC3A` / `FeasibleDeltaVCs3A` are **weaker**
     obligations (implied by the weak-closure VCs), so every existing discharge
     is preserved; and an MRDT (EWFlag is the candidate) could satisfy the
     restated set without the weak one. This is the *only* way the restatement
     buys anything.

3. **The two-sided peel step is realizable — over a *common* `U`.** The obstacle
   to running the induction is not the peel: for two sides that share one fully
   closed `U` (`CommonU`), a `loOn(ev₁∪ev₂)`-maximal event peels off both sides
   and the union while keeping everyone in the class (`CommonU.peel`,
   `CommonU.peel_exists`), and the union and intersection are `AlmostClosed` with
   the same `U` (`almostClosed_union_common`, `almostClosed_inter_common`). The
   mechanized crux: a `loOn(U)`-edge `e → b` with `b` in the (shrinking) union
   contradicts union-maximality via `loOn_mono` (union ⊆ U), and a `b ∈ U`
   outside the union already lies in the peel set — `loOnUpClosed_insert_of_max`.

## THE OBSTRUCTION (why the induction does NOT close generically)

The induction needs the sides `AlmostClosed`, and — to invoke `CDVC3A` at the
whole union and to recurse — needs the union/intersection/peels to stay in the
class. §3 shows that all holds **iff the two sides share a common fully closed
`U` with `loOn(U)`-upward-closed complements**. But that invariant is a *pincer*:

* **(P0 — initialization) `JoinLemma3F`'s hypothesis cannot supply `CommonU`.**
  The Join Lemma's sides are only *individually* fully closed; there is in
  general no common `U` decomposing both as `U ∖ (loOn(U)-upclosed)`. Refuted on
  the very kill-test (`killTest_no_common_U`): with `ev₁ = {A_y, R_x}`,
  `ev₂ = {A_x, R_y}` (both fully closed, union `= peelU` fully closed), the only
  candidate `U = peelU` forces `S₂ = {A_y, R_x}`, which is **not**
  `loOn(peelU)`-upward-closed — the surviving cross-side rc-edge
  `R_x →loOn A_x` (`rc_edge_survives_x`) leaves `S₂`. Concurrent rc-edges
  between the two versions' exclusive events are exactly what full closure does
  *not* control. So the induction cannot be *started* from `JoinLemma3F`.

* **(P0' — independent witnesses don't compose) `JoinLemma3A` (independent
  `AlmostClosed` witnesses per side) is initializable but its peel does not
  compose.** With per-side witnesses `(U₁,S₁) ≠ (U₂,S₂)`, `AlmostClosed.peel`
  needs `loOn(evᵢ)`-maximality of the peeled `e`, whereas the union peel only
  gives `loOn(ev₁∪ev₂)`-maximality; the two do not agree (an rc-edge
  `e → x ∈ evᵢ` can gain an absorber in `ev_j ∖ Uᵢ`, so it is `loOn(Uᵢ)` but not
  `loOn(union)`). Documented in `§4`; this is the independent-witness analogue of
  the common-`U` `loOnUpClosed_insert_of_max` step, which has no proof.

* **(P5 — the downset side) the CD `B`-argument's set is only weakly closed.**
  Even granting `CommonU`, `side_decompositionF` (`Adequacy.lean`) recurses with
  the principal downset `↓e = downset C e` as one side. `downset` is built from
  `visNC` (vis-**non-commuting**) transitive predecessors — it is `weakClosure`-
  closed (`downset_closed`) but **not** fully closed, hence not `AlmostClosed`
  with the ambient `U` (its complement `U ∖ ↓e` is not `loOn(U)`-upward-closed:
  an rc-edge into `↓e` need not have its source in `↓e`). So the inner recursion
  of the state-side decomposition leaves the class. The natural repair —
  redefine the CD `B`-argument over the **full-closure** downset `↓⁺e` (all
  vis-predecessors) — changes `CDVC3A`'s content and is left as a design note.

**Verdict.** Route (b)'s order theory is healthy *within* a common `U`
(mechanized here and in `JoinLemma3C.lean` §6), but the class is caught between
initialization (P0/P0') and the downset (P5). `joinLemma3A_of_cd_feasible` is
therefore **not** provided (it cannot be closed as a generic theorem, and the
task forbids sorried theorems / forced weaker ones); the exact stuck steps are
the two named preservation facts that have no proof —
`loOnUpClosed_insert` for independent witnesses (P0') and "downset is
`AlmostClosed`" (P5) — recorded as commented goal-states in §4. This sends
reunification back to design: either strengthen the Join hypothesis to carry
`CommonU` as data (and re-found the downset over `↓⁺e`), or take route (c) (the
disjunctive contract), which needs no new mathematics
(`JoinLemma3C` already unifies the two statements).

The unconditional tier is intact: the Counter (group class) satisfies the
restated VC set unconditionally (`Counter_cdVC3A`, `Counter_feasibleDeltaVCs3A`).
-/

namespace Sal.Metatheory

open Sal.Emulation
open Classical

/-! ## §1. `AlmostClosed` is a strengthening of weak closure -/

section StrengthLadder
variable {D : CRDTSig}

/-- **`AlmostClosed ⇒ weakClosure`.** A vis-non-commuting edge `a → b` is a
`loOn(U)`-edge (`loOn_of_vis_noncomm`); if `b` survived the peel (`b ∈ U ∖ S`)
and `a` were peeled (`a ∈ S`), upward-closure of `S` would drag `b` into `S`.
So the peel never severs a `¬commutes` vis-edge: the class is weakly closed. -/
theorem weakClosure_of_almostClosed {C : Sal.Emulation.Configuration D}
    {V : Set (Op D.AppOp)} (h : AlmostClosed C V) :
    weakClosure D C V := by
  obtain ⟨U, S, h_cl, _h_sub, h_up, rfl⟩ := h
  intro a b hv hnc hb
  refine ⟨h_cl a b hv hb.1, ?_⟩
  intro haS
  exact hb.2 (h_up a haS b hb.1 (loOn_of_vis_noncomm hv hnc))

end StrengthLadder

/-! ## §2. `JoinLemma3A`, the reunification bridge, and the VC restatements -/

section JoinLemmaA
variable {D : ConditionedMRDTSig}

/-- **The `AlmostClosed`-sided ternary Join Lemma** — `JoinLemma3C` at the
`AlmostClosed` index. Its restriction to fully closed sides is `JoinLemma3F`. -/
def JoinLemma3A (D : ConditionedMRDTSig) : Prop :=
  JoinLemma3C D (AlmostClosed (D := D.toCRDTSig))

/-- **Deliverable 1 — the reunification bridge.** `JoinLemma3A` restricted to
fully closed sides *is* `JoinLemma3F`: near-definitional, `JoinLemma3C.anti`
against `almostClosed_of_fullClosure`. -/
theorem joinLemma3F_of_joinLemma3A (h : JoinLemma3A D) : JoinLemma3F D :=
  (joinLemma3C_full D).mp
    (JoinLemma3C.anti (fun _ _ h_full => almostClosed_of_fullClosure h_full) h)

/-- **VC verdict, half one.** `JoinLemma3A` follows *for free* from the ordinary
weak-closure `JoinLemma3` (`JoinLemma3C.anti` against `weakClosure_of_almostClosed`).
So merely restricting the sides to `AlmostClosed` buys nothing over the existing
weak route — the reunification can help EWFlag only if the *VCs* are weakened. -/
theorem joinLemma3A_of_joinLemma3 (h : JoinLemma3 D) : JoinLemma3A D :=
  JoinLemma3C.anti (fun _ _ h_ac => weakClosure_of_almostClosed h_ac)
    ((joinLemma3C_weak D).mpr h)

/-- **`CDVC3A`** — `CDVC3` with the weak-closure hypothesis on `U` replaced by
`AlmostClosed C U`. A strictly weaker obligation. -/
def CDVC3A (D : ConditionedMRDTSig) : Prop :=
  ∀ (C : Sal.Emulation.Configuration D.toCRDTSig) (U : Set (Op D.AppOp))
    (A B : D.State) (e : Op D.AppOp),
    (∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c) →
    (∀ a : Op D.AppOp, ¬ C.vis a a) →
    (∀ a ∈ U, a ∈ C.events) →
    AlmostClosed C U →
    e ∈ U →
    (∀ x ∈ U, x ≠ e → ¬ loOn C U e x) →
    IsCanonicalState C (U \ {e}) A →
    IsCanonicalState C (downset C e \ {e}) B →
    D.mergeL B A (D.update B e) = D.update A e

/-- **`FeasibleDeltaVCs3A`** — `FeasibleDeltaVCs3` with the two side-closure
hypotheses replaced by `AlmostClosed`. (The unit law `feasible_init` carries no
closure hypothesis and is copied verbatim.) -/
structure FeasibleDeltaVCs3A (D : ConditionedMRDTSig) : Prop where
  feasible_init :
    ∀ (C : Sal.Emulation.Configuration D.toCRDTSig)
      (ev : Set (Op D.AppOp)) (s : D.State),
      (∀ a ∈ ev, a ∈ C.events) →
      IsCanonicalState C ev s →
      D.mergeL D.init D.init s = s
  feasible_local_redistribute :
    ∀ (C : Sal.Emulation.Configuration D.toCRDTSig)
      (ev₁ ev₂ : Set (Op D.AppOp)) (s₀ B t₁ s₂ : D.State) (e : Op D.AppOp),
      (∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c) →
      (∀ a : Op D.AppOp, ¬ C.vis a a) →
      (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
      AlmostClosed C ev₁ → AlmostClosed C ev₂ →
      e ∈ ev₁ → e ∉ ev₂ →
      (∀ x ∈ ev₁ ∪ ev₂, x ≠ e → ¬ loOn C (ev₁ ∪ ev₂) e x) →
      IsCanonicalState C (ev₁ ∩ ev₂) s₀ →
      IsCanonicalState C (downset C e \ {e}) B →
      IsCanonicalState C (ev₁ \ {e}) t₁ →
      IsCanonicalState C ev₂ s₂ →
      D.mergeL s₀ (D.mergeL B t₁ (D.update B e)) s₂
        = D.mergeL B (D.mergeL s₀ t₁ s₂) (D.update B e)
  feasible_redistribute :
    ∀ (C : Sal.Emulation.Configuration D.toCRDTSig)
      (ev₁ ev₂ : Set (Op D.AppOp)) (t₀ t₁ t₂ B : D.State) (e : Op D.AppOp),
      (∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c) →
      (∀ a : Op D.AppOp, ¬ C.vis a a) →
      (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
      AlmostClosed C ev₁ → AlmostClosed C ev₂ →
      e ∈ ev₁ → e ∈ ev₂ →
      (∀ x ∈ ev₁ ∪ ev₂, x ≠ e → ¬ loOn C (ev₁ ∪ ev₂) e x) →
      IsCanonicalState C ((ev₁ ∩ ev₂) \ {e}) t₀ →
      IsCanonicalState C (downset C e \ {e}) B →
      IsCanonicalState C (ev₁ \ {e}) t₁ →
      IsCanonicalState C (ev₂ \ {e}) t₂ →
      D.mergeL (D.mergeL B t₀ (D.update B e)) (D.mergeL B t₁ (D.update B e))
          (D.mergeL B t₂ (D.update B e))
        = D.mergeL B (D.mergeL t₀ t₁ t₂) (D.update B e)

/-- **VC verdict, half two — the restated VCs are weaker (discharges preserved).**
`CDVC3 ⇒ CDVC3A`: the `AlmostClosed U` hypothesis is downgraded to `weakClosure`
before applying `CDVC3`. -/
theorem cdVC3A_of_cdVC3 (h : CDVC3 D) : CDVC3A D := by
  intro C U A B e h_tr h_ir h_in hAC he h_max hA hB
  exact h C U A B e h_tr h_ir h_in (weakClosure_of_almostClosed hAC) he h_max hA hB

/-- `FeasibleDeltaVCs3 ⇒ FeasibleDeltaVCs3A`, field by field, downgrading each
`AlmostClosed` side hypothesis to `weakClosure`. -/
theorem feasibleDeltaVCs3A_of_feasibleDeltaVCs3 (h : FeasibleDeltaVCs3 D) :
    FeasibleDeltaVCs3A D where
  feasible_init := h.feasible_init
  feasible_local_redistribute := by
    intro C ev₁ ev₂ s₀ B t₁ s₂ e h_tr h_ir h_in₁ h_in₂ hA₁ hA₂ he₁ he₂ h_max
      hc₀ hB ht₁ hc₂
    exact h.feasible_local_redistribute C ev₁ ev₂ s₀ B t₁ s₂ e h_tr h_ir
      h_in₁ h_in₂ (weakClosure_of_almostClosed hA₁)
      (weakClosure_of_almostClosed hA₂) he₁ he₂ h_max hc₀ hB ht₁ hc₂
  feasible_redistribute := by
    intro C ev₁ ev₂ t₀ t₁ t₂ B e h_tr h_ir h_in₁ h_in₂ hA₁ hA₂ he₁ he₂ h_max
      ht₀ hB ht₁ ht₂
    exact h.feasible_redistribute C ev₁ ev₂ t₀ t₁ t₂ B e h_tr h_ir h_in₁ h_in₂
      (weakClosure_of_almostClosed hA₁) (weakClosure_of_almostClosed hA₂)
      he₁ he₂ h_max ht₀ hB ht₁ ht₂

end JoinLemmaA

/-! ## §3. The common-`U` join class: the peel step, fully mechanized

The induction consumes `AlmostClosed` of the sides, of their union (for
`CDVC3A`), of their intersection (for the LCA side of `side_decomposition`), and
of the peels (to recurse). All four hold — and the two-sided peel of a
`loOn(union)`-maximal event stays in the class — **provided both sides share one
fully closed `U`**. This section proves exactly that; §4 shows the shared-`U`
hypothesis is the residual obligation route (b) cannot discharge. -/

section CommonU
variable {D : CRDTSig}

/-- **The common-`U` two-sided class**: `ev₁, ev₂` are one fully closed `U` minus
`loOn(U)`-upward-closed peel sets `S₁, S₂`. -/
def CommonU (C : Sal.Emulation.Configuration D) (ev₁ ev₂ : Set (Op D.AppOp)) : Prop :=
  ∃ U S₁ S₂ : Set (Op D.AppOp),
    fullClosure D C U ∧ S₁ ⊆ U ∧ S₂ ⊆ U ∧
    loOnUpClosed C U S₁ ∧ loOnUpClosed C U S₂ ∧
    ev₁ = U \ S₁ ∧ ev₂ = U \ S₂

/-- Union of two common-`U` sides is `AlmostClosed` (witness peel set
`S₁ ∩ S₂`). -/
theorem almostClosed_union_common {C : Sal.Emulation.Configuration D}
    {U S₁ S₂ : Set (Op D.AppOp)}
    (h_cl : fullClosure D C U) (h_s1 : S₁ ⊆ U)
    (h_up1 : loOnUpClosed C U S₁) (h_up2 : loOnUpClosed C U S₂) :
    AlmostClosed C ((U \ S₁) ∪ (U \ S₂)) := by
  refine ⟨U, S₁ ∩ S₂, h_cl, Set.inter_subset_left.trans h_s1, ?_, ?_⟩
  · intro a ha b hbU hlo
    exact ⟨h_up1 a ha.1 b hbU hlo, h_up2 a ha.2 b hbU hlo⟩
  · ext x
    simp only [Set.mem_union, Set.mem_diff, Set.mem_inter_iff]
    tauto

/-- Intersection of two common-`U` sides is `AlmostClosed` (witness peel set
`S₁ ∪ S₂`). -/
theorem almostClosed_inter_common {C : Sal.Emulation.Configuration D}
    {U S₁ S₂ : Set (Op D.AppOp)}
    (h_cl : fullClosure D C U) (h_s1 : S₁ ⊆ U) (h_s2 : S₂ ⊆ U)
    (h_up1 : loOnUpClosed C U S₁) (h_up2 : loOnUpClosed C U S₂) :
    AlmostClosed C ((U \ S₁) ∩ (U \ S₂)) := by
  refine ⟨U, S₁ ∪ S₂, h_cl, Set.union_subset h_s1 h_s2, ?_, ?_⟩
  · intro a ha b hbU hlo
    rcases ha with ha | ha
    · exact Or.inl (h_up1 a ha b hbU hlo)
    · exact Or.inr (h_up2 a ha b hbU hlo)
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_union]
    tauto

/-- **The load-bearing peel lemma.** Adding a `loOn(W)`-maximal `e ∈ U` to a
`loOn(U)`-upward-closed `S` keeps it upward-closed, when `U ∖ S ⊆ W ⊆ U`. A
`loOn(U)`-edge `e → b`: if `b ∈ W` it contradicts maximality (via `loOn_mono`,
`W ⊆ U`); if `b ∈ U ∖ W` then `b ∉ U ∖ S`, so `b ∈ S`. This is the exact step
the two-sided peel needs, and the one the independent-witness class (§4) lacks. -/
theorem loOnUpClosed_insert_of_max {C : Sal.Emulation.Configuration D}
    {U S W : Set (Op D.AppOp)} {e : Op D.AppOp}
    (hupS : loOnUpClosed C U S)
    (hsubW : U \ S ⊆ W) (hWU : W ⊆ U) (_he_U : e ∈ U)
    (h_max : ∀ x ∈ W, x ≠ e → ¬ loOn C W e x) :
    loOnUpClosed C U (insert e S) := by
  intro a ha b hbU hlo
  rcases Set.mem_insert_iff.mp ha with heq | haS
  · rw [heq] at hlo
    by_cases hbe : b = e
    · exact Set.mem_insert_iff.mpr (Or.inl hbe)
    · by_cases hbW : b ∈ W
      · exact absurd (loOn_mono hWU hlo) (h_max b hbW hbe)
      · have hbS : b ∈ S := by
          by_contra hbS
          exact hbW (hsubW ⟨hbU, hbS⟩)
        exact Set.mem_insert_iff.mpr (Or.inr hbS)
  · exact Set.mem_insert_iff.mpr (Or.inr (hupS a haS b hbU hlo))

/-- Peeling a `loOn(union)`-maximal event preserves the whole `AlmostClosed`
value of one side. `evᵢ \ {e} = U \ insert e Sᵢ`, and `insert e Sᵢ` is
`loOn(U)`-upward-closed by `loOnUpClosed_insert_of_max` (`W := union`). -/
theorem almostClosed_side_peel_common {C : Sal.Emulation.Configuration D}
    {U S₁ S₂ : Set (Op D.AppOp)}
    (h_cl : fullClosure D C U) (h_s1 : S₁ ⊆ U)
    (h_up1 : loOnUpClosed C U S₁)
    {e : Op D.AppOp} (he : e ∈ (U \ S₁) ∪ (U \ S₂))
    (h_max : ∀ x ∈ (U \ S₁) ∪ (U \ S₂), x ≠ e →
      ¬ loOn C ((U \ S₁) ∪ (U \ S₂)) e x) :
    AlmostClosed C ((U \ S₁) \ {e}) := by
  have hWU : (U \ S₁) ∪ (U \ S₂) ⊆ U :=
    Set.union_subset Set.diff_subset Set.diff_subset
  refine ⟨U, insert e S₁, h_cl,
    Set.insert_subset_iff.mpr ⟨hWU he, h_s1⟩,
    loOnUpClosed_insert_of_max h_up1 Set.subset_union_left hWU (hWU he) h_max,
    ?_⟩
  rw [Set.diff_diff, Set.union_singleton]

/-- **`CommonU` is peel-stable.** A `loOn(ev₁∪ev₂)`-maximal `e` peels off both
sides at once and the pair stays in the common-`U` class (peel sets grow to
`insert e Sᵢ`; uniform in whether `e` lies in a side, since `e ∉ evᵢ ⇒ e ∈ Sᵢ ⇒
insert e Sᵢ = Sᵢ`). -/
theorem CommonU.peel {C : Sal.Emulation.Configuration D} {ev₁ ev₂ : Set (Op D.AppOp)}
    (h : CommonU C ev₁ ev₂) {e : Op D.AppOp} (he : e ∈ ev₁ ∪ ev₂)
    (h_max : ∀ x ∈ ev₁ ∪ ev₂, x ≠ e → ¬ loOn C (ev₁ ∪ ev₂) e x) :
    CommonU C (ev₁ \ {e}) (ev₂ \ {e}) := by
  obtain ⟨U, S₁, S₂, h_cl, h_s1, h_s2, h_up1, h_up2, rfl, rfl⟩ := h
  have hWU : (U \ S₁) ∪ (U \ S₂) ⊆ U :=
    Set.union_subset Set.diff_subset Set.diff_subset
  refine ⟨U, insert e S₁, insert e S₂, h_cl,
    Set.insert_subset_iff.mpr ⟨hWU he, h_s1⟩,
    Set.insert_subset_iff.mpr ⟨hWU he, h_s2⟩,
    loOnUpClosed_insert_of_max h_up1 Set.subset_union_left hWU (hWU he) h_max,
    loOnUpClosed_insert_of_max h_up2 Set.subset_union_right hWU (hWU he) h_max,
    ?_, ?_⟩
  · rw [Set.diff_diff, Set.union_singleton]
  · rw [Set.diff_diff, Set.union_singleton]

/-- The common-`U` sides, union and intersection are all `AlmostClosed`. -/
theorem CommonU.almostClosed_left {C : Sal.Emulation.Configuration D}
    {ev₁ ev₂ : Set (Op D.AppOp)} (h : CommonU C ev₁ ev₂) :
    AlmostClosed C ev₁ := by
  obtain ⟨U, S₁, _, h_cl, h_s1, _, h_up1, _, rfl, _⟩ := h
  exact ⟨U, S₁, h_cl, h_s1, h_up1, rfl⟩

theorem CommonU.almostClosed_union {C : Sal.Emulation.Configuration D}
    {ev₁ ev₂ : Set (Op D.AppOp)} (h : CommonU C ev₁ ev₂) :
    AlmostClosed C (ev₁ ∪ ev₂) := by
  obtain ⟨U, S₁, S₂, h_cl, h_s1, _, h_up1, h_up2, rfl, rfl⟩ := h
  exact almostClosed_union_common h_cl h_s1 h_up1 h_up2

theorem CommonU.almostClosed_inter {C : Sal.Emulation.Configuration D}
    {ev₁ ev₂ : Set (Op D.AppOp)} (h : CommonU C ev₁ ev₂) :
    AlmostClosed C (ev₁ ∩ ev₂) := by
  obtain ⟨U, S₁, S₂, h_cl, h_s1, h_s2, h_up1, h_up2, rfl, rfl⟩ := h
  exact almostClosed_inter_common h_cl h_s1 h_s2 h_up1 h_up2

/-- **The two-sided peel exists and preserves the class** — the common-`U`
analogue of `almostClosed_peel_exists`, and the full peel step the induction
would take at each level. No analogue of the Gate-G1 obstruction blocks it. -/
theorem CommonU.peel_exists (hU : UpdateVCs D)
    {C : Sal.Emulation.Configuration D}
    (h_tr : ∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c)
    (h_ir : ∀ a : Op D.AppOp, ¬ C.vis a a)
    {ev₁ ev₂ : Set (Op D.AppOp)} {lU : List (Op D.AppOp)}
    (hpU : listPermOf lU (ev₁ ∪ ev₂))
    (h_in : ∀ a ∈ ev₁ ∪ ev₂, a ∈ C.events)
    (h : CommonU C ev₁ ev₂) (h_ne : (ev₁ ∪ ev₂).Nonempty) :
    ∃ e ∈ ev₁ ∪ ev₂,
      (∀ x ∈ ev₁ ∪ ev₂, x ≠ e → ¬ loOn C (ev₁ ∪ ev₂) e x) ∧
      CommonU C (ev₁ \ {e}) (ev₂ \ {e}) := by
  obtain ⟨e, heU, h_max⟩ := exists_loOn_maximal_u hU h_tr h_ir hpU h_in h_ne
  exact ⟨e, heU, h_max, h.peel heU h_max⟩

end CommonU

/-! ## §4. The initialization obstruction (P0), on the kill-test

`CommonU` is exactly what the two-sided peel preserves (§3), and it is the
weakest hypothesis under which the union/intersection stay in the class. But
`JoinLemma3F` only hands us sides that are *individually* fully closed, and those
do **not** in general admit a common `U`. The kill-test refutes it outright. -/

/-- The kill-test's two replica versions, both fully causally closed. -/
def killEv₁ : Set (Op K2.AppOp) := {eAy, eRx}
def killEv₂ : Set (Op K2.AppOp) := {eAx, eRy}

theorem killEv₁_union_killEv₂ : killEv₁ ∪ killEv₂ = peelU := by
  ext x; simp only [killEv₁, killEv₂, peelU, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff]; tauto

/-- **(P0) — fully closed sides do NOT admit a common `U`.** For any fully
closed `U ⊆ peelU` decomposing `killEv₁ = U ∖ S₁` and `killEv₂ = U ∖ S₂` with
`loOn(U)`-upward-closed peels, the surviving rc-edge `R_x →loOn A_x`
(`rc_edge_survives_x`) forces `A_x ∈ S₂`, contradicting `A_x ∈ killEv₂ = U ∖ S₂`.
So `CommonU`, the invariant the induction needs, cannot be initialized from the
`JoinLemma3F` hypothesis — route (b)'s pincer. -/
theorem killTest_no_common_U :
    ¬ ∃ (U S₁ S₂ : Set (Op K2.AppOp)),
        fullClosure K2 peelConfig U ∧ U ⊆ peelU ∧
        killEv₁ = U \ S₁ ∧ killEv₂ = U \ S₂ ∧
        loOnUpClosed peelConfig U S₁ ∧ loOnUpClosed peelConfig U S₂ := by
  rintro ⟨U, S₁, S₂, _h_cl, hUsub, h1, h2, _hup1, hup2⟩
  have hRxK1 : eRx ∈ killEv₁ := by
    simp [killEv₁, Set.mem_insert_iff, Set.mem_singleton_iff]
  have hAxK2 : eAx ∈ killEv₂ := by
    simp [killEv₂, Set.mem_insert_iff, Set.mem_singleton_iff]
  have hRxnK2 : eRx ∉ killEv₂ := by
    simp [killEv₂, Set.mem_insert_iff, Set.mem_singleton_iff, eRx, eAx, eRy]
  -- eRx ∈ killEv₁ = U \ S₁ ⇒ eRx ∈ U
  have hRx_in : eRx ∈ U \ S₁ := h1 ▸ hRxK1
  have hRxU : eRx ∈ U := hRx_in.1
  -- eAx ∈ killEv₂ = U \ S₂ ⇒ eAx ∈ U ∧ eAx ∉ S₂
  have hAx_in : eAx ∈ U \ S₂ := h2 ▸ hAxK2
  have hAxU : eAx ∈ U := hAx_in.1
  have hAxnS₂ : eAx ∉ S₂ := hAx_in.2
  -- eRx ∈ S₂: eRx ∈ U and eRx ∉ killEv₂ = U \ S₂
  have hRxnEv₂ : eRx ∉ U \ S₂ := h2 ▸ hRxnK2
  have hRxS₂ : eRx ∈ S₂ := by
    by_contra hns
    exact hRxnEv₂ ⟨hRxU, hns⟩
  -- the surviving cross-side rc-edge, transported to U by antitonicity
  have hedge : loOn peelConfig U eRx eAx :=
    loOn_mono hUsub rc_edge_survives_x
  exact hAxnS₂ (hup2 eRx hRxS₂ eAx hAxU hedge)

/-! ### The two documented stuck steps (P0', P5) — goal-states, not sorries

**(P0') Independent-witness peel.** For `JoinLemma3A` with *per-side* witnesses,
the peel step would need, at a side `evᵢ = Uᵢ ∖ Sᵢ` and a `loOn(ev₁∪ev₂)`-maximal
`e ∈ evᵢ`:

    loOnUpClosed C Uᵢ (insert e Sᵢ)

i.e. every `loOn(Uᵢ)`-successor `b ∈ Uᵢ` of `e` lies in `insert e Sᵢ`. The
common-`U` proof (`loOnUpClosed_insert_of_max`) discharges this from
`loOn(union)`-maximality **because there `Uᵢ = U ⊇ union`**, so `loOn_mono` turns
a `loOn(U)`-edge into a `loOn(union)`-edge. With `Uᵢ ≠ U` the two `loOn`
relations are incomparable: an rc-edge `e → b` (`b ∈ evᵢ`) can acquire an
absorber in `ev_j ∖ Uᵢ`, making it `loOn(Uᵢ)` but not `loOn(union)`, so
union-maximality does not exclude it. No proof — and no repair short of forcing a
common `U`, which P0 shows is unavailable.

**(P5) The downset side.** `side_decompositionF` recurses (`Adequacy.lean:938`)
with `downset C e` as one side. For the `AlmostClosed` induction that recursion
needs

    AlmostClosed C (downset C e)          -- equivalently: U ∖ ↓e is loOn(U)-upclosed

but `downset C e = {x | x = e ∨ TransGen (visNC C) x e}` is closed only under
`visNC` (vis-**non-commuting**) predecessors (`downset_closed`), not under all
vis-predecessors, so it is `weakClosure`-closed but not fully closed, and
`U ∖ ↓e` is not `loOn(U)`-upward-closed (an rc-edge into `↓e` need not originate
in `↓e`). No proof. The natural repair redefines the CD `B`-argument over the
**full** downset `↓⁺e = {x | x = e ∨ TransGen C.vis x e}`, which *is* fully
closed — but that changes `CDVC3A`'s statement (a different `B`), a design step
outside this file.

Because P0' (or, with a common `U`, P0) and P5 both lack proofs and the task
forbids sorried theorems, `joinLemma3A_of_cd_feasible : CoreVCs3CD →
FeasibleDeltaVCs3A → CDVC3A → JoinLemma3A` is **not** stated. Everything the
induction would consume *except* these two facts is mechanized above. -/

/-! ## §5. Sanity anchor — the counter satisfies the restated VCs unconditionally

Route (b) must not lose the unconditional tier. The Counter (group class,
`mergeL l a b = a + b − l`, all ops commute) satisfies `CDVC3A` and
`FeasibleDeltaVCs3A` with no side conditions, via the collapse lemmas from its
existing `CDVC3` / `FeasibleDeltaVCs3`. -/

/-- The Counter's slim core (needed alongside the VCs by any `join_*_of_cd`). -/
theorem Counter_coreVCs3CD_anchor : CoreVCs3CD Counter := Counter_coreVCs3.toCD

/-- **Counter ⊨ `CDVC3A`, unconditionally.** -/
theorem Counter_cdVC3A : CDVC3A Counter :=
  cdVC3A_of_cdVC3 (cdVC3_of_all_comm Counter_coreVCs3 Counter_all_comm)

/-- **Counter ⊨ `FeasibleDeltaVCs3A`, unconditionally.** -/
theorem Counter_feasibleDeltaVCs3A : FeasibleDeltaVCs3A Counter :=
  feasibleDeltaVCs3A_of_feasibleDeltaVCs3
    (feasibleDeltaVCs3_of_delta Counter_coreVCs3 Counter_deltaVCs3)

end Sal.Metatheory
