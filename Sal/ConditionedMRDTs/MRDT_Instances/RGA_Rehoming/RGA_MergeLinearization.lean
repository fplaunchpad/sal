import Sal.MRDTs.RGA_Rehoming.RGA_Reachability_Invariant

/-!
# The merge-linearization bridge for the tombstone-free RGA

Goal (up to observational `eq`):

    eq (merge l a b) (applySeqR l π)

for a reachable LCA `l`, branches `a`/`b` folded from disjoint concurrent event
lists over `l`, and a `loOnA`-respecting interleave `π` of `Ea ++ Eb`.

## Approach

The merge is defined by a **survivor set** `I` plus a **per-survivor climb**, so it
is inherently per-id.  We match that shape: reduce `eq (merge …) f` to the
extensional obligation *(same domain) ∧ (per live id: same element ∧ same anchor)*
and discharge the anchor obligation by the **anchor-coincidence** invariant

  * for a surviving *original* node `k` (`k ∈ dom l ∩ dom branch`),
    `climb (anc l) (dom branch) (anc l k) = anc branch k`
    — merge's LCA-climb lands where the fold's `resolve`-rehoming lands.

This file mechanizes the **single-sided** core (`b = l`):

  * §1 framework: `applySeqR`, `eq` reflexivity/transitivity.
  * §2 the `climb` algebra (fuel-stability, live-unfold, removal lemmas) — the
    technical crux that makes the climb value-recursive rather than fuel-indexed.
  * §3 `BranchInv l a` (the three l-relative invariants I2/I3/I4) + its base.
  * §4 reduction `BranchInv l a ∧ wf a → eq (merge l a l) a`.
  * §5 preservation of `BranchInv` under a good `do_` step (Ins / Del).
  * §6 the fold corollary + single-sided headline.

Everything is over the RGA's observational `eq` (NOT Lean `Eq`); the generic
`Merge_Linearization_Set` induction (Lean-`Eq`, 2 pre-existing sorries) is NOT
inherited — the needed steps are rebuilt natively.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace RGAMergeLinearization

variable {α : Type} [DecidableEq α] [Inhabited α]

/-! ## §1  Framework: the concrete fold and `eq` plumbing -/

/-- Concrete RGA fold: apply a list of ops left-to-right with `do_`. -/
def applySeqR (s : concrete_st α) (π : List (op_t α)) : concrete_st α := π.foldl do_ s

@[simp] theorem applySeqR_nil (s : concrete_st α) : applySeqR s [] = s := rfl
@[simp] theorem applySeqR_cons (s : concrete_st α) (o : op_t α) (π : List (op_t α)) :
    applySeqR s (o :: π) = applySeqR (do_ s o) π := rfl

theorem eq_refl (s : concrete_st α) : eq s s := fun _ => ⟨rfl, fun _ => rfl⟩

theorem eq_trans (a b c : concrete_st α) (hab : eq a b) (hbc : eq b c) : eq a c := by
  intro k
  refine ⟨(hab k).1.trans (hbc k).1, ?_⟩
  intro hka
  exact ((hab k).2 hka).trans ((hbc k).2 ((hab k).1 ▸ hka))

/-! ## §2  The `climb` algebra

`climb ancL I x = climb_aux ancL I x x` walks `ancL` from `x` to the first node
in `{0} ∪ I`, with fuel `= x`.  Under id-monotone anchors on the LCA the fuel is
always sufficient, so the climb behaves like a value-recursive "nearest node in
`{0} ∪ I` up the `anc l` chain".  These lemmas package exactly that. -/

/-- **Fuel stability.**  Under id-monotone (`Hdec`) forest (`Hstay`) anchors, any
fuel `≥ z` gives the canonical climb `climb_aux … z z` from a live/root node `z`. -/
theorem climb_aux_stable (l : concrete_st α)
    (Hdec : ∀ y, contains l y = true → y ≠ 0 → anc l y < y)
    (Hstay : ∀ y, contains l y = true → (anc l y = 0 ∨ contains l (anc l y) = true))
    (I : set ℕ) :
    ∀ z, (z = 0 ∨ contains l z = true) → ∀ f, z ≤ f →
      climb_aux (fun y => anc l y) I f z = climb_aux (fun y => anc l y) I z z := by
  intro z
  induction z using Nat.strong_induction_on with
  | _ z ih =>
    intro hz f hf
    match z, hz, ih with
    | 0, _, _ => cases f <;> simp [climb_aux]
    | (zc+1), hz, ih =>
      have hlz : contains l (zc+1) = true := by
        rcases hz with h | h
        · exact absurd h (by omega)
        · exact h
      by_cases hIz : I (zc+1) = true
      · cases f with
        | zero => omega
        | succ g => simp [climb_aux, hIz]
      · have hIzf : I (zc+1) = false := by
          cases hI : I (zc+1) with
          | true => exact absurd hI hIz
          | false => rfl
        have hanc_lt : anc l (zc+1) < zc+1 := Hdec (zc+1) hlz (by omega)
        have hstart : anc l (zc+1) = 0 ∨ contains l (anc l (zc+1)) = true := Hstay (zc+1) hlz
        cases f with
        | zero => omega
        | succ g =>
          simp only [climb_aux]
          rw [if_neg (by simp [hIzf]), if_neg (by simp [hIzf])]
          have hg : anc l (zc+1) ≤ g := by omega
          have hzc : anc l (zc+1) ≤ zc := by omega
          rw [ih (anc l (zc+1)) hanc_lt hstart g hg,
              ih (anc l (zc+1)) hanc_lt hstart zc hzc]

/-- **Live unfold.**  A live non-root node not in `I` climbs to the climb of its
`anc l` parent — the value-recursive step (fuel matched by `climb_aux_stable`). -/
theorem climb_live_unfold (l : concrete_st α)
    (Hdec : ∀ y, contains l y = true → y ≠ 0 → anc l y < y)
    (Hstay : ∀ y, contains l y = true → (anc l y = 0 ∨ contains l (anc l y) = true))
    (I : set ℕ) (y : ℕ)
    (hly : contains l y = true) (hy0 : y ≠ 0) (hIy : I y = false) :
    climb (fun z => anc l z) I y = climb (fun z => anc l z) I (anc l y) := by
  obtain ⟨yc, rfl⟩ : ∃ yc, y = yc + 1 := ⟨y - 1, by omega⟩
  have hanc_lt : anc l (yc+1) < yc+1 := Hdec (yc+1) hly (by omega)
  have hstart : anc l (yc+1) = 0 ∨ contains l (anc l (yc+1)) = true := Hstay (yc+1) hly
  simp only [climb]
  simp only [climb_aux]
  rw [if_neg (by simp [hIy])]
  -- goal: climb_aux _ I yc (anc l (yc+1)) = climb_aux _ I (anc l (yc+1)) (anc l (yc+1))
  exact climb_aux_stable l Hdec Hstay I (anc l (yc+1)) hstart yc (by omega)

/-- **Removal below a non-result.**  If the climb of `y` is not `x`, then removing
`x` from the stop-set does not change the climb of `y` (the first `{0}∪I`-hit is
some node other than `x`, and dropping `x` cannot promote an earlier node to a
hit). -/
theorem climb_aux_remove_ne (ancf : ℕ → ℕ) (I : set ℕ) (x : ℕ) :
    ∀ (fuel y : ℕ), climb_aux ancf I fuel y ≠ x →
      climb_aux ancf (fun z => I z && x != z) fuel y = climb_aux ancf I fuel y := by
  intro fuel
  induction fuel with
  | zero => intro y _; rfl
  | succ f ih =>
    intro y hne
    by_cases hy0 : y = 0
    · subst hy0; simp [climb_aux]
    · by_cases hIy : I y = true
      · by_cases hyx : y = x
        · exfalso; apply hne
          subst hyx; simp [climb_aux, hIy]
        · have hbne : (x != y) = true := by simp [Ne.symm hyx]
          simp [climb_aux, hy0, hIy, hbne]
      · have hIyf : I y = false := by
          cases hI : I y with
          | true => exact absurd hI hIy
          | false => rfl
        simp only [climb_aux]
        rw [if_neg (by simp [hy0, hIyf]), if_neg (by simp [hy0, hIyf])]
        apply ih (ancf y)
        have hstep : climb_aux ancf I (f+1) y = climb_aux ancf I f (ancf y) := by
          simp only [climb_aux]; rw [if_neg (by simp [hy0, hIyf])]
        rw [hstep] at hne; exact hne

theorem climb_remove_ne (ancf : ℕ → ℕ) (I : set ℕ) (x y : ℕ)
    (h : climb ancf I y ≠ x) :
    climb ancf (fun z => I z && x != z) y = climb ancf I y :=
  climb_aux_remove_ne ancf I x y y h

/-- **Congruence in the stop-set off the LCA-forest.**  If `I` and `I'` agree on
every live-in-`l` node, the climb (which only ever tests live-in-`l` nodes, or
`0`) is unchanged.  This handles an `Ins`, which grows the stop-set by a fresh id
not in `dom l`. -/
theorem climb_aux_I_congr (l : concrete_st α)
    (Hstay : ∀ y, contains l y = true → (anc l y = 0 ∨ contains l (anc l y) = true))
    (I I' : set ℕ) (hII : ∀ y, contains l y = true → I y = I' y) :
    ∀ (fuel y : ℕ), (y = 0 ∨ contains l y = true) →
      climb_aux (fun z => anc l z) I fuel y = climb_aux (fun z => anc l z) I' fuel y := by
  intro fuel
  induction fuel with
  | zero => intro y _; rfl
  | succ f ih =>
    intro y hy
    by_cases hy0 : y = 0
    · subst hy0; simp [climb_aux]
    · have hly : contains l y = true := by
        rcases hy with h | h
        · exact absurd h hy0
        · exact h
      have hI : I y = I' y := hII y hly
      simp only [climb_aux, hI]
      by_cases hIy : I' y = true
      · rw [if_pos (by simp [hy0, hIy]), if_pos (by simp [hy0, hIy])]
      · have hIyf : I' y = false := by
          cases hI' : I' y with
          | true => exact absurd hI' hIy
          | false => rfl
        rw [if_neg (by simp [hy0, hIyf]), if_neg (by simp [hy0, hIyf])]
        exact ih (anc l y) (Hstay y hly)

/-- **Climb through the removed node.**  If the climb of `y` (under `I`) is `x`
(a live-in-`l`, non-root node), then removing `x` from the stop-set makes the
climb of `y` continue exactly to the climb of `x`'s `anc l` parent. -/
theorem climb_remove_eq_result (l : concrete_st α)
    (Hdec : ∀ y, contains l y = true → y ≠ 0 → anc l y < y)
    (Hstay : ∀ y, contains l y = true → (anc l y = 0 ∨ contains l (anc l y) = true))
    (I : set ℕ) (x : ℕ) (hxl : contains l x = true) (hx0 : x ≠ 0) :
    ∀ y, (y = 0 ∨ contains l y = true) → climb (fun z => anc l z) I y = x →
      climb (fun z => anc l z) (fun z => I z && x != z) y
        = climb (fun z => anc l z) (fun z => I z && x != z) (anc l x) := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro hy hres
    by_cases hy0 : y = 0
    · subst hy0
      -- climb _ I 0 = 0 ≠ x (x ≠ 0): contradiction
      exfalso; apply hx0
      have h0 : climb (fun z => anc l z) I 0 = 0 := climb_fixpoint _ I 0 (Or.inl rfl)
      rw [h0] at hres; exact hres.symm
    · have hly : contains l y = true := by
        rcases hy with h | h
        · exact absurd h hy0
        · exact h
      by_cases hyx : y = x
      · -- y = x: removing x makes the climb of x recurse to anc l x (fixpoint broken)
        rw [hyx]
        exact climb_live_unfold l Hdec Hstay (fun z => I z && x != z) x hxl hx0 (by simp)
      · -- y ≠ x: I y must be false (else climb = y = x), unfold both and recurse
        have hIyf : I y = false := by
          by_contra hne
          have hIy : I y = true := by
            cases hI : I y with | true => rfl | false => exact absurd hI hne
          have hcl : climb (fun z => anc l z) I y = y :=
            climb_fixpoint _ I y (Or.inr hIy)
          rw [hcl] at hres; exact hyx hres
        have hres' : climb (fun z => anc l z) I (anc l y) = x := by
          rw [← climb_live_unfold l Hdec Hstay I y hly hy0 hIyf]; exact hres
        rw [climb_live_unfold l Hdec Hstay (fun z => I z && x != z) y hly hy0
              (by simp [hIyf])]
        have hanc_lt : anc l y < y := Hdec y hly hy0
        have hstart : anc l y = 0 ∨ contains l (anc l y) = true := Hstay y hly
        exact ih (anc l y) hanc_lt hstart hres'

/-! ## §3  `BranchInv`: the l-relative invariants, and merge helpers -/

/-- Element of a merge (definitional projection of the `merge` map). -/
theorem el_merge (l a b : concrete_st α) (t : ℕ) :
    el (merge l a b) t
      = (if contains l t then el l t else if contains a t then el a t else el b t) := rfl

/-- The single-sided (`b = l`) survivor set is exactly `a`'s domain. -/
theorem survivors_single (l a : concrete_st α) : survivors l a l = domain a := by
  funext t
  simp only [survivors, union, intersection, difference]
  cases (domain l t) <;> cases (domain a t) <;> rfl

/-- `contains a k` and `domain a k` are the same Bool. -/
theorem contains_eq_domain (a : concrete_st α) (k : ℕ) : contains a k = domain a k := rfl

/-- The three **l-relative** branch invariants.  `RgaInv`/`id_mono` (state
invariants) and `wf` are threaded separately (they are already known reachable
invariants); `BranchInv` carries only what relates a branch `a` to its LCA `l`:

* **I2** — surviving *original* nodes keep their element;
* **I4** — the anchor-coincidence: merge's LCA-climb from an original node's
  `l`-parent lands on the node's *current* branch anchor (this is the mathematical
  crux — merge's climb reproduces the fold's `resolve`-rehoming);
* **I3** — an original node's branch anchor is again `0`-or-original (rehoming
  never sends an `l`-node onto a branch-new node). -/
def BranchInv (l a : concrete_st α) : Prop :=
  (∀ k, contains l k = true → contains a k = true → el a k = el l k)
  ∧ (∀ k, contains l k = true → contains a k = true →
        climb (fun y => anc l y) (domain a) (anc l k) = anc a k)
  ∧ (∀ k, contains l k = true → contains a k = true →
        anc a k = 0 ∨ contains l (anc a k) = true)

/-! ## §4  Reduction: `BranchInv l a ∧ wf a → eq (merge l a l) a`

The per-id extensional route: `merge l a l` and `a` have the same domain
(`survivors_single`), and on each live id their element (I2) and anchor coincide —
the original-node anchor by I4, the branch-new-node anchor by `climb_fixpoint`
(its birth-anchor is already `0`-or-survivor by `wf a`). -/
theorem eq_merge_single (l a : concrete_st α) (hwfa : wf a) (hbi : BranchInv l a) :
    eq (merge l a l) a := by
  obtain ⟨hI2, hI4, hI3⟩ := hbi
  intro k
  refine ⟨?_, ?_⟩
  · rw [contains_merge, survivors_single l a]; exact (contains_eq_domain a k).symm
  · intro hk
    have hka : contains a k = true := by
      rw [contains_merge, survivors_single l a] at hk; exact hk
    have hel : el (merge l a l) k = el a k := by
      rw [el_merge]
      by_cases hlk : contains l k = true
      · rw [if_pos hlk]; exact (hI2 k hlk hka).symm
      · rw [if_neg hlk, if_pos hka]
    have hanc : anc (merge l a l) k = anc a k := by
      rw [anc_merge, survivors_single l a]
      by_cases hlk : contains l k = true
      · have hbeta : birthAnc l a l k = anc l k := by simp only [birthAnc, hlk, if_true]
        rw [hbeta]; exact hI4 k hlk hka
      · have hbeta : birthAnc l a l k = anc a k := by
          simp only [birthAnc]; rw [if_neg hlk, if_pos hka]
        rw [hbeta]
        apply climb_fixpoint
        rcases hwfa k hka with h | h
        · exact Or.inl h
        · exact Or.inr (by rw [← contains_eq_domain]; exact h)
    have hsel : sel (merge l a l) k = sel a k := by
      have e1 : sel (merge l a l) k = (el (merge l a l) k, anc (merge l a l) k) := rfl
      have e2 : sel a k = (el a k, anc a k) := rfl
      rw [e1, e2, hel, hanc]
    exact hsel

/-! ## §5  Base case and preservation of `BranchInv` -/

private theorem ne_of_lLive_lFresh {l : concrete_st α} {t k : ℕ}
    (htnew : contains l t = false) (hlk : contains l k = true) : t ≠ k := by
  intro e'; rw [e', hlk] at htnew; exact absurd htnew (by simp)

/-- **Base case.**  Every LCA is its own branch: `BranchInv l l` (under `wf l`,
which makes each I4-climb a `climb_fixpoint`). -/
theorem branchInv_refl (l : concrete_st α) (hlwf : wf l) : BranchInv l l := by
  refine ⟨fun _ _ _ => rfl, ?_, fun k _ hk => hlwf k hk⟩
  intro k hlk _
  apply climb_fixpoint
  rcases hlwf k hlk with h | h
  · exact Or.inl h
  · exact Or.inr (by rw [← contains_eq_domain]; exact h)

/-- **Preservation under `Ins`.**  A fresh insert (id `t` new to both `l` and `a`)
preserves `BranchInv`: an original node is untouched by the `upd`, and growing the
stop-set by the off-forest id `t` leaves the LCA-climb unchanged
(`climb_aux_I_congr`). -/
theorem branchInv_doIns (l a : concrete_st α) (t r : ℕ) (e : α) (anch : ℕ) (pre : List ℕ)
    (hlwf : wf l) (htnew_l : contains l t = false) (hbi : BranchInv l a) :
    BranchInv l (do_ a (t, r, .Ins e pre anch)) := by
  obtain ⟨hI2, hI4, hI3⟩ := hbi
  have hdo : do_ a (t, r, .Ins e pre anch) = upd a t (e, resolve a (anch :: pre)) := by
    simp only [do_]
  set v := resolve a (anch :: pre) with hv
  have hcongr : ∀ y, contains l y = true → domain (upd a t (e, v)) y = domain a y := by
    intro y hly
    have hyt : t != y := by simp [ne_of_lLive_lFresh htnew_l hly]
    have h := lemma_InDomUpd2 a y t (e, v) hyt
    simpa only [contains, domain, mem] using h
  refine ⟨?_, ?_, ?_⟩
  · intro k hlk hak'
    rw [hdo] at hak' ⊢
    have hkt : t != k := by simp [ne_of_lLive_lFresh htnew_l hlk]
    have hak : contains a k = true := by
      rw [lemma_InDomUpd2 a k t (e, v) hkt] at hak'; exact hak'
    have : el (upd a t (e, v)) k = el a k := by
      simp only [el]; rw [lemma_SelUpd2 a k t (e, v) hkt]
    rw [this]; exact hI2 k hlk hak
  · intro k hlk hak'
    rw [hdo] at hak' ⊢
    have hkt : t != k := by simp [ne_of_lLive_lFresh htnew_l hlk]
    have hak : contains a k = true := by
      rw [lemma_InDomUpd2 a k t (e, v) hkt] at hak'; exact hak'
    have hanc : anc (upd a t (e, v)) k = anc a k := by
      simp only [anc]; rw [lemma_SelUpd2 a k t (e, v) hkt]
    rw [hanc]
    simp only [climb]
    rw [climb_aux_I_congr l hlwf (domain (upd a t (e, v))) (domain a) hcongr
          (anc l k) (anc l k) (hlwf k hlk)]
    have := hI4 k hlk hak
    simpa only [climb] using this
  · intro k hlk hak'
    rw [hdo] at hak' ⊢
    have hkt : t != k := by simp [ne_of_lLive_lFresh htnew_l hlk]
    have hak : contains a k = true := by
      rw [lemma_InDomUpd2 a k t (e, v) hkt] at hak'; exact hak'
    have hanc : anc (upd a t (e, v)) k = anc a k := by
      simp only [anc]; rw [lemma_SelUpd2 a k t (e, v) hkt]
    rw [hanc]; exact hI3 k hlk hak

/-- Domain of a `Del`: the source domain with `x` removed. -/
theorem domain_doDel (a : concrete_st α) (t r x : ℕ) (pre : List ℕ) :
    domain (do_ a (t, r, .Del pre x)) = (fun z => domain a z && x != z) := by
  funext z
  have h := contains_doDel a t r x pre z
  simp only [contains, domain, mem] at h ⊢
  rw [h, bne_comm]

/-- **Preservation under `Del`** — the crux, with the anchor-coincidence's inductive
step.  Deleting a live `x` (accurate) rehomes `x`'s children to `anc a x`.  On the
merge side the stop-set loses `x`; the LCA-climb of an original node either is
unchanged (`climb_remove_ne`, when its result is not `x`) or continues *through*
`x` to `anc a x` (`climb_remove_eq_result` + `climb_remove_ne`), exactly matching
the rehoming.  A non-live target leaves live nodes untouched. -/
theorem branchInv_doDel (l a : concrete_st α) (t r x : ℕ) (pre : List ℕ)
    (ha0 : contains a 0 = false) (hlwf : wf l) (hlmono : id_mono l) (hamono : id_mono a)
    (hacc : accurate (t, r, .Del pre x) a) (hbi : BranchInv l a) :
    BranchInv l (do_ a (t, r, .Del pre x)) := by
  obtain ⟨hI2, hI4, hI3⟩ := hbi
  simp only [accurate, opLeaf, opPath] at hacc
  have hHdec : ∀ y, contains l y = true → y ≠ 0 → anc l y < y := by
    intro y hy hy0; rcases hlmono y hy with h | h
    · omega
    · exact h
  have hHstay : ∀ y, contains l y = true → (anc l y = 0 ∨ contains l (anc l y) = true) := hlwf
  have hdomdel : domain (do_ a (t, r, .Del pre x)) = (fun z => domain a z && x != z) :=
    domain_doDel a t r x pre
  by_cases hxlive : contains a x = true
  · have hx0 : x ≠ 0 := contains_ne_zero a x ha0 hxlive
    have hxpath : IsAncPath a x pre := by
      rcases hacc with ⟨hx0', _⟩ | ⟨_, hp⟩
      · exact absurd hx0' hx0
      · exact hp
    have hres : resolve a pre = anc a x := isAncPath_resolve a x pre hxpath
    refine ⟨?_, ?_, ?_⟩
    · intro k hlk hak'
      have hak : contains a k = true := by
        rw [contains_doDel a t r x pre k, Bool.and_eq_true] at hak'; exact hak'.1
      rw [el_doDel a t r x pre k]; exact hI2 k hlk hak
    · intro k hlk hak'
      have hak : contains a k = true := by
        rw [contains_doDel a t r x pre k, Bool.and_eq_true] at hak'; exact hak'.1
      rw [anc_doDel a t r x pre k, hres, hdomdel]
      by_cases hax : anc a k = x
      · rw [if_pos hax]
        have hxl : contains l x = true := by
          rcases hI3 k hlk hak with h | h
          · rw [hax] at h; exact absurd h hx0
          · rw [hax] at h; exact h
        have hstepk :
            climb (fun y => anc l y) (fun z => domain a z && x != z) (anc l k)
              = climb (fun y => anc l y) (fun z => domain a z && x != z) (anc l x) := by
          apply climb_remove_eq_result l hHdec hHstay (domain a) x hxl hx0 (anc l k) (hlwf k hlk)
          rw [hI4 k hlk hak]; exact hax
        rw [hstepk]
        have hancax : anc a x ≠ x := by
          rcases hamono x hxlive with h | h
          · rw [h]; exact fun e => hx0 e.symm
          · omega
        have hne : climb (fun y => anc l y) (domain a) (anc l x) ≠ x := by
          rw [hI4 x hxl hxlive]; exact hancax
        rw [climb_remove_ne (fun y => anc l y) (domain a) x (anc l x) hne]
        exact hI4 x hxl hxlive
      · rw [if_neg hax]
        have hne : climb (fun y => anc l y) (domain a) (anc l k) ≠ x := by
          rw [hI4 k hlk hak]; exact hax
        rw [climb_remove_ne (fun y => anc l y) (domain a) x (anc l k) hne]
        exact hI4 k hlk hak
    · intro k hlk hak'
      have hak : contains a k = true := by
        rw [contains_doDel a t r x pre k, Bool.and_eq_true] at hak'; exact hak'.1
      rw [anc_doDel a t r x pre k, hres]
      by_cases hax : anc a k = x
      · rw [if_pos hax]
        have hxl : contains l x = true := by
          rcases hI3 k hlk hak with h | h
          · rw [hax] at h; exact absurd h hx0
          · rw [hax] at h; exact h
        exact hI3 x hxl hxlive
      · rw [if_neg hax]; exact hI3 k hlk hak
  · have hxdom : domain a x = false := by
      cases h : domain a x with
      | false => rfl
      | true => exact absurd (by rw [contains_eq_domain]; exact h) hxlive
    have hdomeq : domain (do_ a (t, r, .Del pre x)) = domain a := by
      rw [hdomdel]; funext z
      show (domain a z && (x != z)) = domain a z
      by_cases hzx : z = x
      · subst hzx; simp only [bne_self_eq_false, Bool.and_false, hxdom]
      · have hb : (x != z) = true := by simp [Ne.symm hzx]
        rw [hb, Bool.and_true]
    have hanceq : ∀ k, contains a k = true → anc (do_ a (t, r, .Del pre x)) k = anc a k := by
      intro k _
      rw [anc_doDel a t r x pre k]
      by_cases hax : anc a k = x
      · rw [if_pos hax]
        rcases hacc with ⟨hx0', hpnil⟩ | ⟨hxl', _⟩
        · rw [hpnil]; simp only [resolve]; rw [hax, hx0']
        · exact absurd hxl' hxlive
      · rw [if_neg hax]
    refine ⟨?_, ?_, ?_⟩
    · intro k hlk hak'
      have hak : contains a k = true := by
        rw [contains_doDel a t r x pre k, Bool.and_eq_true] at hak'; exact hak'.1
      rw [el_doDel a t r x pre k]; exact hI2 k hlk hak
    · intro k hlk hak'
      have hak : contains a k = true := by
        rw [contains_doDel a t r x pre k, Bool.and_eq_true] at hak'; exact hak'.1
      rw [hanceq k hak, hdomeq]; exact hI4 k hlk hak
    · intro k hlk hak'
      have hak : contains a k = true := by
        rw [contains_doDel a t r x pre k, Bool.and_eq_true] at hak'; exact hak'.1
      rw [hanceq k hak]; exact hI3 k hlk hak

/-! ## §6  Fold corollary and the single-sided headline

A branch is built by folding a list of *good* branch events over the LCA: each is
an accurate, fresh, monotonically-allocated `Ins` whose id is new to the LCA, or an
accurate `Del`.  `BranchInv` (with `RgaInv`/`id_mono`) is preserved along such a
fold, so a branch folded from `l` satisfies `BranchInv l ·`, and merging it against
the unchanged LCA reproduces it. -/

/-- One good branch step: an accurate/fresh/monotone `Ins` fresh to `l`, or an
accurate `Del`.  These are exactly the premises that thread `RgaInv`, `id_mono`
(imported invariance lemmas) and `BranchInv` (§5) in one shot. -/
def BranchStepOK (l s : concrete_st α) : op_t α → Prop
  | (t, r, .Ins e pre a) =>
      accurate (t, r, .Ins e pre a) s ∧ fresh_ts (t, r, .Ins e pre a) s
        ∧ mono_alloc (t, r, .Ins e pre a) s ∧ contains l t = false
  | (t, r, .Del pre x)   => accurate (t, r, .Del pre x) s

/-- Every step of `Ea` is good at its own prefix fold. -/
def GoodBranchFold (l : concrete_st α) : concrete_st α → List (op_t α) → Prop
  | _, []        => True
  | s, o :: rest => BranchStepOK l s o ∧ GoodBranchFold l (do_ s o) rest

/-- **Threading.**  `RgaInv ∧ id_mono ∧ BranchInv l` is preserved along a good
branch fold. -/
theorem branchInv_triple_fold (l : concrete_st α) (hlwf : wf l) (hlmono : id_mono l) :
    ∀ (Ea : List (op_t α)) (s : concrete_st α),
      RgaInv s → id_mono s → BranchInv l s → GoodBranchFold l s Ea →
      RgaInv (applySeqR s Ea) ∧ id_mono (applySeqR s Ea) ∧ BranchInv l (applySeqR s Ea) := by
  intro Ea
  induction Ea with
  | nil => intro s hR hm hB _; exact ⟨hR, hm, hB⟩
  | cons o rest ih =>
    intro s hR hm hB hgf
    simp only [GoodBranchFold] at hgf
    obtain ⟨hstep, hrest⟩ := hgf
    rw [applySeqR_cons]
    obtain ⟨t, r, op⟩ := o
    cases op with
    | Ins e pre anch =>
      simp only [BranchStepOK] at hstep
      obtain ⟨hacc, hfr, hmalloc, htl⟩ := hstep
      exact ih (do_ s (t, r, .Ins e pre anch))
        (Inv_doIns s t r e anch pre hR hacc hfr)
        (id_mono_doIns s t r e anch pre hm hmalloc)
        (branchInv_doIns l s t r e anch pre hlwf htl hB) hrest
    | Del pre x =>
      simp only [BranchStepOK] at hstep
      exact ih (do_ s (t, r, .Del pre x))
        (Inv_doDel s t r x pre hR hstep)
        (id_mono_doDel s t r x pre hR.1 hm hstep)
        (branchInv_doDel l s t r x pre hR.1 hlwf hlmono hm hstep hB) hrest

/-- **Single-sided headline.**  For a reachable LCA `l` and a branch built by
a good fold `Ea` of concurrent events over `l`, merging the branch against the
unchanged LCA observationally reproduces the branch:

    eq (merge l (applySeqR l Ea) l) (applySeqR l Ea).

This isolates the survival/climb-vs-`do_` coincidence (the design's core bet)
without the two-sided interleave: merge's LCA-climb re-anchoring reproduces the
fold's `resolve`-rehoming, pointwise per surviving id. -/
theorem eq_merge_branch_single (l : concrete_st α) (Ea : List (op_t α))
    (hl : RgaInv l) (hlmono : id_mono l) (hgf : GoodBranchFold l l Ea) :
    eq (merge l (applySeqR l Ea) l) (applySeqR l Ea) := by
  obtain ⟨hl0, hlwf⟩ := hl
  obtain ⟨hR, _, hB⟩ := branchInv_triple_fold l hlwf hlmono Ea l
    ⟨hl0, hlwf⟩ hlmono (branchInv_refl l hlwf) hgf
  exact eq_merge_single l (applySeqR l Ea) hR.2 hB

/-! ## §7  Axiom audit -/

#print axioms climb_remove_eq_result
#print axioms eq_merge_single
#print axioms branchInv_doDel
#print axioms eq_merge_branch_single

/-! ## Generalizing to the two-sided merge

The single-sided bridge (§6) settles the mathematical crux for one branch: the
per-id anchor coincidence `climb (anc l) (dom a) (anc l k) = anc a k`, proved
as the reachable invariant `BranchInv` whose `Del`-step is the rehoming-through-`x`
argument (`climb_remove_eq_result`).

The two-sided identity `eq (merge l a b) (applySeqR l π)` (`π` a `loOnA`-interleave
of `Ea ++ Eb`) extends this along two orthogonal axes:

* the survivor set: `survivors l a b` (generalizing `survivors_single`) is the
  add/del image of `Ea ∪ Eb` over `dom l`, and for a `loOnA`-respecting fold this
  equals the domain of `applySeqR l π` (an `applySeqR`-domain induction, cf.
  `contains_doDel`/`lemma_InDomUpd1`);
* the anchor coincidence for the merged forest: `BranchInv` generalizes to
  `BranchInv2 l a b`, with the birth-anchor read by `birthAnc l a b` and the
  stop-set `survivors l a b`; the same climb-vs-rehoming argument applies, because
  a surviving node's anchor still climbs the `l`-forest to the nearest two-sided
  survivor.  The interleave-order independence needed to identify `applySeqR l π`
  for two `loOnA`-respecting `π` comes from the `RGA_conditioned_convergence`
  engine (fold-swap over `eq`), via `general_swap_bothFaithful`.

Neither axis reopens the design question the single-sided bridge settles; both are
additive to this file. `RGA_MergeLinearization_TwoSided` carries out this
generalization. -/

end RGAMergeLinearization
