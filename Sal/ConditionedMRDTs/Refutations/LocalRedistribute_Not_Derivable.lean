import Sal.ConditionedMRDTs.Metatheory.VC_Minimal_Core

/-!
# Kill-test: `VC6` (feasible local-redistribute) is INDEPENDENT (task #114, phase 2, T1)

Settles the `VC6` verdict of the VC-minimality sweep
(`whiteboard/vc-minimality-note.md`, the VC6 section): the feasible
local-redistribute law is NOT derivable from the other seven verification
conditions — it is the CHANGE-WINS FLAG.

**Verdict: independent.** The **change-wins flag** `CWFlag` satisfies
`CoreVCs3CD` (VC1–VC4), `FeasibleInitVC` (VC5), `FeasibleRedistributeVC` (VC7)
and `CDVC3` (VC8), yet its merge of the note's four-event countermodel is not a
canonical state, so it is not RA-linearizable (`CWFlag_not_joinLemma3`). The
single failing condition is `VC6`.

## The datatype

* **Σ = `Bool`**, `init = false`; ops `set` (writes `true`), `clear` (writes
  `false`), both constants (`AppOp = Bool`, `do s o = o.2.2`);
  `rc(clear,set) = Fst_then_snd` (add-wins), else `Either`.
* **merge** `mergeL l a b = if l then a ∧ b else a ∨ b`: "whoever changed the
  flag relative to the LCA wins."

## The green conditions

Since `do` is constant, `commutes o₁ o₂ ↔ o₁.2.2 = o₂.2.2`
(`cw_commutes_iff`). VC1–VC4, VC5, VC7 reduce to `Bool` identities. VC8 (CDVC3)
is NOT a finite identity — `mergeL true false u = u` fails for `u = set` — and
its greenness rests on the configuration structure: since `do` is constant,
`σ(ev)` is the written value of the `loOn(ev)`-maximal event
(`cw_canon_value`), and for `e = set` the maximal element of `↓e∖e` is a
`clear` (immediate causal predecessor, `cw_downMax_ne`), forcing `B = false`;
the `e = clear` corner uses add-wins to force `A = false` (`cw_A_false`).

## The countermodel (from the note, LHS = 0 vs RHS = 1)

Events `sA = set`, `cL = clear` with `vis sA cL`, `sE = set` concurrent with
`cL`. Sides `E₁ = {sA, sE}`, `E₂ = {sA, cL}`, LCA `{sA}`. Canonical states
`s₀ = σ({sA}) = true`, `s₁ = σ(E₁) = true`, `s₂ = σ(E₂) = false`;
`σ(E₁∪E₂) = true` (the add-wins `rc` orders `cL` before `sE`). The merge
`mergeL true true false = false ≠ true = σ(E₁∪E₂)`: the re-asserting `set`
`sE` cannot be seen by state-level change-detection.
-/

namespace Sal.ConditionedMRDTs.LocalRedistributeNotDerivable

open Sal.Emulation

/-! ## §1. The change-wins flag -/

/-- The change-wins merge table: `l = true` (changed) ⇒ `∧`, else `∨`. -/
def cwMergeL (l a b : Bool) : Bool := cond l (a && b) (a || b)

/-- The add-wins arbitration: `rc(clear,set) = Fst`, else `Either`. -/
def cwRc (o₁ o₂ : Op Bool) : RcRes :=
  cond (!o₁.2.2 && o₂.2.2) RcRes.Fst_then_snd RcRes.Either

/-- **The change-wins flag.** State `Bool`, `init = false`, `do s o = o.2.2`
(constant per op), merge `cwMergeL`, `rc` add-wins. -/
def CWFlag : ConditionedMRDTSig where
  toMRDTSig :=
    { State := Bool
      dec_state := inferInstance
      init := false
      AppOp := Bool
      dec_op := inferInstance
      Query := Unit
      Value := Bool
      update := fun _ o => o.2.2
      merge := fun a b => a || b
      query := fun s _ => s
      rc := cwRc
      mergeL := cwMergeL
      merge_init_slice := fun _ _ => rfl }
  Inv := fun _ => True
  applicable := fun _ _ => True

@[simp] theorem CW_mergeL (l a b : Bool) : CWFlag.mergeL l a b = cwMergeL l a b := rfl
@[simp] theorem CW_update (s : Bool) (o : Op Bool) : CWFlag.update s o = o.2.2 := rfl
@[simp] theorem CW_init : CWFlag.init = false := rfl
@[simp] theorem CW_rc (o₁ o₂ : Op Bool) : CWFlag.rc o₁ o₂ = cwRc o₁ o₂ := rfl

/-- Constant `do` ⇒ commutation is equality of written values. -/
theorem cw_commutes_iff (o₁ o₂ : Op CWFlag.AppOp) :
    CWFlag.toCRDTSig.commutes o₁ o₂ ↔ o₁.2.2 = o₂.2.2 :=
  ⟨fun h => (h false).symm, fun h _ => h.symm⟩

theorem cw_not_commutes_iff (o₁ o₂ : Op CWFlag.AppOp) :
    ¬ CWFlag.toCRDTSig.commutes o₁ o₂ ↔ o₁.2.2 ≠ o₂.2.2 := by
  rw [cw_commutes_iff]

/-! ### Bool identities (`by decide`) -/

theorem cw_comm_id : ∀ l a b : Bool, cwMergeL l a b = cwMergeL l b a := by decide
theorem cw_init_id : ∀ s : Bool, cwMergeL false false s = s := by decide
theorem cw_redis_id : ∀ B t₀ t₁ t₂ u : Bool,
    cwMergeL (cwMergeL B t₀ u) (cwMergeL B t₁ u) (cwMergeL B t₂ u)
      = cwMergeL B (cwMergeL t₀ t₁ t₂) u := by decide
theorem cw_eq_true_of_ne_false : ∀ b : Bool, b ≠ false → b = true := by decide
theorem cw_eq_false_of_ne_true : ∀ b : Bool, b ≠ true → b = false := by decide
/-- The guarded CDVC3 cell: with `B = false` when `u = set`, and
`B = true ∨ A = false` when `u = clear`, `mergeL B A u = u`. -/
theorem cw_cd_close : ∀ Bv Av uv : Bool,
    (uv = true → Bv = false) → (uv = false → Bv = true ∨ Av = false) →
    cwMergeL Bv Av uv = uv := by decide

/-! ## §2. The green update layer (VC1–VC4) -/

theorem CWFlag_updateVCs : UpdateVCs CWFlag.toCRDTSig where
  rc_non_comm_directional := fun o₁ o₂ _ _ => by
    rw [cw_not_commutes_iff]
    obtain ⟨_, _, v₁⟩ := o₁; obtain ⟨_, _, v₂⟩ := o₂
    simp only [CW_rc, cwRc]
    cases v₁ <;> cases v₂ <;> simp
  no_rc_chain := fun o₁ o₂ o₃ _ _ => by
    obtain ⟨_, _, v₁⟩ := o₁; obtain ⟨_, _, v₂⟩ := o₂; obtain ⟨_, _, v₃⟩ := o₃
    simp only [CW_rc, cwRc]
    cases v₁ <;> cases v₂ <;> cases v₃ <;> decide
  cond_comm_lift := fun _ _ _ _ _ _ _ _ _ _ => by simp only [CW_update]

theorem CWFlag_mergeL_comm (l a b : CWFlag.State) :
    CWFlag.mergeL l a b = CWFlag.mergeL l b a := cw_comm_id l a b

theorem CWFlag_coreVCs3CD : CoreVCs3CD CWFlag where
  update_core := CWFlag_updateVCs
  mergeL_comm := CWFlag_mergeL_comm

/-! ## §3. VC5 and VC7 (green Bool identities) -/

/-- **VC5 (feasible_init) is green**: `mergeL false false s = s`. -/
theorem CWFlag_feasibleInit : FeasibleInitVC CWFlag := by
  intro C ev s _ _
  simp only [CW_mergeL, CW_init]
  exact cw_init_id s

/-- **VC7 (feasible_redistribute) is green** (universal `Bool` identity). -/
theorem CWFlag_feasibleRedistribute : FeasibleRedistributeVC CWFlag := by
  intro C ev₁ ev₂ t₀ t₁ t₂ B e _ _ _ _ _ _ _ _ _ _ _ _ _
  simp only [CW_mergeL, CW_update]
  exact cw_redis_id B t₀ t₁ t₂ e.2.2

/-! ## §4. The `σ = value-of-maximal` machinery (constant `do`) -/

/-- `applySeq init (ρ ++ [x]) = x.2.2` (constant `do`). -/
theorem cw_fold_concat (s : Bool) (ρ : List (Op Bool)) (x : Op Bool) :
    applySeq CWFlag.toCRDTSig s (ρ ++ [x]) = x.2.2 := by
  rw [applySeq_append_single]; rfl

/-- A `visNC`-path folds to a `vis`-edge (`vis` transitive). -/
theorem cw_transGen_vis {C : Sal.Emulation.Configuration CWFlag.toCRDTSig}
    (h_tr : ∀ {a b c : Op CWFlag.AppOp}, C.vis a b → C.vis b c → C.vis a c)
    {x y : Op CWFlag.AppOp}
    (h : Relation.TransGen (fun a b => C.vis a b ∧ ¬ CWFlag.toCRDTSig.commutes a b) x y) :
    C.vis x y := by
  induction h with
  | single h => exact h.1
  | tail _ h ih => exact h_tr ih h.1

/-- **First-edge decomposition** of a `visNC`-path: either `m` reaches the
target in one hop, or its first hop lands on a strict intermediate. -/
theorem cw_transGen_first {C : Sal.Emulation.Configuration CWFlag.toCRDTSig}
    {m e : Op CWFlag.AppOp}
    (h : Relation.TransGen
      (fun a b => C.vis a b ∧ ¬ CWFlag.toCRDTSig.commutes a b) m e) :
    (C.vis m e ∧ ¬ CWFlag.toCRDTSig.commutes m e) ∨
      ∃ z, (C.vis m z ∧ ¬ CWFlag.toCRDTSig.commutes m z) ∧
        Relation.TransGen (fun a b => C.vis a b ∧ ¬ CWFlag.toCRDTSig.commutes a b) z e := by
  induction h with
  | single h => exact Or.inl h
  | @tail mid e' _ h₂ ih =>
    rcases ih with hdirect | ⟨z, hz1, hz2⟩
    · exact Or.inr ⟨mid, hdirect, Relation.TransGen.single h₂⟩
    · exact Or.inr ⟨z, hz1, hz2.tail h₂⟩

/-- **The canonical state is the written value of a `loOn`-maximal event.**
Since `do` is constant, a `loOn(ev)`-respecting fold is decided by its last
(maximal) event. Either `ev = ∅` and `s = σ₀ = false`, or there is a
`loOn(ev)`-maximal `m ∈ ev` with `s = m.2.2`. -/
theorem cw_canon_value {C : Sal.Emulation.Configuration CWFlag.toCRDTSig}
    {ev : Set (Op CWFlag.AppOp)} {s : Bool}
    (h : IsCanonicalState C ev s) :
    (ev = ∅ ∧ s = false) ∨
      ∃ m, m ∈ ev ∧ (∀ x ∈ ev, x ≠ m → ¬ loOn C ev m x) ∧ s = m.2.2 := by
  obtain ⟨ρ, hperm, hresp, hfold⟩ := h
  rcases List.eq_nil_or_concat ρ with rfl | ⟨ρ', x, rfl⟩
  · left
    refine ⟨?_, hfold.symm⟩
    ext y
    simp only [Set.mem_empty_iff_false, iff_false]
    exact fun hy => absurd ((hperm.2 y).mpr hy) List.not_mem_nil
  · right
    simp only [List.concat_eq_append] at hperm hresp hfold
    have hx_ev : x ∈ ev :=
      (hperm.2 x).mp (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    refine ⟨x, hx_ev, ?_, ?_⟩
    · intro z hz hzne
      have hz_mem : z ∈ ρ' ++ [x] := (hperm.2 z).mpr hz
      have hz_ρ' : z ∈ ρ' := by
        rcases List.mem_append.mp hz_mem with h | h
        · exact h
        · exact absurd (List.mem_singleton.mp h) hzne
      exact last_is_maximal hresp z hz_ρ'
    · rw [← hfold, cw_fold_concat]

/-- **L3.** A `loOn(↓e∖e)`-maximal `m` is `vis∧¬commutes`-adjacent to `e`
(the maximal predecessor is *immediate*), so `m.2.2 ≠ e.2.2`. -/
theorem cw_downMax_ne {C : Sal.Emulation.Configuration CWFlag.toCRDTSig}
    (h_tr : ∀ {a b c : Op CWFlag.AppOp}, C.vis a b → C.vis b c → C.vis a c)
    (h_ir : ∀ a : Op CWFlag.AppOp, ¬ C.vis a a)
    {e m : Op CWFlag.AppOp}
    (hm : m ∈ downset C e \ {e})
    (hmax : ∀ x ∈ downset C e \ {e}, x ≠ m →
      ¬ loOn C (downset C e \ {e}) m x) :
    m.2.2 ≠ e.2.2 := by
  obtain ⟨hmd, hmne⟩ := hm
  have htg : Relation.TransGen
      (fun a b => C.vis a b ∧ ¬ CWFlag.toCRDTSig.commutes a b) m e := by
    rcases hmd with rfl | h
    · exact absurd rfl hmne
    · exact h
  have hvisNC : C.vis m e ∧ ¬ CWFlag.toCRDTSig.commutes m e := by
    rcases cw_transGen_first htg with hme | ⟨z, hz1, hz2⟩
    · exact hme
    · exfalso
      have hz_d : z ∈ downset C e := Or.inr hz2
      have hz_ne : z ≠ e := by
        rintro rfl; exact h_ir z (cw_transGen_vis h_tr hz2)
      have hm_ne_z : m ≠ z := by
        rintro rfl; exact h_ir m hz1.1
      exact hmax z ⟨hz_d, hz_ne⟩ (fun h => hm_ne_z h.symm) (Or.inl hz1)
  rw [cw_not_commutes_iff] at hvisNC
  exact hvisNC.2

/-- **L4.** If `e` is a `clear` (`e.2.2 = false`), is `loOn(U)`-maximal, and has
no proper causal predecessor (`↓e∖e = ∅`), then `A = σ(U∖e) = false`: the
`loOn(U∖e)`-maximal element cannot be a `set`, else its add-wins absorber (in
`U`) defeats its own maximality. -/
theorem cw_A_false {C : Sal.Emulation.Configuration CWFlag.toCRDTSig}
    {U : Set (Op CWFlag.AppOp)} {e : Op CWFlag.AppOp} {A : Bool}
    (he_clear : e.2.2 = false) (he_U : e ∈ U)
    (h_emax : ∀ x ∈ U, x ≠ e → ¬ loOn C U e x)
    (h_down_empty : downset C e \ {e} = ∅)
    (hA : IsCanonicalState C (U \ {e}) A) : A = false := by
  rcases cw_canon_value hA with ⟨_, hAf⟩ | ⟨m, hm, hmax, hAm⟩
  · exact hAf
  · obtain ⟨hmU, hmne⟩ := hm
    by_contra hAne
    rw [hAm] at hAne
    have hm_set : m.2.2 = true := cw_eq_true_of_ne_false m.2.2 hAne
    have hnc_me : ¬ CWFlag.toCRDTSig.commutes m e := by
      rw [cw_not_commutes_iff, hm_set, he_clear]; simp
    have h_not_vis_me : ¬ C.vis m e := by
      intro hv
      have hmem : m ∈ downset C e \ {e} :=
        ⟨Or.inr (Relation.TransGen.single ⟨hv, hnc_me⟩), hmne⟩
      rw [h_down_empty] at hmem; exact hmem
    have h_not_vis_em : ¬ C.vis e m := by
      intro hv
      exact h_emax m hmU hmne (Or.inl ⟨hv, fun hc => hnc_me (fun s => (hc s).symm)⟩)
    have h_rc_em : CWFlag.rc e m = RcRes.Fst_then_snd := by
      rw [CW_rc]; unfold cwRc; rw [he_clear, hm_set]; rfl
    have h_abs : ∃ e₃ ∈ U, C.vis m e₃ ∧ ¬ CWFlag.toCRDTSig.commutes m e₃ := by
      by_contra hno
      exact h_emax m hmU hmne (Or.inr ⟨h_not_vis_em, h_not_vis_me, h_rc_em, hno⟩)
    obtain ⟨e₃, he3U, hv3, hnc3⟩ := h_abs
    have he3_clear : e₃.2.2 = false :=
      cw_eq_false_of_ne_true e₃.2.2
        (fun hc => (cw_not_commutes_iff m e₃).mp hnc3 (hm_set.trans hc.symm))
    have he3_ne_e : e₃ ≠ e := by
      rintro rfl
      have hmem : m ∈ downset C e₃ \ {e₃} :=
        ⟨Or.inr (Relation.TransGen.single ⟨hv3, hnc3⟩), hmne⟩
      rw [h_down_empty] at hmem; exact hmem
    have he3_ne_m : e₃ ≠ m := by
      rintro rfl; rw [hm_set] at he3_clear; exact Bool.noConfusion he3_clear
    exact hmax e₃ ⟨he3U, he3_ne_e⟩ he3_ne_m (Or.inl ⟨hv3, hnc3⟩)

/-! ## §5. VC8 (CDVC3) is green -/

/-- **VC8 (CDVC3) is green.** For `e = set`, `B = σ(↓e∖e) = false` (the maximal
predecessor is a `clear`); for `e = clear`, either `B = true` (nonempty
downset) or `A = σ(U∖e) = false` (empty downset, add-wins). `cw_cd_close`
finishes. -/
theorem CWFlag_cdVC3 : CDVC3 CWFlag := by
  intro C U A B e h_tr h_ir h_inU h_clU he_U h_max hA hB
  simp only [CW_mergeL, CW_update]
  refine cw_cd_close B A e.2.2 ?_ ?_
  · -- e.2.2 = true (set) ⇒ B = false
    intro he
    rcases cw_canon_value hB with ⟨_, hBf⟩ | ⟨m, hm, hmmax, hBm⟩
    · exact hBf
    · have hne := cw_downMax_ne h_tr h_ir hm hmmax
      rw [he] at hne; rw [hBm]
      exact cw_eq_false_of_ne_true m.2.2 hne
  · -- e.2.2 = false (clear) ⇒ B = true ∨ A = false
    intro he
    rcases cw_canon_value hB with ⟨hdempty, _⟩ | ⟨m, hm, hmmax, hBm⟩
    · right; exact cw_A_false he he_U h_max hdempty hA
    · left
      have hne := cw_downMax_ne h_tr h_ir hm hmmax
      rw [he] at hne; rw [hBm]
      exact cw_eq_true_of_ne_false m.2.2 hne

/-! ## §6. The four-event countermodel and non-RA-linearizability -/

/-- `sA = set` at replica 0, ts 0. -/
def sA : Op Bool := (0, 0, true)
/-- `cL = clear` at replica 0, ts 1 (`vis sA cL`). -/
def cL : Op Bool := (1, 0, false)
/-- `sE = set` at replica 1, ts 2 (concurrent with `cL`). -/
def sE : Op Bool := (2, 1, true)

/-- Every event of any replica set is one of the three literals. -/
theorem cw_L_cases (r : Replica) (s : Set (Op Bool))
    (hL : (if r = 0 then some ({sA, cL} : Set (Op Bool))
           else if r = 1 then some {sA, sE} else none) = some s) :
    ∀ x ∈ s, x = sA ∨ x = cL ∨ x = sE := by
  intro x hx
  by_cases h0 : r = 0
  · rw [if_pos h0, Option.some.injEq] at hL; rw [← hL] at hx
    rcases hx with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · by_cases h1 : r = 1
    · rw [if_neg h0, if_pos h1, Option.some.injEq] at hL; rw [← hL] at hx
      rcases hx with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rw [if_neg h0, if_neg h1] at hL; exact absurd hL (by simp)

/-- The refuting configuration. Replica 0 holds `{sA, cL}`; replica 1 holds
`{sA, sE}`. The single `vis`-edge is `sA → cL`. -/
def cwConfig : Sal.Emulation.Configuration CWFlag.toCRDTSig where
  N := fun r => if r = 0 then some false else if r = 1 then some true else none
  L := fun r => if r = 0 then some {sA, cL} else if r = 1 then some {sA, sE} else none
  vis := fun x y => x = sA ∧ y = cL
  dom_eq := by
    intro r; by_cases h0 : r = 0
    · simp [h0]
    · by_cases h1 : r = 1 <;> simp [h0, h1]
  vis_src := by rintro x y ⟨rfl, rfl⟩; exact ⟨0, {sA, cL}, by simp, Or.inl rfl⟩
  vis_tgt := by rintro x y ⟨rfl, rfl⟩; exact ⟨0, {sA, cL}, by simp, Or.inr rfl⟩
  vis_causal := by
    rintro x y r s ⟨rfl, rfl⟩ hL hs
    by_cases h0 : r = 0
    · rw [if_pos h0, Option.some.injEq] at hL; rw [← hL]; exact Or.inl rfl
    · by_cases h1 : r = 1
      · rw [if_neg h0, if_pos h1, Option.some.injEq] at hL; rw [← hL] at hs
        rcases hs with h | h
        · exact absurd h (by decide)
        · exact absurd h (by decide)
      · rw [if_neg h0, if_neg h1] at hL; exact absurd hL (by simp)
  timestamps_distinct := by
    intro x y r s r' s' hL hs hL' hs' hne
    rcases cw_L_cases r s hL x hs with rfl | rfl | rfl <;>
      rcases cw_L_cases r' s' hL' y hs' with rfl | rfl | rfl <;>
      first | exact absurd rfl hne | decide
  vis_total_same_replica := by
    intro x y r s r' s' hL hs hL' hs' hne hrep
    rcases cw_L_cases r s hL x hs with rfl | rfl | rfl <;>
      rcases cw_L_cases r' s' hL' y hs' with rfl | rfl | rfl <;>
      first
        | exact absurd rfl hne
        | exact absurd hrep (by decide)
        | exact Or.inl ⟨rfl, rfl⟩
        | exact Or.inr ⟨rfl, rfl⟩

/-! ### The `loOn` non-edges (`vis`/`rc` computations) -/

theorem cw_not_loOn_cL_sA (ev : Set (Op Bool)) : ¬ loOn cwConfig ev cL sA := by
  rintro (⟨hv, _⟩ | ⟨_, hnv2, _, _⟩)
  · exact absurd hv.1 (by decide)
  · exact hnv2 ⟨rfl, rfl⟩

theorem cw_not_loOn_sE_sA (ev : Set (Op Bool)) : ¬ loOn cwConfig ev sE sA := by
  rintro (⟨hv, _⟩ | ⟨_, _, hrc, _⟩)
  · exact absurd hv.1 (by decide)
  · rw [CW_rc] at hrc; exact absurd hrc (by decide)

theorem cw_not_loOn_sE_cL (ev : Set (Op Bool)) : ¬ loOn cwConfig ev sE cL := by
  rintro (⟨hv, _⟩ | ⟨_, _, hrc, _⟩)
  · exact absurd hv.1 (by decide)
  · rw [CW_rc] at hrc; exact absurd hrc (by decide)

/-! ### The canonical states (hand-derived: `σ({sA})=1`, `σ(E₁)=1`, `σ(E₂)=0`,
`σ(E₁∪E₂)=1`) -/

/-- `E₁ = {sA, sE}` (replica 1's set). -/
def E1 : Set (Op Bool) := {sA, sE}
/-- `E₂ = {sA, cL}` (replica 0's set). -/
def E2 : Set (Op Bool) := {sA, cL}

theorem cw_events_sA : sA ∈ cwConfig.events := ⟨0, {sA, cL}, by simp [cwConfig], Or.inl rfl⟩
theorem cw_events_cL : cL ∈ cwConfig.events := ⟨0, {sA, cL}, by simp [cwConfig], Or.inr rfl⟩
theorem cw_events_sE : sE ∈ cwConfig.events := ⟨1, {sA, sE}, by simp [cwConfig], Or.inr rfl⟩

theorem cw_inU : ∀ a ∈ E1 ∪ E2, a ∈ cwConfig.events := by
  rintro a (h | h)
  · rcases h with rfl | rfl
    · exact cw_events_sA
    · exact cw_events_sE
  · rcases h with rfl | rfl
    · exact cw_events_sA
    · exact cw_events_cL

/-- `σ(E₁∩E₂) = σ({sA}) = true`. -/
theorem cw_canon_inter : IsCanonicalState cwConfig (E1 ∩ E2) true := by
  have hset : E1 ∩ E2 = {sA} := by
    ext x
    simp only [E1, E2, Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h₁, h₂⟩; rcases h₁ with rfl | rfl
      · rfl
      · rcases h₂ with h | h <;> exact absurd h (by decide)
    · rintro rfl; exact ⟨Or.inl rfl, Or.inl rfl⟩
  rw [hset]
  exact ⟨[sA], ⟨List.nodup_singleton _, by intro a; simp⟩, List.pairwise_singleton _ _, rfl⟩

/-- `σ(E₁) = σ({sA, sE}) = true`. -/
theorem cw_canon_E1 : IsCanonicalState cwConfig E1 true := by
  refine ⟨[sA, sE], ⟨by decide, by intro a; simp [E1]⟩, ?_, rfl⟩
  refine List.pairwise_cons.mpr ⟨fun b hb => ?_, List.pairwise_singleton _ _⟩
  rw [List.mem_singleton] at hb; subst hb
  exact cw_not_loOn_sE_sA E1

/-- `σ(E₂) = σ({sA, cL}) = false`. -/
theorem cw_canon_E2 : IsCanonicalState cwConfig E2 false := by
  refine ⟨[sA, cL], ⟨by decide, by intro a; simp [E2]⟩, ?_, rfl⟩
  refine List.pairwise_cons.mpr ⟨fun b hb => ?_, List.pairwise_singleton _ _⟩
  rw [List.mem_singleton] at hb; subst hb
  exact cw_not_loOn_cL_sA E2

/-- `σ(E₁∪E₂) = σ({sA, cL, sE}) = true` (add-wins orders `cL` before `sE`). -/
theorem cw_canon_union : IsCanonicalState cwConfig (E1 ∪ E2) true := by
  refine ⟨[sA, cL, sE], ⟨by decide, by intro a; simp [E1, E2, Set.mem_union]; tauto⟩, ?_, rfl⟩
  refine List.pairwise_cons.mpr ⟨fun b hb => ?_, ?_⟩
  · rcases List.mem_cons.mp hb with rfl | hb
    · exact cw_not_loOn_cL_sA _
    · rw [List.mem_singleton] at hb; subst hb; exact cw_not_loOn_sE_sA _
  · refine List.pairwise_cons.mpr ⟨fun b hb => ?_, List.pairwise_singleton _ _⟩
    rw [List.mem_singleton] at hb; subst hb; exact cw_not_loOn_sE_cL _

/-! ### The Join failure (non-RA-linearizability) -/

/-- **The Join fails at the note's four-event countermodel.**
`mergeL (σ(E₁∩E₂)) (σ(E₁)) (σ(E₂)) = mergeL true true false = false`, but
`σ(E₁∪E₂) = true`: the change-wins merge cannot see the concurrent re-assertion
`sE`. -/
theorem CWFlag_not_joinLemma3 : ¬ JoinLemma3 CWFlag := by
  intro h
  have hjoin := h cwConfig E1 E2 true true false
    (by rintro x y z ⟨rfl, rfl⟩ ⟨h1, _⟩; exact absurd h1 (by decide))
    (by rintro a ⟨rfl, h⟩; exact absurd h (by decide))
    (fun a ha => cw_inU a (Or.inl ha)) (fun a ha => cw_inU a (Or.inr ha))
    (by rintro a b ⟨rfl, rfl⟩ _ hb; rcases hb with h | h <;> exact absurd h (by decide))
    (by rintro a b ⟨rfl, rfl⟩ _ _; exact Or.inl rfl)
    cw_canon_inter cw_canon_E1 cw_canon_E2
  -- hjoin : IsCanonicalState cwConfig (E1∪E2) (mergeL true true false = false)
  have huniq := isCanonicalState_unique_u CWFlag_updateVCs cw_inU hjoin cw_canon_union
  simp [CW_mergeL, cwMergeL] at huniq

/-! ### The VC6 failure pin (the note's LHS = 0 vs RHS = 1) -/

/-- FAIL pin: at the countermodel canonical states `s₀ = 1`, `B = 0`, `t₁ = 1`,
`s₂ = 0`, `u = do 0 sE = 1`, the local-redistribute equation reads `0 = 1`. -/
example :
    cwMergeL true (cwMergeL false true (sE.2.2)) false
      ≠ cwMergeL false (cwMergeL true true false) (sE.2.2) := by decide

/-! ## §7. The independence result -/

/-- **`VC6` is an independent VC.** There is a `ConditionedMRDTSig` satisfying
`CoreVCs3CD` (VC1–VC4), `FeasibleInitVC` (VC5), `FeasibleRedistributeVC` (VC7)
and `CDVC3` (VC8), which is not RA-linearizable (the Join fails at the
change-wins countermodel). Hence the flat set cannot be reduced by dropping
`feasible_local_redistribute`. -/
theorem local_redistribute_not_derivable :
    ∃ D : ConditionedMRDTSig,
      CoreVCs3CD D ∧ FeasibleInitVC D ∧ FeasibleRedistributeVC D ∧
      CDVC3 D ∧ ¬ JoinLemma3 D :=
  ⟨CWFlag, CWFlag_coreVCs3CD, CWFlag_feasibleInit, CWFlag_feasibleRedistribute,
   CWFlag_cdVC3, CWFlag_not_joinLemma3⟩

#print axioms local_redistribute_not_derivable

end Sal.ConditionedMRDTs.LocalRedistributeNotDerivable
