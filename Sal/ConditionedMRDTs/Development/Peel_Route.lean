import Sal.ConditionedMRDTs.MRDT_Instances.MRDT_Instances
/-!
# The peel route (HISTORICAL — superseded by the CD/feasible route)

The first proved ternary metatheorem (draft T2–T5): the two contextual peel
*equations* `JoinPeelVCs3` and the master induction `join_lemma3_of_peel`,
with the original end-to-end bridge `ra_linearizable_of_core_join3` and the
peel-route G-Set/Counter corollaries. Kept 0-sorry as the record; the
canonical route is `VC_Set.lean` + `Adequacy.lean` (one CD *equation*
instead of two three-set peel equations).
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

section
variable {D : ConditionedMRDTSig}

/-- **The ternary peel identities** (mission N3). For `e` maximal in
`loOn C (ev₁ ∪ ev₂)`:

* `peel_local3` — `e` local to side 1 (hence `e ∉ E₀ = ev₁ ∩ ev₂`): peel side 1
  only; the LCA component is untouched (`(ev₁ ∖ {e}) ∩ ev₂ = ev₁ ∩ ev₂`).
* `peel_shared3` — `e` shared (a shared event **is** an LCA event): peel all three
  components; the LCA set shrinks in lock-step
  (`(ev₁ ∖ {e}) ∩ (ev₂ ∖ {e}) = (ev₁ ∩ ev₂) ∖ {e}`).

CAUTION (recorded in the draft T3): a union-maximal shared `e` need NOT be
`loOn(E₀)`-maximal (`loOn` is antitone in the set — an absorber in
`(ev₁ ∪ ev₂) ∖ E₀` disappears when the set shrinks to `E₀`), so `s₀ = update t₀ e`
is NOT available and must not be assumed; `t₀` is an independent canonical state.
This is the A3/A5 lesson recurring one level up. -/
structure JoinPeelVCs3 (D : ConditionedMRDTSig) : Prop where
  /-- Peel a union-maximal event local to side 1; the LCA component is inert. -/
  peel_local3 :
    ∀ (C : Sal.Emulation.Configuration D.toCRDTSig)
      (ev₁ ev₂ : Set (Op D.AppOp)) (s₀ s₁ s₂ t₁ : D.State) (e : Op D.AppOp),
      (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
      (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₁ → a ∈ ev₁) →
      (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₂ → a ∈ ev₂) →
      e ∈ ev₁ → e ∉ ev₂ →
      (∀ x ∈ ev₁ ∪ ev₂, x ≠ e → ¬ loOn C (ev₁ ∪ ev₂) e x) →
      IsCanonicalState C (ev₁ ∩ ev₂) s₀ →
      IsCanonicalState C ev₁ s₁ → IsCanonicalState C ev₂ s₂ →
      IsCanonicalState C (ev₁ \ {e}) t₁ →
      D.mergeL s₀ s₁ s₂ = D.update (D.mergeL s₀ t₁ s₂) e
  /-- Peel a union-maximal shared event from all three components. -/
  peel_shared3 :
    ∀ (C : Sal.Emulation.Configuration D.toCRDTSig)
      (ev₁ ev₂ : Set (Op D.AppOp)) (s₀ s₁ s₂ t₀ t₁ t₂ : D.State)
      (e : Op D.AppOp),
      (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
      (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₁ → a ∈ ev₁) →
      (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₂ → a ∈ ev₂) →
      e ∈ ev₁ → e ∈ ev₂ →
      (∀ x ∈ ev₁ ∪ ev₂, x ≠ e → ¬ loOn C (ev₁ ∪ ev₂) e x) →
      IsCanonicalState C (ev₁ ∩ ev₂) s₀ →
      IsCanonicalState C ev₁ s₁ → IsCanonicalState C ev₂ s₂ →
      IsCanonicalState C ((ev₁ ∩ ev₂) \ {e}) t₀ →
      IsCanonicalState C (ev₁ \ {e}) t₁ →
      IsCanonicalState C (ev₂ \ {e}) t₂ →
      D.mergeL s₀ s₁ s₂ = D.update (D.mergeL t₀ t₁ t₂) e

/-- **The ternary Join Lemma holds given the peel identities** — the master
induction (mission N3), the ternary lift of `join_lemma_of_peel`
(`Merge_Linearization_Set.lean:1359`). Same measure (`|l₁| + |l₂|`; the LCA
enumeration never enters it), same re-attachment (`isCanonicalState_snoc`,
reused), with the LCA event set threaded: invariant under a local peel, shrunk
in lock-step under a shared peel. Empty sides collapse via `mergeL_init`. -/
theorem join_lemma3_of_peel (hVC : CoreVCs3 D) (hPeel : JoinPeelVCs3 D) :
    JoinLemma3 D := by
  intro C ev₁ ev₂ s₀ s₁ s₂ h_vis_trans h_vis_irrefl h_in₁ h_in₂
    h_cl₁ h_cl₂ hc₀ hc₁ hc₂
  classical
  have hU := hVC.update_core
  obtain ⟨l₁, hp₁, hr₁, hf₁⟩ := hc₁
  obtain ⟨l₂, hp₂, hr₂, hf₂⟩ := hc₂
  suffices gen : ∀ n (ev₁ ev₂ : Set (Op D.AppOp)) (s₀ s₁ s₂ : D.State)
      (l₁ l₂ : List (Op D.AppOp)),
      l₁.length + l₂.length = n →
      (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
      (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₁ → a ∈ ev₁) →
      (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₂ → a ∈ ev₂) →
      IsCanonicalState C (ev₁ ∩ ev₂) s₀ →
      listPermOf l₁ ev₁ → respects l₁ (loOn C ev₁) →
      applySeq D.toCRDTSig D.init l₁ = s₁ →
      listPermOf l₂ ev₂ → respects l₂ (loOn C ev₂) →
      applySeq D.toCRDTSig D.init l₂ = s₂ →
      IsCanonicalState C (ev₁ ∪ ev₂) (D.mergeL s₀ s₁ s₂) by
    exact gen _ ev₁ ev₂ s₀ s₁ s₂ l₁ l₂ rfl h_in₁ h_in₂ h_cl₁ h_cl₂ hc₀
      hp₁ hr₁ hf₁ hp₂ hr₂ hf₂
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ev₁ ev₂ s₀ s₁ s₂ l₁ l₂ h_len h_in₁ h_in₂ h_cl₁ h_cl₂ hc₀
      hp₁ hr₁ hf₁ hp₂ hr₂ hf₂
    -- Empty sides collapse via mergeL_init.
    rcases Set.eq_empty_or_nonempty ev₁ with h_e₁ | h_ne₁
    · have hs₁ : s₁ = D.init :=
        isCanonicalState_empty h_e₁ ⟨l₁, hp₁, hr₁, hf₁⟩
      have h_int : ev₁ ∩ ev₂ = ∅ := by rw [h_e₁, Set.empty_inter]
      have hs₀ : s₀ = D.init := isCanonicalState_empty h_int hc₀
      subst h_e₁
      rw [hs₀, hs₁, hVC.mergeL_init, Set.empty_union]
      exact ⟨l₂, hp₂, hr₂, hf₂⟩
    rcases Set.eq_empty_or_nonempty ev₂ with h_e₂ | h_ne₂
    · have hs₂ : s₂ = D.init :=
        isCanonicalState_empty h_e₂ ⟨l₂, hp₂, hr₂, hf₂⟩
      have h_int : ev₁ ∩ ev₂ = ∅ := by rw [h_e₂, Set.inter_empty]
      have hs₀ : s₀ = D.init := isCanonicalState_empty h_int hc₀
      subst h_e₂
      rw [hs₀, hs₂, hVC.mergeL_comm, hVC.mergeL_init, Set.union_empty]
      exact ⟨l₁, hp₁, hr₁, hf₁⟩
    -- Select a loOn(∪)-maximal event.
    have h_inU : ∀ a ∈ ev₁ ∪ ev₂, a ∈ C.events := by
      rintro a (h | h)
      · exact h_in₁ a h
      · exact h_in₂ a h
    have hpU := listPermOf_union (D := D.toCRDTSig) hp₁ hp₂
    obtain ⟨x₁, hx₁⟩ := h_ne₁
    obtain ⟨e, he_U, h_max⟩ :=
      exists_loOn_maximal_u hU h_vis_trans h_vis_irrefl hpU h_inU
        ⟨x₁, Or.inl hx₁⟩
    by_cases he₁ : e ∈ ev₁
    · by_cases he₂ : e ∈ ev₂
      · -- Shared case: peel all three components.
        have h_e_l₁ : e ∈ l₁ := (hp₁.2 e).mpr he₁
        have h_e_l₂ : e ∈ l₂ := (hp₂.2 e).mpr he₂
        have hp₁' : listPermOf (l₁.filter (· ≠ e)) (ev₁ \ {e}) :=
          filter_ne_listPermOf hp₁ h_e_l₁
        have hp₂' : listPermOf (l₂.filter (· ≠ e)) (ev₂ \ {e}) :=
          filter_ne_listPermOf hp₂ h_e_l₂
        have hp₀ : listPermOf (l₁.filter (fun a => decide (a ∈ l₂)))
            (ev₁ ∩ ev₂) := listPermOf_inter hp₁ hp₂
        have h_e_l₀ : e ∈ l₁.filter (fun a => decide (a ∈ l₂)) :=
          (hp₀.2 e).mpr ⟨he₁, he₂⟩
        have hp₀' : listPermOf
            ((l₁.filter (fun a => decide (a ∈ l₂))).filter (· ≠ e))
            ((ev₁ ∩ ev₂) \ {e}) :=
          filter_ne_listPermOf hp₀ h_e_l₀
        obtain ⟨t₀, hct₀⟩ :=
          isCanonicalState_exists_u hU h_vis_trans h_vis_irrefl hp₀'
            (fun a ha => h_in₁ a ha.1.1)
        obtain ⟨t₁, hct₁⟩ :=
          isCanonicalState_exists_u hU h_vis_trans h_vis_irrefl hp₁'
            (fun a ha => h_in₁ a ha.1)
        obtain ⟨t₂, hct₂⟩ :=
          isCanonicalState_exists_u hU h_vis_trans h_vis_irrefl hp₂'
            (fun a ha => h_in₂ a ha.1)
        have h_eq := hPeel.peel_shared3 C ev₁ ev₂ s₀ s₁ s₂ t₀ t₁ t₂ e
          h_in₁ h_in₂ h_cl₁ h_cl₂ he₁ he₂ h_max hc₀
          ⟨l₁, hp₁, hr₁, hf₁⟩ ⟨l₂, hp₂, hr₂, hf₂⟩ hct₀ hct₁ hct₂
        obtain ⟨m₁, hm₁, hrm₁, hfm₁⟩ := hct₁
        obtain ⟨m₂, hm₂, hrm₂, hfm₂⟩ := hct₂
        have h_len₁ : m₁.length = l₁.length - 1 :=
          listPermOf_diff_length hp₁ h_e_l₁ hm₁
        have h_len₂ : m₂.length = l₂.length - 1 :=
          listPermOf_diff_length hp₂ h_e_l₂ hm₂
        have h_pos₁ : 0 < l₁.length := List.length_pos_of_mem h_e_l₁
        have h_pos₂ : 0 < l₂.length := List.length_pos_of_mem h_e_l₂
        have hc₀' : IsCanonicalState C ((ev₁ \ {e}) ∩ (ev₂ \ {e})) t₀ := by
          rw [diff_inter_diff]; exact hct₀
        have h_ih := ih (m₁.length + m₂.length) (by omega)
          (ev₁ \ {e}) (ev₂ \ {e}) t₀ t₁ t₂ m₁ m₂ rfl
          (fun a ha => h_in₁ a ha.1) (fun a ha => h_in₂ a ha.1)
          (closure_diff_of_max Set.subset_union_left h_cl₁ h_max)
          (closure_diff_of_max Set.subset_union_right h_cl₂ h_max)
          hc₀' hm₁ hrm₁ hfm₁ hm₂ hrm₂ hfm₂
        have h_set : (ev₁ \ {e}) ∪ (ev₂ \ {e}) = (ev₁ ∪ ev₂) \ {e} := by
          ext x
          simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff]
          tauto
        rw [h_set] at h_ih
        rw [h_eq]
        exact isCanonicalState_snoc (Or.inl he₁) h_max h_ih
      · -- Local to side 1: the LCA component is inert.
        have h_e_l₁ : e ∈ l₁ := (hp₁.2 e).mpr he₁
        have hp₁' : listPermOf (l₁.filter (· ≠ e)) (ev₁ \ {e}) :=
          filter_ne_listPermOf hp₁ h_e_l₁
        obtain ⟨t₁, hct₁⟩ :=
          isCanonicalState_exists_u hU h_vis_trans h_vis_irrefl hp₁'
            (fun a ha => h_in₁ a ha.1)
        have h_eq := hPeel.peel_local3 C ev₁ ev₂ s₀ s₁ s₂ t₁ e
          h_in₁ h_in₂ h_cl₁ h_cl₂ he₁ he₂ h_max hc₀
          ⟨l₁, hp₁, hr₁, hf₁⟩ ⟨l₂, hp₂, hr₂, hf₂⟩ hct₁
        obtain ⟨m₁, hm₁, hrm₁, hfm₁⟩ := hct₁
        have h_len₁ : m₁.length = l₁.length - 1 :=
          listPermOf_diff_length hp₁ h_e_l₁ hm₁
        have h_pos₁ : 0 < l₁.length := List.length_pos_of_mem h_e_l₁
        have hc₀' : IsCanonicalState C ((ev₁ \ {e}) ∩ ev₂) s₀ := by
          rw [inter_diff_left_of_not_mem he₂]; exact hc₀
        have h_ih := ih (m₁.length + l₂.length) (by omega)
          (ev₁ \ {e}) ev₂ s₀ t₁ s₂ m₁ l₂ rfl
          (fun a ha => h_in₁ a ha.1) h_in₂
          (closure_diff_of_max Set.subset_union_left h_cl₁ h_max)
          h_cl₂ hc₀' hm₁ hrm₁ hfm₁ hp₂ hr₂ hf₂
        have h_set : (ev₁ \ {e}) ∪ ev₂ = (ev₁ ∪ ev₂) \ {e} := by
          ext x
          simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff]
          constructor
          · rintro (⟨h, hne⟩ | h)
            · exact ⟨Or.inl h, hne⟩
            · exact ⟨Or.inr h, fun heq => he₂ (heq ▸ h)⟩
          · rintro ⟨h | h, hne⟩
            · exact Or.inl ⟨h, hne⟩
            · exact Or.inr h
        rw [h_set] at h_ih
        rw [h_eq]
        exact isCanonicalState_snoc (Or.inl he₁) h_max h_ih
    · -- Local to side 2: mirror via mergeL_comm.
      have he₂ : e ∈ ev₂ := by
        rcases he_U with h | h
        · exact absurd h he₁
        · exact h
      have h_e_l₂ : e ∈ l₂ := (hp₂.2 e).mpr he₂
      have hp₂' : listPermOf (l₂.filter (· ≠ e)) (ev₂ \ {e}) :=
        filter_ne_listPermOf hp₂ h_e_l₂
      obtain ⟨t₂, hct₂⟩ :=
        isCanonicalState_exists_u hU h_vis_trans h_vis_irrefl hp₂'
          (fun a ha => h_in₂ a ha.1)
      have h_max' : ∀ x ∈ ev₂ ∪ ev₁, x ≠ e →
          ¬ loOn C (ev₂ ∪ ev₁) e x := by
        rw [Set.union_comm]
        exact h_max
      have hc₀_swap : IsCanonicalState C (ev₂ ∩ ev₁) s₀ := by
        rw [Set.inter_comm]; exact hc₀
      have h_eq := hPeel.peel_local3 C ev₂ ev₁ s₀ s₂ s₁ t₂ e
        h_in₂ h_in₁ h_cl₂ h_cl₁ he₂ he₁ h_max' hc₀_swap
        ⟨l₂, hp₂, hr₂, hf₂⟩ ⟨l₁, hp₁, hr₁, hf₁⟩ hct₂
      obtain ⟨m₂, hm₂, hrm₂, hfm₂⟩ := hct₂
      have h_len₂ : m₂.length = l₂.length - 1 :=
        listPermOf_diff_length hp₂ h_e_l₂ hm₂
      have h_pos₂ : 0 < l₂.length := List.length_pos_of_mem h_e_l₂
      have hc₀' : IsCanonicalState C (ev₁ ∩ (ev₂ \ {e})) s₀ := by
        rw [inter_diff_right_of_not_mem he₁]; exact hc₀
      have h_ih := ih (l₁.length + m₂.length) (by omega)
        ev₁ (ev₂ \ {e}) s₀ s₁ t₂ l₁ m₂ rfl
        h_in₁ (fun a ha => h_in₂ a ha.1) h_cl₁
        (closure_diff_of_max Set.subset_union_right h_cl₂ h_max)
        hc₀' hp₁ hr₁ hf₁ hm₂ hrm₂ hfm₂
      have h_set : ev₁ ∪ (ev₂ \ {e}) = (ev₁ ∪ ev₂) \ {e} := by
        ext x
        simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff]
        constructor
        · rintro (h | ⟨h, hne⟩)
          · exact ⟨Or.inl h, fun heq => he₁ (heq ▸ h)⟩
          · exact ⟨Or.inr h, hne⟩
        · rintro ⟨h | h, hne⟩
          · exact Or.inl h
          · exact Or.inr ⟨h, hne⟩
      rw [h_set] at h_ih
      rw [hVC.mergeL_comm s₀ s₁ s₂, h_eq, hVC.mergeL_comm s₀ t₂ s₁]
      exact isCanonicalState_snoc (Or.inr he₂) h_max h_ih

/-! ## §C. The commuting class -/

/-- The peel bundle for the commuting class: with `loOn` edge-free, every
enumeration is canonical, the peeled event extracts from every component
(`applySeq_comm_extract`), and the two peels discharge from `merge_peel_comm3`
and `lem_0op3` respectively. Ternary lift of `joinPeelVCs_of_all_comm`
(`Merge_Linearization_Set.lean:1559`). -/
theorem joinPeelVCs3_of_all_comm (hVC : CoreVCs3 D)
    (h_comm : ∀ a b : Op D.AppOp, D.toCRDTSig.commutes a b) :
    JoinPeelVCs3 D := by
  have hU := hVC.update_core
  constructor
  · -- peel_local3
    intro C ev₁ ev₂ s₀ s₁ s₂ t₁ e h_in₁ h_in₂ _ _ he₁ _ _ hc₀ hc₁ hc₂ hct₁
    obtain ⟨l₀, hp₀, _, hf₀⟩ := hc₀
    obtain ⟨l₁, hp₁, _, hf₁⟩ := hc₁
    obtain ⟨l₂, _, _, hf₂⟩ := hc₂
    have h_e_l₁ : e ∈ l₁ := (hp₁.2 e).mpr he₁
    have h_ex := applySeq_comm_extract (D := D.toCRDTSig) h_e_l₁ hp₁.1
      (fun x _ _ => h_comm e x) D.init
    have hp₁' : listPermOf (l₁.filter (· ≠ e)) (ev₁ \ {e}) :=
      filter_ne_listPermOf hp₁ h_e_l₁
    have h_t₁ : applySeq D.toCRDTSig D.init (l₁.filter (· ≠ e)) = t₁ :=
      isCanonicalState_unique_u hU (fun a ha => h_in₁ a ha.1)
        (isCanonicalState_of_all_comm_u hU h_comm
          (fun a ha => h_in₁ a ha.1) hp₁') hct₁
    rw [← hf₀, ← hf₁, ← hf₂, h_ex, h_t₁]
    exact hVC.merge_peel_comm3 t₁ e l₀ l₂
      (fun x _ => h_comm e x) (fun x _ => h_comm e x)
  · -- peel_shared3
    intro C ev₁ ev₂ s₀ s₁ s₂ t₀ t₁ t₂ e h_in₁ h_in₂ _ _ he₁ he₂ _
      hc₀ hc₁ hc₂ hct₀ hct₁ hct₂
    obtain ⟨l₀, hp₀, _, hf₀⟩ := hc₀
    obtain ⟨l₁, hp₁, _, hf₁⟩ := hc₁
    obtain ⟨l₂, hp₂, _, hf₂⟩ := hc₂
    have h_e_l₀ : e ∈ l₀ := (hp₀.2 e).mpr ⟨he₁, he₂⟩
    have h_e_l₁ : e ∈ l₁ := (hp₁.2 e).mpr he₁
    have h_e_l₂ : e ∈ l₂ := (hp₂.2 e).mpr he₂
    have h_ex₀ := applySeq_comm_extract (D := D.toCRDTSig) h_e_l₀ hp₀.1
      (fun x _ _ => h_comm e x) D.init
    have h_ex₁ := applySeq_comm_extract (D := D.toCRDTSig) h_e_l₁ hp₁.1
      (fun x _ _ => h_comm e x) D.init
    have h_ex₂ := applySeq_comm_extract (D := D.toCRDTSig) h_e_l₂ hp₂.1
      (fun x _ _ => h_comm e x) D.init
    have hp₀' : listPermOf (l₀.filter (· ≠ e)) ((ev₁ ∩ ev₂) \ {e}) :=
      filter_ne_listPermOf hp₀ h_e_l₀
    have hp₁' : listPermOf (l₁.filter (· ≠ e)) (ev₁ \ {e}) :=
      filter_ne_listPermOf hp₁ h_e_l₁
    have hp₂' : listPermOf (l₂.filter (· ≠ e)) (ev₂ \ {e}) :=
      filter_ne_listPermOf hp₂ h_e_l₂
    have h_t₀ : applySeq D.toCRDTSig D.init (l₀.filter (· ≠ e)) = t₀ :=
      isCanonicalState_unique_u hU (fun a ha => h_in₁ a ha.1.1)
        (isCanonicalState_of_all_comm_u hU h_comm
          (fun a ha => h_in₁ a ha.1.1) hp₀') hct₀
    have h_t₁ : applySeq D.toCRDTSig D.init (l₁.filter (· ≠ e)) = t₁ :=
      isCanonicalState_unique_u hU (fun a ha => h_in₁ a ha.1)
        (isCanonicalState_of_all_comm_u hU h_comm
          (fun a ha => h_in₁ a ha.1) hp₁') hct₁
    have h_t₂ : applySeq D.toCRDTSig D.init (l₂.filter (· ≠ e)) = t₂ :=
      isCanonicalState_unique_u hU (fun a ha => h_in₂ a ha.1)
        (isCanonicalState_of_all_comm_u hU h_comm
          (fun a ha => h_in₂ a ha.1) hp₂') hct₂
    rw [← hf₀, ← hf₁, ← hf₂, h_ex₀, h_ex₁, h_ex₂, h_t₀, h_t₁, h_t₂]
    exact hVC.lem_0op3 t₀ t₁ t₂ e

/-- **The ternary Join Lemma, unconditionally, for the commuting class.** -/
theorem join_lemma3_of_all_comm (hVC : CoreVCs3 D)
    (h_comm : ∀ a b : Op D.AppOp, D.toCRDTSig.commutes a b) : JoinLemma3 D :=
  join_lemma3_of_peel hVC (joinPeelVCs3_of_all_comm hVC h_comm)

end

/-- **The ternary Join Lemma for G-Set.** -/
theorem GSet_joinLemma3 : JoinLemma3 GSetCond :=
  join_lemma3_of_all_comm GSet_coreVCs3 GSet_all_comm

/-- **The ternary Join Lemma for the counter.** -/
theorem Counter_joinLemma3 : JoinLemma3 Counter :=
  join_lemma3_of_all_comm Counter_coreVCs3 Counter_all_comm

open LabeledTS in
/-- **The ternary bridge theorem** (mission N5, the ternary analog of FINDINGS A9's
`ra_linearizable_of_core_join`): for an MRDT satisfying the ternary core bundle
and the ternary peel identities, every reachable configuration of the ternary
system is RA-linearizable, per version. -/
theorem ra_linearizable_of_core_join3
    (hVC : CoreVCs3 D) (hPeel : JoinPeelVCs3 D)
    {hInit : D.Inv D.init}
    (C : Configuration D)
    (hReach : (labeledTS3 D).ReachableFrom (initConfig D hInit) C) :
    IsRALinearizable3 C := by
  have hJoin : JoinLemma3 D := join_lemma3_of_peel hVC hPeel
  suffices h : GoodConfig3 C from isRALinearizable3_of_good h
  induction hReach with
  | refl => exact goodConfig3_init hInit
  | tail _ hs ih =>
    obtain ⟨ℓ, hstep⟩ := hs
    cases hstep with
    | createReplica h_fresh C' hN hL hvis hver hhead hparents =>
      exact goodConfig3_createReplica h_fresh hL hvis hver ih
    | apply h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank C'
        hN hL hvis hver hhead hparents =>
      exact goodConfig3_apply h_head h_ver h_fresh_t h_vnew hL hvis hver ih
    | merge h_head₁ h_head₂ h_ver₁ h_ver₂ h_lca h_verT h_vm h_rank₁ h_rank₂ C'
        hN hL hvis hver hhead hparents =>
      exact goodConfig3_merge hJoin h_head₁ h_ver₁ h_ver₂ h_lca h_verT
        hL hvis hver ih
    | query h_s h_val => exact ih

/-! ## Corollaries: end-to-end for the two §D instances -/

open LabeledTS in
/-- End-to-end RA-linearizability for the G-Set MRDT. -/
theorem gset_ra_linearizable3
    (C : Configuration GSetCond)
    (hReach : (labeledTS3 GSetCond).ReachableFrom
      (initConfig GSetCond trivial) C) :
    IsRALinearizable3 C :=
  ra_linearizable_of_core_join3 GSet_coreVCs3
    (joinPeelVCs3_of_all_comm GSet_coreVCs3 GSet_all_comm) C hReach

open LabeledTS in
/-- End-to-end RA-linearizability for the **counter** MRDT — an MRDT the binary
metatheorem provably cannot host (`Counter_binary_lem_0op_false`): the first
end-to-end instance in this development where the LCA argument of `merge` is
mathematically load-bearing. -/
theorem counter_ra_linearizable3
    (C : Configuration Counter)
    (hReach : (labeledTS3 Counter).ReachableFrom
      (initConfig Counter trivial) C) :
    IsRALinearizable3 C :=
  ra_linearizable_of_core_join3 Counter_coreVCs3
    (joinPeelVCs3_of_all_comm Counter_coreVCs3 Counter_all_comm) C hReach


end Sal.ConditionedMRDTs
