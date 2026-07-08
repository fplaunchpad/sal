import Sal.CRDTs.Metatheory.Merge_Linearization_Set
import Sal.ConditionedMRDTs.Framework.ExecutionModel

/-!
# The σ/`loOn` layer for the ternary setting

The set-relative linearization machinery of the binary development
(`Sal/CRDTs/Metatheory/Merge_Linearization_Set.lean`), re-hosted on the
merge-free **guarded** `UpdateVCs` fragment (three fields: guarded
`rc_non_comm_directional` — the `differentReplicas` guard is the paper's own
F* interface form — `no_rc_chain`, `cond_comm_lift`), plus the **core
projection**: the ternary `Configuration`'s replica-keyed core *is* a binary
`Emulation.Configuration`, so `loOn`/`IsCanonicalState`/`convergence_on` and
friends are reused, not re-proved. See `Development/MRDT_METATHEORY_DRAFT.md`
(T4, T9.3, T10.2) for why the merge-shaped fields of the historical
`CoreVCs3` cannot be demanded of real MRDTs.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

/-! ## §A. The update-layer VC fragment, and the σ-machinery re-hosted on it -/

section UpdateLayer
variable {D : CRDTSig}

/-- The three update-layer fields of the 2-way `CoreVCs` — the exact fragment the
`loOn`/convergence/canonical-state machinery consumes. An MRDT's `CoreVCs3` (§B)
supplies these unchanged; the binary *merge* fields of `CoreVCs` are deliberately NOT
required (they are false for LCA-sensitive MRDTs such as the counter, §D). -/
structure UpdateVCs (D : CRDTSig) : Prop where
  rc_non_comm_directional :
    ∀ o₁ o₂ : Op D.AppOp,
      distinctOps o₁ o₂ → differentReplicas o₁ o₂ →
      (¬ D.commutes o₁ o₂ ↔
       (D.rc o₁ o₂ = RcRes.Fst_then_snd ∨
        D.rc o₂ o₁ = RcRes.Fst_then_snd))
  no_rc_chain :
    ∀ o₁ o₂ o₃ : Op D.AppOp,
      distinctOps o₁ o₂ → distinctOps o₂ o₃ →
      ¬ (D.rc o₁ o₂ = RcRes.Fst_then_snd ∧
         D.rc o₂ o₃ = RcRes.Fst_then_snd)
  cond_comm_lift :
    ∀ (s : D.State) (e e' e'' : Op D.AppOp) (π : List (Op D.AppOp)),
      distinctOps e e' → distinctOps e e'' → distinctOps e' e'' →
      D.rc e e' = RcRes.Fst_then_snd →
      ¬ D.commutes e' e'' →
      D.update (applySeq D (D.update (D.update s e') e) π) e''
        = D.update (applySeq D (D.update (D.update s e) e') π) e''

/-- The slim bundle from the full 2-way core. -/
theorem UpdateVCs.of_core (hVC : CoreVCs D) : UpdateVCs D :=
  ⟨fun o₁ o₂ hd _ => hVC.rc_non_comm_directional o₁ o₂ hd,
   hVC.no_rc_chain, hVC.cond_comm_lift⟩

/-- Verbatim `Merge_Linearization_Set.lean:128` (`applySeq_swap_via_cond_comm_lift_core`)
with `CoreVCs` slimmed to `UpdateVCs`. -/
theorem applySeq_swap_via_cond_comm_lift_u
    (hU : UpdateVCs D)
    {a b e₃ : Op D.AppOp}
    (h_dist_ab : distinctOps a b)
    (h_dist_be : distinctOps b e₃)
    (h_dist_ae : distinctOps a e₃)
    (h_rc_ab : D.rc a b = RcRes.Fst_then_snd)
    (h_nc_be : ¬ D.commutes b e₃)
    (pfx α β : List (Op D.AppOp)) (s : D.State) :
    applySeq D s (pfx ++ a :: b :: (α ++ e₃ :: β))
    = applySeq D s (pfx ++ b :: a :: (α ++ e₃ :: β)) := by
  have hexp1 : applySeq D s (pfx ++ a :: b :: (α ++ e₃ :: β))
             = applySeq D (D.update (applySeq D
                 (D.update (D.update (applySeq D s pfx) a) b) α) e₃) β := by
    simp [applySeq, List.foldl_append, List.foldl_cons]
  have hexp2 : applySeq D s (pfx ++ b :: a :: (α ++ e₃ :: β))
             = applySeq D (D.update (applySeq D
                 (D.update (D.update (applySeq D s pfx) b) a) α) e₃) β := by
    simp [applySeq, List.foldl_append, List.foldl_cons]
  rw [hexp1, hexp2]
  exact congrArg (fun t => applySeq D t β)
    (hU.cond_comm_lift (applySeq D s pfx) a b e₃ α
      h_dist_ab h_dist_ae h_dist_be h_rc_ab h_nc_be).symm

/-- Verbatim `Merge_Linearization_Set.lean:255` (`loOn_rc_no_succ`). -/
theorem loOn_rc_no_succ_u (hU : UpdateVCs D)
    {C : Sal.Emulation.Configuration D}
    {T : Set (Op D.AppOp)}
    (h_in_C : ∀ a ∈ T, a ∈ C.events)
    {x y z : Op D.AppOp}
    (hxy_ne : x ≠ y) (hyz_ne : y ≠ z)
    (hx : x ∈ T) (hy : y ∈ T) (hz : z ∈ T)
    (h_rc_edge : ¬ C.vis x y ∧ ¬ C.vis y x
      ∧ D.rc x y = RcRes.Fst_then_snd
      ∧ ¬ ∃ e₃ ∈ T, C.vis y e₃ ∧ ¬ D.commutes y e₃)
    (h_edge : loOn C T y z) : False := by
  obtain ⟨_, _, h_rc, h_no_abs⟩ := h_rc_edge
  rcases h_edge with ⟨hv, hnc⟩ | ⟨_, _, h_rc', _⟩
  · exact h_no_abs ⟨z, hz, hv, hnc⟩
  · exact hU.no_rc_chain x y z
      (distinctOps_of_events (h_in_C x hx) (h_in_C y hy) hxy_ne)
      (distinctOps_of_events (h_in_C y hy) (h_in_C z hz) hyz_ne)
      ⟨h_rc, h_rc'⟩

/-- Verbatim `Merge_Linearization_Set.lean:276` (`transGen_loOnNe_structure`). -/
theorem transGen_loOnNe_structure_u (hU : UpdateVCs D)
    {C : Sal.Emulation.Configuration D}
    (h_vis_trans : ∀ {a b c : Op D.AppOp},
       C.vis a b → C.vis b c → C.vis a c)
    {T : Set (Op D.AppOp)}
    (h_in_C : ∀ a ∈ T, a ∈ C.events)
    {a b : Op D.AppOp}
    (h : Relation.TransGen (loOnNe C T) a b) :
    C.vis a b ∨
    (∃ x, x ≠ b ∧ x ∈ T ∧
      (¬ C.vis x b ∧ ¬ C.vis b x
        ∧ D.rc x b = RcRes.Fst_then_snd
        ∧ ¬ ∃ e₃ ∈ T, C.vis b e₃ ∧ ¬ D.commutes b e₃)) := by
  induction h with
  | single h_edge =>
    obtain ⟨hne, hxT, hyT, h_lo⟩ := h_edge
    rcases h_lo with ⟨hv, _⟩ | h_rc
    · exact Or.inl hv
    · exact Or.inr ⟨a, hne, hxT, h_rc⟩
  | tail _ h_edge ih =>
    rename_i mid c h_path
    obtain ⟨hne, hmidT, hcT, h_lo⟩ := h_edge
    rcases ih with h_vis_amid | ⟨x, hx_ne, hxT, h_rc_edge⟩
    · rcases h_lo with ⟨hv, _⟩ | h_rc
      · exact Or.inl (h_vis_trans h_vis_amid hv)
      · exact Or.inr ⟨mid, hne, hmidT, h_rc⟩
    · exact absurd h_lo
        (fun h => loOn_rc_no_succ_u hU h_in_C hx_ne hne hxT hmidT hcT
          h_rc_edge h)

/-- Verbatim `Merge_Linearization_Set.lean:307` (`loOnNe_acyclic`). -/
theorem loOnNe_acyclic_u (hU : UpdateVCs D)
    {C : Sal.Emulation.Configuration D}
    (h_vis_trans : ∀ {a b c : Op D.AppOp},
       C.vis a b → C.vis b c → C.vis a c)
    (h_vis_irrefl : ∀ a : Op D.AppOp, ¬ C.vis a a)
    {T : Set (Op D.AppOp)}
    (h_in_C : ∀ a ∈ T, a ∈ C.events)
    (a : Op D.AppOp) :
    ¬ Relation.TransGen (loOnNe C T) a a := by
  intro h_cycle
  rcases transGen_loOnNe_structure_u hU h_vis_trans h_in_C h_cycle with
    h_vis | ⟨x, hx_ne, hxT, h_rc_edge⟩
  · exact h_vis_irrefl a h_vis
  · have h_head : ∀ {p q : Op D.AppOp},
        Relation.TransGen (loOnNe C T) p q →
        ∃ c, loOnNe C T p c := by
      intro p q h
      induction h with
      | single h => exact ⟨_, h⟩
      | tail _ _ ih => exact ih
    obtain ⟨c, hac_ne, haT, hcT, h_lo⟩ := h_head h_cycle
    exact loOn_rc_no_succ_u hU h_in_C hx_ne hac_ne hxT haT hcT
      h_rc_edge h_lo

/-- Verbatim `Merge_Linearization_Set.lean:342` (`exists_loOn_maximal`). -/
theorem exists_loOn_maximal_u (hU : UpdateVCs D)
    {C : Sal.Emulation.Configuration D}
    (h_vis_trans : ∀ {a b c : Op D.AppOp},
       C.vis a b → C.vis b c → C.vis a c)
    (h_vis_irrefl : ∀ a : Op D.AppOp, ¬ C.vis a a)
    {T : Set (Op D.AppOp)} {l : List (Op D.AppOp)}
    (h_l : listPermOf l T)
    (h_in_C : ∀ a ∈ T, a ∈ C.events)
    (h_ne : T.Nonempty) :
    ∃ e ∈ T, ∀ x ∈ T, x ≠ e → ¬ loOn C T e x := by
  suffices walk : ∀ n (rem : List (Op D.AppOp)), rem.length = n →
      rem.Nodup →
      ∀ cur ∈ T,
      (∀ x ∈ T, x ∉ rem → x ≠ cur →
        Relation.TransGen (loOnNe C T) x cur) →
      ∃ e ∈ T, ∀ x ∈ T, x ≠ e → ¬ loOn C T e x by
    obtain ⟨t₀, ht₀⟩ := h_ne
    exact walk l.length l rfl h_l.1 t₀ ht₀
      (fun x hx hx_not_l _ => absurd ((h_l.2 x).mpr hx) hx_not_l)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro rem h_len h_nodup cur h_cur h_reach
    by_cases h_max : ∃ x ∈ T, x ≠ cur ∧ loOn C T cur x
    · obtain ⟨x, hx_T, hx_ne, h_edge⟩ := h_max
      have h_edge_ne : loOnNe C T cur x :=
        ⟨fun h => hx_ne h.symm, h_cur, hx_T, h_edge⟩
      by_cases hx_rem : x ∈ rem
      · have h_len' : (rem.erase x).length < n := by
          have h_pos : 0 < rem.length := List.length_pos_of_mem hx_rem
          rw [List.length_erase_of_mem hx_rem]
          omega
        refine ih _ h_len' (rem.erase x) rfl (h_nodup.erase x)
          x hx_T ?_
        intro y hy_T hy_not hy_ne
        by_cases hy_cur : y = cur
        · subst hy_cur
          exact Relation.TransGen.single h_edge_ne
        · have hy_not_rem : y ∉ rem := fun h_in =>
            hy_not (h_nodup.mem_erase_iff.mpr ⟨hy_ne, h_in⟩)
          exact (h_reach y hy_T hy_not_rem hy_cur).tail h_edge_ne
      · exfalso
        have h_x_reaches_cur : Relation.TransGen (loOnNe C T) x cur :=
          h_reach x hx_T hx_rem hx_ne
        exact loOnNe_acyclic_u hU h_vis_trans h_vis_irrefl h_in_C x
          (h_x_reaches_cur.tail h_edge_ne)
    · push_neg at h_max
      exact ⟨cur, h_cur, fun x hx hx_ne h_lo =>
        (h_max x hx hx_ne) h_lo⟩

/-- Verbatim `Merge_Linearization_Set.lean:398` (`exists_loOn_respecting_perm`). -/
theorem exists_loOn_respecting_perm_u (hU : UpdateVCs D)
    {C : Sal.Emulation.Configuration D}
    (h_vis_trans : ∀ {a b c : Op D.AppOp},
       C.vis a b → C.vis b c → C.vis a c)
    (h_vis_irrefl : ∀ a : Op D.AppOp, ¬ C.vis a a)
    {T : Set (Op D.AppOp)} {l : List (Op D.AppOp)}
    (h_l : listPermOf l T)
    (h_in_C : ∀ a ∈ T, a ∈ C.events) :
    ∃ ρ : List (Op D.AppOp),
      listPermOf ρ T ∧ respects ρ (loOn C T) := by
  suffices gen : ∀ n (T : Set (Op D.AppOp)) (l : List (Op D.AppOp)),
      l.length = n → listPermOf l T → (∀ a ∈ T, a ∈ C.events) →
      ∃ ρ, listPermOf ρ T ∧ respects ρ (loOn C T) by
    exact gen _ T l rfl h_l h_in_C
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T l h_len h_perm h_in_C
    rcases Set.eq_empty_or_nonempty T with rfl | h_ne
    · exact ⟨[], ⟨List.nodup_nil, fun a => by simp⟩, List.Pairwise.nil⟩
    · obtain ⟨m, hm, h_max⟩ :=
        exists_loOn_maximal_u hU h_vis_trans h_vis_irrefl h_perm
          h_in_C h_ne
      have hm_in_l : m ∈ l := (h_perm.2 m).mpr hm
      have h_perm' : listPermOf (l.erase m) (T \ {m}) := by
        refine ⟨h_perm.1.erase m, fun a => ?_⟩
        rw [h_perm.1.mem_erase_iff]
        constructor
        · rintro ⟨hne, ha⟩
          exact ⟨(h_perm.2 a).mp ha, hne⟩
        · rintro ⟨ha, hne⟩
          exact ⟨hne, (h_perm.2 a).mpr ha⟩
      have h_len' : (l.erase m).length < n := by
        have h_pos : 0 < l.length := List.length_pos_of_mem hm_in_l
        rw [List.length_erase_of_mem hm_in_l]
        omega
      obtain ⟨ρ', hρ'_perm, hρ'_resp⟩ :=
        ih _ h_len' (T \ {m}) (l.erase m) rfl h_perm'
          (fun a ha => h_in_C a ha.1)
      have hm_not_ρ' : m ∉ ρ' := fun h =>
        ((hρ'_perm.2 m).mp h).2 rfl
      refine ⟨ρ' ++ [m], ⟨?_, fun a => ?_⟩, ?_⟩
      · rw [List.nodup_append]
        refine ⟨hρ'_perm.1, List.nodup_singleton _, ?_⟩
        intro x hx y hy
        rw [List.mem_singleton] at hy; subst hy
        intro heq; subst heq
        exact hm_not_ρ' hx
      · rw [List.mem_append, List.mem_singleton]
        constructor
        · rintro (h | rfl)
          · exact ((hρ'_perm.2 a).mp h).1
          · exact hm
        · intro ha
          by_cases hae : a = m
          · exact Or.inr hae
          · exact Or.inl ((hρ'_perm.2 a).mpr ⟨ha, hae⟩)
      · unfold respects
        rw [List.pairwise_append]
        refine ⟨respects_loOn_mono (fun a ha => ha.1) hρ'_resp,
          List.pairwise_singleton _ _, ?_⟩
        intro y hy b hb
        rw [List.mem_singleton] at hb; subst hb
        obtain ⟨hy_T, hy_ne⟩ := (hρ'_perm.2 y).mp hy
        exact h_max y hy_T hy_ne

/-- Verbatim `Merge_Linearization_Set.lean:472` (`applySeq_swap_loOn_incomparable`). -/
theorem applySeq_swap_loOn_incomparable_u
    (hU : UpdateVCs D) {C : Sal.Emulation.Configuration D}
    {ev : Set (Op D.AppOp)}
    {a b : Op D.AppOp} (h_ne : a ≠ b)
    (h_a_in_C : a ∈ C.events) (h_b_in_C : b ∈ C.events)
    (h_not_lo_ab : ¬ loOn C ev a b) (h_not_lo_ba : ¬ loOn C ev b a)
    (pfx sfx : List (Op D.AppOp)) (s : D.State)
    (h_ov : ¬ D.commutes a b → a.rep ≠ b.rep →
      ∃ e₃ α β, sfx = α ++ e₃ :: β ∧
                distinctOps a e₃ ∧ distinctOps b e₃ ∧
                ((D.rc a b = RcRes.Fst_then_snd ∧
                  ¬ D.commutes b e₃) ∨
                 (D.rc b a = RcRes.Fst_then_snd ∧
                  ¬ D.commutes a e₃))) :
    applySeq D s (pfx ++ a :: b :: sfx)
    = applySeq D s (pfx ++ b :: a :: sfx) := by
  by_cases h_comm : D.commutes a b
  · exact applySeq_swap_commute h_comm pfx sfx s
  · obtain ⟨_, _, hL_a, h_a_in_s⟩ := h_a_in_C
    obtain ⟨_, _, hL_b, h_b_in_s⟩ := h_b_in_C
    by_cases h_same : a.rep = b.rep
    · exfalso
      have h_vis :=
        C.vis_total_same_replica hL_a h_a_in_s hL_b h_b_in_s h_ne h_same
      rcases h_vis with hvab | hvba
      · exact h_not_lo_ab (Or.inl ⟨hvab, h_comm⟩)
      · have h_comm_ba : ¬ D.commutes b a :=
          fun h => h_comm (fun s => (h s).symm)
        exact h_not_lo_ba (Or.inl ⟨hvba, h_comm_ba⟩)
    · have h_dist_ab : distinctOps a b :=
        C.timestamps_distinct hL_a h_a_in_s hL_b h_b_in_s h_ne
      obtain ⟨e₃, α, β, h_sfx, h_dae, h_dbe, h_case⟩ := h_ov h_comm h_same
      subst h_sfx
      rcases h_case with ⟨h_rc_ab, h_nc_be⟩ | ⟨h_rc_ba, h_nc_ae⟩
      · exact applySeq_swap_via_cond_comm_lift_u hU h_dist_ab h_dbe h_dae
          h_rc_ab h_nc_be pfx α β s
      · have h_dist_ba : distinctOps b a := Ne.symm h_dist_ab
        exact (applySeq_swap_via_cond_comm_lift_u hU h_dist_ba h_dae h_dbe
          h_rc_ba h_nc_ae pfx α β s).symm

/-- Verbatim `Merge_Linearization_Set.lean:513` (`applySeq_bubble_to_front_loOn`). -/
theorem applySeq_bubble_to_front_loOn_u
    (hU : UpdateVCs D) {C : Sal.Emulation.Configuration D}
    {ev : Set (Op D.AppOp)}
    (e : Op D.AppOp) (σ tail : List (Op D.AppOp))
    (h_e_in_C : e ∈ C.events)
    (h_σ_in_C : ∀ y ∈ σ, y ∈ C.events)
    (h_e_notin : e ∉ σ)
    (h_not_lo_fwd : ∀ y ∈ σ, ¬ loOn C ev e y)
    (h_not_lo_bwd : ∀ y ∈ σ, ¬ loOn C ev y e)
    (h_ov : ∀ α β y, σ = α ++ y :: β →
      ¬ D.commutes y e → y.rep ≠ e.rep →
      ∃ e₃ α' β', β ++ tail = α' ++ e₃ :: β' ∧
                  distinctOps y e₃ ∧ distinctOps e e₃ ∧
                  ((D.rc y e = RcRes.Fst_then_snd ∧
                    ¬ D.commutes e e₃) ∨
                   (D.rc e y = RcRes.Fst_then_snd ∧
                    ¬ D.commutes y e₃)))
    (s : D.State) :
    applySeq D s (σ ++ e :: tail) = applySeq D s (e :: σ ++ tail) := by
  induction σ generalizing s with
  | nil => rfl
  | cons y σ' ih =>
    have h_y_in : y ∈ y :: σ' := List.mem_cons_self
    have h_y_ne : y ≠ e := fun heq => h_e_notin (heq ▸ h_y_in)
    have h_y_in_C := h_σ_in_C y h_y_in
    have hih : applySeq D (D.update s y) (σ' ++ e :: tail)
             = applySeq D (D.update s y) (e :: σ' ++ tail) :=
      ih (fun z hz => h_σ_in_C z (List.mem_cons_of_mem _ hz))
         (fun h => h_e_notin (List.mem_cons_of_mem _ h))
         (fun z hz => h_not_lo_fwd z (List.mem_cons_of_mem _ hz))
         (fun z hz => h_not_lo_bwd z (List.mem_cons_of_mem _ hz))
         (fun α β z h_eq h_nc h_diff =>
            h_ov (y :: α) β z (by rw [h_eq]; rfl) h_nc h_diff)
         (D.update s y)
    have hswap : applySeq D s (y :: e :: σ' ++ tail)
               = applySeq D s (e :: y :: σ' ++ tail) := by
      have := applySeq_swap_loOn_incomparable_u (D := D) (ev := ev)
        hU h_y_ne h_y_in_C h_e_in_C
        (h_not_lo_bwd y h_y_in) (h_not_lo_fwd y h_y_in)
        [] (σ' ++ tail) s
        (fun h_nc h_diff => h_ov [] σ' y rfl h_nc h_diff)
      simpa using this
    show applySeq D (D.update s y) (σ' ++ e :: tail)
         = applySeq D s (e :: y :: σ' ++ tail)
    rw [hih]
    show applySeq D s (y :: e :: σ' ++ tail)
         = applySeq D s (e :: y :: σ' ++ tail)
    exact hswap

/-- Verbatim `Merge_Linearization_Set.lean:577` (`convergence_on`): two
`loOn C ev`-respecting permutations of `ev` fold to the same state — no closure
hypotheses. -/
theorem convergence_on_u
    (hU : UpdateVCs D) {C : Sal.Emulation.Configuration D}
    (s : D.State) {π₁ π₂ : List (Op D.AppOp)} {ev : Set (Op D.AppOp)}
    (h_ev_in_C : ∀ a ∈ ev, a ∈ C.events)
    (h₁_perm : listPermOf π₁ ev) (h₂_perm : listPermOf π₂ ev)
    (h₁_resp : respects π₁ (loOn C ev))
    (h₂_resp : respects π₂ (loOn C ev)) :
    applySeq D s π₁ = applySeq D s π₂ := by
  suffices gen : ∀ n (s : D.State) (evC : Set (Op D.AppOp))
                   (π₁ π₂ : List (Op D.AppOp)),
      π₁.length = n →
      (∀ a ∈ evC, a ∈ C.events) →
      (∀ x ∈ evC, ∀ z ∈ ev, C.vis x z → ¬ D.commutes x z → z ∈ evC) →
      listPermOf π₁ evC → listPermOf π₂ evC →
      respects π₁ (loOn C ev) → respects π₂ (loOn C ev) →
      applySeq D s π₁ = applySeq D s π₂ by
    exact gen _ s ev π₁ π₂ rfl h_ev_in_C
      (fun x _ z hz _ _ => hz) h₁_perm h₂_perm h₁_resp h₂_resp
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s evC π₁ π₂ h_len h_evC_in_C h_abs h₁p h₂p h₁r h₂r
    match π₁, h_len, h₁p, h₁r with
    | [], _, h₁p, _ =>
      obtain ⟨_, hm₁⟩ := h₁p
      have hev_empty : evC = ∅ := by
        ext a
        exact ⟨fun ha => absurd ((hm₁ a).mpr ha) List.not_mem_nil,
               fun ha => ha.elim⟩
      subst hev_empty
      obtain ⟨_, hm₂⟩ := h₂p
      have hπ₂_nil : π₂ = [] := by
        match π₂, hm₂ with
        | [], _ => rfl
        | x :: _, hm₂ =>
          exact absurd ((hm₂ x).mp List.mem_cons_self) id
      subst hπ₂_nil
      rfl
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
      have he_notin_σ : e ∉ σ := fun h =>
        hnd₂.2.2 e h e (by simp) rfl
      have he_notin_τ : e ∉ τ := hnd₂.2.1.1
      have hστ_nodup : (σ ++ τ).Nodup := by
        rw [List.nodup_append]
        refine ⟨hnd₂.1, hnd₂.2.1.2, ?_⟩
        intro a ha b hb
        exact hnd₂.2.2 a ha b (List.mem_cons_of_mem _ hb)
      have he_in_C : e ∈ C.events := h_evC_in_C e he_in_ev
      have h_e_lo_min : ∀ z ∈ evC, z ≠ e → ¬ loOn C ev z e := by
        intro z hz hz_ne
        have hz_in_π₁ : z ∈ e :: π₁' := (hmem₁ z).mpr hz
        have hz_in_π₁' : z ∈ π₁' := by
          rcases List.mem_cons.mp hz_in_π₁ with h | h
          · exact absurd h hz_ne
          · exact h
        exact (List.pairwise_cons.mp h₁r).1 z hz_in_π₁'
      have hbubble : applySeq D s (σ ++ e :: τ)
                   = applySeq D s (e :: σ ++ τ) := by
        have h_σ_sub_ev : ∀ y ∈ σ, y ∈ evC := fun y hy =>
          (hmem₂ y).mp (List.mem_append.mpr (Or.inl hy))
        have h_σ_in_C : ∀ y ∈ σ, y ∈ C.events :=
          fun y hy => h_evC_in_C y (h_σ_sub_ev y hy)
        have h_τ_sub_ev : ∀ x ∈ τ, x ∈ evC := fun x hx =>
          (hmem₂ x).mp (List.mem_append.mpr (Or.inr
            (List.mem_cons_of_mem _ hx)))
        have h_not_lo_fwd : ∀ y ∈ σ, ¬ loOn C ev e y := by
          intro y hy
          have h2 := List.pairwise_append.mp h₂r
          exact h2.2.2 y hy e List.mem_cons_self
        have h_not_lo_bwd : ∀ y ∈ σ, ¬ loOn C ev y e := by
          intro y hy
          have hy_ne_e : y ≠ e := fun h => he_notin_σ (h ▸ hy)
          exact h_e_lo_min y (h_σ_sub_ev y hy) hy_ne_e
        have h_ov : ∀ α β y, σ = α ++ y :: β →
            ¬ D.commutes y e → y.rep ≠ e.rep →
            ∃ e₃ α' β', β ++ τ = α' ++ e₃ :: β' ∧
                        distinctOps y e₃ ∧ distinctOps e e₃ ∧
                        ((D.rc y e = RcRes.Fst_then_snd ∧
                          ¬ D.commutes e e₃) ∨
                         (D.rc e y = RcRes.Fst_then_snd ∧
                          ¬ D.commutes y e₃)) := by
          intro α β y h_σ_eq h_nc h_diff_rep
          subst h_σ_eq
          have hy_in_σ : y ∈ α ++ y :: β :=
            List.mem_append.mpr (Or.inr List.mem_cons_self)
          have hy_in_ev : y ∈ evC := h_σ_sub_ev y hy_in_σ
          have hy_in_C : y ∈ C.events := h_evC_in_C y hy_in_ev
          have hy_ne_e : y ≠ e := fun h => he_notin_σ (h ▸ hy_in_σ)
          have h_dist_ye : distinctOps y e :=
            distinctOps_of_events hy_in_C he_in_C hy_ne_e
          have h_not_lo_ye : ¬ loOn C ev y e := h_not_lo_bwd y hy_in_σ
          have h_not_lo_ey : ¬ loOn C ev e y := h_not_lo_fwd y hy_in_σ
          have h_rc_disj :=
            (hU.rc_non_comm_directional y e h_dist_ye h_diff_rep).mp h_nc
          rcases h_rc_disj with h_rc_ye | h_rc_ey
          · have h_not_vis_ye : ¬ C.vis y e := fun hv =>
              h_not_lo_ye (Or.inl ⟨hv, h_nc⟩)
            have h_not_vis_ey : ¬ C.vis e y := by
              intro hv
              have h_nc_ey : ¬ D.commutes e y :=
                fun h => h_nc (fun s => (h s).symm)
              exact h_not_lo_ey (Or.inl ⟨hv, h_nc_ey⟩)
            have h_overwriter_e :
                ∃ e₃ ∈ ev, C.vis e e₃ ∧ ¬ D.commutes e e₃ := by
              by_contra h_no_ow
              exact h_not_lo_ye
                (Or.inr ⟨h_not_vis_ye, h_not_vis_ey, h_rc_ye, h_no_ow⟩)
            obtain ⟨e₃, h_e₃_ev, h_vis_ee₃, h_nc_ee₃⟩ := h_overwriter_e
            have h_e₃_in_evC : e₃ ∈ evC :=
              h_abs e he_in_ev e₃ h_e₃_ev h_vis_ee₃ h_nc_ee₃
            have h_e₃_in_π₂ : e₃ ∈ (α ++ y :: β) ++ e :: τ :=
              (hmem₂ e₃).mpr h_e₃_in_evC
            have h_lo_ee₃ : loOn C ev e e₃ := Or.inl ⟨h_vis_ee₃, h_nc_ee₃⟩
            have h_e₃_in_τ : e₃ ∈ τ := by
              rcases List.mem_append.mp h_e₃_in_π₂ with h | h
              · exfalso
                have hresp_pair := List.pairwise_append.mp h₂r
                exact hresp_pair.2.2 e₃ h e List.mem_cons_self h_lo_ee₃
              · rcases List.mem_cons.mp h with h_eq | h_τ
                · exact absurd h_eq.symm
                    (fun h_eq2 => h_nc_ee₃ (fun s => by rw [h_eq2]))
                · exact h_τ
            have h_e₃_ne_y : e₃ ≠ y := by
              intro h_eq
              rw [h_eq] at h_e₃_in_τ
              exact hnd₂.2.2 y
                (List.mem_append.mpr (Or.inr List.mem_cons_self)) y
                (List.mem_cons_of_mem _ h_e₃_in_τ) rfl
            have h_e₃_ne_e : e₃ ≠ e := by
              intro h_eq
              rw [h_eq] at h_e₃_in_τ
              exact he_notin_τ h_e₃_in_τ
            obtain ⟨τ_a, τ_b, hτ_split⟩ := List.append_of_mem h_e₃_in_τ
            have h_e₃_in_C : e₃ ∈ C.events := h_ev_in_C e₃ h_e₃_ev
            have h_dist_ye₃ : distinctOps y e₃ :=
              distinctOps_of_events hy_in_C h_e₃_in_C
                (fun h => h_e₃_ne_y h.symm)
            have h_dist_ee₃ : distinctOps e e₃ :=
              distinctOps_of_events he_in_C h_e₃_in_C
                (fun h => h_e₃_ne_e h.symm)
            refine ⟨e₃, β ++ τ_a, τ_b, ?_, h_dist_ye₃, h_dist_ee₃,
                    Or.inl ⟨h_rc_ye, h_nc_ee₃⟩⟩
            rw [hτ_split, List.append_assoc]
          · have h_not_vis_ey : ¬ C.vis e y := fun hv =>
              h_not_lo_ey (Or.inl ⟨hv, fun h => h_nc (fun s => (h s).symm)⟩)
            have h_not_vis_ye : ¬ C.vis y e := fun hv =>
              h_not_lo_ye (Or.inl ⟨hv, h_nc⟩)
            have h_overwriter_y :
                ∃ e₃ ∈ ev, C.vis y e₃ ∧ ¬ D.commutes y e₃ := by
              by_contra h_no_ow
              exact h_not_lo_ey
                (Or.inr ⟨h_not_vis_ey, h_not_vis_ye, h_rc_ey, h_no_ow⟩)
            obtain ⟨e₃, h_e₃_ev, h_vis_ye₃, h_nc_ye₃⟩ := h_overwriter_y
            have h_e₃_in_evC : e₃ ∈ evC :=
              h_abs y hy_in_ev e₃ h_e₃_ev h_vis_ye₃ h_nc_ye₃
            have h_e₃_in_π₂ : e₃ ∈ (α ++ y :: β) ++ e :: τ :=
              (hmem₂ e₃).mpr h_e₃_in_evC
            have h_lo_ye₃ : loOn C ev y e₃ := Or.inl ⟨h_vis_ye₃, h_nc_ye₃⟩
            have h_e₃_ne_e : e₃ ≠ e := fun h_eq => by
              subst h_eq; exact h_not_lo_ye h_lo_ye₃
            have h_e₃_ne_y : e₃ ≠ y := fun h_eq => by
              subst h_eq
              exact h_nc_ye₃ (fun _ => rfl)
            have h_e₃_in_C : e₃ ∈ C.events := h_ev_in_C e₃ h_e₃_ev
            have h_dist_ye₃ : distinctOps y e₃ :=
              distinctOps_of_events hy_in_C h_e₃_in_C
                (fun h => h_e₃_ne_y h.symm)
            have h_dist_ee₃ : distinctOps e e₃ :=
              distinctOps_of_events he_in_C h_e₃_in_C
                (fun h => h_e₃_ne_e h.symm)
            have h_e₃_in_βτ : e₃ ∈ β ++ τ := by
              rcases List.mem_append.mp h_e₃_in_π₂ with h | h
              · rcases List.mem_append.mp h with h_α | h_yβ
                · exfalso
                  rw [respects, List.pairwise_append] at h₂r
                  obtain ⟨h_resp_left, _, _⟩ := h₂r
                  rw [List.pairwise_append] at h_resp_left
                  obtain ⟨_, _, h_cross⟩ := h_resp_left
                  exact h_cross e₃ h_α y List.mem_cons_self h_lo_ye₃
                · rcases List.mem_cons.mp h_yβ with h_eq | h_β
                  · exact absurd h_eq h_e₃_ne_y
                  · exact List.mem_append.mpr (Or.inl h_β)
              · rcases List.mem_cons.mp h with h_eq | h_τ
                · exact absurd h_eq h_e₃_ne_e
                · exact List.mem_append.mpr (Or.inr h_τ)
            obtain ⟨γ_a, γ_b, hγ_split⟩ := List.append_of_mem h_e₃_in_βτ
            exact ⟨e₃, γ_a, γ_b, hγ_split, h_dist_ye₃, h_dist_ee₃,
                    Or.inr ⟨h_rc_ey, h_nc_ye₃⟩⟩
        exact applySeq_bubble_to_front_loOn_u (D := D) (ev := ev) hU e σ τ
          he_in_C h_σ_in_C he_notin_σ h_not_lo_fwd h_not_lo_bwd h_ov s
      have h_len_new : π₁'.length < n := by
        simp only [List.length_cons] at h_len; omega
      have h_evC'_in_C : ∀ a ∈ evC \ {e}, a ∈ C.events :=
        fun a ha => h_evC_in_C a ha.1
      have h_abs' : ∀ x ∈ evC \ {e}, ∀ z ∈ ev,
          C.vis x z → ¬ D.commutes x z → z ∈ evC \ {e} := by
        intro x hx z hz hv hnc
        refine ⟨h_abs x hx.1 z hz hv hnc, ?_⟩
        intro hz_eq
        have hz_eq' : z = e := hz_eq
        rw [hz_eq'] at hv hnc
        have hlo_xe : loOn C ev x e := Or.inl ⟨hv, hnc⟩
        exact h_e_lo_min x hx.1 hx.2 hlo_xe
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
            intro rfl; exact he_notin_σ ha
          · refine ⟨(hmem₂ a).mp
              (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ ha))), ?_⟩
            intro rfl; exact he_notin_τ ha
        · rintro ⟨hae, hne⟩
          rcases List.mem_append.mp ((hmem₂ a).mpr hae) with h | h
          · exact Or.inl h
          · rcases List.mem_cons.mp h with h' | h'
            · exact absurd h' hne
            · exact Or.inr h'
      have hr₁' : respects π₁' (loOn C ev) := (List.pairwise_cons.mp h₁r).2
      have hrστ : respects (σ ++ τ) (loOn C ev) := by
        have h2split := List.pairwise_append.mp h₂r
        rw [List.pairwise_cons] at h2split
        obtain ⟨hσ, ⟨_, hτ⟩, hcross⟩ := h2split
        rw [respects, List.pairwise_append]
        refine ⟨hσ, hτ, ?_⟩
        intro a ha b hb
        exact hcross a ha b (List.mem_cons_of_mem _ hb)
      rw [hbubble]
      show applySeq D (D.update s e) π₁' = applySeq D (D.update s e) (σ ++ τ)
      exact ih _ h_len_new (D.update s e) (evC \ {e}) π₁' (σ ++ τ) rfl
        h_evC'_in_C h_abs' hp₁' hpστ hr₁' hrστ

/-- Verbatim `Merge_Linearization_Set.lean:992` (`isCanonicalState_unique`). -/
theorem isCanonicalState_unique_u (hU : UpdateVCs D)
    {C : Sal.Emulation.Configuration D} {ev : Set (Op D.AppOp)} {s s' : D.State}
    (h_ev_in_C : ∀ a ∈ ev, a ∈ C.events)
    (h : IsCanonicalState C ev s) (h' : IsCanonicalState C ev s') :
    s = s' := by
  obtain ⟨ρ, hp, hr, hs⟩ := h
  obtain ⟨ρ', hp', hr', hs'⟩ := h'
  rw [← hs, ← hs']
  exact convergence_on_u hU D.init h_ev_in_C hp hp' hr hr'

/-- Verbatim `Merge_Linearization_Set.lean:1003` (`isCanonicalState_exists`). -/
theorem isCanonicalState_exists_u (hU : UpdateVCs D)
    {C : Sal.Emulation.Configuration D}
    (h_vis_trans : ∀ {a b c : Op D.AppOp},
       C.vis a b → C.vis b c → C.vis a c)
    (h_vis_irrefl : ∀ a : Op D.AppOp, ¬ C.vis a a)
    {ev : Set (Op D.AppOp)} {l : List (Op D.AppOp)}
    (h_l : listPermOf l ev)
    (h_in_C : ∀ a ∈ ev, a ∈ C.events) :
    ∃ s, IsCanonicalState C ev s := by
  obtain ⟨ρ, hp, hr⟩ :=
    exists_loOn_respecting_perm_u hU h_vis_trans h_vis_irrefl h_l h_in_C
  exact ⟨applySeq D D.init ρ, ρ, hp, hr, rfl⟩

/-- Verbatim `Merge_Linearization_Set.lean:1532` (`loOn_empty_of_all_comm`). -/
theorem loOn_empty_of_all_comm_u (hU : UpdateVCs D)
    {C : Sal.Emulation.Configuration D} {ev : Set (Op D.AppOp)}
    (h_comm : ∀ a b : Op D.AppOp, D.commutes a b)
    {x y : Op D.AppOp} (hx : x ∈ C.events) (hy : y ∈ C.events)
    (hne : x ≠ y) :
    ¬ loOn C ev x y := by
  rintro (⟨_, hnc⟩ | ⟨h₁, h₂, h_rc, _⟩)
  · exact hnc (h_comm x y)
  · by_cases hrep : x.rep = y.rep
    · obtain ⟨r, s, hL, hs⟩ := hx
      obtain ⟨r', s', hL', hs'⟩ := hy
      rcases C.vis_total_same_replica hL hs hL' hs' hne hrep with hv | hv
      · exact h₁ hv
      · exact h₂ hv
    · exact (hU.rc_non_comm_directional x y
        (distinctOps_of_events hx hy hne) hrep).mpr (Or.inl h_rc) (h_comm x y)

/-- Verbatim `Merge_Linearization_Set.lean:1544` (`isCanonicalState_of_all_comm`). -/
theorem isCanonicalState_of_all_comm_u (hU : UpdateVCs D)
    {C : Sal.Emulation.Configuration D}
    {ev : Set (Op D.AppOp)} {l : List (Op D.AppOp)}
    (h_comm : ∀ a b : Op D.AppOp, D.commutes a b)
    (h_in_C : ∀ a ∈ ev, a ∈ C.events)
    (h_perm : listPermOf l ev) :
    IsCanonicalState C ev (applySeq D D.init l) := by
  refine ⟨l, h_perm, ?_, rfl⟩
  refine List.Pairwise.imp_of_mem ?_ h_perm.1
  intro a b ha hb hne
  exact loOn_empty_of_all_comm_u hU h_comm
    (h_in_C b ((h_perm.2 b).mp hb)) (h_in_C a ((h_perm.2 a).mp ha))
    (Ne.symm hne)

/-! ### Small set/list toolkit for the ternary induction -/

/-- Enumerate an intersection: side 1's list filtered by membership in side 2's. -/
theorem listPermOf_inter {l₁ l₂ : List (Op D.AppOp)}
    {ev₁ ev₂ : Set (Op D.AppOp)}
    (h₁ : listPermOf l₁ ev₁) (h₂ : listPermOf l₂ ev₂) :
    listPermOf (l₁.filter (fun a => decide (a ∈ l₂))) (ev₁ ∩ ev₂) := by
  constructor
  · exact h₁.1.filter _
  · intro a
    rw [List.mem_filter]
    constructor
    · rintro ⟨ha, hd⟩
      exact ⟨(h₁.2 a).mp ha, (h₂.2 a).mp (of_decide_eq_true hd)⟩
    · rintro ⟨ha₁, ha₂⟩
      exact ⟨(h₁.2 a).mpr ha₁, decide_eq_true ((h₂.2 a).mpr ha₂)⟩

/-- Removing an event absent from side 2 leaves the intersection unchanged. -/
theorem inter_diff_left_of_not_mem {α : Type} {ev₁ ev₂ : Set α} {e : α}
    (he : e ∉ ev₂) : (ev₁ \ {e}) ∩ ev₂ = ev₁ ∩ ev₂ := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, fun hx => he (hx ▸ h2)⟩, h2⟩

/-- Mirror of `inter_diff_left_of_not_mem`. -/
theorem inter_diff_right_of_not_mem {α : Type} {ev₁ ev₂ : Set α} {e : α}
    (he : e ∉ ev₁) : ev₁ ∩ (ev₂ \ {e}) = ev₁ ∩ ev₂ := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2, _⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2, fun hx => he (hx ▸ h1)⟩

/-- Removing a shared event shrinks the intersection in lock-step. -/
theorem diff_inter_diff {α : Type} {ev₁ ev₂ : Set α} {e : α} :
    (ev₁ \ {e}) ∩ (ev₂ \ {e}) = (ev₁ ∩ ev₂) \ {e} := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_singleton_iff]
  tauto

end UpdateLayer

section Core
variable {D : ConditionedMRDTSig}

/-- **The core projection**: the ternary `Configuration`'s replica-keyed core *is* a
2-way `Emulation.Configuration` — field for field. This is what makes the entire
`loOn`/σ layer literally reusable (not merely portable) in the ternary setting. -/
def Configuration.core (C : Configuration D) :
    Sal.Emulation.Configuration D.toCRDTSig where
  N := C.N
  L := C.L
  vis := C.vis
  dom_eq := C.dom_eq
  vis_src := C.vis_src
  vis_tgt := C.vis_tgt
  vis_causal := C.vis_causal
  timestamps_distinct := C.timestamps_distinct
  vis_total_same_replica := C.vis_total_same_replica

/-- The core projection preserves the event universe (definitionally). -/
theorem core_events (C : Configuration D) :
    (Configuration.core C).events = C.events := rfl

/-- The core projection commutes with `vis` (definitionally; named for `rw`). -/
theorem core_vis (C : Configuration D) :
    (Configuration.core C).vis = C.vis := rfl

/-- **Timestamp uniqueness, contrapositive form**: two events of a binary
configuration's universe with equal timestamps are equal (structural, from
`timestamps_distinct`; instances consume it through the core projection). -/
theorem _root_.Sal.Emulation.Configuration.ts_unique {D' : CRDTSig}
    (C : Sal.Emulation.Configuration D') {a b : Op D'.AppOp}
    (ha : a ∈ C.events) (hb : b ∈ C.events) (h : a.1 = b.1) : a = b := by
  by_contra hne
  obtain ⟨r, s, hL, hs⟩ := ha
  obtain ⟨r', s', hL', hs'⟩ := hb
  exact C.timestamps_distinct hL hs hL' hs' hne h

end Core

end Sal.ConditionedMRDTs
