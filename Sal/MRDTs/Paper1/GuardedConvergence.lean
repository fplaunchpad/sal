import Sal.MRDTs.Paper1.GuardedReplay

/-!
# Replay convergence from event-guarded paper laws

The proof works directly with `paperOrder`. It applies policy exactness only
when swapping supported events with distinct timestamps and different replicas.
Causal order and the absorber invariant use actual concrete noncommutation.
Neither global exactness nor the guarded no-chain field is needed here.
-/

namespace Sal.MRDTs.Paper1
open Foundation Classical
variable {D : UpdateSig} {P : OperationPolicy D.AppOp}

theorem applySeq_swap_via_cond_comm_lift_guarded
    (hU : GuardedReplay.Laws D P)
    {a b e₃ : Op D.AppOp}
    (h_dist_ab : distinctOps a b)
    (h_dist_be : distinctOps b e₃)
    (h_dist_ae : distinctOps a e₃)
    (h_rc_ab : P.before a.op b.op)
    (h_abs_be : ¬ D.commutes b e₃)
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
    (hU.conditional_commutation (applySeq D s pfx) a b e₃ α
      h_dist_ab h_dist_ae h_dist_be h_rc_ab h_abs_be).symm

theorem applySeq_swap_loOn_incomparable_guarded
    (hU : GuardedReplay.Laws D P) {C : Sal.MRDTs.Foundation.ReplayContext D}
    {ev : Set (Op D.AppOp)}
    {a b : Op D.AppOp} (h_ne : a ≠ b)
    (h_a_in_C : a ∈ C.events) (h_b_in_C : b ∈ C.events)
    (h_not_lo_ab : ¬ paperOrder P C ev a b) (h_not_lo_ba : ¬ paperOrder P C ev b a)
    (pfx sfx : List (Op D.AppOp)) (s : D.State)
    (h_ov : ¬ D.commutes a b → a.rep ≠ b.rep →
      ∃ e₃ α β, sfx = α ++ e₃ :: β ∧
                distinctOps a e₃ ∧ distinctOps b e₃ ∧
                ((P.before a.op b.op ∧
                  ¬ D.commutes b e₃) ∨
                 (P.before b.op a.op ∧
                  ¬ D.commutes a e₃))) :
    applySeq D s (pfx ++ a :: b :: sfx)
    = applySeq D s (pfx ++ b :: a :: sfx) := by
  by_cases h_comm : D.commutes a b
  · exact applySeq_swap_commute_basic h_comm pfx sfx s
  · obtain ⟨_, _, hL_a, h_a_in_s⟩ := h_a_in_C
    obtain ⟨_, _, hL_b, h_b_in_s⟩ := h_b_in_C
    have h_dist_ab : distinctOps a b :=
      C.timestamps_distinct hL_a h_a_in_s hL_b h_b_in_s h_ne
    by_cases h_same : a.rep = b.rep
    · exfalso
      have h_vis :=
        C.vis_total_same_replica hL_a h_a_in_s hL_b h_b_in_s h_ne h_same
      rcases h_vis with hvab | hvba
      · exact h_not_lo_ab (Or.inl ⟨hvab, h_comm⟩)
      · exact h_not_lo_ba (Or.inl ⟨hvba, fun h => h_comm (commutes_symm h)⟩)
    ·
      obtain ⟨e₃, α, β, h_sfx, h_dae, h_dbe, h_case⟩ := h_ov h_comm h_same
      subst h_sfx
      rcases h_case with ⟨h_rc_ab, h_nc_be⟩ | ⟨h_rc_ba, h_nc_ae⟩
      · exact applySeq_swap_via_cond_comm_lift_guarded hU h_dist_ab h_dbe h_dae
          h_rc_ab h_nc_be pfx α β s
      · have h_dist_ba : distinctOps b a := Ne.symm h_dist_ab
        exact (applySeq_swap_via_cond_comm_lift_guarded hU h_dist_ba h_dae h_dbe
          h_rc_ba h_nc_ae pfx α β s).symm

/-- Bubble an event past an incomparable prefix, retaining each absorber. -/
theorem applySeq_bubble_to_front_loOn_guarded
    (hU : GuardedReplay.Laws D P) {C : Sal.MRDTs.Foundation.ReplayContext D}
    {ev : Set (Op D.AppOp)}
    (e : Op D.AppOp) (σ tail : List (Op D.AppOp))
    (h_e_in_C : e ∈ C.events)
    (h_σ_in_C : ∀ y ∈ σ, y ∈ C.events)
    (h_e_notin : e ∉ σ)
    (h_not_lo_fwd : ∀ y ∈ σ, ¬ paperOrder P C ev e y)
    (h_not_lo_bwd : ∀ y ∈ σ, ¬ paperOrder P C ev y e)
    (h_ov : ∀ α β y, σ = α ++ y :: β →
      ¬ D.commutes y e → y.rep ≠ e.rep →
      ∃ e₃ α' β', β ++ tail = α' ++ e₃ :: β' ∧
                  distinctOps y e₃ ∧ distinctOps e e₃ ∧
                  ((P.before y.op e.op ∧
                    ¬ D.commutes e e₃) ∨
                   (P.before e.op y.op ∧
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
      have := applySeq_swap_loOn_incomparable_guarded (D := D) (ev := ev)
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

/-- Supported permutations respecting the semantic paper order converge from
every initial state. No closure assumption on the event set is required. -/
theorem convergence_on_guarded
    (hU : GuardedReplay.Laws D P) {C : Sal.MRDTs.Foundation.ReplayContext D}
    (s : D.State) {π₁ π₂ : List (Op D.AppOp)} {ev : Set (Op D.AppOp)}
    (h_ev_in_C : ∀ a ∈ ev, a ∈ C.events)
    (h₁_perm : listPermOf π₁ ev) (h₂_perm : listPermOf π₂ ev)
    (h₁_resp : respects π₁ (paperOrder P C ev))
    (h₂_resp : respects π₂ (paperOrder P C ev)) :
    applySeq D s π₁ = applySeq D s π₂ := by
  suffices gen : ∀ n (s : D.State) (evC : Set (Op D.AppOp))
                   (π₁ π₂ : List (Op D.AppOp)),
      π₁.length = n →
      (∀ a ∈ evC, a ∈ C.events) →
      (∀ x ∈ evC, ∀ z ∈ ev, C.vis x z → ¬ D.commutes x z → z ∈ evC) →
      listPermOf π₁ evC → listPermOf π₂ evC →
      respects π₁ (paperOrder P C ev) → respects π₂ (paperOrder P C ev) →
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
      have h_e_lo_min : ∀ z ∈ evC, z ≠ e → ¬ paperOrder P C ev z e := by
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
        have h_not_lo_fwd : ∀ y ∈ σ, ¬ paperOrder P C ev e y := by
          intro y hy
          have h2 := List.pairwise_append.mp h₂r
          exact h2.2.2 y hy e List.mem_cons_self
        have h_not_lo_bwd : ∀ y ∈ σ, ¬ paperOrder P C ev y e := by
          intro y hy
          have hy_ne_e : y ≠ e := fun h => he_notin_σ (h ▸ hy)
          exact h_e_lo_min y (h_σ_sub_ev y hy) hy_ne_e
        have h_ov : ∀ α β y, σ = α ++ y :: β →
            ¬ D.commutes y e → y.rep ≠ e.rep →
            ∃ e₃ α' β', β ++ τ = α' ++ e₃ :: β' ∧
                        distinctOps y e₃ ∧ distinctOps e e₃ ∧
                        ((P.before y.op e.op ∧
                          ¬ D.commutes e e₃) ∨
                         (P.before e.op y.op ∧
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
          have h_not_lo_ye : ¬ paperOrder P C ev y e := h_not_lo_bwd y hy_in_σ
          have h_not_lo_ey : ¬ paperOrder P C ev e y := h_not_lo_fwd y hy_in_σ
          have h_rc_disj :=
            (hU.noncomm_exact y e h_dist_ye h_diff_rep).mp h_nc
          rcases h_rc_disj with h_rc_ye | h_rc_ey
          · have h_not_vis_ye : ¬ C.vis y e := fun hv =>
              h_not_lo_ye (Or.inl ⟨hv, h_nc⟩)
            have h_not_vis_ey : ¬ C.vis e y := by
              intro hv
              exact h_not_lo_ey (Or.inl ⟨hv, fun h => h_nc (commutes_symm h)⟩)
            have h_overwriter_e :
                ∃ e₃ ∈ ev, C.vis e e₃ ∧ ¬ D.commutes e e₃ := by
              by_contra h_no_ow
              exact h_not_lo_ye
                (Or.inr ⟨h_not_vis_ye, h_not_vis_ey, h_rc_ye, h_no_ow⟩)
            obtain ⟨e₃, h_e₃_ev, h_vis_ee₃, h_rc_ee₃⟩ := h_overwriter_e
            have h_e₃_in_evC : e₃ ∈ evC :=
              h_abs e he_in_ev e₃ h_e₃_ev h_vis_ee₃ h_rc_ee₃
            have h_e₃_in_π₂ : e₃ ∈ (α ++ y :: β) ++ e :: τ :=
              (hmem₂ e₃).mpr h_e₃_in_evC
            have h_lo_ee₃ : paperOrder P C ev e e₃ :=
              Or.inl ⟨h_vis_ee₃, h_rc_ee₃⟩
            have h_e₃_in_τ : e₃ ∈ τ := by
              rcases List.mem_append.mp h_e₃_in_π₂ with h | h
              · exfalso
                have hresp_pair := List.pairwise_append.mp h₂r
                exact hresp_pair.2.2 e₃ h e List.mem_cons_self h_lo_ee₃
              · rcases List.mem_cons.mp h with h_eq | h_τ
                · subst e₃
                  exact False.elim (h_rc_ee₃ (fun _ => rfl))
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
            have h_e₃_in_C : e₃ ∈ C.events := h_ev_in_C e₃ h_e₃_ev
            have h_dist_ee₃ : distinctOps e e₃ :=
              distinctOps_of_events he_in_C h_e₃_in_C
                (fun h => h_e₃_ne_e h.symm)
            have h_dist_ye₃ : distinctOps y e₃ :=
              distinctOps_of_events hy_in_C h_e₃_in_C
                (fun h => h_e₃_ne_y h.symm)
            obtain ⟨τ_a, τ_b, hτ_split⟩ := List.append_of_mem h_e₃_in_τ
            have h_dist_ye₃ : distinctOps y e₃ :=
              distinctOps_of_events hy_in_C h_e₃_in_C
                (fun h => h_e₃_ne_y h.symm)
            refine ⟨e₃, β ++ τ_a, τ_b, ?_, h_dist_ye₃, h_dist_ee₃,
                    Or.inl ⟨h_rc_ye, h_rc_ee₃⟩⟩
            rw [hτ_split, List.append_assoc]
          · have h_not_vis_ey : ¬ C.vis e y := fun hv =>
              h_not_lo_ey
                (Or.inl ⟨hv, fun h => h_nc (commutes_symm h)⟩)
            have h_not_vis_ye : ¬ C.vis y e := fun hv =>
              h_not_lo_ye (Or.inl ⟨hv, h_nc⟩)
            have h_overwriter_y :
                ∃ e₃ ∈ ev, C.vis y e₃ ∧ ¬ D.commutes y e₃ := by
              by_contra h_no_ow
              exact h_not_lo_ey
                (Or.inr ⟨h_not_vis_ey, h_not_vis_ye, h_rc_ey, h_no_ow⟩)
            obtain ⟨e₃, h_e₃_ev, h_vis_ye₃, h_rc_ye₃⟩ := h_overwriter_y
            have h_e₃_in_evC : e₃ ∈ evC :=
              h_abs y hy_in_ev e₃ h_e₃_ev h_vis_ye₃ h_rc_ye₃
            have h_e₃_in_π₂ : e₃ ∈ (α ++ y :: β) ++ e :: τ :=
              (hmem₂ e₃).mpr h_e₃_in_evC
            have h_lo_ye₃ : paperOrder P C ev y e₃ :=
              Or.inl ⟨h_vis_ye₃, h_rc_ye₃⟩
            have h_e₃_ne_e : e₃ ≠ e := fun h_eq => by
              subst h_eq; exact h_not_lo_ye h_lo_ye₃
            have h_e₃_ne_y : e₃ ≠ y := fun h_eq => by
              subst h_eq
              exact h_rc_ye₃ (fun _ => rfl)
            have h_e₃_in_C : e₃ ∈ C.events := h_ev_in_C e₃ h_e₃_ev
            have h_dist_ee₃ : distinctOps e e₃ :=
              distinctOps_of_events he_in_C h_e₃_in_C
                (fun h => h_e₃_ne_e h.symm)
            have h_dist_ye₃ : distinctOps y e₃ :=
              distinctOps_of_events hy_in_C h_e₃_in_C
                (fun h => h_e₃_ne_y h.symm)
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
                    Or.inr ⟨h_rc_ey, h_rc_ye₃⟩⟩
        exact applySeq_bubble_to_front_loOn_guarded (D := D) (ev := ev) hU e σ τ
          he_in_C h_σ_in_C he_notin_σ h_not_lo_fwd h_not_lo_bwd h_ov s
      have h_len_new : π₁'.length < n := by
        simp only [List.length_cons] at h_len; omega
      have h_evC'_in_C : ∀ a ∈ evC \ {e}, a ∈ C.events :=
        fun a ha => h_evC_in_C a ha.1
      have h_abs' : ∀ x ∈ evC \ {e}, ∀ z ∈ ev,
          C.vis x z → ¬ D.commutes x z → z ∈ evC \ {e} := by
        intro x hx z hz hv hrc
        refine ⟨h_abs x hx.1 z hz hv hrc, ?_⟩
        intro hz_eq
        have hz_eq' : z = e := hz_eq
        rw [hz_eq'] at hv hrc
        have hlo_xe : paperOrder P C ev x e := Or.inl ⟨hv, hrc⟩
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
      have hr₁' : respects π₁' (paperOrder P C ev) := (List.pairwise_cons.mp h₁r).2
      have hrστ : respects (σ ++ τ) (paperOrder P C ev) := by
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


end Sal.MRDTs.Paper1
