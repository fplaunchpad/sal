import Sal.MRDTs.Metatheory.Join.SetRelativeReplay
import Sal.MRDTs.Framework.Execution

/-!
# Sufficient algebraic laws for set-relative replay

The selected `rc` specifies semantic resolution, not concrete noncommutation.
This optional proof route covers noncommuting updates by `rc`, requires
acyclicity, and justifies swaps in the presence of a semantic absorber.
Additional edges between commuting updates are allowed. Public correctness
is separately stated by `VerifiedMRDT` against a sequential specification.
-/

namespace Sal.MRDTs

open Sal.MRDTs.Foundation
open Classical

/-! ## §A. The update-layer VC fragment, and the σ-machinery re-hosted on it -/

section UpdateLayer
variable {D : UpdateSig}
variable [ReplayPolicy D]

/-- The directed part of the replay policy, restricted to event pairs with
distinct timestamps.  This is the part of `replayOrder` that can contribute
an `rc`-flavored edge to `loOnNe` in a replay context. -/
def RcEdge (D : UpdateSig) [ReplayPolicy D]
    (a b : Op D.AppOp) : Prop :=
  distinctOps a b ∧ D.rc a b

/-- The semantic resolve-conflict relation has no nonempty directed cycle. -/
def RcAcyclic (D : UpdateSig) [ReplayPolicy D] : Prop :=
  ∀ a, ¬ Relation.TransGen D.rc a a

/-- Sufficient concrete-update laws for replay convergence under the selected
semantic `rc`. Coverage is one-way: ordered updates may commute. The swap law
uses precisely the semantic absorber tested by `loOn`. This bundle is a proof
technique, not the definition of conflict or a field of `VerifiedMRDT`. -/
structure ReplayLaws (D : UpdateSig) [ReplayPolicy D] : Prop where
  noncomm_covered :
    ∀ o₁ o₂ : Op D.AppOp,
      ¬ D.commutes o₁ o₂ → (D.rc o₁ o₂ ∨ D.rc o₂ o₁)
  rc_acyclic : RcAcyclic D
  cond_comm_lift :
    ∀ (s : D.State) (e e' e'' : Op D.AppOp) (π : List (Op D.AppOp)),
      distinctOps e e' → distinctOps e e'' → distinctOps e' e'' →
      D.rc e e' →
      (D.rc e' e'' ∨ D.rc e'' e') →
      D.update (applySeq D (D.update (D.update s e') e) π) e''
        = D.update (applySeq D (D.update (D.update s e) e') π) e''

/-- Every acyclic semantic policy is compatible with all-commuting concrete
updates. In particular, commutativity does not force `rc` to be empty. -/
theorem ReplayLaws.of_all_comm
    (hcomm : ∀ a b : Op D.AppOp, D.commutes a b)
    (hRc : RcAcyclic D) : ReplayLaws D := by
  refine ⟨fun a b h => (h (hcomm a b)).elim, hRc, ?_⟩
  intro s e e' e'' π _ _ _ _ _
  rw [hcomm e' e s]

/-- Forbidding every length-two chain is a stronger sufficient condition for
acyclicity. Unlike the historical timestamp-guarded law, this premise also
excludes self edges and cycles between equal-timestamp inputs. -/
theorem rcAcyclic_of_noRcChain
    (h : ∀ o₁ o₂ o₃ : Op D.AppOp,
      ¬ (D.replayOrder o₁ o₂ = RcRes.Fst_then_snd ∧
         D.replayOrder o₂ o₃ = RcRes.Fst_then_snd)) :
    RcAcyclic D := by
  intro a hcycle
  cases hcycle with
  | single haa =>
      exact h a a a ⟨haa, haa⟩
  | @tail b _ hab hba =>
      rcases Relation.TransGen.tail'_iff.mp hab with ⟨x, _, hxb⟩
      exact h x b a ⟨hxb, hba⟩

/-- Camel-case accessor retained for theorem call sites. -/
theorem ReplayLaws.rcAcyclic (hU : ReplayLaws D) : RcAcyclic D :=
  hU.rc_acyclic

/-- Semantic rc acyclicity supplies the policy-path premise of the shared
order-only theorem. -/
theorem loOnNe_acyclic_of_rcAcyclic
    (hRc : RcAcyclic D)
    {C : ReplayContext D}
    (h_vis_trans : ∀ {a b c : Op D.AppOp},
       C.vis a b → C.vis b c → C.vis a c)
    (h_vis_irrefl : ∀ a : Op D.AppOp, ¬ C.vis a a)
    {T : Set (Op D.AppOp)}
    (_h_in_C : ∀ a ∈ T, a ∈ C.events)
    (a : Op D.AppOp) :
    ¬ Relation.TransGen (loOnNe C T) a a := by
  apply loOnNe_acyclic_of_policy_paths h_vis_trans h_vis_irrefl ?_ a
  intro x cycle
  apply hRc x
  exact cycle.lift id (by
    intro u v edge
    rcases edge with ⟨⟨_, _, _, hvis | hrc⟩, hnvis⟩
    · exact (hnvis hvis.1).elim
    · exact hrc.2.2.1)

/-- Reuse historical swap equations with an explicit acyclicity proof. The
historical timestamp-guarded no-chain law alone does not establish full `rc`
acyclicity on arbitrary inputs. -/
theorem ReplayLaws.ofBinaryMergeLaws [HistoricalBinaryMerge D]
    (hVC : BinaryMergeLaws D) (hRc : RcAcyclic D) : ReplayLaws D := by
  refine ⟨fun a b => (hVC.rc_non_comm_directional a b).mp,
    hRc, ?_⟩
  intro s e e' e'' π h₁ h₂ h₃ hrc habs
  exact hVC.cond_comm_lift s e e' e'' π h₁ h₂ h₃ hrc
    ((hVC.rc_non_comm_directional e' e'').mpr habs)

/-- Verbatim `SetRelativeReplay.lean:128` (`applySeq_swap_via_cond_comm_lift_core`)
with `BinaryMergeLaws` slimmed to `ReplayLaws`. -/
theorem applySeq_swap_via_cond_comm_lift_of_replayLaws
    (hU : ReplayLaws D)
    {a b e₃ : Op D.AppOp}
    (h_dist_ab : distinctOps a b)
    (h_dist_be : distinctOps b e₃)
    (h_dist_ae : distinctOps a e₃)
    (h_rc_ab : D.replayOrder a b = RcRes.Fst_then_snd)
    (h_abs_be : D.rc b e₃ ∨ D.rc e₃ b)
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
      h_dist_ab h_dist_ae h_dist_be h_rc_ab h_abs_be).symm

/-- Compatibility wrapper for callers carrying the complete law bundle. -/
theorem loOnNe_acyclic_of_replayLaws (hU : ReplayLaws D)
    {C : Sal.MRDTs.Foundation.ReplayContext D}
    (h_vis_trans : ∀ {a b c : Op D.AppOp},
       C.vis a b → C.vis b c → C.vis a c)
    (h_vis_irrefl : ∀ a : Op D.AppOp, ¬ C.vis a a)
    {T : Set (Op D.AppOp)}
    (h_in_C : ∀ a ∈ T, a ∈ C.events)
    (a : Op D.AppOp) :
    ¬ Relation.TransGen (loOnNe C T) a a := by
  exact loOnNe_acyclic_of_rcAcyclic hU.rcAcyclic h_vis_trans h_vis_irrefl h_in_C a

/-- Compatibility wrapper for callers carrying replay laws. -/
theorem exists_loOn_maximal_of_replayLaws (hU : ReplayLaws D)
    {C : Sal.MRDTs.Foundation.ReplayContext D}
    (h_vis_trans : ∀ {a b c : Op D.AppOp},
       C.vis a b → C.vis b c → C.vis a c)
    (h_vis_irrefl : ∀ a : Op D.AppOp, ¬ C.vis a a)
    {T : Set (Op D.AppOp)} {l : List (Op D.AppOp)}
    (h_l : listPermOf l T)
    (h_in_C : ∀ a ∈ T, a ∈ C.events)
    (h_ne : T.Nonempty) :
    ∃ e ∈ T, ∀ x ∈ T, x ≠ e → ¬ loOn C T e x := by
  exact exists_loOn_maximal_of_acyclic h_l
    (loOnNe_acyclic_of_rcAcyclic hU.rcAcyclic h_vis_trans h_vis_irrefl h_in_C) h_ne

/-- Enumeration uses only the acyclicity component of replay laws. -/
theorem exists_loOn_respecting_perm_of_replayLaws (hU : ReplayLaws D)
    {C : Sal.MRDTs.Foundation.ReplayContext D}
    (h_vis_trans : ∀ {a b c : Op D.AppOp},
       C.vis a b → C.vis b c → C.vis a c)
    (h_vis_irrefl : ∀ a : Op D.AppOp, ¬ C.vis a a)
    {T : Set (Op D.AppOp)} {l : List (Op D.AppOp)}
    (h_l : listPermOf l T)
    (h_in_C : ∀ a ∈ T, a ∈ C.events) :
    ∃ ρ : List (Op D.AppOp),
      listPermOf ρ T ∧ respects ρ (loOn C T) := by
  exact exists_loOn_respecting_perm_of_acyclic h_l
    (loOnNe_acyclic_of_rcAcyclic hU.rcAcyclic h_vis_trans h_vis_irrefl h_in_C)

/-- Verbatim `SetRelativeReplay.lean:472` (`applySeq_swap_loOn_incomparable`). -/
theorem applySeq_swap_loOn_incomparable_of_replayLaws
    (hU : ReplayLaws D) {C : Sal.MRDTs.Foundation.ReplayContext D}
    {ev : Set (Op D.AppOp)}
    {a b : Op D.AppOp} (h_ne : a ≠ b)
    (h_a_in_C : a ∈ C.events) (h_b_in_C : b ∈ C.events)
    (h_not_lo_ab : ¬ loOn C ev a b) (h_not_lo_ba : ¬ loOn C ev b a)
    (pfx sfx : List (Op D.AppOp)) (s : D.State)
    (h_ov : ¬ D.commutes a b → a.rep ≠ b.rep →
      ∃ e₃ α β, sfx = α ++ e₃ :: β ∧
                distinctOps a e₃ ∧ distinctOps b e₃ ∧
                ((D.replayOrder a b = RcRes.Fst_then_snd ∧
                  (D.rc b e₃ ∨ D.rc e₃ b)) ∨
                 (D.replayOrder b a = RcRes.Fst_then_snd ∧
                  (D.rc a e₃ ∨ D.rc e₃ a)))) :
    applySeq D s (pfx ++ a :: b :: sfx)
    = applySeq D s (pfx ++ b :: a :: sfx) := by
  by_cases h_comm : D.commutes a b
  · exact applySeq_swap_commute_basic h_comm pfx sfx s
  · obtain ⟨_, _, hL_a, h_a_in_s⟩ := h_a_in_C
    obtain ⟨_, _, hL_b, h_b_in_s⟩ := h_b_in_C
    have h_dist_ab : distinctOps a b :=
      C.timestamps_distinct hL_a h_a_in_s hL_b h_b_in_s h_ne
    have h_rc_pair := hU.noncomm_covered a b h_comm
    by_cases h_same : a.rep = b.rep
    · exfalso
      have h_vis :=
        C.vis_total_same_replica hL_a h_a_in_s hL_b h_b_in_s h_ne h_same
      rcases h_vis with hvab | hvba
      · exact h_not_lo_ab (Or.inl ⟨hvab, h_rc_pair⟩)
      · exact h_not_lo_ba (Or.inl ⟨hvba, h_rc_pair.symm⟩)
    ·
      obtain ⟨e₃, α, β, h_sfx, h_dae, h_dbe, h_case⟩ := h_ov h_comm h_same
      subst h_sfx
      rcases h_case with ⟨h_rc_ab, h_nc_be⟩ | ⟨h_rc_ba, h_nc_ae⟩
      · exact applySeq_swap_via_cond_comm_lift_of_replayLaws hU h_dist_ab h_dbe h_dae
          h_rc_ab h_nc_be pfx α β s
      · have h_dist_ba : distinctOps b a := Ne.symm h_dist_ab
        exact (applySeq_swap_via_cond_comm_lift_of_replayLaws hU h_dist_ba h_dae h_dbe
          h_rc_ba h_nc_ae pfx α β s).symm

/-- Verbatim `SetRelativeReplay.lean:513` (`applySeq_bubble_to_front_loOn`). -/
theorem applySeq_bubble_to_front_loOn_of_replayLaws
    (hU : ReplayLaws D) {C : Sal.MRDTs.Foundation.ReplayContext D}
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
                  ((D.replayOrder y e = RcRes.Fst_then_snd ∧
                    (D.rc e e₃ ∨ D.rc e₃ e)) ∨
                   (D.replayOrder e y = RcRes.Fst_then_snd ∧
                    (D.rc y e₃ ∨ D.rc e₃ y))))
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
      have := applySeq_swap_loOn_incomparable_of_replayLaws (D := D) (ev := ev)
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

/-- Verbatim `SetRelativeReplay.lean:577` (`convergence_on`): two
`loOn C ev`-respecting permutations of `ev` fold to the same state (no closure
hypotheses). -/
theorem convergence_on_of_replayLaws
    (hU : ReplayLaws D) {C : Sal.MRDTs.Foundation.ReplayContext D}
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
      (∀ x ∈ evC, ∀ z ∈ ev, C.vis x z → (D.rc x z ∨ D.rc z x) → z ∈ evC) →
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
                        ((D.replayOrder y e = RcRes.Fst_then_snd ∧
                          (D.rc e e₃ ∨ D.rc e₃ e)) ∨
                         (D.replayOrder e y = RcRes.Fst_then_snd ∧
                          (D.rc y e₃ ∨ D.rc e₃ y))) := by
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
            hU.noncomm_covered y e h_nc
          rcases h_rc_disj with h_rc_ye | h_rc_ey
          · have h_not_vis_ye : ¬ C.vis y e := fun hv =>
              h_not_lo_ye (Or.inl ⟨hv, Or.inl h_rc_ye⟩)
            have h_not_vis_ey : ¬ C.vis e y := by
              intro hv
              exact h_not_lo_ey (Or.inl ⟨hv, Or.inr h_rc_ye⟩)
            have h_overwriter_e :
                ∃ e₃ ∈ ev, C.vis e e₃ ∧ (D.rc e e₃ ∨ D.rc e₃ e) := by
              by_contra h_no_ow
              exact h_not_lo_ye
                (Or.inr ⟨h_not_vis_ye, h_not_vis_ey, h_rc_ye, h_no_ow⟩)
            obtain ⟨e₃, h_e₃_ev, h_vis_ee₃, h_rc_ee₃⟩ := h_overwriter_e
            have h_e₃_in_evC : e₃ ∈ evC :=
              h_abs e he_in_ev e₃ h_e₃_ev h_vis_ee₃ h_rc_ee₃
            have h_e₃_in_π₂ : e₃ ∈ (α ++ y :: β) ++ e :: τ :=
              (hmem₂ e₃).mpr h_e₃_in_evC
            have h_lo_ee₃ : loOn C ev e e₃ :=
              Or.inl ⟨h_vis_ee₃, h_rc_ee₃⟩
            have h_e₃_in_τ : e₃ ∈ τ := by
              rcases List.mem_append.mp h_e₃_in_π₂ with h | h
              · exfalso
                have hresp_pair := List.pairwise_append.mp h₂r
                exact hresp_pair.2.2 e₃ h e List.mem_cons_self h_lo_ee₃
              · rcases List.mem_cons.mp h with h_eq | h_τ
                · subst e₃
                  exact False.elim (hU.rc_acyclic e
                    (.single (h_rc_ee₃.elim id id)))
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
                (Or.inl ⟨hv, Or.inl h_rc_ey⟩)
            have h_not_vis_ye : ¬ C.vis y e := fun hv =>
              h_not_lo_ye (Or.inl ⟨hv, Or.inr h_rc_ey⟩)
            have h_overwriter_y :
                ∃ e₃ ∈ ev, C.vis y e₃ ∧ (D.rc y e₃ ∨ D.rc e₃ y) := by
              by_contra h_no_ow
              exact h_not_lo_ey
                (Or.inr ⟨h_not_vis_ey, h_not_vis_ye, h_rc_ey, h_no_ow⟩)
            obtain ⟨e₃, h_e₃_ev, h_vis_ye₃, h_rc_ye₃⟩ := h_overwriter_y
            have h_e₃_in_evC : e₃ ∈ evC :=
              h_abs y hy_in_ev e₃ h_e₃_ev h_vis_ye₃ h_rc_ye₃
            have h_e₃_in_π₂ : e₃ ∈ (α ++ y :: β) ++ e :: τ :=
              (hmem₂ e₃).mpr h_e₃_in_evC
            have h_lo_ye₃ : loOn C ev y e₃ :=
              Or.inl ⟨h_vis_ye₃, h_rc_ye₃⟩
            have h_e₃_ne_e : e₃ ≠ e := fun h_eq => by
              subst h_eq; exact h_not_lo_ye h_lo_ye₃
            have h_e₃_ne_y : e₃ ≠ y := fun h_eq => by
              subst h_eq
              exact hU.rc_acyclic _ (.single (h_rc_ye₃.elim id id))
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
        exact applySeq_bubble_to_front_loOn_of_replayLaws (D := D) (ev := ev) hU e σ τ
          he_in_C h_σ_in_C he_notin_σ h_not_lo_fwd h_not_lo_bwd h_ov s
      have h_len_new : π₁'.length < n := by
        simp only [List.length_cons] at h_len; omega
      have h_evC'_in_C : ∀ a ∈ evC \ {e}, a ∈ C.events :=
        fun a ha => h_evC_in_C a ha.1
      have h_abs' : ∀ x ∈ evC \ {e}, ∀ z ∈ ev,
          C.vis x z → (D.rc x z ∨ D.rc z x) → z ∈ evC \ {e} := by
        intro x hx z hz hv hrc
        refine ⟨h_abs x hx.1 z hz hv hrc, ?_⟩
        intro hz_eq
        have hz_eq' : z = e := hz_eq
        rw [hz_eq'] at hv hrc
        have hlo_xe : loOn C ev x e := Or.inl ⟨hv, hrc⟩
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

/-- Verbatim `SetRelativeReplay.lean:992` (`isCanonicalState_unique`). -/
theorem isCanonicalState_unique_of_replayLaws (hU : ReplayLaws D)
    {C : Sal.MRDTs.Foundation.ReplayContext D} {ev : Set (Op D.AppOp)} {s s' : D.State}
    (h_ev_in_C : ∀ a ∈ ev, a ∈ C.events)
    (h : IsCanonicalState C ev s) (h' : IsCanonicalState C ev s') :
    s = s' := by
  obtain ⟨ρ, hp, hr, hs⟩ := h
  obtain ⟨ρ', hp', hr', hs'⟩ := h'
  rw [← hs, ← hs']
  exact convergence_on_of_replayLaws hU D.init h_ev_in_C hp hp' hr hr'

/-- Verbatim `SetRelativeReplay.lean:1003` (`isCanonicalState_exists`). -/
theorem isCanonicalState_exists_of_replayLaws (hU : ReplayLaws D)
    {C : Sal.MRDTs.Foundation.ReplayContext D}
    (h_vis_trans : ∀ {a b c : Op D.AppOp},
       C.vis a b → C.vis b c → C.vis a c)
    (h_vis_irrefl : ∀ a : Op D.AppOp, ¬ C.vis a a)
    {ev : Set (Op D.AppOp)} {l : List (Op D.AppOp)}
    (h_l : listPermOf l ev)
    (h_in_C : ∀ a ∈ ev, a ∈ C.events) :
    ∃ s, IsCanonicalState C ev s := by
  obtain ⟨ρ, hp, hr⟩ :=
    exists_loOn_respecting_perm_of_replayLaws hU h_vis_trans h_vis_irrefl h_l h_in_C
  exact ⟨applySeq D D.init ρ, ρ, hp, hr, rfl⟩

/-- Verbatim `SetRelativeReplay.lean:1532` (`loOn_empty_of_all_comm`). -/
theorem loOn_empty_of_all_comm_of_replayLaws
    {C : Sal.MRDTs.Foundation.ReplayContext D} {ev : Set (Op D.AppOp)}
    (h_comm : ∀ a b : Op D.AppOp, D.commutes a b)
    (h_rc_either : ∀ a b : Op D.AppOp,
      D.replayOrder a b = RcRes.Either)
    {x y : Op D.AppOp} (hx : x ∈ C.events) (hy : y ∈ C.events)
    (hne : x ≠ y) :
    ¬ loOn C ev x y := by
  rintro (⟨_, hrc⟩ | ⟨h₁, h₂, h_rc, _⟩)
  · rcases hrc with hrc | hrc
    · change D.replayOrder x y = RcRes.Fst_then_snd at hrc
      rw [h_rc_either] at hrc
      exact RcRes.noConfusion hrc
    · change D.replayOrder y x = RcRes.Fst_then_snd at hrc
      rw [h_rc_either] at hrc
      exact RcRes.noConfusion hrc
  · change D.replayOrder x y = RcRes.Fst_then_snd at h_rc
    rw [h_rc_either] at h_rc
    exact RcRes.noConfusion h_rc

/-- Verbatim `SetRelativeReplay.lean:1544` (`isCanonicalState_of_all_comm`). -/
theorem isCanonicalState_of_all_comm_of_replayLaws
    {C : Sal.MRDTs.Foundation.ReplayContext D}
    {ev : Set (Op D.AppOp)} {l : List (Op D.AppOp)}
    (h_comm : ∀ a b : Op D.AppOp, D.commutes a b)
    (h_rc_either : ∀ a b : Op D.AppOp,
      D.replayOrder a b = RcRes.Either)
    (h_in_C : ∀ a ∈ ev, a ∈ C.events)
    (h_perm : listPermOf l ev) :
    IsCanonicalState C ev (applySeq D D.init l) := by
  refine ⟨l, h_perm, ?_, rfl⟩
  refine List.Pairwise.imp_of_mem ?_ h_perm.1
  intro a b ha hb hne
  exact loOn_empty_of_all_comm_of_replayLaws h_comm h_rc_either
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

section Replay
variable {D : MRDTSig}
variable [ReplayPolicy D.toUpdateSig]

/-- **Timestamp uniqueness, contrapositive form**: two events of a replay
context's universe with equal timestamps are equal (structural, from
`timestamps_distinct`; instances consume it through the replay projection). -/
theorem _root_.Sal.MRDTs.Foundation.ReplayContext.ts_unique {D' : UpdateSig}
    (C : Sal.MRDTs.Foundation.ReplayContext D') {a b : Op D'.AppOp}
    (ha : a ∈ C.events) (hb : b ∈ C.events) (h : a.1 = b.1) : a = b := by
  by_contra hne
  obtain ⟨r, s, hL, hs⟩ := ha
  obtain ⟨r', s', hL', hs'⟩ := hb
  exact C.timestamps_distinct hL hs hL' hs' hne h

end Replay

end Sal.MRDTs
