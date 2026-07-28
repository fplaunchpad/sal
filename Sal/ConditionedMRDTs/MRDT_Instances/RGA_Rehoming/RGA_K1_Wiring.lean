import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_K1_DeltaDiscipline
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_DeltaEnum

/-!
# K1 wiring — discharging `canonFoldOK_delta`'s closure hypotheses

The three inputs `canonFoldOK_delta` still carries, discharged from Skeleton 3's
premise vocabulary (closures of `ev₁`/`ev₂`, perms, `respects`):

* `lcaClosed_deps` — the LCA set is dependency-closed: `DepC ⊆ vis` and `ev₁ ∩ ev₂` is
  `vis`-backward-closed (intersection of two closed sets).
* `deltaDeps_discharge` (via `delta_chain_forward`) — the per-position delta closure `hδdeps`:
  a dependency of a delta op is either an LCA op (∈ ρ₀) or an EARLIER delta op (∈ pre).  The
  mechanism: a `DepE`-edge never crosses from the delta INTO the LCA (`vis`-closure would pull the
  source into both branches), so a dependency chain ending at a delta op stays wholly inside the
  delta, where `respects π₀ (loOnA …)` forces every edge forward — by `List.pairwise_append` /
  `pairwise_cons` cross-clauses, no index arithmetic.
* `exists_loOnA_perm` — the freely-chosen ambient enumeration `U` exists: `loOnA ⊆ vis` and `vis`
  is a strict order, so the generic topological sort applies (mirror of `exists_loOnEq_enum`).
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
open Classical

namespace Sal.ConditionedMRDTs.RGAK1Delta

variable {α : Type} [DecidableEq α] [Inhabited α]

open Sal.Emulation
open Sal.ConditionedMRDTs.RGASig (RGACondSig)
open Sal.ConditionedMRDTs.ConditionedConvergence (loOnA)
open RGAMergeLinearization (applySeqR)
open RGACanonConvergence (CanonFoldOK)
open Sal.ConditionedMRDTs.RGACanonFoldOK
open Sal.ConditionedMRDTs.RGADeltaEnum (exists_min_of_irrefl_trans)
open Sal.ConditionedMRDTs.ConditionedExecutionModel.ConditionedConfiguration (exists_respecting)

/-! ## §1  Dependency-chain structure across the LCA/delta split -/

/-- The source of a transitive dependency is a delivered event. -/
theorem depC_src_mem (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (E : Set (op_t α)) (z o : op_t α) (h : DepC Cfg E z o) : z ∈ E := by
  induction h with
  | single h => exact h.1
  | tail _ _ ih => exact ih

/-- **No dependency edge crosses from outside the LCA into it.**  If `DepE u v` and
`v ∈ ev₁ ∩ ev₂`, then `u ∈ ev₁ ∩ ev₂`: the edge is a `vis` edge, and both branch sets are
`vis`-backward-closed. -/
theorem depE_into_lca (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (ev₁ ev₂ : Set (op_t α))
    (hcl1 : ∀ a b : op_t α, Cfg.vis a b → b ∈ ev₁ → a ∈ ev₁)
    (hcl2 : ∀ a b : op_t α, Cfg.vis a b → b ∈ ev₂ → a ∈ ev₂)
    (u v : op_t α) (h : DepE Cfg (ev₁ ∪ ev₂) u v) (hv : v ∈ ev₁ ∩ ev₂) :
    u ∈ ev₁ ∩ ev₂ := by
  have hvis : Cfg.vis u v := depE_imp_vis Cfg (ev₁ ∪ ev₂) u v h
  exact ⟨hcl1 u v hvis hv.1, hcl2 u v hvis hv.2⟩

/-- **A dependency chain into a delta op stays in the delta and points backward.**  For
`o` in the split `pre ++ o :: post` of a `loOnA`-respecting delta enumeration, any transitive
dependency `z` of `o` that lies in the delta is in `pre`: the chain never enters the LCA
(`depE_into_lca` would pull it out of the delta), so every link is between enumeration members,
where `respects` forces each edge forward. -/
theorem delta_chain_forward (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (ev₁ ev₂ : Set (op_t α))
    (htr : ∀ {a b c : op_t α}, Cfg.vis a b → Cfg.vis b c → Cfg.vis a c)
    (hirr : ∀ a : op_t α, ¬ Cfg.vis a a)
    (hcl1 : ∀ a b : op_t α, Cfg.vis a b → b ∈ ev₁ → a ∈ ev₁)
    (hcl2 : ∀ a b : op_t α, Cfg.vis a b → b ∈ ev₂ → a ∈ ev₂)
    (pre post : List (op_t α)) (o : op_t α)
    (hπr : respects (pre ++ o :: post) (loOnA (RGACondSig α) Cfg (ev₁ ∪ ev₂)))
    (hDmem : ∀ x ∈ (ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂), x ∈ pre ++ o :: post)
    (z : op_t α) (hzD : z ∈ (ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))
    (hdep : DepC Cfg (ev₁ ∪ ev₂) z o) :
    z ∈ pre := by
  obtain ⟨hcrossP, hop⟩ := List.pairwise_append.mp hπr
  have hopost : ∀ b ∈ post, ¬ loOnA (RGACondSig α) Cfg (ev₁ ∪ ev₂) b o :=
    fun b hb => (List.pairwise_cons.mp hop.1).1 b hb
  have hcross : ∀ a ∈ pre, ∀ b ∈ o :: post,
      ¬ loOnA (RGACondSig α) Cfg (ev₁ ∪ ev₂) b a := hop.2
  -- head-first induction along the chain, motive: a delta source lies in `pre`
  revert hzD
  induction hdep using Relation.TransGen.head_induction_on with
  | single h =>
    -- single edge z' → o
    rename_i z'
    intro hzD
    rcases List.mem_append.mp (hDmem z' hzD) with hpre | hrest
    · exact hpre
    · rcases List.mem_cons.mp hrest with rfl | hpost
      · exact absurd (loOnA_imp_vis Cfg _ _ _ h.2) (hirr z')
      · exact absurd h.2 (hopost z' hpost)
  | head h' hc ihc =>
    -- edge z' → c, chain c →* o
    rename_i z' c
    intro hzD
    -- c is a delta member: an edge into the LCA would pull z' out of the delta
    have hcE : c ∈ ev₁ ∪ ev₂ := depC_src_mem Cfg (ev₁ ∪ ev₂) c o hc
    have hcD : c ∈ (ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂) := by
      refine ⟨hcE, fun hcL => ?_⟩
      exact hzD.2 (depE_into_lca Cfg ev₁ ev₂ hcl1 hcl2 z' c h' hcL)
    have hcpre : c ∈ pre := ihc hcD
    rcases List.mem_append.mp (hDmem z' hzD) with hpre | hrest
    · exact hpre
    · rcases List.mem_cons.mp hrest with rfl | hpost
      · exact absurd (Relation.TransGen.head h' hc)
          (depC_irrefl Cfg (ev₁ ∪ ev₂) htr hirr z')
      · exact absurd h'.2 (hcross c hcpre z' (List.mem_cons_of_mem o hpost))

/-! ## §2  The two closure discharges -/

/-- **The LCA set is dependency-closed** — `hρclosed` of `canonFoldOK_delta`. -/
theorem lcaClosed_deps (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (ev₁ ev₂ : Set (op_t α))
    (htr : ∀ {a b c : op_t α}, Cfg.vis a b → Cfg.vis b c → Cfg.vis a c)
    (hcl1 : ∀ a b : op_t α, Cfg.vis a b → b ∈ ev₁ → a ∈ ev₁)
    (hcl2 : ∀ a b : op_t α, Cfg.vis a b → b ∈ ev₂ → a ∈ ev₂)
    (ρ₀ : List (op_t α)) (hρp : listPermOf ρ₀ (ev₁ ∩ ev₂)) :
    ∀ w ∈ ρ₀, ∀ z ∈ (ev₁ ∪ ev₂), z ≠ w → DepC Cfg (ev₁ ∪ ev₂) z w → z ∈ ρ₀ := by
  intro w hw z _hz _hzw hdep
  have hwL : w ∈ ev₁ ∩ ev₂ := (hρp.2 w).mp hw
  have hvis : Cfg.vis z w := depC_imp_vis Cfg (ev₁ ∪ ev₂) htr z w hdep
  exact (hρp.2 z).mpr ⟨hcl1 z w hvis hwL.1, hcl2 z w hvis hwL.2⟩

/-- **The per-position delta closure** — `hδdeps` of `canonFoldOK_delta`: a dependency of a
delta op is an LCA op or an earlier delta op. -/
theorem deltaDeps_discharge (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (ev₁ ev₂ : Set (op_t α))
    (htr : ∀ {a b c : op_t α}, Cfg.vis a b → Cfg.vis b c → Cfg.vis a c)
    (hirr : ∀ a : op_t α, ¬ Cfg.vis a a)
    (hcl1 : ∀ a b : op_t α, Cfg.vis a b → b ∈ ev₁ → a ∈ ev₁)
    (hcl2 : ∀ a b : op_t α, Cfg.vis a b → b ∈ ev₂ → a ∈ ev₂)
    (ρ₀ π₀ : List (op_t α))
    (hρp : listPermOf ρ₀ (ev₁ ∩ ev₂))
    (hπp : listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)))
    (hπr : respects π₀ (loOnA (RGACondSig α) Cfg (ev₁ ∪ ev₂))) :
    ∀ pre o post, π₀ = pre ++ o :: post →
      ∀ z ∈ (ev₁ ∪ ev₂), z ≠ o → DepC Cfg (ev₁ ∪ ev₂) z o → z ∈ ρ₀ ++ pre := by
  intro pre o post hsplit z hz _hzo hdep
  by_cases hzL : z ∈ ev₁ ∩ ev₂
  · exact List.mem_append_left _ ((hρp.2 z).mpr hzL)
  · refine List.mem_append_right _ ?_
    rw [hsplit] at hπr
    exact delta_chain_forward Cfg ev₁ ev₂ htr hirr hcl1 hcl2 pre post o hπr
      (fun x hx => hsplit ▸ (hπp.2 x).mpr hx) z ⟨hz, hzL⟩ hdep

/-! ## §3  The ambient `loOnA`-respecting enumeration exists -/

/-- A `loOnA`-respecting enumeration of any finitely-listed event set exists: `loOnA ⊆ vis`
and `vis` is a strict order, so a `vis`-minimal element is `loOnA`-minimal and the generic
topological sort applies. -/
theorem exists_loOnA_perm (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (E : Set (op_t α)) (lE : List (op_t α)) (hnd : lE.Nodup) (henum : ∀ a, a ∈ lE ↔ a ∈ E)
    (htr : ∀ {a b c : op_t α}, Cfg.vis a b → Cfg.vis b c → Cfg.vis a c)
    (hirr : ∀ a : op_t α, ¬ Cfg.vis a a) :
    ∃ U, listPermOf U E ∧ respects U (loOnA (RGACondSig α) Cfg E) := by
  obtain ⟨U, hperm, hpw⟩ := exists_respecting (loOnA (RGACondSig α) Cfg E) lE.length lE rfl
    (fun l' _ hne => by
      obtain ⟨m, hm, hmin⟩ := exists_min_of_irrefl_trans Cfg.vis (@htr) hirr l' hne
      exact ⟨m, hm, fun y hy hlo => hmin y hy (loOnA_imp_vis Cfg E y m hlo)⟩)
  refine ⟨U, ⟨hperm.nodup_iff.mpr hnd, fun a => ?_⟩, hpw⟩
  rw [hperm.mem_iff]; exact henum a

/-! ## §4  The K1 bundle -/

/-- **K1, assembled.**  `CanonFoldOK ρ₀ (fold ρ₀) π₀` — Skeleton 3's delta-discipline
leaf — from the honest residual only:

* `hGen : GenDisc2C Cfg (ev₁ ∪ ev₂)` — each event accurate at its own dependency fold (the
  born-applicable generation content);
* `hρOK : CanonFoldOK [] (init_st (α := α)) ρ₀` — the LCA's own discipline (the existing noopFeasible
  engine route on the born-applicable `ρ₀`);
* `hπr : respects π₀ (loOnA …)` — the delta enum is causally sorted (constructible: any
  `vis`-topological sort works, since `loOnA ⊆ vis`);
* the execution-model facts (`hdts`/`hids0`/strict `vis`/branch closures).

Everything else — the ambient enumeration, the dependency closures, the per-position delta
closure — is derived. NO order hypothesis on `ρ₀`; NO feasibility at the LCA-first fold. -/
theorem K1_canonFoldOK (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (ev₁ ev₂ : Set (op_t α))
    (htr : ∀ {a b c : op_t α}, Cfg.vis a b → Cfg.vis b c → Cfg.vis a c)
    (hirr : ∀ a : op_t α, ¬ Cfg.vis a a)
    (hcl1 : ∀ a b : op_t α, Cfg.vis a b → b ∈ ev₁ → a ∈ ev₁)
    (hcl2 : ∀ a b : op_t α, Cfg.vis a b → b ∈ ev₂ → a ∈ ev₂)
    (hdts : ∀ a b : op_t α, a ∈ ev₁ ∪ ev₂ → b ∈ ev₁ ∪ ev₂ → a ≠ b → a.1 ≠ b.1)
    (hids0 : ∀ o ∈ ev₁ ∪ ev₂, o.1 ≠ 0)
    (hGen : GenDisc2C Cfg (ev₁ ∪ ev₂))
    (ρ₀ π₀ : List (op_t α))
    (hρp : listPermOf ρ₀ (ev₁ ∩ ev₂))
    (hπp : listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)))
    (hπr : respects π₀ (loOnA (RGACondSig α) Cfg (ev₁ ∪ ev₂)))
    (hρOK : CanonFoldOK [] (init_st (α := α)) ρ₀) :
    CanonFoldOK ρ₀ (applySeqR (init_st (α := α)) ρ₀) π₀ := by
  -- the union list and its set algebra
  have hmem : ∀ o, o ∈ ρ₀ ++ π₀ ↔ o ∈ ev₁ ∪ ev₂ := by
    intro o
    rw [List.mem_append, hρp.2 o, hπp.2 o]
    constructor
    · rintro (h | h)
      · exact Set.mem_union_left _ h.1
      · exact h.1
    · intro h
      by_cases hI : o ∈ ev₁ ∩ ev₂
      · exact Or.inl hI
      · exact Or.inr ⟨h, hI⟩
  have hnd : (ρ₀ ++ π₀).Nodup := by
    refine List.nodup_append.mpr ⟨hρp.1, hπp.1, ?_⟩
    intro a ha b hb heq
    exact ((hπp.2 b).mp hb).2 (heq ▸ (hρp.2 a).mp ha)
  -- the ambient loOnA-respecting enumeration
  obtain ⟨U, hUp, hUr⟩ := exists_loOnA_perm Cfg (ev₁ ∪ ev₂) (ρ₀ ++ π₀) hnd hmem htr hirr
  -- assemble
  exact canonFoldOK_delta Cfg (ev₁ ∪ ev₂) hdts hids0 hGen htr hirr U hUp hUr ρ₀ π₀
    (fun x hx => Set.mem_union_left _ ((hρp.2 x).mp hx).1)
    (fun x hx => ((hπp.2 x).mp hx).1)
    hnd hρOK
    (lcaClosed_deps Cfg ev₁ ev₂ htr hcl1 hcl2 ρ₀ hρp)
    (deltaDeps_discharge Cfg ev₁ ev₂ htr hirr hcl1 hcl2 ρ₀ π₀ hρp hπp hπr)

/-! ## Axiom audit -/

#print axioms delta_chain_forward
#print axioms lcaClosed_deps
#print axioms deltaDeps_discharge
#print axioms exists_loOnA_perm
#print axioms K1_canonFoldOK

end Sal.ConditionedMRDTs.RGAK1Delta
