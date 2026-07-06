import Sal.MRDTs.Metatheory.Adequacy
import Sal.MRDTs.Metatheory.Development.GenericEqQuotient_NF
import Sal.MRDTs.Metatheory.Development.BornApplicable_Guard

/-!
# The born-applicable reachability invariant `GoodConfig3NF` (datatype-side)

*Additive; modifies no existing file; 0 `sorry`.*

The `≈`-route reachability invariant that carries a BORN-APPLICABLE canonical
witness for every version.  `GoodConfig3NF = GoodConfig3 ∧ canonicalNF`, where

  `canonicalNF v s Ev : ∃ σ hσ, s = qmk σ hσ ∧ IsCanonicalStateEqNF (core C).vis Ev σ`

i.e. each version's class `s` is `qmk` of a representative `σ` that has a
`noopFeasible` (over the RAW `do_` fold) canonical witness.  This is the
DATATYPE-side design (`IsCanonicalStateEqNF`, over `D`).

The exec-side alternative (`noopFeasible` over the guarded `qdo`) was found VACUOUS
(`appOrNoop_qsig` makes every `QSig` step `appOrNoop` unconditionally), so it could
not feed `EqJoinLemma3C_NF`; the datatype-side clause is the meaningful one and lets
the merge feed the NF join DIRECTLY (via `qmergeL_qmk`, no bridge).

* apply — `isCanonicalStateNF_extend` (via `isCanonicalStateEqNF_extend`), with a
  per-apply honest premise `qapplicable e s` (the client applies `e` where it is
  applicable) and `hgenW : applicable e ⟹ W e` (from `e`'s genuineness).
* merge — `goodConfig3NF_merge_of_canonical` (store bookkeeping) + `h_mergedNF` from
  the NF join (`EqJoinLemma3C_NF`, gated on the merge residual WALL 1).
-/

set_option maxHeartbeats 1000000

namespace Sal.Metatheory.GoodConfig3NF

open Sal.Emulation
open Sal.Metatheory.GenericEqQuotient
open Sal.Metatheory.UpdateFeasibilityGate (noopFeasible)

variable {D : ConditionedMRDTSig}

/-! ## §1  `IsCanonicalStateNF` and its lemmas -/

/-- **Born-applicable canonical state (datatype-side).**  The version class `q` is
`qmk` of a representative `σ` carrying a `noopFeasible` datatype witness. -/
def IsCanonicalStateNF (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (Cq : Sal.Emulation.Configuration (QSig E W hP hC hA).toCRDTSig)
    (ev : Set (Op D.AppOp)) (q : QState D E) : Prop :=
  ∃ (σ : D.State) (hσ : D.Inv σ),
    q = qmk E σ hσ ∧ IsCanonicalStateEqNF E W Cq.vis ev σ

/-- Drop the feasibility clause: a born-applicable canonical state is a canonical
state (via `isCanonicalState_of_NF`, `hWA : applicable ⟹ W` on `ev`). -/
theorem isCanonicalState_of_NFcls (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (Cq : Sal.Emulation.Configuration (QSig E W hP hC hA).toCRDTSig)
    (ev : Set (Op D.AppOp)) (q : QState D E)
    (hWA : ∀ o ∈ ev, ∀ s', D.applicable o s' → W o s')
    (h : IsCanonicalStateNF E W hP hC hA Cq ev q) :
    Sal.Emulation.IsCanonicalState Cq ev q := by
  obtain ⟨σ, hσ, hq, hcs⟩ := h
  rw [hq]
  exact isCanonicalState_of_NF E W hP hC hA Cq ev hWA σ hσ hcs

/-- Transport under `vis`-agreement: the representative and the `qmk` relation are
`vis`-independent; only the datatype witness transports (`isCanonicalStateEqNF_congr`). -/
theorem isCanonicalStateNF_congr (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    {Cq Cq' : Sal.Emulation.Configuration (QSig E W hP hC hA).toCRDTSig}
    {ev : Set (Op D.AppOp)} {q : QState D E}
    (h_vis : ∀ a ∈ ev, ∀ b ∈ ev, (Cq'.vis a b ↔ Cq.vis a b))
    (h : IsCanonicalStateNF E W hP hC hA Cq ev q) :
    IsCanonicalStateNF E W hP hC hA Cq' ev q := by
  obtain ⟨σ, hσ, hq, hcs⟩ := h
  exact ⟨σ, hσ, hq, isCanonicalStateEqNF_congr E W h_vis hcs⟩

/-- **The apply-step extension.**  Extend the parent's born-applicable witness by
the fresh, `vis`-maximal event `e`, applied where it is `qapplicable`.  The new
version class is `qdo q e = qmk (do_ σ e)` (guard fires, `W e σ` from `hgenW`), and
the datatype witness extends by `isCanonicalStateEqNF_extend`. -/
theorem isCanonicalStateNF_extend (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (hInvCong : ∀ {s s' : D.State}, E.eqv s s' → D.Inv s → D.Inv s')
    (Cq : Sal.Emulation.Configuration (QSig E W hP hC hA).toCRDTSig)
    (ev : Set (Op D.AppOp)) (q : QState D E) (e : Op D.AppOp)
    (hgenW : ∀ s : D.State, D.applicable e s → W e s)
    (h_e_fresh : e ∉ ev)
    (h_e_sees : ∀ x ∈ ev, Cq.vis x e)
    (h_e_last : ∀ x ∈ ev, ¬ Cq.vis e x)
    (hqapp : qapplicable E W hA e q)
    (h : IsCanonicalStateNF E W hP hC hA Cq ev q) :
    IsCanonicalStateNF E W hP hC hA Cq (insert e ev)
      ((QSig E W hP hC hA).toCRDTSig.update q e) := by
  obtain ⟨σ, hσ, hq, hcs⟩ := h
  have happ : D.applicable e σ := by rw [hq] at hqapp; exact hqapp
  have hW : W e σ := hgenW σ happ
  refine ⟨D.update σ e, hP.inv_update σ e hσ hW, ?_, ?_⟩
  · rw [hq]
    show qdo E W hP hC hA (qmk E σ hσ) e = qmk E (D.update σ e) (hP.inv_update σ e hσ hW)
    rw [qdo_qmk]
    refine (qmk_eq_iff E).mpr ?_
    rw [show doW D W e σ = D.update σ e from if_pos hW]
    exact E.equiv.refl _
  · exact isCanonicalStateEqNF_extend E W hC hA hInvCong Cq.vis ev σ hσ e
      h_e_fresh h_e_sees h_e_last happ hcs

/-! ## §2  The invariant and the result direction -/

/-- **The born-applicable reachability invariant.**  `GoodConfig3` plus a
datatype-side `noopFeasible` canonical witness for every version. -/
def GoodConfig3NF (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (C : Sal.Metatheory.Configuration (QSig E W hP hC hA)) : Prop :=
  Sal.Metatheory.GoodConfig3 C ∧
  ∀ (v : Sal.Metatheory.Version) (s : QState D E) (Ev : Set (Op D.AppOp)),
    C.ver v = some (s, Ev) →
    IsCanonicalStateNF E W hP hC hA (Sal.Metatheory.Configuration.core C) Ev s

/-- **`GoodConfig3NF ⟹ IsRALinearizable3`** — carries `GoodConfig3`, so immediate. -/
theorem isRALinearizable3_of_goodNF (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (C : Sal.Metatheory.Configuration (QSig E W hP hC hA))
    (h : GoodConfig3NF E W hP hC hA C) :
    Sal.Metatheory.IsRALinearizable3 C :=
  Sal.Metatheory.isRALinearizable3_of_good h.1

/-! ## §3  Step preservations -/

/-- **Init satisfies `GoodConfig3NF`.**  Version `0 = (init, ∅)`: witness `[]`. -/
theorem goodConfig3NF_init (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W) :
    GoodConfig3NF E W hP hC hA
      (Sal.Metatheory.initConfig (QSig E W hP hC hA) trivial) := by
  refine ⟨Sal.Metatheory.goodConfig3_init trivial, ?_⟩
  intro v s' E' hv
  have hver : (Sal.Metatheory.initConfig (QSig E W hP hC hA) trivial).ver v
      = if v = 0 then some ((QSig E W hP hC hA).init, (∅ : Set (Op D.AppOp)))
        else none := rfl
  rw [hver] at hv
  by_cases hv0 : v = 0
  · rw [if_pos hv0, Option.some.injEq, Prod.mk.injEq] at hv
    rw [← hv.1, ← hv.2]
    refine ⟨D.init, hP.inv_init, rfl, ?_⟩
    exact ⟨[], ⟨List.nodup_nil, fun a => by simp⟩, List.Pairwise.nil, trivial,
      E.equiv.refl _⟩
  · rw [if_neg hv0] at hv; simp at hv

/-- **CreateReplica preserves `GoodConfig3NF`.**  Store and `vis` unchanged. -/
theorem goodConfig3NF_createReplica (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    {C C' : Sal.Metatheory.Configuration (QSig E W hP hC hA)}
    {r : Sal.Emulation.Replica}
    (h_fresh : C.N r = none)
    (hL : C'.L = Sal.Emulation.updateRep C.L r ∅)
    (hvis : C'.vis = C.vis)
    (hver : C'.ver = C.ver)
    (h : GoodConfig3NF E W hP hC hA C) :
    GoodConfig3NF E W hP hC hA C' := by
  refine ⟨Sal.Metatheory.goodConfig3_createReplica h_fresh hL hvis hver h.1, ?_⟩
  intro w s' E' hw
  rw [hver] at hw
  exact isCanonicalStateNF_congr E W hP hC hA
    (fun a _ b _ => by rw [Sal.Metatheory.core_vis, Sal.Metatheory.core_vis, hvis])
    (h.2 w s' E' hw)

/-- **Apply preserves `GoodConfig3NF`.**  The fresh event extends the parent's
born-applicable witness; `hqapp`/`hgenW` are the born-applicable honest-execution
conditions (client applies `e` where applicable; `e` genuine ⟹ `applicable ⟹ W`). -/
theorem goodConfig3NF_apply (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (hInvCong : ∀ {s s' : D.State}, E.eqv s s' → D.Inv s → D.Inv s')
    {C C' : Sal.Metatheory.Configuration (QSig E W hP hC hA)}
    {t : Sal.Emulation.Timestamp} {r : Sal.Emulation.Replica} {oo : D.AppOp}
    {v : Sal.Metatheory.Version} {s : QState D E} {ev : Set (Op D.AppOp)}
    {vnew : Sal.Metatheory.Version}
    (hgenW : ∀ s' : D.State, D.applicable (t, r, oo) s' → W (t, r, oo) s')
    (h_head : C.head r = some v)
    (h_ver : C.ver v = some (s, ev))
    (h_fresh_t : ∀ e', e' ∈ C.events → Sal.Emulation.Op.time e' ≠ t)
    (h_vnew : C.ver vnew = none)
    (hL : C'.L = Sal.Emulation.updateRep C.L r (ev ∪ {(t, r, oo)}))
    (hvis : C'.vis = fun a b => C.vis a b ∨ (ev a ∧ b = (t, r, oo)))
    (hver : C'.ver = fun w => if w = vnew
      then some ((QSig E W hP hC hA).update s (t, r, oo), ev ∪ {(t, r, oo)})
      else C.ver w)
    (hqapp : qapplicable E W hA (t, r, oo) s)
    (h : GoodConfig3NF E W hP hC hA C) :
    GoodConfig3NF E W hP hC hA C' := by
  refine ⟨Sal.Metatheory.goodConfig3_apply h_head h_ver h_fresh_t h_vnew hL hvis hver h.1, ?_⟩
  set e : Op D.AppOp := (t, r, oo) with he_def
  have hco := C.head_coherent r v h_head
  have hLr : C.L r = some ev := by rw [← hco.2, h_ver]; rfl
  have he_not_events : e ∉ C.events := fun hmem => h_fresh_t _ hmem rfl
  have h_ev_events : ∀ x ∈ ev, x ∈ C.events := fun x hx => ⟨r, ev, hLr, hx⟩
  have he_not_ev : e ∉ ev := fun hmem => he_not_events (h_ev_events e hmem)
  have h_no_vis_out : ∀ x, ¬ C.vis e x := by
    intro x hx
    obtain ⟨r₀, s₀, hL₀, hs₀⟩ := C.vis_src hx
    exact he_not_events ⟨r₀, s₀, hL₀, hs₀⟩
  have hver_new : C'.ver vnew = some ((QSig E W hP hC hA).update s e, ev ∪ {e}) := by
    rw [hver]; simp
  have hver_old : ∀ w, w ≠ vnew → C'.ver w = C.ver w := by
    intro w hw; rw [hver]; simp [hw]
  have h_vis_old : ∀ (E' : Set (Op D.AppOp)), (∀ x ∈ E', x ∈ C.events) →
      ∀ a, a ∈ E' → ∀ b, b ∈ E' → ((C.core).vis a b ↔ (C'.core).vis a b) := by
    intro E' hsub a _ b hb
    rw [Sal.Metatheory.core_vis, Sal.Metatheory.core_vis, hvis]
    constructor
    · exact Or.inl
    · rintro (hab | ⟨_, rfl⟩)
      · exact hab
      · exact absurd (hsub _ hb) he_not_events
  intro w s' E' hw
  by_cases hwn : w = vnew
  · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
    rw [← hw.1, ← hw.2]
    have h_old : IsCanonicalStateNF E W hP hC hA (C.core) ev s := h.2 v s ev h_ver
    have h_old' : IsCanonicalStateNF E W hP hC hA (C'.core) ev s :=
      isCanonicalStateNF_congr E W hP hC hA
        (fun a ha b hb => (h_vis_old ev h_ev_events a ha b hb).symm) h_old
    have h_ext := isCanonicalStateNF_extend E W hP hC hA hInvCong (C'.core) ev s e
      hgenW he_not_ev
      (fun x hx => by
        rw [Sal.Metatheory.core_vis, hvis]; exact Or.inr ⟨hx, rfl⟩)
      (fun x hx => by
        rw [Sal.Metatheory.core_vis, hvis]
        rintro (hex | ⟨he_ev, _⟩)
        · exact h_no_vis_out x hex
        · exact he_not_ev he_ev)
      hqapp h_old'
    rw [Set.union_singleton]
    exact h_ext
  · rw [hver_old w hwn] at hw
    have h_old : IsCanonicalStateNF E W hP hC hA (C.core) E' s' := h.2 w s' E' hw
    exact isCanonicalStateNF_congr E W hP hC hA
      (fun a ha b hb => (h_vis_old E' (h.1.ver_events_sub w s' E' hw) a ha b hb).symm) h_old

/-- **Merge preserves `GoodConfig3NF`, given the merged born-applicable canonical
state.**  The store-bookkeeping half of the NF merge (design-agnostic in
`h_mergedNF`). -/
theorem goodConfig3NF_merge_of_canonical (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    {C C' : Sal.Metatheory.Configuration (QSig E W hP hC hA)}
    {r₁ : Sal.Emulation.Replica} {v₁ v₂ vm : Sal.Metatheory.Version}
    {s₁ s₂ sT : QState D E} {ev₁ ev₂ : Set (Op D.AppOp)}
    (h_head₁ : C.head r₁ = some v₁)
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂))
    (hL : C'.L = Sal.Emulation.updateRep C.L r₁ (ev₁ ∪ ev₂))
    (hvis : C'.vis = C.vis)
    (hver : C'.ver = fun w => if w = vm
      then some ((QSig E W hP hC hA).mergeL sT s₁ s₂, ev₁ ∪ ev₂) else C.ver w)
    (h : GoodConfig3NF E W hP hC hA C)
    (hWA : ∀ o ∈ ev₁ ∪ ev₂, ∀ s', D.applicable o s' → W o s')
    (h_mergedNF : IsCanonicalStateNF E W hP hC hA (C.core) (ev₁ ∪ ev₂)
      ((QSig E W hP hC hA).mergeL sT s₁ s₂)) :
    GoodConfig3NF E W hP hC hA C' := by
  refine ⟨goodConfig3_merge_of_canonical h_head₁ h_ver₁ h_ver₂ hL hvis hver
    h.1 (isCanonicalState_of_NFcls E W hP hC hA _ _ _ hWA h_mergedNF), ?_⟩
  have hver_new : C'.ver vm
      = some ((QSig E W hP hC hA).mergeL sT s₁ s₂, ev₁ ∪ ev₂) := by rw [hver]; simp
  have hver_old : ∀ w, w ≠ vm → C'.ver w = C.ver w := by
    intro w hw; rw [hver]; simp [hw]
  have h_sameNF : ∀ (E' : Set (Op D.AppOp)) (s' : QState D E),
      IsCanonicalStateNF E W hP hC hA (C.core) E' s' →
      IsCanonicalStateNF E W hP hC hA (C'.core) E' s' :=
    fun E' s' hcs => isCanonicalStateNF_congr E W hP hC hA
      (fun a _ b _ => by rw [Sal.Metatheory.core_vis, Sal.Metatheory.core_vis, hvis]) hcs
  intro w s' E' hw
  by_cases hwn : w = vm
  · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
    rw [← hw.1, ← hw.2]
    exact h_sameNF _ _ h_mergedNF
  · rw [hver_old w hwn] at hw
    exact h_sameNF E' s' (h.2 w s' E' hw)

/-- **The NF join: merged born-applicable canonical state from `EqJoinLemma3C_NF`.**
With the datatype-side design the join is DIRECT — no exec↔datatype bridge:
extract the three representatives, apply `EqJoinLemma3C_NF` to them, and repackage
via `qmergeL_qmk`.  This supplies `h_mergedNF` to `goodConfig3NF_merge_of_canonical`.
Gated only on `EqJoinLemma3C_NF` (the RGA's merge residual, WALL 1). -/
theorem mergedNF_of_join (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (hJoinNF : EqJoinLemma3C_NF D E W)
    (Cq : Sal.Emulation.Configuration (QSig E W hP hC hA).toCRDTSig)
    (events ev₁ ev₂ : Set (Op D.AppOp)) (sT s₁ s₂ : QState D E)
    (htr : ∀ {a b c : Op D.AppOp}, Cq.vis a b → Cq.vis b c → Cq.vis a c)
    (hir : ∀ a : Op D.AppOp, ¬ Cq.vis a a)
    (hdts : ∀ a b : Op D.AppOp, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1)
    (hsub₁ : ∀ a ∈ ev₁, a ∈ events) (hsub₂ : ∀ a ∈ ev₂, a ∈ events)
    (hcl₁ : fullClosureRel Cq.vis ev₁) (hcl₂ : fullClosureRel Cq.vis ev₂)
    (hcT : IsCanonicalStateNF E W hP hC hA Cq (ev₁ ∩ ev₂) sT)
    (hc₁ : IsCanonicalStateNF E W hP hC hA Cq ev₁ s₁)
    (hc₂ : IsCanonicalStateNF E W hP hC hA Cq ev₂ s₂) :
    IsCanonicalStateNF E W hP hC hA Cq (ev₁ ∪ ev₂)
      ((QSig E W hP hC hA).mergeL sT s₁ s₂) := by
  obtain ⟨σT, hσT, hqT, hcsT⟩ := hcT
  obtain ⟨σ₁, hσ₁, hq₁, hcs₁⟩ := hc₁
  obtain ⟨σ₂, hσ₂, hq₂, hcs₂⟩ := hc₂
  refine ⟨D.mergeL σT σ₁ σ₂, hP.inv_mergeL σT σ₁ σ₂ hσT hσ₁ hσ₂, ?_, ?_⟩
  · rw [hqT, hq₁, hq₂]; rfl
  · exact hJoinNF Cq.vis events ev₁ ev₂ σT σ₁ σ₂ hσT hσ₁ hσ₂
      htr hir hdts hsub₁ hsub₂ hcl₁ hcl₂ hcsT hcs₁ hcs₂

/-- **The full merge step.**  Mirrors `goodConfig3_merge_wfgen`, but derives the
merged canonical from `mergedNF_of_join` (NF join, `EqJoinLemma3C_NF` direct) — no
`GenDisc`, no `GDSupply`, no `WfOpReachable`.  The LCA canonical is delivered by
`lca_events` + `canonicalNF`; closures by `ver_causal`/`ver_events_sub`. -/
theorem goodConfig3NF_merge (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (hJoinNF : EqJoinLemma3C_NF D E W)
    {C C' : Sal.Metatheory.Configuration (QSig E W hP hC hA)}
    {r₁ : Sal.Emulation.Replica} {v₁ v₂ vT vm : Sal.Metatheory.Version}
    {s₁ s₂ sT : QState D E} {ev₁ ev₂ evT : Set (Op D.AppOp)}
    (h_head₁ : C.head r₁ = some v₁)
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂))
    (h_lca : Sal.Metatheory.IsLCA C.parents v₁ v₂ vT)
    (h_verT : C.ver vT = some (sT, evT))
    (hL : C'.L = Sal.Emulation.updateRep C.L r₁ (ev₁ ∪ ev₂))
    (hvis : C'.vis = C.vis)
    (hver : C'.ver = fun w => if w = vm
      then some ((QSig E W hP hC hA).mergeL sT s₁ s₂, ev₁ ∪ ev₂) else C.ver w)
    (hWA : ∀ o ∈ ev₁ ∪ ev₂, ∀ s', D.applicable o s' → W o s')
    (h : GoodConfig3NF E W hP hC hA C) :
    GoodConfig3NF E W hP hC hA C' := by
  have hcTNF : IsCanonicalStateNF E W hP hC hA (C.core) (ev₁ ∩ ev₂) sT := by
    rw [← C.lca_events h_lca h_ver₁ h_ver₂ h_verT]
    exact h.2 vT sT evT h_verT
  have hcl₁f : fullClosureRel (C.core).vis ev₁ :=
    fun a b hab hb => h.1.ver_causal v₁ s₁ ev₁ h_ver₁ a b hab hb
  have hcl₂f : fullClosureRel (C.core).vis ev₂ :=
    fun a b hab hb => h.1.ver_causal v₂ s₂ ev₂ h_ver₂ a b hab hb
  have hsub₁ : ∀ a ∈ ev₁, a ∈ (C.core).events := h.1.ver_events_sub v₁ s₁ ev₁ h_ver₁
  have hsub₂ : ∀ a ∈ ev₂, a ∈ (C.core).events := h.1.ver_events_sub v₂ s₂ ev₂ h_ver₂
  -- the ONE generic execution fact the datatype Join consumes: distinct events have distinct ids,
  -- straight from the reachable config's `timestamps_distinct` (each event is witnessed).
  have hdts : ∀ a b : Op D.AppOp,
      a ∈ (C.core).events → b ∈ (C.core).events → a ≠ b → a.1 ≠ b.1 := by
    intro a b ha hb hne
    obtain ⟨r, s, hLr, hsa⟩ := ha
    obtain ⟨r', s', hLr', hsb⟩ := hb
    exact (C.core).timestamps_distinct hLr hsa hLr' hsb hne
  have h_mergedNF := mergedNF_of_join E W hP hC hA hJoinNF (C.core) (C.core).events
    ev₁ ev₂ sT s₁ s₂
    (fun hab hbc => h.1.vis_trans hab hbc) (fun a ha => h.1.vis_irrefl a ha) hdts
    hsub₁ hsub₂ hcl₁f hcl₂f hcTNF (h.2 v₁ s₁ ev₁ h_ver₁) (h.2 v₂ s₂ ev₂ h_ver₂)
  exact goodConfig3NF_merge_of_canonical E W hP hC hA h_head₁ h_ver₁ h_ver₂ hL hvis hver
    h hWA h_mergedNF

/-! ## §5  The reachability induction and the top-level metatheorem

`goodConfig3NF_of_reachF` mirrors `goodConfig3_of_reachF_wfgen`, but over the
datatype-side invariant.  It threads TWO honest-execution conditions:
`hgenW` (per-event `applicable ⟹ W`, weakened along the trace like `hGenC`) and
`hBA` — the BORN-APPLICABLE delivery discipline: on every reachable apply step the
applied op is `qapplicable` at the head ("clients issue ops honest about the state
they are applied to").  `hBA` is the honest-execution hypothesis the datatype-side
(RAW-fold) canonical witness genuinely requires (the guarded fold hid it via
skip). -/

open Sal.Metatheory (Configuration Step3 Label3 IsLCA initConfig) in
/-- **`GoodConfig3NF` from born-applicable reachability.**  Gated on
`EqJoinLemma3C_NF` (the merge residual, WALL 1) and the honest conditions
`hgenW`/`hBA`.  No `GenDisc`, no `GDSupply`, no `WfOpReachable`. -/
theorem goodConfig3NF_of_reachF (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (hInvCong : ∀ {s s' : D.State}, E.eqv s s' → D.Inv s → D.Inv s')
    (hJoinNF : EqJoinLemma3C_NF D E W)
    (hBA : ∀ {C₀ C₁ : Configuration (QSig E W hP hC hA)}
      {t : Sal.Emulation.Timestamp} {r : Sal.Emulation.Replica} {o : D.AppOp}
      {v : Sal.Metatheory.Version} {sh : QState D E} {evh : Set (Op D.AppOp)},
      (labeledTS3 (QSig E W hP hC hA)).ReachableFrom
        (initConfig (QSig E W hP hC hA) trivial) C₀ →
      Step3 (QSig E W hP hC hA) C₀ (Label3.apply t r o) C₁ →
      C₀.head r = some v → C₀.ver v = some (sh, evh) →
      qapplicable E W hA (t, r, o) sh ∧
        (∀ s', D.applicable (t, r, o) s' → W (t, r, o) s'))
    (C : Configuration (QSig E W hP hC hA))
    (hReach : (labeledTS3 (QSig E W hP hC hA)).ReachableFrom
        (initConfig (QSig E W hP hC hA) trivial) C)
    (hgenW : ∀ o ∈ (Configuration.core C).events, ∀ s', D.applicable o s' → W o s') :
    GoodConfig3NF E W hP hC hA C := by
  revert hgenW
  induction hReach with
  | refl => intro _; exact goodConfig3NF_init E W hP hC hA
  | tail hprev hs ih =>
    intro hgenWcurr
    obtain ⟨ℓ, hstep⟩ := hs
    have hmono := events_mono_of_step hstep
    have hkeep := hstep
    cases hstep with
    | createReplica h_fresh C' hN hL hvis hver hhead hparents =>
      exact goodConfig3NF_createReplica E W hP hC hA h_fresh hL hvis hver
        (ih (fun o ho => hgenWcurr o (hmono o ho)))
    | apply h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank C' hN hL hvis hver hhead hparents =>
      obtain ⟨hqapp, hgw⟩ := hBA hprev hkeep h_head h_ver
      exact goodConfig3NF_apply E W hP hC hA hInvCong hgw
        h_head h_ver h_fresh_t h_vnew hL hvis hver hqapp
        (ih (fun o ho => hgenWcurr o (hmono o ho)))
    | merge h_head₁ h_head₂ h_ver₁ h_ver₂ h_lca h_verT h_vm h_rank₁ h_rank₂
        C' hN hL hvis hver hhead hparents =>
      have hih := ih (fun o ho => hgenWcurr o (hmono o ho))
      refine goodConfig3NF_merge E W hP hC hA hJoinNF h_head₁ h_ver₁ h_ver₂ h_lca h_verT
        hL hvis hver ?_ hih
      intro o ho
      refine hgenWcurr o (hmono o ?_)
      exact ho.elim
        (fun h' => hih.1.ver_events_sub _ _ _ h_ver₁ o h')
        (fun h' => hih.1.ver_events_sub _ _ _ h_ver₂ o h')
    | query h_s h_val => exact ih (fun o ho => hgenWcurr o (hmono o ho))

/-- **The born-applicable `≈`-metatheorem.**  A reachable `QSig`-configuration under
the born-applicable discipline (`hBA`) with genuine events (`hgenW`) is per-version
RA-linearizable — GATED only on the datatype's merge VC `EqJoinLemma3C_NF` (no
`GenDisc`, no `GDSupply`, no `WfOpReachable`). -/
theorem RA_linearizable_up_to_eq_NF (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (hInvCong : ∀ {s s' : D.State}, E.eqv s s' → D.Inv s → D.Inv s')
    (hJoinNF : EqJoinLemma3C_NF D E W)
    (hBA : ∀ {C₀ C₁ : Sal.Metatheory.Configuration (QSig E W hP hC hA)}
      {t : Sal.Emulation.Timestamp} {r : Sal.Emulation.Replica} {o : D.AppOp}
      {v : Sal.Metatheory.Version} {sh : QState D E} {evh : Set (Op D.AppOp)},
      (labeledTS3 (QSig E W hP hC hA)).ReachableFrom
        (Sal.Metatheory.initConfig (QSig E W hP hC hA) trivial) C₀ →
      Sal.Metatheory.Step3 (QSig E W hP hC hA) C₀ (Sal.Metatheory.Label3.apply t r o) C₁ →
      C₀.head r = some v → C₀.ver v = some (sh, evh) →
      qapplicable E W hA (t, r, o) sh ∧
        (∀ s', D.applicable (t, r, o) s' → W (t, r, o) s'))
    (C : Sal.Metatheory.Configuration (QSig E W hP hC hA))
    (hReach : (labeledTS3 (QSig E W hP hC hA)).ReachableFrom
        (Sal.Metatheory.initConfig (QSig E W hP hC hA) trivial) C)
    (hgenW : ∀ o ∈ (Sal.Metatheory.Configuration.core C).events,
        ∀ s', D.applicable o s' → W o s') :
    Sal.Metatheory.IsRALinearizable3 C :=
  isRALinearizable3_of_goodNF E W hP hC hA C
    (goodConfig3NF_of_reachF E W hP hC hA hInvCong hJoinNF hBA C hReach hgenW)

/-! ## §4  Axiom audit -/

#print axioms isCanonicalState_of_NFcls
#print axioms isCanonicalStateNF_congr
#print axioms isCanonicalStateNF_extend
#print axioms isRALinearizable3_of_goodNF
#print axioms goodConfig3NF_init
#print axioms goodConfig3NF_createReplica
#print axioms goodConfig3NF_apply
#print axioms goodConfig3NF_merge_of_canonical
#print axioms mergedNF_of_join
#print axioms goodConfig3NF_merge
#print axioms goodConfig3NF_of_reachF
#print axioms RA_linearizable_up_to_eq_NF

end Sal.Metatheory.GoodConfig3NF
