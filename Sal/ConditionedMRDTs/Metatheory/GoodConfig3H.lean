import Sal.ConditionedMRDTs.Metatheory.GenericEqQuotient_H
import Sal.ConditionedMRDTs.Metatheory.GoodConfig3NF

/-!
# The H-disciplined reachability invariant and the RAW-≈ metatheorem

The raw-≈ route to RA-linearizability, for datatypes where the
guarded final target `IsRALinearizable3` is unsatisfiable at `QSig …WfOpA…` for the tombstone-free
RGA (the criss-cross union admits no guarded replay), and the base `GoodConfig3.canonical` clause
(guarded) is equally unmaintainable at merges.  This file:

* `GoodConfig3S`: the STRUCTURAL fields of `GoodConfig3` (vis-strictness, event-universe bounds,
  causal closure) as a standalone invariant, with its own step preservations (the structural
  bullets of `Adequacy.goodConfig3_*`, without the guarded canonical clause).
* `IsCanonicalStateH`, per-version: the class is `qmk` of a representative carrying an
  `H`-disciplined RAW-fold witness (`IsCanonicalStateEqH`).
* `IsRALinearizable3Eq`, **the raw-≈ capstone statement**: every version's class is `qmk` of a
  representative that is the RAW datatype fold of a `lo`-respecting linearization of its events,
  up to `≈`.  This is the paper's Def. lin applied to the datatype; no guarded fold anywhere.
* `RA_linearizable_up_to_eq_H`, the metatheorem: reachable + born-applicable (`hBA`) +
  `H`-extension at applies (`hHext`) + the `H`-join (`EqJoinLemma3C_H`, the RDT's merge residual)
  ⟹ `IsRALinearizable3Eq`.
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs.GoodConfig3H

open Sal.Emulation
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs (Configuration Version Step3 Label3 IsLCA initConfig labeledTS3 core_vis)

variable {D : ConditionedMRDTSig}

/-! ## §1  The structural invariant -/

/-- The structural fields of `GoodConfig3`, everything except the (guarded) canonical clause. -/
structure GoodConfig3S (C : Configuration D') : Prop where
  vis_trans : ∀ {a b c : Op D'.AppOp}, C.vis a b → C.vis b c → C.vis a c
  vis_irrefl : ∀ a : Op D'.AppOp, ¬ C.vis a a
  ver_events_sub : ∀ (v : Version) (s : D'.State) (E : Set (Op D'.AppOp)),
    C.ver v = some (s, E) → ∀ a ∈ E, a ∈ C.events
  ver_causal : ∀ (v : Version) (s : D'.State) (E : Set (Op D'.AppOp)),
    C.ver v = some (s, E) → ∀ a b, C.vis a b → b ∈ E → a ∈ E

variable {D' : ConditionedMRDTSig}

/-- Projection: the structural part of a full `GoodConfig3`. -/
theorem GoodConfig3S.ofGood {C : Configuration D'} (h : Sal.ConditionedMRDTs.GoodConfig3 C) :
    GoodConfig3S C :=
  ⟨h.vis_trans, h.vis_irrefl, h.ver_events_sub, h.ver_causal⟩

/-- CreateReplica preserves the structural invariant. -/
theorem goodConfig3S_createReplica {C C' : Configuration D'} {r : Replica}
    (h_fresh : C.N r = none)
    (hL : C'.L = updateRep C.L r ∅)
    (hvis : C'.vis = C.vis)
    (hver : C'.ver = C.ver)
    (h : GoodConfig3S C) : GoodConfig3S C' := by
  have h_events : ∀ x, x ∈ C.events → x ∈ C'.events := by
    rintro x ⟨r'', s'', hLr'', hx⟩
    by_cases hr'' : r'' = r
    · subst hr''
      have hnone := (C.dom_eq r'').mp h_fresh
      rw [hnone] at hLr''
      simp at hLr''
    · refine ⟨r'', s'', ?_, hx⟩
      rw [hL]
      simp only [updateRep, if_neg hr'']
      exact hLr''
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b c hab hbc
    rw [hvis] at hab hbc ⊢
    exact h.vis_trans hab hbc
  · intro a ha
    rw [hvis] at ha
    exact h.vis_irrefl a ha
  · intro v s E hv a ha
    rw [hver] at hv
    exact h_events a (h.ver_events_sub v s E hv a ha)
  · intro v s E hv a b hab hb
    rw [hver] at hv
    rw [hvis] at hab
    exact h.ver_causal v s E hv a b hab hb

/-- Apply preserves the structural invariant. -/
theorem goodConfig3S_apply {C C' : Configuration D'}
    {t : Timestamp} {r : Replica} {o : D'.AppOp}
    {v : Version} {s : D'.State} {ev : Set (Op D'.AppOp)} {vnew : Version}
    (h_head : C.head r = some v)
    (h_ver : C.ver v = some (s, ev))
    (h_fresh_t : ∀ e', e' ∈ C.events → Op.time e' ≠ t)
    (hL : C'.L = updateRep C.L r (ev ∪ {(t, r, o)}))
    (hvis : C'.vis = fun a b => C.vis a b ∨ (ev a ∧ b = (t, r, o)))
    (hver : C'.ver = fun w => if w = vnew
      then some (D'.update s (t, r, o), ev ∪ {(t, r, o)}) else C.ver w)
    (h : GoodConfig3S C) : GoodConfig3S C' := by
  set e : Op D'.AppOp := (t, r, o) with he_def
  have hco := C.head_coherent r v h_head
  have hLr : C.L r = some ev := by
    rw [← hco.2, h_ver]; rfl
  have he_not_events : e ∉ C.events := fun hmem => h_fresh_t _ hmem rfl
  have h_ev_events : ∀ x ∈ ev, x ∈ C.events := fun x hx => ⟨r, ev, hLr, hx⟩
  have he_not_ev : e ∉ ev := fun hmem => he_not_events (h_ev_events e hmem)
  have h_no_vis_out : ∀ x, ¬ C.vis e x := by
    intro x hx
    obtain ⟨r₀, s₀, hL₀, hs₀⟩ := C.vis_src hx
    exact he_not_events ⟨r₀, s₀, hL₀, hs₀⟩
  have hver_new : C'.ver vnew = some (D'.update s e, ev ∪ {e}) := by
    rw [hver]; simp
  have hver_old : ∀ w, w ≠ vnew → C'.ver w = C.ver w := by
    intro w hw; rw [hver]; simp [hw]
  have h_events : ∀ x, x ∈ C.events → x ∈ C'.events := by
    rintro x ⟨r'', s'', hLr'', hx⟩
    by_cases hr'' : r'' = r
    · subst hr''
      rw [hLr, Option.some.injEq] at hLr''
      refine ⟨r'', ev ∪ {e}, ?_, Or.inl (hLr'' ▸ hx)⟩
      rw [hL]
      simp [updateRep]
    · refine ⟨r'', s'', ?_, hx⟩
      rw [hL]
      simp only [updateRep, if_neg hr'']
      exact hLr''
  have hL'r : C'.L r = some (ev ∪ {e}) := by
    rw [hL]
    simp [updateRep]
  have h_old_no_e : ∀ (w : Version) (s' : D'.State) (E' : Set (Op D'.AppOp)),
      C.ver w = some (s', E') → e ∉ E' := by
    intro w s' E' hw hmem
    exact he_not_events (h.ver_events_sub w s' E' hw e hmem)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b c hab hbc
    rw [hvis] at hab hbc ⊢
    rcases hab with hab | ⟨ha_ev, rfl⟩
    · rcases hbc with hbc | ⟨hb_ev, rfl⟩
      · exact Or.inl (h.vis_trans hab hbc)
      · exact Or.inr ⟨h.ver_causal v s ev h_ver a b hab hb_ev, rfl⟩
    · rcases hbc with hbc | ⟨hb_ev, rfl⟩
      · exact absurd hbc (h_no_vis_out c)
      · exact absurd hb_ev he_not_ev
  · intro a ha
    rw [hvis] at ha
    rcases ha with ha | ⟨ha_ev, rfl⟩
    · exact h.vis_irrefl a ha
    · exact he_not_ev ha_ev
  · intro w s' E' hw a ha
    by_cases hwn : w = vnew
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.2] at ha
      rcases ha with ha | ha
      · exact ⟨r, ev ∪ {e}, hL'r, Or.inl ha⟩
      · exact ⟨r, ev ∪ {e}, hL'r, Or.inr ha⟩
    · rw [hver_old w hwn] at hw
      exact h_events a (h.ver_events_sub w s' E' hw a ha)
  · intro w s' E' hw a b hab hb
    rw [hvis] at hab
    by_cases hwn : w = vnew
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.2] at hb ⊢
      rcases hb with hb | hb
      · rcases hab with hab | ⟨_, rfl⟩
        · exact Or.inl (h.ver_causal v s ev h_ver a b hab hb)
        · exact absurd hb he_not_ev
      · have hb_e : b = e := hb
        subst hb_e
        rcases hab with hab | ⟨ha_ev, _⟩
        · exfalso
          obtain ⟨r₀, s₀, hL₀, hs₀⟩ := C.vis_tgt hab
          exact he_not_events ⟨r₀, s₀, hL₀, hs₀⟩
        · exact Or.inl ha_ev
    · rw [hver_old w hwn] at hw
      rcases hab with hab | ⟨_, rfl⟩
      · exact h.ver_causal w s' E' hw a b hab hb
      · exact absurd hb (h_old_no_e w s' E' hw)

/-- Merge preserves the structural invariant. -/
theorem goodConfig3S_merge {C C' : Configuration D'} {r₁ : Replica}
    {v₁ v₂ vm : Version} {s₁ s₂ sT : D'.State} {ev₁ ev₂ : Set (Op D'.AppOp)}
    (h_head₁ : C.head r₁ = some v₁)
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂))
    (hL : C'.L = updateRep C.L r₁ (ev₁ ∪ ev₂))
    (hvis : C'.vis = C.vis)
    (hver : C'.ver = fun w => if w = vm
      then some (D'.mergeL sT s₁ s₂, ev₁ ∪ ev₂) else C.ver w)
    (h : GoodConfig3S C) : GoodConfig3S C' := by
  have hco := C.head_coherent r₁ v₁ h_head₁
  have hLr₁ : C.L r₁ = some ev₁ := by rw [← hco.2, h_ver₁]; rfl
  have hver_new : C'.ver vm = some (D'.mergeL sT s₁ s₂, ev₁ ∪ ev₂) := by
    rw [hver]; simp
  have hver_old : ∀ w, w ≠ vm → C'.ver w = C.ver w := by
    intro w hw; rw [hver]; simp [hw]
  have hL'r₁ : C'.L r₁ = some (ev₁ ∪ ev₂) := by rw [hL]; simp [updateRep]
  have h_events : ∀ x, x ∈ C.events → x ∈ C'.events := by
    rintro x ⟨r'', s'', hLr'', hx⟩
    by_cases hr'' : r'' = r₁
    · subst hr''
      rw [hLr₁, Option.some.injEq] at hLr''
      exact ⟨r'', ev₁ ∪ ev₂, hL'r₁, Or.inl (hLr'' ▸ hx)⟩
    · refine ⟨r'', s'', ?_, hx⟩
      rw [hL]; simp only [updateRep, if_neg hr'']; exact hLr''
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b c hab hbc
    rw [hvis] at hab hbc ⊢
    exact h.vis_trans hab hbc
  · intro a ha
    rw [hvis] at ha
    exact h.vis_irrefl a ha
  · intro w s' E' hw a ha
    by_cases hwn : w = vm
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.2] at ha
      exact ⟨r₁, ev₁ ∪ ev₂, hL'r₁, ha⟩
    · rw [hver_old w hwn] at hw
      exact h_events a (h.ver_events_sub w s' E' hw a ha)
  · intro w s' E' hw a b hab hb
    rw [hvis] at hab
    by_cases hwn : w = vm
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.2] at hb ⊢
      rcases hb with hb | hb
      · exact Or.inl (h.ver_causal v₁ s₁ ev₁ h_ver₁ a b hab hb)
      · exact Or.inr (h.ver_causal v₂ s₂ ev₂ h_ver₂ a b hab hb)
    · rw [hver_old w hwn] at hw
      exact h.ver_causal w s' E' hw a b hab hb

/-! ## §2  The H-disciplined per-version witness -/

variable (H : List (Op D.AppOp) → Prop)

/-- The version class `q` is `qmk` of a representative carrying an `H`-disciplined RAW-fold
canonical witness. -/
def IsCanonicalStateH (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (Cq : Sal.Emulation.Configuration (QSig E W hP hC hA).toCRDTSig)
    (ev : Set (Op D.AppOp)) (q : QState D E) : Prop :=
  ∃ (σ : D.State) (hσ : D.Inv σ),
    q = qmk E σ hσ ∧ IsCanonicalStateEqH H E W Cq.vis ev σ

/-- Transport under `vis`-agreement. -/
theorem isCanonicalStateH_congr (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    {Cq Cq' : Sal.Emulation.Configuration (QSig E W hP hC hA).toCRDTSig}
    {ev : Set (Op D.AppOp)} {q : QState D E}
    (h_vis : ∀ a ∈ ev, ∀ b ∈ ev, (Cq'.vis a b ↔ Cq.vis a b))
    (h : IsCanonicalStateH H E W hP hC hA Cq ev q) :
    IsCanonicalStateH H E W hP hC hA Cq' ev q := by
  obtain ⟨σ, hσ, hq, hcs⟩ := h
  exact ⟨σ, hσ, hq, isCanonicalStateEqH_congr H E W h_vis hcs⟩

/-- The apply-step extension: the fresh, `vis`-maximal, `qapplicable` event extends the
representative's witness; the class steps by `qdo`. -/
theorem isCanonicalStateH_extend (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (hInvCong : ∀ {s s' : D.State}, E.eqv s s' → D.Inv s → D.Inv s')
    (Cq : Sal.Emulation.Configuration (QSig E W hP hC hA).toCRDTSig)
    (ev : Set (Op D.AppOp)) (q : QState D E) (e : Op D.AppOp)
    (hgenW : ∀ s : D.State, D.applicable e s → W e s)
    (h_e_fresh : e ∉ ev)
    (h_e_sees : ∀ x ∈ ev, Cq.vis x e)
    (h_e_last : ∀ x ∈ ev, ¬ Cq.vis e x)
    (hqapp : qapplicable E W hA e q)
    (hHext : ∀ ρ : List (Op D.AppOp), listPermOf ρ ev → H ρ →
        D.applicable e (applySeq D.toCRDTSig D.init ρ) → H (ρ ++ [e]))
    (h : IsCanonicalStateH H E W hP hC hA Cq ev q) :
    IsCanonicalStateH H E W hP hC hA Cq (insert e ev)
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
  · exact isCanonicalStateEqH_extend H E W hC hA hInvCong Cq.vis ev σ hσ e
      h_e_fresh h_e_sees h_e_last happ hHext hcs

/-! ## §3  The invariant, the raw-≈ target, and the extraction -/

/-- **The H-disciplined reachability invariant**: structural facts + per-version H-witness. -/
def GoodConfig3H (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (C : Configuration (QSig E W hP hC hA)) : Prop :=
  GoodConfig3S C ∧
  ∀ (v : Version) (s : QState D E) (Ev : Set (Op D.AppOp)),
    C.ver v = some (s, Ev) →
    IsCanonicalStateH H E W hP hC hA (Sal.ConditionedMRDTs.Configuration.core C) Ev s

/-- **The RAW-≈ capstone statement**, the paper's Def. lin applied to the datatype: every
version's class is `qmk` of a representative that is the RAW datatype fold of a `lo`-respecting
linearization of its events, up to observational `≈`.  NO guarded fold anywhere. -/
def IsRALinearizable3Eq (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (C : Sal.ConditionedMRDTs.Configuration (QSig E W hP hC hA)) : Prop :=
  ∀ (v : Version) (s : QState D E) (Ev : Set (Op D.AppOp)),
    C.ver v = some (s, Ev) →
    ∃ (σ : D.State) (hσ : D.Inv σ),
      s = qmk E σ hσ ∧
      ∃ π : List (Op D.AppOp),
        listPermOf π Ev ∧
        respects π (Sal.Emulation.lo (D := (QSig E W hP hC hA).toCRDTSig)
          (Sal.ConditionedMRDTs.Configuration.core (D := QSig E W hP hC hA) C)) ∧
        E.eqv (applySeq D.toCRDTSig D.init π) σ

/-- **`GoodConfig3H ⟹ IsRALinearizable3Eq`.**  The witness's `loOnEq`-respect converts to the
paper's `lo` via the quotient order bridge (`loOn_qsig_iff`) and the set-relative weakening
(`respects_lo_of_respects_loOn`); the fold clause is already raw. -/
theorem isRALinearizable3Eq_of_goodH (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (C : Sal.ConditionedMRDTs.Configuration (QSig E W hP hC hA))
    (h : GoodConfig3H H E W hP hC hA C) :
    IsRALinearizable3Eq E W hP hC hA C := by
  intro v s Ev hv
  obtain ⟨σ, hσ, hq, ρ, hperm, hresp, _hH, heqv⟩ := h.2 v s Ev hv
  refine ⟨σ, hσ, hq, ρ, hperm, ?_, heqv⟩
  have h1 : respects ρ (Sal.Emulation.loOn (D := (QSig E W hP hC hA).toCRDTSig)
      (Sal.ConditionedMRDTs.Configuration.core (D := QSig E W hP hC hA) C) Ev) :=
    (respects_congr (loOn_qsig_iff E W hP hC hA
      (Sal.ConditionedMRDTs.Configuration.core (D := QSig E W hP hC hA) C) Ev)).mpr hresp
  exact respects_lo_of_respects_loOn
    (C := Sal.ConditionedMRDTs.Configuration.core (D := QSig E W hP hC hA) C) h1

/-! ## §4  Step preservations -/

/-- Init: version `0 = (init, ∅)`, witness `[]`, needs `H []`. -/
theorem goodConfig3H_init (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (hHnil : H []) :
    GoodConfig3H H E W hP hC hA (initConfig (QSig E W hP hC hA) trivial) := by
  refine ⟨GoodConfig3S.ofGood (Sal.ConditionedMRDTs.goodConfig3_init trivial), ?_⟩
  intro v s' E' hv
  have hver : (initConfig (QSig E W hP hC hA) trivial).ver v
      = if v = 0 then some ((QSig E W hP hC hA).init, (∅ : Set (Op D.AppOp)))
        else none := rfl
  rw [hver] at hv
  by_cases hv0 : v = 0
  · rw [if_pos hv0, Option.some.injEq, Prod.mk.injEq] at hv
    rw [← hv.1, ← hv.2]
    refine ⟨D.init, hP.inv_init, rfl, ?_⟩
    exact ⟨[], ⟨List.nodup_nil, fun a => by simp⟩, List.Pairwise.nil, hHnil,
      E.equiv.refl _⟩
  · rw [if_neg hv0] at hv; simp at hv

/-- CreateReplica: store and `vis` unchanged. -/
theorem goodConfig3H_createReplica (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    {C C' : Configuration (QSig E W hP hC hA)} {r : Replica}
    (h_fresh : C.N r = none)
    (hL : C'.L = updateRep C.L r ∅)
    (hvis : C'.vis = C.vis)
    (hver : C'.ver = C.ver)
    (h : GoodConfig3H H E W hP hC hA C) :
    GoodConfig3H H E W hP hC hA C' := by
  refine ⟨goodConfig3S_createReplica h_fresh hL hvis hver h.1, ?_⟩
  intro w s' E' hw
  rw [hver] at hw
  exact isCanonicalStateH_congr H E W hP hC hA
    (fun a _ b _ => by rw [core_vis, core_vis, hvis])
    (h.2 w s' E' hw)

/-- Apply: the fresh event extends the parent's witness. -/
theorem goodConfig3H_apply (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (hInvCong : ∀ {s s' : D.State}, E.eqv s s' → D.Inv s → D.Inv s')
    {C C' : Configuration (QSig E W hP hC hA)}
    {t : Timestamp} {r : Replica} {oo : D.AppOp}
    {v : Version} {s : QState D E} {ev : Set (Op D.AppOp)}
    {vnew : Version}
    (hgenW : ∀ s' : D.State, D.applicable (t, r, oo) s' → W (t, r, oo) s')
    (h_head : C.head r = some v)
    (h_ver : C.ver v = some (s, ev))
    (h_fresh_t : ∀ e', e' ∈ C.events → Op.time e' ≠ t)
    (h_vnew : C.ver vnew = none)
    (hL : C'.L = updateRep C.L r (ev ∪ {(t, r, oo)}))
    (hvis : C'.vis = fun a b => C.vis a b ∨ (ev a ∧ b = (t, r, oo)))
    (hver : C'.ver = fun w => if w = vnew
      then some ((QSig E W hP hC hA).update s (t, r, oo), ev ∪ {(t, r, oo)})
      else C.ver w)
    (hqapp : qapplicable E W hA (t, r, oo) s)
    (hHext : ∀ ρ : List (Op D.AppOp), listPermOf ρ ev → H ρ →
        D.applicable (t, r, oo) (applySeq D.toCRDTSig D.init ρ) → H (ρ ++ [(t, r, oo)]))
    (h : GoodConfig3H H E W hP hC hA C) :
    GoodConfig3H H E W hP hC hA C' := by
  refine ⟨goodConfig3S_apply h_head h_ver h_fresh_t hL hvis hver h.1, ?_⟩
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
    rw [core_vis, core_vis, hvis]
    constructor
    · exact Or.inl
    · rintro (hab | ⟨_, rfl⟩)
      · exact hab
      · exact absurd (hsub _ hb) he_not_events
  intro w s' E' hw
  by_cases hwn : w = vnew
  · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
    rw [← hw.1, ← hw.2]
    have h_old : IsCanonicalStateH H E W hP hC hA (C.core) ev s := h.2 v s ev h_ver
    have h_old' : IsCanonicalStateH H E W hP hC hA (C'.core) ev s :=
      isCanonicalStateH_congr H E W hP hC hA
        (fun a ha b hb => (h_vis_old ev h_ev_events a ha b hb).symm) h_old
    have h_ext := isCanonicalStateH_extend H E W hP hC hA hInvCong (C'.core) ev s e
      hgenW he_not_ev
      (fun x hx => by
        rw [core_vis, hvis]; exact Or.inr ⟨hx, rfl⟩)
      (fun x hx => by
        rw [core_vis, hvis]
        rintro (hex | ⟨he_ev, _⟩)
        · exact h_no_vis_out x hex
        · exact he_not_ev he_ev)
      hqapp hHext h_old'
    rw [Set.union_singleton]
    exact h_ext
  · rw [hver_old w hwn] at hw
    have h_old : IsCanonicalStateH H E W hP hC hA (C.core) E' s' := h.2 w s' E' hw
    exact isCanonicalStateH_congr H E W hP hC hA
      (fun a ha b hb => (h_vis_old E' (h.1.ver_events_sub w s' E' hw) a ha b hb).symm) h_old

/-- The H-join: merged H-canonical state from `EqJoinLemma3C_H`. -/
theorem mergedH_of_join (HonJ : (Op D.AppOp → Op D.AppOp → Prop) → Set (Op D.AppOp) → Prop)
    (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (hJoinH : EqJoinLemma3C_H D E W H HonJ)
    (Cq : Sal.Emulation.Configuration (QSig E W hP hC hA).toCRDTSig)
    (events ev₁ ev₂ : Set (Op D.AppOp)) (sT s₁ s₂ : QState D E)
    (hHonJ : HonJ Cq.vis events)
    (htr : ∀ {a b c : Op D.AppOp}, Cq.vis a b → Cq.vis b c → Cq.vis a c)
    (hir : ∀ a : Op D.AppOp, ¬ Cq.vis a a)
    (hdts : ∀ a b : Op D.AppOp, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1)
    (hsub₁ : ∀ a ∈ ev₁, a ∈ events) (hsub₂ : ∀ a ∈ ev₂, a ∈ events)
    (hcl₁ : fullClosureRel Cq.vis ev₁) (hcl₂ : fullClosureRel Cq.vis ev₂)
    (hcT : IsCanonicalStateH H E W hP hC hA Cq (ev₁ ∩ ev₂) sT)
    (hc₁ : IsCanonicalStateH H E W hP hC hA Cq ev₁ s₁)
    (hc₂ : IsCanonicalStateH H E W hP hC hA Cq ev₂ s₂) :
    IsCanonicalStateH H E W hP hC hA Cq (ev₁ ∪ ev₂)
      ((QSig E W hP hC hA).mergeL sT s₁ s₂) := by
  obtain ⟨σT, hσT, hqT, hcsT⟩ := hcT
  obtain ⟨σ₁, hσ₁, hq₁, hcs₁⟩ := hc₁
  obtain ⟨σ₂, hσ₂, hq₂, hcs₂⟩ := hc₂
  refine ⟨D.mergeL σT σ₁ σ₂, hP.inv_mergeL σT σ₁ σ₂ hσT hσ₁ hσ₂, ?_, ?_⟩
  · rw [hqT, hq₁, hq₂]; rfl
  · exact hJoinH Cq.vis events ev₁ ev₂ σT σ₁ σ₂ hHonJ hσT hσ₁ hσ₂
      htr hir hdts hsub₁ hsub₂ hcl₁ hcl₂ hcsT hcs₁ hcs₂

/-- The full merge step. -/
theorem goodConfig3H_merge (HonJ : (Op D.AppOp → Op D.AppOp → Prop) → Set (Op D.AppOp) → Prop)
    (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (hJoinH : EqJoinLemma3C_H D E W H HonJ)
    {C C' : Configuration (QSig E W hP hC hA)}
    {r₁ : Replica} {v₁ v₂ vT vm : Version}
    {s₁ s₂ sT : QState D E} {ev₁ ev₂ evT : Set (Op D.AppOp)}
    (h_head₁ : C.head r₁ = some v₁)
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂))
    (h_lca : IsLCA C.parents v₁ v₂ vT)
    (h_verT : C.ver vT = some (sT, evT))
    (hL : C'.L = updateRep C.L r₁ (ev₁ ∪ ev₂))
    (hvis : C'.vis = C.vis)
    (hver : C'.ver = fun w => if w = vm
      then some ((QSig E W hP hC hA).mergeL sT s₁ s₂, ev₁ ∪ ev₂) else C.ver w)
    (hHonJ : HonJ (Sal.ConditionedMRDTs.Configuration.core C).vis
      (Sal.ConditionedMRDTs.Configuration.core C).events)
    (h : GoodConfig3H H E W hP hC hA C) :
    GoodConfig3H H E W hP hC hA C' := by
  have hcTH : IsCanonicalStateH H E W hP hC hA (C.core) (ev₁ ∩ ev₂) sT := by
    rw [← C.lca_events h_lca h_ver₁ h_ver₂ h_verT]
    exact h.2 vT sT evT h_verT
  have hcl₁f : fullClosureRel (C.core).vis ev₁ :=
    fun a b hab hb => h.1.ver_causal v₁ s₁ ev₁ h_ver₁ a b hab hb
  have hcl₂f : fullClosureRel (C.core).vis ev₂ :=
    fun a b hab hb => h.1.ver_causal v₂ s₂ ev₂ h_ver₂ a b hab hb
  have hsub₁ : ∀ a ∈ ev₁, a ∈ (C.core).events := h.1.ver_events_sub v₁ s₁ ev₁ h_ver₁
  have hsub₂ : ∀ a ∈ ev₂, a ∈ (C.core).events := h.1.ver_events_sub v₂ s₂ ev₂ h_ver₂
  have hdts : ∀ a b : Op D.AppOp,
      a ∈ (C.core).events → b ∈ (C.core).events → a ≠ b → a.1 ≠ b.1 := by
    intro a b ha hb hne
    obtain ⟨r, s, hLr, hsa⟩ := ha
    obtain ⟨r', s', hLr', hsb⟩ := hb
    exact (C.core).timestamps_distinct hLr hsa hLr' hsb hne
  have h_mergedH := mergedH_of_join H HonJ E W hP hC hA hJoinH (C.core) (C.core).events
    ev₁ ev₂ sT s₁ s₂ hHonJ
    (fun hab hbc => h.1.vis_trans hab hbc) (fun a ha => h.1.vis_irrefl a ha) hdts
    hsub₁ hsub₂ hcl₁f hcl₂f hcTH (h.2 v₁ s₁ ev₁ h_ver₁) (h.2 v₂ s₂ ev₂ h_ver₂)
  refine ⟨goodConfig3S_merge h_head₁ h_ver₁ h_ver₂ hL hvis hver h.1, ?_⟩
  have hver_new : C'.ver vm
      = some ((QSig E W hP hC hA).mergeL sT s₁ s₂, ev₁ ∪ ev₂) := by rw [hver]; simp
  have hver_old : ∀ w, w ≠ vm → C'.ver w = C.ver w := by
    intro w hw; rw [hver]; simp [hw]
  have h_sameH : ∀ (E' : Set (Op D.AppOp)) (s' : QState D E),
      IsCanonicalStateH H E W hP hC hA (C.core) E' s' →
      IsCanonicalStateH H E W hP hC hA (C'.core) E' s' :=
    fun E' s' hcs => isCanonicalStateH_congr H E W hP hC hA
      (fun a _ b _ => by rw [core_vis, core_vis, hvis]) hcs
  intro w s' E' hw
  by_cases hwn : w = vm
  · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
    rw [← hw.1, ← hw.2]
    exact h_sameH _ _ h_mergedH
  · rw [hver_old w hwn] at hw
    exact h_sameH E' s' (h.2 w s' E' hw)

/-! ## §5  The reachability induction and the RAW-≈ metatheorem -/

/-- **`GoodConfig3H` from reachability.**  Gated on the H-join (`EqJoinLemma3C_H`), the honest
conditions `hgenW`/`hBA`, and the H-discipline conditions `hHnil`/`hHext`. -/
theorem goodConfig3H_of_reachF (HonJ : (Op D.AppOp → Op D.AppOp → Prop) → Set (Op D.AppOp) → Prop)
    (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (hInvCong : ∀ {s s' : D.State}, E.eqv s s' → D.Inv s → D.Inv s')
    (hJoinH : EqJoinLemma3C_H D E W H HonJ)
    (hHon : ∀ {C₀ : Configuration (QSig E W hP hC hA)},
      (labeledTS3 (QSig E W hP hC hA)).ReachableFrom
        (initConfig (QSig E W hP hC hA) trivial) C₀ →
      HonJ (Sal.ConditionedMRDTs.Configuration.core C₀).vis
        (Sal.ConditionedMRDTs.Configuration.core C₀).events)
    (hHnil : H [])
    (hHext : ∀ {C₀ C₁ : Configuration (QSig E W hP hC hA)}
      {t : Timestamp} {r : Replica} {o : D.AppOp}
      {v : Version} {sh : QState D E} {evh : Set (Op D.AppOp)},
      (labeledTS3 (QSig E W hP hC hA)).ReachableFrom
        (initConfig (QSig E W hP hC hA) trivial) C₀ →
      Step3 (QSig E W hP hC hA) C₀ (Label3.apply t r o) C₁ →
      C₀.head r = some v → C₀.ver v = some (sh, evh) →
      ∀ ρ : List (Op D.AppOp), listPermOf ρ evh → H ρ →
        D.applicable (t, r, o) (applySeq D.toCRDTSig D.init ρ) → H (ρ ++ [(t, r, o)]))
    (hBA : ∀ {C₀ C₁ : Configuration (QSig E W hP hC hA)}
      {t : Timestamp} {r : Replica} {o : D.AppOp}
      {v : Version} {sh : QState D E} {evh : Set (Op D.AppOp)},
      (labeledTS3 (QSig E W hP hC hA)).ReachableFrom
        (initConfig (QSig E W hP hC hA) trivial) C₀ →
      Step3 (QSig E W hP hC hA) C₀ (Label3.apply t r o) C₁ →
      C₀.head r = some v → C₀.ver v = some (sh, evh) →
      qapplicable E W hA (t, r, o) sh ∧
        (∀ s', D.applicable (t, r, o) s' → W (t, r, o) s'))
    (C : Configuration (QSig E W hP hC hA))
    (hReach : (labeledTS3 (QSig E W hP hC hA)).ReachableFrom
        (initConfig (QSig E W hP hC hA) trivial) C) :
    GoodConfig3H H E W hP hC hA C := by
  induction hReach with
  | refl => exact goodConfig3H_init H E W hP hC hA hHnil
  | tail hprev hs ih =>
    obtain ⟨ℓ, hstep⟩ := hs
    have hkeep := hstep
    cases hstep with
    | createReplica h_fresh C' hN hL hvis hver hhead hparents =>
      exact goodConfig3H_createReplica H E W hP hC hA h_fresh hL hvis hver ih
    | apply h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank C' hN hL hvis hver hhead hparents =>
      obtain ⟨hqapp, hgw⟩ := hBA hprev hkeep h_head h_ver
      exact goodConfig3H_apply H E W hP hC hA hInvCong hgw
        h_head h_ver h_fresh_t h_vnew hL hvis hver hqapp
        (fun ρ hρp hH happ => hHext hprev hkeep h_head h_ver ρ hρp hH happ) ih
    | merge h_head₁ h_head₂ h_ver₁ h_ver₂ h_lca h_verT h_vm h_rank₁ h_rank₂
        C' hN hL hvis hver hhead hparents =>
      exact goodConfig3H_merge H HonJ E W hP hC hA hJoinH h_head₁ h_ver₁ h_ver₂ h_lca h_verT
        hL hvis hver (hHon hprev) ih
    | query h_s h_val => exact ih

/-- **The RAW-≈ metatheorem.**  A reachable `QSig`-configuration under the born-applicable
discipline is per-version RA-linearizable in the paper's sense, raw datatype folds, up to `≈`,
gated on the datatype's H-join (`EqJoinLemma3C_H`) and the H-discipline conditions. -/
theorem RA_linearizable_up_to_eq_H (HonJ : (Op D.AppOp → Op D.AppOp → Prop) → Set (Op D.AppOp) → Prop)
    (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (hInvCong : ∀ {s s' : D.State}, E.eqv s s' → D.Inv s → D.Inv s')
    (hJoinH : EqJoinLemma3C_H D E W H HonJ)
    (hHon : ∀ {C₀ : Configuration (QSig E W hP hC hA)},
      (labeledTS3 (QSig E W hP hC hA)).ReachableFrom
        (initConfig (QSig E W hP hC hA) trivial) C₀ →
      HonJ (Sal.ConditionedMRDTs.Configuration.core C₀).vis
        (Sal.ConditionedMRDTs.Configuration.core C₀).events)
    (hHnil : H [])
    (hHext : ∀ {C₀ C₁ : Configuration (QSig E W hP hC hA)}
      {t : Timestamp} {r : Replica} {o : D.AppOp}
      {v : Version} {sh : QState D E} {evh : Set (Op D.AppOp)},
      (labeledTS3 (QSig E W hP hC hA)).ReachableFrom
        (initConfig (QSig E W hP hC hA) trivial) C₀ →
      Step3 (QSig E W hP hC hA) C₀ (Label3.apply t r o) C₁ →
      C₀.head r = some v → C₀.ver v = some (sh, evh) →
      ∀ ρ : List (Op D.AppOp), listPermOf ρ evh → H ρ →
        D.applicable (t, r, o) (applySeq D.toCRDTSig D.init ρ) → H (ρ ++ [(t, r, o)]))
    (hBA : ∀ {C₀ C₁ : Configuration (QSig E W hP hC hA)}
      {t : Timestamp} {r : Replica} {o : D.AppOp}
      {v : Version} {sh : QState D E} {evh : Set (Op D.AppOp)},
      (labeledTS3 (QSig E W hP hC hA)).ReachableFrom
        (initConfig (QSig E W hP hC hA) trivial) C₀ →
      Step3 (QSig E W hP hC hA) C₀ (Label3.apply t r o) C₁ →
      C₀.head r = some v → C₀.ver v = some (sh, evh) →
      qapplicable E W hA (t, r, o) sh ∧
        (∀ s', D.applicable (t, r, o) s' → W (t, r, o) s'))
    (C : Configuration (QSig E W hP hC hA))
    (hReach : (labeledTS3 (QSig E W hP hC hA)).ReachableFrom
        (initConfig (QSig E W hP hC hA) trivial) C) :
    IsRALinearizable3Eq E W hP hC hA C :=
  isRALinearizable3Eq_of_goodH H E W hP hC hA C
    (goodConfig3H_of_reachF H HonJ E W hP hC hA hInvCong hJoinH hHon hHnil hHext hBA C hReach)

/-! ## Axiom audit -/

#print axioms goodConfig3S_apply
#print axioms goodConfig3S_merge
#print axioms isCanonicalStateH_extend
#print axioms isRALinearizable3Eq_of_goodH
#print axioms goodConfig3H_of_reachF
#print axioms RA_linearizable_up_to_eq_H

end Sal.ConditionedMRDTs.GoodConfig3H
