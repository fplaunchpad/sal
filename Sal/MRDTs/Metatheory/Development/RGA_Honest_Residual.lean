import Sal.MRDTs.Metatheory.Development.RGA_Final_Assembly

/-!
# The honest-execution residual DISCHARGED — hHon + hBA from per-step delivery honesty

*Additive; modifies no existing file; 0 `sorry`.*

`rga_RA_linearizable_final`'s residual (`hHon`, `hBA`) quantifies over all reachable
configurations and speaks in framework vocabulary (`GenDisc2C`, `qapplicable`).  This file
grinds it down to a SINGLE per-step assumption about what an honest system delivers
(`HonestDelivery`), and proves the rest by reachability induction:

* **Free from the structure**: the metatheory `Configuration` carries `causal_mono` (Lamport
  clocks), `timestamps_distinct`, and `vis_src`/`vis_tgt`/`vis_causal` as structural fields —
  configurations with dishonest clocks are unrepresentable.  `rgaHonJ`'s visibility-restriction
  and Lamport clauses need no induction at all.
* **Free from the delivered op's wellformedness** (`WfOpQ`, extracted from `hBA`'s own clause at
  a representative of the head class): insert timestamps are nonzero, and delete targets are
  nonzero (`resolve ≠ x ∧ (resolve = 0 ∨ resolve < x)` is unsatisfiable in `ℕ` at `x = 0`).
  Delete TIMESTAMPS are nonzero by Lamport: an accurate non-root delete saw its target's insert
  (`t > x-insert's time ≥ 0` in `ℕ` forces `t ≥ 1`).
* **The genuinely irreducible clause** — *born accuracy*: each delivered op was generated
  accurately against a causal fold of the events it had seen (this is how an RGA client works:
  it reads its replica's state).  This is exactly the generation-discipline assumption the
  whole development identified as forced by tombstone-freedom; `genDisc2C_of_born` converts it
  to `GenDisc2C` at every reachable core.

`HonestDelivery` = born accuracy + `hBA`'s applicable-delivery clause.  Everything else is
induction (`HonCore`) over `Step3`.
-/

set_option maxHeartbeats 1000000

open Classical

namespace Sal.Metatheory.RGASkeleton3

open Sal.Emulation
open Sal.Metatheory.GenericEqQuotient
open Sal.Metatheory.GoodConfig3H
open Sal.Metatheory (Configuration Version Step3 Label3 initConfig labeledTS3)
open Sal.Metatheory.RGAInstance (RGACondSig' rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)
open Sal.Metatheory.RGAInvUpdateQ (WfOpQ)
open Sal.Metatheory.G2Probe (RGACondSig)
open Sal.Metatheory.ConditionedConvergence (loOnA)
open Sal.Metatheory.RGAK1Delta (rgaHonJ loOnA_imp_vis genDisc2C_of_born pastE)
open Sal.Metatheory.RGACanonFoldOK (GenDisc2C insertedIn_of_contains_fold)
open RGAMergeLinearization (applySeqR)

local notation "QD" => QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA
local notation "Cfg3" => Sal.Metatheory.Configuration
  (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)
local notation "Reach3" => LabeledTS.ReachableFrom
  (labeledTS3 (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA))
  (initConfig (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA) trivial)

/-! ## §0  Small bricks -/

private theorem updateRep_self {α} (f : Replica → Option α) (r : Replica) (x : α) :
    updateRep f r x r = some x := by simp [updateRep]

private theorem updateRep_other {α} (f : Replica → Option α) {r r' : Replica} (x : α)
    (h : r' ≠ r) : updateRep f r x r' = f r' := by simp [updateRep, h]

/-- The delivered op is `WfOpQ` somewhere: extract a representative of the head class from
`hBA`'s own clauses.  (`qapplicable` lifts `applicable`; `applicable ⟹ WfOpA ⟹ WfOpQ`.) -/
theorem wfOpQ_of_hBA {t : ℕ} {r : ℕ} {o : app_op_t} {sh : QState RGACondSig' rgaEqEquiv'}
    (hq : qapplicable rgaEqEquiv' WfOpA rgaInvInvVCA (t, r, o) sh)
    (himp : ∀ s', RGACondSig'.applicable (t, r, o) s' → WfOpA (t, r, o) s') :
    ∃ σ : concrete_st, WfOpQ (t, r, o) σ := by
  obtain ⟨⟨σ, _hσ⟩, hrep⟩ := Quotient.exists_rep sh
  rw [← hrep] at hq
  have happ : RGACondSig'.applicable (t, r, o) σ := hq
  exact ⟨σ, (himp σ happ).1⟩

/-! ## §1  The re-typed core: the `rgaHonJ` witness configuration

`Configuration.core` lands at the QUOTIENT signature; `rgaHonJ` wants a configuration over the
raw `RGACondSig.toCRDTSig`.  Only `N`'s state type differs — and nothing downstream reads `N` —
so re-seat it and carry every invariant field verbatim. -/

def coreR (C : Cfg3) : Sal.Emulation.Configuration RGACondSig.toCRDTSig where
  N := fun r => (C.L r).map fun _ => init_st
  L := C.L
  vis := C.vis
  dom_eq := by intro r; cases h : C.L r <;> simp
  vis_src := C.vis_src
  vis_tgt := C.vis_tgt
  vis_causal := C.vis_causal
  timestamps_distinct := C.timestamps_distinct
  vis_total_same_replica := C.vis_total_same_replica

/-! ## §2  The structural invariant at every reachable configuration -/

theorem goodConfig3S_of_reach {C : Cfg3} (hReach : Reach3 C) : GoodConfig3S C := by
  induction hReach with
  | refl => exact GoodConfig3S.ofGood (Sal.Metatheory.goodConfig3_init trivial)
  | tail _ hs ih =>
    obtain ⟨ℓ, hstep⟩ := hs
    cases hstep with
    | createReplica h_fresh C' hN hL hvis hver hhead hparents =>
      exact goodConfig3S_createReplica h_fresh hL hvis hver ih
    | apply h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank C'
        hN hL hvis hver hhead hparents =>
      exact goodConfig3S_apply h_head h_ver h_fresh_t hL hvis hver ih
    | merge h_head₁ h_head₂ h_ver₁ h_ver₂ h_lca h_verT h_vm h_rank₁ h_rank₂ C'
        hN hL hvis hver hhead hparents =>
      exact goodConfig3S_merge h_head₁ h_ver₁ h_ver₂ hL hvis hver ih
    | query h_s h_val => exact ih

/-! ## §3  The honest-core invariant -/

/-- The reachability invariant behind `rgaHonJ`: the event universe is finite (listable), ids
are nonzero, deletes have nonzero targets, and every event was BORN ACCURATE — accurate at some
causal-order fold of its strict `vis`-past. -/
def HonCore (C : Cfg3) : Prop :=
  (∃ lE : List op_t, listPermOf lE C.events) ∧
  (∀ o ∈ C.events, o.1 ≠ 0) ∧
  (∀ (t r x : ℕ) (p : List ℕ), ((t, r, app_op_t.Del p x) : op_t) ∈ C.events → x ≠ 0) ∧
  (∀ o ∈ C.events, ∃ π : List op_t,
      listPermOf π {z : op_t | z ∈ C.events ∧ C.vis z o} ∧
      respects π (fun a b : op_t => C.vis a b) ∧
      accurate o (applySeqR init_st π))

/-- **The honest-delivery residual** — the ONLY assumption about the system, per apply step:
the delivered op was generated accurately against a causal fold of the head version's events
(born accuracy — the generation discipline forced by tombstone-freedom), and delivery is
born-applicable (`hBA`'s own clauses, verbatim). -/
def HonestDelivery : Prop :=
  ∀ {C₀ C₁ : Cfg3} {t : Sal.Emulation.Timestamp} {r : Sal.Emulation.Replica} {o : app_op_t}
    {v : Sal.Metatheory.Version} {sh : QState RGACondSig' rgaEqEquiv'} {evh : Set (Op app_op_t)},
    Reach3 C₀ →
    Step3 (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)
      C₀ (Label3.apply t r o) C₁ →
    C₀.head r = some v → C₀.ver v = some (sh, evh) →
    (∃ π : List op_t, listPermOf π evh ∧ respects π (fun a b : op_t => C₀.vis a b) ∧
        accurate (t, r, o) (applySeqR init_st π)) ∧
    qapplicable rgaEqEquiv' WfOpA rgaInvInvVCA (t, r, o) sh ∧
    (∀ s', RGACondSig'.applicable (t, r, o) s' → WfOpA (t, r, o) s')

theorem honCore_init : HonCore (initConfig QD trivial) := by
  have hev : ∀ e : op_t, e ∈ (initConfig QD trivial).events → False := by
    rintro e ⟨r, s, hLs, hse⟩
    have hLs' : (if r = 0 then (some (∅ : Set op_t)) else none) = some s := hLs
    by_cases h : r = 0
    · subst h
      rw [if_pos rfl] at hLs'
      injection hLs' with hs
      subst hs
      exact hse
    · rw [if_neg h] at hLs'
      simp at hLs'
  exact ⟨⟨[], List.nodup_nil, fun a => ⟨fun h => by simp at h, fun h => (hev a h).elim⟩⟩,
    fun o ho => (hev o ho).elim,
    fun t r x p h => (hev _ h).elim,
    fun o ho => (hev o ho).elim⟩

/-- Events-preserving, vis-preserving steps transfer the whole invariant. -/
theorem honCore_transfer {C C' : Cfg3}
    (hE : ∀ e : op_t, e ∈ C'.events ↔ e ∈ C.events)
    (hvis : C'.vis = C.vis)
    (h : HonCore C) : HonCore C' := by
  obtain ⟨⟨lE, hlE⟩, hz, hd, hb⟩ := h
  refine ⟨⟨lE, hlE.1, fun a => (hlE.2 a).trans (hE a).symm⟩,
    fun o ho => hz o ((hE o).mp ho),
    fun t r x p hm => hd t r x p ((hE _).mp hm),
    fun o ho => ?_⟩
  obtain ⟨π, hπp, hπr, hπacc⟩ := hb o ((hE o).mp ho)
  refine ⟨π, ⟨hπp.1, fun z => (hπp.2 z).trans ?_⟩, ?_, hπacc⟩
  · constructor
    · rintro ⟨hz', hv⟩
      exact ⟨(hE z).mpr hz', by rw [hvis]; exact hv⟩
    · rintro ⟨hz', hv⟩
      exact ⟨(hE z).mp hz', by rw [← hvis]; exact hv⟩
  · exact hπr.imp fun hn hv => hn (hvis ▸ hv)

theorem honCore_createReplica {C C' : Cfg3} {r : Replica}
    (h_fresh : C.N r = none)
    (hL : C'.L = updateRep C.L r ∅)
    (hvis : C'.vis = C.vis)
    (h : HonCore C) : HonCore C' := by
  refine honCore_transfer ?_ hvis h
  intro e
  constructor
  · rintro ⟨r', s', hLs, hse⟩
    rw [hL] at hLs
    by_cases hr : r' = r
    · subst hr
      rw [updateRep_self] at hLs
      injection hLs with hs
      subst hs
      exact hse.elim
    · rw [updateRep_other _ _ hr] at hLs
      exact ⟨r', s', hLs, hse⟩
  · rintro ⟨r', s', hLs, hse⟩
    by_cases hr : r' = r
    · subst hr
      rw [(C.dom_eq r').mp h_fresh] at hLs
      simp at hLs
    · exact ⟨r', s', by rw [hL, updateRep_other _ _ hr]; exact hLs, hse⟩

theorem honCore_merge {C C' : Cfg3} {r₁ r₂ : Replica} {v₁ v₂ : Version}
    {s₁ s₂ : (QD).State} {ev₁ ev₂ : Set op_t}
    (h_head₁ : C.head r₁ = some v₁) (h_head₂ : C.head r₂ = some v₂)
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂))
    (hL : C'.L = updateRep C.L r₁ (ev₁ ∪ ev₂))
    (hvis : C'.vis = C.vis)
    (h : HonCore C) : HonCore C' := by
  have hLr₁ : C.L r₁ = some ev₁ := by
    rw [← (C.head_coherent r₁ v₁ h_head₁).2, h_ver₁]; rfl
  have hLr₂ : C.L r₂ = some ev₂ := by
    rw [← (C.head_coherent r₂ v₂ h_head₂).2, h_ver₂]; rfl
  refine honCore_transfer ?_ hvis h
  intro e
  constructor
  · rintro ⟨r', s', hLs, hse⟩
    rw [hL] at hLs
    by_cases hr : r' = r₁
    · subst hr
      rw [updateRep_self] at hLs
      injection hLs with hs
      subst hs
      rcases hse with h1 | h2
      · exact ⟨r', ev₁, hLr₁, h1⟩
      · exact ⟨r₂, ev₂, hLr₂, h2⟩
    · rw [updateRep_other _ _ hr] at hLs
      exact ⟨r', s', hLs, hse⟩
  · rintro ⟨r', s', hLs, hse⟩
    by_cases hr : r' = r₁
    · subst hr
      rw [hLr₁] at hLs
      injection hLs with hs
      subst hs
      exact ⟨r', ev₁ ∪ ev₂, by rw [hL, updateRep_self], Or.inl hse⟩
    · exact ⟨r', s', by rw [hL, updateRep_other _ _ hr]; exact hLs, hse⟩

/-- **The apply step** — the only step that adds an event.  Freshness (`h_fresh_t`), the
structural Lamport field of the POST-configuration, born accuracy, and `WfOpQ` of the new op
maintain all four clauses. -/
theorem honCore_apply {C C' : Cfg3} {t : Timestamp} {r : Replica} {o : app_op_t}
    {v : Version} {sh : (QD).State} {evh : Set op_t}
    (h_head : C.head r = some v) (h_ver : C.ver v = some (sh, evh))
    (h_fresh_t : ∀ e', e' ∈ C.events → Op.time e' ≠ t)
    (hL : C'.L = updateRep C.L r (evh ∪ {(t, r, o)}))
    (hvis : C'.vis = fun a b => C.vis a b ∨ (evh a ∧ b = (t, r, o)))
    (hborn : ∃ π : List op_t, listPermOf π evh ∧
        respects π (fun a b : op_t => C.vis a b) ∧
        accurate (t, r, o) (applySeqR init_st π))
    (hwfQ : ∃ σ : concrete_st, WfOpQ (t, r, o) σ)
    (h : HonCore C) : HonCore C' := by
  have hLr : C.L r = some evh := by
    rw [← (C.head_coherent r v h_head).2, h_ver]; rfl
  have hevh_sub : ∀ a ∈ evh, a ∈ C.events := fun a ha => ⟨r, evh, hLr, ha⟩
  have hnew_not : ((t, r, o) : op_t) ∉ C.events := fun hm => h_fresh_t _ hm rfl
  -- the event universe grows by exactly the new op
  have hE : ∀ e : op_t, e ∈ C'.events ↔ e ∈ C.events ∨ e = (t, r, o) := by
    intro e
    constructor
    · rintro ⟨r', s', hLs, hse⟩
      rw [hL] at hLs
      by_cases hr : r' = r
      · subst hr
        rw [updateRep_self] at hLs
        injection hLs with hs
        subst hs
        rcases hse with h1 | h2
        · exact Or.inl (hevh_sub _ h1)
        · exact Or.inr h2
      · rw [updateRep_other _ _ hr] at hLs
        exact Or.inl ⟨r', s', hLs, hse⟩
    · rintro (he | rfl)
      · obtain ⟨r', s', hLs, hse⟩ := he
        by_cases hr : r' = r
        · subst hr
          rw [hLr] at hLs
          injection hLs with hs
          subst hs
          exact ⟨r', evh ∪ {(t, r', o)}, by rw [hL, updateRep_self], Or.inl hse⟩
        · exact ⟨r', s', by rw [hL, updateRep_other _ _ hr]; exact hLs, hse⟩
      · exact ⟨r, evh ∪ {(t, r, o)}, by rw [hL, updateRep_self], Or.inr rfl⟩
  -- the new op's timestamp is nonzero: WfOpQ for inserts; Lamport-over-the-target for deletes
  have ht0 : t ≠ 0 := by
    obtain ⟨σ, hq⟩ := hwfQ
    cases o with
    | Ins e p a => exact hq.1.1
    | Del p x =>
      have hx0 : x ≠ 0 := by
        rintro rfl
        rcases hq.2 with h0 | hlt
        · exact hq.1 h0
        · exact Nat.not_lt_zero _ hlt
      obtain ⟨π, hπp, _, hπacc⟩ := hborn
      simp only [accurate, opLeaf, opPath] at hπacc
      rcases hπacc with ⟨h0eq, _⟩ | ⟨hlive, _⟩
      · exact absurd h0eq hx0
      · obtain ⟨rx, ex, px, ax, hmx⟩ := insertedIn_of_contains_fold π x hlive
        have hxevh : ((x, rx, app_op_t.Ins ex px ax) : op_t) ∈ evh := (hπp.2 _).mp hmx
        have hvis' : C'.vis (x, rx, app_op_t.Ins ex px ax) (t, r, app_op_t.Del p x) := by
          rw [hvis]
          exact Or.inr ⟨hxevh, rfl⟩
        have hlt : x < t := C'.causal_mono hvis'
        intro ht
        rw [ht] at hlt
        exact Nat.not_lt_zero _ hlt
  obtain ⟨⟨lE, hlE⟩, hz, hd, hb⟩ := h
  refine ⟨⟨lE ++ [(t, r, o)], ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- Nodup: the new op is fresh
    refine List.nodup_append.mpr ⟨hlE.1, List.nodup_singleton _, ?_⟩
    intro a ha b hb' heq
    rw [List.mem_singleton] at hb'
    subst hb'
    subst heq
    exact hnew_not ((hlE.2 _).mp ha)
  · -- membership
    intro a
    rw [List.mem_append, List.mem_singleton, hE a]
    exact or_congr (hlE.2 a) Iff.rfl
  · -- nonzero ids
    intro o' ho'
    rcases (hE o').mp ho' with hold | rfl
    · exact hz o' hold
    · exact ht0
  · -- no root deletes
    intro t' r' x p hm
    rcases (hE _).mp hm with hold | heq
    · exact hd t' r' x p hold
    · obtain ⟨σ, hq⟩ := hwfQ
      have h3 := congrArg (fun z : op_t => z.2.2) heq
      cases o with
      | Ins e p₀ a₀ => exact app_op_t.noConfusion h3
      | Del p₀ x₀ =>
        injection h3 with h3p h3x
        subst h3x
        rintro rfl
        rcases hq.2 with h0 | hlt
        · exact hq.1 h0
        · exact Nat.not_lt_zero _ hlt
  · -- born accuracy
    intro o' ho'
    rcases (hE o').mp ho' with hold | rfl
    · -- an old event: its past and its witness are untouched
      obtain ⟨π, hπp, hπr, hπacc⟩ := hb o' hold
      have ho'ne : o' ≠ (t, r, o) := fun he => hnew_not (he ▸ hold)
      refine ⟨π, ⟨hπp.1, fun z => (hπp.2 z).trans ?_⟩, ?_, hπacc⟩
      · constructor
        · rintro ⟨hz', hv⟩
          exact ⟨(hE z).mpr (Or.inl hz'), by rw [hvis]; exact Or.inl hv⟩
        · rintro ⟨hz', hv⟩
          rw [hvis] at hv
          rcases hv with hv | ⟨_, heq⟩
          · rcases (hE z).mp hz' with hzo | rfl
            · exact ⟨hzo, hv⟩
            · exact absurd (C.vis_src hv) hnew_not
          · exact absurd heq ho'ne
      · refine hπr.imp_of_mem ?_
        intro a b ha _hb hn hv
        rw [hvis] at hv
        rcases hv with hv | ⟨_, heq⟩
        · exact hn hv
        · exact hnew_not (heq ▸ ((hπp.2 a).mp ha).1)
    · -- the new op: its past is exactly the head version's events
      obtain ⟨π, hπp, hπr, hπacc⟩ := hborn
      refine ⟨π, ⟨hπp.1, fun z => (hπp.2 z).trans ?_⟩, ?_, hπacc⟩
      · constructor
        · intro hz'
          refine ⟨(hE z).mpr (Or.inl (hevh_sub _ hz')), ?_⟩
          rw [hvis]
          exact Or.inr ⟨hz', rfl⟩
        · rintro ⟨hz', hv⟩
          rw [hvis] at hv
          rcases hv with hv | ⟨hev, _⟩
          · exact absurd (C.vis_tgt hv) hnew_not
          · exact hev
      · refine hπr.imp_of_mem ?_
        intro a b ha _hb hn hv
        rw [hvis] at hv
        rcases hv with hv | ⟨_, heq⟩
        · exact hn hv
        · exact hnew_not (heq ▸ hevh_sub _ ((hπp.2 a).mp ha))

/-- The honest-core invariant at every reachable configuration. -/
theorem honCore_of_reach (hHD : HonestDelivery) {C : Cfg3} (hReach : Reach3 C) :
    HonCore C := by
  induction hReach with
  | refl => exact honCore_init
  | tail hpre hs ih =>
    obtain ⟨ℓ, hstep⟩ := hs
    cases ℓ with
    | createReplica r =>
      cases hstep with
      | createReplica h_fresh C' hN hL hvis hver hhead hparents =>
        exact honCore_createReplica h_fresh hL hvis ih
    | apply t r o =>
      have hstep' := hstep
      cases hstep with
      | apply h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank C'
          hN hL hvis hver hhead hparents =>
        obtain ⟨hborn, hq, himp⟩ := hHD hpre hstep' h_head h_ver
        exact honCore_apply h_head h_ver h_fresh_t hL hvis hborn (wfOpQ_of_hBA hq himp) ih
    | merge r₁ r₂ =>
      cases hstep with
      | merge h_head₁ h_head₂ h_ver₁ h_ver₂ h_lca h_verT h_vm h_rank₁ h_rank₂ C'
          hN hL hvis hver hhead hparents =>
        exact honCore_merge h_head₁ h_head₂ h_ver₁ h_ver₂ hL hvis ih
    | query r q vq =>
      cases hstep with
      | query h_s h_val => exact ih

/-! ## §4  hHon and hBA, discharged -/

/-- **hHon, discharged**: the join context holds at every reachable core.  The witness is the
re-typed core itself; visibility restriction is `vis_src`/`vis_tgt`, Lamport is the structural
`causal_mono`, id-uniqueness is `timestamps_distinct`, and the generation discipline is
`genDisc2C_of_born` at the honest-core invariant. -/
theorem rga_hHon_discharged (hHD : HonestDelivery) :
    ∀ {C₀ : Cfg3}, Reach3 C₀ →
      rgaHonJ (Sal.Metatheory.Configuration.core C₀).vis
        (Sal.Metatheory.Configuration.core C₀).events := by
  intro C₀ hreach
  obtain ⟨⟨lE, hlE⟩, hz, hd, hb⟩ := honCore_of_reach hHD hreach
  have hS := goodConfig3S_of_reach hreach
  refine ⟨coreR C₀, ?_, ?_, hz, ?_, hd⟩
  · -- the witness's visibility is the ambient visibility restricted to events
    intro a b
    exact ⟨fun h => ⟨h, C₀.vis_src h, C₀.vis_tgt h⟩, fun h => h.1⟩
  · -- the generation discipline, from born accuracy
    refine genDisc2C_of_born (coreR C₀) (Sal.Metatheory.Configuration.core C₀).events lE hlE
      (fun a b ha hb' hne => ?_) hz
      (fun hab hbc => hS.vis_trans hab hbc) hS.vis_irrefl
      (fun o ho => ?_)
    · obtain ⟨ra, sa, hLa, hsa⟩ := ha
      obtain ⟨rb, sb, hLb, hsb⟩ := hb'
      exact C₀.timestamps_distinct hLa hsa hLb hsb hne
    · obtain ⟨π, hπp, hπr, hπacc⟩ := hb o ho
      exact ⟨π, hπp,
        hπr.imp (fun hn hlo => hn (loOnA_imp_vis (coreR C₀) _ _ _ hlo)), hπacc⟩
  · -- Lamport monotonicity is structural
    exact fun a b _ _ h => C₀.causal_mono h

/-! ## §5  THE HONEST CAPSTONE -/

/-- **RGA RA-linearizability up to ≈, on the honest-delivery residual alone.**  Every reachable
configuration of the quotient LTS is per-version RA-linearizable up to observational `≈`, given
only `HonestDelivery`: each delivered op was generated accurately against a causal fold of the
events it had seen, and delivery is born-applicable. -/
theorem rga_RA_linearizable_honest (hHD : HonestDelivery)
    (C : Cfg3) (hReach : Reach3 C) :
    IsRALinearizable3Eq rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA C :=
  rga_RA_linearizable_final
    (fun hreach => rga_hHon_discharged hHD hreach)
    (fun hreach hstep hhead hver => (hHD hreach hstep hhead hver).2)
    C hReach

/-! ## Axiom audit -/

#print axioms wfOpQ_of_hBA
#print axioms goodConfig3S_of_reach
#print axioms honCore_of_reach
#print axioms rga_hHon_discharged
#print axioms rga_RA_linearizable_honest

end Sal.Metatheory.RGASkeleton3
