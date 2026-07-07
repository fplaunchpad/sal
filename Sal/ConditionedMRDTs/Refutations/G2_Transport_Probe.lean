import Sal.ConditionedMRDTs.Framework.Sigma_LoOn3
import Sal.MRDTs.RGA_Tombstone_Free.RGA_Reachability_Invariant
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_CondSig
import Sal.ConditionedMRDTs.Framework.LoOnC

/-!
# Gate G2 (OQ4): permutation-transport of the RGA invariant — the probe

Task #3 of `CONDITIONED_METATHEORY_PLAN.md`. The feasible update layer wants the
convergence induction (`convergence_on_u`, `Sigma_LoOn3.lean:372`) to run with
`CRDTSig.commutes` replaced by `ConditionedMRDTSig.commutesOn` (`MRDTSig.lean:73`)
at every ⚑ site. This file maps the ⚑ sites, discharges obligation (A)
(Inv-transport) generically, and **refutes** obligation (B)
(applicability-transport) with a kernel-checked 2-event counterexample.

## The ⚑-site map

The induction `convergence_on_u` peels the head `e` of π₁ and bubbles `e` to the
front of π₂ = σ ++ e :: τ (`applySeq_bubble_to_front_loOn_u`,
`Sigma_LoOn3.lean:320`). Commutation is invoked at exactly two families of sites,
both inside `applySeq_swap_loOn_incomparable_u` (`Sigma_LoOn3.lean:279`):

* **⚑1 (`Sigma_LoOn3.lean:296`)** — the `D.commutes a b` branch
  (`applySeq_swap_commute`, `Merge_Linearization.lean:394`): the adjacent pair
  `(y, e)` is swapped at the state `applySeq D D.init (peeled π₁-prefix ++
  bubbled σ-prefix)`.  These are **hybrid** states: prefix-folds of mid-bubble
  permutations that are themselves NOT `loOn`-respecting enumerations.
* **⚑2 (`Sigma_LoOn3.lean:60,313-317`)** — the `cond_comm_lift` VC, invoked at
  the same hybrid states with an arbitrary interleaved residual `π`.

So the conditioned induction needs, at every hybrid prefix-fold state `σ*`:
**(A)** `Inv σ*`, and **(B)** `applicable e σ*` for both swapped events —
because `commutesOn` (`MRDTSig.lean:73`) only yields the swap under
`Inv σ* → applicable e₁ σ* → applicable e₂ σ*`.

## Verdicts (mechanized below, 0 sorries)

* **(A) = PROVABLE, unconditionally, and decoupled from (B).**
  `Inv_doIns`/`Inv_doDel` (`RGA_Reachability_Invariant.lean`) take the
  state-dependent hypotheses `accurate`/`fresh_ts`, which would entangle (A)
  with (B).  But the *load-bearing* content is order-stable and op-only:
  `Ins` needs only `t ≠ 0`, `Del` needs only `x ∉ pre` (packaged as `opOK`;
  derivable at generation time — `opOK_of_generation`).  With `opOK`, `RgaInv`
  transports along **every** permutation and every mid-bubble hybrid
  (`Inv_transport_generic`/`obligation_A_RGA`), covering all ⚑ states.
* **(B) = FALSE — trichotomy branch (ii).**  Counterexample `insOpE`/`delOpE`
  below: a genuine single-replica execution (insert node 1, then delete node 1)
  whose conditioned `lo` has NO edge between the two events — `fresh_ts insOpE`
  demands node 1 absent, `accurate delOpE` demands node 1 present, so the two
  events are never jointly applicable and `commutesOn` holds **vacuously** in
  both directions, while `rc = Either` kills the rc-flavored edge.  Hence both
  `[ins, del]` and `[del, ins]` respect the conditioned `loOn`, but they fold to
  different states.  The conditioned convergence statement is refuted outright
  (`G2_conditioned_convergence_refuted`), not merely unprovable.
* **Route (iii) (strengthened `Inv`) is DEAD**: the failing enumeration's every
  state satisfies `RgaInv` (`bad_enumeration_stays_in_Inv`), and conditioning is
  *antitone* — strengthening `Inv`/`applicable` shrinks `commutesOn`'s domain,
  makes `commutesOn` easier, hence **removes** `lo`-edges and admits MORE
  enumerations.  No state-shape envelope can restore the lost edge.
* **Contrast**: the unconditioned binary `loOn` keeps the edge
  (`binary_loOn_keeps_edge`) and correctly excludes the bad order
  (`binary_respects_excludes_bad_order`) — the failure is introduced exactly by
  the `commutes ↦ commutesOn` substitution.

Consequence for the feasible update layer: the conditioned `lo` must be
**applicability-aware** — a vis-edge `e₁ → e₂` must survive not only when
`¬ commutesOn e₁ e₂` but also when `e₂`'s applicability *depends on* `e₁`
(generation dependency; for the RGA this is op-syntactic: `e₂` references
`e₁`'s timestamp as Del-target / Ins-anchor / path member).  See
`G2_FINDINGS.md` for the proposed interface.
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs.G2Probe

open Sal.Emulation
open Sal.ConditionedMRDTs.RGASig

/-! ## §1–§3 — moved to `RGA_CondSig.lean`

The generic Inv-transport (§1), the op-only `opOK` layer (§2), and the
packaged signature `RGAM`/`RGACondSig` (§3) now live in `RGA_CondSig.lean`
(namespace `Sal.ConditionedMRDTs.RGASig`); the set-relative order `loOnC` lives in
`LoOnC.lean` (namespace `Sal.ConditionedMRDTs`).  This file keeps the ⚑-site map
and the obligation-(B) refutation. -/

/-! ## §4 Obligation (B): the counterexample

A genuine single-replica execution: `insOpE` inserts node `1` at the root,
`delOpE` deletes node `1`.  Both are applicable at their generation states
(`insOpE_applicable_at_init`, `delOpE_applicable_after_ins`), and
`vis insOpE delOpE` (program order).  Yet:

* they are **never jointly applicable** — `fresh_ts insOpE s` forces
  `contains s 1 = false`, `accurate delOpE s` forces `contains s 1 = true` —
  so `commutesOn` holds VACUOUSLY in both directions;
* `rc = Either` kills the rc-flavored edge;
* hence the conditioned `lo` (both `Sal.ConditionedMRDTs.lo` and the set-relative
  `loOnC` the update layer would use) has NO edge between them, both orders are
  admissible, and the folds differ: `[ins, del] ↦ ∅` but `[del, ins] ↦ {1}`. -/

/-- Insert element 65 as node `1` anchored at the root (path `[]`). -/
def insOpE : Op app_op_t := (1, 0, .Ins 65 [] 0)

/-- Delete node `1` (its true ancestor chain at generation time is `[]`). -/
def delOpE : Op app_op_t := (2, 0, .Del [] 1)

theorem ins_ne_del : insOpE ≠ delOpE := by decide

/-- A freshly inserted node is present. -/
theorem contains_doIns_self (s : concrete_st) (t r e a : ℕ) (pre : List ℕ) :
    contains (do_ s (t, r, .Ins e pre a)) t = true := by
  simp only [do_]
  rw [lemma_InDomUpd1]
  simp

/-- **The two admissible orders fold to different states.**
`[ins, del]` yields the empty sequence; `[del, ins]` leaves node `1` alive. -/
theorem folds_differ :
    do_ (do_ init_st insOpE) delOpE ≠ do_ (do_ init_st delOpE) insOpE := by
  intro hEq
  have h1 : contains (do_ (do_ init_st insOpE) delOpE) 1
          = contains (do_ (do_ init_st delOpE) insOpE) 1 :=
    congrArg (fun st => contains st 1) hEq
  have hL : contains (do_ (do_ init_st insOpE) delOpE) 1 = false := by
    show contains (do_ (do_ init_st insOpE) (2, 0, app_op_t.Del [] 1)) 1 = false
    rw [contains_doDel]
    simp
  have hR : contains (do_ (do_ init_st delOpE) insOpE) 1 = true := by
    show contains (do_ (do_ init_st delOpE) (1, 0, app_op_t.Ins 65 [] 0)) 1 = true
    exact contains_doIns_self (do_ init_st delOpE) 1 0 65 0 []
  rw [hL, hR] at h1
  exact Bool.noConfusion h1

/-! ### The counterexample is a genuine execution -/

/-- `insOpE` is applicable (accurate + fresh) at the initial state. -/
theorem insOpE_applicable_at_init :
    accurate insOpE init_st ∧ fresh_ts insOpE init_st := by
  constructor
  · exact Or.inl ⟨rfl, rfl⟩
  · show (1 : ℕ) ≠ 0 ∧ contains init_st 1 = false
    exact ⟨one_ne_zero, by simp [init_st]⟩

/-- `delOpE` is applicable at its generation state (right after `insOpE`):
node `1` is live and its true ancestor chain is `[]`. -/
theorem delOpE_applicable_after_ins :
    accurate delOpE (do_ init_st insOpE) ∧ fresh_ts delOpE (do_ init_st insOpE) := by
  constructor
  · refine Or.inr ⟨?_, ?_⟩
    · show contains (do_ init_st (1, 0, app_op_t.Ins 65 [] 0)) 1 = true
      exact contains_doIns_self init_st 1 0 65 0 []
    · show anc (do_ init_st (1, 0, app_op_t.Ins 65 [] 0)) 1 = 0
      have hdo : do_ init_st (1, 0, app_op_t.Ins 65 [] 0)
               = upd init_st 1 (65, resolve init_st (0 :: [])) := by
        simp only [do_]
      rw [hdo]
      show (sel (upd init_st 1 (65, resolve init_st (0 :: []))) 1).2 = 0
      rw [lemma_SelUpd1]
      show resolve init_st (0 :: []) = 0
      rw [resolve_dead_head init_st 0 [] (by simp [init_st])]
      rfl
  · show True
    trivial

/-! ### Vacuous conditioning: the pair is never jointly applicable -/

/-- The heart of the failure: `fresh_ts insOpE` demands node `1` ABSENT while
`accurate delOpE` demands node `1` PRESENT — no state satisfies both, so the
conditioned commutation quantifier is empty. -/
theorem never_jointly_applicable (s : concrete_st)
    (hIns : accurate insOpE s ∧ fresh_ts insOpE s)
    (hDel : accurate delOpE s ∧ fresh_ts delOpE s) : False := by
  obtain ⟨_, hfr⟩ := hIns
  obtain ⟨hacc, _⟩ := hDel
  have hfr' : (1 : ℕ) ≠ 0 ∧ contains s 1 = false := hfr
  have hacc' : ((1 : ℕ) = 0 ∧ ([] : List ℕ) = []) ∨
      (contains s 1 = true ∧ IsAncPath s 1 []) := hacc
  rcases hacc' with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact one_ne_zero h1
  · rw [hfr'.2] at h1
    exact Bool.noConfusion h1

/-- `commutesOn insOpE delOpE` holds — VACUOUSLY. -/
theorem G2_commutesOn_ins_del : RGACondSig.commutesOn insOpE delOpE := by
  intro s _hInv hIns hDel
  exact (never_jointly_applicable s hIns hDel).elim

/-- `commutesOn delOpE insOpE` holds — VACUOUSLY. -/
theorem G2_commutesOn_del_ins : RGACondSig.commutesOn delOpE insOpE := by
  intro s _hInv hDel hIns
  exact (never_jointly_applicable s hIns hDel).elim

/-! ### The conditioned linearization order loses the edge -/

/-- In ANY configuration and relative to ANY event set, the conditioned
set-relative order has no edge between `insOpE` and `delOpE` in either
direction: the vis-flavor dies on the vacuous `commutesOn`, the rc-flavor dies
on `rc = Either`. -/
theorem no_loOnC_edge (C : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (ev : Set (Op app_op_t)) :
    ¬ loOnC RGACondSig C ev insOpE delOpE
    ∧ ¬ loOnC RGACondSig C ev delOpE insOpE := by
  constructor
  · rintro (⟨_, hnc⟩ | ⟨_, _, hrc, _⟩)
    · exact hnc G2_commutesOn_ins_del
    · rw [rc_is_Either] at hrc
      exact RcRes.noConfusion hrc
  · rintro (⟨_, hnc⟩ | ⟨_, _, hrc, _⟩)
    · exact hnc G2_commutesOn_del_ins
    · rw [rc_is_Either] at hrc
      exact RcRes.noConfusion hrc

/-- Same for the repo's global conditioned `lo` (`MRDTSig.lean:89`). -/
theorem no_metatheory_lo_edge (C : Sal.Emulation.Configuration RGACondSig.toCRDTSig) :
    ¬ Sal.ConditionedMRDTs.lo RGACondSig C insOpE delOpE
    ∧ ¬ Sal.ConditionedMRDTs.lo RGACondSig C delOpE insOpE := by
  constructor
  · rintro (⟨_, hnc⟩ | ⟨_, _, hrc, _⟩)
    · exact hnc G2_commutesOn_ins_del
    · rw [rc_is_Either] at hrc
      exact RcRes.noConfusion hrc
  · rintro (⟨_, hnc⟩ | ⟨_, _, hrc, _⟩)
    · exact hnc G2_commutesOn_del_ins
    · rw [rc_is_Either] at hrc
      exact RcRes.noConfusion hrc

/-! ### The concrete configuration

The reachable shape a single replica produces via
`createReplica 0; apply insOpE; apply delOpE` (see `CRDT_TS.lean` `Step.apply`:
the second apply adds exactly the edge `insOpE → delOpE`).  Step-reachability
is noted, not mechanized — the convergence machinery consumes only the
structural fields below, so the refutation targets it verbatim. -/

def evCex : Set (Op app_op_t) := {insOpE, delOpE}

private theorem optL_inv {α : Type} {x y : α} {r : ℕ}
    (h : (if r = 0 then some x else none) = some y) : x = y := by
  by_cases hr : r = 0
  · rw [if_pos hr] at h
    exact Option.some.inj h
  · rw [if_neg hr] at h
    exact absurd h (by simp)

noncomputable def Ccex : Sal.Emulation.Configuration RGACondSig.toCRDTSig where
  N := fun r => if r = 0 then some (do_ (do_ init_st insOpE) delOpE) else none
  L := fun r => if r = 0 then some evCex else none
  vis := fun a b => a = insOpE ∧ b = delOpE
  dom_eq := by
    intro r
    by_cases h : r = 0 <;> simp [h]
  vis_src := by
    intro a b hv
    obtain ⟨rfl, rfl⟩ := hv
    exact ⟨0, evCex, rfl, Set.mem_insert _ _⟩
  vis_tgt := by
    intro a b hv
    obtain ⟨rfl, rfl⟩ := hv
    exact ⟨0, evCex, rfl, Set.mem_insert_of_mem _ rfl⟩
  vis_causal := by
    intro a b r s hv hL _hb
    obtain ⟨rfl, rfl⟩ := hv
    obtain rfl := optL_inv hL
    exact Set.mem_insert _ _
  timestamps_distinct := by
    intro a b r s r' s' hL ha hL' hb hne
    obtain rfl := optL_inv hL
    obtain rfl := optL_inv hL'
    have ha' : a = insOpE ∨ a = delOpE := ha
    have hb' : b = insOpE ∨ b = delOpE := hb
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact absurd rfl hne
    · decide
    · decide
    · exact absurd rfl hne
  vis_total_same_replica := by
    intro a b r s r' s' hL ha hL' hb hne _hrep
    obtain rfl := optL_inv hL
    obtain rfl := optL_inv hL'
    have ha' : a = insOpE ∨ a = delOpE := ha
    have hb' : b = insOpE ∨ b = delOpE := hb
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact absurd rfl hne
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact absurd rfl hne

theorem Ccex_vis_trans : ∀ {a b c : Op app_op_t},
    Ccex.vis a b → Ccex.vis b c → Ccex.vis a c := by
  intro a b c hab hbc
  obtain ⟨rfl, rfl⟩ := hab
  obtain ⟨h1, _⟩ := hbc
  exact absurd h1 (by decide)

theorem Ccex_vis_irrefl : ∀ a : Op app_op_t, ¬ Ccex.vis a a := by
  rintro a ⟨h1, h2⟩
  exact ins_ne_del (h1.symm.trans h2)

theorem Ccex_ev_in : ∀ a ∈ evCex, a ∈ Ccex.events :=
  fun a ha => ⟨0, evCex, rfl, ha⟩

/-! ### Both orders are admissible -/

theorem perm_ins_del : listPermOf [insOpE, delOpE] evCex := by
  constructor
  · decide
  · intro a
    constructor
    · intro h
      rcases List.mem_cons.mp h with rfl | h
      · exact Set.mem_insert _ _
      · rw [List.mem_singleton] at h
        subst h
        exact Set.mem_insert_of_mem _ rfl
    · intro h
      have h' : a = insOpE ∨ a = delOpE := h
      rcases h' with rfl | rfl
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ List.mem_cons_self

theorem perm_del_ins : listPermOf [delOpE, insOpE] evCex := by
  constructor
  · decide
  · intro a
    constructor
    · intro h
      rcases List.mem_cons.mp h with rfl | h
      · exact Set.mem_insert_of_mem _ rfl
      · rw [List.mem_singleton] at h
        subst h
        exact Set.mem_insert _ _
    · intro h
      have h' : a = insOpE ∨ a = delOpE := h
      rcases h' with rfl | rfl
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact List.mem_cons_self

theorem respects_ins_del (C : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (ev : Set (Op app_op_t)) :
    respects [insOpE, delOpE] (loOnC RGACondSig C ev) := by
  show List.Pairwise (fun a b => ¬ loOnC RGACondSig C ev b a) [insOpE, delOpE]
  refine List.pairwise_cons.mpr ⟨?_, List.pairwise_singleton _ _⟩
  intro b hb
  rw [List.mem_singleton] at hb
  subst hb
  exact (no_loOnC_edge C ev).2

theorem respects_del_ins (C : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (ev : Set (Op app_op_t)) :
    respects [delOpE, insOpE] (loOnC RGACondSig C ev) := by
  show List.Pairwise (fun a b => ¬ loOnC RGACondSig C ev b a) [delOpE, insOpE]
  refine List.pairwise_cons.mpr ⟨?_, List.pairwise_singleton _ _⟩
  intro b hb
  rw [List.mem_singleton] at hb
  subst hb
  exact (no_loOnC_edge C ev).1

/-! ### The kill theorem -/

/-- **Gate G2, verdict (B) = FALSE.**  The conditioned analogue of
`convergence_on_u` (`Sigma_LoOn3.lean:372`) — `commutes ↦ commutesOn` inside the
linearization order, all other hypotheses kept (vis-transitivity,
vis-irreflexivity, events-in-configuration) — is REFUTED by the tombstone-free
RGA: the 2-event set `{insOpE, delOpE}` of a genuine single-replica execution
admits two loOnC-respecting enumerations with different folds.

The failure is at the FIRST fold step of the bad enumeration (`delOpE` applied
at `init`, where it is not applicable), i.e. obligation (B) fails already at
ordinary prefix states — before any mid-bubble hybrid subtleties arise. -/
theorem G2_conditioned_convergence_refuted :
    ¬ (∀ (C : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
         (ev : Set (Op RGACondSig.AppOp))
         (π₁ π₂ : List (Op RGACondSig.AppOp)),
        (∀ {a b c : Op RGACondSig.AppOp}, C.vis a b → C.vis b c → C.vis a c) →
        (∀ a : Op RGACondSig.AppOp, ¬ C.vis a a) →
        (∀ a ∈ ev, a ∈ C.events) →
        listPermOf π₁ ev → listPermOf π₂ ev →
        respects π₁ (loOnC RGACondSig C ev) →
        respects π₂ (loOnC RGACondSig C ev) →
        applySeq RGACondSig.toCRDTSig RGACondSig.init π₁
          = applySeq RGACondSig.toCRDTSig RGACondSig.init π₂) := by
  intro hconv
  have h := hconv Ccex evCex [insOpE, delOpE] [delOpE, insOpE]
    Ccex_vis_trans Ccex_vis_irrefl Ccex_ev_in
    perm_ins_del perm_del_ins
    (respects_ins_del Ccex evCex) (respects_del_ins Ccex evCex)
  rw [applySeq_two, applySeq_two] at h
  exact folds_differ h

/-! ### Contrast and the death of route (iii) -/

/-- Unconditioned, the pair genuinely does not commute (witness: `init_st`). -/
theorem insdel_not_commutes_unconditioned :
    ¬ RGACondSig.toCRDTSig.commutes insOpE delOpE :=
  fun h => folds_differ (h init_st)

/-- The UNCONDITIONED binary `loOn` keeps the vis-edge `insOpE → delOpE` —
conditioning (`commutes ↦ commutesOn`) is exactly what deletes it. -/
theorem binary_loOn_keeps_edge (ev : Set (Op app_op_t)) :
    loOn Ccex ev insOpE delOpE :=
  Or.inl ⟨⟨rfl, rfl⟩, insdel_not_commutes_unconditioned⟩

/-- Consequently the unconditioned machinery correctly EXCLUDES the bad
enumeration: `[delOpE, insOpE]` does not respect `loOn Ccex evCex`. -/
theorem binary_respects_excludes_bad_order :
    ¬ respects [delOpE, insOpE] (loOn Ccex evCex) := by
  intro h
  have h1 := (List.pairwise_cons.mp h).1 insOpE List.mem_cons_self
  exact h1 (binary_loOn_keeps_edge evCex)

/-- **Route (iii) — a strengthened state invariant — cannot repair (B)**: every
state visited by the failing enumeration `[delOpE, insOpE]` satisfies `RgaInv`
(obligation (A) holds along it!).  The defect is in `applicable`, which the
`lo`-edge predicate consults only under a quantifier that conditioning makes
vacuous; strengthening `Inv` only shrinks that quantifier further. -/
theorem bad_enumeration_stays_in_Inv :
    RgaInv init_st
    ∧ RgaInv (do_ init_st delOpE)
    ∧ RgaInv (do_ (do_ init_st delOpE) insOpE) := by
  have h1 : RgaInv (do_ init_st delOpE) :=
    RgaInv_do_opOK init_st delOpE Inv_init
      (show (1 : ℕ) ∉ ([] : List ℕ) from List.not_mem_nil)
  refine ⟨Inv_init, h1, ?_⟩
  exact RgaInv_do_opOK (do_ init_st delOpE) insOpE h1
    (show (1 : ℕ) ≠ 0 from one_ne_zero)

/-! ## §5 Axiom audit — all kernel-checked (no `native_decide`) -/

#print axioms G2_conditioned_convergence_refuted
#print axioms binary_respects_excludes_bad_order
#print axioms bad_enumeration_stays_in_Inv

/-!
## VERDICT (Gate G2)

**(A) Inv-transport: DISCHARGED, generically and decoupled from (B).**
`Inv_transport_generic` + `RgaInv_do_opOK` prove `RgaInv` at every prefix-fold
of EVERY enumeration (including the ⚑ sites' mid-bubble hybrids) from op-only
side conditions `opOK` (`Ins`: `t ≠ 0`; `Del`: `x ∉ pre`), which
`opOK_of_generation` extracts once from applicability at the generation state.
The published `Inv_doIns`/`Inv_doDel` hypotheses (`accurate`/`fresh_ts`) are
stronger than needed; had they been load-bearing, (A) would have entangled with
(B) and failed with it.

**(B) applicability-transport: FALSE — trichotomy branch (ii).**
`G2_conditioned_convergence_refuted`.  Root cause: *vacuous conditioning* —
creation dependencies (an op referencing a node another op creates) make the
two events never jointly applicable, so `commutesOn` is vacuously true and the
conditioned `lo` drops precisely the vis-edges that creation order needs.
Not a path-staleness phenomenon: the path-carrying design tolerates stale
paths at swap sites (that is what `resolve`-climbing is for); hand-checked
concurrent Ins/Del scenarios converge.  The failure is confined to vis-ordered
create-then-use pairs.

**Monotonicity (kills route (iii)):** `commutesOn` is antitone in the strength
of `(Inv, applicable)` — a stronger condition means a smaller quantification
domain, hence MORE vacuous commutation, hence FEWER `lo`-edges, hence MORE
admissible enumerations.  Conditioning that rescues the commutation VCs
monotonically destroys the linearization order.  `bad_enumeration_stays_in_Inv`
shows the failing enumeration is `Inv`-internal, so no swap-closed state
envelope exists that excludes it.

**What the feasible update layer actually needs** (see G2_FINDINGS.md):
an applicability-aware `lo` — keep the vis-edge `e₁ → e₂` when
`¬ commutesOn e₁ e₂` OR when `e₂`'s applicability depends on `e₁`
(for the RGA an op-syntactic, decidable dependency: `e₂` mentions `e₁`'s
timestamp as Del-target, Ins-anchor, or path member), plus the (A) transport
above as a separate generic obligation.  Alternatively, restrict the
enumeration class to applicability-admissible ones — but then the bubble-sort's
hybrid states must be proved admissible, a new and harder obligation, since
swaps visit states no execution visits.
-/

end Sal.ConditionedMRDTs.G2Probe
