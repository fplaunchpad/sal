import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_Instance
import Sal.ConditionedMRDTs.Framework.ConditionedConvergence
import Sal.ConditionedMRDTs.Development.RGA_WfOpReachable

/-!
# The RGA order bridge: `loOnEq` vs `loOnA` — the orders are INCOMPARABLE

Target (`RGA_Instance.lean` §7 residual): relate the framework's
`≈`-conditioned linearization order `loOnEq rgaEqEquiv' WfOp` to the RGA's
applicability-aware order `loOnA RGACondSig` so that `loOnA`-respecting
witnesses (the RGA convergence/merge engines) transport to `loOnEq`-respecting
ones (the framework's `EqJoinLemma3C`) and back.

## Verdict (all kernel-checked, 0 sorries)

Fact 1 — `rc ≡ Either` — TRUE (`rfl`): both orders' rc-tiebreak arms are
vacuous, and each order collapses to its vis-arm (`loOnEq_reduce`,
`loOnA_reduce`).  The whole bridge question is therefore the per-pair iff
`¬eqCommutesOn e₁ e₂ ↔ (¬commutesOn e₁ e₂ ∨ appliesDependsOn e₂ e₁)` — and
BOTH directions FAIL:

* **`loOnA ⊄ loOnEq`** (fact 3 refuted): `dd₁ = Del [] 5`, `dd₂ = Del [5] 7`.
  `appliesDependsOn dd₂ dd₁` holds — its `∃ s` ranges over arbitrary states,
  and at `{5, 7‹anc 5›}` deleting 5 flips `accurate dd₂` — yet the two deletes
  `≈`-commute at EVERY state (`dd_eqCommutesOn`): both `WfOp` guards are
  identically true and the path-carrying delete is order-insensitive
  (reparent-through-5-then-drop-5 = reparent-to-0 directly).
* **`loOnEq ⊄ loOnA`** (fact 2 refuted): `ji = Ins 42 [] 9` (junk path: claims
  the root as 9's chain), `jd = Del [7,7] 9` (junk path: `[7,7]` demands
  `anc 7 = 7 ∧ anc 7 = 0`, so `accurate jd` is UNSATISFIABLE).  Then
  `commutesOn ji jd` holds vacuously and `¬appliesDependsOn jd ji` (applicable
  is constantly `False`), so `loOnA` has NO `ji → jd` edge; but both ops pass
  their `WfOp` guards at the `qInv` state `{7, 9‹anc 7›}` and the guarded
  folds differ (`11 ↦ anc 7` vs `11 ↦ anc 0`), so `¬eqCommutesOn ji jd` and
  `loOnEq` HAS the edge.

Both respects-transport corollaries fail on 2-event enumerations
(`respects_loOnEq_not_loOnA`, `respects_loOnA_not_loOnEq`), over genuine
`Configuration`s (`pairCfg`) with the needed vis-edge.

## Why, and what would restore the bridge

The two failures are dual quantifier mismatches:
* `appliesDependsOn`'s `∃ s` admits junk states no execution reaches (K-pair);
* `eqCommutesOn`'s guard is `WfOp` (satisfiable where `applicable` is not), so
  never-jointly-`applicable` pairs are `commutesOn`-vacuous yet `doW`-active
  (J-pair).

Both witnesses exploit op/vis combinations a generation-accurate execution
never produces: `jd` is nowhere applicable, and `vis dd₁ dd₂` forces `dd₂`'s
generation state to have node 5 dead, contradicting `accurate dd₂`'s claimed
path `[5]`.  So the bridge is NOT edge-level order equality; it can only hold
CONDITIONED on a generation-discipline oracle tying each event's path accuracy
to its vis-past (GenDisc-style), which is precisely the remaining shape of the
`RGA_Instance` §7 adapter gap.
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs.RGAOrderBridge

open Sal.Emulation
open Sal.ConditionedMRDTs
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.ConditionedConvergence (loOnA appliesDependsOn)
open Sal.ConditionedMRDTs.RGASig (RGACondSig)
open Sal.ConditionedMRDTs (loOnC)
open Sal.ConditionedMRDTs.RGAInstance (RGACondSig' rgaEqEquiv')
open Classical

/-! ## §1  Fact 1: `rc ≡ Either`, and both orders collapse to their vis-arm -/

/-- **`loOnEq` collapses to its vis-arm**: the rc-tiebreak arm needs
`rc = Fst_then_snd`, which `rc ≡ Either` refutes. -/
theorem loOnEq_reduce (vis : Op app_op_t → Op app_op_t → Prop)
    (ev : Set (Op app_op_t)) (e₁ e₂ : Op app_op_t) :
    loOnEq rgaEqEquiv' WfOp vis ev e₁ e₂
      ↔ (vis e₁ e₂ ∧ ¬ eqCommutesOn rgaEqEquiv' WfOp e₁ e₂) := by
  constructor
  · rintro (h | ⟨_, _, hrc, _⟩)
    · exact h
    · exact absurd hrc (by rw [rc_is_Either']; exact fun h => RcRes.noConfusion h)
  · exact Or.inl

/-- **`loOnA` collapses to its vis-arms**: `loOnC`'s rc-arm dies on
`rc ≡ Either`, leaving the `¬commutesOn` vis-arm and the dependency arm. -/
theorem loOnA_reduce (C : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (ev : Set (Op app_op_t)) (e₁ e₂ : Op app_op_t) :
    loOnA RGACondSig C ev e₁ e₂
      ↔ (C.vis e₁ e₂ ∧
          (¬ RGACondSig.commutesOn e₁ e₂ ∨ appliesDependsOn RGACondSig e₂ e₁)) := by
  constructor
  · rintro ((⟨hv, hnc⟩ | ⟨_, _, hrc, _⟩) | ⟨hv, hdep⟩)
    · exact ⟨hv, Or.inl hnc⟩
    · exact absurd hrc (by
        rw [Sal.ConditionedMRDTs.RGASig.rc_is_Either]
        exact fun h => RcRes.noConfusion h)
    · exact ⟨hv, Or.inr hdep⟩
  · rintro ⟨hv, hnc | hdep⟩
    · exact Or.inl (Or.inl ⟨hv, hnc⟩)
    · exact Or.inr ⟨hv, hdep⟩

/-! ## §2  K-witness: fact 3 (`appliesDependsOn ⟹ ¬eqCommutesOn`) is FALSE,
hence `loOnA ⊄ loOnEq` -/

/-- Delete node 5, path `[]` (5 anchored at the root).  `WfOpGen` ✓. -/
def dd₁ : Op app_op_t := (1, 0, .Del [] 5)

/-- Delete node 7, path `[5]` (7 anchored at 5).  `WfOpGen` ✓. -/
def dd₂ : Op app_op_t := (2, 0, .Del [5] 7)

/-- `dd₁`'s `doW` guard is identically true: `resolve s [] = 0 ≠ 5`. -/
theorem wfOp_dd₁ (s : concrete_st) : WfOp dd₁ s := by
  show resolve s [] ≠ 5
  simp

/-- `dd₂`'s `doW` guard is identically true: `resolve s [5] ∈ {5, 0}`, never 7. -/
theorem wfOp_dd₂ (s : concrete_st) : WfOp dd₂ s := by
  show resolve s [5] ≠ 7
  by_cases h : s.domain 5 = true <;> simp [h]

/-- **The two deletes commute observationally at EVERY state** (raw steps):
the path-carrying delete is order-insensitive — reparenting 7's children
through the dying 5 and then dropping 5 equals reparenting directly to 0. -/
theorem dd_raw_comm (s : concrete_st) :
    eq (do_ (do_ s dd₁) dd₂) (do_ (do_ s dd₂) dd₁) := by
  intro k
  constructor
  · -- domains: the two removals commute
    show ((s.domain k && (5 != k)) && (7 != k))
       = ((s.domain k && (7 != k)) && (5 != k))
    cases hd : s.domain k <;> cases h5 : (5 != k) <;> cases h7 : (7 != k) <;>
      simp
  · -- records: pointwise equality of the two reparent pipelines
    intro _
    by_cases h5 : (s.mappings k).2 = 5 <;> by_cases h7 : (s.mappings k).2 = 7 <;>
      by_cases hc : contains s 5 = true <;>
      simp_all [dd₁, dd₂]

/-- One `WfOp`-guarded step with a true guard is the raw step. -/
theorem doW_pos (o : Op app_op_t) (t : concrete_st) (h : WfOp o t) :
    doW RGACondSig' WfOp o t = do_ t o := by
  unfold doW
  rw [if_pos h]
  rfl

/-- **Fact 3's conclusion FAILS on the K-pair**: `dd₁, dd₂` `≈`-commute in the
framework's sense (`eqCommutesOn`) — the guards are identically true and the
raw folds observationally agree at every state, `Inv` unneeded. -/
theorem dd_eqCommutesOn : eqCommutesOn rgaEqEquiv' WfOp dd₁ dd₂ := by
  intro s _hInv
  rw [doW_pos dd₁ s (wfOp_dd₁ s), doW_pos dd₂ _ (wfOp_dd₂ _),
      doW_pos dd₂ s (wfOp_dd₂ s), doW_pos dd₁ _ (wfOp_dd₁ _)]
  exact dd_raw_comm s

/-- The K-dependency state: node 5 at the root, node 7 anchored at 5. -/
def sK : concrete_st := upd (upd init_st 5 (20, 0)) 7 (21, 5)

/-- **Fact 3's premise HOLDS on the K-pair**: `dd₂`'s applicability flips when
`dd₁` deletes node 5 — `accurate dd₂` (path `[5]`) is true at `sK` but false
after `dd₁` (5 dead, 7 rehomed to 0).  The `∃ s` needs no reachability. -/
theorem dd_appliesDependsOn : appliesDependsOn RGACondSig dd₂ dd₁ := by
  refine ⟨sK, fun h => ?_⟩
  have hP : RGACondSig.applicable dd₂ sK := by
    refine ⟨Or.inr ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · show contains sK 7 = true
      decide
    · show anc sK 7 = 5
      decide
    · show contains sK 5 = true
      decide
    · show anc sK 5 = 0
      decide
    · show True
      trivial
  have hQ : RGACondSig.applicable dd₂ (RGACondSig.update sK dd₁) := cast h hP
  rcases hQ.1 with ⟨h70, _⟩ | ⟨_, h7anc, _⟩
  · exact absurd h70 (by decide)
  · exact absurd h7anc (by decide)

/-! ## §3  J-witness: fact 2 (`commutesOn ⟹ eqCommutesOn`) is FALSE, hence
`loOnEq ⊄ loOnA` -/

/-- Insert 42 as node 11 anchored at 9, claiming path `[]` for 9 (junk path:
9's genuine chain in the J-state is `[7]`).  `WfOpGen` ✓ (`11 ≠ 0`). -/
def ji : Op app_op_t := (11, 0, .Ins 42 [] 9)

/-- Delete node 9 claiming path `[7,7]` — structurally junk: `IsAncPath`
demands `anc s 7 = 7 ∧ anc s 7 = 0`, so `accurate jd` is UNSATISFIABLE.
`WfOpGen` ✓ (`9 ∉ [7,7]`, `9 ≠ 0`). -/
def jd : Op app_op_t := (13, 0, .Del [7, 7] 9)

/-- `jd` is applicable NOWHERE: its path is structurally inconsistent. -/
theorem jd_never_applicable (s : concrete_st) :
    ¬ RGACondSig.applicable jd s := by
  rintro ⟨(⟨h90, -⟩ | ⟨-, -, -, h77, -, h70⟩), -⟩
  · exact absurd h90 (by decide)
  · exact absurd (h77.symm.trans h70) (by decide)

/-- **Fact 2's premise HOLDS on the J-pair**: `commutesOn ji jd` — vacuously,
`jd` being never applicable empties the conditioned quantifier. -/
theorem j_commutesOn : RGACondSig.commutesOn ji jd :=
  fun s _ _ hjd => absurd hjd (jd_never_applicable s)

/-- `ji` never flips `jd`'s applicability — both sides are `False`, so the
semantic dependency `appliesDependsOn jd ji` FAILS. -/
theorem j_not_appliesDependsOn : ¬ appliesDependsOn RGACondSig jd ji := by
  rintro ⟨s, hne⟩
  exact hne (propext (iff_of_false (jd_never_applicable s)
    (jd_never_applicable _)))

/-- The J-state: node 7 at the root, node 9 anchored at 7. -/
def sJ : concrete_st := upd (upd init_st 7 (20, 0)) 9 (21, 7)

/-- `sJ` satisfies the hosting invariant `qInv = wf ∧ root-free ∧ id_mono`. -/
theorem sJ_qInv : RGACondSig'.Inv sJ := by
  refine ⟨?_, by decide, ?_⟩
  · intro t ht
    have h : t = 7 ∨ t = 9 := by simpa [sJ] using ht
    rcases h with rfl | rfl
    · left; decide
    · right; decide
  · intro t ht
    have h : t = 7 ∨ t = 9 := by simpa [sJ] using ht
    rcases h with rfl | rfl
    · left; decide
    · right; decide

/-- **Fact 2's conclusion FAILS on the J-pair**: at the `qInv` state `sJ` both
`WfOp` guards pass and the guarded folds differ observationally.  `ji` first:
11 anchors at the live 9, and `jd`'s delete rehomes it to 9's path-resolved
parent 7.  `jd` first: 9 dies, and `ji`'s junk path `[]` resolves 11's anchor
to the root — `sel 11 = (42, 7)` vs `(42, 0)`. -/
theorem j_not_eqCommutesOn : ¬ eqCommutesOn rgaEqEquiv' WfOp ji jd := by
  intro h
  have hj := h sJ sJ_qInv
  have g1 : WfOp ji sJ := ⟨by decide, by decide⟩
  have g2 : WfOp jd (do_ sJ ji) := by
    show resolve (do_ sJ ji) [7, 7] ≠ 9
    decide
  have g3 : WfOp jd sJ := by
    show resolve sJ [7, 7] ≠ 9
    decide
  have g4 : WfOp ji (do_ sJ jd) := ⟨by decide, by decide⟩
  rw [doW_pos ji sJ g1, doW_pos jd _ g2, doW_pos jd sJ g3, doW_pos ji _ g4] at hj
  have h11 := (hj 11).2 (by decide)
  exact absurd h11 (by decide)

/-! ## §4  Edge- and `respects`-level separations over genuine configurations -/

private theorem optSome_inv {α : Type} {x y : α} {r : Replica}
    (h : (if r = 0 then some x else none) = some y) : x = y := by
  by_cases hr : r = 0
  · rw [if_pos hr] at h
    exact Option.some.inj h
  · rw [if_neg hr] at h
    exact absurd h (by simp)

/-- The 2-event set `{o₁, o₂}`. -/
def pairEv (o₁ o₂ : Op app_op_t) : Set (Op app_op_t) := {o₁, o₂}

/-- The 2-event, single-replica configuration with the single vis-edge
`o₁ → o₂` — the shape `createReplica 0; apply o₁; apply o₂` produces. -/
noncomputable def pairCfg (o₁ o₂ : Op app_op_t) (hne : o₁ ≠ o₂)
    (hts : o₁.1 ≠ o₂.1) :
    Sal.Emulation.Configuration RGACondSig.toCRDTSig where
  N := fun r => if r = 0 then some (do_ (do_ init_st o₁) o₂) else none
  L := fun r => if r = 0 then some (pairEv o₁ o₂) else none
  vis := fun a b => a = o₁ ∧ b = o₂
  dom_eq := by
    intro r
    by_cases h : r = 0 <;> simp [h]
  vis_src := by
    intro a b hv
    refine ⟨0, pairEv o₁ o₂, rfl, ?_⟩
    rw [hv.1]
    exact Set.mem_insert _ _
  vis_tgt := by
    intro a b hv
    refine ⟨0, pairEv o₁ o₂, rfl, ?_⟩
    rw [hv.2]
    exact Set.mem_insert_of_mem _ rfl
  vis_causal := by
    intro a b r s hv hL _hb
    obtain rfl := optSome_inv hL
    rw [hv.1]
    exact Set.mem_insert _ _
  timestamps_distinct := by
    intro a b r s r' s' hL ha hL' hb hab
    obtain rfl := optSome_inv hL
    obtain rfl := optSome_inv hL'
    have ha' : a = o₁ ∨ a = o₂ := ha
    have hb' : b = o₁ ∨ b = o₂ := hb
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact absurd rfl hab
    · exact hts
    · exact hts.symm
    · exact absurd rfl hab
  vis_total_same_replica := by
    intro a b r s r' s' hL ha hL' hb hab _hrep
    obtain rfl := optSome_inv hL
    obtain rfl := optSome_inv hL'
    have ha' : a = o₁ ∨ a = o₂ := ha
    have hb' : b = o₁ ∨ b = o₂ := hb
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact absurd rfl hab
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact absurd rfl hab

/-! ### The K-instance: `loOnA ⊄ loOnEq` -/

def evK : Set (Op app_op_t) := {dd₁, dd₂}

/-- The K-configuration: single replica, `vis dd₁ dd₂`. -/
noncomputable def CfgK : Sal.Emulation.Configuration RGACondSig.toCRDTSig :=
  pairCfg dd₁ dd₂ (by decide) (by decide)

/-- **`loOnA ⊄ loOnEq`**: the vis-edge `dd₁ → dd₂` is a `loOnA`-edge (via the
dependency arm) but NOT a `loOnEq`-edge (the pair `≈`-commutes everywhere). -/
theorem loOnA_edge_not_loOnEq :
    loOnA RGACondSig CfgK evK dd₁ dd₂
    ∧ ¬ loOnEq rgaEqEquiv' WfOp CfgK.vis evK dd₁ dd₂ := by
  constructor
  · exact Or.inr ⟨⟨rfl, rfl⟩, dd_appliesDependsOn⟩
  · intro h
    exact ((loOnEq_reduce CfgK.vis evK dd₁ dd₂).mp h).2 dd_eqCommutesOn

/-- **The transport `respects loOnEq → respects loOnA` FAILS**: `[dd₂, dd₁]`
is a genuine enumeration of `{dd₁, dd₂}` that respects `loOnEq` but not
`loOnA`.  A framework-side (`loOnEq`) witness is NOT an RGA-side (`loOnA`)
witness. -/
theorem respects_loOnEq_not_loOnA :
    listPermOf [dd₂, dd₁] evK
    ∧ respects [dd₂, dd₁] (loOnEq rgaEqEquiv' WfOp CfgK.vis evK)
    ∧ ¬ respects [dd₂, dd₁] (loOnA RGACondSig CfgK evK) := by
  refine ⟨⟨by decide, ?_⟩, ?_, ?_⟩
  · intro a
    constructor
    · intro h
      rcases List.mem_cons.mp h with rfl | h
      · exact Set.mem_insert_of_mem _ rfl
      · rw [List.mem_singleton] at h
        subst h
        exact Set.mem_insert _ _
    · intro h
      have h' : a = dd₁ ∨ a = dd₂ := h
      rcases h' with rfl | rfl
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact List.mem_cons_self
  · refine List.pairwise_cons.mpr ⟨?_, List.pairwise_singleton _ _⟩
    intro b hb
    rw [List.mem_singleton] at hb
    subst hb
    exact loOnA_edge_not_loOnEq.2
  · intro h
    exact (List.pairwise_cons.mp h).1 dd₁ List.mem_cons_self
      loOnA_edge_not_loOnEq.1

/-! ### The J-instance: `loOnEq ⊄ loOnA` -/

def evJ : Set (Op app_op_t) := {ji, jd}

/-- The J-configuration: single replica, `vis ji jd`. -/
noncomputable def CfgJ : Sal.Emulation.Configuration RGACondSig.toCRDTSig :=
  pairCfg ji jd (by decide) (by decide)

/-- **`loOnEq ⊄ loOnA`**: the vis-edge `ji → jd` is a `loOnEq`-edge (the
guarded folds do not `≈`-commute) but NOT a `loOnA`-edge (`commutesOn` holds
vacuously and there is no semantic generation dependency). -/
theorem loOnEq_edge_not_loOnA :
    loOnEq rgaEqEquiv' WfOp CfgJ.vis evJ ji jd
    ∧ ¬ loOnA RGACondSig CfgJ evJ ji jd := by
  constructor
  · exact Or.inl ⟨⟨rfl, rfl⟩, j_not_eqCommutesOn⟩
  · intro h
    rcases ((loOnA_reduce CfgJ evJ ji jd).mp h).2 with hnc | hdep
    · exact hnc j_commutesOn
    · exact j_not_appliesDependsOn hdep

/-- **The transport `respects loOnA → respects loOnEq` FAILS**: `[jd, ji]` is
a genuine enumeration of `{ji, jd}` that respects `loOnA` but not `loOnEq`.
An RGA-side (`loOnA`) witness is NOT a framework-side (`loOnEq`) witness. -/
theorem respects_loOnA_not_loOnEq :
    listPermOf [jd, ji] evJ
    ∧ respects [jd, ji] (loOnA RGACondSig CfgJ evJ)
    ∧ ¬ respects [jd, ji] (loOnEq rgaEqEquiv' WfOp CfgJ.vis evJ) := by
  refine ⟨⟨by decide, ?_⟩, ?_, ?_⟩
  · intro a
    constructor
    · intro h
      rcases List.mem_cons.mp h with rfl | h
      · exact Set.mem_insert_of_mem _ rfl
      · rw [List.mem_singleton] at h
        subst h
        exact Set.mem_insert _ _
    · intro h
      have h' : a = ji ∨ a = jd := h
      rcases h' with rfl | rfl
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact List.mem_cons_self
  · refine List.pairwise_cons.mpr ⟨?_, List.pairwise_singleton _ _⟩
    intro b hb
    rw [List.mem_singleton] at hb
    subst hb
    exact loOnEq_edge_not_loOnA.2
  · intro h
    exact (List.pairwise_cons.mp h).1 ji List.mem_cons_self
      loOnEq_edge_not_loOnA.1

/-! ## §5  Headline and axiom audit -/

/-- **HEADLINE — the RGA order bridge FAILS in both directions.**  The
framework's `≈`-conditioned order `loOnEq rgaEqEquiv' WfOp` and the RGA's
applicability-aware order `loOnA RGACondSig` are INCOMPARABLE: each has an
edge (over a genuine 2-event configuration, on `WfOpGen`, distinct-timestamp
events) that the other lacks.  Consequently neither `respects`-transport
holds unconditionally, and the `RGA_Instance` §7 adapter cannot be a pure
order-inclusion: it must be conditioned on generation discipline. -/
theorem loOnEq_loOnA_incomparable :
    (loOnA RGACondSig CfgK evK dd₁ dd₂
      ∧ ¬ loOnEq rgaEqEquiv' WfOp CfgK.vis evK dd₁ dd₂)
    ∧ (loOnEq rgaEqEquiv' WfOp CfgJ.vis evJ ji jd
      ∧ ¬ loOnA RGACondSig CfgJ evJ ji jd) :=
  ⟨loOnA_edge_not_loOnEq, loOnEq_edge_not_loOnA⟩

/-- All four witness events are generation-wellformed (`WfOpGen`) — the
counterexamples survive the `Nodup`/distinct-ts/`WfOpGen` discipline that the
capstone's reachable configurations supply. -/
theorem witnesses_WfOpGen :
    WfOpGen dd₁ ∧ WfOpGen dd₂ ∧ WfOpGen ji ∧ WfOpGen jd := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_,
    ⟨by decide, by decide⟩⟩
  show (11 : ℕ) ≠ 0
  decide

#print axioms loOnEq_reduce
#print axioms loOnA_reduce
#print axioms dd_eqCommutesOn
#print axioms dd_appliesDependsOn
#print axioms j_commutesOn
#print axioms j_not_appliesDependsOn
#print axioms j_not_eqCommutesOn
#print axioms loOnA_edge_not_loOnEq
#print axioms loOnEq_edge_not_loOnA
#print axioms respects_loOnEq_not_loOnA
#print axioms respects_loOnA_not_loOnEq
#print axioms loOnEq_loOnA_incomparable

end Sal.ConditionedMRDTs.RGAOrderBridge
