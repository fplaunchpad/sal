import Sal.MRDTs.Metatheory.Development.RGA_OrderBridge
import Sal.MRDTs.Metatheory.Sigma_LoOn3

/-!
# Gate experiment: forcing `rc(insert-after-x, delete-x) = Fst_then_snd` breaks the
`rc-non-comm` VC

**Question.** Does adding the insert-before-delete edge `rc insX delX = Fst_then_snd`
break an update-layer VC?

**Answer (proved here, 0 sorries).** YES.  A *genuine* `insert-after-node-7`
(`insX`) and `delete-node-7` (`delX`) that SHARE node 7's ancestor path `[5]`
observationally **commute at every state** (`insDelX_raw_comm`), hence `≈`-commute
on the framework's `Inv`-conditioned quotient (`insDelX_eqCommutesOn`).  The
`rc-non-comm` VC (`Sigma_LoOn3.UpdateVCs.rc_non_comm_directional`) is the IFF
`¬ commutes o₁ o₂ ↔ (rc o₁ o₂ = Fst ∨ rc o₂ o₁ = Fst)`.  Its contrapositive
(`commutes_forces_rc_not_Fst`) says a *commuting* pair is FORCED to
`rc … ≠ Fst_then_snd` — i.e. `Either`.  Therefore any hosting signature that keeps
the RGA's `update` (so `insX`/`delX` still commute) but sets
`rc insX delX = Fst_then_snd` cannot satisfy `UpdateVCs`
(`insDelX_rc_forced_not_Fst`): the proposed insert-before-delete edge is
inconsistent with the VC.

**Why they commute.** Both ops resolve node 7 through the SAME carried path `[5]`.
Order `ins;del`: 42 lands under `resolve s [7,5]` (= 7 while 7 is live), then
`Del 7` rehomes 42 (now 7's child) to `resolve s [5]`.  Order `del;ins`: `Del 7`
rehomes 7's children to `resolve s [5]`, then `Ins`'s anchor `resolve s [7,5]`
climbs past the dead 7 to `resolve s [5]`.  Both give 42 under `resolve s [5]`;
node 7 removed both ways; 7's other children rehomed to `resolve s [5]` both ways;
the fresh id 10 (≠ 7) never collides.  Holds unconditionally — no `accurate`,
`fresh`, or `Inv` needed for the raw step.
-/

set_option maxHeartbeats 1000000

namespace Sal.Metatheory.RGAInsDelOrderGate

open Sal.Emulation
open Sal.Metatheory
open Sal.Metatheory.GenericEqQuotient
open Sal.Metatheory.RGAInstance (RGACondSig' rgaEqEquiv' rgaCongVC' rgaInvInvVC')
open Sal.Metatheory.RGAOrderBridge (doW_pos rc_is_Either')
open Classical

/-! ## §1  Witness ops (genuine, sharing node 7's path `[5]`) -/

/-- Insert 42 as node 10, anchored at 7, carrying 7's chain `[5]`. -/
def insX : Op app_op_t := (10, 1, .Ins 42 [5] 7)

/-- Delete node 7, path `[5]` (7 anchored at 5). -/
def delX : Op app_op_t := (11, 2, .Del [5] 7)

/-- `delX`'s `doW` guard `resolve s [5] ≠ 7` is identically true
(`resolve s [5] ∈ {5, 0}`, never 7).  Mirrors `wfOp_dd₂`. -/
theorem wfOp_delX (s : concrete_st) : WfOp delX s := by
  show resolve s [5] ≠ 7
  by_cases h : s.domain 5 = true <;> simp [h]

/-! ## §2  The raw step commutes at EVERY state -/

/-- **Deliverable 1.**  `insX` and `delX` observationally commute at every state.
The shared path `[5]` makes both orders land node 42 under `resolve s [5]` and
rehome 7's children there. -/
theorem insDelX_raw_comm (s : concrete_st) :
    eq (do_ (do_ s insX) delX) (do_ (do_ s delX) insX) := by
  simp only [insX, delX]
  -- reparent target on the ins side is state-stable across the fresh upd
  have hResIns : resolve (upd s 10 (42, resolve s [7, 5])) [5] = resolve s [5] :=
    resolve_upd_notMem s 10 (42, resolve s [7, 5]) [5] (by decide)
  -- the del-first side climbs the dead 7 to `resolve s [5]`
  have hResDel : resolve (do_ s (11, 2, .Del [5] 7)) [7, 5] = resolve s [5] := by
    have hfil : ([7, 5].filter (fun c => c != 7)) = [5] := by decide
    rw [resolve_doDel, hfil]
  -- inner Ins as an upd (definitional)
  have hIns : do_ s (10, 1, .Ins 42 [5] 7) = upd s 10 (42, resolve s [7, 5]) := rfl
  -- del-first side as an upd, with anchor rewritten to `resolve s [5]`
  have hDel : do_ (do_ s (11, 2, .Del [5] 7)) (10, 1, .Ins 42 [5] 7)
      = upd (do_ s (11, 2, .Del [5] 7)) 10 (42, resolve s [5]) := by
    show upd (do_ s (11, 2, .Del [5] 7)) 10
          (42, resolve (do_ s (11, 2, .Del [5] 7)) [7, 5]) = _
    rw [hResDel]
  rw [hIns, hDel]
  intro k
  refine ⟨?_, ?_⟩
  · -- containment
    rw [contains_doDel, lemma_InDomUpd1, lemma_InDomUpd1, contains_doDel]
    by_cases hk10 : k = 10
    · subst hk10; simp
    · have h10 : ¬ (10 = k) := fun e => hk10 e.symm
      simp [h10]
  · -- value
    intro _hcont
    by_cases hk10 : k = 10
    · subst hk10
      rw [sel_doDel]
      have ha : anc (upd s 10 (42, resolve s [7, 5])) 10 = resolve s [7, 5] := rfl
      have he : el (upd s 10 (42, resolve s [7, 5])) 10 = 42 := rfl
      have hs : sel (upd s 10 (42, resolve s [7, 5])) 10 = (42, resolve s [7, 5]) := rfl
      have hR : sel (upd (do_ s (11, 2, .Del [5] 7)) 10 (42, resolve s [5])) 10
          = (42, resolve s [5]) := rfl
      rw [ha, he, hs, hResIns, hR]
      cases h7 : contains s 7 with
      | true => rw [resolve_live_head s 7 [5] h7]; simp
      | false => rw [resolve_dead_head s 7 [5] h7]; simp
    · have hbne : (10 != k) = true := by
        simp only [bne_iff_ne, ne_eq]; exact fun e => hk10 e.symm
      have hsel_ne : sel (upd s 10 (42, resolve s [7, 5])) k = sel s k :=
        lemma_SelUpd2 s k 10 (42, resolve s [7, 5]) hbne
      rw [sel_doDel,
          lemma_SelUpd2 (do_ s (11, 2, .Del [5] 7)) k 10 (42, resolve s [5]) hbne,
          sel_doDel]
      simp only [anc, el, hsel_ne, hResIns]

/-! ## §3  The `≈`-conditioned commutation -/

/-- **Deliverable 2.**  `insX` and `delX` `≈`-commute on the framework's
`Inv`-conditioned quotient (`eqCommutesOn`).  `delX`'s guard is identically true;
`insX`'s freshness guard `contains s 10 = false` is NOT, so we case-split on it:
when 10 is fresh both `doW insX` are raw steps and we invoke `insDelX_raw_comm`;
when 10 is present `doW insX` is a no-op at `s` and at `doW delX s` (deleting 7
leaves `contains · 10` unchanged since 10 ≠ 7), so both sides reduce to
`do_ s delX`.  `Inv` unused. -/
theorem insDelX_eqCommutesOn : eqCommutesOn rgaEqEquiv' WfOp insX delX := by
  intro s _hInv
  by_cases hc : contains s 10 = true
  · -- node 10 already present: `insX` is a no-op both times
    have hnwf : ¬ WfOp insX s := fun hw => absurd hw.2 (by rw [hc]; decide)
    have hc' : contains (do_ s delX) 10 = true := by
      show contains (do_ s (11, 2, .Del [5] 7)) 10 = true
      rw [contains_doDel, hc]; decide
    have hnwf' : ¬ WfOp insX (do_ s delX) := fun hw => absurd hw.2 (by rw [hc']; decide)
    have hi_noop : doW RGACondSig' WfOp insX s = s := by unfold doW; rw [if_neg hnwf]
    have hi_noop' : doW RGACondSig' WfOp insX (do_ s delX) = do_ s delX := by
      unfold doW; rw [if_neg hnwf']
    rw [hi_noop, doW_pos delX s (wfOp_delX s), hi_noop']
    exact fun k => ⟨rfl, fun _ => rfl⟩
  · -- node 10 fresh: both `doW insX` are the raw step
    have hc0 : contains s 10 = false := by simpa using hc
    have gi : WfOp insX s := ⟨by decide, hc0⟩
    have gi2 : WfOp insX (do_ s delX) := by
      refine ⟨by decide, ?_⟩
      show contains (do_ s (11, 2, .Del [5] 7)) 10 = false
      rw [contains_doDel, hc0]; decide
    rw [doW_pos insX s gi, doW_pos delX _ (wfOp_delX _),
        doW_pos delX s (wfOp_delX s), doW_pos insX _ gi2]
    exact insDelX_raw_comm s

/-! ## §4  Consequence: forcing `rc insX delX = Fst_then_snd` violates the VC -/

/-- Current fact: `rc insX delX = Either` (the RGA's `rc` is `Either` everywhere). -/
theorem insDelX_rc_is_Either : RGACondSig'.rc insX delX = RcRes.Either :=
  rc_is_Either' insX delX

/-- **The rc-non-comm VC forces a commuting pair to `≠ Fst_then_snd`.**  Generic
contrapositive of `UpdateVCs.rc_non_comm_directional`: if `o₁, o₂` commute in `D`
then `rc` may not order them `Fst_then_snd`. -/
theorem commutes_forces_rc_not_Fst {D : CRDTSig} (hU : UpdateVCs D)
    (o₁ o₂ : Op D.AppOp) (hd : distinctOps o₁ o₂) (hr : differentReplicas o₁ o₂)
    (hcomm : D.commutes o₁ o₂) :
    D.rc o₁ o₂ ≠ RcRes.Fst_then_snd :=
  fun hFst => (hU.rc_non_comm_directional o₁ o₂ hd hr).mpr (Or.inl hFst) hcomm

/-- **Deliverable 3 (Lean fact).**  On the RGA quotient — for ANY `InvPres`
residual `hP` and any signature satisfying `UpdateVCs` — `rc insX delX` is FORCED
to `≠ Fst_then_snd`.  Because `commutes` is defined purely from `update` (which is
unchanged), any variant that keeps the RGA's `update` but sets
`rc insX delX = Fst_then_snd` still has `commutes insX delX` (via `qcommutes_iff`
+ `insDelX_eqCommutesOn`) and hence CANNOT satisfy `UpdateVCs`.  So the proposed
insert-before-delete edge breaks the `rc-non-comm` VC. -/
theorem insDelX_rc_forced_not_Fst
    (hP : InvPres RGACondSig' WfOp)
    (hU : UpdateVCs (QSig rgaEqEquiv' WfOp hP rgaCongVC' rgaInvInvVC').toCRDTSig) :
    (QSig rgaEqEquiv' WfOp hP rgaCongVC' rgaInvInvVC').toCRDTSig.rc insX delX
      ≠ RcRes.Fst_then_snd := by
  have hcomm := (qcommutes_iff rgaEqEquiv' WfOp hP rgaCongVC' rgaInvInvVC' insX delX).mpr
    insDelX_eqCommutesOn
  refine commutes_forces_rc_not_Fst hU insX delX ?_ ?_ hcomm
  · show insX.time ≠ delX.time; decide
  · show insX.rep ≠ delX.rep; decide

#print axioms insDelX_raw_comm
#print axioms insDelX_eqCommutesOn
#print axioms insDelX_rc_forced_not_Fst

end Sal.Metatheory.RGAInsDelOrderGate
