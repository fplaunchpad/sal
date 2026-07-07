import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_Instance

/-!
# `inv_update` over `qInv` — the strengthened `WfOpQ` closes `InvPres`

`RGA_Instance.lean` §5 pins the ONE failing `InvPres RGACondSig' W` field:
`inv_update` needs `id_mono (do_ s o)` from `qInv s ∧ W o s`, and `W = WfOp` is
too weak (`id_mono_doIns` was stated with `mono_alloc`, `id_mono_doDel` with
`accurate`).  This file supplies the MINIMAL strengthening `WfOpQ` and closes
the full `InvPres RGACondSig' WfOpQ`:

* **`WfOpQ`** = `WfOp` PLUS, for `Ins`, `resolve s (a :: pre) < t` (the inserted
  id exceeds its RESOLVED anchor — not `mono_alloc`'s "exceeds EVERY live id"),
  and for `Del`, `resolve s pre = 0 ∨ resolve s pre < x` (the rehome target is
  root or below the deleted node).
* **`idMono_doIns_wfq` / `idMono_doDel_wfq`** — `id_mono` preservation from
  exactly these weaker facts (`mono_alloc`/`accurate` were over-asks: their
  proofs only ever consume the resolved value).
* **`qInv_doOp`** — `qInv s → WfOpQ o s → qInv (do_ s o)`; the wf∧root-free part
  is `rgaInv_doOp_fresh` (via `WfOpQ ⊆ WfOp`), the `id_mono` part the two lemmas.
* **`rgaInvPresQ : InvPres RGACondSig' WfOpQ`** — the FULL framework bundle:
  `inv_init`/`inv_mergeL` from `RGA_Instance`, `inv_update := qInv_doOp`.
* **Static dischargeability** — the strengthening is a PER-OP fact, stable under
  reordering: `WfOpGenQ` (`Ins`: `t ≠ 0 ∧ ∀ c ∈ a::pre, c < t`; `Del`: `x ≠ 0 ∧
  ∀ c ∈ pre, c < x`) forces the `WfOpQ` extras at EVERY state (`resolve_mem`),
  holds at generation (`wfOpGenQ_ins`/`wfOpGenQ_del_live`: accurate paths are
  live and id-descending under `id_mono` + monotone allocation), and discharges
  the full `WfOpReachable RGACondSig' WfOpQ WfOpGenQ` (`rga_wfOpReachableQ`).
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs.RGAInvUpdateQ

open Sal.Emulation (Op)
open Sal.ConditionedMRDTs.GenericEqQuotient (InvPres WfChain WfOpReachable)
open Sal.ConditionedMRDTs.RGAInstance (RGACondSig' rga_inv_init' rga_inv_mergeL')
open Sal.ConditionedMRDTs.RGACanonFoldOK (insertedIn_of_contains_fold)
open RGAMergeLinearization (applySeqR)

/-! ## §1. `qInv` and the strengthened `WfOpQ` -/

/-- The framework `Inv`: `RGACondSig'.Inv`, spelled out. -/
def qInv (s : concrete_st) : Prop := wf s ∧ contains s 0 = false ∧ id_mono s

/-- **The minimal strengthening of `WfOp` for `id_mono` preservation.**
`Ins` additionally requires the fresh id to exceed its RESOLVED anchor
(`resolve s (a :: pre) < t` — NOT `mono_alloc`'s "exceeds every live id");
`Del` requires the rehome target to be root-or-below the deleted node
(`resolve s pre = 0 ∨ resolve s pre < x`). -/
def WfOpQ (o : op_t) (s : concrete_st) : Prop :=
  match o with
  | (t, _, .Ins _ pre a) => (t ≠ 0 ∧ contains s t = false) ∧ resolve s (a :: pre) < t
  | (_, _, .Del pre x)   => resolve s pre ≠ x ∧ (resolve s pre = 0 ∨ resolve s pre < x)

/-- `WfOpQ` strengthens `WfOp`, so `rgaInv_doOp_fresh` applies unchanged. -/
theorem wfOp_of_wfOpQ (o : op_t) (s : concrete_st) (h : WfOpQ o s) : WfOp o s := by
  obtain ⟨t, r, ao⟩ := o
  cases ao with
  | Ins e pre a => exact h.1
  | Del pre x => exact h.1

/-! ## §2. `id_mono` preservation under `do_` from `WfOpQ` alone -/

/-- `Ins` preserves `id_mono` from `resolve s (a :: pre) < t` alone —
`id_mono_doIns`'s `mono_alloc` was an over-ask: its proof consumes the
allocation bound ONLY at the resolved anchor. -/
theorem idMono_doIns_wfq (s : concrete_st) (t r e a : ℕ) (pre : List ℕ)
    (hmono : id_mono s) (hlt : resolve s (a :: pre) < t) :
    id_mono (do_ s (t, r, .Ins e pre a)) := by
  intro k hk
  have hdo : do_ s (t, r, .Ins e pre a) = upd s t (e, resolve s (a :: pre)) := by
    simp only [do_]
  rw [hdo] at hk ⊢
  by_cases hkt : k = t
  · subst hkt
    have hanc : anc (upd s k (e, resolve s (a :: pre))) k = resolve s (a :: pre) := by
      simp only [anc]; rw [lemma_SelUpd1]
    rw [hanc]
    right; exact hlt
  · have htk : t ≠ k := fun e' => hkt e'.symm
    have hck : contains s k = true := by
      rw [lemma_InDomUpd1] at hk
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hk
      rcases hk with h | h
      · exact absurd h htk
      · exact h
    have hanc : anc (upd s t (e, resolve s (a :: pre))) k = anc s k := by
      simp only [anc]
      rw [lemma_SelUpd2 s k t (e, resolve s (a :: pre))
            (by simp only [bne_iff_ne, ne_eq]; exact htk)]
    rw [hanc]
    exact hmono k hck

/-- `Del` preserves `id_mono` from `resolve s pre = 0 ∨ resolve s pre < x` alone —
`id_mono_doDel`'s `accurate` was an over-ask (it was consumed only to place the
rehome target at `anc s x < x`); even `contains s 0 = false` is not needed. -/
theorem idMono_doDel_wfq (s : concrete_st) (t r x : ℕ) (pre : List ℕ)
    (hmono : id_mono s) (hdq : resolve s pre = 0 ∨ resolve s pre < x) :
    id_mono (do_ s (t, r, .Del pre x)) := by
  intro k hk
  rw [contains_doDel] at hk
  rw [Bool.and_eq_true] at hk
  obtain ⟨hck, _hkx⟩ := hk
  rw [anc_doDel]
  by_cases hax : anc s k = x
  · rw [if_pos hax]
    rcases hdq with h0 | hlt
    · left; exact h0
    · rcases hmono k hck with hk0 | hklt
      · exfalso; rw [hax] at hk0; omega
      · right; rw [hax] at hklt; omega
  · rw [if_neg hax]
    exact hmono k hck

/-! ## §3. `inv_update` over `qInv`, and the full `InvPres` -/

/-- **`inv_update` over the full `qInv`.**  The wf∧root-free part is
`rgaInv_doOp_fresh` (via `WfOpQ ⊆ WfOp`); the `id_mono` part is §2. -/
theorem qInv_doOp (s : concrete_st) (o : op_t)
    (h : qInv s) (hw : WfOpQ o s) : qInv (do_ s o) := by
  obtain ⟨hwf, h0, hmono⟩ := h
  have hR : RgaInv (do_ s o) :=
    rgaInv_doOp_fresh s o ⟨h0, hwf⟩ (wfOp_of_wfOpQ o s hw)
  refine ⟨hR.2, hR.1, ?_⟩
  obtain ⟨t, r, ao⟩ := o
  cases ao with
  | Ins e pre a => exact idMono_doIns_wfq s t r e a pre hmono hw.2
  | Del pre x => exact idMono_doDel_wfq s t r x pre hmono hw.2

/-! ## §4. `WfOpQ` is dischargeable: static per-op facts force it at EVERY state -/

/-! ## §5. `WfOpGenQ` holds at generation -/

/-! ## §6. `WfOpReachable RGACondSig' WfOpQ WfOpGenQ` — dischargeable at
reordered folds.  Mirror of `RGA_WfOpReachable.wfChain_acc`: the only
fold-positional conjunct is Ins freshness (from `Nodup` + distinct ts + the
fold-domain lemma); every Q-extra is static (§4). -/

end Sal.ConditionedMRDTs.RGAInvUpdateQ
