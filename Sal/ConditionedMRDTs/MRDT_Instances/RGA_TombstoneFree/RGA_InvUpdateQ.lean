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
open Sal.ConditionedMRDTs.RGASig (resolve_mem isAncPath_not_mem)
open Sal.ConditionedMRDTs.RGAInstance (RGACondSig' rga_inv_init' rga_inv_mergeL')
open Sal.ConditionedMRDTs.RGACanonFoldOK (insertedIn_of_contains_fold)
open RGAMergeLinearization (applySeqR)

/-! ## §1. `qInv` and the strengthened `WfOpQ` -/

/-- The framework `Inv`: `RGACondSig'.Inv`, spelled out. -/
def qInv (s : concrete_st) : Prop := wf s ∧ contains s 0 = false ∧ id_mono s

theorem qInv_iff_Inv (s : concrete_st) : qInv s ↔ RGACondSig'.Inv s := Iff.rfl

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

/-- **The FULL `InvPres RGACondSig' WfOpQ`** — the bundle `RGA_Instance` §5 could
not assemble with `W = WfOp`: `inv_init`/`inv_mergeL` are `RGA_Instance`'s,
`inv_update` is `qInv_doOp`. -/
theorem rgaInvPresQ : InvPres RGACondSig' WfOpQ :=
  ⟨rga_inv_init', fun s o hI hw => qInv_doOp s o hI hw, rga_inv_mergeL'⟩

#print axioms qInv_doOp
#print axioms rgaInvPresQ

/-! ## §4. `WfOpQ` is dischargeable: static per-op facts force it at EVERY state -/

/-- **Per-op genuineness, Q-strengthened** — a property of the op ALONE (stable
under any reordering): the recorded path (and anchor/leaf) ids sit strictly
below the op's own id.  `Ins`: `t ≠ 0 ∧ ∀ c ∈ a :: pre, c < t`; `Del`:
`x ≠ 0 ∧ ∀ c ∈ pre, c < x` (`x ∉ pre` is then free: `c < x` forbids `c = x`). -/
def WfOpGenQ : op_t → Prop
  | (t, _, .Ins _ pre a) => t ≠ 0 ∧ ∀ c ∈ a :: pre, c < t
  | (_, _, .Del pre x)   => x ≠ 0 ∧ ∀ c ∈ pre, c < x

theorem wfOpQ_ins_of_genQ (s : concrete_st) (t r e a : ℕ) (pre : List ℕ)
    (hg : WfOpGenQ (t, r, .Ins e pre a)) (hfr : contains s t = false) :
    WfOpQ (t, r, .Ins e pre a) s := by
  obtain ⟨ht0, hlt⟩ := hg
  refine ⟨⟨ht0, hfr⟩, ?_⟩
  rcases resolve_mem s (a :: pre) with h0 | hmem
  · rw [h0]; exact Nat.pos_of_ne_zero ht0
  · exact hlt _ hmem

/-- The `Del` `WfOpQ` holds at EVERY state — unconditionally from the static
fact: `resolve` lands in `{0} ∪ pre`, i.e. `0` (`≠ x` as `x ≠ 0`) or `< x`. -/
theorem wfOpQ_del_of_genQ (s : concrete_st) (t r x : ℕ) (pre : List ℕ)
    (hg : WfOpGenQ (t, r, .Del pre x)) :
    WfOpQ (t, r, .Del pre x) s := by
  obtain ⟨hx0, hlt⟩ := hg
  have hres : resolve s pre = 0 ∨ resolve s pre < x := by
    rcases resolve_mem s pre with h0 | hmem
    · left; exact h0
    · right; exact hlt _ hmem
  refine ⟨?_, hres⟩
  intro heq
  rcases hres with h0 | hlt'
  · apply hx0; rw [← heq]; exact h0
  · rw [heq] at hlt'; exact absurd hlt' (lt_irrefl x)

/-! ## §5. `WfOpGenQ` holds at generation -/

/-- Under `id_mono`, ids strictly DESCEND along a genuine ancestor path: every
element of `pre` is `< x`.  (The `anc = 0` branch is impossible mid-path — path
entries are live, the root is not.) -/
theorem isAncPath_mem_lt (s : concrete_st) (h0 : contains s 0 = false)
    (hmono : id_mono s) :
    ∀ (p : List ℕ) (x : ℕ), contains s x = true → IsAncPath s x p →
      ∀ c ∈ p, c < x := by
  intro p
  induction p with
  | nil => intro x _ _ c hc; simp at hc
  | cons d ds ih =>
    intro x hx hpath c hc
    simp only [IsAncPath] at hpath
    obtain ⟨hd, hdl, hds⟩ := hpath
    have hdx : d < x := by
      rcases hmono x hx with ha0 | halt
      · exfalso
        rw [ha0] at hd
        rw [← hd] at hdl
        rw [h0] at hdl
        exact Bool.noConfusion hdl
      · rw [hd] at halt; exact halt
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact hdx
    · exact lt_trans (ih d hdl hds c hc') hdx

/-- **`WfOpGenQ` for `Ins` at generation**: `fresh_ts` gives `t ≠ 0`; `accurate`
makes the anchor and every path entry live (or the root-with-empty-path case),
and `mono_alloc` — the generating site's monotone allocation — puts every live
id below `t`.  A static consequence of generation-time applicability. -/
theorem wfOpGenQ_ins (s : concrete_st) (t r e a : ℕ) (pre : List ℕ)
    (hfr : fresh_ts (t, r, .Ins e pre a) s)
    (hacc : accurate (t, r, .Ins e pre a) s)
    (halloc : mono_alloc (t, r, .Ins e pre a) s) :
    WfOpGenQ (t, r, .Ins e pre a) := by
  simp only [fresh_ts] at hfr
  simp only [accurate, opLeaf, opPath] at hacc
  simp only [mono_alloc] at halloc
  obtain ⟨ht0, _⟩ := hfr
  refine ⟨ht0, ?_⟩
  intro c hc
  rcases hacc with ⟨ha0, hp0⟩ | ⟨halive, hpath⟩
  · subst ha0; subst hp0
    simp only [List.mem_singleton] at hc
    subst hc
    exact Nat.pos_of_ne_zero ht0
  · rcases List.mem_cons.mp hc with rfl | hc'
    · exact halloc c halive
    · exact halloc c (isAncPath_mem s a pre hpath c hc')

/-- **`WfOpGenQ` for a LIVE `Del` at generation**: the target is live hence
nonzero, and its genuine ancestor path descends in id (`isAncPath_mem_lt`,
from the generation state's `id_mono`).  A static consequence of `accurate` +
`qInv` at generation. -/
theorem wfOpGenQ_del_live (s : concrete_st) (t r x : ℕ) (pre : List ℕ)
    (h0 : contains s 0 = false) (hmono : id_mono s)
    (hlive : contains s x = true) (hpath : IsAncPath s x pre) :
    WfOpGenQ (t, r, .Del pre x) :=
  ⟨contains_ne_zero s x h0 hlive, isAncPath_mem_lt s h0 hmono pre x hlive hpath⟩

/-! ## §6. `WfOpReachable RGACondSig' WfOpQ WfOpGenQ` — dischargeable at
reordered folds.  Mirror of `RGA_WfOpReachable.wfChain_acc`: the only
fold-positional conjunct is Ins freshness (from `Nodup` + distinct ts + the
fold-domain lemma); every Q-extra is static (§4). -/

theorem wfChainQ_acc : ∀ (rest pre : List op_t),
    (pre ++ rest).Nodup →
    (∀ a ∈ pre ++ rest, ∀ b ∈ pre ++ rest, a ≠ b → Op.time a ≠ Op.time b) →
    (∀ o ∈ rest, WfOpGenQ o) →
    WfChain RGACondSig' WfOpQ (applySeqR init_st pre) rest := by
  intro rest
  induction rest with
  | nil => intro pre _ _ _; exact True.intro
  | cons o rest' ih =>
    intro pre hnd hts hgen
    refine ⟨?head, ?tail⟩
    case head =>
      have hdisj : pre.Disjoint (o :: rest') :=
        List.disjoint_of_nodup_append hnd
      have hfresh : ∀ b ∈ pre, Op.time b ≠ Op.time o := by
        intro b hb
        have hbo : b ≠ o := by
          intro heq; apply hdisj hb; rw [heq]; exact List.mem_cons.mpr (Or.inl rfl)
        exact hts b (List.mem_append_left _ hb) o
          (List.mem_append_right _ (List.mem_cons.mpr (Or.inl rfl))) hbo
      have hgo : WfOpGenQ o := hgen o (List.mem_cons.mpr (Or.inl rfl))
      obtain ⟨t, r, ao⟩ := o
      cases ao with
      | Ins e p a =>
        refine wfOpQ_ins_of_genQ _ t r e a p hgo ?_
        by_contra hc
        have hc' : contains (applySeqR init_st pre) t = true := by
          cases hh : contains (applySeqR init_st pre) t
          · exact absurd hh hc
          · rfl
        obtain ⟨r', e', p', a', hmem⟩ := insertedIn_of_contains_fold pre t hc'
        exact hfresh (t, r', app_op_t.Ins e' p' a') hmem rfl
      | Del p x =>
        exact wfOpQ_del_of_genQ _ t r x p hgo
    case tail =>
      have hstate : applySeqR init_st (pre ++ [o]) = do_ (applySeqR init_st pre) o := by
        simp only [applySeqR, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have happ : (pre ++ [o]) ++ rest' = pre ++ o :: rest' := by
        rw [List.append_assoc]; rfl
      have key := ih (pre ++ [o])
        (by rw [happ]; exact hnd)
        (by rw [happ]; exact hts)
        (fun o' ho' => hgen o' (List.mem_cons_of_mem o ho'))
      rw [hstate] at key
      show WfChain RGACondSig' WfOpQ (do_ (applySeqR init_st pre) o) rest'
      exact key

/-- **`WfOpReachable` for `WfOpQ`, satisfied** — `WfOpQ` holds at every fold
prefix of any `Nodup`, distinct-ts, `WfOpGenQ` list.  So the strengthened guard
is exactly as dischargeable as `WfOp` was. -/
theorem rga_wfOpReachableQ : WfOpReachable RGACondSig' WfOpQ WfOpGenQ :=
  fun ρ hnd hts hgen => wfChainQ_acc ρ [] hnd hts hgen

#print axioms rgaInvPresQ
#print axioms wfOpGenQ_ins
#print axioms wfOpGenQ_del_live
#print axioms rga_wfOpReachableQ

end Sal.ConditionedMRDTs.RGAInvUpdateQ
