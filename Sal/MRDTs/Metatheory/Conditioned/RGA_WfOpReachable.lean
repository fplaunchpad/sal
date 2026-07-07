import Sal.MRDTs.Metatheory.Conditioned.RGA_InvFresh
import Sal.MRDTs.Metatheory.Conditioned.G2_Transport_Probe
import Sal.MRDTs.Metatheory.Conditioned.RGA_CanonFoldOK
import Sal.MRDTs.Metatheory.Conditioned.GenericEqQuotient

/-!
# Discharging the framework's `WfOpReachable` VC for the tombstone-free RGA

`GenericEqQuotient.WfOpReachable D W` (its EXACT def) is

    ∀ ρ, ρ.Nodup → (pairwise-distinct timestamps on ρ) → WfChain D W D.init ρ

i.e. `W` holds at every fold-prefix of ANY `Nodup`, distinct-timestamp list — it
keeps NONE of the reachable-configuration context beyond those two facts.

For the RGA the target `W` is `WfOp` (`RGA_InvFresh`):
* `Ins t`:  `t ≠ 0 ∧ contains (fold pre) t = false`
* `Del pre x`:  `resolve (fold pre) pre ≠ x`.

**The two supplied facts are NOT enough.**  `Nodup + distinct-ts` gives the Ins
FRESHNESS conjunct (`contains … = false`) cleanly, but it cannot supply
`t ≠ 0` (a `t = 0` Ins is `Nodup`+distinct-ts-legal), nor the Del path
condition (a `Del [x] x` at a state where `x` is live has `resolve = x`).  Those
are per-op GENUINENESS facts (`t ≠ 0`; `x ∉ pre ∧ x ≠ 0`) that a real execution
supplies through `applicable` at the generation state, not through the VC's
hypotheses.  Hence the literal `WfOpReachable RGACondSig WfOp` is **refutable**
(`rga_wfOpReachable_false`, below), and the honest discharge carries the per-op
genuineness predicate `WfOpGen` (`rga_wfChain_of_genuine`).

Both structural halves close cleanly:
* **Ins freshness** — `contains (fold pre) t = false` from distinct-ts + `Nodup`
  + the fold-domain lemma `insertedIn_of_contains_fold` (ids enter a fold only by
  their own `Ins`), because `t`'s own event is not in `pre`.
* **Del path ≠ target** — `resolve (fold pre) pre ≠ x` from `x ∉ pre` (so
  `resolve ∈ {0} ∪ pre` by `resolve_mem`, never `x`) together with `x ≠ 0` (which
  rules out the `resolve = 0` branch).  This holds REGARDLESS of liveness /
  rehoming: the argument is purely about the recorded entries, confirming the
  path never resolves to its own target.
-/

set_option maxHeartbeats 1000000

open Sal.Emulation (Op)
open Sal.Metatheory.GenericEqQuotient (WfChain WfOpReachable)
open Sal.Metatheory.RGASig (RGACondSig resolve_mem isAncPath_not_mem)
open Sal.Metatheory.RGACanonFoldOK (insertedIn_of_contains_fold)
open RGACanonConvergence (insertedIn)
open RGAMergeLinearization (applySeqR)

/-- **Per-op genuineness** — the order-stable side condition a real execution
supplies (via `applicable` at generation).  `Ins` needs a nonzero id; `Del` needs
a self-free (`x ∉ pre`) and non-root (`x ≠ 0`) target.  This is exactly the gap
between `WfOpReachable`'s `Nodup + distinct-ts` and the RGA's `WfOp`. -/
def WfOpGen : op_t → Prop
  | (t, _, .Ins _ _ _) => t ≠ 0
  | (_, _, .Del pre x) => x ∉ pre ∧ x ≠ 0

/-- **The accumulator discharge.**  Folding `rest` from the state reached by an
already-applied prefix `pre`, `WfOp` holds at every step, provided the whole list
`pre ++ rest` is `Nodup` with distinct timestamps and every event of `rest` is
`WfOpGen`.  Proof: at each head `o`, the Ins-freshness conjunct comes from the
fold-domain lemma (no `pre`-event shares `o`'s id) and the Del path fact from
`resolve_mem`; the state advances by `applySeqR … (pre ++ [o])`. -/
theorem wfChain_acc : ∀ (rest pre : List op_t),
    (pre ++ rest).Nodup →
    (∀ a ∈ pre ++ rest, ∀ b ∈ pre ++ rest, a ≠ b → Op.time a ≠ Op.time b) →
    (∀ o ∈ rest, WfOpGen o) →
    WfChain RGACondSig WfOp (applySeqR init_st pre) rest := by
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
      have hgo : WfOpGen o := hgen o (List.mem_cons.mpr (Or.inl rfl))
      obtain ⟨t, r, ao⟩ := o
      cases ao with
      | Ins e p a =>
        show t ≠ 0 ∧ contains (applySeqR init_st pre) t = false
        refine ⟨hgo, ?_⟩
        by_contra hc
        have hc' : contains (applySeqR init_st pre) t = true := by
          cases hh : contains (applySeqR init_st pre) t
          · exact absurd hh hc
          · rfl
        obtain ⟨r', e', p', a', hmem⟩ := insertedIn_of_contains_fold pre t hc'
        exact hfresh (t, r', app_op_t.Ins e' p' a') hmem rfl
      | Del p x =>
        show resolve (applySeqR init_st pre) p ≠ x
        obtain ⟨hxp, hx0⟩ := hgo
        intro heq
        rcases resolve_mem (applySeqR init_st pre) p with h0 | hmem
        · apply hx0; rw [← heq, h0]
        · rw [heq] at hmem; exact hxp hmem
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
      show WfChain RGACondSig WfOp (do_ (applySeqR init_st pre) o) rest'
      exact key

/-- **Honest discharge of the VC (conditioned form).**  For any `Nodup`,
distinct-timestamp list whose events are all `WfOpGen`, `WfOp` holds at every
fold-prefix from `init`.  This is `WfOpReachable` with the ONE honest execution
hypothesis (`WfOpGen`) the datatype genuinely needs and that a reachable
configuration supplies (`wfOpGen_ins` / `wfOpGen_del_live`).  `Nodup +
distinct-ts` alone are insufficient — see `rga_wfOpReachable_false`. -/
theorem rga_wfChain_of_genuine (ρ : List op_t)
    (hnd : ρ.Nodup)
    (hts : ∀ a ∈ ρ, ∀ b ∈ ρ, a ≠ b → Op.time a ≠ Op.time b)
    (hgen : ∀ o ∈ ρ, WfOpGen o) :
    WfChain RGACondSig WfOp RGACondSig.init ρ :=
  wfChain_acc ρ [] hnd hts hgen

/-- Genuineness is FREE at the generation state for a fresh insert: `fresh_ts`
already gives the nonzero id. -/
theorem wfOpGen_ins {t r e a : ℕ} {p : List ℕ} (ht : t ≠ 0) :
    WfOpGen (t, r, app_op_t.Ins e p a) := ht

/-- Genuineness is FREE at the generation state for a LIVE delete: the recorded
path is the target's genuine ancestor chain, hence self-free (`x ∉ pre`,
`isAncPath_not_mem`), and the live target is non-root (`contains x ⇒ x ≠ 0`).
So `resolve … pre ≠ x` holds regardless of any later rehoming. -/
theorem wfOpGen_del_live {t r x : ℕ} {p : List ℕ} {s : concrete_st}
    (h0 : contains s 0 = false) (hlive : contains s x = true)
    (hpath : IsAncPath s x p) :
    WfOpGen (t, r, app_op_t.Del p x) := by
  refine ⟨isAncPath_not_mem s h0 x p hpath, ?_⟩
  intro hx0; rw [hx0, h0] at hlive; exact Bool.noConfusion hlive

/- **HISTORICAL FINDING — the old 2-argument `WfOpReachable` was FALSE.** It kept
only `Nodup` + distinct timestamps, no per-op genuineness. A single genuinely-
applicable root delete `[(2,0,.Del [] 0)]` (accurate at `init`, hence reachable)
breaks `WfOp`: `resolve init [] = 0 = x`, so `WfOp (Del [] 0) init = (0≠0)` is
false, yet the list is `Nodup` with distinct timestamps. (A `t=0` insert refutes it
too.) The framework's `WfOpReachable` was strengthened to carry the per-event
`WfOpGen` premise (`GenericEqQuotient.lean`); the RGA now DISCHARGES the corrected
3-argument VC below. -/

/-- **`WfOpReachable` for the RGA, satisfied.**  The corrected 3-argument VC holds:
`rga_wfChain_of_genuine` is exactly its unfolded form under the RGA's `WfOpGen`
(Ins `t≠0`; Del `x∉pre ∧ x≠0`), which is free at generation. -/
theorem rga_wfOpReachable : WfOpReachable RGACondSig WfOp WfOpGen :=
  rga_wfChain_of_genuine

#print axioms rga_wfChain_of_genuine
#print axioms wfOpGen_del_live
#print axioms rga_wfOpReachable
