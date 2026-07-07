import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_RecPathFaithful
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_ChainFaithful_doDel

/-!
# Interleaved Faithful-threading: the accurate-ancestor `Ins` step (Step 1) and the
interleaved-enablement fold (Step 2)

*Additive; modifies no existing file; 0 `sorry` in what is kept.*

This file closes the ONE gap M1's `chainFaithful_doIns` left for threading
`ChainFaithful (recList w)` along an INTERLEAVED delivery prefix: the step that
folds an event's OWN accurate ancestor `Ins` (id `t' ∈ recList w`, a genuine
dead ancestor entry becoming live), not the concurrent-fresh `Ins` (`t' ∉
recList w`, already covered by `chainFaithful_doIns`) and not the clash regime
(`t' ∈ L` for an INCONSISTENT `L`, refuted by
`RGA_StaledDel_Gate.chainFaithful_not_preserved_under_clash_ins`).

The distinction between the ancestor step and the clash regime is exactly the
`RecListVisFaithful` linkage the `RGA_UpdateConvergence_Assembly` note located:
here the inserted id `t'` sits in `recList w`'s DEAD descendant-prefix and
attaches at the current live chain head (`AncInsLink`), so the residual
ChainFaithfulAux obligation `resolve s ((recList w).filter (· ≠ t')) = anch'`
closes; in the clash regime it does not.  Step 1 proves the step preservation
GIVEN this per-step linkage; Step 2 threads it (with the concurrent-Ins and
`Faithful`-Del steps) from the vacuous base `ChainFaithful init_st (recList w)`
to the enabled prefix, yielding `Faithful w (applySeqR init_st pre)` — the M1
ingredient `eq_convergence`'s oracle consumes.
-/

set_option maxHeartbeats 1000000

open Sal.ConditionedMRDTs.RGABubbleWiring
  (recList ChainFaithful ChainFaithfulAux chainFaithful_doIns chainFaithfulAux_doIns
   climbFaithful_of_chain)
open Sal.ConditionedMRDTs.RGAChainFaithfulDoDel
  (chain_unfold aux_nil flt_comm filter_ne_length_lt resolve_mem_of_live
   all_dead_of_resolve_dead resolve_all_dead)
open Sal.ConditionedMRDTs.RGAGeneralSwap (Faithful ClimbFaithful DelTargetFaithful contains_init)
open Sal.ConditionedMRDTs.RGAStaledDelGate (chainFaithful_doDel_faithful)
open Sal.ConditionedMRDTs.RGAConditionedConvergence (applySeqR applySeqR_cons applySeqR_nil)
open RGAFaithfulThreadingGate
  (IncompStep IncompFold chainFaithful_incompStep chainFaithful_incompFold foldDo)
open RGARecPathFaithful (RecPathFaithful faithful_of_recPathFaithful)

namespace RGAInterleavedThreading

/-! ## §0  A dead id is never a `resolve` value, and removing it is inert -/

/-- `resolve` returns a live candidate or the root `0`; a nonzero dead id is
neither, so `resolve` never equals it. -/
theorem resolve_ne_dead (s : concrete_st) (y : ℕ) (hy : contains s y = false)
    (hy0 : y ≠ 0) : ∀ (M : List ℕ), resolve s M ≠ y := by
  intro M
  induction M with
  | nil => simp only [resolve]; exact fun e => hy0 e.symm
  | cons c rest ih =>
    simp only [resolve]
    by_cases hc : contains s c = true
    · rw [if_pos hc]; intro e; subst e; rw [hy] at hc; exact Bool.noConfusion hc
    · rw [if_neg hc]; exact ih

/-- **Removing a dead list entry preserves `ChainFaithfulAux`.**  A dead `y` is
never a `resolve` value, so it is never selected in the chain recursion; deleting
it from the list leaves every `resolve`/`anc` level untouched.  The fuel-indexed
statement (input fuel `n ≥ M.length`, output at any adequate `m`) matches the
`ChainFaithful` fuel bookkeeping Step 1 needs. -/
theorem chainFaithfulAux_removeDead (s : concrete_st) (h0 : contains s 0 = false)
    (y : ℕ) (hy : contains s y = false) (hy0 : y ≠ 0) :
    ∀ (n : Nat) (M : List ℕ), M.length ≤ n → ChainFaithfulAux s n M →
      ∀ (m : Nat), (M.filter (fun c => c != y)).length ≤ m →
        ChainFaithfulAux s m (M.filter (fun c => c != y)) := by
  intro n
  induction n with
  | zero =>
    intro M hM _ m _
    have : M = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hM)
    subst this; simpa using aux_nil s h0 m
  | succ n ih =>
    intro M hM hCF m hm
    by_cases hlive : contains s (resolve s M) = true
    · set v := resolve s M with hv
      have hfy : resolve s (M.filter (fun c => c != y)) = v := by
        rw [hv]; exact resolve_filter_ne s y M (resolve_ne_dead s y hy hy0 M)
      obtain ⟨hlink, htail⟩ := chain_unfold s h0 (n + 1) M hCF hM hlive
      simp only [Nat.add_sub_cancel] at htail
      have hvmem : v ∈ M := resolve_mem_of_live s h0 M hlive
      have hvne_y : v ≠ y := resolve_ne_dead s y hy hy0 M
      have hvmemf : v ∈ M.filter (fun c => c != y) := by
        rw [List.mem_filter]; exact ⟨hvmem, by simp [hvne_y]⟩
      cases m with
      | zero => exact absurd (List.length_pos_of_mem hvmemf) (by omega)
      | succ k =>
        intro _
        refine ⟨?_, ?_⟩
        · rw [hfy, flt_comm y v M,
            resolve_filter_ne s y (M.filter (fun c => c != v)) (resolve_ne_dead s y hy hy0 _)]
          exact hlink
        · rw [hfy, flt_comm y v M]
          have hlt : (M.filter (fun c => c != v)).length < M.length :=
            filter_ne_length_lt M v hvmem
          have hb : ((M.filter (fun c => c != y)).filter (fun c => c != v)).length
              < (M.filter (fun c => c != y)).length := filter_ne_length_lt _ v hvmemf
          have hbe : ((M.filter (fun c => c != v)).filter (fun c => c != y)).length
              = ((M.filter (fun c => c != y)).filter (fun c => c != v)).length :=
            congrArg List.length (flt_comm v y M)
          exact ih (M.filter (fun c => c != v)) (by omega) htail k (by omega)
    · have hvf : contains s (resolve s M) = false := by
        cases hh : contains s (resolve s M) with
        | true => exact absurd hh hlive
        | false => rfl
      have hall : ∀ c ∈ M, contains s c = false := all_dead_of_resolve_dead s M hvf
      cases m with
      | zero => exact trivial
      | succ k =>
        intro hlive'
        have hz : resolve s (M.filter (fun c => c != y)) = 0 :=
          resolve_all_dead s _ (fun c hc => hall c (List.mem_of_mem_filter hc))
        rw [hz, h0] at hlive'; exact absurd hlive' (by simp)

/-- `resolve` skips an all-dead prefix. -/
theorem resolve_dead_prefix (s : concrete_st) :
    ∀ (D rest : List ℕ), (∀ c ∈ D, contains s c = false) →
      resolve s (D ++ rest) = resolve s rest := by
  intro D rest
  induction D with
  | nil => intro _; rfl
  | cons c D' ih =>
    intro hd
    have hc : contains s c = false := hd c List.mem_cons_self
    rw [List.cons_append, resolve_dead_head s c _ hc]
    exact ih (fun d hdm => hd d (List.mem_cons_of_mem _ hdm))

/-! ## §1  Step 1 — the accurate-ancestor `Ins` step preserves `ChainFaithful`

The step M1's `chainFaithful_doIns` omitted: fold an event's OWN accurate ancestor
`Ins` whose fresh id `t'` is a genuine (dead) entry of `recList w`, becoming live.
The residual ChainFaithfulAux obligation `resolve s ((recList w).filter (· ≠ t')) =
anch'` closes precisely under the linkage `AncInsLink` (t' in the dead
descendant-prefix, attaching at the current live chain head) — the localized
`RecListVisFaithful` fact that separates this from the clash counterexample. -/

/-- **`AncInsLink s L t' anch'`** — the per-step reachability linkage: `L` splits as
`D ++ t' :: R` where the descendant-prefix `D` is all dead in `s`, `t'` is dead
(about to be inserted), its parent `anch'` is live, and `anch'` is the current live
head of the tail `R`.  For `L = recList w` this is exactly "recList w is w's true
chain and t' attaches at its recorded parent", localized to the folded step. -/
def AncInsLink (s : concrete_st) (L : List ℕ) (t' anch' : ℕ) : Prop :=
  ∃ D R : List ℕ,
    L = D ++ t' :: R ∧ (∀ c ∈ D, contains s c = false) ∧
    t' ∉ D ∧ t' ∉ R ∧ contains s t' = false ∧
    contains s anch' = true ∧ resolve s R = anch'

/-- **Step 1 — `chainFaithful_doIns_ancestor`.**  Under `AncInsLink`, folding the
accurate ancestor `Ins` `(t', r', .Ins e' p' anch')` preserves
`ChainFaithful L`.  The new head `t'` slots in at `anch'` (the old live head), the
top obligation is `resolve s' (D ++ R) = anc s' t' = anch'`, and the recursion is
`chainFaithfulAux_doIns` over the dead-`t'`-removed list (`chainFaithfulAux_removeDead`). -/
theorem chainFaithful_doIns_ancestor (s : concrete_st) (t' r' e' anch' : ℕ)
    (p' L : List ℕ) (h0 : contains s 0 = false) (ht'0 : t' ≠ 0)
    (hlink : AncInsLink s L t' anch') (hcf : ChainFaithful s L) :
    ChainFaithful (do_ s (t', r', .Ins e' p' anch')) L := by
  obtain ⟨D, R, hL, hDdead, htD, htR, ht'dead, hanchlive, hRhead⟩ := hlink
  subst hL
  set s' := do_ s (t', r', .Ins e' p' anch') with hs'
  have hstep : s' = upd s t' (e', resolve s (anch' :: p')) := by rw [hs']; simp only [do_]
  have htDR : t' ∉ D ++ R := fun h => (List.mem_append.mp h).elim htD htR
  have ht'live' : contains s' t' = true := by
    rw [hstep, lemma_InDomUpd1 s t' t' (e', resolve s (anch' :: p'))]; simp
  have hDdead' : ∀ c ∈ D, contains s' c = false := by
    intro c hc
    have hcne : c ≠ t' := fun e => htD (e ▸ hc)
    rw [hstep, lemma_InDomUpd2 s c t' (e', resolve s (anch' :: p'))
      (by simp only [bne_iff_ne, ne_eq]; exact fun e => hcne e.symm)]
    exact hDdead c hc
  have hanc_t' : anc s' t' = anch' := by
    simp only [anc, hstep, lemma_SelUpd1]
    exact resolve_live_head s anch' p' hanchlive
  have hresN : resolve s' (D ++ t' :: R) = t' := by
    rw [resolve_dead_prefix s' D (t' :: R) hDdead']
    exact resolve_live_head s' t' R ht'live'
  have hresDR : resolve s' (D ++ R) = anch' := by
    rw [resolve_dead_prefix s' D R hDdead', hstep,
        resolve_upd_notMem s t' (e', resolve s (anch' :: p')) R htR, hRhead]
  have hfilt : (D ++ t' :: R).filter (fun c => c != t') = D ++ R := by
    have hDf : D.filter (fun c => c != t') = D :=
      List.filter_eq_self.mpr (fun c hc => by
        simp only [bne_iff_ne, ne_eq]; exact fun e => htD (e ▸ hc))
    have hRf : R.filter (fun c => c != t') = R :=
      List.filter_eq_self.mpr (fun c hc => by
        simp only [bne_iff_ne, ne_eq]; exact fun e => htR (e ▸ hc))
    simp [List.filter_append, hDf, hRf]
  have hbaseS : ChainFaithfulAux s (D ++ R).length (D ++ R) := by
    have := chainFaithfulAux_removeDead s h0 t' ht'dead ht'0
      (D ++ t' :: R).length (D ++ t' :: R) (le_refl _) hcf (D ++ R).length
      (Nat.le_of_eq (by rw [hfilt]))
    rwa [hfilt] at this
  have hbase : ChainFaithfulAux s' (D ++ R).length (D ++ R) :=
    chainFaithfulAux_doIns s t' r' e' anch' p' ht'0 (D ++ R).length (D ++ R) htDR hbaseS
  have hNlen : (D ++ t' :: R).length = (D ++ R).length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  show ChainFaithfulAux s' (D ++ t' :: R).length (D ++ t' :: R)
  rw [hNlen]
  simp only [ChainFaithfulAux]
  rw [hresN, hfilt]
  intro _
  exact ⟨by rw [hresDR, hanc_t'], hbase⟩

/-! ## §2  Step 2 — the interleaved-enablement fold

Thread `ChainFaithful (recList w)` from the vacuous base `ChainFaithful init_st
(recList w)` (all of `recList w` dead at `init`) along an INTERLEAVED delivery
prefix `pre`.  Each step of `pre` is a `GoodStep` for `recList w`: a concurrent
fresh `Ins` (`chainFaithful_doIns`), `w`'s own accurate ancestor `Ins` (Step 1),
or a staled `Faithful` `Del` (`chainFaithful_doDel_faithful`).  At the end,
`ChainFaithful (recList w)` holds at `applySeqR init_st pre`, projecting to
`Faithful w` for the enabled `Ins`. -/

/-- **`GoodStep s L o`** — the per-step classification a `loOnA`-respecting
interleaved prefix presents for the pending list `L = recList w`: a concurrent
fresh `Ins` (`t ≠ 0`, `t ∉ L`), `w`'s own accurate ancestor `Ins` (`AncInsLink`),
or a staled `Faithful` `Del`.  Discharging that every reachable step IS a
`GoodStep` (in particular the `AncInsLink` linkage) is the reachability invariant
the execution model supplies; the ORDER-layer preservation is closed below. -/
def GoodStep (s : concrete_st) (L : List ℕ) (o : op_t) : Prop :=
  match o with
  | (t, _, .Ins _ _ anch) =>
      (t ≠ 0 ∧ t ∉ L) ∨ (t ≠ 0 ∧ contains s 0 = false ∧ AncInsLink s L t anch)
  | (_, _, .Del _ _) => contains s 0 = false ∧ wf s ∧ Faithful o s

/-- One `GoodStep` preserves `ChainFaithful L`. -/
theorem chainFaithful_goodStep (s : concrete_st) (L : List ℕ) (o : op_t)
    (hg : GoodStep s L o) (hcf : ChainFaithful s L) : ChainFaithful (do_ s o) L := by
  obtain ⟨t, r, op⟩ := o
  cases op with
  | Ins e pre a =>
      simp only [GoodStep] at hg
      rcases hg with ⟨ht0, htL⟩ | ⟨ht0, h0, hlink⟩
      · exact chainFaithful_doIns s t r e a pre L ht0 htL hcf
      · exact chainFaithful_doIns_ancestor s t r e a pre L h0 ht0 hlink hcf
  | Del pre x =>
      simp only [GoodStep] at hg
      obtain ⟨h0, hwf, hfaith⟩ := hg
      exact chainFaithful_doDel_faithful s t r x pre L h0 hwf hfaith hcf

/-- Every step of `π` is a `GoodStep` for `L` at its own prefix fold. -/
def GoodFold (L : List ℕ) : concrete_st → List op_t → Prop
  | _, [] => True
  | s, o :: rest => GoodStep s L o ∧ GoodFold L (do_ s o) rest

/-- **The interleaved threading — CLOSED (order layer).**  `ChainFaithful L` is
preserved along any fold whose every step is a `GoodStep` for `L`. -/
theorem chainFaithful_goodFold (L : List ℕ) :
    ∀ (π : List op_t) (s : concrete_st),
      GoodFold L s π → ChainFaithful s L → ChainFaithful (applySeqR s π) L := by
  intro π
  induction π with
  | nil => intro s _ hcf; rw [applySeqR_nil]; exact hcf
  | cons o rest ih =>
      intro s hgf hcf
      obtain ⟨hstep, hrest⟩ := hgf
      rw [applySeqR_cons]
      exact ih (do_ s o) hrest (chainFaithful_goodStep s L o hstep hcf)

/-- On an everywhere-dead state, `ChainFaithfulAux` holds at any fuel/list
(vacuously — no climb-target is ever live). -/
theorem chainFaithfulAux_all_dead (s : concrete_st) (hdead : ∀ k, contains s k = false) :
    ∀ (n : Nat) (L : List ℕ), ChainFaithfulAux s n L := by
  intro n
  induction n with
  | zero => intro L; exact trivial
  | succ k _ =>
      intro L hlive
      rw [hdead (resolve s L)] at hlive; exact absurd hlive (by simp)

/-- **The vacuous base.**  `ChainFaithful init_st (recList w)`: every id is dead at
`init`, so the chain invariant holds at fuel-full vacuously. -/
theorem chainFaithful_init_recList (w : op_t) : ChainFaithful init_st (recList w) :=
  chainFaithfulAux_all_dead init_st contains_init (recList w).length (recList w)

/-- **Step 2 (core) — `ChainFaithful (recList w)` at the interleaved enabled fold.**
From the vacuous base, threaded along the `GoodFold` interleaving `pre`. -/
theorem chainFaithful_at_interleaved_fold (w : op_t) (pre : List op_t)
    (hgf : GoodFold (recList w) init_st pre) :
    ChainFaithful (applySeqR init_st pre) (recList w) :=
  chainFaithful_goodFold (recList w) pre init_st hgf (chainFaithful_init_recList w)

/-- **Step 2 (Ins projection) — `faithful_at_interleaved_fold`.**  For an enabled
pending `Ins` `w`, `Faithful w` holds at the interleaved delivery prefix — exactly
the M1 ingredient `eq_convergence`'s oracle consumes.  The `Del` projection uses the
`LiveChain` route (`RGA_RecPathFaithful.faithful_of_recPathFaithful`), not repeated
here. -/
theorem faithful_at_interleaved_fold (t r e a : ℕ) (p : List ℕ) (pre : List op_t)
    (hgf : GoodFold (recList (t, r, .Ins e p a)) init_st pre)
    (h0' : contains (applySeqR init_st pre) 0 = false) :
    Faithful (t, r, .Ins e p a) (applySeqR init_st pre) := by
  have hcf : ChainFaithful (applySeqR init_st pre) (a :: p) :=
    chainFaithful_at_interleaved_fold (t, r, .Ins e p a) pre hgf
  exact climbFaithful_of_chain (applySeqR init_st pre) (a :: p) h0' hcf

/-! ## §3  Axiom audit — kernel-clean, no `sorryAx`, no `native_decide`. -/

#print axioms chainFaithful_doIns_ancestor
#print axioms faithful_at_interleaved_fold

end RGAInterleavedThreading
