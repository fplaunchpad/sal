import Sal.MRDTs.Metatheory.Join.ReplayOrderBasics

/-!
# Set-relative linearization order (`loOn`) and its convergence theory

## Why this file exists

The original merge-linearization induction was blocked by six missing proofs
that depended on a convergence lemma valid over merely
backward-closed reachable replica sets: `convergence` with the
overwriter-closure hypothesis dropped.

**That lemma is false.** Counter-model (OR-set, add-wins,
`rem →rc add`, all 24 VCs hold): replica B executes `rem_a` (event
`y`), replica A executes `add_a` (event `e`), B merges A's state
*before* A issues a later `rem_a` (event `e₃`, `vis e e₃`). Then B's
event set is `{y, e}` (backward-closed) and in the final
configuration `C` (which contains `e₃`) the relation `lo C` orders
*neither* `y, e` (the rc-edge `y →lo e` is cancelled by the absorber
`e₃ ∈ C.events`). Both `[y, e]` and `[e, y]` respect `lo C`, but they
fold to different states (`{a-tag}` vs `∅`). Convergence over the
replica set w.r.t. `lo C` therefore fails.

## Set-relative `lo`

The absorber existential in `lo` must range over the *event set of
the version being linearized*, not over the whole configuration:

    loOn C ev e₁ e₂  ⟺  (vis e₁ e₂ ∧ ¬commute)
                       ∨ (concurrent ∧ rc e₁ e₂ = Fst
                          ∧ ¬∃ e₃ ∈ ev, vis e₂ e₃ ∧ ¬commute e₂ e₃)

In the counter-model `loOn C {y,e}` *keeps* the edge `y → e` (no
absorber inside `{y,e}`), so only `[y, e]` respects it and
convergence over `{y, e}` w.r.t. `loOn` holds. In general:

* `lo C ⊆ loOn C ev` pointwise, so a witness respecting `loOn` also
  respects `lo C`, the strengthened invariant *implies* the paper's
  Def-lin obligation.
* `loOn C ev` depends only on `vis`/`rc`/`commutes` restricted to
  `ev`, it never changes as the configuration grows, so it is a
  *stable* per-version invariant.
* Convergence w.r.t. `loOn C ev` needs **no closure hypotheses at
  all**: whenever the bubble-sort argument must swap a non-commuting
  concurrent pair, the failed `loOn`-edge *hands it an absorber
  inside `ev`* by definition.

This matches the Sal/Neem paper's own (implicit) usage: the appendix
Merge case works with `lo_i` whose absorber clause is
`∃ e'' ∈ L(v_i)` (appendix.tex, "lo between two events should remain
the same in all versions"). The paper's claim that `lo_i ⟺ lo_m` is
**false in the ⟹ direction** for shared events (a shared `e'` can
gain an absorber from the other branch's local events); the ⟸
direction, the one needed for sub-witness compatibility, is exactly
`loOn`-monotonicity below.

## Contents

1. `loOn`, monotonicity, transfer lemmas.
2. Acyclicity of `loOn C T` on `T` (from `no_rc_chain` + the absorber
   clause + `vis`-transitivity/irreflexivity, both reachability
   facts) and existence of `loOn`-maximal elements / respecting
   permutations of finite sets.
3. Swap/bubble lemmas re-targeted at `loOn`.
4. `convergence_on`, the *true* replacement for the false blocker:
   two `loOn C ev`-respecting permutations of `ev` fold to the same
   state, with no closure hypotheses.
5. Re-permutation (`perm_ending_in_loOn_max`) and the normalization
   lemma (`normalize_peel_tail`) that repairs a witness after a tail
   peel, restoring the `loOn`-of-current-set invariant.
-/

namespace Sal.MRDTs.Foundation

open Classical

section
variable {D : UpdateSig} [ReplayPolicy D]
variable [ReplayPolicy D]

/-! ### 0. The core VC bundle

The σ/`loOn` machinery of this file consumes only a small fragment of
`HistoricalReplayVCs`, notably NOT `shared_peel_1op`, which
`Convergence_CounterModel.lean` shows is *false* for state-dependent
RDTs like `AWSet`. Parameterizing over the fragment lets such RDTs
instantiate the Join-Lemma machinery. -/

/-- The fields of `HistoricalReplayVCs` actually consumed by the set-relative
linearization theory and the Join-Lemma induction. -/
structure BinaryMergeLaws (D : UpdateSig) [ReplayPolicy D]
    [HistoricalBinaryMerge D] : Prop where
  rc_non_comm_directional :
    ∀ o₁ o₂ : Op D.AppOp,
      distinctOps o₁ o₂ →
      (¬ D.commutes o₁ o₂ ↔
       (D.replayOrder o₁ o₂ = RcRes.Fst_then_snd ∨
        D.replayOrder o₂ o₁ = RcRes.Fst_then_snd))
  no_rc_chain :
    ∀ o₁ o₂ o₃ : Op D.AppOp,
      distinctOps o₁ o₂ → distinctOps o₂ o₃ →
      ¬ (D.replayOrder o₁ o₂ = RcRes.Fst_then_snd ∧
         D.replayOrder o₂ o₃ = RcRes.Fst_then_snd)
  cond_comm_lift :
    ∀ (s : D.State) (e e' e'' : Op D.AppOp) (π : List (Op D.AppOp)),
      distinctOps e e' → distinctOps e e'' → distinctOps e' e'' →
      D.replayOrder e e' = RcRes.Fst_then_snd →
      ¬ D.commutes e' e'' →
      D.update (applySeq D (D.update (D.update s e') e) π) e''
        = D.update (applySeq D (D.update (D.update s e) e') π) e''
  merge_comm : ∀ a b : D.State, D.historicalMerge a b = D.historicalMerge b a
  merge_init : ∀ s : D.State, D.historicalMerge D.init s = s
  lem_0op :
    ∀ (a b : D.State) (ol : Op D.AppOp),
      D.historicalMerge (D.update a ol) (D.update b ol)
        = D.update (D.historicalMerge a b) ol
  merge_peel_comm :
    ∀ (a : D.State) (e : Op D.AppOp) (π : List (Op D.AppOp)),
      (∀ x ∈ π, D.commutes e x) →
      D.historicalMerge (D.update a e) (applySeq D D.init π)
        = D.update (D.historicalMerge a (applySeq D D.init π)) e

/-- Core-bundle version of `applySeq_swap_via_cond_comm_lift`. -/
theorem applySeq_swap_via_cond_comm_lift_core
    [HistoricalBinaryMerge D]
    (hVC : BinaryMergeLaws D)
    {a b e₃ : Op D.AppOp}
    (h_dist_ab : distinctOps a b)
    (h_dist_be : distinctOps b e₃)
    (h_dist_ae : distinctOps a e₃)
    (h_rc_ab : D.replayOrder a b = RcRes.Fst_then_snd)
    (h_nc_be : ¬ D.commutes b e₃)
    (pfx α β : List (Op D.AppOp)) (s : D.State) :
    applySeq D s (pfx ++ a :: b :: (α ++ e₃ :: β))
    = applySeq D s (pfx ++ b :: a :: (α ++ e₃ :: β)) := by
  have hexp1 : applySeq D s (pfx ++ a :: b :: (α ++ e₃ :: β))
             = applySeq D (D.update (applySeq D
                 (D.update (D.update (applySeq D s pfx) a) b) α) e₃) β := by
    simp [applySeq, List.foldl_append, List.foldl_cons]
  have hexp2 : applySeq D s (pfx ++ b :: a :: (α ++ e₃ :: β))
             = applySeq D (D.update (applySeq D
                 (D.update (D.update (applySeq D s pfx) b) a) α) e₃) β := by
    simp [applySeq, List.foldl_append, List.foldl_cons]
  rw [hexp1, hexp2]
  exact congrArg (fun t => applySeq D t β)
    (hVC.cond_comm_lift (applySeq D s pfx) a b e₃ α
      h_dist_ab h_dist_ae h_dist_be h_rc_ab h_nc_be).symm

/-! ### 1. The set-relative linearization relation -/

/-- **Set-relative linearization relation.** Like `lo C`, but the
overwriter/absorber existential ranges over the event set `ev` of the
version being linearized instead of over the whole configuration.
`lo C = loOn C C.events` (the absorber's membership in `C.events` is
implied by `vis_tgt`). -/
def loOn (C : ReplayContext D) (ev : Set (Op D.AppOp))
    (e₁ e₂ : Op D.AppOp) : Prop :=
  (C.vis e₁ e₂ ∧ ¬ D.commutes e₁ e₂)
  ∨ ( ¬ C.vis e₁ e₂ ∧ ¬ C.vis e₂ e₁
      ∧ D.replayOrder e₁ e₂ = RcRes.Fst_then_snd
      ∧ ¬ ∃ e₃ ∈ ev, C.vis e₂ e₃ ∧ ¬ D.commutes e₂ e₃ )

/-- The configuration-global `lo` is contained in every `loOn`:
a `lo C`-edge asserts *no absorber anywhere*, hence none in `ev`. -/
theorem loOn_of_lo {C : ReplayContext D} {ev : Set (Op D.AppOp)}
    {e₁ e₂ : Op D.AppOp} (h : lo C e₁ e₂) : loOn C ev e₁ e₂ := by
  rcases h with h | ⟨h₁, h₂, h₃, h₄⟩
  · exact Or.inl h
  · exact Or.inr ⟨h₁, h₂, h₃, fun ⟨e₃, _, hv, hnc⟩ => h₄ ⟨e₃, hv, hnc⟩⟩

/-- Antitonicity in the event set: growing the set adds absorbers and
hence *removes* rc-edges. -/
theorem loOn_mono {C : ReplayContext D} {ev ev' : Set (Op D.AppOp)}
    (h_sub : ev ⊆ ev') {e₁ e₂ : Op D.AppOp}
    (h : loOn C ev' e₁ e₂) : loOn C ev e₁ e₂ := by
  rcases h with h | ⟨h₁, h₂, h₃, h₄⟩
  · exact Or.inl h
  · exact Or.inr ⟨h₁, h₂, h₃,
      fun ⟨e₃, he₃, hv, hnc⟩ => h₄ ⟨e₃, h_sub he₃, hv, hnc⟩⟩

/-- The vis-flavored edge lives in every `loOn`. -/
theorem loOn_of_vis_noncomm {C : ReplayContext D}
    {ev : Set (Op D.AppOp)} {a b : Op D.AppOp}
    (hv : C.vis a b) (hnc : ¬ D.commutes a b) : loOn C ev a b :=
  Or.inl ⟨hv, hnc⟩

/-- A permutation respecting `loOn C ev` respects the coarser
`loOn C ev'` for any larger `ev'`. -/
theorem respects_loOn_mono {ev ev' : Set (Op D.AppOp)}
    {C : ReplayContext D} {π : List (Op D.AppOp)}
    (h_sub : ev ⊆ ev')
    (h : respects π (loOn C ev)) : respects π (loOn C ev') :=
  h.imp (fun hn h' => hn (loOn_mono h_sub h'))

/-- A permutation respecting `loOn C ev` respects the paper's
configuration-global `lo C`, the strengthened invariant implies the
original Def-lin obligation. -/
theorem respects_lo_of_respects_loOn {ev : Set (Op D.AppOp)}
    {C : ReplayContext D} {π : List (Op D.AppOp)}
    (h : respects π (loOn C ev)) : respects π (lo C) :=
  h.imp (fun hn h' => hn (loOn_of_lo h'))

/-- Generic form of `last_is_lo_maximal`: the tail of a list
respecting any relation `R` has no `R`-successor in the prefix. -/
theorem last_is_maximal {α : Type} {R : α → α → Prop}
    {π' : List α} {e : α}
    (h_resp : respects (π' ++ [e]) R) :
    ∀ x ∈ π', ¬ R e x := by
  have hsplit := List.pairwise_append.mp h_resp
  intro x hx
  exact hsplit.2.2 x hx e (by simp)

/-- Generic form of `filter_ne_respects`. -/
theorem filter_ne_respects' {α : Type} [DecidableEq α]
    {R : α → α → Prop} {e : α} {π : List α}
    (h_resp : respects π R) :
    respects (π.filter (· ≠ e)) R :=
  h_resp.filter _

/-- Two distinct events of the configuration have distinct
timestamps (`distinctOps`). Convenience wrapper around
`timestamps_distinct`. -/
theorem distinctOps_of_events {C : ReplayContext D}
    {a b : Op D.AppOp}
    (ha : a ∈ C.events) (hb : b ∈ C.events) (hne : a ≠ b) :
    distinctOps a b := by
  obtain ⟨r, s, hL, hs⟩ := ha
  obtain ⟨r', s', hL', hs'⟩ := hb
  exact C.timestamps_distinct hL hs hL' hs' hne

/-! ### 2. Acyclicity and maximal elements

`loOn C T`, restricted to distinct events of `T`, has no cycles:

* an rc-flavored edge `x → y` cannot be followed by *any* edge
  `y → z` with `z ∈ T`, a vis-flavored successor makes `z` an
  absorber of `y` inside `T` (contradicting the rc-edge's no-absorber
  clause), and an rc-flavored successor violates `no_rc_chain`;
* hence a cycle would be all-vis-flavored, contradicting
  transitivity + irreflexivity of `vis` (both hold in reachable
  configurations; threaded as hypotheses, following the existing
  `h_vis_trans` convention of `no_lo_a_to_b`). -/

/-- The maximality step relation: a `loOn`-edge between *distinct*
events, both in `T`. Self-edges are irrelevant for `respects`
(pairwise over distinct positions of a nodup list). -/
def loOnNe (C : ReplayContext D) (T : Set (Op D.AppOp))
    (a b : Op D.AppOp) : Prop :=
  a ≠ b ∧ a ∈ T ∧ b ∈ T ∧ loOn C T a b

/-- **rc-flavored edges have no successors inside the set.** -/
theorem loOn_rc_no_succ [HistoricalBinaryMerge D]
    (hVC : BinaryMergeLaws D) {C : ReplayContext D}
    {T : Set (Op D.AppOp)}
    (h_in_C : ∀ a ∈ T, a ∈ C.events)
    {x y z : Op D.AppOp}
    (hxy_ne : x ≠ y) (hyz_ne : y ≠ z)
    (hx : x ∈ T) (hy : y ∈ T) (hz : z ∈ T)
    (h_rc_edge : ¬ C.vis x y ∧ ¬ C.vis y x
      ∧ D.replayOrder x y = RcRes.Fst_then_snd
      ∧ ¬ ∃ e₃ ∈ T, C.vis y e₃ ∧ ¬ D.commutes y e₃)
    (h_edge : loOn C T y z) : False := by
  obtain ⟨_, _, h_rc, h_no_abs⟩ := h_rc_edge
  rcases h_edge with ⟨hv, hnc⟩ | ⟨_, _, h_rc', _⟩
  · exact h_no_abs ⟨z, hz, hv, hnc⟩
  · exact hVC.no_rc_chain x y z
      (distinctOps_of_events (h_in_C x hx) (h_in_C y hy) hxy_ne)
      (distinctOps_of_events (h_in_C y hy) (h_in_C z hz) hyz_ne)
      ⟨h_rc, h_rc'⟩

/-- **Path structure:** every `loOnNe`-path is either vis-connected,
or its *last* edge is rc-flavored (an rc-flavored edge strictly
inside a path is killed by `loOn_rc_no_succ`). -/
theorem transGen_loOnNe_structure [HistoricalBinaryMerge D]
    (hVC : BinaryMergeLaws D)
    {C : ReplayContext D}
    (h_vis_trans : ∀ {a b c : Op D.AppOp},
       C.vis a b → C.vis b c → C.vis a c)
    {T : Set (Op D.AppOp)}
    (h_in_C : ∀ a ∈ T, a ∈ C.events)
    {a b : Op D.AppOp}
    (h : Relation.TransGen (loOnNe C T) a b) :
    C.vis a b ∨
    (∃ x, x ≠ b ∧ x ∈ T ∧
      (¬ C.vis x b ∧ ¬ C.vis b x
        ∧ D.replayOrder x b = RcRes.Fst_then_snd
        ∧ ¬ ∃ e₃ ∈ T, C.vis b e₃ ∧ ¬ D.commutes b e₃)) := by
  induction h with
  | single h_edge =>
    obtain ⟨hne, hxT, hyT, h_lo⟩ := h_edge
    rcases h_lo with ⟨hv, _⟩ | h_rc
    · exact Or.inl hv
    · exact Or.inr ⟨a, hne, hxT, h_rc⟩
  | tail _ h_edge ih =>
    rename_i mid c h_path
    obtain ⟨hne, hmidT, hcT, h_lo⟩ := h_edge
    rcases ih with h_vis_amid | ⟨x, hx_ne, hxT, h_rc_edge⟩
    · rcases h_lo with ⟨hv, _⟩ | h_rc
      · exact Or.inl (h_vis_trans h_vis_amid hv)
      · exact Or.inr ⟨mid, hne, hmidT, h_rc⟩
    · exact absurd h_lo
        (fun h => loOn_rc_no_succ hVC h_in_C hx_ne hne hxT hmidT hcT
          h_rc_edge h)

/-- **`loOnNe` is acyclic** (no `TransGen`-cycle). -/
theorem loOnNe_acyclic [HistoricalBinaryMerge D]
    (hVC : BinaryMergeLaws D) {C : ReplayContext D}
    (h_vis_trans : ∀ {a b c : Op D.AppOp},
       C.vis a b → C.vis b c → C.vis a c)
    (h_vis_irrefl : ∀ a : Op D.AppOp, ¬ C.vis a a)
    {T : Set (Op D.AppOp)}
    (h_in_C : ∀ a ∈ T, a ∈ C.events)
    (a : Op D.AppOp) :
    ¬ Relation.TransGen (loOnNe C T) a a := by
  intro h_cycle
  rcases transGen_loOnNe_structure hVC h_vis_trans h_in_C h_cycle with
    h_vis | ⟨x, hx_ne, hxT, h_rc_edge⟩
  · exact h_vis_irrefl a h_vis
  · -- The cycle also gives `a` an outgoing edge; compose it with the
    -- rc-flavored edge `x → a` to contradict `loOn_rc_no_succ`.
    have h_head : ∀ {p q : Op D.AppOp},
        Relation.TransGen (loOnNe C T) p q →
        ∃ c, loOnNe C T p c := by
      intro p q h
      induction h with
      | single h => exact ⟨_, h⟩
      | tail _ _ ih => exact ih
    obtain ⟨c, hac_ne, haT, hcT, h_lo⟩ := h_head h_cycle
    exact loOn_rc_no_succ hVC h_in_C hx_ne hac_ne hxT haT hcT
      h_rc_edge h_lo

/-- **A `loOn`-maximal element exists in every finite nonempty set**
(finiteness via an enumerating list). Maximal = no `loOn C T`-edge to
a *distinct* element of `T`.

Proof: greedy walk. Start anywhere; while the current event has an
outgoing edge, follow it. The walk cannot revisit an event (that
would close a `TransGen`-cycle, contradicting `loOnNe_acyclic`), so
it terminates at a maximal element. The `visited` bookkeeping is the
invariant `h_reach`: every event outside `rem ∪ {cur}` reaches `cur`
by a `TransGen`-path. -/
theorem exists_loOn_maximal [HistoricalBinaryMerge D]
    (hVC : BinaryMergeLaws D)
    {C : ReplayContext D}
    (h_vis_trans : ∀ {a b c : Op D.AppOp},
       C.vis a b → C.vis b c → C.vis a c)
    (h_vis_irrefl : ∀ a : Op D.AppOp, ¬ C.vis a a)
    {T : Set (Op D.AppOp)} {l : List (Op D.AppOp)}
    (h_l : listPermOf l T)
    (h_in_C : ∀ a ∈ T, a ∈ C.events)
    (h_ne : T.Nonempty) :
    ∃ e ∈ T, ∀ x ∈ T, x ≠ e → ¬ loOn C T e x := by
  suffices walk : ∀ n (rem : List (Op D.AppOp)), rem.length = n →
      rem.Nodup →
      ∀ cur ∈ T,
      (∀ x ∈ T, x ∉ rem → x ≠ cur →
        Relation.TransGen (loOnNe C T) x cur) →
      ∃ e ∈ T, ∀ x ∈ T, x ≠ e → ¬ loOn C T e x by
    obtain ⟨t₀, ht₀⟩ := h_ne
    exact walk l.length l rfl h_l.1 t₀ ht₀
      (fun x hx hx_not_l _ => absurd ((h_l.2 x).mpr hx) hx_not_l)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro rem h_len h_nodup cur h_cur h_reach
    by_cases h_max : ∃ x ∈ T, x ≠ cur ∧ loOn C T cur x
    · obtain ⟨x, hx_T, hx_ne, h_edge⟩ := h_max
      have h_edge_ne : loOnNe C T cur x :=
        ⟨fun h => hx_ne h.symm, h_cur, hx_T, h_edge⟩
      by_cases hx_rem : x ∈ rem
      · -- Step to `x`; recurse on the shrunk remainder.
        have h_len' : (rem.erase x).length < n := by
          have h_pos : 0 < rem.length := List.length_pos_of_mem hx_rem
          rw [List.length_erase_of_mem hx_rem]
          omega
        refine ih _ h_len' (rem.erase x) rfl (h_nodup.erase x)
          x hx_T ?_
        intro y hy_T hy_not hy_ne
        by_cases hy_cur : y = cur
        · subst hy_cur
          exact Relation.TransGen.single h_edge_ne
        · have hy_not_rem : y ∉ rem := fun h_in =>
            hy_not (h_nodup.mem_erase_iff.mpr ⟨hy_ne, h_in⟩)
          exact (h_reach y hy_T hy_not_rem hy_cur).tail h_edge_ne
      · -- `x` was already visited: the walk closes a cycle.
        exfalso
        have h_x_reaches_cur : Relation.TransGen (loOnNe C T) x cur :=
          h_reach x hx_T hx_rem hx_ne
        exact loOnNe_acyclic hVC h_vis_trans h_vis_irrefl h_in_C x
          (h_x_reaches_cur.tail h_edge_ne)
    · -- `cur` has no outgoing edge: it is maximal.
      push_neg at h_max
      exact ⟨cur, h_cur, fun x hx hx_ne h_lo =>
        (h_max x hx hx_ne) h_lo⟩

/-- **Every finite set has a `loOn`-respecting enumeration.**
Peel a `loOn`-maximal element, enumerate the rest recursively, append
the maximal element at the tail. -/
theorem exists_loOn_respecting_perm [HistoricalBinaryMerge D]
    (hVC : BinaryMergeLaws D)
    {C : ReplayContext D}
    (h_vis_trans : ∀ {a b c : Op D.AppOp},
       C.vis a b → C.vis b c → C.vis a c)
    (h_vis_irrefl : ∀ a : Op D.AppOp, ¬ C.vis a a)
    {T : Set (Op D.AppOp)} {l : List (Op D.AppOp)}
    (h_l : listPermOf l T)
    (h_in_C : ∀ a ∈ T, a ∈ C.events) :
    ∃ ρ : List (Op D.AppOp),
      listPermOf ρ T ∧ respects ρ (loOn C T) := by
  suffices gen : ∀ n (T : Set (Op D.AppOp)) (l : List (Op D.AppOp)),
      l.length = n → listPermOf l T → (∀ a ∈ T, a ∈ C.events) →
      ∃ ρ, listPermOf ρ T ∧ respects ρ (loOn C T) by
    exact gen _ T l rfl h_l h_in_C
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T l h_len h_perm h_in_C
    rcases Set.eq_empty_or_nonempty T with rfl | h_ne
    · exact ⟨[], ⟨List.nodup_nil, fun a => by simp⟩, List.Pairwise.nil⟩
    · obtain ⟨m, hm, h_max⟩ :=
        exists_loOn_maximal hVC h_vis_trans h_vis_irrefl h_perm
          h_in_C h_ne
      have hm_in_l : m ∈ l := (h_perm.2 m).mpr hm
      -- Enumerate `T \ {m}` by `l.erase m`.
      have h_perm' : listPermOf (l.erase m) (T \ {m}) := by
        refine ⟨h_perm.1.erase m, fun a => ?_⟩
        rw [h_perm.1.mem_erase_iff]
        constructor
        · rintro ⟨hne, ha⟩
          exact ⟨(h_perm.2 a).mp ha, hne⟩
        · rintro ⟨ha, hne⟩
          exact ⟨hne, (h_perm.2 a).mpr ha⟩
      have h_len' : (l.erase m).length < n := by
        have h_pos : 0 < l.length := List.length_pos_of_mem hm_in_l
        rw [List.length_erase_of_mem hm_in_l]
        omega
      obtain ⟨ρ', hρ'_perm, hρ'_resp⟩ :=
        ih _ h_len' (T \ {m}) (l.erase m) rfl h_perm'
          (fun a ha => h_in_C a ha.1)
      have hm_not_ρ' : m ∉ ρ' := fun h =>
        ((hρ'_perm.2 m).mp h).2 rfl
      refine ⟨ρ' ++ [m], ⟨?_, fun a => ?_⟩, ?_⟩
      · rw [List.nodup_append]
        refine ⟨hρ'_perm.1, List.nodup_singleton _, ?_⟩
        intro x hx y hy
        rw [List.mem_singleton] at hy; subst hy
        intro heq; subst heq
        exact hm_not_ρ' hx
      · rw [List.mem_append, List.mem_singleton]
        constructor
        · rintro (h | rfl)
          · exact ((hρ'_perm.2 a).mp h).1
          · exact hm
        · intro ha
          by_cases hae : a = m
          · exact Or.inr hae
          · exact Or.inl ((hρ'_perm.2 a).mpr ⟨ha, hae⟩)
      · unfold respects
        rw [List.pairwise_append]
        refine ⟨respects_loOn_mono (fun a ha => ha.1) hρ'_resp,
          List.pairwise_singleton _ _, ?_⟩
        intro y hy b hb
        rw [List.mem_singleton] at hb; subst hb
        obtain ⟨hy_T, hy_ne⟩ := (hρ'_perm.2 y).mp hy
        exact h_max y hy_T hy_ne

/-! ### 3. Swap and bubble machinery re-targeted at `loOn`

Identical in structure to `applySeq_swap_lo_incomparable` /
`applySeq_bubble_to_front`; only the relation whose first disjunct is
used in the same-replica case changes from `lo C` to `loOn C ev`. -/

/-- Swap adjacent `loOn`-incomparable events (Path 1 version). -/
theorem applySeq_swap_loOn_incomparable
    [HistoricalBinaryMerge D]
    (hVC : BinaryMergeLaws D) {C : ReplayContext D}
    {ev : Set (Op D.AppOp)}
    {a b : Op D.AppOp} (h_ne : a ≠ b)
    (h_a_in_C : a ∈ C.events) (h_b_in_C : b ∈ C.events)
    (h_not_lo_ab : ¬ loOn C ev a b) (h_not_lo_ba : ¬ loOn C ev b a)
    (pfx sfx : List (Op D.AppOp)) (s : D.State)
    (h_ov : ¬ D.commutes a b → a.rep ≠ b.rep →
      ∃ e₃ α β, sfx = α ++ e₃ :: β ∧
                distinctOps a e₃ ∧ distinctOps b e₃ ∧
                ((D.replayOrder a b = RcRes.Fst_then_snd ∧
                  ¬ D.commutes b e₃) ∨
                 (D.replayOrder b a = RcRes.Fst_then_snd ∧
                  ¬ D.commutes a e₃))) :
    applySeq D s (pfx ++ a :: b :: sfx)
    = applySeq D s (pfx ++ b :: a :: sfx) := by
  by_cases h_comm : D.commutes a b
  · exact applySeq_swap_commute_basic h_comm pfx sfx s
  · obtain ⟨_, _, hL_a, h_a_in_s⟩ := h_a_in_C
    obtain ⟨_, _, hL_b, h_b_in_s⟩ := h_b_in_C
    by_cases h_same : a.rep = b.rep
    · exfalso
      have h_vis :=
        C.vis_total_same_replica hL_a h_a_in_s hL_b h_b_in_s h_ne h_same
      rcases h_vis with hvab | hvba
      · exact h_not_lo_ab (Or.inl ⟨hvab, h_comm⟩)
      · have h_comm_ba : ¬ D.commutes b a :=
          fun h => h_comm (fun s => (h s).symm)
        exact h_not_lo_ba (Or.inl ⟨hvba, h_comm_ba⟩)
    · have h_dist_ab : distinctOps a b :=
        C.timestamps_distinct hL_a h_a_in_s hL_b h_b_in_s h_ne
      obtain ⟨e₃, α, β, h_sfx, h_dae, h_dbe, h_case⟩ := h_ov h_comm h_same
      subst h_sfx
      rcases h_case with ⟨h_rc_ab, h_nc_be⟩ | ⟨h_rc_ba, h_nc_ae⟩
      · exact applySeq_swap_via_cond_comm_lift_core hVC h_dist_ab h_dbe h_dae
          h_rc_ab h_nc_be pfx α β s
      · have h_dist_ba : distinctOps b a := Ne.symm h_dist_ab
        exact (applySeq_swap_via_cond_comm_lift_core hVC h_dist_ba h_dae h_dbe
          h_rc_ba h_nc_ae pfx α β s).symm

/-- Bubble a `loOn`-minimal event to the front of a list (with tail). -/
theorem applySeq_bubble_to_front_loOn
    [HistoricalBinaryMerge D]
    (hVC : BinaryMergeLaws D) {C : ReplayContext D}
    {ev : Set (Op D.AppOp)}
    (e : Op D.AppOp) (σ tail : List (Op D.AppOp))
    (h_e_in_C : e ∈ C.events)
    (h_σ_in_C : ∀ y ∈ σ, y ∈ C.events)
    (h_e_notin : e ∉ σ)
    (h_not_lo_fwd : ∀ y ∈ σ, ¬ loOn C ev e y)
    (h_not_lo_bwd : ∀ y ∈ σ, ¬ loOn C ev y e)
    (h_ov : ∀ α β y, σ = α ++ y :: β →
      ¬ D.commutes y e → y.rep ≠ e.rep →
      ∃ e₃ α' β', β ++ tail = α' ++ e₃ :: β' ∧
                  distinctOps y e₃ ∧ distinctOps e e₃ ∧
                  ((D.replayOrder y e = RcRes.Fst_then_snd ∧
                    ¬ D.commutes e e₃) ∨
                   (D.replayOrder e y = RcRes.Fst_then_snd ∧
                    ¬ D.commutes y e₃)))
    (s : D.State) :
    applySeq D s (σ ++ e :: tail) = applySeq D s (e :: σ ++ tail) := by
  induction σ generalizing s with
  | nil => rfl
  | cons y σ' ih =>
    have h_y_in : y ∈ y :: σ' := List.mem_cons_self
    have h_y_ne : y ≠ e := fun heq => h_e_notin (heq ▸ h_y_in)
    have h_y_in_C := h_σ_in_C y h_y_in
    have hih : applySeq D (D.update s y) (σ' ++ e :: tail)
             = applySeq D (D.update s y) (e :: σ' ++ tail) :=
      ih (fun z hz => h_σ_in_C z (List.mem_cons_of_mem _ hz))
         (fun h => h_e_notin (List.mem_cons_of_mem _ h))
         (fun z hz => h_not_lo_fwd z (List.mem_cons_of_mem _ hz))
         (fun z hz => h_not_lo_bwd z (List.mem_cons_of_mem _ hz))
         (fun α β z h_eq h_nc h_diff =>
            h_ov (y :: α) β z (by rw [h_eq]; rfl) h_nc h_diff)
         (D.update s y)
    have hswap : applySeq D s (y :: e :: σ' ++ tail)
               = applySeq D s (e :: y :: σ' ++ tail) := by
      have := applySeq_swap_loOn_incomparable (D := D) (ev := ev)
        hVC h_y_ne h_y_in_C h_e_in_C
        (h_not_lo_bwd y h_y_in) (h_not_lo_fwd y h_y_in)
        [] (σ' ++ tail) s
        (fun h_nc h_diff => h_ov [] σ' y rfl h_nc h_diff)
      simpa using this
    show applySeq D (D.update s y) (σ' ++ e :: tail)
         = applySeq D s (e :: y :: σ' ++ tail)
    rw [hih]
    show applySeq D s (y :: e :: σ' ++ tail)
         = applySeq D s (e :: y :: σ' ++ tail)
    exact hswap

/-! ### 4. Convergence w.r.t. `loOn`: no closure hypotheses

The replacement for the false "convergence over backward-closed
replica sets": any two `loOn C ev`-respecting permutations of `ev`
fold to the same state. The overwriters demanded by the swap
machinery are supplied by the *failed* `loOn`-edges themselves, a
missing rc-edge means an absorber exists **inside `ev`**, so no
forward/overwriter closure is assumed.

The internal induction peels the head of `π₁` (a `loOn`-minimal
event) and recurses on a shrunken set `evC ⊆ ev` while keeping the
relation pinned at `loOn C ev`. The invariant `h_abs` records that
`ev`-absorbers of surviving events survive: it holds trivially at
`evC = ev` and is preserved because a peeled head is `loOn`-minimal,
so it absorbs nothing that remains. -/
theorem convergence_on
    [HistoricalBinaryMerge D]
    (hVC : BinaryMergeLaws D) {C : ReplayContext D}
    (s : D.State) {π₁ π₂ : List (Op D.AppOp)} {ev : Set (Op D.AppOp)}
    (h_ev_in_C : ∀ a ∈ ev, a ∈ C.events)
    (h₁_perm : listPermOf π₁ ev) (h₂_perm : listPermOf π₂ ev)
    (h₁_resp : respects π₁ (loOn C ev))
    (h₂_resp : respects π₂ (loOn C ev)) :
    applySeq D s π₁ = applySeq D s π₂ := by
  suffices gen : ∀ n (s : D.State) (evC : Set (Op D.AppOp))
                   (π₁ π₂ : List (Op D.AppOp)),
      π₁.length = n →
      (∀ a ∈ evC, a ∈ C.events) →
      (∀ x ∈ evC, ∀ z ∈ ev, C.vis x z → ¬ D.commutes x z → z ∈ evC) →
      listPermOf π₁ evC → listPermOf π₂ evC →
      respects π₁ (loOn C ev) → respects π₂ (loOn C ev) →
      applySeq D s π₁ = applySeq D s π₂ by
    exact gen _ s ev π₁ π₂ rfl h_ev_in_C
      (fun x _ z hz _ _ => hz) h₁_perm h₂_perm h₁_resp h₂_resp
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s evC π₁ π₂ h_len h_evC_in_C h_abs h₁p h₂p h₁r h₂r
    match π₁, h_len, h₁p, h₁r with
    | [], _, h₁p, _ =>
      obtain ⟨_, hm₁⟩ := h₁p
      have hev_empty : evC = ∅ := by
        ext a
        exact ⟨fun ha => absurd ((hm₁ a).mpr ha) List.not_mem_nil,
               fun ha => ha.elim⟩
      subst hev_empty
      obtain ⟨_, hm₂⟩ := h₂p
      have hπ₂_nil : π₂ = [] := by
        match π₂, hm₂ with
        | [], _ => rfl
        | x :: _, hm₂ =>
          exact absurd ((hm₂ x).mp List.mem_cons_self) id
      subst hπ₂_nil
      rfl
    | e :: π₁', h_len, h₁p, h₁r =>
      obtain ⟨hnd₁, hmem₁⟩ := h₁p
      obtain ⟨hnd₂, hmem₂⟩ := h₂p
      have he_in_ev : e ∈ evC := (hmem₁ e).mp List.mem_cons_self
      have he_in_π₂ : e ∈ π₂ := (hmem₂ e).mpr he_in_ev
      obtain ⟨σ, τ, hπ₂_split⟩ := List.append_of_mem he_in_π₂
      subst hπ₂_split
      rw [List.nodup_cons] at hnd₁
      have he_notin_π₁' : e ∉ π₁' := hnd₁.1
      rw [List.nodup_append, List.nodup_cons] at hnd₂
      have he_notin_σ : e ∉ σ := fun h =>
        hnd₂.2.2 e h e (by simp) rfl
      have he_notin_τ : e ∉ τ := hnd₂.2.1.1
      have hστ_nodup : (σ ++ τ).Nodup := by
        rw [List.nodup_append]
        refine ⟨hnd₂.1, hnd₂.2.1.2, ?_⟩
        intro a ha b hb
        exact hnd₂.2.2 a ha b (List.mem_cons_of_mem _ hb)
      have he_in_C : e ∈ C.events := h_evC_in_C e he_in_ev
      -- e is loOn-min in evC: ∀ z ∈ evC \ {e}, ¬ loOn C ev z e.
      have h_e_lo_min : ∀ z ∈ evC, z ≠ e → ¬ loOn C ev z e := by
        intro z hz hz_ne
        have hz_in_π₁ : z ∈ e :: π₁' := (hmem₁ z).mpr hz
        have hz_in_π₁' : z ∈ π₁' := by
          rcases List.mem_cons.mp hz_in_π₁ with h | h
          · exact absurd h hz_ne
          · exact h
        exact (List.pairwise_cons.mp h₁r).1 z hz_in_π₁'
      -- Bubble e to the front of π₂: σ ++ e :: τ → e :: σ ++ τ.
      have hbubble : applySeq D s (σ ++ e :: τ)
                   = applySeq D s (e :: σ ++ τ) := by
        have h_σ_sub_ev : ∀ y ∈ σ, y ∈ evC := fun y hy =>
          (hmem₂ y).mp (List.mem_append.mpr (Or.inl hy))
        have h_σ_in_C : ∀ y ∈ σ, y ∈ C.events :=
          fun y hy => h_evC_in_C y (h_σ_sub_ev y hy)
        have h_τ_sub_ev : ∀ x ∈ τ, x ∈ evC := fun x hx =>
          (hmem₂ x).mp (List.mem_append.mpr (Or.inr
            (List.mem_cons_of_mem _ hx)))
        have h_not_lo_fwd : ∀ y ∈ σ, ¬ loOn C ev e y := by
          intro y hy
          have h2 := List.pairwise_append.mp h₂r
          exact h2.2.2 y hy e List.mem_cons_self
        have h_not_lo_bwd : ∀ y ∈ σ, ¬ loOn C ev y e := by
          intro y hy
          have hy_ne_e : y ≠ e := fun h => he_notin_σ (h ▸ hy)
          exact h_e_lo_min y (h_σ_sub_ev y hy) hy_ne_e
        -- Discharge h_ov: the failed loOn-edge supplies an absorber
        -- inside ev; h_abs pulls it into evC; the respects facts
        -- place it after the swap point.
        have h_ov : ∀ α β y, σ = α ++ y :: β →
            ¬ D.commutes y e → y.rep ≠ e.rep →
            ∃ e₃ α' β', β ++ τ = α' ++ e₃ :: β' ∧
                        distinctOps y e₃ ∧ distinctOps e e₃ ∧
                        ((D.replayOrder y e = RcRes.Fst_then_snd ∧
                          ¬ D.commutes e e₃) ∨
                         (D.replayOrder e y = RcRes.Fst_then_snd ∧
                          ¬ D.commutes y e₃)) := by
          intro α β y h_σ_eq h_nc h_diff_rep
          subst h_σ_eq
          have hy_in_σ : y ∈ α ++ y :: β :=
            List.mem_append.mpr (Or.inr List.mem_cons_self)
          have hy_in_ev : y ∈ evC := h_σ_sub_ev y hy_in_σ
          have hy_in_C : y ∈ C.events := h_evC_in_C y hy_in_ev
          have hy_ne_e : y ≠ e := fun h => he_notin_σ (h ▸ hy_in_σ)
          have h_dist_ye : distinctOps y e :=
            distinctOps_of_events hy_in_C he_in_C hy_ne_e
          have h_not_lo_ye : ¬ loOn C ev y e := h_not_lo_bwd y hy_in_σ
          have h_not_lo_ey : ¬ loOn C ev e y := h_not_lo_fwd y hy_in_σ
          have h_rc_disj :=
            (hVC.rc_non_comm_directional y e h_dist_ye).mp h_nc
          rcases h_rc_disj with h_rc_ye | h_rc_ey
          · -- Case rc(y, e) = Fst. The failed edge `loOn ev y e`
            -- yields an absorber of e inside ev.
            have h_not_vis_ye : ¬ C.vis y e := fun hv =>
              h_not_lo_ye (Or.inl ⟨hv, h_nc⟩)
            have h_not_vis_ey : ¬ C.vis e y := by
              intro hv
              have h_nc_ey : ¬ D.commutes e y :=
                fun h => h_nc (fun s => (h s).symm)
              exact h_not_lo_ey (Or.inl ⟨hv, h_nc_ey⟩)
            have h_overwriter_e :
                ∃ e₃ ∈ ev, C.vis e e₃ ∧ ¬ D.commutes e e₃ := by
              by_contra h_no_ow
              exact h_not_lo_ye
                (Or.inr ⟨h_not_vis_ye, h_not_vis_ey, h_rc_ye, h_no_ow⟩)
            obtain ⟨e₃, h_e₃_ev, h_vis_ee₃, h_nc_ee₃⟩ := h_overwriter_e
            have h_e₃_in_evC : e₃ ∈ evC :=
              h_abs e he_in_ev e₃ h_e₃_ev h_vis_ee₃ h_nc_ee₃
            have h_e₃_in_π₂ : e₃ ∈ (α ++ y :: β) ++ e :: τ :=
              (hmem₂ e₃).mpr h_e₃_in_evC
            have h_lo_ee₃ : loOn C ev e e₃ := Or.inl ⟨h_vis_ee₃, h_nc_ee₃⟩
            have h_e₃_in_τ : e₃ ∈ τ := by
              rcases List.mem_append.mp h_e₃_in_π₂ with h | h
              · exfalso
                have hresp_pair := List.pairwise_append.mp h₂r
                exact hresp_pair.2.2 e₃ h e List.mem_cons_self h_lo_ee₃
              · rcases List.mem_cons.mp h with h_eq | h_τ
                · exact absurd h_eq.symm
                    (fun h_eq2 => h_nc_ee₃ (fun s => by rw [h_eq2]))
                · exact h_τ
            have h_e₃_ne_y : e₃ ≠ y := by
              intro h_eq
              rw [h_eq] at h_e₃_in_τ
              exact hnd₂.2.2 y
                (List.mem_append.mpr (Or.inr List.mem_cons_self)) y
                (List.mem_cons_of_mem _ h_e₃_in_τ) rfl
            have h_e₃_ne_e : e₃ ≠ e := by
              intro h_eq
              rw [h_eq] at h_e₃_in_τ
              exact he_notin_τ h_e₃_in_τ
            obtain ⟨τ_a, τ_b, hτ_split⟩ := List.append_of_mem h_e₃_in_τ
            have h_e₃_in_C : e₃ ∈ C.events := h_ev_in_C e₃ h_e₃_ev
            have h_dist_ye₃ : distinctOps y e₃ :=
              distinctOps_of_events hy_in_C h_e₃_in_C
                (fun h => h_e₃_ne_y h.symm)
            have h_dist_ee₃ : distinctOps e e₃ :=
              distinctOps_of_events he_in_C h_e₃_in_C
                (fun h => h_e₃_ne_e h.symm)
            refine ⟨e₃, β ++ τ_a, τ_b, ?_, h_dist_ye₃, h_dist_ee₃,
                    Or.inl ⟨h_rc_ye, h_nc_ee₃⟩⟩
            rw [hτ_split, List.append_assoc]
          · -- Case rc(e, y) = Fst. Absorber of y inside ev.
            have h_not_vis_ey : ¬ C.vis e y := fun hv =>
              h_not_lo_ey (Or.inl ⟨hv, fun h => h_nc (fun s => (h s).symm)⟩)
            have h_not_vis_ye : ¬ C.vis y e := fun hv =>
              h_not_lo_ye (Or.inl ⟨hv, h_nc⟩)
            have h_overwriter_y :
                ∃ e₃ ∈ ev, C.vis y e₃ ∧ ¬ D.commutes y e₃ := by
              by_contra h_no_ow
              exact h_not_lo_ey
                (Or.inr ⟨h_not_vis_ey, h_not_vis_ye, h_rc_ey, h_no_ow⟩)
            obtain ⟨e₃, h_e₃_ev, h_vis_ye₃, h_nc_ye₃⟩ := h_overwriter_y
            have h_e₃_in_evC : e₃ ∈ evC :=
              h_abs y hy_in_ev e₃ h_e₃_ev h_vis_ye₃ h_nc_ye₃
            have h_e₃_in_π₂ : e₃ ∈ (α ++ y :: β) ++ e :: τ :=
              (hmem₂ e₃).mpr h_e₃_in_evC
            have h_lo_ye₃ : loOn C ev y e₃ := Or.inl ⟨h_vis_ye₃, h_nc_ye₃⟩
            have h_e₃_ne_e : e₃ ≠ e := fun h_eq => by
              subst h_eq; exact h_not_lo_ye h_lo_ye₃
            have h_e₃_ne_y : e₃ ≠ y := fun h_eq => by
              subst h_eq
              exact h_nc_ye₃ (fun _ => rfl)
            have h_e₃_in_C : e₃ ∈ C.events := h_ev_in_C e₃ h_e₃_ev
            have h_dist_ye₃ : distinctOps y e₃ :=
              distinctOps_of_events hy_in_C h_e₃_in_C
                (fun h => h_e₃_ne_y h.symm)
            have h_dist_ee₃ : distinctOps e e₃ :=
              distinctOps_of_events he_in_C h_e₃_in_C
                (fun h => h_e₃_ne_e h.symm)
            have h_e₃_in_βτ : e₃ ∈ β ++ τ := by
              rcases List.mem_append.mp h_e₃_in_π₂ with h | h
              · rcases List.mem_append.mp h with h_α | h_yβ
                · exfalso
                  rw [respects, List.pairwise_append] at h₂r
                  obtain ⟨h_resp_left, _, _⟩ := h₂r
                  rw [List.pairwise_append] at h_resp_left
                  obtain ⟨_, _, h_cross⟩ := h_resp_left
                  exact h_cross e₃ h_α y List.mem_cons_self h_lo_ye₃
                · rcases List.mem_cons.mp h_yβ with h_eq | h_β
                  · exact absurd h_eq h_e₃_ne_y
                  · exact List.mem_append.mpr (Or.inl h_β)
              · rcases List.mem_cons.mp h with h_eq | h_τ
                · exact absurd h_eq h_e₃_ne_e
                · exact List.mem_append.mpr (Or.inr h_τ)
            obtain ⟨γ_a, γ_b, hγ_split⟩ := List.append_of_mem h_e₃_in_βτ
            exact ⟨e₃, γ_a, γ_b, hγ_split, h_dist_ye₃, h_dist_ee₃,
                    Or.inr ⟨h_rc_ey, h_nc_ye₃⟩⟩
        exact applySeq_bubble_to_front_loOn (D := D) (ev := ev) hVC e σ τ
          he_in_C h_σ_in_C he_notin_σ h_not_lo_fwd h_not_lo_bwd h_ov s
      -- Peel e from both sides and recurse on evC \ {e}.
      have h_len_new : π₁'.length < n := by
        simp only [List.length_cons] at h_len; omega
      have h_evC'_in_C : ∀ a ∈ evC \ {e}, a ∈ C.events :=
        fun a ha => h_evC_in_C a ha.1
      have h_abs' : ∀ x ∈ evC \ {e}, ∀ z ∈ ev,
          C.vis x z → ¬ D.commutes x z → z ∈ evC \ {e} := by
        intro x hx z hz hv hnc
        refine ⟨h_abs x hx.1 z hz hv hnc, ?_⟩
        intro hz_eq
        have hz_eq' : z = e := hz_eq
        rw [hz_eq'] at hv hnc
        have hlo_xe : loOn C ev x e := Or.inl ⟨hv, hnc⟩
        exact h_e_lo_min x hx.1 hx.2 hlo_xe
      have hp₁' : listPermOf π₁' (evC \ {e}) := by
        refine ⟨hnd₁.2, fun a => ?_⟩
        simp only [Set.mem_diff, Set.mem_singleton_iff]
        constructor
        · intro ha
          refine ⟨(hmem₁ a).mp (List.mem_cons_of_mem _ ha), ?_⟩
          intro h_eq; subst h_eq; exact he_notin_π₁' ha
        · rintro ⟨hae, hne⟩
          rcases List.mem_cons.mp ((hmem₁ a).mpr hae) with h | h
          · exact absurd h hne
          · exact h
      have hpστ : listPermOf (σ ++ τ) (evC \ {e}) := by
        refine ⟨hστ_nodup, fun a => ?_⟩
        simp only [Set.mem_diff, Set.mem_singleton_iff, List.mem_append]
        constructor
        · rintro (ha | ha)
          · refine ⟨(hmem₂ a).mp (List.mem_append.mpr (Or.inl ha)), ?_⟩
            intro rfl; exact he_notin_σ ha
          · refine ⟨(hmem₂ a).mp
              (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ ha))), ?_⟩
            intro rfl; exact he_notin_τ ha
        · rintro ⟨hae, hne⟩
          rcases List.mem_append.mp ((hmem₂ a).mpr hae) with h | h
          · exact Or.inl h
          · rcases List.mem_cons.mp h with h' | h'
            · exact absurd h' hne
            · exact Or.inr h'
      have hr₁' : respects π₁' (loOn C ev) := (List.pairwise_cons.mp h₁r).2
      have hrστ : respects (σ ++ τ) (loOn C ev) := by
        have h2split := List.pairwise_append.mp h₂r
        rw [List.pairwise_cons] at h2split
        obtain ⟨hσ, ⟨_, hτ⟩, hcross⟩ := h2split
        rw [respects, List.pairwise_append]
        refine ⟨hσ, hτ, ?_⟩
        intro a ha b hb
        exact hcross a ha b (List.mem_cons_of_mem _ hb)
      rw [hbubble]
      show applySeq D (D.update s e) π₁' = applySeq D (D.update s e) (σ ++ τ)
      exact ih _ h_len_new (D.update s e) (evC \ {e}) π₁' (σ ++ τ) rfl
        h_evC'_in_C h_abs' hp₁' hpστ hr₁' hrστ

/-! ### 5. Re-permutation and normalization -/

/-- Re-permute `π` to end in a chosen `loOn`-maximal element `e`,
preserving `loOn`-respect and the folded state (via
`convergence_on`, no closure hypotheses needed). -/
theorem perm_ending_in_loOn_max
    [HistoricalBinaryMerge D]
    (hVC : BinaryMergeLaws D) {C : ReplayContext D}
    {ev : Set (Op D.AppOp)} {π : List (Op D.AppOp)} {e : Op D.AppOp}
    (h_ev_in_C : ∀ a ∈ ev, a ∈ C.events)
    (h_perm : listPermOf π ev) (h_resp : respects π (loOn C ev))
    (h_e_in_ev : e ∈ ev)
    (h_e_lo_max : ∀ x ∈ ev, x ≠ e → ¬ loOn C ev e x) :
    listPermOf ((π.filter (· ≠ e)) ++ [e]) ev ∧
    respects ((π.filter (· ≠ e)) ++ [e]) (loOn C ev) ∧
    ∀ s : D.State,
      applySeq D s π = applySeq D s ((π.filter (· ≠ e)) ++ [e]) := by
  have h_e_in_π : e ∈ π := (h_perm.2 e).mpr h_e_in_ev
  have hfilt_perm : listPermOf (π.filter (· ≠ e)) (ev \ {e}) :=
    filter_ne_listPermOf_basic h_perm h_e_in_π
  have hfilt_resp : respects (π.filter (· ≠ e)) (loOn C ev) :=
    filter_ne_respects' h_resp
  have h_perm' : listPermOf ((π.filter (· ≠ e)) ++ [e]) ev := by
    refine ⟨?_, fun a => ?_⟩
    · rw [List.nodup_append]
      refine ⟨hfilt_perm.1, List.nodup_singleton _, ?_⟩
      intro x hx y hy heq
      rw [List.mem_singleton] at hy; subst y; subst heq
      exact (hfilt_perm.2 x).mp hx |>.2 rfl
    · rw [List.mem_append, List.mem_singleton]
      constructor
      · rintro (h | rfl)
        · exact ((hfilt_perm.2 a).mp h).1
        · exact h_e_in_ev
      · intro ha
        by_cases hae : a = e
        · exact Or.inr hae
        · exact Or.inl ((hfilt_perm.2 a).mpr ⟨ha, hae⟩)
  have h_resp' : respects ((π.filter (· ≠ e)) ++ [e]) (loOn C ev) := by
    unfold respects
    rw [List.pairwise_append]
    refine ⟨hfilt_resp, List.pairwise_singleton _ _, ?_⟩
    intro y hy b hb
    rw [List.mem_singleton] at hb; subst b
    have ⟨hy_in_ev, hy_ne⟩ := (hfilt_perm.2 y).mp hy
    exact h_e_lo_max y hy_in_ev hy_ne
  exact ⟨h_perm', h_resp', fun s =>
    convergence_on hVC s h_ev_in_C h_perm h_perm' h_resp h_resp'⟩

/-- **Normalization after a tail peel.** Given a witness `ρ ++ [t]`
of `ev` respecting `loOn C ev`, produce a front `ρ'` for `ev \ {t}`
that respects the *shrunken-set* relation `loOn C (ev \ {t})`, the
relation gains rc-edges whose only `ev`-absorber was `t` itself, so
`ρ` need not respect it, while preserving the fold of the full
list. Fold preservation: both `ρ ++ [t]` and `ρ' ++ [t]` respect
`loOn C ev` and enumerate `ev`, so `convergence_on` applies; the
lost absorber `t` sits at the tail, absorbing exactly the swaps the
re-sort performs. -/
theorem normalize_peel_tail
    [HistoricalBinaryMerge D]
    (hVC : BinaryMergeLaws D) {C : ReplayContext D}
    (h_vis_trans : ∀ {a b c : Op D.AppOp},
       C.vis a b → C.vis b c → C.vis a c)
    (h_vis_irrefl : ∀ a : Op D.AppOp, ¬ C.vis a a)
    {ev : Set (Op D.AppOp)} {ρ : List (Op D.AppOp)} {t : Op D.AppOp}
    (h_ev_in_C : ∀ a ∈ ev, a ∈ C.events)
    (h_perm : listPermOf (ρ ++ [t]) ev)
    (h_resp : respects (ρ ++ [t]) (loOn C ev)) :
    ∃ ρ' : List (Op D.AppOp),
      listPermOf ρ' (ev \ {t}) ∧
      respects ρ' (loOn C (ev \ {t})) ∧
      ∀ s : D.State,
        applySeq D s (ρ' ++ [t]) = applySeq D s (ρ ++ [t]) := by
  have h_t_in_ev : t ∈ ev :=
    (h_perm.2 t).mp (List.mem_append.mpr (Or.inr (by simp)))
  have h_t_notin_ρ : t ∉ ρ := by
    intro h
    have hnd := List.nodup_append.mp h_perm.1
    exact hnd.2.2 t h t (by simp) rfl
  have h_ρ_perm : listPermOf ρ (ev \ {t}) := by
    refine ⟨(List.nodup_append.mp h_perm.1).1, fun a => ?_⟩
    simp only [Set.mem_diff, Set.mem_singleton_iff]
    constructor
    · intro ha
      refine ⟨(h_perm.2 a).mp (List.mem_append.mpr (Or.inl ha)), ?_⟩
      intro h_eq; subst h_eq; exact h_t_notin_ρ ha
    · rintro ⟨ha, hne⟩
      rcases List.mem_append.mp ((h_perm.2 a).mpr ha) with h | h
      · exact h
      · rw [List.mem_singleton] at h; exact absurd h hne
  -- Re-sort the front against the shrunken-set relation.
  obtain ⟨ρ', hρ'_perm, hρ'_resp⟩ :=
    exists_loOn_respecting_perm hVC h_vis_trans h_vis_irrefl h_ρ_perm
      (fun a ha => h_ev_in_C a ha.1)
  refine ⟨ρ', hρ'_perm, hρ'_resp, fun s => ?_⟩
  -- Both full lists respect `loOn C ev` and enumerate `ev`.
  have h_t_max : ∀ x ∈ ρ, ¬ loOn C ev t x := last_is_maximal h_resp
  have h_perm' : listPermOf (ρ' ++ [t]) ev := by
    refine ⟨?_, fun a => ?_⟩
    · rw [List.nodup_append]
      refine ⟨hρ'_perm.1, List.nodup_singleton _, ?_⟩
      intro x hx y hy heq
      rw [List.mem_singleton] at hy; subst y; subst heq
      exact ((hρ'_perm.2 x).mp hx).2 rfl
    · rw [List.mem_append, List.mem_singleton]
      constructor
      · rintro (h | rfl)
        · exact ((hρ'_perm.2 a).mp h).1
        · exact h_t_in_ev
      · intro ha
        by_cases hae : a = t
        · exact Or.inr hae
        · exact Or.inl ((hρ'_perm.2 a).mpr ⟨ha, hae⟩)
  have h_resp' : respects (ρ' ++ [t]) (loOn C ev) := by
    unfold respects
    rw [List.pairwise_append]
    refine ⟨respects_loOn_mono (fun a ha => ha.1) hρ'_resp,
      List.pairwise_singleton _ _, ?_⟩
    intro y hy b hb
    rw [List.mem_singleton] at hb; subst b
    have hy_ρ : y ∈ ρ := by
      have := (hρ'_perm.2 y).mp hy
      exact (h_ρ_perm.2 y).mpr this
    exact h_t_max y hy_ρ
  exact convergence_on hVC s h_ev_in_C h_perm' h_perm h_resp' h_resp

/-! ### 6. Canonical states and the Join Lemma

`convergence_on` makes every finite event set `ev` denote a unique
state: the fold of *any* `loOn C ev`-respecting enumeration. This
reformulates the whole metatheorem: the strengthened canonical-state invariant
is "every replica's state is the canonical state of its event set",
the Apply case is `isCanonicalState_extend`, and the Merge case
reduces to a single state-level statement, the **Join Lemma**:

    IsCanonicalState ev₁ s₁ → IsCanonicalState ev₂ s₂ →
    IsCanonicalState (ev₁ ∪ ev₂) (merge s₁ s₂)

for backward-closed `ev₁, ev₂`. Witness lists disappear from the
induction entirely; `isCanonicalState_peel` (below) is the
engine that avoids the unsound side-witness re-permutation of the
paper. The Join Lemma itself is the open obligation: its peel step
is *true* under `loOn`-maximality + backward closure but not
expressible as an unconditional per-CRDT VC. -/

/-- `s` is the canonical state of `ev`: the fold of some (hence, by
`convergence_on`, of every) `loOn C ev`-respecting enumeration. -/
def IsCanonicalState (C : ReplayContext D) (ev : Set (Op D.AppOp))
    (s : D.State) : Prop :=
  ∃ ρ : List (Op D.AppOp),
    listPermOf ρ ev ∧ respects ρ (loOn C ev) ∧
    applySeq D D.init ρ = s

/-- `loOn` is local to its event set: replay contexts agreeing on visibility
over `E × E` induce the same canonical states of `E`. -/
theorem isCanonicalState_congr {C C' : ReplayContext D}
    {E : Set (Op D.AppOp)} {s : D.State}
    (h_vis : ∀ a ∈ E, ∀ b ∈ E, (C'.vis a b ↔ C.vis a b))
    (h : IsCanonicalState C E s) : IsCanonicalState C' E s := by
  obtain ⟨ρ, hp, hr, hf⟩ := h
  refine ⟨ρ, hp, ?_, hf⟩
  refine hr.imp_of_mem ?_
  intro a b ha hb hn h_lo
  have ha_E : a ∈ E := (hp.2 a).mp ha
  have hb_E : b ∈ E := (hp.2 b).mp hb
  apply hn
  rcases h_lo with ⟨hv, hnc⟩ | ⟨h1, h2, h3, h4⟩
  · exact Or.inl ⟨(h_vis b hb_E a ha_E).mp hv, hnc⟩
  · refine Or.inr ⟨fun hv => h1 ((h_vis b hb_E a ha_E).mpr hv),
      fun hv => h2 ((h_vis a ha_E b hb_E).mpr hv), h3, ?_⟩
    rintro ⟨e₃, he₃, hv, hnc⟩
    exact h4 ⟨e₃, he₃, (h_vis a ha_E e₃ he₃).mpr hv, hnc⟩

/-- Canonical states are unique. -/
theorem isCanonicalState_unique [HistoricalBinaryMerge D]
    (hVC : BinaryMergeLaws D)
    {C : ReplayContext D} {ev : Set (Op D.AppOp)} {s s' : D.State}
    (h_ev_in_C : ∀ a ∈ ev, a ∈ C.events)
    (h : IsCanonicalState C ev s) (h' : IsCanonicalState C ev s') :
    s = s' := by
  obtain ⟨ρ, hp, hr, hs⟩ := h
  obtain ⟨ρ', hp', hr', hs'⟩ := h'
  rw [← hs, ← hs']
  exact convergence_on hVC D.init h_ev_in_C hp hp' hr hr'

/-- Canonical states exist for every finite set. -/
theorem isCanonicalState_exists [HistoricalBinaryMerge D]
    (hVC : BinaryMergeLaws D)
    {C : ReplayContext D}
    (h_vis_trans : ∀ {a b c : Op D.AppOp},
       C.vis a b → C.vis b c → C.vis a c)
    (h_vis_irrefl : ∀ a : Op D.AppOp, ¬ C.vis a a)
    {ev : Set (Op D.AppOp)} {l : List (Op D.AppOp)}
    (h_l : listPermOf l ev)
    (h_in_C : ∀ a ∈ ev, a ∈ C.events) :
    ∃ s, IsCanonicalState C ev s := by
  obtain ⟨ρ, hp, hr⟩ :=
    exists_loOn_respecting_perm hVC h_vis_trans h_vis_irrefl h_l h_in_C
  exact ⟨applySeq D D.init ρ, ρ, hp, hr, rfl⟩

/-- A canonical state is a witness for the paper's Def-lin
obligation: its enumeration respects `lo C`. -/
theorem isCanonicalState_lo_witness {C : ReplayContext D}
    {ev : Set (Op D.AppOp)} {s : D.State}
    (h : IsCanonicalState C ev s) :
    ∃ ρ, listPermOf ρ ev ∧ respects ρ (lo C) ∧
      applySeq D D.init ρ = s := by
  obtain ⟨ρ, hp, hr, hs⟩ := h
  exact ⟨ρ, hp, respects_lo_of_respects_loOn hr, hs⟩

/-- **Peel** (the sound replacement for the paper's side-witness
re-permutation): a `loOn C ev`-maximal event factors out of the
canonical state exactly. Composes `perm_ending_in_loOn_max` (move
`e` to the tail, state-preserving) with `normalize_peel_tail`
(re-sort the front against the shrunken-set relation). -/
theorem isCanonicalState_peel [HistoricalBinaryMerge D]
    (hVC : BinaryMergeLaws D)
    {C : ReplayContext D}
    (h_vis_trans : ∀ {a b c : Op D.AppOp},
       C.vis a b → C.vis b c → C.vis a c)
    (h_vis_irrefl : ∀ a : Op D.AppOp, ¬ C.vis a a)
    {ev : Set (Op D.AppOp)} {s : D.State} {e : Op D.AppOp}
    (h_ev_in_C : ∀ a ∈ ev, a ∈ C.events)
    (h_e_in_ev : e ∈ ev)
    (h_e_max : ∀ x ∈ ev, x ≠ e → ¬ loOn C ev e x)
    (h : IsCanonicalState C ev s) :
    ∃ s', IsCanonicalState C (ev \ {e}) s' ∧ s = D.update s' e := by
  obtain ⟨ρ, hp, hr, hs⟩ := h
  obtain ⟨hp', hr', h_state⟩ :=
    perm_ending_in_loOn_max hVC h_ev_in_C hp hr h_e_in_ev h_e_max
  obtain ⟨ρ'', hp'', hr'', h_state''⟩ :=
    normalize_peel_tail hVC h_vis_trans h_vis_irrefl h_ev_in_C hp' hr'
  refine ⟨applySeq D D.init ρ'', ⟨ρ'', hp'', hr'', rfl⟩, ?_⟩
  rw [← hs, h_state D.init, ← h_state'' D.init, applySeq_append_single]

/-- **Extend** (the Apply case at the σ-level): a fresh event `e`
that observed everything in `ev` extends the canonical state by one
update. `e` has no outgoing `loOn`-edges, it is `vis`-after all of
`ev`, so neither disjunct can fire, and adding it only removes
rc-edges among the old events. -/
theorem isCanonicalState_extend {C : ReplayContext D}
    {ev : Set (Op D.AppOp)} {s : D.State} {e : Op D.AppOp}
    (h_e_fresh : e ∉ ev)
    (h_e_sees : ∀ x ∈ ev, C.vis x e)
    (h_e_last : ∀ x ∈ ev, ¬ C.vis e x)
    (h : IsCanonicalState C ev s) :
    IsCanonicalState C (insert e ev) (D.update s e) := by
  obtain ⟨ρ, hp, hr, hs⟩ := h
  refine ⟨ρ ++ [e], ⟨?_, fun a => ?_⟩, ?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨hp.1, List.nodup_singleton _, ?_⟩
    intro x hx y hy heq
    rw [List.mem_singleton] at hy; subst hy; subst heq
    exact h_e_fresh ((hp.2 x).mp hx)
  · rw [List.mem_append, List.mem_singleton, Set.mem_insert_iff]
    constructor
    · rintro (h' | rfl)
      · exact Or.inr ((hp.2 a).mp h')
      · exact Or.inl rfl
    · rintro (rfl | h')
      · exact Or.inr rfl
      · exact Or.inl ((hp.2 a).mpr h')
  · unfold respects
    rw [List.pairwise_append]
    refine ⟨hr.imp (fun hn h' =>
      hn (loOn_mono (Set.subset_insert _ _) h')), ?_, ?_⟩
    · exact List.pairwise_singleton _ _
    · intro y hy b hb
      rw [List.mem_singleton] at hb; subst hb
      have hy_ev : y ∈ ev := (hp.2 y).mp hy
      rintro (⟨h_vis, _⟩ | ⟨_, h_nvis_ye, _, _⟩)
      · exact h_e_last y hy_ev h_vis
      · -- the rc disjunct requires `e ∥ y`, but `e` observed `y`.
        exact h_nvis_ye (h_e_sees y hy_ev)
  · rw [applySeq_append_single, hs]

/-- **The Join Lemma.** The *entire* merge case of
the replay-convergence metatheorem reduces to this one state-level
statement (see `merge_linearization_of_join`). It is TRUE on every
worked instance including the associative counter-model, and its
peel step is valid under `loOn`-maximality + backward closure; but
it is NOT derivable from the VC bundle (the associative counter-model
kills every bottom-up derivation), and its peel identities are
irreducibly contextual: no unconditional per-CRDT equation
captures them. Discharging it (from cond-comm-style leaf VCs via a
contextual induction, or from lattice VCs (merge associativity +
update inflation/monotonicity)) is the open obligation. -/
def BinaryJoin (D : UpdateSig) [ReplayPolicy D]
    [HistoricalBinaryMerge D] : Prop :=
  ∀ (C : ReplayContext D) (ev₁ ev₂ : Set (Op D.AppOp)) (s₁ s₂ : D.State),
    (∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c) →
    (∀ a : Op D.AppOp, ¬ C.vis a a) →
    (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
    (∀ a b, C.vis a b → ¬ D.commutes a b → b ∈ ev₁ → a ∈ ev₁) →
    (∀ a b, C.vis a b → ¬ D.commutes a b → b ∈ ev₂ → a ∈ ev₂) →
    IsCanonicalState C ev₁ s₁ → IsCanonicalState C ev₂ s₂ →
    IsCanonicalState C (ev₁ ∪ ev₂) (D.historicalMerge s₁ s₂)

/-- **Reduction: the Join Lemma closes the merge case.** Given the
strengthened (set-relative) witnesses for the two replicas, the Join
Lemma delivers the merged witness, respecting `loOn` of the merged
set, hence in particular the paper's `lo C`. It stands in for
`merge_linearization_exists` without the (false) forward-closure
hypotheses and without the unsound re-permutation, using
`isCanonicalState_peel`-based reasoning inside `BinaryJoin`. -/
theorem merge_linearization_of_join {D : UpdateSig} [ReplayPolicy D]
    [HistoricalBinaryMerge D]
    (hJoin : BinaryJoin D) {C : ReplayContext D}
    (h_vis_trans : ∀ {a b c : Op D.AppOp},
       C.vis a b → C.vis b c → C.vis a c)
    (h_vis_irrefl : ∀ a : Op D.AppOp, ¬ C.vis a a)
    {π₁ π₂ : List (Op D.AppOp)} {ev₁ ev₂ : Set (Op D.AppOp)}
    {s₁ s₂ : D.State}
    (h_ev₁_in_C : ∀ a ∈ ev₁, a ∈ C.events)
    (h_ev₂_in_C : ∀ a ∈ ev₂, a ∈ C.events)
    (h_ev₁_closed :
      ∀ a b, C.vis a b → ¬ D.commutes a b → b ∈ ev₁ → a ∈ ev₁)
    (h_ev₂_closed :
      ∀ a b, C.vis a b → ¬ D.commutes a b → b ∈ ev₂ → a ∈ ev₂)
    (h₁_perm : listPermOf π₁ ev₁) (h₂_perm : listPermOf π₂ ev₂)
    (h₁_resp : respects π₁ (loOn C ev₁))
    (h₂_resp : respects π₂ (loOn C ev₂))
    (h₁_state : applySeq D D.init π₁ = s₁)
    (h₂_state : applySeq D D.init π₂ = s₂) :
    ∃ π, listPermOf π (ev₁ ∪ ev₂) ∧
         respects π (loOn C (ev₁ ∪ ev₂)) ∧
         respects π (lo C) ∧
         applySeq D D.init π = D.historicalMerge s₁ s₂ := by
  have h_join := hJoin C ev₁ ev₂ s₁ s₂ h_vis_trans h_vis_irrefl
    h_ev₁_in_C h_ev₂_in_C h_ev₁_closed h_ev₂_closed
    ⟨π₁, h₁_perm, h₁_resp, h₁_state⟩ ⟨π₂, h₂_perm, h₂_resp, h₂_state⟩
  obtain ⟨π, hp, hr, hs⟩ := h_join
  exact ⟨π, hp, hr, respects_lo_of_respects_loOn hr, hs⟩

/-! ### 7. The Join Lemma from the peel identities

The Join Lemma's induction peels a `loOn(ev₁ ∪ ev₂)`-maximal event
`e` from the union. Everything about that induction (maximal-event
selection, closure preservation, the measure, re-attachment) is
proved below. The two *state equations* it consumes are exactly the
contextual identities isolated here as the `BinaryPeelLaws` bundle:

* `peel_local`:  `merge s₁ s₂ = update (merge t₁ s₂) e` when `e` is
  union-maximal and local to side 1 (`t₁` canonical for `ev₁ ∖ {e}`);
* `peel_shared`: `merge s₁ s₂ = update (merge t₁ t₂) e` when `e` is
  union-maximal and shared.

They are stated over canonical states *with their full context*
(union-maximality, backward closure) because, as the two-key OR-set
shows, no unconditional equation over raw states is both
true and sufficient. `binaryJoin_of_peel` then closes the Join Lemma
completely. `binaryPeelLaws_of_all_comm` discharges the bundle for the
commuting class (every pair of events commutes, G-Set and friends),
giving the unconditional `binaryJoin_of_all_comm`. -/

/-- Two enumerations of the same set have the same length. -/
theorem listPermOf_length_eq {α : Type} {l₁ l₂ : List α}
    {ev : Set α}
    (h₁ : listPermOf l₁ ev) (h₂ : listPermOf l₂ ev) :
    l₁.length = l₂.length := by
  induction l₁ generalizing l₂ ev with
  | nil =>
    match l₂, h₂ with
    | [], _ => rfl
    | x :: _, h₂ =>
      exact absurd ((h₁.2 x).mpr ((h₂.2 x).mp List.mem_cons_self))
        List.not_mem_nil
  | cons a t ih =>
    classical
    have ha_ev : a ∈ ev := (h₁.2 a).mp List.mem_cons_self
    have ha_l₂ : a ∈ l₂ := (h₂.2 a).mpr ha_ev
    have h_nodup₁ := h₁.1
    rw [List.nodup_cons] at h_nodup₁
    have ht : listPermOf t (ev \ {a}) := by
      refine ⟨h_nodup₁.2, fun x => ?_⟩
      simp only [Set.mem_diff, Set.mem_singleton_iff]
      constructor
      · intro hx
        refine ⟨(h₁.2 x).mp (List.mem_cons_of_mem _ hx), ?_⟩
        intro rfl; exact h_nodup₁.1 hx
      · rintro ⟨hx, hne⟩
        rcases List.mem_cons.mp ((h₁.2 x).mpr hx) with h | h
        · exact absurd h hne
        · exact h
    have h₂' : listPermOf (l₂.erase a) (ev \ {a}) := by
      refine ⟨h₂.1.erase a, fun x => ?_⟩
      rw [h₂.1.mem_erase_iff]
      simp only [Set.mem_diff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hne, hx⟩
        exact ⟨(h₂.2 x).mp hx, hne⟩
      · rintro ⟨hx, hne⟩
        exact ⟨hne, (h₂.2 x).mpr hx⟩
    have h_len := ih ht h₂'
    have h_pos : 0 < l₂.length := List.length_pos_of_mem ha_l₂
    have h_er := List.length_erase_of_mem ha_l₂
    simp only [List.length_cons]
    omega

/-- Enumerate a union: side 1's list followed by side 2's leftovers. -/
theorem listPermOf_union {D : UpdateSig} [ReplayPolicy D] {l₁ l₂ : List (Op D.AppOp)}
    {ev₁ ev₂ : Set (Op D.AppOp)}
    (h₁ : listPermOf l₁ ev₁) (h₂ : listPermOf l₂ ev₂) :
    listPermOf (l₁ ++ l₂.filter (fun a => decide (a ∉ l₁)))
      (ev₁ ∪ ev₂) := by
  classical
  constructor
  · rw [List.nodup_append]
    refine ⟨h₁.1, h₂.1.filter _, ?_⟩
    intro x hx y hy heq
    subst heq
    have := (List.mem_filter.mp hy).2
    exact absurd hx (of_decide_eq_true this)
  · intro a
    rw [List.mem_append, List.mem_filter, Set.mem_union]
    constructor
    · rintro (h | ⟨h, _⟩)
      · exact Or.inl ((h₁.2 a).mp h)
      · exact Or.inr ((h₂.2 a).mp h)
    · rintro (h | h)
      · exact Or.inl ((h₁.2 a).mpr h)
      · by_cases hmem : a ∈ l₁
        · exact Or.inl hmem
        · exact Or.inr ⟨(h₂.2 a).mpr h, decide_eq_true hmem⟩

/-- Erasing an element of an enumeration enumerates the difference. -/
theorem erase_listPermOf {α : Type} [DecidableEq α]
    {l : List α} {ev : Set α} {e : α}
    (h : listPermOf l ev) (he : e ∈ l) :
    listPermOf (l.erase e) (ev \ {e}) := by
  refine ⟨h.1.erase e, fun a => ?_⟩
  rw [h.1.mem_erase_iff]
  simp only [Set.mem_diff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hne, ha⟩; exact ⟨(h.2 a).mp ha, hne⟩
  · rintro ⟨ha, hne⟩; exact ⟨hne, (h.2 a).mpr ha⟩

/-- Enumerations of `ev ∖ {e}` are one shorter than those of `ev`. -/
theorem listPermOf_diff_length {α : Type} [DecidableEq α]
    {l m : List α} {ev : Set α} {e : α}
    (hl : listPermOf l ev) (he : e ∈ l)
    (hm : listPermOf m (ev \ {e})) :
    m.length = l.length - 1 := by
  rw [listPermOf_length_eq hm (erase_listPermOf hl he)]
  exact List.length_erase_of_mem he

/-- The empty set's canonical state is `init`. -/
theorem isCanonicalState_empty {D : UpdateSig} [ReplayPolicy D] {C : ReplayContext D}
    {ev : Set (Op D.AppOp)} {s : D.State}
    (h_empty : ev = ∅) (h : IsCanonicalState C ev s) : s = D.init := by
  obtain ⟨ρ, hp, _, hf⟩ := h
  subst h_empty
  match ρ, hp with
  | [], _ => exact hf.symm ▸ rfl
  | x :: _, hp => exact absurd ((hp.2 x).mp List.mem_cons_self) id

/-- Backward closure survives removing a union-maximal event: a
`vis ∧ ¬commutes` edge out of `e` would be a `loOn`-edge in every
relation, contradicting maximality. -/
theorem closure_diff_of_max {D : UpdateSig} [ReplayPolicy D] {C : ReplayContext D}
    {ev evU : Set (Op D.AppOp)} {e : Op D.AppOp}
    (h_sub : ev ⊆ evU)
    (h_closed : ∀ a b, C.vis a b → ¬ D.commutes a b → b ∈ ev → a ∈ ev)
    (h_max : ∀ x ∈ evU, x ≠ e → ¬ loOn C evU e x) :
    ∀ a b, C.vis a b → ¬ D.commutes a b →
      b ∈ ev \ {e} → a ∈ ev \ {e} := by
  intro a b hv hnc ⟨hb, hb_ne⟩
  refine ⟨h_closed a b hv hnc hb, ?_⟩
  intro ha_eq
  have ha_eq' : a = e := ha_eq
  subst ha_eq'
  exact h_max b (h_sub hb) hb_ne (Or.inl ⟨hv, hnc⟩)

/-- Re-attach a union-maximal event to a canonical state of the
set-minus-it. -/
theorem isCanonicalState_snoc {D : UpdateSig} [ReplayPolicy D] {C : ReplayContext D}
    {ev : Set (Op D.AppOp)} {t : D.State} {e : Op D.AppOp}
    (h_e_in : e ∈ ev)
    (h_max : ∀ x ∈ ev, x ≠ e → ¬ loOn C ev e x)
    (h : IsCanonicalState C (ev \ {e}) t) :
    IsCanonicalState C ev (D.update t e) := by
  obtain ⟨ρ, hp, hr, hf⟩ := h
  have h_e_notin : e ∉ ρ := fun hmem => ((hp.2 e).mp hmem).2 rfl
  refine ⟨ρ ++ [e], ⟨?_, fun a => ?_⟩, ?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨hp.1, List.nodup_singleton _, ?_⟩
    intro x hx y hy heq
    rw [List.mem_singleton] at hy; subst hy; subst heq
    exact h_e_notin hx
  · rw [List.mem_append, List.mem_singleton]
    constructor
    · rintro (h' | rfl)
      · exact ((hp.2 a).mp h').1
      · exact h_e_in
    · intro ha
      by_cases hae : a = e
      · exact Or.inr hae
      · exact Or.inl ((hp.2 a).mpr ⟨ha, hae⟩)
  · unfold respects
    rw [List.pairwise_append]
    refine ⟨respects_loOn_mono (fun a ha => ha.1) hr,
      List.pairwise_singleton _ _, ?_⟩
    intro y hy b hb
    rw [List.mem_singleton] at hb; subst hb
    obtain ⟨hy_ev, hy_ne⟩ := (hp.2 y).mp hy
    exact h_max y hy_ev hy_ne
  · rw [applySeq_append_single, hf]

/-- **The peel identities**: the two contextual state equations the
Join Lemma's induction consumes, isolated as an explicit bundle.
See the section header for why they are stated over canonical states
with the union-maximality context. -/
structure BinaryPeelLaws (D : UpdateSig) [ReplayPolicy D]
    [HistoricalBinaryMerge D] : Prop where
  /-- Peel a union-maximal event local to side 1. -/
  peel_local :
    ∀ (C : ReplayContext D) (ev₁ ev₂ : Set (Op D.AppOp))
      (s₁ s₂ t₁ : D.State) (e : Op D.AppOp),
      (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
      (∀ a b, C.vis a b → ¬ D.commutes a b → b ∈ ev₁ → a ∈ ev₁) →
      (∀ a b, C.vis a b → ¬ D.commutes a b → b ∈ ev₂ → a ∈ ev₂) →
      e ∈ ev₁ → e ∉ ev₂ →
      (∀ x ∈ ev₁ ∪ ev₂, x ≠ e → ¬ loOn C (ev₁ ∪ ev₂) e x) →
      IsCanonicalState C ev₁ s₁ → IsCanonicalState C ev₂ s₂ →
      IsCanonicalState C (ev₁ \ {e}) t₁ →
      D.historicalMerge s₁ s₂ = D.update (D.historicalMerge t₁ s₂) e
  /-- Peel a union-maximal shared event. -/
  peel_shared :
    ∀ (C : ReplayContext D) (ev₁ ev₂ : Set (Op D.AppOp))
      (s₁ s₂ t₁ t₂ : D.State) (e : Op D.AppOp),
      (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
      (∀ a b, C.vis a b → ¬ D.commutes a b → b ∈ ev₁ → a ∈ ev₁) →
      (∀ a b, C.vis a b → ¬ D.commutes a b → b ∈ ev₂ → a ∈ ev₂) →
      e ∈ ev₁ → e ∈ ev₂ →
      (∀ x ∈ ev₁ ∪ ev₂, x ≠ e → ¬ loOn C (ev₁ ∪ ev₂) e x) →
      IsCanonicalState C ev₁ s₁ → IsCanonicalState C ev₂ s₂ →
      IsCanonicalState C (ev₁ \ {e}) t₁ →
      IsCanonicalState C (ev₂ \ {e}) t₂ →
      D.historicalMerge s₁ s₂ = D.update (D.historicalMerge t₁ t₂) e

/-- **The Join Lemma holds given the peel identities.** The master
induction: enumerate the union, select a `loOn(∪)`-maximal event,
peel it with `BinaryPeelLaws`, recurse on the strictly smaller sets,
and re-attach with `isCanonicalState_snoc`. -/
theorem binaryJoin_of_peel {D : UpdateSig} [ReplayPolicy D]
    [HistoricalBinaryMerge D] (hVC : BinaryMergeLaws D)
    (hPeel : BinaryPeelLaws D) : BinaryJoin D := by
  intro C ev₁ ev₂ s₁ s₂ h_vis_trans h_vis_irrefl h_in₁ h_in₂
    h_cl₁ h_cl₂ hc₁ hc₂
  classical
  obtain ⟨l₁, hp₁, hr₁, hf₁⟩ := hc₁
  obtain ⟨l₂, hp₂, hr₂, hf₂⟩ := hc₂
  -- Strong induction on the total enumeration length.
  suffices gen : ∀ n (ev₁ ev₂ : Set (Op D.AppOp)) (s₁ s₂ : D.State)
      (l₁ l₂ : List (Op D.AppOp)),
      l₁.length + l₂.length = n →
      (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
      (∀ a b, C.vis a b → ¬ D.commutes a b → b ∈ ev₁ → a ∈ ev₁) →
      (∀ a b, C.vis a b → ¬ D.commutes a b → b ∈ ev₂ → a ∈ ev₂) →
      listPermOf l₁ ev₁ → respects l₁ (loOn C ev₁) →
      applySeq D D.init l₁ = s₁ →
      listPermOf l₂ ev₂ → respects l₂ (loOn C ev₂) →
      applySeq D D.init l₂ = s₂ →
      IsCanonicalState C (ev₁ ∪ ev₂) (D.historicalMerge s₁ s₂) by
    exact gen _ ev₁ ev₂ s₁ s₂ l₁ l₂ rfl h_in₁ h_in₂ h_cl₁ h_cl₂
      hp₁ hr₁ hf₁ hp₂ hr₂ hf₂
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ev₁ ev₂ s₁ s₂ l₁ l₂ h_len h_in₁ h_in₂ h_cl₁ h_cl₂
      hp₁ hr₁ hf₁ hp₂ hr₂ hf₂
    -- Empty sides collapse via merge_init.
    rcases Set.eq_empty_or_nonempty ev₁ with h_e₁ | h_ne₁
    · have hs₁ : s₁ = D.init :=
        isCanonicalState_empty h_e₁ ⟨l₁, hp₁, hr₁, hf₁⟩
      subst h_e₁
      rw [hs₁, hVC.merge_init, Set.empty_union]
      exact ⟨l₂, hp₂, hr₂, hf₂⟩
    rcases Set.eq_empty_or_nonempty ev₂ with h_e₂ | h_ne₂
    · have hs₂ : s₂ = D.init :=
        isCanonicalState_empty h_e₂ ⟨l₂, hp₂, hr₂, hf₂⟩
      subst h_e₂
      rw [hs₂, hVC.merge_comm, hVC.merge_init, Set.union_empty]
      exact ⟨l₁, hp₁, hr₁, hf₁⟩
    -- Select a loOn(∪)-maximal event.
    have h_inU : ∀ a ∈ ev₁ ∪ ev₂, a ∈ C.events := by
      rintro a (h | h)
      · exact h_in₁ a h
      · exact h_in₂ a h
    have hpU := listPermOf_union (D := D) hp₁ hp₂
    obtain ⟨x₁, hx₁⟩ := h_ne₁
    obtain ⟨e, he_U, h_max⟩ :=
      exists_loOn_maximal hVC h_vis_trans h_vis_irrefl hpU h_inU
        ⟨x₁, Or.inl hx₁⟩
    -- Canonical states of the shrunken sides.
    by_cases he₁ : e ∈ ev₁
    · by_cases he₂ : e ∈ ev₂
      · -- Shared case.
        have h_e_l₁ : e ∈ l₁ := (hp₁.2 e).mpr he₁
        have h_e_l₂ : e ∈ l₂ := (hp₂.2 e).mpr he₂
        have hp₁' : listPermOf (l₁.filter (· ≠ e)) (ev₁ \ {e}) :=
          filter_ne_listPermOf_basic hp₁ h_e_l₁
        have hp₂' : listPermOf (l₂.filter (· ≠ e)) (ev₂ \ {e}) :=
          filter_ne_listPermOf_basic hp₂ h_e_l₂
        obtain ⟨t₁, hct₁⟩ :=
          isCanonicalState_exists hVC h_vis_trans h_vis_irrefl hp₁'
            (fun a ha => h_in₁ a ha.1)
        obtain ⟨t₂, hct₂⟩ :=
          isCanonicalState_exists hVC h_vis_trans h_vis_irrefl hp₂'
            (fun a ha => h_in₂ a ha.1)
        have h_eq := hPeel.peel_shared C ev₁ ev₂ s₁ s₂ t₁ t₂ e
          h_in₁ h_in₂ h_cl₁ h_cl₂ he₁ he₂ h_max
          ⟨l₁, hp₁, hr₁, hf₁⟩ ⟨l₂, hp₂, hr₂, hf₂⟩ hct₁ hct₂
        -- Recurse.
        obtain ⟨m₁, hm₁, hrm₁, hfm₁⟩ := hct₁
        obtain ⟨m₂, hm₂, hrm₂, hfm₂⟩ := hct₂
        have h_len₁ : m₁.length = l₁.length - 1 :=
          listPermOf_diff_length hp₁ h_e_l₁ hm₁
        have h_len₂ : m₂.length = l₂.length - 1 :=
          listPermOf_diff_length hp₂ h_e_l₂ hm₂
        have h_pos₁ : 0 < l₁.length := List.length_pos_of_mem h_e_l₁
        have h_pos₂ : 0 < l₂.length := List.length_pos_of_mem h_e_l₂
        have h_ih := ih (m₁.length + m₂.length) (by omega)
          (ev₁ \ {e}) (ev₂ \ {e}) t₁ t₂ m₁ m₂ rfl
          (fun a ha => h_in₁ a ha.1) (fun a ha => h_in₂ a ha.1)
          (closure_diff_of_max Set.subset_union_left h_cl₁ h_max)
          (closure_diff_of_max Set.subset_union_right h_cl₂ h_max)
          hm₁ hrm₁ hfm₁ hm₂ hrm₂ hfm₂
        have h_set : (ev₁ \ {e}) ∪ (ev₂ \ {e}) = (ev₁ ∪ ev₂) \ {e} := by
          ext x
          simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff]
          tauto
        rw [h_set] at h_ih
        rw [h_eq]
        exact isCanonicalState_snoc (Or.inl he₁) h_max h_ih
      · -- Local to side 1.
        have h_e_l₁ : e ∈ l₁ := (hp₁.2 e).mpr he₁
        have hp₁' : listPermOf (l₁.filter (· ≠ e)) (ev₁ \ {e}) :=
          filter_ne_listPermOf_basic hp₁ h_e_l₁
        obtain ⟨t₁, hct₁⟩ :=
          isCanonicalState_exists hVC h_vis_trans h_vis_irrefl hp₁'
            (fun a ha => h_in₁ a ha.1)
        have h_eq := hPeel.peel_local C ev₁ ev₂ s₁ s₂ t₁ e
          h_in₁ h_in₂ h_cl₁ h_cl₂ he₁ he₂ h_max
          ⟨l₁, hp₁, hr₁, hf₁⟩ ⟨l₂, hp₂, hr₂, hf₂⟩ hct₁
        obtain ⟨m₁, hm₁, hrm₁, hfm₁⟩ := hct₁
        have h_len₁ : m₁.length = l₁.length - 1 :=
          listPermOf_diff_length hp₁ h_e_l₁ hm₁
        have h_pos₁ : 0 < l₁.length := List.length_pos_of_mem h_e_l₁
        have h_ih := ih (m₁.length + l₂.length) (by omega)
          (ev₁ \ {e}) ev₂ t₁ s₂ m₁ l₂ rfl
          (fun a ha => h_in₁ a ha.1) h_in₂
          (closure_diff_of_max Set.subset_union_left h_cl₁ h_max)
          h_cl₂ hm₁ hrm₁ hfm₁ hp₂ hr₂ hf₂
        have h_set : (ev₁ \ {e}) ∪ ev₂ = (ev₁ ∪ ev₂) \ {e} := by
          ext x
          simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff]
          constructor
          · rintro (⟨h, hne⟩ | h)
            · exact ⟨Or.inl h, hne⟩
            · exact ⟨Or.inr h, fun heq => he₂ (heq ▸ h)⟩
          · rintro ⟨h | h, hne⟩
            · exact Or.inl ⟨h, hne⟩
            · exact Or.inr h
        rw [h_set] at h_ih
        rw [h_eq]
        exact isCanonicalState_snoc (Or.inl he₁) h_max h_ih
    · -- Local to side 2: mirror via merge_comm.
      have he₂ : e ∈ ev₂ := by
        rcases he_U with h | h
        · exact absurd h he₁
        · exact h
      have h_e_l₂ : e ∈ l₂ := (hp₂.2 e).mpr he₂
      have hp₂' : listPermOf (l₂.filter (· ≠ e)) (ev₂ \ {e}) :=
        filter_ne_listPermOf_basic hp₂ h_e_l₂
      obtain ⟨t₂, hct₂⟩ :=
        isCanonicalState_exists hVC h_vis_trans h_vis_irrefl hp₂'
          (fun a ha => h_in₂ a ha.1)
      have h_max' : ∀ x ∈ ev₂ ∪ ev₁, x ≠ e →
          ¬ loOn C (ev₂ ∪ ev₁) e x := by
        rw [Set.union_comm]
        exact h_max
      have h_eq := hPeel.peel_local C ev₂ ev₁ s₂ s₁ t₂ e
        h_in₂ h_in₁ h_cl₂ h_cl₁ he₂ he₁ h_max'
        ⟨l₂, hp₂, hr₂, hf₂⟩ ⟨l₁, hp₁, hr₁, hf₁⟩ hct₂
      obtain ⟨m₂, hm₂, hrm₂, hfm₂⟩ := hct₂
      have h_len₂ : m₂.length = l₂.length - 1 :=
        listPermOf_diff_length hp₂ h_e_l₂ hm₂
      have h_pos₂ : 0 < l₂.length := List.length_pos_of_mem h_e_l₂
      have h_ih := ih (l₁.length + m₂.length) (by omega)
        ev₁ (ev₂ \ {e}) s₁ t₂ l₁ m₂ rfl
        h_in₁ (fun a ha => h_in₂ a ha.1) h_cl₁
        (closure_diff_of_max Set.subset_union_right h_cl₂ h_max)
        hp₁ hr₁ hf₁ hm₂ hrm₂ hfm₂
      have h_set : ev₁ ∪ (ev₂ \ {e}) = (ev₁ ∪ ev₂) \ {e} := by
        ext x
        simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff]
        constructor
        · rintro (h | ⟨h, hne⟩)
          · exact ⟨Or.inl h, fun heq => he₁ (heq ▸ h)⟩
          · exact ⟨Or.inr h, hne⟩
        · rintro ⟨h | h, hne⟩
          · exact Or.inl h
          · exact Or.inr ⟨h, hne⟩
      rw [h_set] at h_ih
      rw [hVC.merge_comm, h_eq, hVC.merge_comm t₂ s₁]
      exact isCanonicalState_snoc (Or.inr he₂) h_max h_ih

/-! #### The commuting class

For a `D` in which every pair of events commutes (G-Set and its
relatives), `loOn` relates no two distinct events at all,
`rc_non_comm_directional` kills the rc disjunct, so both peel
identities discharge from `applySeq_comm_extract`, `merge_peel_comm`
and `lem_0op`, and the Join Lemma holds unconditionally. -/

/-- With all events commuting, `loOn` has no edges between distinct
events of the configuration. -/
theorem loOn_empty_of_all_comm {D : UpdateSig} [ReplayPolicy D]
    [HistoricalBinaryMerge D] (hVC : BinaryMergeLaws D)
    {C : ReplayContext D} {ev : Set (Op D.AppOp)}
    (h_comm : ∀ a b : Op D.AppOp, D.commutes a b)
    {x y : Op D.AppOp} (hx : x ∈ C.events) (hy : y ∈ C.events)
    (hne : x ≠ y) :
    ¬ loOn C ev x y := by
  rintro (⟨_, hnc⟩ | ⟨_, _, h_rc, _⟩)
  · exact hnc (h_comm x y)
  · exact (hVC.rc_non_comm_directional x y
      (distinctOps_of_events hx hy hne)).mpr (Or.inl h_rc) (h_comm x y)

/-- Any enumeration is canonical when all events commute. -/
theorem isCanonicalState_of_all_comm {D : UpdateSig} [ReplayPolicy D]
    [HistoricalBinaryMerge D]
    (hVC : BinaryMergeLaws D) {C : ReplayContext D}
    {ev : Set (Op D.AppOp)} {l : List (Op D.AppOp)}
    (h_comm : ∀ a b : Op D.AppOp, D.commutes a b)
    (h_in_C : ∀ a ∈ ev, a ∈ C.events)
    (h_perm : listPermOf l ev) :
    IsCanonicalState C ev (applySeq D D.init l) := by
  refine ⟨l, h_perm, ?_, rfl⟩
  refine List.Pairwise.imp_of_mem ?_ h_perm.1
  intro a b ha hb hne
  exact loOn_empty_of_all_comm hVC h_comm
    (h_in_C b ((h_perm.2 b).mp hb)) (h_in_C a ((h_perm.2 a).mp ha))
    (Ne.symm hne)

/-- The peel bundle for the commuting class. -/
theorem binaryPeelLaws_of_all_comm {D : UpdateSig} [ReplayPolicy D]
    [HistoricalBinaryMerge D] (hVC : BinaryMergeLaws D)
    (h_comm : ∀ a b : Op D.AppOp, D.commutes a b) :
    BinaryPeelLaws D := by
  constructor
  · -- peel_local
    intro C ev₁ ev₂ s₁ s₂ t₁ e h_in₁ h_in₂ _ _ he₁ _ _ hc₁ hc₂ hct₁
    obtain ⟨l₁, hp₁, _, hf₁⟩ := hc₁
    obtain ⟨l₂, _, _, hf₂⟩ := hc₂
    have h_e_l₁ : e ∈ l₁ := (hp₁.2 e).mpr he₁
    -- Extract e from side 1's enumeration.
    have h_ex := applySeq_comm_extract_basic (D := D) h_e_l₁ hp₁.1
      (fun x _ _ => h_comm e x) D.init
    -- The filtered fold is canonical for ev₁ \ {e}, hence equals t₁.
    have hp₁' : listPermOf (l₁.filter (· ≠ e)) (ev₁ \ {e}) :=
      filter_ne_listPermOf_basic hp₁ h_e_l₁
    have h_t₁ : applySeq D D.init (l₁.filter (· ≠ e)) = t₁ :=
      isCanonicalState_unique hVC (fun a ha => h_in₁ a ha.1)
        (isCanonicalState_of_all_comm hVC h_comm
          (fun a ha => h_in₁ a ha.1) hp₁') hct₁
    rw [← hf₁, ← hf₂, h_ex, h_t₁]
    exact hVC.merge_peel_comm t₁ e l₂ (fun x _ => h_comm e x)
  · -- peel_shared
    intro C ev₁ ev₂ s₁ s₂ t₁ t₂ e h_in₁ h_in₂ _ _ he₁ he₂ _
      hc₁ hc₂ hct₁ hct₂
    obtain ⟨l₁, hp₁, _, hf₁⟩ := hc₁
    obtain ⟨l₂, hp₂, _, hf₂⟩ := hc₂
    have h_e_l₁ : e ∈ l₁ := (hp₁.2 e).mpr he₁
    have h_e_l₂ : e ∈ l₂ := (hp₂.2 e).mpr he₂
    have h_ex₁ := applySeq_comm_extract_basic (D := D) h_e_l₁ hp₁.1
      (fun x _ _ => h_comm e x) D.init
    have h_ex₂ := applySeq_comm_extract_basic (D := D) h_e_l₂ hp₂.1
      (fun x _ _ => h_comm e x) D.init
    have hp₁' : listPermOf (l₁.filter (· ≠ e)) (ev₁ \ {e}) :=
      filter_ne_listPermOf_basic hp₁ h_e_l₁
    have hp₂' : listPermOf (l₂.filter (· ≠ e)) (ev₂ \ {e}) :=
      filter_ne_listPermOf_basic hp₂ h_e_l₂
    have h_t₁ : applySeq D D.init (l₁.filter (· ≠ e)) = t₁ :=
      isCanonicalState_unique hVC (fun a ha => h_in₁ a ha.1)
        (isCanonicalState_of_all_comm hVC h_comm
          (fun a ha => h_in₁ a ha.1) hp₁') hct₁
    have h_t₂ : applySeq D D.init (l₂.filter (· ≠ e)) = t₂ :=
      isCanonicalState_unique hVC (fun a ha => h_in₂ a ha.1)
        (isCanonicalState_of_all_comm hVC h_comm
          (fun a ha => h_in₂ a ha.1) hp₂') hct₂
    rw [← hf₁, ← hf₂, h_ex₁, h_ex₂, h_t₁, h_t₂]
    exact hVC.lem_0op t₁ t₂ e

/-- **The Join Lemma, unconditionally, for the commuting class.** -/
theorem binaryJoin_of_all_comm {D : UpdateSig} [ReplayPolicy D]
    [HistoricalBinaryMerge D] (hVC : BinaryMergeLaws D)
    (h_comm : ∀ a b : Op D.AppOp, D.commutes a b) : BinaryJoin D :=
  binaryJoin_of_peel hVC (binaryPeelLaws_of_all_comm hVC h_comm)

end

end Sal.MRDTs.Foundation
