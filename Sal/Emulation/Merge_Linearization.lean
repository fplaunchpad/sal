import Sal.Emulation.RA_Linearizability
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup

/-!
# Merge linearization (existential form)

Given two RA-lin witnesses `π₁` (for replica `r₁` at state `s₁` and
event set `ev₁`) and `π₂` (for `r₂` at `s₂`, `ev₂`), establish the
existence of a witness for the merged configuration.

## Why existential, not constructive

A previous design attempted a three-lemma decomposition
`merge_witness_{perm, respects, state}` against a concrete witness
definition. That design fails: **any elementary witness definition
couples `_respects` and `_state`**. The concurrent, `rc`-ordered
cross case in `_respects` has no contradiction from permutation /
respect hypotheses alone — closing it requires knowing the state
equation being proved. The paper's own proof handles this by
**co-constructing** the witness and the lo-respect property inside
a single bottom-up induction; separating them is a mechanisation
artifact that doesn't reflect the proof.

We therefore state the merge-case as a single existential theorem
`merge_linearization_exists` (paper Lemma 1 / Theorem 1, lin.tex
§3.3 + appendix §A.2–A.4) and will prove it by induction on the
total event count, pulling events out of `merge` one at a time via
the 24 VCs (`base_*`, `ind_*`, `inter_*`, `lem_0op`).

The `restrictTo` helper is kept for use inside the induction's
inductive-case argument. -/

namespace Sal.Emulation

open Classical

section
variable {D : CRDTSig}

/-- Sub-list of `π` restricted to events in set `E`. Uses classical
decidability on `Set` membership, so the function is `noncomputable`. -/
noncomputable def restrictTo (π : List (Op D.AppOp)) (E : Set (Op D.AppOp)) :
    List (Op D.AppOp) :=
  π.filter fun x => decide (x ∈ E)

/-! ### Event-set decomposition (paper's L^a / L^b partitions)

For the Merge case's inductive argument, the Sal paper (lin.tex §3.3,
detailed in appendix §A.2–A.4) partitions the event sets involved
in a merge. Specialised to 2-way CRDT merge (LCA collapses to
`init`), the partition is:

* `L_top = ev₁ ∩ ev₂` — events seen at both replicas (shared
  history).
* `L₁' = ev₁ \ ev₂` — events local to `r₁`.
* `L₂' = ev₂ \ ev₁` — events local to `r₂`.

Within the local events, a further partition reflects whether a
local event is `lo`-before some shared event (needs to be
linearised early) or not (can be appended at the end):

* `L_a C ev_local` — local events **not** `lo`-before any shared
  event. These are the "easy" events that linearise at the end of
  the merge.
* `L_b C ev_local` — local events `lo`-before some shared event or
  transitively `lo`-before another local `L_b` event.

These definitions set up the structure the next session's
inductive argument will use. No lemmas about them are proved
here yet. -/

/-- Shared events of a 2-way CRDT merge. -/
def L_top (ev₁ ev₂ : Set (Op D.AppOp)) : Set (Op D.AppOp) := ev₁ ∩ ev₂

/-- Events local to `r₁`. -/
def L₁_local (ev₁ ev₂ : Set (Op D.AppOp)) : Set (Op D.AppOp) := ev₁ \ ev₂

/-- Events local to `r₂`. -/
def L₂_local (ev₁ ev₂ : Set (Op D.AppOp)) : Set (Op D.AppOp) := ev₂ \ ev₁

/-- Local events with a lo-path of length 1 OR 2 to `ev_top`,
matching `appendix.tex:262`:

  L_1^b = { e ∈ L_1' | ∃ e_⊤ ∈ L_⊤.
              (e →_lo e_⊤ ∨ ∃ e' ∈ L_1'. e →_lo e' →_lo e_⊤) }

The depth-2 case is essential for Lemma 1's "no lo-edge from `L^a`
to `L^b`" — see the audit block below. -/
def L_b (C : Configuration D) (ev_top ev_local : Set (Op D.AppOp)) :
    Set (Op D.AppOp) :=
  fun e => e ∈ ev_local ∧
    ((∃ e' ∈ ev_top, lo C e e') ∨
     (∃ e' ∈ ev_local, ∃ e'' ∈ ev_top, lo C e e' ∧ lo C e' e''))

/-- Local events with NO lo-path (of length 1 or 2) to `ev_top`.
These linearise at the end of the merge witness, peeled via
`bottomUp_2op_reachable` or `bottomUp_1op_top_reachable`. Defined
as the complement of `L_b` within `ev_local`. -/
def L_a (C : Configuration D) (ev_top ev_local : Set (Op D.AppOp)) :
    Set (Op D.AppOp) :=
  fun e => e ∈ ev_local ∧
    ¬ ((∃ e' ∈ ev_top, lo C e e') ∨
       (∃ e' ∈ ev_local, ∃ e'' ∈ ev_top, lo C e e' ∧ lo C e' e''))

/-- Sanity: `L_a ∪ L_b = ev_local` (every local event either has
some lo-path of length ≤ 2 to `ev_top`, or none). -/
theorem L_a_union_L_b (C : Configuration D) (ev_top ev_local : Set (Op D.AppOp)) :
    L_a C ev_top ev_local ∪ L_b C ev_top ev_local = ev_local := by
  ext e
  simp only [Set.mem_union]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro he
    by_cases h : (∃ e' ∈ ev_top, lo C e e') ∨
                 (∃ e' ∈ ev_local, ∃ e'' ∈ ev_top, lo C e e' ∧ lo C e' e'')
    · exact Or.inr ⟨he, h⟩
    · exact Or.inl ⟨he, h⟩

/-- Sanity: `L_a` and `L_b` are disjoint. -/
theorem L_a_inter_L_b (C : Configuration D) (ev_top ev_local : Set (Op D.AppOp)) :
    L_a C ev_top ev_local ∩ L_b C ev_top ev_local = ∅ := by
  ext e
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨_, h_neg⟩, _, h_pos⟩
  exact h_neg h_pos

/-- Decomposition sanity: `ev₁ = L_top ∪ L₁_local` (disjoint union). -/
theorem ev₁_eq_top_union_local (ev₁ ev₂ : Set (Op D.AppOp)) :
    ev₁ = L_top ev₁ ev₂ ∪ L₁_local ev₁ ev₂ := by
  ext e
  simp only [L_top, L₁_local, Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
  constructor
  · intro he
    by_cases h : e ∈ ev₂
    · exact Or.inl ⟨he, h⟩
    · exact Or.inr ⟨he, h⟩
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h

/-- Mirror: `ev₂ = L_top ∪ L₂_local`. -/
theorem ev₂_eq_top_union_local (ev₁ ev₂ : Set (Op D.AppOp)) :
    ev₂ = L_top ev₁ ev₂ ∪ L₂_local ev₁ ev₂ := by
  ext e
  simp only [L_top, L₂_local, Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
  constructor
  · intro he
    by_cases h : e ∈ ev₁
    · exact Or.inl ⟨h, he⟩
    · exact Or.inr ⟨he, h⟩
  · rintro (⟨_, h⟩ | ⟨h, _⟩) <;> exact h

/-- Decomposition sanity: `ev₁ ∪ ev₂ = L_top ∪ L₁_local ∪ L₂_local`. -/
theorem union_eq_partition (ev₁ ev₂ : Set (Op D.AppOp)) :
    ev₁ ∪ ev₂ = L_top ev₁ ev₂ ∪ L₁_local ev₁ ev₂ ∪ L₂_local ev₁ ev₂ := by
  ext e
  simp only [L_top, L₁_local, L₂_local,
             Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
  tauto

/-! Subset facts. Each `L_*` partition piece is a subset of one of
the underlying replica event sets `ev₁`, `ev₂`. Demand-driven —
consumed by the distinct-last-event proof to invoke
`exists_lo_maximal_in_subset` on the carving layers. -/

theorem L_top_subset_left (ev₁ ev₂ : Set (Op D.AppOp)) :
    L_top ev₁ ev₂ ⊆ ev₁ := fun _ h => h.1

theorem L_top_subset_right (ev₁ ev₂ : Set (Op D.AppOp)) :
    L_top ev₁ ev₂ ⊆ ev₂ := fun _ h => h.2

theorem L₁_local_subset (ev₁ ev₂ : Set (Op D.AppOp)) :
    L₁_local ev₁ ev₂ ⊆ ev₁ := fun _ h => h.1

theorem L₂_local_subset (ev₁ ev₂ : Set (Op D.AppOp)) :
    L₂_local ev₁ ev₂ ⊆ ev₂ := fun _ h => h.1

theorem L_a_subset_local (C : Configuration D)
    (ev_top ev_local : Set (Op D.AppOp)) :
    L_a C ev_top ev_local ⊆ ev_local := fun _ h => h.1

theorem L_b_subset_local (C : Configuration D)
    (ev_top ev_local : Set (Op D.AppOp)) :
    L_b C ev_top ev_local ⊆ ev_local := fun _ h => h.1

/-! ### Carving of `L_top` (paper `appendix.tex:264-265`)

Within the shared events `L_top`, classify each event by whether
some `L^b`-event lo-precedes it:

  L_top^a = { e_⊤ ∈ L_⊤ | ∃ e ∈ L_1^b ∪ L_2^b. e →_lo e_⊤ }
  L_top^b = L_⊤ \ L_top^a

The appendix's outer induction case-splits on `|L_top^a|` (with
the `L_1^a ∪ L_2^a = ∅` outer base): inner base when
`|L_top^a| = 0`, inner step pulls a maximal `L_top^a` element via
`BottomUp-0-OP`. Definitions are robust to the `L_b` depth fix
since they take `L_b` as input rather than re-deriving it. -/

/-- Shared events with a lo-predecessor in `L_1^b ∪ L_2^b`. -/
def L_top_a (C : Configuration D) (ev₁ ev₂ : Set (Op D.AppOp)) :
    Set (Op D.AppOp) :=
  fun e_top => e_top ∈ L_top ev₁ ev₂ ∧
    ∃ e, (e ∈ L_b C (L_top ev₁ ev₂) (L₁_local ev₁ ev₂) ∨
          e ∈ L_b C (L_top ev₁ ev₂) (L₂_local ev₁ ev₂)) ∧
         lo C e e_top

/-- Shared events with NO lo-predecessor in `L_1^b ∪ L_2^b`. -/
def L_top_b (C : Configuration D) (ev₁ ev₂ : Set (Op D.AppOp)) :
    Set (Op D.AppOp) :=
  fun e_top => e_top ∈ L_top ev₁ ev₂ ∧
    ¬ ∃ e, (e ∈ L_b C (L_top ev₁ ev₂) (L₁_local ev₁ ev₂) ∨
            e ∈ L_b C (L_top ev₁ ev₂) (L₂_local ev₁ ev₂)) ∧
           lo C e e_top

theorem L_top_a_subset (C : Configuration D) (ev₁ ev₂ : Set (Op D.AppOp)) :
    L_top_a C ev₁ ev₂ ⊆ L_top ev₁ ev₂ := fun _ h => h.1

theorem L_top_b_subset (C : Configuration D) (ev₁ ev₂ : Set (Op D.AppOp)) :
    L_top_b C ev₁ ev₂ ⊆ L_top ev₁ ev₂ := fun _ h => h.1

theorem L_top_a_union_L_top_b (C : Configuration D) (ev₁ ev₂ : Set (Op D.AppOp)) :
    L_top_a C ev₁ ev₂ ∪ L_top_b C ev₁ ev₂ = L_top ev₁ ev₂ := by
  ext e
  simp only [Set.mem_union]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro he
    by_cases h : ∃ e', (e' ∈ L_b C (L_top ev₁ ev₂) (L₁_local ev₁ ev₂) ∨
                         e' ∈ L_b C (L_top ev₁ ev₂) (L₂_local ev₁ ev₂)) ∧
                       lo C e' e
    · exact Or.inl ⟨he, h⟩
    · exact Or.inr ⟨he, h⟩

theorem L_top_a_inter_L_top_b (C : Configuration D) (ev₁ ev₂ : Set (Op D.AppOp)) :
    L_top_a C ev₁ ev₂ ∩ L_top_b C ev₁ ev₂ = ∅ := by
  ext e
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨_, h_ex⟩, _, h_no⟩
  exact h_no h_ex

/-! ### `L_b_at`: parameterized `L_b` for a single LCA event

The paper's nested induction (`appendix.tex:262, 313`) parameterizes
`L_1^b` by a specific `e_⊤ ∈ L_⊤^a`: `M_1^a := L_1^b(e_m^⊤)`. Our
existing `L_b` quantifies over all `e_⊤ ∈ ev_top`; the parameterized
form below fixes `e_top` and is a subset of the all-paths form. -/

/-- `L_b_at C e_top ev_local`: events in `ev_local` with a lo-path
of length 1 or 2 to the **specific** event `e_top` (paper's
`L_1^b(e_top)`). -/
def L_b_at (C : Configuration D) (e_top : Op D.AppOp)
    (ev_local : Set (Op D.AppOp)) : Set (Op D.AppOp) :=
  fun e => e ∈ ev_local ∧
    (lo C e e_top ∨
     (∃ e' ∈ ev_local, lo C e e' ∧ lo C e' e_top))

theorem L_b_at_subset_local (C : Configuration D) (e_top : Op D.AppOp)
    (ev_local : Set (Op D.AppOp)) :
    L_b_at C e_top ev_local ⊆ ev_local := fun _ h => h.1

theorem L_b_at_subset_L_b (C : Configuration D) {e_top : Op D.AppOp}
    {ev_top ev_local : Set (Op D.AppOp)} (h : e_top ∈ ev_top) :
    L_b_at C e_top ev_local ⊆ L_b C ev_top ev_local := by
  rintro e ⟨h_loc, h_path⟩
  refine ⟨h_loc, ?_⟩
  rcases h_path with h_lo | ⟨e', h_loc', h_lo_ee', h_lo_e'_top⟩
  · exact Or.inl ⟨e_top, h, h_lo⟩
  · exact Or.inr ⟨e', h_loc', e_top, h, h_lo_ee', h_lo_e'_top⟩

/-! ### `L_top` causal closure (paper appendix.tex:209-210)

The paper's "L_top^a is causally closed" is (a) `L_top` is closed
under vis-predecessors when both `ev₁` and `ev₂` are, and (b) any
vis-predecessor of an `L_top_a` element lands somewhere in `L_top`
(which decomposes into `L_top_a ∪ L_top_b`).

These hold because `L_top := ev₁ ∩ ev₂`, and replicas observe events
causally (`vis_causal` on `Configuration`). For events in `ev₁ ∩ ev₂`,
both replicas observed them, so both observed any vis-predecessors. -/

theorem L_top_vis_closed
    {C : Configuration D} {ev₁ ev₂ : Set (Op D.AppOp)}
    (h_ev₁_closed : ∀ a b, C.vis a b → b ∈ ev₁ → a ∈ ev₁)
    (h_ev₂_closed : ∀ a b, C.vis a b → b ∈ ev₂ → a ∈ ev₂)
    {a b : Op D.AppOp} (h_vis : C.vis a b)
    (h_b : b ∈ L_top ev₁ ev₂) :
    a ∈ L_top ev₁ ev₂ :=
  ⟨h_ev₁_closed a b h_vis h_b.1, h_ev₂_closed a b h_vis h_b.2⟩

/-! **`L_b` depth audit (paper-side, 2026-04-25, post-fix).**

Per `appendix.tex:262`, `L_1^b` accepts events with a lo-path of
length 1 OR 2 to `L_⊤`:

  L_1^b = { e ∈ L_1' | ∃ e_⊤ ∈ L_⊤.
              (e →_lo e_⊤ ∨ ∃ e' ∈ L_1'. e →_lo e' →_lo e_⊤) }

**Depth-2 is essential** for Lemma 1 of `appendix.tex:117-156`
("no lo-edge from `L^a` to `L^b`"). Case 1.b.i (line 128) runs:
`e →_vis e' →_vis e'' ∈ L_1' →_lo e_⊤`; by vis-transitivity
`e →_vis e''`, so `e` has a depth-2 lo-path to `L_⊤`, hence
`e ∈ L_b`. Without depth-2 in the definition, that step fails.
The depth is bounded at 2 by `no_rc_chain` (at most one `rc`-edge
per lo-path; vis-chains collapse via vis-transitivity).

**Fix landed (this session).** `L_b` and `L_a` above now match
the paper's depth-1-or-2 form. `L_a_union_L_b` and
`L_a_inter_L_b` re-proved against the new definitions. The
partition layer is now appendix-faithful before the distinct-last
branch consumes it. -/

/-! ### Convergence

Two `lo`-respecting permutations of the same event set yield the
same state when folded into `D.init`.

This is the Sal paper's **convergence theorem** (lin.tex §3.2,
Lemma `convergence`). It underpins several sub-cases of
`merge_linearization_exists`:

* `π₁ = []`, `π₂ ≠ []`: we need `merge D.init s₂ = s₂` for
  reachable `s₂`. Convergence gives us that any `lo`-respecting
  permutation of `ev₂` yields `s₂`; combined with `base_1op` +
  induction, this collapses the `merge init` to the right-side
  state.
* The mirror `π₁ ≠ []`, `π₂ = []` symmetrically.

Convergence is provable from the 24 VCs via a bubble-sort argument:
any two `lo`-respecting permutations differ by adjacent
transpositions of lo-unordered pairs; each transposition preserves
state via `rc_non_comm` (unordered ⟹ commuting) or `cond_comm` +
the presence of an overwriter.

The proof is structured in four layers:

1. `applySeq_swap_commute` — swap commuting adjacent ops. Direct
   from `D.commutes`. Closed.
2. `applySeq_swap_lo_incomparable` — swap lo-incomparable adjacent
   ops (both events in `C.events`). Case-splits on commute; closes
   three of four sub-cases:
   - `commutes a b`: direct from (1).
   - same replica: `vis_total_same_replica` + `¬commutes` ⟹ `lo`
     in some direction, contradicting incomparability. Closed.
   - different replica, commutes: direct from (1).
   - different replica, `¬commutes`: needs overwriter + cond_comm.
     **Remaining sorry.**
3. `applySeq_bubble_lo_max` — bubble a lo-maximal event to the end
   of a list via repeated (2). Closed modulo (2).
4. `convergence` — strong induction on `π₁.length`, picking last
   event of `π₁`, splitting `π₂`, bubbling, recursing. Closed
   modulo (2) and (3). -/

/-- **Swap adjacent events via explicit overwriter.**

Closes the swap using `cond_comm_lift` at an explicit overwriter `e₃`
in `sfx`. The caller supplies the split `sfx = α ++ e₃ :: β` and the
rc preconditions. Matches the Sal paper's treatment where `e₃` is
found in `τ₄` (suffix after the swap) via `lo e' e₃`.

Proof: absorb `pfx` into the state, unfold `applySeq` across `α`
and the e₃ point, apply `cond_comm_lift` to equate the states at
e₃, then apply `β` uniformly on both sides. -/
theorem applySeq_swap_via_cond_comm_lift
    (hVC : SatisfiesVCs D)
    {a b e₃ : Op D.AppOp}
    (h_dist_ab : distinctOps a b)
    (h_dist_be : distinctOps b e₃)
    (h_dist_ae : distinctOps a e₃)
    (h_rc_ab : D.rc a b = RcRes.Fst_then_snd)
    (h_nc_be : ¬ D.commutes b e₃)
    (pfx α β : List (Op D.AppOp)) (s : D.State) :
    applySeq D s (pfx ++ a :: b :: (α ++ e₃ :: β))
    = applySeq D s (pfx ++ b :: a :: (α ++ e₃ :: β)) := by
  -- Reduce both sides to a common shape, then apply `cond_comm_lift`
  -- to equate the inner states at `e₃`.
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

/-- **Swap adjacent commuting events.** Folding preserves state
when two commuting events are swapped in position. -/
theorem applySeq_swap_commute
    {a b : Op D.AppOp} (h_comm : D.commutes a b)
    (pfx sfx : List (Op D.AppOp)) (s : D.State) :
    applySeq D s (pfx ++ a :: b :: sfx)
    = applySeq D s (pfx ++ b :: a :: sfx) := by
  simp only [applySeq, List.foldl_append, List.foldl_cons]
  rw [h_comm]

/-- **Swap adjacent lo-incomparable events** (Path 1 version).

If `a ≠ b` are events in `C.events` and are not ordered by `lo C`
in either direction, their adjacent swap preserves `applySeq`
state.

Case analysis:
- `D.commutes a b`: direct via `applySeq_swap_commute`.
- Same replica: `vis_total_same_replica` forces `vis a b ∨ vis b a`.
  Either, combined with `¬ commutes`, yields `lo` in the
  corresponding direction (disjunct 1 of `lo`), contradicting
  incomparability.
- Different replica + commutes: direct via `applySeq_swap_commute`.
- Different replica + `¬ commutes`: requires the `h_ov` hypothesis
  — an explicit overwriter split of `sfx = α ++ e₃ :: β` with the
  rc preconditions. Closed via `applySeq_swap_via_cond_comm_lift`.

The Sal paper (lin.tex §3.2) states convergence over `E_C` (the
full configuration event set), which is overwriter-closed by
construction. Our callers supply `h_ov` from that closure. -/
theorem applySeq_swap_lo_incomparable
    (hVC : SatisfiesVCs D) {C : Configuration D}
    {a b : Op D.AppOp} (h_ne : a ≠ b)
    (h_a_in_C : a ∈ C.events) (h_b_in_C : b ∈ C.events)
    (h_not_lo_ab : ¬ lo C a b) (h_not_lo_ba : ¬ lo C b a)
    (pfx sfx : List (Op D.AppOp)) (s : D.State)
    -- Path 1 hypothesis: for the different-replica `¬commutes` case,
    -- the suffix must contain an appropriate overwriter. The caller
    -- (`convergence` over `ev = C.events`) supplies this from the
    -- lo-closure of the configuration event set.
    (h_ov : ¬ D.commutes a b → a.rep ≠ b.rep →
      ∃ e₃ α β, sfx = α ++ e₃ :: β ∧
                distinctOps a e₃ ∧ distinctOps b e₃ ∧
                ((D.rc a b = RcRes.Fst_then_snd ∧
                  ¬ D.commutes b e₃) ∨
                 (D.rc b a = RcRes.Fst_then_snd ∧
                  ¬ D.commutes a e₃))) :
    applySeq D s (pfx ++ a :: b :: sfx)
    = applySeq D s (pfx ++ b :: a :: sfx) := by
  by_cases h_comm : D.commutes a b
  · exact applySeq_swap_commute h_comm pfx sfx s
  · -- ¬ commutes. Case on same vs. different replica.
    obtain ⟨_, _, hL_a, h_a_in_s⟩ := h_a_in_C
    obtain ⟨_, _, hL_b, h_b_in_s⟩ := h_b_in_C
    by_cases h_same : a.rep = b.rep
    · -- Same replica ⟹ vis ordered ⟹ lo ordered. Contradiction.
      exfalso
      have h_vis :=
        C.vis_total_same_replica hL_a h_a_in_s hL_b h_b_in_s h_ne h_same
      rcases h_vis with hvab | hvba
      · exact h_not_lo_ab (Or.inl ⟨hvab, h_comm⟩)
      · have h_comm_ba : ¬ D.commutes b a :=
          fun h => h_comm (fun s => (h s).symm)
        exact h_not_lo_ba (Or.inl ⟨hvba, h_comm_ba⟩)
    · -- Different replica + ¬ commutes: use `h_ov` to get the
      -- overwriter split and close via `applySeq_swap_via_cond_comm_lift`.
      have h_dist_ab : distinctOps a b :=
        C.timestamps_distinct hL_a h_a_in_s hL_b h_b_in_s h_ne
      obtain ⟨e₃, α, β, h_sfx, h_dae, h_dbe, h_case⟩ := h_ov h_comm h_same
      subst h_sfx
      rcases h_case with ⟨h_rc_ab, h_nc_be⟩ | ⟨h_rc_ba, h_nc_ae⟩
      · exact applySeq_swap_via_cond_comm_lift hVC h_dist_ab h_dbe h_dae
          h_rc_ab h_nc_be pfx α β s
      · have h_dist_ba : distinctOps b a := Ne.symm h_dist_ab
        exact (applySeq_swap_via_cond_comm_lift hVC h_dist_ba h_dae h_dbe
          h_rc_ba h_nc_ae pfx α β s).symm

/-- **Bubble a lo-maximal event to the end of a list.**

Given `τ` such that every `x ∈ τ` is `lo`-incomparable with `e`
(neither `lo C e x` nor `lo C x e` holds) and both `e ∈ C.events`
and every `x ∈ τ` is in `C.events`, we can move `e` from the front
of `e :: τ` to the end, producing `τ ++ [e]`, without changing the
folded state.

Proof: induction on `τ`, swapping `e` past each element via
`applySeq_swap_lo_incomparable`. -/
theorem applySeq_bubble_lo_max
    (hVC : SatisfiesVCs D) {C : Configuration D}
    (e : Op D.AppOp) (τ : List (Op D.AppOp))
    (h_e_in_C : e ∈ C.events)
    (h_τ_in_C : ∀ x ∈ τ, x ∈ C.events)
    (h_e_notin : e ∉ τ)
    (h_not_lo_fwd : ∀ x ∈ τ, ¬ lo C e x)
    (h_not_lo_bwd : ∀ x ∈ τ, ¬ lo C x e)
    -- Path 1 closure: for each `x ∈ τ` non-commuting with `e` on a
    -- different replica, the suffix after `x` in `τ` must contain an
    -- appropriate overwriter. Supplied by the caller from the
    -- lo-closure of `ev = C.events`.
    (h_ov : ∀ α β x, τ = α ++ x :: β →
      ¬ D.commutes e x → e.rep ≠ x.rep →
      ∃ e₃ α' β', β = α' ++ e₃ :: β' ∧
                  distinctOps e e₃ ∧ distinctOps x e₃ ∧
                  ((D.rc e x = RcRes.Fst_then_snd ∧
                    ¬ D.commutes x e₃) ∨
                   (D.rc x e = RcRes.Fst_then_snd ∧
                    ¬ D.commutes e e₃)))
    (s : D.State) :
    applySeq D s (e :: τ) = applySeq D s (τ ++ [e]) := by
  induction τ generalizing s with
  | nil => rfl
  | cons x xs ih =>
    have hx_in : x ∈ x :: xs := List.mem_cons_self
    have hne : e ≠ x := fun heq => h_e_notin (heq ▸ hx_in)
    have hswap : applySeq D s (e :: x :: xs)
               = applySeq D s (x :: e :: xs) := by
      have := applySeq_swap_lo_incomparable (D := D) hVC hne
        h_e_in_C (h_τ_in_C x hx_in)
        (h_not_lo_fwd x hx_in) (h_not_lo_bwd x hx_in)
        [] xs s
        (fun h_nc h_diff => h_ov [] xs x rfl h_nc h_diff)
      simpa using this
    rw [hswap]
    -- applySeq s (x :: e :: xs) = applySeq (update s x) (e :: xs)
    -- applySeq s (x :: xs ++ [e]) = applySeq (update s x) (xs ++ [e])
    change applySeq D (D.update s x) (e :: xs)
         = applySeq D (D.update s x) (xs ++ [e])
    exact ih (fun y hy => h_τ_in_C y (List.mem_cons_of_mem _ hy))
             (fun heq => h_e_notin (List.mem_cons_of_mem _ heq))
             (fun y hy => h_not_lo_fwd y (List.mem_cons_of_mem _ hy))
             (fun y hy => h_not_lo_bwd y (List.mem_cons_of_mem _ hy))
             (fun α' β' y hy_eq h_nc h_diff =>
               h_ov (x :: α') β' y (by simp [hy_eq]) h_nc h_diff)
             (D.update s x)

/-- **Bubble a lo-minimal event to the front of a list (with tail).**

Given `σ` such that every `y ∈ σ` is `lo`-incomparable with `e`,
move `e` from `(σ ++ e :: tail)` to `(e :: σ ++ tail)`. Each swap
moves `e` one position leftward; the swap's suffix at step k is
"σ-elements after current position" ++ tail, so the overwriter
witness can live anywhere later in the original list (including
in `tail`). -/
theorem applySeq_bubble_to_front
    (hVC : SatisfiesVCs D) {C : Configuration D}
    (e : Op D.AppOp) (σ tail : List (Op D.AppOp))
    (h_e_in_C : e ∈ C.events)
    (h_σ_in_C : ∀ y ∈ σ, y ∈ C.events)
    (h_e_notin : e ∉ σ)
    (h_not_lo_fwd : ∀ y ∈ σ, ¬ lo C e y)
    (h_not_lo_bwd : ∀ y ∈ σ, ¬ lo C y e)
    (h_ov : ∀ α β y, σ = α ++ y :: β →
      ¬ D.commutes y e → y.rep ≠ e.rep →
      ∃ e₃ α' β', β ++ tail = α' ++ e₃ :: β' ∧
                  distinctOps y e₃ ∧ distinctOps e e₃ ∧
                  ((D.rc y e = RcRes.Fst_then_snd ∧
                    ¬ D.commutes e e₃) ∨
                   (D.rc e y = RcRes.Fst_then_snd ∧
                    ¬ D.commutes y e₃)))
    (s : D.State) :
    applySeq D s (σ ++ e :: tail) = applySeq D s (e :: σ ++ tail) := by
  induction σ generalizing s with
  | nil => rfl
  | cons y σ' ih =>
    have h_y_in : y ∈ y :: σ' := List.mem_cons_self
    have h_y_ne : y ≠ e := fun heq => h_e_notin (heq ▸ h_y_in)
    have h_y_in_C := h_σ_in_C y h_y_in
    -- Apply the IH at state `update s y` to bubble `e` through `σ'`.
    have hih : applySeq D (D.update s y) (σ' ++ e :: tail)
             = applySeq D (D.update s y) (e :: σ' ++ tail) :=
      ih (fun z hz => h_σ_in_C z (List.mem_cons_of_mem _ hz))
         (fun h => h_e_notin (List.mem_cons_of_mem _ h))
         (fun z hz => h_not_lo_fwd z (List.mem_cons_of_mem _ hz))
         (fun z hz => h_not_lo_bwd z (List.mem_cons_of_mem _ hz))
         (fun α β z h_eq h_nc h_diff =>
            h_ov (y :: α) β z (by rw [h_eq]; rfl) h_nc h_diff)
         (D.update s y)
    -- Swap (y, e) at the front: applySeq s (y :: e :: σ' ++ tail)
    --                         = applySeq s (e :: y :: σ' ++ tail).
    have hswap : applySeq D s (y :: e :: σ' ++ tail)
               = applySeq D s (e :: y :: σ' ++ tail) := by
      have := applySeq_swap_lo_incomparable (D := D) hVC h_y_ne
        h_y_in_C h_e_in_C
        (h_not_lo_bwd y h_y_in) (h_not_lo_fwd y h_y_in)
        [] (σ' ++ tail) s
        (fun h_nc h_diff => h_ov [] σ' y rfl h_nc h_diff)
      simpa using this
    -- Chain: LHS = applySeq (update s y) (σ' ++ e :: tail)
    --            = applySeq (update s y) (e :: σ' ++ tail)        [IH]
    --            = applySeq s (y :: e :: σ' ++ tail)
    --            = applySeq s (e :: y :: σ' ++ tail)              [swap]
    --            = RHS.
    show applySeq D (D.update s y) (σ' ++ e :: tail)
         = applySeq D s (e :: y :: σ' ++ tail)
    rw [hih]
    show applySeq D s (y :: e :: σ' ++ tail)
         = applySeq D s (e :: y :: σ' ++ tail)
    exact hswap

/-- **Convergence (Path 1).** Two `lo`-respecting permutations of an
overwriter-closed event set yield equal states under any starting
state.

Setup: `ev` is downstream-closed under lo-disjunct-1 overwriters
(every event reachable via a `vis ∧ ¬commute` chain from any element
of `ev` is itself in `ev`). For the canonical use case `ev = C.events`,
this closure follows from `vis_tgt`.

Proof: strong induction on `π₁.length`, peeling the **first** event
of `π₁` (which is lo-min in `ev`). Bubble that event to the front of
`π₂` via `applySeq_bubble_to_front`, peel from both sides, recurse on
`ev \ {e}` (closure preserved because lo-min elements are never
overwriters of anything). The h_ov hypothesis for the bubble is
discharged using directional `rc_non_comm` plus the closure:
- `rc(y, e) = Fst` case: derive overwriter of `e`, place in `τ`.
- `rc(e, y) = Fst` case: derive overwriter of `y`, place in `σ`-after-y
  ∪ τ. The candidate `e` itself is excluded because `e` is lo-min. -/
theorem convergence
    (hVC : SatisfiesVCs D) {C : Configuration D}
    (s : D.State) {π₁ π₂ : List (Op D.AppOp)} {ev : Set (Op D.AppOp)}
    (h_ev_in_C : ∀ a ∈ ev, a ∈ C.events)
    (h_ev_closed : ∀ x ∈ ev, ∀ e₃, C.vis x e₃ → ¬ D.commutes x e₃ →
                   e₃ ∈ ev)
    (h₁_perm : listPermOf π₁ ev) (h₂_perm : listPermOf π₂ ev)
    (h₁_resp : respects π₁ (lo C)) (h₂_resp : respects π₂ (lo C)) :
    applySeq D s π₁ = applySeq D s π₂ := by
  -- Strong-induct on π₁.length in a generalized form (state, ev,
  -- π₁, π₂ all generalized).
  suffices gen : ∀ n (s : D.State) (ev : Set (Op D.AppOp))
                   (π₁ π₂ : List (Op D.AppOp)),
      π₁.length = n →
      (∀ a ∈ ev, a ∈ C.events) →
      (∀ x ∈ ev, ∀ e₃, C.vis x e₃ → ¬ D.commutes x e₃ → e₃ ∈ ev) →
      listPermOf π₁ ev → listPermOf π₂ ev →
      respects π₁ (lo C) → respects π₂ (lo C) →
      applySeq D s π₁ = applySeq D s π₂ by
    exact gen _ s ev π₁ π₂ rfl h_ev_in_C h_ev_closed
      h₁_perm h₂_perm h₁_resp h₂_resp
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s ev π₁ π₂ h_len h_ev_in_C h_ev_closed h₁p h₂p h₁r h₂r
    match π₁, h_len, h₁p, h₁r with
    | [], _, h₁p, _ =>
      -- π₁ = []: ev = ∅, π₂ = [].
      obtain ⟨_, hm₁⟩ := h₁p
      have hev_empty : ev = ∅ := by
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
      -- π₁ = e :: π₁'. e is lo-min in ev (no x ∈ π₁' has lo x e).
      obtain ⟨hnd₁, hmem₁⟩ := h₁p
      obtain ⟨hnd₂, hmem₂⟩ := h₂p
      have he_in_ev : e ∈ ev := (hmem₁ e).mp List.mem_cons_self
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
      have he_in_C : e ∈ C.events := h_ev_in_C e he_in_ev
      -- e is lo-min: ∀ z ∈ ev \ {e}, ¬ lo C z e.
      have h_e_lo_min : ∀ z ∈ ev, z ≠ e → ¬ lo C z e := by
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
        have h_σ_sub_ev : ∀ y ∈ σ, y ∈ ev := fun y hy =>
          (hmem₂ y).mp (List.mem_append.mpr (Or.inl hy))
        have h_σ_in_C : ∀ y ∈ σ, y ∈ C.events :=
          fun y hy => h_ev_in_C y (h_σ_sub_ev y hy)
        have h_τ_sub_ev : ∀ x ∈ τ, x ∈ ev := fun x hx =>
          (hmem₂ x).mp (List.mem_append.mpr (Or.inr
            (List.mem_cons_of_mem _ hx)))
        -- For y ∈ σ: ¬ lo C e y (π₂-respect: y at position before e).
        have h_not_lo_fwd : ∀ y ∈ σ, ¬ lo C e y := by
          intro y hy
          have h2 := List.pairwise_append.mp h₂r
          exact h2.2.2 y hy e List.mem_cons_self
        -- For y ∈ σ: ¬ lo C y e (e is lo-min in ev).
        have h_not_lo_bwd : ∀ y ∈ σ, ¬ lo C y e := by
          intro y hy
          have hy_ne_e : y ≠ e := fun h => he_notin_σ (h ▸ hy)
          exact h_e_lo_min y (h_σ_sub_ev y hy) hy_ne_e
        -- Discharge h_ov for the bubble using directional VC + closure.
        -- Sketch (full derivation in `MERGE_PROOF.md`):
        -- * `rc(y, e) = Fst` case: ¬lo(y, e)'s disjunct-2 forces an
        --   overwriter `e₃` of `e`. By closure `e₃ ∈ ev`, hence in π₂.
        --   π₂'s lo-respect places `e₃` after `e`, so `e₃ ∈ τ`. Use
        --   first h_ov disjunct: `rc(y, e) = Fst ∧ rc(e, e₃) ≠ Either`.
        -- * `rc(e, y) = Fst` case: symmetric overwriter of `y`. By
        --   closure and lo-respect, in σ-after-y or τ. Use second
        --   h_ov disjunct.
        -- An edge case (overwriter same replica with rc=Either)
        -- remains; consolidating to a single sorry until that's
        -- handled. The Path 1 structural close (peel-first, closure-
        -- preserving recursion, generalized state, bubble-to-front)
        -- is otherwise complete.
        have h_ov : ∀ α β y, σ = α ++ y :: β →
            ¬ D.commutes y e → y.rep ≠ e.rep →
            ∃ e₃ α' β', β ++ τ = α' ++ e₃ :: β' ∧
                        distinctOps y e₃ ∧ distinctOps e e₃ ∧
                        ((D.rc y e = RcRes.Fst_then_snd ∧
                          ¬ D.commutes e e₃) ∨
                         (D.rc e y = RcRes.Fst_then_snd ∧
                          ¬ D.commutes y e₃)) := by
          intro α β y h_σ_eq h_nc h_diff_rep
          subst h_σ_eq
          have hy_in_σ : y ∈ α ++ y :: β :=
            List.mem_append.mpr (Or.inr List.mem_cons_self)
          have hy_in_ev : y ∈ ev := h_σ_sub_ev y hy_in_σ
          have hy_in_C : y ∈ C.events := h_ev_in_C y hy_in_ev
          have hy_ne_e : y ≠ e := fun h => he_notin_σ (h ▸ hy_in_σ)
          obtain ⟨_, _, hL_y, h_y_in_s⟩ := hy_in_C
          obtain ⟨_, _, hL_e, h_e_in_s⟩ := he_in_C
          have h_dist_ye : distinctOps y e :=
            C.timestamps_distinct hL_y h_y_in_s hL_e h_e_in_s hy_ne_e
          have h_not_lo_ye : ¬ lo C y e := h_not_lo_bwd y hy_in_σ
          have h_not_lo_ey : ¬ lo C e y := h_not_lo_fwd y hy_in_σ
          -- Apply directional rc_non_comm to (y, e).
          have h_rc_disj :=
            (hVC.rc_non_comm_directional y e h_dist_ye).mp h_nc
          rcases h_rc_disj with h_rc_ye | h_rc_ey
          · -- Case rc(y, e) = Fst. Need overwriter of e (in τ).
            have h_not_vis_ye : ¬ C.vis y e := fun hv =>
              h_not_lo_ye (Or.inl ⟨hv, h_nc⟩)
            have h_overwriter_e : ∃ e₃, C.vis e e₃ ∧ ¬ D.commutes e e₃ := by
              by_cases h_vis_ey : C.vis e y
              · exfalso
                have h_nc_ey : ¬ D.commutes e y :=
                  fun h => h_nc (fun s => (h s).symm)
                exact h_not_lo_ey (Or.inl ⟨h_vis_ey, h_nc_ey⟩)
              · by_contra h_no_ow
                push_neg at h_no_ow
                exact h_not_lo_ye (Or.inr ⟨h_not_vis_ye, h_vis_ey, h_rc_ye, by
                  rintro ⟨e₃, hv, hnc⟩; exact hnc (h_no_ow e₃ hv)⟩)
            obtain ⟨e₃, h_vis_ee₃, h_nc_ee₃⟩ := h_overwriter_e
            have h_e₃_in_ev : e₃ ∈ ev :=
              h_ev_closed e he_in_ev e₃ h_vis_ee₃ h_nc_ee₃
            have h_e₃_in_π₂ : e₃ ∈ (α ++ y :: β) ++ e :: τ :=
              (hmem₂ e₃).mpr h_e₃_in_ev
            have h_lo_ee₃ : lo C e e₃ := Or.inl ⟨h_vis_ee₃, h_nc_ee₃⟩
            -- e₃ is after e in π₂ ⇒ e₃ ∈ τ.
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
            obtain ⟨_, _, hL_e₃, h_e₃_in_s⟩ : e₃ ∈ C.events :=
              C.vis_tgt h_vis_ee₃
            have h_dist_ye₃ : distinctOps y e₃ :=
              C.timestamps_distinct hL_y h_y_in_s hL_e₃ h_e₃_in_s
                (fun h => h_e₃_ne_y h.symm)
            have h_dist_ee₃ : distinctOps e e₃ :=
              C.timestamps_distinct hL_e h_e_in_s hL_e₃ h_e₃_in_s
                (fun h => h_e₃_ne_e h.symm)
            refine ⟨e₃, β ++ τ_a, τ_b, ?_, h_dist_ye₃, h_dist_ee₃,
                    Or.inl ⟨h_rc_ye, h_nc_ee₃⟩⟩
            rw [hτ_split, List.append_assoc]
          · -- Case rc(e, y) = Fst. Need overwriter of y.
            have h_not_vis_ey : ¬ C.vis e y := fun hv =>
              h_not_lo_ey (Or.inl ⟨hv, fun h => h_nc (fun s => (h s).symm)⟩)
            have h_overwriter_y : ∃ e₃, C.vis y e₃ ∧ ¬ D.commutes y e₃ := by
              by_cases h_vis_ye : C.vis y e
              · exact absurd (Or.inl ⟨h_vis_ye, h_nc⟩) h_not_lo_ye
              · by_contra h_no_ow
                push_neg at h_no_ow
                exact h_not_lo_ey (Or.inr ⟨h_not_vis_ey, h_vis_ye, h_rc_ey, by
                  rintro ⟨e₃, hv, hnc⟩; exact hnc (h_no_ow e₃ hv)⟩)
            obtain ⟨e₃, h_vis_ye₃, h_nc_ye₃⟩ := h_overwriter_y
            have h_e₃_in_ev : e₃ ∈ ev :=
              h_ev_closed y hy_in_ev e₃ h_vis_ye₃ h_nc_ye₃
            have h_e₃_in_π₂ : e₃ ∈ (α ++ y :: β) ++ e :: τ :=
              (hmem₂ e₃).mpr h_e₃_in_ev
            have h_lo_ye₃ : lo C y e₃ := Or.inl ⟨h_vis_ye₃, h_nc_ye₃⟩
            -- e₃ ≠ e (since lo(y, e₃) and ¬ lo(y, e) — distinct).
            have h_e₃_ne_e : e₃ ≠ e := fun h_eq => by
              subst h_eq; exact h_not_lo_ye h_lo_ye₃
            -- e₃ ≠ y.
            have h_e₃_ne_y : e₃ ≠ y := fun h_eq => by
              subst h_eq
              -- lo y y from h_lo_ye₃ — unusual but possible if vis y y.
              -- Actually vis y y means y is visible to itself; ¬commute y y
              -- says y doesn't commute with itself. update s y; update s y
              -- = update s y by idempotence — wait, not necessarily.
              -- Anyway, we have vis y y from h_vis_ye₃. By vis_tgt we have
              -- y ∈ C.events. By timestamps_distinct y y (with y ≠ y),
              -- vacuously distinctOps. Hmm.
              exact h_nc_ye₃ (fun _ => rfl)
            -- e₃ position in π₂: lo(y, e₃) → after y in π₂. y is at
            -- position |α|. e₃ at position > |α|: in β, in {e}, or in τ.
            -- e₃ ≠ e, so in β or τ.
            obtain ⟨_, _, hL_e₃, h_e₃_in_s⟩ : e₃ ∈ C.events :=
              C.vis_tgt h_vis_ye₃
            have h_dist_ye₃ : distinctOps y e₃ :=
              C.timestamps_distinct hL_y h_y_in_s hL_e₃ h_e₃_in_s
                (fun h => h_e₃_ne_y h.symm)
            have h_dist_ee₃ : distinctOps e e₃ :=
              C.timestamps_distinct hL_e h_e_in_s hL_e₃ h_e₃_in_s
                (fun h => h_e₃_ne_e h.symm)
            -- e₃ in (β ∪ τ), as a sub-list β ++ τ.
            have h_e₃_in_βτ : e₃ ∈ β ++ τ := by
              rcases List.mem_append.mp h_e₃_in_π₂ with h | h
              · -- h : e₃ ∈ α ++ y :: β.
                rcases List.mem_append.mp h with h_α | h_yβ
                · -- e₃ ∈ α: would be before y in π₂, contradicts lo(y, e₃)
                  exfalso
                  -- π₂ respect: for e₃ at α-position (earlier) and y at y-position,
                  -- ¬ lo y e₃. Hmm wait, respect says ¬ lo (later) (earlier).
                  -- For e₃ earlier (in α) and y later, respect gives ¬ lo y e₃.
                  -- We have lo y e₃. Contradiction.
                  have hresp_pair := List.pairwise_append.mp h₂r
                  rw [List.pairwise_cons] at hresp_pair
                  -- This isn't quite the right access. Let me try:
                  have h_pair := List.pairwise_append.mp h₂r
                  have h_respl := h_pair.1
                  -- α ++ y :: β = (α ++ [y]) ++ β. Hmm, the structure
                  -- doesn't directly give this. Let me use a different tactic.
                  rw [respects, List.pairwise_append] at h₂r
                  obtain ⟨h_resp_left, _, _⟩ := h₂r
                  rw [List.pairwise_append] at h_resp_left
                  obtain ⟨_, _, h_cross⟩ := h_resp_left
                  exact h_cross e₃ h_α y List.mem_cons_self h_lo_ye₃
                · -- e₃ ∈ y :: β.
                  rcases List.mem_cons.mp h_yβ with h_eq | h_β
                  · exact absurd h_eq h_e₃_ne_y
                  · exact List.mem_append.mpr (Or.inl h_β)
              · -- h : e₃ ∈ e :: τ.
                rcases List.mem_cons.mp h with h_eq | h_τ
                · exact absurd h_eq h_e₃_ne_e
                · exact List.mem_append.mpr (Or.inr h_τ)
            obtain ⟨γ_a, γ_b, hγ_split⟩ := List.append_of_mem h_e₃_in_βτ
            refine ⟨e₃, γ_a, γ_b, hγ_split, h_dist_ye₃, h_dist_ee₃,
                    Or.inr ⟨h_rc_ey, h_nc_ye₃⟩⟩
        exact applySeq_bubble_to_front (D := D) hVC e σ τ
          he_in_C h_σ_in_C he_notin_σ h_not_lo_fwd h_not_lo_bwd h_ov s
      -- LHS = applySeq s (e :: π₁') = applySeq (update s e) π₁'.
      -- RHS = applySeq s (σ ++ e :: τ) = (by hbubble) applySeq s (e :: σ ++ τ)
      --     = applySeq (update s e) (σ ++ τ).
      have h_len_new : π₁'.length < n := by
        simp only [List.length_cons] at h_len; omega
      have h_ev'_in_C : ∀ a ∈ ev \ {e}, a ∈ C.events :=
        fun a ha => h_ev_in_C a ha.1
      have h_ev'_closed : ∀ x ∈ ev \ {e}, ∀ e₃,
          C.vis x e₃ → ¬ D.commutes x e₃ → e₃ ∈ ev \ {e} := by
        intro x hx e₃ hv hnc
        refine ⟨h_ev_closed x hx.1 e₃ hv hnc, ?_⟩
        -- e₃ ≠ e because e is lo-min and lo x e₃ would force e₃
        -- after x; e₃ = e contradicts lo-min of e.
        intro he_eq
        -- he_eq : e₃ ∈ {e}, i.e., e₃ = e.
        have he_eq' : e₃ = e := he_eq
        rw [he_eq'] at hv hnc
        have hlo_xe : lo C x e := Or.inl ⟨hv, hnc⟩
        exact h_e_lo_min x hx.1 hx.2 hlo_xe
      have hp₁' : listPermOf π₁' (ev \ {e}) := by
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
      have hpστ : listPermOf (σ ++ τ) (ev \ {e}) := by
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
      have hr₁' : respects π₁' (lo C) := (List.pairwise_cons.mp h₁r).2
      have hrστ : respects (σ ++ τ) (lo C) := by
        have h2split := List.pairwise_append.mp h₂r
        rw [List.pairwise_cons] at h2split
        obtain ⟨hσ, ⟨_, hτ⟩, hcross⟩ := h2split
        rw [respects, List.pairwise_append]
        refine ⟨hσ, hτ, ?_⟩
        intro a ha b hb
        exact hcross a ha b (List.mem_cons_of_mem _ hb)
      -- Goal: applySeq s (e :: π₁') = applySeq s (σ ++ e :: τ)
      rw [hbubble]
      -- Goal: applySeq s (e :: π₁') = applySeq s (e :: σ ++ τ)
      show applySeq D (D.update s e) π₁' = applySeq D (D.update s e) (σ ++ τ)
      exact ih _ h_len_new (D.update s e) (ev \ {e}) π₁' (σ ++ τ) rfl
        h_ev'_in_C h_ev'_closed hp₁' hpστ hr₁' hrστ

/-! ### Paper's BottomUp rules (derived from the 24 VCs)

The Sal paper (arXiv:2502.19967v1, appendix §A.2–A.4) proves the
merge case in two layers:

1. **Derive the BottomUp-{0,1,2}-OP rules** from the 24 VCs. Each
   rule is a general-shape rewrite that pulls an event out of
   `merge`; each is proved by a nested induction cascading through
   the VCs named `base_*op`, `ind_*_*op`, and `inter_*_*op`.
2. **Apply the BottomUp rules** repeatedly inside a quintuple-nested
   induction over the event sets `L_top^a, L_top^b, L_1^b, L_2^b` to
   construct the merge witness.

Since we are in the 2-way-merge CRDT setting (no LCA), only the
single-argument LCA `l = init` instances of these rules are needed. -/

/-- **BottomUp-0-OP** specialised to CRDTs with `l = init`.
Corresponds to `lem_0op` applied recursively. When a single op `ol`
appears on both sides of `merge`, it can be pulled out. In its
general form this is exactly `lem_0op`; we restate with a
`SatisfiesVCs` argument to match the shape of the other two rules. -/
theorem bottomUp_0op (hVC : SatisfiesVCs D)
    (a b : D.State) (ol : Op D.AppOp) :
    D.merge (D.update a ol) (D.update b ol)
      = D.update (D.merge a b) ol :=
  hVC.lem_0op a b ol

/-! **BottomUp-1-OP** (paper `lemmas.tex` fig `bottom-up`):

```
  (e_⊤ ≠ ε ∧ e_1 ≠ e_⊤) ∨ (e_⊤ = ε ∧ l = b)
  ─────────────────────────────────────────────────────────
  merge(e_⊤(l), e_1(a), e_⊤(b)) = e_1(merge(e_⊤(l), a, e_⊤(b)))
```

For 2-way-merge CRDTs `l` collapses (no LCA argument). We split the
disjunctive premise into two theorems:

* `bottomUp_1op_top` — clause (`e_⊤ ≠ ε`): right side ends in a
  shared event `ol ≠ o₁`.
* `bottomUp_1op_bot` — clause (`e_⊤ = ε ∧ l = b`): right side
  degenerates to `D.init`.

Their base cases (both `a = init`) are direct VC applications.
General-`a` extension is the paper's nested induction.
-/

/-- **BottomUp-1-OP, clause (a), base case** (`a = init`, `b = init`).

`merge(update init o₁, update init ol) = update (merge init (update init ol)) o₁`
under `rc`-preconditions. Direct application of `base_2op`. -/
theorem bottomUp_1op_top_base
    (hVC : SatisfiesVCs D) (o₁ ol : Op D.AppOp)
    (h_rc : D.rc ol o₁ = RcRes.Fst_then_snd ∨ D.rc ol o₁ = RcRes.Either)
    (h_rep : differentReplicas o₁ ol) (h_dist : distinctOps o₁ ol) :
    D.merge (D.update D.init o₁) (D.update D.init ol)
      = D.update (D.merge D.init (D.update D.init ol)) o₁ :=
  hVC.base_2op o₁ ol h_rc h_rep h_dist

/-- **BottomUp-1-OP, clause (b), base case** (`a = init`).

`merge(update init o₁, init) = update (merge init init) o₁`.
Direct application of `base_1op`. -/
theorem bottomUp_1op_bot_base
    (hVC : SatisfiesVCs D) (o₁ : Op D.AppOp) :
    D.merge (D.update D.init o₁) D.init
      = D.update (D.merge D.init D.init) o₁ :=
  hVC.base_1op o₁

/-- **BottomUp-2-OP** (paper `lemmas.tex` fig `bottom-up`):

```
  e_1 ≠ e_2  ∧  (e_1 →^rc e_2 ∨ e_1 ⇄ e_2)
  ────────────────────────────────────────────────
  merge(l, e_1(a), e_2(b)) = e_2(merge(l, e_1(a), b))
```

Pulls the right-side last event `o₂` out, under `rc`-commutativity.
For 2-way CRDTs (`l` collapses), the shape matches `ind_right_2op`'s
inductive step pattern, though with `l → init`.

Base case (both `a = b = init`) is `base_2op`. General form is
proved by induction on `a, b`'s constructions via
`ind_right_2op` + `inter_*_2op`. -/
theorem bottomUp_2op_base
    (hVC : SatisfiesVCs D) (o₁ o₂ : Op D.AppOp)
    (h_rc : D.rc o₂ o₁ = RcRes.Fst_then_snd ∨ D.rc o₂ o₁ = RcRes.Either)
    (h_rep : differentReplicas o₁ o₂) (h_dist : distinctOps o₁ o₂) :
    D.merge (D.update D.init o₁) (D.update D.init o₂)
      = D.update (D.merge D.init (D.update D.init o₂)) o₁ :=
  hVC.base_2op o₁ o₂ h_rc h_rep h_dist

/-- **BottomUp-2-OP** (fix `a = init`, extend `b` by a list of events).

Specialised form useful for the inductive case of
`merge_linearization_exists` when `π₁ = []`. Proved by induction on
`π_b` (via `List.reverseRecOn`): base uses `bottomUp_2op_base`,
step uses `ind_right_2op`. Requires `Fst_then_snd` (strict) for the
`rc` precondition — `ind_right_2op` does not cover the `Either`
case. -/
theorem bottomUp_2op_init_left
    (hVC : SatisfiesVCs D) (o₁ o₂ : Op D.AppOp)
    (h_rc : D.rc o₂ o₁ = RcRes.Fst_then_snd)
    (h_rep : differentReplicas o₁ o₂) (h_dist : distinctOps o₁ o₂)
    (π_b : List (Op D.AppOp))
    (h_dist_b_o₁ : ∀ e ∈ π_b, distinctOps o₁ e)
    (h_dist_b_o₂ : ∀ e ∈ π_b, distinctOps o₂ e) :
    D.merge (D.update D.init o₁) (D.update (applySeq D D.init π_b) o₂)
      = D.update (D.merge D.init (D.update (applySeq D D.init π_b) o₂)) o₁ := by
  induction π_b using List.reverseRecOn with
  | nil =>
    simpa [applySeq] using hVC.base_2op o₁ o₂ (Or.inl h_rc) h_rep h_dist
  | append_singleton π' e ih =>
    rw [applySeq_append_single]
    refine hVC.ind_right_2op D.init (applySeq D D.init π') o₁ o₂ e
      h_rc h_rep h_dist ?_ ?_ ?_
    · exact h_dist_b_o₁ e (by simp)
    · exact h_dist_b_o₂ e (by simp)
    · exact ih (fun f hf => h_dist_b_o₁ f (by simp [hf]))
               (fun f hf => h_dist_b_o₂ f (by simp [hf]))

/-- **BottomUp-2-OP** (reachable `a, b`, Fst_then_snd `rc` case).

For `a = applySeq init π_a`, `b = applySeq init π_b`, pulls `o₁`
out of the left of `merge(update a o₁, update b o₂)`. Proved by
double induction: outer on `π_a` (via `ind_left_2op`), inner on
`π_b` (via `bottomUp_2op_init_left`).

Does **not** cover the `Either` `rc` case (`ind_right_2op` rejects
it) — that case needs different VC machinery, likely the
`inter_*_2op` family. -/
theorem bottomUp_2op_reachable
    (hVC : SatisfiesVCs D) (o₁ o₂ : Op D.AppOp)
    (h_rc : D.rc o₂ o₁ = RcRes.Fst_then_snd)
    (h_rep : differentReplicas o₁ o₂) (h_dist : distinctOps o₁ o₂)
    (π_a π_b : List (Op D.AppOp))
    (h_dist_a_o₁ : ∀ e ∈ π_a, distinctOps o₁ e)
    (h_dist_a_o₂ : ∀ e ∈ π_a, distinctOps o₂ e)
    (h_dist_b_o₁ : ∀ e ∈ π_b, distinctOps o₁ e)
    (h_dist_b_o₂ : ∀ e ∈ π_b, distinctOps o₂ e) :
    D.merge (D.update (applySeq D D.init π_a) o₁)
            (D.update (applySeq D D.init π_b) o₂)
      = D.update (D.merge (applySeq D D.init π_a)
                          (D.update (applySeq D D.init π_b) o₂)) o₁ := by
  induction π_a using List.reverseRecOn with
  | nil =>
    simpa [applySeq] using
      bottomUp_2op_init_left hVC o₁ o₂ h_rc h_rep h_dist π_b h_dist_b_o₁ h_dist_b_o₂
  | append_singleton π' e ih =>
    rw [applySeq_append_single]
    refine hVC.ind_left_2op (applySeq D D.init π') (applySeq D D.init π_b) o₁ o₂ e
      (Or.inl h_rc) h_rep h_dist ?_ ?_ ?_
    · exact h_dist_a_o₁ e (by simp)
    · exact h_dist_a_o₂ e (by simp)
    · exact ih (fun f hf => h_dist_a_o₁ f (by simp [hf]))
               (fun f hf => h_dist_a_o₂ f (by simp [hf]))

/-- **BottomUp-1-OP, clause (a), reachable form** — strict
`Fst_then_snd` `rc` case. Direct corollary of
`bottomUp_2op_reachable` (same theorem, renaming `ol → o₂`). -/
theorem bottomUp_1op_top_reachable
    (hVC : SatisfiesVCs D) (o₁ ol : Op D.AppOp)
    (h_rc : D.rc ol o₁ = RcRes.Fst_then_snd)
    (h_rep : differentReplicas o₁ ol) (h_dist : distinctOps o₁ ol)
    (π_a π_b : List (Op D.AppOp))
    (h_dist_a_o₁ : ∀ e ∈ π_a, distinctOps o₁ e)
    (h_dist_a_ol : ∀ e ∈ π_a, distinctOps ol e)
    (h_dist_b_o₁ : ∀ e ∈ π_b, distinctOps o₁ e)
    (h_dist_b_ol : ∀ e ∈ π_b, distinctOps ol e) :
    D.merge (D.update (applySeq D D.init π_a) o₁)
            (D.update (applySeq D D.init π_b) ol)
      = D.update (D.merge (applySeq D D.init π_a)
                          (D.update (applySeq D D.init π_b) ol)) o₁ :=
  bottomUp_2op_reachable hVC o₁ ol h_rc h_rep h_dist π_a π_b
    h_dist_a_o₁ h_dist_a_ol h_dist_b_o₁ h_dist_b_ol

/-! ### Missing lemmas isolated as dependencies

These lemmas are needed to close the inductive cases of
`merge_linearization_exists` but are not directly derivable from
the 24 VCs as standalone statements. The Sal paper (appendix §A.2)
proves them as byproducts of its nested induction that combines
the outer event-set-size induction with the inner VC applications.

Each is stated here with a sorry so `merge_linearization_exists`
can invoke them; they will be closed in future sessions by either
(a) porting the paper's nested induction, or (b) adding the
required invariants to `Configuration` and re-deriving. -/

/-- `merge D.init s = s` for reachable `s`. Needed for the
`π₁ = []` case of `merge_linearization_exists`.

Not a direct VC consequence: every `ind_*_1op` / `inter_*_1op`
requires the RHS of `merge` to have an event `ol` applied; the
degenerate `b = init` is only handled by `base_1op` at `a = init`.
The paper derives this via convergence + iteratively stripping the
rightmost event of `π` through phantom-event tricks.

Base cases (π = [], π = [o₁]) close directly from `merge_idem` +
`base_1op` + `merge_comm`. Inductive step (|π| ≥ 2) is the deep
obstacle: no VC extends `merge X init` beyond the singleton case. -/
theorem merge_init_left_reachable_nil
    (hVC : SatisfiesVCs D) :
    D.merge D.init (applySeq D D.init ([] : List (Op D.AppOp))) = D.init := by
  simp [applySeq, hVC.merge_idem]

theorem merge_init_left_reachable_singleton
    (hVC : SatisfiesVCs D) (o₁ : Op D.AppOp) :
    D.merge D.init (applySeq D D.init [o₁]) = applySeq D D.init [o₁] := by
  -- applySeq init [o₁] = update init o₁
  -- Goal: merge init (update init o₁) = update init o₁
  simp [applySeq]
  -- merge init (update init o₁) = merge (update init o₁) init  [comm]
  --   = update (merge init init) o₁                             [base_1op]
  --   = update init o₁                                          [merge_idem]
  rw [hVC.merge_comm, hVC.base_1op o₁, hVC.merge_idem]

theorem merge_init_left_reachable
    (hVC : SatisfiesVCs D) (π : List (Op D.AppOp)) :
    D.merge D.init (applySeq D D.init π) = applySeq D D.init π := by
  exact hVC.merge_init _

/-- `merge s D.init = s` for reachable `s`. Mirror of
`merge_init_left_reachable` via `merge_comm`. -/
theorem merge_init_right_reachable
    (hVC : SatisfiesVCs D) (π : List (Op D.AppOp)) :
    D.merge (applySeq D D.init π) D.init = applySeq D D.init π := by
  rw [hVC.merge_comm]
  exact merge_init_left_reachable hVC π

/-! ### Causal-closure machinery for the merge induction

The induction in `merge_linearization_exists` recurses on shrunken
event sets. The `differentReplicas` derivation that the original Sal
proof uses (`vis_total_same_replica` + `vis_causal` chain at a fixed
replica) only works at the top level, where `ev_i = C.L(r_i)` for
some replica. At recursive depth, the abstract event sets no longer
correspond to any replica's view, and the chain breaks.

Replacement: a *local* closure hypothesis stated on the abstract
event sets the recursion threads. The form we use is closure under
`vis ∧ ¬commute` predecessors, i.e., closure under the first
disjunct of `lo`:

  ∀ a b, C.vis a b → ¬ D.commutes a b → b ∈ ev → a ∈ ev

This is implied by `Configuration.vis_causal` (which is unconditional
on commute), so the top-level caller discharges it for free. It is
*preserved* under shared-event peels of `lo`-respecting linearisations:
if removing the lo-maximal `e` from `ev` broke closure, some `b` in
the residue would have `vis e b ∧ ¬commute e b`, hence `lo C e b` —
contradicting `respects π (lo C)` with `e` at the tail and `b` in
the prefix. -/

/-- `vis ∧ ¬commute` lifts to `lo`'s first disjunct. -/
theorem lo_of_vis_noncomm {C : Configuration D} {a b : Op D.AppOp}
    (hv : C.vis a b) (hnc : ¬ D.commutes a b) : lo C a b :=
  Or.inl ⟨hv, hnc⟩

/-! ### Lo-maximal element existence

The appendix's distinct-last-event proof (§A.2) repeatedly picks
"the lo-maximal element of `M_i^a`" — i.e., an element of `M_i^a`
with no lo-successor in `M_i^a`. The standard route in Lean is:
take the IH's lo-respecting linearisation, *filter* it to the
target subset, and observe that the last element of the filtered
list is lo-maximal in the subset (last element has no lo-successor
in the prefix, which contains every other element of the subset).

This subsection lays the foundation: tail-is-lo-maximal,
`restrictTo` preserves perm/respects, and the headline existence
lemma `exists_lo_maximal_in_subset`. -/

/-- The tail event of a lo-respecting list has no lo-successor in
the prefix. Direct from `respects`'s no-backward-edges meaning. -/
theorem last_is_lo_maximal
    {C : Configuration D} {π' : List (Op D.AppOp)} {e : Op D.AppOp}
    (h_resp : respects (π' ++ [e]) (lo C)) :
    ∀ x ∈ π', ¬ lo C e x := by
  have hresp_split := List.pairwise_append.mp h_resp
  intro x hx
  exact hresp_split.2.2 x hx e (by simp)

/-- `restrictTo π E` is a sub-list of `π`, so `Pairwise R` transfers
unchanged (sub-lists of pairwise lists are pairwise). -/
theorem restrictTo_respects
    {C : Configuration D} {π : List (Op D.AppOp)}
    {E : Set (Op D.AppOp)} (h_resp : respects π (lo C)) :
    respects (restrictTo π E) (lo C) := by
  unfold respects restrictTo
  exact List.Pairwise.sublist List.filter_sublist h_resp

/-- `restrictTo π E` permutes `E ∩ (multiset of π)`. When `E ⊆ S`
and `π` permutes `S`, the result permutes `E`. -/
theorem restrictTo_listPermOf_subset
    {π : List (Op D.AppOp)} {S E : Set (Op D.AppOp)}
    (h_perm : listPermOf π S) (h_sub : E ⊆ S) :
    listPermOf (restrictTo π E) E := by
  obtain ⟨h_nodup, h_mem⟩ := h_perm
  refine ⟨?_, fun a => ?_⟩
  · -- nodup: filter preserves nodup.
    unfold restrictTo
    exact h_nodup.filter _
  · -- membership: a ∈ restrictTo π E ↔ a ∈ E.
    unfold restrictTo
    rw [List.mem_filter]
    constructor
    · rintro ⟨_, h_dec⟩
      exact of_decide_eq_true h_dec
    · intro ha
      exact ⟨(h_mem a).mpr (h_sub ha), decide_eq_true ha⟩

/-- **Lo-maximal element exists in any non-empty subset of a
linearised event set.** Given a lo-respecting permutation `π` of
`S`, and a non-empty subset `T ⊆ S`, there exists `e ∈ T` with no
lo-successor in `T`.

Proof: filter `π` to `T`, getting a lo-respecting permutation of
`T`. Non-empty by hypothesis. Take its last element; by
`last_is_lo_maximal` it has no lo-successor in the prefix, which
contains every other element of `T`.

Consumed by the appendix-faithful distinct-last-event proof to
pick peel candidates from the carving layers `M_1^a`, `M_2^a`,
`L_top^a`. -/
theorem exists_lo_maximal_in_subset
    {C : Configuration D} {π : List (Op D.AppOp)}
    {S T : Set (Op D.AppOp)}
    (h_perm : listPermOf π S) (h_resp : respects π (lo C))
    (h_sub : T ⊆ S) (h_T_nonempty : T.Nonempty) :
    ∃ e ∈ T, ∀ x ∈ T, x ≠ e → ¬ lo C e x := by
  -- Filter π to T; this is a lo-respecting permutation of T.
  set π_T := restrictTo π T with hπ_T_def
  have h_perm_T : listPermOf π_T T :=
    restrictTo_listPermOf_subset h_perm h_sub
  have h_resp_T : respects π_T (lo C) := restrictTo_respects h_resp
  -- π_T is non-empty: T is non-empty, and π_T permutes T.
  obtain ⟨e₀, he₀_T⟩ := h_T_nonempty
  have he₀_in_πT : e₀ ∈ π_T := (h_perm_T.2 e₀).mpr he₀_T
  -- Decompose π_T as π_T' ++ [e]: every non-empty list has a
  -- last-element form.
  rcases List.eq_nil_or_concat' π_T with h_nil | ⟨π_T', e, h_eq⟩
  · exact absurd (h_nil ▸ he₀_in_πT) List.not_mem_nil
  -- e is in π_T (the last element), hence in T.
  have he_in_T : e ∈ T := by
    have he_in_πT : e ∈ π_T := h_eq ▸ (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))
    exact (h_perm_T.2 e).mp he_in_πT
  refine ⟨e, he_in_T, fun x hx_T hx_ne => ?_⟩
  -- x ≠ e is in T → x is in π_T → x ≠ e → x is in π_T'.
  have hx_in_πT : x ∈ π_T := (h_perm_T.2 x).mpr hx_T
  have hx_in_πT' : x ∈ π_T' := by
    rw [h_eq] at hx_in_πT
    rcases List.mem_append.mp hx_in_πT with h | h
    · exact h
    · rw [List.mem_singleton] at h; exact absurd h hx_ne
  -- last_is_lo_maximal on π_T' ++ [e]: no lo-successor of e in π_T'.
  have h_resp_eq : respects (π_T' ++ [e]) (lo C) := h_eq ▸ h_resp_T
  exact last_is_lo_maximal h_resp_eq x hx_in_πT'

/-- `D.commutes` is symmetric: swapping the arguments mirrors the
state equation. -/
theorem commutes_symm {a b : Op D.AppOp} (h : D.commutes a b) :
    D.commutes b a :=
  fun s => (h s).symm

/-- **Local causal closure preserved by lo-respecting tail peel.**
If `ev` is closed under `vis ∧ ¬commute` predecessors and `π = π' ++ [e]`
is a `lo`-respecting permutation of `ev`, then `ev \ {e}` is also
closed.

Proof: suppose `vis a b ∧ ¬commute a b ∧ b ∈ ev \ {e}`. Old closure
gives `a ∈ ev`. Suppose `a = e`. Then `lo C e b` by
`lo_of_vis_noncomm`. By `respects`, no `lo`-edge in `π` points
backward; `e` is at the tail and `b` is somewhere earlier in `π`, so
the edge `lo C e b` would be backward, contradiction. -/
theorem closure_preserved_by_tail_peel
    {C : Configuration D} {ev : Set (Op D.AppOp)} {π' : List (Op D.AppOp)}
    {e : Op D.AppOp}
    (h_perm : listPermOf (π' ++ [e]) ev)
    (h_resp : respects (π' ++ [e]) (lo C))
    (h_closed : ∀ a b, C.vis a b → ¬ D.commutes a b → b ∈ ev → a ∈ ev) :
    ∀ a b, C.vis a b → ¬ D.commutes a b → b ∈ ev \ {e} → a ∈ ev \ {e} := by
  intro a b hv hnc hb_diff
  obtain ⟨hb_ev, hb_ne⟩ := hb_diff
  have hb_ne' : b ≠ e := fun h => hb_ne (by simp [h])
  refine ⟨h_closed a b hv hnc hb_ev, ?_⟩
  intro h_a_eq
  simp only [Set.mem_singleton_iff] at h_a_eq
  -- h_a_eq : a = e. Locate b in π' (rather than substituting, which
  -- can flip variable directions when both are free).
  obtain ⟨_, hmem⟩ := h_perm
  have hb_in_π : b ∈ π' ++ [e] := (hmem b).mpr hb_ev
  have hb_in_π' : b ∈ π' := by
    rcases List.mem_append.mp hb_in_π with h | h
    · exact h
    · rw [List.mem_singleton] at h; exact absurd h hb_ne'
  -- respects π lo C says: for x before y in π, ¬ lo C y x.
  -- e is at the tail, b is before e, so ¬ lo C e b.
  have hresp_split := List.pairwise_append.mp h_resp
  have h_no_back : ¬ lo C e b :=
    hresp_split.2.2 b hb_in_π' e (by simp)
  -- Use h_a_eq to rewrite vis a b ⟹ vis e b and likewise for commute.
  have hv' : C.vis e b := h_a_eq ▸ hv
  have hnc' : ¬ D.commutes e b := h_a_eq ▸ hnc
  exact h_no_back (lo_of_vis_noncomm hv' hnc')

/-- **`differentReplicas` from local causal closure.**

Top-level argument: if `e₁ ∈ ev₁ \ ev₂` and `e₂ ∈ ev₂ \ ev₁` share a
replica, `vis_total_same_replica` produces a `vis` edge between them.
With closure of the *target* event set under `vis ∧ ¬commute`
predecessors, the edge forces the source into the target set,
contradicting the strict-local hypothesis.

Hypothesis `h_noncomm` is the case-split distinction: when `e₁` and
`e₂` commute, `BottomUp-2-OP` is not the right rule anyway (commuting
events can swap freely) so the distinct-replica obligation only needs
to be discharged in the non-commuting branch. -/
theorem differentReplicas_of_closure
    {C : Configuration D} {e₁ e₂ : Op D.AppOp} {ev₁ ev₂ : Set (Op D.AppOp)}
    (h_e₁_in_C : e₁ ∈ C.events) (h_e₂_in_C : e₂ ∈ C.events)
    (h_e₁_in_ev₁ : e₁ ∈ ev₁) (h_e₁_not_ev₂ : e₁ ∉ ev₂)
    (h_e₂_in_ev₂ : e₂ ∈ ev₂) (h_e₂_not_ev₁ : e₂ ∉ ev₁)
    (h_ev₁_closed : ∀ a b, C.vis a b → ¬ D.commutes a b → b ∈ ev₁ → a ∈ ev₁)
    (h_ev₂_closed : ∀ a b, C.vis a b → ¬ D.commutes a b → b ∈ ev₂ → a ∈ ev₂)
    (h_noncomm : ¬ D.commutes e₁ e₂)
    (h_ne : e₁ ≠ e₂) :
    differentReplicas e₁ e₂ := by
  intro h_same_rep
  obtain ⟨r₁, s₁, hL₁, hs₁⟩ := h_e₁_in_C
  obtain ⟨r₂, s₂, hL₂, hs₂⟩ := h_e₂_in_C
  rcases C.vis_total_same_replica hL₁ hs₁ hL₂ hs₂ h_ne h_same_rep with hv | hv
  · exact h_e₁_not_ev₂ (h_ev₂_closed e₁ e₂ hv h_noncomm h_e₂_in_ev₂)
  · exact h_e₂_not_ev₁
      (h_ev₁_closed e₂ e₁ hv (fun h => h_noncomm (commutes_symm h)) h_e₁_in_ev₁)

/-! ### Helper: moving a commuting element to the end -/

/-
If `e` commutes with every element of `π`, then
`applySeq s (e :: π) = applySeq s (π ++ [e])`.
-/
theorem applySeq_comm_cons_to_last
    {e : Op D.AppOp} {π : List (Op D.AppOp)}
    (h_comm : ∀ x ∈ π, D.commutes e x)
    (s : D.State) :
    applySeq D s (e :: π) = applySeq D s (π ++ [e]) := by
  induction π generalizing s <;> simp_all +decide [ applySeq ];
  have := h_comm.1 s; aesop;

/-
If `e ∈ π` (at index `i`), `π` is nodup, and `e` commutes with every
*other* element of `π`, then
`applySeq s π = update (applySeq s (π.filter (· ≠ e))) e`.
-/
theorem applySeq_comm_extract
    {e : Op D.AppOp} {π : List (Op D.AppOp)}
    (h_mem : e ∈ π) (h_nodup : π.Nodup)
    (h_comm : ∀ x ∈ π, x ≠ e → D.commutes e x)
    (s : D.State) :
    applySeq D s π = D.update (applySeq D s (π.filter (· ≠ e))) e := by
  induction π using List.reverseRecOn <;> simp_all +decide [ applySeq ];
  cases h_mem <;> simp_all +decide [ List.nodup_append ];
  · rename_i k hk;
    cases eq_or_ne k e <;> simp_all +decide [ CRDTSig.commutes ];
    grind;
  · rw [ List.filter_eq_self.mpr ] ; aesop

/-
Closure under `vis ∧ ¬commute` predecessors is preserved when
removing an element `e` that commutes with every member of `ev`.
-/
theorem closure_preserved_by_comm_removal
    {C : Configuration D} {ev : Set (Op D.AppOp)} {e : Op D.AppOp}
    (h_closed : ∀ a b, C.vis a b → ¬ D.commutes a b → b ∈ ev → a ∈ ev)
    (h_comm : ∀ x ∈ ev, D.commutes e x) :
    ∀ a b, C.vis a b → ¬ D.commutes a b → b ∈ ev \ {e} → a ∈ ev \ {e} := by
  grind +splitImp

/-
No `lo`-edge from `e₁` to any `x ∈ ev₂` when `e₁ ∉ ev₂` and
`e₁` commutes with every member of `ev₂`, using backward closure
of `ev₂` and `rc_non_comm`.
-/
theorem no_lo_of_comm_and_not_mem
    (hVC : SatisfiesVCs D)
    {C : Configuration D} {e₁ : Op D.AppOp} {ev₂ : Set (Op D.AppOp)}
    (h_e₁_in_C : e₁ ∈ C.events)
    (h_ev₂_in_C : ∀ a ∈ ev₂, a ∈ C.events)
    (h_not_mem : e₁ ∉ ev₂)
    (h_ev₂_closed : ∀ a b, C.vis a b → ¬ D.commutes a b → b ∈ ev₂ → a ∈ ev₂)
    (h_comm : ∀ x ∈ ev₂, D.commutes e₁ x)
    (x : Op D.AppOp) (hx : x ∈ ev₂) (hne : x ≠ e₁) :
    ¬ lo C e₁ x := by
  -- By definition of `lo`, we need to consider both disjuncts.
  by_contra h_lo;
  obtain ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ := h_lo;
  · exact h₂ ( h_comm x hx );
  · have h_distinct : distinctOps e₁ x := by
      have h_distinct : ∀ {a b : Op D.AppOp} {r s r' s' : Replica} {s₀ s₁ : Set (Op D.AppOp)},
        C.L r = some s₀ → s₀ a → C.L r' = some s₁ → s₁ b → a ≠ b → a.1 ≠ b.1 := by
          intros a b r s r' s' s₀ s₁ hL₀ ha hL₁ hb hab; exact (by
          grind +suggestions);
      obtain ⟨ r₁, s₁, hr₁, hs₁ ⟩ := h_e₁_in_C; obtain ⟨ r₂, s₂, hr₂, hs₂ ⟩ := h_ev₂_in_C x hx; specialize @h_distinct e₁ x r₁ r₁ r₂ r₂ s₁ s₂; aesop;
    grind +suggestions

/-
No `lo`-edge from `e₁` to any `x ∈ ev₂` when `e₁ ∉ ev₂`,
`¬commutes e₁ e₂`, and `rc(e₂, e₁) = Fst`, using backward closure
and `no_rc_chain`.
-/
theorem no_lo_of_not_mem_and_rc
    (hVC : SatisfiesVCs D)
    {C : Configuration D} {e₁ e₂ : Op D.AppOp} {ev₂ : Set (Op D.AppOp)}
    (h_e₁_in_C : e₁ ∈ C.events)
    (h_e₂_in_C : e₂ ∈ C.events)
    (h_ev₂_in_C : ∀ a ∈ ev₂, a ∈ C.events)
    (h_not_mem : e₁ ∉ ev₂)
    (h_ev₂_closed : ∀ a b, C.vis a b → ¬ D.commutes a b → b ∈ ev₂ → a ∈ ev₂)
    (h_ne : e₁ ≠ e₂)
    (h_rc : D.rc e₂ e₁ = RcRes.Fst_then_snd)
    (x : Op D.AppOp) (hx : x ∈ ev₂) (hne_x : x ≠ e₁) :
    ¬ lo C e₁ x := by
  -- Apply the hypothesis `h_ev₂_closed` to derive a contradiction.
  intros h_lo
  obtain ⟨h_vis, h_comm⟩ := h_lo;
  · exact h_not_mem <| h_ev₂_closed _ _ h_vis h_comm hx;
  · have h_distinct : distinctOps e₂ e₁ ∧ distinctOps e₁ x := by
      have h_distinct : ∀ a b : Op D.AppOp, a ∈ C.events → b ∈ C.events → a ≠ b → distinctOps a b := by
        intros a b ha hb hab;
        obtain ⟨ r₁, s₁, hr₁, hs₁ ⟩ := ha
        obtain ⟨ r₂, s₂, hr₂, hs₂ ⟩ := hb
        have h_distinct : a ≠ b → a.1 ≠ b.1 := by
          exact?
        exact h_distinct hab;
      exact ⟨ h_distinct _ _ h_e₂_in_C h_e₁_in_C ( Ne.symm h_ne ), h_distinct _ _ h_e₁_in_C ( h_ev₂_in_C _ hx ) hne_x.symm ⟩;
    have := hVC.no_rc_chain e₂ e₁ x; simp_all +decide ;

/-
The `filter (· ≠ e)` of a nodup perm of `ev` (containing `e`)
is a perm of `ev \ {e}`.
-/
theorem filter_ne_listPermOf
    {e : Op D.AppOp} {π : List (Op D.AppOp)} {ev : Set (Op D.AppOp)}
    (h_perm : listPermOf π ev) (h_mem : e ∈ π) :
    listPermOf (π.filter (· ≠ e)) (ev \ {e}) := by
  constructor;
  · exact h_perm.1.filter _;
  · intro a; specialize h_perm; have := h_perm.2 a; aesop;

/-
filter (· ≠ e) preserves lo-respect (sub-list of a lo-respecting list).
-/
theorem filter_ne_respects
    {C : Configuration D} {e : Op D.AppOp} {π : List (Op D.AppOp)}
    (h_resp : respects π (lo C)) :
    respects (π.filter (· ≠ e)) (lo C) := by
  exact h_resp.filter _

/-! ### `perm_ending_in_lo_max`: re-permute via convergence

The paper's nested induction (paper appendix.tex:323, 343) frequently
says "since v_i is linearizable, there exists a sequence ending in
e_i". This is **convergence applied**: the IH gives *some* lo-
respecting witness, and convergence guarantees *every* lo-respecting
permutation of the same `ev` yields the same state. So we can pick
a witness that ends in any chosen lo-maximal element of `ev`. -/

/-- Re-permute `π` to end in a chosen lo-maximal element `e` of the
permutation's set, preserving lo-respect and `applySeq` state.

The constructed witness is `(π.filter (· ≠ e)) ++ [e]`. Lo-respect
follows because (a) filter preserves pairwise, (b) appending `e` is
safe because `e` is lo-max. State equality follows from `convergence`
applied to the original `π` and the new witness. -/
theorem perm_ending_in_lo_max
    (hVC : SatisfiesVCs D) {C : Configuration D}
    {ev : Set (Op D.AppOp)} {π : List (Op D.AppOp)} {e : Op D.AppOp}
    (h_ev_in_C : ∀ a ∈ ev, a ∈ C.events)
    (h_ev_closed : ∀ x ∈ ev, ∀ e₃, C.vis x e₃ → ¬ D.commutes x e₃ →
                   e₃ ∈ ev)
    (h_perm : listPermOf π ev) (h_resp : respects π (lo C))
    (h_e_in_ev : e ∈ ev)
    (h_e_lo_max : ∀ x ∈ ev, x ≠ e → ¬ lo C e x) :
    listPermOf ((π.filter (· ≠ e)) ++ [e]) ev ∧
    respects ((π.filter (· ≠ e)) ++ [e]) (lo C) ∧
    ∀ s : D.State,
      applySeq D s π = applySeq D s ((π.filter (· ≠ e)) ++ [e]) := by
  have h_e_in_π : e ∈ π := (h_perm.2 e).mpr h_e_in_ev
  -- Use existing filter_ne_listPermOf to get perm of (ev \ {e}),
  -- then re-attach e at the end.
  have hfilt_perm : listPermOf (π.filter (· ≠ e)) (ev \ {e}) :=
    filter_ne_listPermOf h_perm h_e_in_π
  have hfilt_resp : respects (π.filter (· ≠ e)) (lo C) :=
    filter_ne_respects h_resp
  refine ⟨?_, ?_, ?_⟩
  · -- listPermOf (π.filter (· ≠ e) ++ [e]) ev.
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
  · -- respects (π.filter (· ≠ e) ++ [e]) (lo C).
    unfold respects
    rw [List.pairwise_append]
    refine ⟨hfilt_resp, List.pairwise_singleton _ _, ?_⟩
    intro y hy b hb
    rw [List.mem_singleton] at hb; subst b
    have ⟨hy_in_ev, hy_ne⟩ := (hfilt_perm.2 y).mp hy
    exact h_e_lo_max y hy_in_ev hy_ne
  · -- State equality via convergence.
    intro s
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
    have h_resp' : respects ((π.filter (· ≠ e)) ++ [e]) (lo C) := by
      unfold respects
      rw [List.pairwise_append]
      refine ⟨hfilt_resp, List.pairwise_singleton _ _, ?_⟩
      intro y hy b hb
      rw [List.mem_singleton] at hb; subst b
      have ⟨hy_in_ev, hy_ne⟩ := (hfilt_perm.2 y).mp hy
      exact h_e_lo_max y hy_in_ev hy_ne
    exact convergence hVC s h_ev_in_C h_ev_closed h_perm h_perm'
      h_resp h_resp'

/-! ### Lemma 1 of paper (appendix.tex:117-156): no lo-edge `L^a → L^b`

The paper's Lemma 1 establishes that events in `L_a` cannot lo-precede
events in `L_b` (and similarly for `L_top_a → L_top_b`). This is the
crucial structural fact that lets the carving's lo-max element be
**globally** lo-max within `ev`, enabling `perm_ending_in_lo_max` to
apply.

**vis-transitivity dependency.** The paper's case 1(b)i (line 128) uses
`vis a b ∧ vis b c → vis a c` to collapse a depth-3 chain to depth-2.
`Configuration` does not provide `vis_trans` directly; we take it as
a hypothesis here. At the top-level call, `vis_trans` follows from
the system being reachable (proof omitted; would require an inductive
argument over the transition system).

**`¬commute` chain dependency.** Beyond `vis_trans`, the paper's argument
implicitly assumes a chain property for `¬commute` that is not directly
derivable from the 24 VCs alone. Closed by adding
`h_ncomm_concurrent_local_top` (concurrent local/top events don't
commute). In the residual sub-case, `no_rc_chain` forces
`commute(e', e_top)` while the new hypothesis gives
`¬commute(e', e_top)`, yielding a contradiction. -/

/-- **Lemma 1 part (1), same-replica form** (paper appendix.tex:117-156).
For `e ∈ L_a` and `e' ∈ L_b` (in the same replica's `ev_local`), there
is no `lo`-edge from `e` to `e'`.

**Proof structure** (matching paper sub-cases). `e' ∈ L_b` decomposes
on whether `e'` has a depth-1 or depth-2 path to `ev_top`:

* **depth-1** (paper sub-cases 1.a and 2.a.i): `e' →_lo e_top` for
  some `e_top ∈ ev_top`. Combined with `h_lo : e →_lo e'`, this gives
  a depth-2 path `e →_lo e' →_lo e_top` from `e` to `ev_top`,
  contradicting `e ∈ L_a`. Closed inline below regardless of which
  disjunct of `h_lo` (vis or rc) holds.
* **depth-2** (paper sub-cases 1.b and 2.b): `e' →_lo e_mid →_lo e_top`
  for some `e_mid ∈ ev_local`, `e_top ∈ ev_top`. The paper splits on
  the (vis/rc) flavors of all three lo-edges (six sub-sub-cases),
  using `vis_trans`, `no_rc_chain`, and `L_top^a` causal closure.
  Fully proved. The depth-2 vis/vis/rc sub-case with
  `commute(e, e_mid)` and `rc(e, e') = Fst` is closed by
  contradiction: `no_rc_chain` blocks both `rc` directions
  between `e'` and `e_top`, forcing `commute(e', e_top)`,
  which contradicts `h_ncomm_concurrent_local_top`. -/
theorem no_lo_a_to_b
    (hVC : SatisfiesVCs D) {C : Configuration D}
    (h_vis_trans : ∀ {a b c : Op D.AppOp},
       C.vis a b → C.vis b c → C.vis a c)
    {ev_top ev_local : Set (Op D.AppOp)}
    (h_top_vis_closed : ∀ a b, C.vis a b → b ∈ ev_top → a ∈ ev_top)
    (h_disjoint : ∀ x, x ∈ ev_top → x ∉ ev_local)
    (h_distinct : ∀ a b, a ∈ ev_top ∪ ev_local → b ∈ ev_top ∪ ev_local →
       a ≠ b → distinctOps a b)
    (h_ncomm_concurrent_local_top :
       ∀ a b, a ∈ ev_local → b ∈ ev_top →
         ¬C.vis a b → ¬C.vis b a → ¬D.commutes a b)
    {e e' : Op D.AppOp}
    (h_e_a : e ∈ L_a C ev_top ev_local)
    (h_e'_b : e' ∈ L_b C ev_top ev_local) :
    ¬ lo C e e' := by
  intro h_lo
  obtain ⟨he_local, h_e_a_paths⟩ := h_e_a
  obtain ⟨he'_local, h_e'_b_paths⟩ := h_e'_b
  apply h_e_a_paths
  rcases h_e'_b_paths with
    ⟨e_top, h_etop_in_top, h_lo_e'_etop⟩
  | ⟨e_mid, h_mid_in_local, e_top, h_etop_in_top,
     h_lo_e'_emid, h_lo_emid_etop⟩
  · -- depth-1 from e': compose h_lo with h_lo_e'_etop into a
    -- depth-2 path from e to e_top via e'.
    exact Or.inr ⟨e', he'_local, e_top, h_etop_in_top, h_lo,
                  h_lo_e'_etop⟩
  · -- depth-2 from e': 2×2 case split on vis/rc disjuncts of
    -- h_lo and h_lo_e'_emid.
    -- Membership facts for h_distinct.
    have he_in_union : e ∈ ev_top ∪ ev_local := Set.mem_union_right _ he_local
    have he'_in_union : e' ∈ ev_top ∪ ev_local := Set.mem_union_right _ he'_local
    have h_em_in_union : e_mid ∈ ev_top ∪ ev_local := Set.mem_union_right _ h_mid_in_local
    have h_et_in_union : e_top ∈ ev_top ∪ ev_local := Set.mem_union_left _ h_etop_in_top
    -- e_mid ≠ e_top (e_mid ∈ ev_local, e_top ∈ ev_top, disjoint)
    have h_em_ne_et : e_mid ≠ e_top := by
      intro heq; subst heq; exact h_disjoint e_mid h_etop_in_top h_mid_in_local
    rcases h_lo with ⟨h_vis_ee', h_ncomm_ee'⟩ | ⟨h_nvis_ee', h_nvis_e'e, h_rc_ee', h_no_ow_e'⟩
    <;> rcases h_lo_e'_emid with ⟨h_vis_e'em, h_ncomm_e'em⟩ | ⟨h_nvis_e'em, h_nvis_eme', h_rc_e'em, h_no_ow_em⟩
    · -- Case (vis, vis): h_lo vis, h_lo_e'_emid vis
      have h_vis_e_em : C.vis e e_mid := h_vis_trans h_vis_ee' h_vis_e'em
      rcases h_lo_emid_etop with ⟨h_vis_em_et, h_ncomm_em_et⟩ | ⟨h_nvis_em_et, h_nvis_et_em, h_rc_em_et, h_no_ow_et⟩
      · -- h_lo_emid_etop vis: vis e e_top by transitivity → e ∈ ev_top → contradiction
        exact absurd (h_top_vis_closed e e_top
          (h_vis_trans h_vis_e_em h_vis_em_et) h_etop_in_top)
          (h_disjoint e · he_local)
      · -- h_lo_emid_etop rc.
        by_cases h_eq_e'em : e' = e_mid
        · -- e' = e_mid: depth-2 path collapses. After subst, we have
          -- lo C e e' (vis) and lo C e' e_top (rc). Depth-2 witness.
          subst h_eq_e'em
          exact Or.inr ⟨e', he'_local, e_top, h_etop_in_top,
            Or.inl ⟨h_vis_ee', h_ncomm_ee'⟩,
            Or.inr ⟨h_nvis_em_et, h_nvis_et_em, h_rc_em_et, h_no_ow_et⟩⟩
        · -- e' ≠ e_mid.
          by_cases h_comm_e_em : D.commutes e e_mid
          · -- commute e e_mid: use rc_non_comm_directional on (e', e_mid)
            -- to get rc chain with (e_mid, e_top), then no_rc_chain.
            have h_dops_e'em := h_distinct e' e_mid he'_in_union h_em_in_union h_eq_e'em
            have h_dops_emet := h_distinct e_mid e_top h_em_in_union h_et_in_union h_em_ne_et
            have h_rc_dir := (hVC.rc_non_comm_directional e' e_mid h_dops_e'em).mp h_ncomm_e'em
            rcases h_rc_dir with h_rc1 | h_rc2
            · -- rc(e', e_mid) = Fst, rc(e_mid, e_top) = Fst → no_rc_chain
              exact absurd ⟨h_rc1, h_rc_em_et⟩
                (hVC.no_rc_chain e' e_mid e_top h_dops_e'em h_dops_emet)
            · -- rc(e_mid, e') = Fst. Split on rc_non_comm_directional(e,e').
              have h_e_ne_e' : e ≠ e' := by
                intro heq; subst heq; exact h_ncomm_e'em h_comm_e_em
              have h_dops_ee' := h_distinct e e' he_in_union he'_in_union h_e_ne_e'
              have h_rc_dir2 := (hVC.rc_non_comm_directional e e' h_dops_ee').mp h_ncomm_ee'
              rcases h_rc_dir2 with h_rc_ee'_fst | h_rc_e'e_fst
              · -- rc(e, e') = Fst.
                by_cases h_eq_eem : e = e_mid
                · -- e = e_mid: after subst, lo C e e_top directly.
                  subst h_eq_eem
                  exact Or.inl ⟨e_top, h_etop_in_top,
                    Or.inr ⟨h_nvis_em_et, h_nvis_et_em, h_rc_em_et, h_no_ow_et⟩⟩
                · -- e ≠ e_mid: derive contradiction via
                  -- h_ncomm_concurrent_local_top vs no_rc_chain.
                  -- Step 1: ¬vis(e', e_top) and ¬vis(e_top, e').
                  have h_nvis_e'_et : ¬C.vis e' e_top := by
                    intro h; exact h_disjoint e'
                      (h_top_vis_closed e' e_top h h_etop_in_top) he'_local
                  have h_nvis_et_e' : ¬C.vis e_top e' := by
                    intro h; exact h_nvis_et_em (h_vis_trans h h_vis_e'em)
                  -- Step 2: ¬commute(e', e_top) from hypothesis.
                  have h_e'_ne_et : e' ≠ e_top := by
                    intro heq; subst heq
                    exact h_disjoint e' h_etop_in_top he'_local
                  have h_ncomm_e'_et : ¬D.commutes e' e_top :=
                    h_ncomm_concurrent_local_top e' e_top he'_local
                      h_etop_in_top h_nvis_e'_et h_nvis_et_e'
                  -- Step 3: no_rc_chain forces commute(e', e_top),
                  -- giving a contradiction.
                  exfalso
                  have h_dops_e'et := h_distinct e' e_top he'_in_union
                    h_et_in_union h_e'_ne_et
                  have h_dops_eme' : distinctOps e_mid e' :=
                    h_distinct e_mid e' h_em_in_union he'_in_union
                      (Ne.symm h_eq_e'em)
                  -- rc(e', e_top) ≠ Fst from chain (e_mid, e', e_top)
                  have h1 : D.rc e' e_top ≠ RcRes.Fst_then_snd := by
                    intro h; exact hVC.no_rc_chain e_mid e' e_top
                      h_dops_eme' h_dops_e'et ⟨h_rc2, h⟩
                  -- rc(e_top, e') ≠ Fst from chain (e_mid, e_top, e')
                  have h_dops_ete' : distinctOps e_top e' := by
                    exact h_distinct e_top e' h_et_in_union he'_in_union
                      (Ne.symm h_e'_ne_et)
                  have h2 : D.rc e_top e' ≠ RcRes.Fst_then_snd := by
                    intro h; exact hVC.no_rc_chain e_mid e_top e'
                      h_dops_emet h_dops_ete' ⟨h_rc_em_et, h⟩
                  -- Both directions blocked → commute(e', e_top)
                  have h_comm : D.commutes e' e_top := by
                    by_contra hc
                    rcases (hVC.rc_non_comm_directional e' e_top
                      h_dops_e'et).mp hc with h | h
                    · exact h1 h
                    · exact h2 h
                  exact h_ncomm_e'_et h_comm
              · -- rc(e', e) = Fst: chain (e_mid, e', e) → no_rc_chain.
                exfalso
                have h_dops_e'e := h_distinct e' e he'_in_union he_in_union (Ne.symm h_e_ne_e')
                have h_dops_eme' : distinctOps e_mid e' := fun h => h_dops_e'em (h.symm)
                exact hVC.no_rc_chain e_mid e' e h_dops_eme' h_dops_e'e ⟨h_rc2, h_rc_e'e_fst⟩
          · -- ¬commute e e_mid: lo_vis gives lo C e e_mid. Depth-2 witness.
            exact Or.inr ⟨e_mid, h_mid_in_local, e_top, h_etop_in_top,
                         Or.inl ⟨h_vis_e_em, h_comm_e_em⟩,
                         Or.inr ⟨h_nvis_em_et, h_nvis_et_em, h_rc_em_et, h_no_ow_et⟩⟩
    · -- Case (vis, rc): h_lo vis, h_lo_e'_emid rc
      -- no-overwriter on e_mid: ¬∃ e₃, vis e_mid e₃ ∧ ¬commute e_mid e₃
      rcases h_lo_emid_etop with ⟨h_vis_em_et, h_ncomm_em_et⟩ | ⟨h_nvis_em_et, h_nvis_et_em, h_rc_em_et, h_no_ow_et⟩
      · -- h_lo_emid_etop vis: contradicts no-overwriter on e_mid.
        exact absurd ⟨e_top, h_vis_em_et, h_ncomm_em_et⟩ h_no_ow_em
      · -- Both h_lo_e'_emid and h_lo_emid_etop are rc.
        -- rc(e', e_mid) = Fst and rc(e_mid, e_top) = Fst.
        by_cases h_eq_e'em : e' = e_mid
        · -- e' = e_mid: lo C e' e_top from rc components. Depth-2 witness.
          subst h_eq_e'em
          exact Or.inr ⟨e', he'_local, e_top, h_etop_in_top,
            Or.inl ⟨h_vis_ee', h_ncomm_ee'⟩,
            Or.inr ⟨h_nvis_em_et, h_nvis_et_em, h_rc_em_et, h_no_ow_et⟩⟩
        · -- e' ≠ e_mid: no_rc_chain(e', e_mid, e_top)
          exfalso
          exact hVC.no_rc_chain e' e_mid e_top
            (h_distinct e' e_mid he'_in_union h_em_in_union h_eq_e'em)
            (h_distinct e_mid e_top h_em_in_union h_et_in_union h_em_ne_et)
            ⟨h_rc_e'em, h_rc_em_et⟩
    · -- Case (rc, vis): h_lo rc, h_lo_e'_emid vis
      -- no-overwriter on e': ¬∃ e₃, vis e' e₃ ∧ ¬commute e' e₃
      -- But vis e' e_mid ∧ ¬commute e' e_mid: e_mid is such an e₃.
      exact absurd ⟨e_mid, h_vis_e'em, h_ncomm_e'em⟩ h_no_ow_e'
    · -- Case (rc, rc): h_lo rc, h_lo_e'_emid rc
      -- rc(e, e') = Fst and rc(e', e_mid) = Fst.
      -- no_rc_chain(e, e', e_mid) gives contradiction.
      by_cases h_eq_ee' : e = e'
      · -- e = e': after subst, h_lo_e'_emid becomes lo C e e_mid.
        -- And h_lo_emid_etop is lo C e_mid e_top.
        -- So depth-2 path from e: e → e_mid → e_top.
        subst h_eq_ee'
        exact Or.inr ⟨e_mid, h_mid_in_local, e_top, h_etop_in_top,
          Or.inr ⟨h_nvis_e'em, h_nvis_eme', h_rc_e'em, h_no_ow_em⟩,
          h_lo_emid_etop⟩
      · -- e ≠ e'
        by_cases h_eq_e'em : e' = e_mid
        · -- e' = e_mid: after subst, lo C e' e_top from h_lo_emid_etop.
          -- And lo C e e' from rc components. Depth-2 witness.
          subst h_eq_e'em
          exact Or.inr ⟨e', he'_local, e_top, h_etop_in_top,
            Or.inr ⟨h_nvis_ee', h_nvis_e'e, h_rc_ee', h_no_ow_e'⟩,
            h_lo_emid_etop⟩
        · -- e ≠ e', e' ≠ e_mid: no_rc_chain(e, e', e_mid)
          exfalso
          exact hVC.no_rc_chain e e' e_mid
            (h_distinct e e' he_in_union he'_in_union h_eq_ee')
            (h_distinct e' e_mid he'_in_union h_em_in_union h_eq_e'em)
            ⟨h_rc_ee', h_rc_e'em⟩

/-- **Lemma 1 part (2)** (paper appendix.tex:158-178). For
`e ∈ L_top_a` and `e' ∈ L_top_b`, no `lo`-edge from `e` to `e'`.

**Proof structure.** `e ∈ L_top_a` provides a witness `e''` with
`e'' ∈ L_b` (in either replica's local) and `lo C e'' e`. The vis
disjunct of `lo e'' e` is **closed inline** below — it would force
`e'' ∈ L_top` via `h_top_vis_closed`, but `e'' ∈ L_local` (which is
disjoint from `L_top`). Hence `lo e'' e` reduces to its rc disjunct.

Then to derive a contradiction with `e' ∈ L_top_b`, the goal is to
show `lo e'' e'` (giving `e'` an L_b predecessor, contradicting
`L_top_b`'s definition). This composition `lo e'' e ∧ lo e e' →
lo e'' e'` is the paper's case-analysis (lines 158-178); it
consumes `vis_trans` + `no_rc_chain` + concurrent-rc reasoning.

**Added hypothesis** `h_distinct`: all distinct events in `ev₁ ∪ ev₂`
have distinct timestamps. This follows from `C.timestamps_distinct`
at call sites (where ev₁, ev₂ are replica event sets). The paper's
proof assumes it implicitly; the formalization needs it explicitly
because `no_rc_chain` requires `distinctOps`. -/
theorem no_lo_top_a_to_top_b
    (hVC : SatisfiesVCs D) {C : Configuration D}
    (h_vis_trans : ∀ {a b c : Op D.AppOp},
       C.vis a b → C.vis b c → C.vis a c)
    {ev₁ ev₂ : Set (Op D.AppOp)}
    (h_top_vis_closed : ∀ a b, C.vis a b →
       b ∈ L_top ev₁ ev₂ → a ∈ L_top ev₁ ev₂)
    (h_distinct : ∀ a b, a ∈ ev₁ ∪ ev₂ → b ∈ ev₁ ∪ ev₂ →
       a ≠ b → distinctOps a b)
    {e e' : Op D.AppOp}
    (h_e_top_a : e ∈ L_top_a C ev₁ ev₂)
    (h_e'_top_b : e' ∈ L_top_b C ev₁ ev₂) :
    ¬ lo C e e' := by
  intro h_lo
  obtain ⟨he_top, e'', h_e''_lb, h_lo_e''_e⟩ := h_e_top_a
  obtain ⟨he'_top, h_no_pred⟩ := h_e'_top_b
  -- Rule out vis disjunct of `lo e'' e` via L_top causal closure.
  have h_e''_in_local :
      e'' ∈ L₁_local ev₁ ev₂ ∨ e'' ∈ L₂_local ev₁ ev₂ := by
    rcases h_e''_lb with h | h
    · exact Or.inl (L_b_subset_local _ _ _ h)
    · exact Or.inr (L_b_subset_local _ _ _ h)
  have h_e''_not_top : e'' ∉ L_top ev₁ ev₂ := by
    intro h_top
    rcases h_e''_in_local with ⟨_, h_ne⟩ | ⟨_, h_ne⟩
    · exact h_ne h_top.2
    · exact h_ne h_top.1
  have h_lo_e''_e_rc :
      ¬ C.vis e'' e ∧ ¬ C.vis e e'' ∧
      D.rc e'' e = RcRes.Fst_then_snd ∧
      ¬ ∃ e₃, C.vis e e₃ ∧ ¬ D.commutes e e₃ := by
    rcases h_lo_e''_e with ⟨h_vis_e''e, _⟩ | h_rc
    · exact absurd (h_top_vis_closed e'' e h_vis_e''e he_top)
        h_e''_not_top
    · exact h_rc
  -- Goal: derive a contradiction. Aim for `lo e'' e'` to contradict
  -- e' ∈ L_top_b (no L_b predecessor). The composition
  -- `lo_rc e'' e ∧ lo e e' → lo e'' e'` is the paper's case-analysis.
  -- Membership facts for h_distinct.
  have he_in_union : e ∈ ev₁ ∪ ev₂ := Set.mem_union_left _ he_top.1
  have he'_in_union : e' ∈ ev₁ ∪ ev₂ := Set.mem_union_left _ he'_top.1
  have he''_in_union : e'' ∈ ev₁ ∪ ev₂ := by
    rcases h_e''_in_local with ⟨h, _⟩ | ⟨h, _⟩
    · exact Set.mem_union_left _ h
    · exact Set.mem_union_right _ h
  -- e'' ≠ e (different partition layers: e'' ∈ L_local, e ∈ L_top).
  have h_e''_ne_e : e'' ≠ e := by
    intro heq; subst heq; exact h_e''_not_top he_top
  -- e ≠ e' (L_top_a and L_top_b are complementary, hence disjoint).
  have h_e_ne_e' : e ≠ e' := by
    intro heq; subst heq
    exact h_no_pred ⟨e'', h_e''_lb, h_lo_e''_e⟩
  -- In the rc-rc case, D.rc e'' e = Fst and D.rc e e' = Fst.
  -- By no_rc_chain with distinctOps, this is a contradiction.
  apply h_no_pred
  refine ⟨e'', h_e''_lb, ?_⟩
  -- Case-split on vis/rc disjuncts of h_lo : lo C e e'
  rcases h_lo with ⟨h_vis_ee', h_ncomm_ee'⟩ | ⟨h_nvis_ee', h_nvis_e'e, h_rc_ee', h_no_ow_e'⟩
  · -- Vis case: C.vis e e' ∧ ¬ D.commutes e e'.
    -- Contradicts the no-overwriter condition of e in h_lo_e''_e_rc.
    exact absurd ⟨e', h_vis_ee', h_ncomm_ee'⟩ h_lo_e''_e_rc.2.2.2
  · -- RC case: D.rc e'' e = Fst_then_snd and D.rc e e' = Fst_then_snd.
    -- By no_rc_chain, this gives False.
    exfalso
    exact hVC.no_rc_chain e'' e e'
      (h_distinct e'' e he''_in_union he_in_union h_e''_ne_e)
      (h_distinct e e' he_in_union he'_in_union h_e_ne_e')
      ⟨h_lo_e''_e_rc.2.2.1, h_rc_ee'⟩

/-! Note: an earlier stub `no_lo_within_L_top_a` claimed
`∀ e e' ∈ L_top_a, e ≠ e' → ¬ lo C e e'` — this is too strong and
**false in general** (lo-edges between distinct `L_top_a` elements
are not precluded by the carving's definitions). Block 6's inner
step uses `exists_lo_maximal_in_subset (L_top_a)` directly to
extract a lo-max element, which gives no-lo-successor *within*
`L_top_a` for free. -/

/-
Extend the 1-op peel equation by prepending a list of operations to
the left-side base state.  Uses `ind_left_1op` at each step.
-/
theorem ind_left_1op_list
    {D : CRDTSig} (hVC : SatisfiesVCs D)
    (o₁ ol : Op D.AppOp)
    (h_dist_o₁_ol : distinctOps o₁ ol)
    (l : List (Op D.AppOp))
    (h_dist_l_o₁ : ∀ y ∈ l, distinctOps o₁ y)
    (h_dist_l_ol : ∀ y ∈ l, distinctOps ol y)
    (a b : D.State)
    (h_base : D.merge (D.update a o₁) (D.update b ol)
                = D.update (D.merge a (D.update b ol)) o₁) :
    D.merge (D.update (applySeq D a l) o₁) (D.update b ol)
      = D.update (D.merge (applySeq D a l) (D.update b ol)) o₁ := by
  -- Apply the induction hypothesis to the list l.
  have h_ind : ∀ (l : List (Op D.AppOp)), (∀ y ∈ l, distinctOps o₁ y) → (∀ y ∈ l, distinctOps ol y) → D.merge (D.update (applySeq D a l) o₁) (D.update b ol) = D.update (D.merge (applySeq D a l) (D.update b ol)) o₁ := by
    intro l hl₁ hl₂; induction l using List.reverseRecOn <;> simp_all +decide ;
    · exact h_base;
    · rw [ applySeq_append_single ];
      apply hVC.ind_left_1op;
      · exact hl₁ _ _ _ ( Or.inr rfl );
      · exact h_dist_o₁_ol;
      · exact hl₂ _ _ _ ( Or.inr rfl ) |> fun h => by tauto;
      · assumption;
  exact h_ind l h_dist_l_o₁ h_dist_l_ol

/-- **1-op peel equation for reachable states sharing element `ol`.**

`merge(update(update(A, ol), o₁), update(B, ol))`
  `= update(merge(update(A, ol), update(B, ol)), o₁)`

where `A = applySeq init π_a`, `B = applySeq init π_b`.

The Sal paper (appendix §A.2) proves this by a nested induction
mirrroring the `bottomUp_1op` template:

1. **Base case** (π_a = [], π_b = []): `ind_lca_1op` with `base_1op`.
2. **Left-side extension** (π_a → π_a ++ [y]): `ind_left_1op`
   (needs `distinctOps o₁ y`, `distinctOps ol y`; no
   `differentReplicas` required).
3. **Right-side extension** (π_b → π_b ++ [y]): requires the
   `inter_right_base_1op` / `inter_right_1op` VCs, which
   need `differentReplicas y ol` between each right-side
   element and the shared element.  Deriving that relation
   from the abstract event-set hypotheses available in the
   merge-linearization induction requires additional
   infrastructure (forward closure of ev₂, or a replica-level
   argument that is not threaded through the current proof).
4. **Shared-side extension** (ol' added to both sides):
   `inter_lca_1op`.

Steps 3–4 are the remaining obstacle.

**Resolution.** The shared-`ol` peel is a fundamental CRDT-lattice
property: when `ol` is applied to both sides of a merge, any further
operation `o₁` on the left can be factored out.  In a join-semilattice
where `update` is join with a singleton, this follows from
associativity and commutativity of join.  The existing 24 VCs do not
directly imply it (every VC that extends a single side requires
`distinctOps` between the new operation and the other side's
operation, which fails when both sides share `ol`).  We therefore take
the property as an explicit hypothesis `h_shared_peel`, to be
discharged by extending `SatisfiesVCs` with this additional VC (or by
proving it from a lattice structure) in a future session. -/
theorem merge_peel_1op_shared_base
    {D : CRDTSig} (hVC : SatisfiesVCs D)
    (o₁ ol : Op D.AppOp)
    (π_a π_b : List (Op D.AppOp))
    (h_shared_peel : ∀ (a b : D.State),
      D.merge (D.update (D.update a ol) o₁) (D.update b ol)
        = D.update (D.merge (D.update a ol) (D.update b ol)) o₁) :
    D.merge (D.update (D.update (applySeq D D.init π_a) ol) o₁)
            (D.update (applySeq D D.init π_b) ol)
      = D.update (D.merge (D.update (applySeq D D.init π_a) ol)
                          (D.update (applySeq D D.init π_b) ol)) o₁ :=
  h_shared_peel _ _

/-- **Merge peel with shared event.** When `e₁` sits at the tail of
the left-side list and `e₁ ∉ ev₂`, the 1-op peel equation
`merge(update(A, e₁), B) = update(merge(A, B), e₁)` holds.

This generalises `bottomUp_2op_reachable` to the case where the
right-tail event `e₂` also appears in the left-side body list `π₁'`
(a shared event).  `bottomUp_2op_reachable` requires `distinctOps e₂ y`
for every `y ∈ π₁'`, which fails when `e₂ ∈ π₁'`.

The proof splits `π₁'` at the position of `e₂`, uses
`merge_peel_1op_shared_base` for the base (where `e₂` sits at the
split point), then extends by the remaining elements via
`ind_left_1op_list`. -/
theorem merge_peel_shared
    {D : CRDTSig} (hVC : SatisfiesVCs D)
    {C : Configuration D}
    (e₁ e₂ : Op D.AppOp)
    (π₁' π₂' : List (Op D.AppOp))
    {ev₁ ev₂ : Set (Op D.AppOp)}
    (h_e₁_in_C : e₁ ∈ C.events)
    (h_e₂_in_C : e₂ ∈ C.events)
    (h_ev₁_in_C : ∀ a ∈ ev₁, a ∈ C.events)
    (h_ev₂_in_C : ∀ a ∈ ev₂, a ∈ C.events)
    (h₁p : listPermOf (π₁' ++ [e₁]) ev₁)
    (h₂p : listPermOf (π₂' ++ [e₂]) ev₂)
    (h₁r : respects (π₁' ++ [e₁]) (lo C))
    (h₂r : respects (π₂' ++ [e₂]) (lo C))
    (h_e₁_in_ev₁ : e₁ ∈ ev₁)
    (h_e₂_in_ev₂ : e₂ ∈ ev₂)
    (h_e₂_in_ev₁ : e₂ ∈ ev₁)
    (h_e₁_not_ev₂ : e₁ ∉ ev₂)
    (h_ne : e₁ ≠ e₂)
    (h_nc : ¬ D.commutes e₁ e₂)
    (h_rc : D.rc e₂ e₁ = RcRes.Fst_then_snd)
    (h_dist : distinctOps e₁ e₂)
    (h_shared_peel : ∀ (a b : D.State),
      D.merge (D.update (D.update a e₂) e₁) (D.update b e₂)
        = D.update (D.merge (D.update a e₂) (D.update b e₂)) e₁) :
    D.merge (D.update (applySeq D D.init π₁') e₁)
            (D.update (applySeq D D.init π₂') e₂)
      = D.update (D.merge (applySeq D D.init π₁')
                          (D.update (applySeq D D.init π₂') e₂)) e₁ := by
  -- Step 1: e₂ ∈ π₁'
  have h_e₂_in_π₁' : e₂ ∈ π₁' := by
    have h := (h₁p.2 e₂).mpr h_e₂_in_ev₁
    rcases List.mem_append.mp h with h | h
    · exact h
    · simp at h; exact absurd h.symm h_ne
  -- Step 2: split π₁' at e₂
  obtain ⟨α, β, h_split⟩ := List.append_of_mem h_e₂_in_π₁'
  -- Step 3: π₁' nodup, and membership facts
  have h_nodup_π₁' : π₁'.Nodup := (List.nodup_append.mp h₁p.1).1
  have h_e₁_notin_π₁' : e₁ ∉ π₁' := by
    intro h
    have hnd := List.nodup_append.mp h₁p.1
    exact absurd rfl (hnd.2.2 e₁ h e₁ (by simp))
  have h_e₂_notin_β : e₂ ∉ β := by
    rw [h_split] at h_nodup_π₁'
    have hnd := List.nodup_append.mp h_nodup_π₁'
    exact (List.nodup_cons.mp hnd.2.1).1
  have h_e₂_notin_α : e₂ ∉ α := by
    rw [h_split] at h_nodup_π₁'
    intro h
    have hnd := List.nodup_append.mp h_nodup_π₁'
    exact absurd rfl (hnd.2.2 e₂ h e₂ (by exact List.Mem.head _))
  have h_e₂_notin_π₂' : e₂ ∉ π₂' := by
    intro h
    have hnd := List.nodup_append.mp h₂p.1
    exact absurd rfl (hnd.2.2 e₂ h e₂ (by simp))
  -- Step 4: all events are in C.events
  have h_π₁'_in_C : ∀ y ∈ π₁', y ∈ C.events := by
    intro y hy; exact h_ev₁_in_C y ((h₁p.2 y).mp
      (List.mem_append.mpr (Or.inl hy)))
  have h_π₂'_in_C : ∀ y ∈ π₂', y ∈ C.events := by
    intro y hy; exact h_ev₂_in_C y ((h₂p.2 y).mp
      (List.mem_append.mpr (Or.inl hy)))
  -- Step 5: distinctOps for β elements
  have h_dist_β_e₁ : ∀ y ∈ β, distinctOps e₁ y := by
    intro y hy
    have hy_in_π : y ∈ π₁' := h_split ▸ List.mem_append.mpr
      (Or.inr (List.mem_cons_of_mem _ hy))
    have hne : e₁ ≠ y := fun heq => h_e₁_notin_π₁' (heq ▸ hy_in_π)
    obtain ⟨_, _, hL₁, hs₁⟩ := h_e₁_in_C
    obtain ⟨_, _, hL_y, hs_y⟩ := h_π₁'_in_C y hy_in_π
    exact C.timestamps_distinct hL₁ hs₁ hL_y hs_y hne
  have h_dist_β_e₂ : ∀ y ∈ β, distinctOps e₂ y := by
    intro y hy
    have hy_in_π : y ∈ π₁' := h_split ▸ List.mem_append.mpr
      (Or.inr (List.mem_cons_of_mem _ hy))
    have hne : e₂ ≠ y := fun heq => h_e₂_notin_β (heq ▸ hy)
    obtain ⟨_, _, hL₂, hs₂⟩ := h_e₂_in_C
    obtain ⟨_, _, hL_y, hs_y⟩ := h_π₁'_in_C y hy_in_π
    exact C.timestamps_distinct hL₂ hs₂ hL_y hs_y hne
  -- Step 6: distinctOps for α elements
  have h_dist_α_e₁ : ∀ y ∈ α, distinctOps e₁ y := by
    intro y hy
    have hy_in_π : y ∈ π₁' := h_split ▸ List.mem_append.mpr (Or.inl hy)
    have hne : e₁ ≠ y := fun heq => h_e₁_notin_π₁' (heq ▸ hy_in_π)
    obtain ⟨_, _, hL₁, hs₁⟩ := h_e₁_in_C
    obtain ⟨_, _, hL_y, hs_y⟩ := h_π₁'_in_C y hy_in_π
    exact C.timestamps_distinct hL₁ hs₁ hL_y hs_y hne
  have h_dist_α_e₂ : ∀ y ∈ α, distinctOps e₂ y := by
    intro y hy
    have hy_in_π : y ∈ π₁' := h_split ▸ List.mem_append.mpr (Or.inl hy)
    have hne : e₂ ≠ y := fun heq => h_e₂_notin_α (heq ▸ hy)
    obtain ⟨_, _, hL₂, hs₂⟩ := h_e₂_in_C
    obtain ⟨_, _, hL_y, hs_y⟩ := h_π₁'_in_C y hy_in_π
    exact C.timestamps_distinct hL₂ hs₂ hL_y hs_y hne
  -- Step 7: distinctOps for π₂' elements
  have h_dist_π₂'_e₁ : ∀ y ∈ π₂', distinctOps e₁ y := by
    intro y hy
    have hne : e₁ ≠ y := by
      intro heq; subst heq
      exact h_e₁_not_ev₂ ((h₂p.2 e₁).mp
        (List.mem_append.mpr (Or.inl hy)))
    obtain ⟨_, _, hL₁, hs₁⟩ := h_e₁_in_C
    obtain ⟨_, _, hL_y, hs_y⟩ := h_π₂'_in_C y hy
    exact C.timestamps_distinct hL₁ hs₁ hL_y hs_y hne
  have h_dist_π₂'_e₂ : ∀ y ∈ π₂', distinctOps e₂ y := by
    intro y hy
    have hne : e₂ ≠ y := fun heq => h_e₂_notin_π₂' (heq ▸ hy)
    obtain ⟨_, _, hL₂, hs₂⟩ := h_e₂_in_C
    obtain ⟨_, _, hL_y, hs_y⟩ := h_π₂'_in_C y hy
    exact C.timestamps_distinct hL₂ hs₂ hL_y hs_y hne
  -- Step 8: rewrite applySeq with the split
  have h_applySeq_split : applySeq D D.init π₁' =
      applySeq D (D.update (applySeq D D.init α) e₂) β := by
    rw [h_split]
    simp [applySeq, List.foldl_append, List.foldl_cons]
  rw [h_applySeq_split]
  -- Step 9: apply ind_left_1op_list to handle β
  exact ind_left_1op_list hVC e₁ e₂ h_dist β h_dist_β_e₁ h_dist_β_e₂
    (D.update (applySeq D D.init α) e₂) (applySeq D D.init π₂')
    (merge_peel_1op_shared_base hVC e₁ e₂ α π₂' h_shared_peel)

/-- **Distinct-last-event case** of `merge_linearization_exists`.
Extracted as a separate theorem so the subagent can focus on it. -/
theorem distinct_last_case
    {D : CRDTSig} (hVC : SatisfiesVCs D)
    {C : Configuration D}
    {n : ℕ}
    (ih : ∀ m, m < n →
      ∀ (π₁ π₂ : List (Op D.AppOp)) (ev₁ ev₂ : Set (Op D.AppOp)) (s₁ s₂ : D.State),
        π₁.length + π₂.length = m →
        (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
        (∀ a b, C.vis a b → ¬ D.commutes a b → b ∈ ev₁ → a ∈ ev₁) →
        (∀ a b, C.vis a b → ¬ D.commutes a b → b ∈ ev₂ → a ∈ ev₂) →
        listPermOf π₁ ev₁ → listPermOf π₂ ev₂ →
        respects π₁ (lo C) → respects π₂ (lo C) →
        applySeq D D.init π₁ = s₁ → applySeq D D.init π₂ = s₂ →
        ∃ π, listPermOf π (ev₁ ∪ ev₂) ∧ respects π (lo C) ∧
             applySeq D D.init π = D.merge s₁ s₂)
    {ev₁ ev₂ : Set (Op D.AppOp)}
    {s₁ s₂ : D.State}
    (h_ev₁_in_C : ∀ a ∈ ev₁, a ∈ C.events)
    (h_ev₂_in_C : ∀ a ∈ ev₂, a ∈ C.events)
    (h_ev₁_closed : ∀ a b, C.vis a b → ¬ D.commutes a b → b ∈ ev₁ → a ∈ ev₁)
    (h_ev₂_closed : ∀ a b, C.vis a b → ¬ D.commutes a b → b ∈ ev₂ → a ∈ ev₂)
    {π₁' : List (Op D.AppOp)} {e₁ : Op D.AppOp}
    (h₁p : listPermOf (π₁' ++ [e₁]) ev₁)
    {π₂' : List (Op D.AppOp)} {e₂ : Op D.AppOp}
    (h₂p : listPermOf (π₂' ++ [e₂]) ev₂)
    (h₁r : respects (π₁' ++ [e₁]) (lo C))
    (h₂r : respects (π₂' ++ [e₂]) (lo C))
    (h₁s : applySeq D D.init (π₁' ++ [e₁]) = s₁)
    (h₂s : applySeq D D.init (π₂' ++ [e₂]) = s₂)
    (h_len : (π₁' ++ [e₁]).length + (π₂' ++ [e₂]).length = n)
    (h_ne : ¬ e₁ = e₂)
    (h_shared_peel : ∀ (o₁ ol : Op D.AppOp), distinctOps o₁ ol →
      ∀ (a b : D.State),
        D.merge (D.update (D.update a ol) o₁) (D.update b ol)
          = D.update (D.merge (D.update a ol) (D.update b ol)) o₁) :
    ∃ π, listPermOf π (ev₁ ∪ ev₂) ∧ respects π (lo C) ∧
         applySeq D D.init π = D.merge s₁ s₂ := by
  by_cases h_e₁_comm : ∀ x ∈ π₂' ++ [e₂], D.commutes e₁ x
  · -- Case 1: e₁ commutes with all of π₂' ++ [e₂].
    by_cases h_e₁_in_ev₂ : e₁ ∈ ev₂
    · -- Case 1b: e₁ shared.
      -- Step 1: s₁ = D.update s₁' e₁ (same as Case 1a)
      set s₁' := applySeq D D.init π₁' with hs₁'_def
      have hs₁_eq : s₁ = D.update s₁' e₁ := by
        rw [← h₁s, applySeq_append_single]
      -- Step 2: extract e₁ from π₂ via applySeq_comm_extract
      have h_e₁_in_π₂ : e₁ ∈ π₂' ++ [e₂] := (h₂p.2 e₁).mpr h_e₁_in_ev₂
      set π₂_no_e₁ := (π₂' ++ [e₂]).filter (· ≠ e₁) with hπ₂_no_e₁_def
      set s₂' := applySeq D D.init π₂_no_e₁ with hs₂'_def
      have hs₂_eq : s₂ = D.update s₂' e₁ := by
        rw [← h₂s]
        exact applySeq_comm_extract h_e₁_in_π₂ h₂p.1
          (fun x hx _ => h_e₁_comm x hx) D.init
      -- Step 3: lem_0op
      have h_merge_eq : D.merge s₁ s₂ = D.update (D.merge s₁' s₂') e₁ := by
        rw [hs₁_eq, hs₂_eq, hVC.lem_0op]
      -- Step 4: e₁ ∉ π₁'
      have h_e₁_not_in_π₁' : e₁ ∉ π₁' := by
        intro h
        have hnd := List.nodup_append.mp h₁p.1
        exact hnd.2.2 e₁ h e₁ (List.mem_singleton.mpr rfl) rfl
      -- Step 5: listPermOf π₁' (ev₁ \ {e₁})
      have h₁p' : listPermOf π₁' (ev₁ \ {e₁}) := by
        constructor
        · exact (List.nodup_append.mp h₁p.1).1
        · intro a; constructor
          · intro ha
            exact ⟨(h₁p.2 a).mp (List.mem_append.mpr (Or.inl ha)),
              fun heq => h_e₁_not_in_π₁' (heq ▸ ha)⟩
          · intro ⟨ha_ev₁, ha_ne⟩
            rcases List.mem_append.mp ((h₁p.2 a).mpr ha_ev₁) with h | h
            · exact h
            · exact absurd (List.mem_singleton.mp h) ha_ne
      -- Step 6: listPermOf π₂_no_e₁ (ev₂ \ {e₁})
      have h₂p' : listPermOf π₂_no_e₁ (ev₂ \ {e₁}) :=
        filter_ne_listPermOf h₂p h_e₁_in_π₂
      -- Step 7: respects
      have h₁r' : respects π₁' (lo C) := (List.pairwise_append.mp h₁r).1
      have h₂r' : respects π₂_no_e₁ (lo C) := filter_ne_respects h₂r
      -- Step 8: closures
      have h_ev₁'_closed : ∀ a b, C.vis a b → ¬ D.commutes a b →
          b ∈ ev₁ \ {e₁} → a ∈ ev₁ \ {e₁} :=
        closure_preserved_by_tail_peel h₁p h₁r h_ev₁_closed
      have h_e₁_comm_ev₂ : ∀ x ∈ ev₂, D.commutes e₁ x :=
        fun x hx => h_e₁_comm x ((h₂p.2 x).mpr hx)
      have h_ev₂'_closed : ∀ a b, C.vis a b → ¬ D.commutes a b →
          b ∈ ev₂ \ {e₁} → a ∈ ev₂ \ {e₁} :=
        closure_preserved_by_comm_removal h_ev₂_closed h_e₁_comm_ev₂
      -- Step 9: events in C
      have h_ev₁'_in_C : ∀ a ∈ ev₁ \ {e₁}, a ∈ C.events :=
        fun a ⟨ha, _⟩ => h_ev₁_in_C a ha
      have h_ev₂'_in_C : ∀ a ∈ ev₂ \ {e₁}, a ∈ C.events :=
        fun a ⟨ha, _⟩ => h_ev₂_in_C a ha
      -- Step 10: length bound
      have h_len' : π₁'.length + π₂_no_e₁.length < n := by
        have hfilt : π₂_no_e₁.length ≤ (π₂' ++ [e₂]).length :=
          List.length_filter_le _ _
        simp only [List.length_append, List.length_singleton] at h_len hfilt
        omega
      -- Step 11: apply ih
      obtain ⟨π_ih, hπ_ih_perm, hπ_ih_resp, hπ_ih_state⟩ :=
        ih _ h_len' π₁' π₂_no_e₁ (ev₁ \ {e₁}) (ev₂ \ {e₁}) s₁' s₂'
          rfl h_ev₁'_in_C h_ev₂'_in_C h_ev₁'_closed h_ev₂'_closed
          h₁p' h₂p' h₁r' h₂r' rfl rfl
      -- Step 12: e₁ ∉ π_ih
      have h_e₁_not_in_π_ih : e₁ ∉ π_ih := by
        intro h_in
        rcases (hπ_ih_perm.2 e₁).mp h_in with ⟨_, hne⟩ | ⟨_, hne⟩ <;> exact hne rfl
      have h_e₁_in_ev₁ : e₁ ∈ ev₁ :=
        (h₁p.2 e₁).mp (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))
      -- Step 13: final witness π_ih ++ [e₁]
      refine ⟨π_ih ++ [e₁], ?_, ?_, ?_⟩
      · -- listPermOf (π_ih ++ [e₁]) (ev₁ ∪ ev₂)
        obtain ⟨hnd_ih, hm_ih⟩ := hπ_ih_perm
        refine ⟨?_, fun a => ?_⟩
        · rw [List.nodup_append]
          refine ⟨hnd_ih, List.nodup_singleton _, ?_⟩
          intro x hx y hy
          rw [List.mem_singleton] at hy; subst y
          intro heq; subst heq
          exact h_e₁_not_in_π_ih hx
        · rw [List.mem_append, List.mem_singleton, Set.mem_union]
          constructor
          · rintro (h | rfl)
            · rcases (hm_ih a).mp h with ⟨h_ev, _⟩ | ⟨h_ev, _⟩
              · exact Or.inl h_ev
              · exact Or.inr h_ev
            · exact Or.inl h_e₁_in_ev₁
          · intro h
            by_cases hae : a = e₁
            · exact Or.inr hae
            · exact Or.inl ((hm_ih a).mpr (by
                rcases h with h | h
                · exact Or.inl ⟨h, hae⟩
                · exact Or.inr ⟨h, hae⟩))
      · -- respects (π_ih ++ [e₁]) (lo C)
        unfold respects
        rw [List.pairwise_append]
        refine ⟨hπ_ih_resp, List.pairwise_singleton _ _, ?_⟩
        intro y hy b hb
        rw [List.mem_singleton] at hb; subst b
        have hy_ev : y ∈ (ev₁ \ {e₁}) ∪ (ev₂ \ {e₁}) := (hπ_ih_perm.2 y).mp hy
        rcases hy_ev with ⟨hy_ev₁, hy_ne⟩ | ⟨hy_ev₂, hy_ne⟩
        · -- y ∈ ev₁ \ {e₁}: use last_is_lo_maximal
          have hy_π₁' : y ∈ π₁' := by
            rcases List.mem_append.mp ((h₁p.2 y).mpr hy_ev₁) with h | h
            · exact h
            · exact absurd (List.mem_singleton.mp h) hy_ne
          exact last_is_lo_maximal h₁r y hy_π₁'
        · -- y ∈ ev₂ \ {e₁}: use no_lo_of_comm_and_not_mem on ev₂ \ {e₁}
          have h_e₁_not_ev₂' : e₁ ∉ ev₂ \ {e₁} := fun h => h.2 rfl
          have h_comm_ev₂' : ∀ x ∈ ev₂ \ {e₁}, D.commutes e₁ x :=
            fun x ⟨hx, _⟩ => h_e₁_comm_ev₂ x hx
          exact no_lo_of_comm_and_not_mem hVC
            (h_ev₁_in_C e₁ h_e₁_in_ev₁)
            h_ev₂'_in_C h_e₁_not_ev₂' h_ev₂'_closed h_comm_ev₂'
            y ⟨hy_ev₂, hy_ne⟩ (Ne.symm (fun h => hy_ne (h ▸ rfl)))
      · -- applySeq D D.init (π_ih ++ [e₁]) = D.merge s₁ s₂
        rw [applySeq_append_single, hπ_ih_state, h_merge_eq]
    · -- Case 1a: e₁ strictly local.
      -- Step 1: s₁' = applySeq D D.init π₁', s₁ = D.update s₁' e₁
      set s₁' := applySeq D D.init π₁' with hs₁'_def
      have hs₁_eq : s₁ = D.update s₁' e₁ := by
        rw [← h₁s, applySeq_append_single]
      -- Step 2: merge_peel_comm
      have h_e₁_comm_ev₂ : ∀ x ∈ ev₂, D.commutes e₁ x := by
        intro x hx
        exact h_e₁_comm x ((h₂p.2 x).mpr hx)
      have h_peel : D.merge s₁ s₂ = D.update (D.merge s₁' s₂) e₁ := by
        rw [hs₁_eq, ← h₂s]
        exact hVC.merge_peel_comm s₁' e₁ (π₂' ++ [e₂]) h_e₁_comm
      -- Step 3: e₁ ∉ π₁' (from Nodup of π₁' ++ [e₁])
      have h_e₁_nodup : (π₁' ++ [e₁]).Nodup := h₁p.1
      have h_e₁_not_in_π₁' : e₁ ∉ π₁' := by
        intro h
        have := (List.nodup_append.mp h_e₁_nodup).2.2 e₁ h e₁ (List.mem_singleton.mpr rfl)
        exact this rfl
      -- Step 3b: listPermOf π₁' (ev₁ \ {e₁})
      have h₁p' : listPermOf π₁' (ev₁ \ {e₁}) := by
        constructor
        · exact (List.nodup_append.mp h_e₁_nodup).1
        · intro a
          constructor
          · intro ha
            have ha_ev₁ : a ∈ ev₁ := (h₁p.2 a).mp (List.mem_append.mpr (Or.inl ha))
            refine ⟨ha_ev₁, ?_⟩
            simp only [Set.mem_singleton_iff]
            intro heq; subst heq; exact h_e₁_not_in_π₁' ha
          · intro ⟨ha_ev₁, ha_ne⟩
            have ha_list : a ∈ π₁' ++ [e₁] := (h₁p.2 a).mpr ha_ev₁
            rcases List.mem_append.mp ha_list with h | h
            · exact h
            · simp only [Set.mem_singleton_iff] at ha_ne
              rw [List.mem_singleton] at h
              exact absurd h (fun h => ha_ne h)
      -- Step 3c: respects π₁' (lo C)
      have h₁r' : respects π₁' (lo C) := by
        exact (List.pairwise_append.mp h₁r).1
      -- Step 4: closure for ev₁ \ {e₁}
      have h_ev₁'_closed : ∀ a b, C.vis a b → ¬ D.commutes a b →
          b ∈ ev₁ \ {e₁} → a ∈ ev₁ \ {e₁} :=
        closure_preserved_by_tail_peel h₁p h₁r h_ev₁_closed
      -- Step 5: ev₁_in_C for smaller set
      have h_ev₁'_in_C : ∀ a ∈ ev₁ \ {e₁}, a ∈ C.events := by
        intro a ⟨ha, _⟩; exact h_ev₁_in_C a ha
      -- Step 6: length bound for ih
      have h_len' : π₁'.length + (π₂' ++ [e₂]).length < n := by
        have : (π₁' ++ [e₁]).length = π₁'.length + 1 := by simp
        omega
      -- Step 7: apply ih
      obtain ⟨π_ih, hπ_ih_perm, hπ_ih_resp, hπ_ih_state⟩ :=
        ih _ h_len' π₁' (π₂' ++ [e₂]) (ev₁ \ {e₁}) ev₂ s₁' s₂
          (by omega) h_ev₁'_in_C h_ev₂_in_C h_ev₁'_closed h_ev₂_closed
          h₁p' h₂p h₁r' h₂r rfl h₂s
      -- Step 8: final witness π_ih ++ [e₁]
      -- e₁ not in π_ih (since π_ih perms (ev₁ \ {e₁}) ∪ ev₂ and e₁ ∉ either)
      have h_e₁_not_in_π_ih : e₁ ∉ π_ih := by
        intro h_in
        have := (hπ_ih_perm.2 e₁).mp h_in
        rcases this with h | h
        · exact h.2 rfl
        · exact h_e₁_in_ev₂ h
      -- e₁ ∈ ev₁ (for later use)
      have h_e₁_in_ev₁ : e₁ ∈ ev₁ :=
        (h₁p.2 e₁).mp (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))
      refine ⟨π_ih ++ [e₁], ?_, ?_, ?_⟩
      · -- listPermOf (π_ih ++ [e₁]) (ev₁ ∪ ev₂)
        constructor
        · -- Nodup
          rw [List.nodup_append]
          exact ⟨hπ_ih_perm.1, List.nodup_singleton _, fun a ha b hb => by
            rw [List.mem_singleton] at hb
            intro hab
            rw [hab, hb] at ha
            exact h_e₁_not_in_π_ih ha⟩
        · -- membership
          intro a
          constructor
          · intro ha
            rcases List.mem_append.mp ha with h | h
            · rcases (hπ_ih_perm.2 a).mp h with hl | hr
              · exact Or.inl hl.1
              · exact Or.inr hr
            · rw [List.mem_singleton] at h
              rw [h]; exact Or.inl h_e₁_in_ev₁
          · intro ha
            rcases ha with hl | hr
            · by_cases hae : a = e₁
              · rw [hae]; exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
              · exact List.mem_append.mpr (Or.inl ((hπ_ih_perm.2 a).mpr (Or.inl ⟨hl, hae⟩)))
            · exact List.mem_append.mpr (Or.inl ((hπ_ih_perm.2 a).mpr (Or.inr hr)))
      · -- respects (π_ih ++ [e₁]) (lo C)
        unfold respects
        rw [List.pairwise_append]
        refine ⟨hπ_ih_resp, List.pairwise_singleton _ _, ?_⟩
        intro y hy b hb
        rw [List.mem_singleton] at hb
        rw [hb]
        -- Need: ¬ lo C e₁ y for y ∈ π_ih
        have hy_ev : y ∈ (ev₁ \ {e₁}) ∪ ev₂ := (hπ_ih_perm.2 y).mp hy
        rcases hy_ev with hy_ev₁ | hy_ev₂
        · -- y ∈ ev₁ \ {e₁}: use last_is_lo_maximal
          exact last_is_lo_maximal h₁r y ((h₁p'.2 y).mpr hy_ev₁)
        · -- y ∈ ev₂: use no_lo_of_comm_and_not_mem
          have hyne : y ≠ e₁ := fun heq => h_e₁_in_ev₂ (heq ▸ hy_ev₂)
          exact no_lo_of_comm_and_not_mem hVC (h_ev₁_in_C e₁ h_e₁_in_ev₁)
            h_ev₂_in_C h_e₁_in_ev₂ h_ev₂_closed h_e₁_comm_ev₂ y hy_ev₂ hyne
      · -- applySeq D D.init (π_ih ++ [e₁]) = D.merge s₁ s₂
        rw [applySeq_append_single, hπ_ih_state, h_peel]
  · -- Case ¬: e₁ does NOT commute with all of π₂' ++ [e₂].
    by_cases h_e₂_comm : ∀ x ∈ π₁' ++ [e₁], D.commutes e₂ x
    · -- Case 2: e₂ commutes with all of π₁' ++ [e₁].
      -- Symmetric to Case 1 via merge_comm.
      by_cases h_e₂_in_ev₁ : e₂ ∈ ev₁
      · -- Case 2b: e₂ shared (e₂ ∈ ev₁ ∩ ev₂).
        -- Step 1: s₂ = D.update s₂' e₂
        set s₂' := applySeq D D.init π₂' with hs₂'_def
        have hs₂_eq : s₂ = D.update s₂' e₂ := by
          rw [← h₂s, applySeq_append_single]
        -- Step 2: extract e₂ from π₁' ++ [e₁] via applySeq_comm_extract
        have h_e₂_in_π₁ : e₂ ∈ π₁' ++ [e₁] := (h₁p.2 e₂).mpr h_e₂_in_ev₁
        set π₁_no_e₂ := (π₁' ++ [e₁]).filter (· ≠ e₂) with hπ₁_no_e₂_def
        set s₁' := applySeq D D.init π₁_no_e₂ with hs₁'_def
        have hs₁_eq : s₁ = D.update s₁' e₂ := by
          rw [← h₁s]
          exact applySeq_comm_extract h_e₂_in_π₁ h₁p.1
            (fun x hx _ => h_e₂_comm x hx) D.init
        -- Step 3: lem_0op
        have h_merge_eq : D.merge s₁ s₂ = D.update (D.merge s₁' s₂') e₂ := by
          rw [hs₁_eq, hs₂_eq, hVC.lem_0op]
        -- Step 4: e₂ ∉ π₂'
        have h_e₂_not_in_π₂' : e₂ ∉ π₂' := by
          intro h
          have hnd := List.nodup_append.mp h₂p.1
          exact hnd.2.2 e₂ h e₂ (List.mem_singleton.mpr rfl) rfl
        -- Step 5: listPermOf π₂' (ev₂ \ {e₂})
        have h₂p' : listPermOf π₂' (ev₂ \ {e₂}) := by
          constructor
          · exact (List.nodup_append.mp h₂p.1).1
          · intro a; constructor
            · intro ha
              have ha_ev₂ : a ∈ ev₂ := (h₂p.2 a).mp (List.mem_append.mpr (Or.inl ha))
              refine ⟨ha_ev₂, ?_⟩
              simp only [Set.mem_singleton_iff]
              intro heq; subst heq; exact h_e₂_not_in_π₂' ha
            · intro ⟨ha_ev₂, ha_ne⟩
              have ha_list : a ∈ π₂' ++ [e₂] := (h₂p.2 a).mpr ha_ev₂
              rcases List.mem_append.mp ha_list with h | h
              · exact h
              · simp only [Set.mem_singleton_iff] at ha_ne
                rw [List.mem_singleton] at h
                exact absurd h (fun h => ha_ne h)
        -- Step 6: listPermOf π₁_no_e₂ (ev₁ \ {e₂})
        have h₁p' : listPermOf π₁_no_e₂ (ev₁ \ {e₂}) :=
          filter_ne_listPermOf h₁p h_e₂_in_π₁
        -- Step 7: respects
        have h₂r' : respects π₂' (lo C) := (List.pairwise_append.mp h₂r).1
        have h₁r' : respects π₁_no_e₂ (lo C) := filter_ne_respects h₁r
        -- Step 8: closures
        have h_ev₂'_closed : ∀ a b, C.vis a b → ¬ D.commutes a b →
            b ∈ ev₂ \ {e₂} → a ∈ ev₂ \ {e₂} :=
          closure_preserved_by_tail_peel h₂p h₂r h_ev₂_closed
        have h_e₂_comm_ev₁ : ∀ x ∈ ev₁, D.commutes e₂ x :=
          fun x hx => h_e₂_comm x ((h₁p.2 x).mpr hx)
        have h_ev₁'_closed : ∀ a b, C.vis a b → ¬ D.commutes a b →
            b ∈ ev₁ \ {e₂} → a ∈ ev₁ \ {e₂} :=
          closure_preserved_by_comm_removal h_ev₁_closed h_e₂_comm_ev₁
        -- Step 9: events in C
        have h_ev₂'_in_C : ∀ a ∈ ev₂ \ {e₂}, a ∈ C.events :=
          fun a ⟨ha, _⟩ => h_ev₂_in_C a ha
        have h_ev₁'_in_C : ∀ a ∈ ev₁ \ {e₂}, a ∈ C.events :=
          fun a ⟨ha, _⟩ => h_ev₁_in_C a ha
        -- Step 10: length bound
        have h_len' : π₁_no_e₂.length + π₂'.length < n := by
          have hfilt : π₁_no_e₂.length ≤ (π₁' ++ [e₁]).length :=
            List.length_filter_le _ _
          simp only [List.length_append, List.length_singleton] at h_len hfilt
          omega
        -- Step 11: apply ih
        obtain ⟨π_ih, hπ_ih_perm, hπ_ih_resp, hπ_ih_state⟩ :=
          ih _ h_len' π₁_no_e₂ π₂' (ev₁ \ {e₂}) (ev₂ \ {e₂}) s₁' s₂'
            rfl h_ev₁'_in_C h_ev₂'_in_C h_ev₁'_closed h_ev₂'_closed
            h₁p' h₂p' h₁r' h₂r' rfl rfl
        -- Step 12: e₂ ∉ π_ih
        have h_e₂_not_in_π_ih : e₂ ∉ π_ih := by
          intro h_in
          rcases (hπ_ih_perm.2 e₂).mp h_in with ⟨_, hne⟩ | ⟨_, hne⟩ <;> exact hne rfl
        have h_e₂_in_ev₂ : e₂ ∈ ev₂ :=
          (h₂p.2 e₂).mp (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))
        -- Step 13: final witness π_ih ++ [e₂]
        refine ⟨π_ih ++ [e₂], ?_, ?_, ?_⟩
        · -- listPermOf (π_ih ++ [e₂]) (ev₁ ∪ ev₂)
          obtain ⟨hnd_ih, hm_ih⟩ := hπ_ih_perm
          refine ⟨?_, fun a => ?_⟩
          · rw [List.nodup_append]
            refine ⟨hnd_ih, List.nodup_singleton _, ?_⟩
            intro x hx y hy
            rw [List.mem_singleton] at hy; subst y
            intro heq; subst heq
            exact h_e₂_not_in_π_ih hx
          · rw [List.mem_append, List.mem_singleton, Set.mem_union]
            constructor
            · rintro (h | rfl)
              · rcases (hm_ih a).mp h with ⟨h_ev, _⟩ | ⟨h_ev, _⟩
                · exact Or.inl h_ev
                · exact Or.inr h_ev
              · exact Or.inr h_e₂_in_ev₂
            · intro h
              by_cases hae : a = e₂
              · exact Or.inr hae
              · exact Or.inl ((hm_ih a).mpr (by
                  rcases h with h | h
                  · exact Or.inl ⟨h, hae⟩
                  · exact Or.inr ⟨h, hae⟩))
        · -- respects (π_ih ++ [e₂]) (lo C)
          unfold respects
          rw [List.pairwise_append]
          refine ⟨hπ_ih_resp, List.pairwise_singleton _ _, ?_⟩
          intro y hy b hb
          rw [List.mem_singleton] at hb; subst b
          have hy_ev : y ∈ (ev₁ \ {e₂}) ∪ (ev₂ \ {e₂}) := (hπ_ih_perm.2 y).mp hy
          rcases hy_ev with ⟨hy_ev₁, hy_ne⟩ | ⟨hy_ev₂, hy_ne⟩
          · -- y ∈ ev₁ \ {e₂}: use no_lo_of_comm_and_not_mem
            have h_e₂_not_ev₁' : e₂ ∉ ev₁ \ {e₂} := fun h => h.2 rfl
            have h_comm_ev₁' : ∀ x ∈ ev₁ \ {e₂}, D.commutes e₂ x :=
              fun x ⟨hx, _⟩ => h_e₂_comm_ev₁ x hx
            exact no_lo_of_comm_and_not_mem hVC
              (h_ev₂_in_C e₂ h_e₂_in_ev₂)
              h_ev₁'_in_C h_e₂_not_ev₁' h_ev₁'_closed h_comm_ev₁'
              y ⟨hy_ev₁, hy_ne⟩ (Ne.symm (fun h => hy_ne (h ▸ rfl)))
          · -- y ∈ ev₂ \ {e₂}: use last_is_lo_maximal
            have hy_π₂' : y ∈ π₂' := by
              rcases List.mem_append.mp ((h₂p.2 y).mpr hy_ev₂) with h | h
              · exact h
              · exact absurd (List.mem_singleton.mp h) hy_ne
            exact last_is_lo_maximal h₂r y hy_π₂'
        · -- applySeq D D.init (π_ih ++ [e₂]) = D.merge s₁ s₂
          rw [applySeq_append_single, hπ_ih_state, h_merge_eq]
      · -- Case 2a: e₂ strictly local (e₂ ∉ ev₁).
        -- Step 1: s₂' = applySeq D D.init π₂', s₂ = D.update s₂' e₂
        set s₂' := applySeq D D.init π₂' with hs₂'_def
        have hs₂_eq : s₂ = D.update s₂' e₂ := by
          rw [← h₂s, applySeq_append_single]
        -- Step 2: merge_peel_comm (via merge_comm)
        have h_e₂_comm_ev₁ : ∀ x ∈ ev₁, D.commutes e₂ x := by
          intro x hx; exact h_e₂_comm x ((h₁p.2 x).mpr hx)
        have h_peel : D.merge s₁ s₂ = D.update (D.merge s₁ s₂') e₂ := by
          rw [hVC.merge_comm s₁ s₂, hs₂_eq, ← h₁s,
            hVC.merge_peel_comm s₂' e₂ (π₁' ++ [e₁]) h_e₂_comm,
            h₁s, hVC.merge_comm s₂' s₁]
        -- Step 3: e₂ ∉ π₂'
        have h_e₂_nodup : (π₂' ++ [e₂]).Nodup := h₂p.1
        have h_e₂_not_in_π₂' : e₂ ∉ π₂' := by
          intro h
          have := (List.nodup_append.mp h_e₂_nodup).2.2 e₂ h e₂ (List.mem_singleton.mpr rfl)
          exact this rfl
        -- Step 3b: listPermOf π₂' (ev₂ \ {e₂})
        have h₂p' : listPermOf π₂' (ev₂ \ {e₂}) := by
          constructor
          · exact (List.nodup_append.mp h_e₂_nodup).1
          · intro a
            constructor
            · intro ha
              have ha_ev₂ : a ∈ ev₂ := (h₂p.2 a).mp (List.mem_append.mpr (Or.inl ha))
              refine ⟨ha_ev₂, ?_⟩
              simp only [Set.mem_singleton_iff]
              intro heq; subst heq; exact h_e₂_not_in_π₂' ha
            · intro ⟨ha_ev₂, ha_ne⟩
              have ha_list : a ∈ π₂' ++ [e₂] := (h₂p.2 a).mpr ha_ev₂
              rcases List.mem_append.mp ha_list with h | h
              · exact h
              · simp only [Set.mem_singleton_iff] at ha_ne
                rw [List.mem_singleton] at h
                exact absurd h (fun h => ha_ne h)
        -- Step 3c: respects π₂' (lo C)
        have h₂r' : respects π₂' (lo C) := by
          exact (List.pairwise_append.mp h₂r).1
        -- Step 4: closure for ev₂ \ {e₂}
        have h_ev₂'_closed : ∀ a b, C.vis a b → ¬ D.commutes a b →
            b ∈ ev₂ \ {e₂} → a ∈ ev₂ \ {e₂} :=
          closure_preserved_by_tail_peel h₂p h₂r h_ev₂_closed
        -- Step 5: ev₂_in_C for smaller set
        have h_ev₂'_in_C : ∀ a ∈ ev₂ \ {e₂}, a ∈ C.events := by
          intro a ⟨ha, _⟩; exact h_ev₂_in_C a ha
        -- Step 6: length bound for ih
        have h_len' : (π₁' ++ [e₁]).length + π₂'.length < n := by
          have : (π₂' ++ [e₂]).length = π₂'.length + 1 := by simp
          omega
        -- Step 7: apply ih
        obtain ⟨π_ih, hπ_ih_perm, hπ_ih_resp, hπ_ih_state⟩ :=
          ih _ h_len' (π₁' ++ [e₁]) π₂' ev₁ (ev₂ \ {e₂}) s₁ s₂'
            (by omega) h_ev₁_in_C h_ev₂'_in_C h_ev₁_closed h_ev₂'_closed
            h₁p h₂p' h₁r h₂r' h₁s rfl
        -- Step 8: final witness π_ih ++ [e₂]
        have h_e₂_not_in_π_ih : e₂ ∉ π_ih := by
          intro h_in
          have := (hπ_ih_perm.2 e₂).mp h_in
          rcases this with h | h
          · exact h_e₂_in_ev₁ h
          · exact h.2 rfl
        have h_e₂_in_ev₂ : e₂ ∈ ev₂ :=
          (h₂p.2 e₂).mp (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))
        refine ⟨π_ih ++ [e₂], ?_, ?_, ?_⟩
        · -- listPermOf (π_ih ++ [e₂]) (ev₁ ∪ ev₂)
          constructor
          · -- Nodup
            rw [List.nodup_append]
            exact ⟨hπ_ih_perm.1, List.nodup_singleton _, fun a ha b hb => by
              rw [List.mem_singleton] at hb
              intro hab
              rw [hab, hb] at ha
              exact h_e₂_not_in_π_ih ha⟩
          · -- membership
            intro a
            constructor
            · intro ha
              rcases List.mem_append.mp ha with h | h
              · rcases (hπ_ih_perm.2 a).mp h with hl | hr
                · exact Or.inl hl
                · exact Or.inr hr.1
              · rw [List.mem_singleton] at h
                rw [h]; exact Or.inr h_e₂_in_ev₂
            · intro ha
              rcases ha with hl | hr
              · by_cases hae : a = e₂
                · rw [hae]; exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
                · exact List.mem_append.mpr (Or.inl ((hπ_ih_perm.2 a).mpr (Or.inl hl)))
              · by_cases hae : a = e₂
                · rw [hae]; exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
                · exact List.mem_append.mpr (Or.inl ((hπ_ih_perm.2 a).mpr (Or.inr ⟨hr, hae⟩)))
        · -- respects (π_ih ++ [e₂]) (lo C)
          unfold respects
          rw [List.pairwise_append]
          refine ⟨hπ_ih_resp, List.pairwise_singleton _ _, ?_⟩
          intro y hy b hb
          rw [List.mem_singleton] at hb
          rw [hb]
          -- Need: ¬ lo C e₂ y for y ∈ π_ih
          have hy_ev : y ∈ ev₁ ∪ (ev₂ \ {e₂}) := (hπ_ih_perm.2 y).mp hy
          rcases hy_ev with hy_ev₁ | hy_ev₂
          · -- y ∈ ev₁: use no_lo_of_comm_and_not_mem
            have hyne : y ≠ e₂ := fun heq => h_e₂_in_ev₁ (heq ▸ hy_ev₁)
            exact no_lo_of_comm_and_not_mem hVC (h_ev₂_in_C e₂ h_e₂_in_ev₂)
              h_ev₁_in_C h_e₂_in_ev₁ h_ev₁_closed h_e₂_comm_ev₁ y hy_ev₁ hyne
          · -- y ∈ ev₂ \ {e₂}: use last_is_lo_maximal
            exact last_is_lo_maximal h₂r y ((h₂p'.2 y).mpr hy_ev₂)
        · -- applySeq D D.init (π_ih ++ [e₂]) = D.merge s₁ s₂
          rw [applySeq_append_single, hπ_ih_state, h_peel]
    · -- Case 3: neither e₁ nor e₂ commutes with everything on the
      -- other side.
      by_cases h_e₁e₂_comm : D.commutes e₁ e₂
      · -- Case 3b: e₁, e₂ commute with each other, but each has
        -- non-commuting partners on the OTHER list.
        --
        -- Decomposition strategy: derive witnesses from the negated
        -- commutativity hypotheses, then split on shared membership.
        -- Step 1: Basic membership facts.
        have h_e₁_in_ev₁ : e₁ ∈ ev₁ :=
          (h₁p.2 e₁).mp (List.mem_append.mpr (Or.inr
            (List.mem_singleton.mpr rfl)))
        have h_e₂_in_ev₂ : e₂ ∈ ev₂ :=
          (h₂p.2 e₂).mp (List.mem_append.mpr (Or.inr
            (List.mem_singleton.mpr rfl)))
        have h_e₁_in_C : e₁ ∈ C.events := h_ev₁_in_C e₁ h_e₁_in_ev₁
        have h_e₂_in_C : e₂ ∈ C.events := h_ev₂_in_C e₂ h_e₂_in_ev₂
        have h_dist_e₁e₂ : distinctOps e₁ e₂ := by
          obtain ⟨_, _, hL_e₁, hs_e₁⟩ := h_e₁_in_C
          obtain ⟨_, _, hL_e₂, hs_e₂⟩ := h_e₂_in_C
          exact C.timestamps_distinct hL_e₁ hs_e₁ hL_e₂ hs_e₂ h_ne
        -- Step 2: Commutativity is symmetric.
        have h_e₂e₁_comm : D.commutes e₂ e₁ :=
          fun s => (h_e₁e₂_comm s).symm
        -- Step 3: Extract witnesses from negated hypotheses.
        -- Since e₁ commutes with e₂, the non-commuting witness from
        -- h_e₁_comm must be in π₂' (not e₂).
        have ⟨x₀, hx₀_mem, hx₀_nc⟩ : ∃ x ∈ π₂', ¬D.commutes e₁ x := by
          push_neg at h_e₁_comm
          obtain ⟨x, hx_mem, hx_nc⟩ := h_e₁_comm
          rcases List.mem_append.mp hx_mem with h | h
          · exact ⟨x, h, hx_nc⟩
          · rw [List.mem_singleton] at h
            subst h; exact absurd h_e₁e₂_comm hx_nc
        -- Similarly for the other side.
        have ⟨y₀, hy₀_mem, hy₀_nc⟩ : ∃ y ∈ π₁', ¬D.commutes e₂ y := by
          push_neg at h_e₂_comm
          obtain ⟨y, hy_mem, hy_nc⟩ := h_e₂_comm
          rcases List.mem_append.mp hy_mem with h | h
          · exact ⟨y, h, hy_nc⟩
          · rw [List.mem_singleton] at h
            subst h; exact absurd h_e₂e₁_comm hy_nc
        -- Step 4: Sub-case decomposition on shared membership.
        -- The proof strategy depends on whether e₁/e₂ appear on
        -- the other side's event set.
        by_cases h_e₂_in_ev₁ : e₂ ∈ ev₁
        · by_cases h_e₁_in_ev₂ : e₁ ∈ ev₂
          · -- Sub-case 3b-i-a: e₂ ∈ ev₁, e₁ ∈ ev₂ (both shared).
            -- Both tail events are shared between the two sides.
            -- The state equation via merge_peel_shared-style proof
            -- works, but e₁ ∈ ev₂ means e₁ can appear in the IH
            -- witness, preventing the simple "append e₁ at end"
            -- strategy.
            --
            -- Requires: forward closure of ev₂ for the respects
            -- proof, or a fundamentally different approach.
            sorry
          · -- Sub-case 3b-i-b: e₂ ∈ ev₁, e₁ ∉ ev₂.
            -- Strategy: peel e₁ using merge_peel_shared-style
            -- reasoning. The state equation holds because the proof
            -- of merge_peel_shared doesn't use ¬commutes or rc.
            -- Step 1: e₁ ∉ π₁'
            have h_e₁_not_π₁' : e₁ ∉ π₁' := by
              intro h
              have hnd := List.nodup_append.mp h₁p.1
              exact hnd.2.2 e₁ h e₁ (List.mem_singleton.mpr rfl) rfl
            -- Step 2: e₂ ∈ π₁'
            have h_e₂_in_π₁' : e₂ ∈ π₁' := by
              have h := (h₁p.2 e₂).mpr h_e₂_in_ev₁
              rcases List.mem_append.mp h with h | h
              · exact h
              · rw [List.mem_singleton] at h; exact absurd h (Ne.symm h_ne)
            -- Step 3: split π₁' at e₂
            obtain ⟨α, β, h_split⟩ := List.append_of_mem h_e₂_in_π₁'
            -- Step 4: basic nodup / membership facts
            have h_nodup_π₁' : π₁'.Nodup :=
              (List.nodup_append.mp h₁p.1).1
            have h_e₂_notin_β : e₂ ∉ β := by
              rw [h_split] at h_nodup_π₁'
              exact (List.nodup_cons.mp
                (List.nodup_append.mp h_nodup_π₁').2.1).1
            have h_e₂_notin_α : e₂ ∉ α := by
              rw [h_split] at h_nodup_π₁'
              intro h
              exact (List.nodup_append.mp h_nodup_π₁').2.2 e₂ h e₂
                (List.Mem.head _) rfl
            -- Step 5: state equation
            have h_applySeq_split : applySeq D D.init π₁' =
                applySeq D (D.update (applySeq D D.init α) e₂) β := by
              rw [h_split]
              simp [applySeq, List.foldl_append, List.foldl_cons]
            have h_π₁'_in_C : ∀ y ∈ π₁', y ∈ C.events := by
              intro y hy; exact h_ev₁_in_C y ((h₁p.2 y).mp
                (List.mem_append.mpr (Or.inl hy)))
            have h_dist_β_e₁ : ∀ y ∈ β, distinctOps e₁ y := by
              intro y hy
              have hy_in_π : y ∈ π₁' := h_split ▸
                List.mem_append.mpr
                  (Or.inr (List.mem_cons_of_mem _ hy))
              have hne' : e₁ ≠ y := fun heq =>
                h_e₁_not_π₁' (heq ▸ hy_in_π)
              obtain ⟨_, _, hL₁, hs₁'⟩ := h_e₁_in_C
              obtain ⟨_, _, hL_y, hs_y⟩ := h_π₁'_in_C y hy_in_π
              exact C.timestamps_distinct hL₁ hs₁' hL_y hs_y hne'
            have h_dist_β_e₂ : ∀ y ∈ β, distinctOps e₂ y := by
              intro y hy
              have hy_in_π : y ∈ π₁' := h_split ▸
                List.mem_append.mpr
                  (Or.inr (List.mem_cons_of_mem _ hy))
              have hne' : e₂ ≠ y := fun heq =>
                h_e₂_notin_β (heq ▸ hy)
              obtain ⟨_, _, hL₂, hs₂'⟩ := h_e₂_in_C
              obtain ⟨_, _, hL_y, hs_y⟩ := h_π₁'_in_C y hy_in_π
              exact C.timestamps_distinct hL₂ hs₂' hL_y hs_y hne'
            have h_peel_eq :
              D.merge (D.update (applySeq D D.init π₁') e₁)
                      (D.update (applySeq D D.init π₂') e₂)
                = D.update (D.merge (applySeq D D.init π₁')
                    (D.update (applySeq D D.init π₂') e₂)) e₁ := by
              rw [h_applySeq_split]
              exact ind_left_1op_list hVC e₁ e₂ h_dist_e₁e₂ β
                h_dist_β_e₁ h_dist_β_e₂
                (D.update (applySeq D D.init α) e₂)
                (applySeq D D.init π₂')
                (merge_peel_1op_shared_base hVC e₁ e₂ α π₂'
                  (h_shared_peel e₁ e₂ h_dist_e₁e₂))
            have h_peel : D.merge s₁ s₂ =
                D.update
                  (D.merge (applySeq D D.init π₁')
                           (applySeq D D.init (π₂' ++ [e₂])))
                  e₁ := by
              rw [← h₁s, ← h₂s, applySeq_append_single,
                  applySeq_append_single]
              exact h_peel_eq
            -- Step 6: prepare for IH
            have h₁p' : listPermOf π₁' (ev₁ \ {e₁}) := by
              constructor
              · exact h_nodup_π₁'
              · intro a; constructor
                · intro ha
                  exact ⟨(h₁p.2 a).mp
                    (List.mem_append.mpr (Or.inl ha)),
                    fun heq => h_e₁_not_π₁' (heq ▸ ha)⟩
                · intro ⟨ha_ev₁, ha_ne⟩
                  rcases List.mem_append.mp
                    ((h₁p.2 a).mpr ha_ev₁) with h | h
                  · exact h
                  · exact absurd (List.mem_singleton.mp h) ha_ne
            have h₁r' : respects π₁' (lo C) :=
              (List.pairwise_append.mp h₁r).1
            have h_ev₁'_closed :
                ∀ a b, C.vis a b → ¬ D.commutes a b →
                b ∈ ev₁ \ {e₁} → a ∈ ev₁ \ {e₁} :=
              closure_preserved_by_tail_peel h₁p h₁r h_ev₁_closed
            have h_ev₁'_in_C : ∀ a ∈ ev₁ \ {e₁}, a ∈ C.events :=
              fun a ⟨ha, _⟩ => h_ev₁_in_C a ha
            have h_len' :
                π₁'.length + (π₂' ++ [e₂]).length < n := by
              simp only [List.length_append,
                List.length_singleton] at h_len ⊢; omega
            -- Step 7: apply IH
            obtain ⟨π_ih, hπ_ih_perm, hπ_ih_resp,
                    hπ_ih_state⟩ :=
              ih _ h_len' π₁' (π₂' ++ [e₂]) (ev₁ \ {e₁}) ev₂
                (applySeq D D.init π₁') s₂
                rfl h_ev₁'_in_C h_ev₂_in_C h_ev₁'_closed
                h_ev₂_closed h₁p' h₂p h₁r' h₂r rfl h₂s
            -- Step 8: e₁ ∉ π_ih (since e₁ ∉ ev₂)
            have h_e₁_not_π_ih : e₁ ∉ π_ih := by
              intro h_in
              rcases (hπ_ih_perm.2 e₁).mp h_in with
                ⟨_, hne'⟩ | h
              · exact hne' rfl
              · exact h_e₁_in_ev₂ h
            -- Step 9: final witness π_ih ++ [e₁]
            refine ⟨π_ih ++ [e₁], ?_, ?_, ?_⟩
            · -- listPermOf (π_ih ++ [e₁]) (ev₁ ∪ ev₂)
              constructor
              · rw [List.nodup_append]
                exact ⟨hπ_ih_perm.1, List.nodup_singleton _,
                  fun a ha b hb => by
                    rw [List.mem_singleton] at hb
                    intro hab; rw [hab, hb] at ha
                    exact h_e₁_not_π_ih ha⟩
              · intro a
                rw [List.mem_append, List.mem_singleton,
                    Set.mem_union]
                constructor
                · rintro (h | rfl)
                  · rcases (hπ_ih_perm.2 a).mp h with
                      ⟨h_ev, _⟩ | h_ev
                    · exact Or.inl h_ev
                    · exact Or.inr h_ev
                  · exact Or.inl h_e₁_in_ev₁
                · intro h
                  by_cases hae : a = e₁
                  · exact Or.inr hae
                  · exact Or.inl ((hπ_ih_perm.2 a).mpr
                      (by rcases h with h | h
                          · exact Or.inl ⟨h, hae⟩
                          · exact Or.inr h))
            · -- respects (π_ih ++ [e₁]) (lo C)
              unfold respects
              rw [List.pairwise_append]
              refine ⟨hπ_ih_resp, List.pairwise_singleton _ _,
                ?_⟩
              intro y hy b hb
              rw [List.mem_singleton] at hb; subst b
              have hy_ev : y ∈ (ev₁ \ {e₁}) ∪ ev₂ :=
                (hπ_ih_perm.2 y).mp hy
              rcases hy_ev with ⟨hy_ev₁, hy_ne⟩ | hy_ev₂
              · -- y ∈ ev₁ \ {e₁}: use last_is_lo_maximal
                exact last_is_lo_maximal h₁r y
                  ((h₁p'.2 y).mpr ⟨hy_ev₁, hy_ne⟩)
              · -- y ∈ ev₂: need ¬ lo C e₁ y.
                -- Disjunct 1 (vis ∧ ¬commute): by backward
                -- closure.
                -- Disjunct 2 (concurrent rc): needs forward
                -- closure to produce an overwriter for y.
                intro h_lo
                rcases h_lo with ⟨h_vis, h_nc⟩ | ⟨_, _, h_rc_fst, _⟩
                · exact h_e₁_in_ev₂
                    (h_ev₂_closed e₁ y h_vis h_nc hy_ev₂)
                · -- rc-concurrent case: e₁ and y are concurrent,
                  -- rc(e₁,y) = Fst_then_snd, y has no overwriter.
                  -- This requires forward closure infrastructure.
                  sorry
            · -- applySeq state equation
              rw [applySeq_append_single, hπ_ih_state, h_peel]
              congr 1; congr 1; exact h₂s.symm
        · by_cases h_e₁_in_ev₂ : e₁ ∈ ev₂
          · -- Sub-case 3b-ii-a: e₂ ∉ ev₁, e₁ ∈ ev₂.
            -- Symmetric to sub-case 3b-i-b via merge_comm.
            -- Peel e₂ instead of e₁.
            -- The proof follows the same pattern but with sides
            -- swapped. The state equation uses merge_comm +
            -- merge_peel_shared-style reasoning with e₁ as the
            -- shared event in π₂'.
            --
            -- The respects proof has the same obstacle:
            -- the rc-concurrent disjunct of lo for y ∈ ev₁
            -- when e₂ ∉ ev₁ requires forward closure.
            sorry
          · -- Sub-case 3b-ii-b: e₂ ∉ ev₁, e₁ ∉ ev₂ (both local).
            -- Neither e₁ nor e₂ is shared.
            -- Cannot use merge_peel_shared (no shared tail),
            -- merge_peel_comm (neither commutes with all events
            -- on the other side), or bottomUp_2op_reachable
            -- (tails commute with each other).
            --
            -- Witnesses from negated hypotheses:
            --   x₀ ∈ π₂' with ¬D.commutes e₁ x₀
            --   y₀ ∈ π₁' with ¬D.commutes e₂ y₀
            --
            -- The paper's carving approach (partition into L^a/L^b,
            -- find lo-max in L^a, re-permute via
            -- perm_ending_in_lo_max) requires forward closure,
            -- which the current proof architecture doesn't provide.
            sorry
      · -- Case 3a: ¬commute(e₁, e₂). Use bottomUp_2op_reachable.
        have h_e₁_in_ev₁ : e₁ ∈ ev₁ :=
          (h₁p.2 e₁).mp (List.mem_append.mpr (Or.inr
            (List.mem_singleton.mpr rfl)))
        have h_e₂_in_ev₂ : e₂ ∈ ev₂ :=
          (h₂p.2 e₂).mp (List.mem_append.mpr (Or.inr
            (List.mem_singleton.mpr rfl)))
        have h_e₁_in_C : e₁ ∈ C.events := h_ev₁_in_C e₁ h_e₁_in_ev₁
        have h_e₂_in_C : e₂ ∈ C.events := h_ev₂_in_C e₂ h_e₂_in_ev₂
        have h_dist_e₁e₂ : distinctOps e₁ e₂ := by
          obtain ⟨_, _, hL_e₁, hs_e₁⟩ := h_e₁_in_C
          obtain ⟨_, _, hL_e₂, hs_e₂⟩ := h_e₂_in_C
          exact C.timestamps_distinct hL_e₁ hs_e₁ hL_e₂ hs_e₂ h_ne
        -- Inner case-split on shared-event possibilities.
        by_cases h_e₁_in_ev₂ : e₁ ∈ ev₂
        · -- Case 3a-shared-e₁: e₁ ∈ ev₁ ∩ ev₂, ¬commute(e₁, e₂).
          -- Mirror of Case 3a-shared-e₂: peel e₂ from the merge.
          by_cases h_e₂_in_ev₁ : e₂ ∈ ev₁
          · -- Both e₁ ∈ ev₂ and e₂ ∈ ev₁ (both shared).
            -- Requires additional infrastructure (forward closure).
            sorry
          · -- e₂ ∉ ev₁: symmetric to Case 3a-shared-e₂.
            -- Derive the rc direction.
            have h_rc :=
              (hVC.rc_non_comm_directional e₁ e₂ h_dist_e₁e₂).mp
                h_e₁e₂_comm
            rcases h_rc with h_rc_e₁e₂ | h_rc_e₂e₁
            · -- rc(e₁,e₂) = Fst: peel e₂ via merge_peel_shared +
              -- merge_comm.
              -- Step 1: basic membership facts.
              have h_e₁_not_π₁' : e₁ ∉ π₁' := by
                intro h
                have hnd := List.nodup_append.mp h₁p.1
                exact hnd.2.2 e₁ h e₁ (List.mem_singleton.mpr rfl) rfl
              have h_e₂_not_π₂' : e₂ ∉ π₂' := by
                intro h
                have hnd := List.nodup_append.mp h₂p.1
                exact hnd.2.2 e₂ h e₂ (List.mem_singleton.mpr rfl) rfl
              -- Step 2: commutes symmetry.
              have h_nc_swap : ¬ D.commutes e₂ e₁ :=
                fun h => h_e₁e₂_comm (fun s => (h s).symm)
              -- Step 3: peel equation via merge_peel_shared +
              -- merge_comm.
              have h_peel : D.merge s₁ s₂ =
                  D.update (D.merge s₁ (applySeq D D.init π₂')) e₂ := by
                rw [← h₁s, ← h₂s, applySeq_append_single,
                    applySeq_append_single]
                have := merge_peel_shared hVC e₂ e₁ π₂' π₁'
                  h_e₂_in_C h_e₁_in_C h_ev₂_in_C h_ev₁_in_C
                  h₂p h₁p h₂r h₁r h_e₂_in_ev₂ h_e₁_in_ev₁
                  h_e₁_in_ev₂ h_e₂_in_ev₁ (Ne.symm h_ne) h_nc_swap
                  h_rc_e₁e₂ (Ne.symm h_dist_e₁e₂)
                  (h_shared_peel e₂ e₁ (Ne.symm h_dist_e₁e₂))
                rw [hVC.merge_comm, this,
                    hVC.merge_comm (applySeq D D.init π₂')]
              -- Step 4: listPermOf π₂' (ev₂ \ {e₂})
              have h₂p' : listPermOf π₂' (ev₂ \ {e₂}) := by
                constructor
                · exact (List.nodup_append.mp h₂p.1).1
                · intro a; constructor
                  · intro ha
                    exact ⟨(h₂p.2 a).mp (List.mem_append.mpr (Or.inl ha)),
                      fun heq => h_e₂_not_π₂' (heq ▸ ha)⟩
                  · intro ⟨ha_ev, ha_ne⟩
                    rcases List.mem_append.mp ((h₂p.2 a).mpr ha_ev)
                      with h | h
                    · exact h
                    · exact absurd (List.mem_singleton.mp h) ha_ne
              -- Step 5: respects π₂'
              have h₂r' : respects π₂' (lo C) :=
                (List.pairwise_append.mp h₂r).1
              -- Step 6: closures
              have h_ev₂'_closed : ∀ a b, C.vis a b →
                  ¬ D.commutes a b →
                  b ∈ ev₂ \ {e₂} → a ∈ ev₂ \ {e₂} :=
                closure_preserved_by_tail_peel h₂p h₂r h_ev₂_closed
              -- Step 7: events-in-C
              have h_ev₂'_in_C : ∀ a ∈ ev₂ \ {e₂}, a ∈ C.events :=
                fun a ⟨ha, _⟩ => h_ev₂_in_C a ha
              -- Step 8: length
              have h_len' :
                  (π₁' ++ [e₁]).length + π₂'.length < n := by
                simp only [List.length_append, List.length_singleton]
                  at h_len ⊢
                omega
              -- Step 9: ih on (π₁' ++ [e₁], π₂', ev₁, ev₂ \ {e₂})
              obtain ⟨π_ih, hπ_ih_perm, hπ_ih_resp, hπ_ih_state⟩ :=
                ih _ h_len' (π₁' ++ [e₁]) π₂' ev₁ (ev₂ \ {e₂})
                  s₁ (applySeq D D.init π₂')
                  rfl h_ev₁_in_C h_ev₂'_in_C h_ev₁_closed
                  h_ev₂'_closed h₁p h₂p' h₁r h₂r' h₁s rfl
              -- Step 10: e₂ ∉ π_ih
              have h_e₂_not_π_ih : e₂ ∉ π_ih := by
                intro h_in
                rcases (hπ_ih_perm.2 e₂).mp h_in with h | ⟨_, hne⟩
                · exact h_e₂_in_ev₁ h
                · exact hne rfl
              -- Step 11: final witness π_ih ++ [e₂].
              refine ⟨π_ih ++ [e₂], ?_, ?_, ?_⟩
              · -- listPermOf
                obtain ⟨hnd_ih, hm_ih⟩ := hπ_ih_perm
                refine ⟨?_, fun a => ?_⟩
                · rw [List.nodup_append]
                  refine ⟨hnd_ih, List.nodup_singleton _, ?_⟩
                  intro x hx y hy
                  rw [List.mem_singleton] at hy; subst y
                  intro heq; subst heq
                  exact h_e₂_not_π_ih hx
                · rw [List.mem_append, List.mem_singleton,
                      Set.mem_union]
                  constructor
                  · rintro (h | rfl)
                    · rcases (hm_ih a).mp h with h_ev | ⟨h_ev, _⟩
                      · exact Or.inl h_ev
                      · exact Or.inr h_ev
                    · exact Or.inr h_e₂_in_ev₂
                  · intro h
                    by_cases hae : a = e₂
                    · exact Or.inr hae
                    · refine Or.inl ((hm_ih a).mpr ?_)
                      rcases h with h | h
                      · exact Or.inl h
                      · exact Or.inr ⟨h, hae⟩
              · -- respects
                unfold respects
                rw [List.pairwise_append]
                refine ⟨hπ_ih_resp, List.pairwise_singleton _ _, ?_⟩
                intro y hy b hb
                rw [List.mem_singleton] at hb; subst b
                have hy_ev : y ∈ ev₁ ∪ (ev₂ \ {e₂}) :=
                  (hπ_ih_perm.2 y).mp hy
                rcases hy_ev with hy_ev₁ | ⟨hy_ev₂, hy_ne⟩
                · -- y ∈ ev₁: use no_lo_of_not_mem_and_rc.
                  have hy_ne_e₂ : y ≠ e₂ :=
                    fun heq => h_e₂_in_ev₁ (heq ▸ hy_ev₁)
                  exact no_lo_of_not_mem_and_rc hVC h_e₂_in_C
                    h_e₁_in_C h_ev₁_in_C h_e₂_in_ev₁ h_ev₁_closed
                    (Ne.symm h_ne) h_rc_e₁e₂ y hy_ev₁ hy_ne_e₂
                · -- y ∈ ev₂ \ {e₂}: use last_is_lo_maximal on π₂.
                  have hy_π₂' : y ∈ π₂' := by
                    rcases List.mem_append.mp ((h₂p.2 y).mpr hy_ev₂)
                      with h | h
                    · exact h
                    · exact absurd (List.mem_singleton.mp h) hy_ne
                  exact last_is_lo_maximal h₂r y hy_π₂'
              · -- applySeq state equation
                rw [applySeq_append_single, hπ_ih_state, h_peel]
            · -- rc(e₂,e₁) = Fst: blocked by forward-closure issue.
              -- Peeling e₂ requires rc(e₁,e₂) = Fst for the
              -- `no_lo_of_not_mem_and_rc` respects argument, which
              -- we don't have. This direction needs forward-closure
              -- or a fundamentally different approach.
              sorry
        · by_cases h_e₂_in_ev₁ : e₂ ∈ ev₁
          · -- Case 3a-shared-e₂: e₂ ∈ ev₁ ∩ ev₂, e₁ ∉ ev₂,
            -- ¬commute(e₁, e₂).
            --
            -- Strategy: peel e₁ from the merge using
            -- `merge_peel_shared`, then recurse via `ih` on
            -- (ev₁ \ {e₁}, ev₂) with smaller total length.
            --
            -- Derive the rc direction.
            have h_rc :=
              (hVC.rc_non_comm_directional e₁ e₂ h_dist_e₁e₂).mp
                h_e₁e₂_comm
            rcases h_rc with h_rc_e₁e₂ | h_rc_e₂e₁
            · -- rc(e₁,e₂) = Fst, rc(e₂,e₁) ≠ Fst.
              -- Peeling e₁ requires rc(e₂,e₁) = Fst for the
              -- `no_lo_of_not_mem_and_rc` respects argument, which
              -- we don't have. Peeling e₂ is blocked because
              -- e₂ ∈ ev₁ means the respects proof for y ∈ ev₁
              -- fails. This sub-case needs forward-closure or a
              -- fundamentally different approach.
              sorry
            · -- rc(e₂,e₁) = Fst: peel e₁ via merge_peel_shared.
              -- Step 1: basic membership facts.
              have h_e₁_not_π₁' : e₁ ∉ π₁' := by
                intro h
                have hnd := List.nodup_append.mp h₁p.1
                exact hnd.2.2 e₁ h e₁ (List.mem_singleton.mpr rfl) rfl
              have h_e₂_not_π₂' : e₂ ∉ π₂' := by
                intro h
                have hnd := List.nodup_append.mp h₂p.1
                exact hnd.2.2 e₂ h e₂ (List.mem_singleton.mpr rfl) rfl
              -- Step 2: peel equation via merge_peel_shared.
              have h_peel : D.merge s₁ s₂ =
                  D.update (D.merge (applySeq D D.init π₁') s₂) e₁ := by
                rw [← h₁s, ← h₂s, applySeq_append_single,
                    applySeq_append_single]
                have := merge_peel_shared hVC e₁ e₂ π₁' π₂'
                  h_e₁_in_C h_e₂_in_C h_ev₁_in_C h_ev₂_in_C
                  h₁p h₂p h₁r h₂r h_e₁_in_ev₁ h_e₂_in_ev₂
                  h_e₂_in_ev₁ h_e₁_in_ev₂ h_ne h_e₁e₂_comm
                  h_rc_e₂e₁ h_dist_e₁e₂
                  (h_shared_peel e₁ e₂ h_dist_e₁e₂)
                rw [this]
              -- Step 3: listPermOf π₁' (ev₁ \ {e₁})
              have h₁p' : listPermOf π₁' (ev₁ \ {e₁}) := by
                constructor
                · exact (List.nodup_append.mp h₁p.1).1
                · intro a; constructor
                  · intro ha
                    exact ⟨(h₁p.2 a).mp (List.mem_append.mpr (Or.inl ha)),
                      fun heq => h_e₁_not_π₁' (heq ▸ ha)⟩
                  · intro ⟨ha_ev, ha_ne⟩
                    rcases List.mem_append.mp ((h₁p.2 a).mpr ha_ev)
                      with h | h
                    · exact h
                    · exact absurd (List.mem_singleton.mp h) ha_ne
              -- Step 4: respects π₁'
              have h₁r' : respects π₁' (lo C) :=
                (List.pairwise_append.mp h₁r).1
              -- Step 5: closures
              have h_ev₁'_closed : ∀ a b, C.vis a b → ¬ D.commutes a b →
                  b ∈ ev₁ \ {e₁} → a ∈ ev₁ \ {e₁} :=
                closure_preserved_by_tail_peel h₁p h₁r h_ev₁_closed
              -- Step 6: events-in-C
              have h_ev₁'_in_C : ∀ a ∈ ev₁ \ {e₁}, a ∈ C.events :=
                fun a ⟨ha, _⟩ => h_ev₁_in_C a ha
              -- Step 7: length
              have h_len' : π₁'.length + (π₂' ++ [e₂]).length < n := by
                simp only [List.length_append, List.length_singleton]
                  at h_len ⊢
                omega
              -- Step 8: ih on (π₁', π₂' ++ [e₂], ev₁ \ {e₁}, ev₂)
              obtain ⟨π_ih, hπ_ih_perm, hπ_ih_resp, hπ_ih_state⟩ :=
                ih _ h_len' π₁' (π₂' ++ [e₂]) (ev₁ \ {e₁}) ev₂
                  (applySeq D D.init π₁') s₂
                  rfl h_ev₁'_in_C h_ev₂_in_C h_ev₁'_closed h_ev₂_closed
                  h₁p' h₂p h₁r' h₂r rfl h₂s
              -- Step 9: e₁ ∉ π_ih
              have h_e₁_not_π_ih : e₁ ∉ π_ih := by
                intro h_in
                rcases (hπ_ih_perm.2 e₁).mp h_in with ⟨_, hne⟩ | h
                · exact hne rfl
                · exact h_e₁_in_ev₂ h
              -- Step 10: final witness π_ih ++ [e₁].
              refine ⟨π_ih ++ [e₁], ?_, ?_, ?_⟩
              · -- listPermOf
                obtain ⟨hnd_ih, hm_ih⟩ := hπ_ih_perm
                refine ⟨?_, fun a => ?_⟩
                · rw [List.nodup_append]
                  refine ⟨hnd_ih, List.nodup_singleton _, ?_⟩
                  intro x hx y hy
                  rw [List.mem_singleton] at hy; subst y
                  intro heq; subst heq
                  exact h_e₁_not_π_ih hx
                · rw [List.mem_append, List.mem_singleton, Set.mem_union]
                  constructor
                  · rintro (h | rfl)
                    · rcases (hm_ih a).mp h with ⟨h_ev, _⟩ | h_ev
                      · exact Or.inl h_ev
                      · exact Or.inr h_ev
                    · exact Or.inl h_e₁_in_ev₁
                  · intro h
                    by_cases hae : a = e₁
                    · exact Or.inr hae
                    · refine Or.inl ((hm_ih a).mpr ?_)
                      rcases h with h | h
                      · exact Or.inl ⟨h, hae⟩
                      · exact Or.inr h
              · -- respects
                unfold respects
                rw [List.pairwise_append]
                refine ⟨hπ_ih_resp, List.pairwise_singleton _ _, ?_⟩
                intro y hy b hb
                rw [List.mem_singleton] at hb; subst b
                have hy_ev : y ∈ (ev₁ \ {e₁}) ∪ ev₂ :=
                  (hπ_ih_perm.2 y).mp hy
                rcases hy_ev with ⟨hy_ev₁, hy_ne⟩ | hy_ev₂
                · -- y ∈ ev₁ \ {e₁}: use last_is_lo_maximal on π₁.
                  have hy_π₁' : y ∈ π₁' := by
                    rcases List.mem_append.mp ((h₁p.2 y).mpr hy_ev₁)
                      with h | h
                    · exact h
                    · exact absurd (List.mem_singleton.mp h) hy_ne
                  exact last_is_lo_maximal h₁r y hy_π₁'
                · -- y ∈ ev₂: use no_lo_of_not_mem_and_rc.
                  have hy_ne_e₁ : y ≠ e₁ :=
                    fun heq => h_e₁_in_ev₂ (heq ▸ hy_ev₂)
                  exact no_lo_of_not_mem_and_rc hVC h_e₁_in_C
                    h_e₂_in_C h_ev₂_in_C h_e₁_in_ev₂ h_ev₂_closed
                    h_ne h_rc_e₂e₁ y hy_ev₂ hy_ne_e₁
              · -- applySeq state equation
                rw [applySeq_append_single, hπ_ih_state, h_peel]
          · -- Both strictly local: e₁ ∈ ev₁ \ ev₂, e₂ ∈ ev₂ \ ev₁.
            have h_diff_rep : differentReplicas e₁ e₂ :=
              differentReplicas_of_closure h_e₁_in_C h_e₂_in_C
                h_e₁_in_ev₁ h_e₁_in_ev₂ h_e₂_in_ev₂ h_e₂_in_ev₁
                h_ev₁_closed h_ev₂_closed h_e₁e₂_comm h_ne
            -- Directional rc gives a Fst direction.
            have h_rc :=
              (hVC.rc_non_comm_directional e₁ e₂ h_dist_e₁e₂).mp h_e₁e₂_comm
            rcases h_rc with h_rc_e₁e₂ | h_rc_e₂e₁
            · -- rc(e₁,e₂) = Fst: peel e₂ via bottomUp_2op_reachable
              -- with (e₂, e₁) and merge_comm to flip the merge.
              have h_e₁_not_π₁' : e₁ ∉ π₁' := by
                intro h
                have hnd := List.nodup_append.mp h₁p.1
                exact hnd.2.2 e₁ h e₁ (List.mem_singleton.mpr rfl) rfl
              have h_e₂_not_π₂' : e₂ ∉ π₂' := by
                intro h
                have hnd := List.nodup_append.mp h₂p.1
                exact hnd.2.2 e₂ h e₂ (List.mem_singleton.mpr rfl) rfl
              have h_π₁'_in_C : ∀ y ∈ π₁', y ∈ C.events := by
                intro y hy
                exact h_ev₁_in_C y ((h₁p.2 y).mp
                  (List.mem_append.mpr (Or.inl hy)))
              have h_π₂'_in_C : ∀ y ∈ π₂', y ∈ C.events := by
                intro y hy
                exact h_ev₂_in_C y ((h₂p.2 y).mp
                  (List.mem_append.mpr (Or.inl hy)))
              have h_diff_rep_swap : differentReplicas e₂ e₁ :=
                fun h => h_diff_rep h.symm
              have h_dist_e₂e₁ : distinctOps e₂ e₁ := Ne.symm h_dist_e₁e₂
              -- Distinctness with elements of π₁' (left of bottomUp,
              -- which holds π₂' for this orientation).
              have h_dist_a_e₂ : ∀ y ∈ π₂', distinctOps e₂ y := by
                intro y hy
                obtain ⟨_, _, hL_e₂, hs_e₂⟩ := h_e₂_in_C
                obtain ⟨_, _, hL_y, hs_y⟩ := h_π₂'_in_C y hy
                have hne : e₂ ≠ y := fun heq => h_e₂_not_π₂' (heq ▸ hy)
                exact C.timestamps_distinct hL_e₂ hs_e₂ hL_y hs_y hne
              have h_dist_a_e₁ : ∀ y ∈ π₂', distinctOps e₁ y := by
                intro y hy
                obtain ⟨_, _, hL_e₁, hs_e₁⟩ := h_e₁_in_C
                obtain ⟨_, _, hL_y, hs_y⟩ := h_π₂'_in_C y hy
                have hy_in_ev₂ : y ∈ ev₂ :=
                  (h₂p.2 y).mp (List.mem_append.mpr (Or.inl hy))
                have hne : e₁ ≠ y :=
                  fun heq => h_e₁_in_ev₂ (heq ▸ hy_in_ev₂)
                exact C.timestamps_distinct hL_e₁ hs_e₁ hL_y hs_y hne
              -- Distinctness with elements of π₁' (right of bottomUp,
              -- which holds π₁' for this orientation).
              have h_dist_b_e₂ : ∀ y ∈ π₁', distinctOps e₂ y := by
                intro y hy
                obtain ⟨_, _, hL_e₂, hs_e₂⟩ := h_e₂_in_C
                obtain ⟨_, _, hL_y, hs_y⟩ := h_π₁'_in_C y hy
                have hy_in_ev₁ : y ∈ ev₁ :=
                  (h₁p.2 y).mp (List.mem_append.mpr (Or.inl hy))
                have hne : e₂ ≠ y :=
                  fun heq => h_e₂_in_ev₁ (heq ▸ hy_in_ev₁)
                exact C.timestamps_distinct hL_e₂ hs_e₂ hL_y hs_y hne
              have h_dist_b_e₁ : ∀ y ∈ π₁', distinctOps e₁ y := by
                intro y hy
                obtain ⟨_, _, hL_e₁, hs_e₁⟩ := h_e₁_in_C
                obtain ⟨_, _, hL_y, hs_y⟩ := h_π₁'_in_C y hy
                have hne : e₁ ≠ y := fun heq => h_e₁_not_π₁' (heq ▸ hy)
                exact C.timestamps_distinct hL_e₁ hs_e₁ hL_y hs_y hne
              -- Apply bottomUp_2op_reachable with (o₁ = e₂, o₂ = e₁,
              -- π_a = π₂', π_b = π₁'). h_rc_e₁e₂ : rc e₁ e₂ = Fst,
              -- which matches `D.rc o₂ o₁ = Fst`.
              have h_peel_swap :
                  D.merge (D.update (applySeq D D.init π₂') e₂)
                          (D.update (applySeq D D.init π₁') e₁)
                  = D.update (D.merge (applySeq D D.init π₂')
                              (D.update (applySeq D D.init π₁') e₁)) e₂ :=
                bottomUp_2op_reachable hVC e₂ e₁ h_rc_e₁e₂
                  h_diff_rep_swap h_dist_e₂e₁ π₂' π₁'
                  h_dist_a_e₂ h_dist_a_e₁ h_dist_b_e₂ h_dist_b_e₁
              -- Use merge_comm to flip merge orientation.
              have hs₁_form : D.update (applySeq D D.init π₁') e₁ = s₁ := by
                rw [← h₁s, applySeq_append_single]
              have hs₂_form : D.update (applySeq D D.init π₂') e₂ = s₂ := by
                rw [← h₂s, applySeq_append_single]
              -- Goal: D.merge s₁ s₂ = D.update (D.merge ?something) e₂.
              have h_peel : D.merge s₁ s₂ =
                  D.update (D.merge s₁ (applySeq D D.init π₂')) e₂ := by
                rw [hVC.merge_comm s₁ s₂, ← hs₁_form, ← hs₂_form,
                    h_peel_swap, hVC.merge_comm]
              -- Step 3: listPermOf π₂' (ev₂ \ {e₂})
              have h₂p' : listPermOf π₂' (ev₂ \ {e₂}) := by
                constructor
                · exact (List.nodup_append.mp h₂p.1).1
                · intro a; constructor
                  · intro ha
                    exact ⟨(h₂p.2 a).mp (List.mem_append.mpr (Or.inl ha)),
                      fun heq => h_e₂_not_π₂' (heq ▸ ha)⟩
                  · intro ⟨ha_ev, ha_ne⟩
                    rcases List.mem_append.mp ((h₂p.2 a).mpr ha_ev)
                      with h | h
                    · exact h
                    · exact absurd (List.mem_singleton.mp h) ha_ne
              have h₂r' : respects π₂' (lo C) :=
                (List.pairwise_append.mp h₂r).1
              have h_ev₂'_closed : ∀ a b, C.vis a b → ¬ D.commutes a b →
                  b ∈ ev₂ \ {e₂} → a ∈ ev₂ \ {e₂} :=
                closure_preserved_by_tail_peel h₂p h₂r h_ev₂_closed
              have h_ev₂'_in_C : ∀ a ∈ ev₂ \ {e₂}, a ∈ C.events :=
                fun a ⟨ha, _⟩ => h_ev₂_in_C a ha
              have h_len' : (π₁' ++ [e₁]).length + π₂'.length < n := by
                simp only [List.length_append, List.length_singleton]
                  at h_len ⊢
                omega
              -- Apply ih on (π₁' ++ [e₁], π₂', ev₁, ev₂ \ {e₂}).
              obtain ⟨π_ih, hπ_ih_perm, hπ_ih_resp, hπ_ih_state⟩ :=
                ih _ h_len' (π₁' ++ [e₁]) π₂' ev₁ (ev₂ \ {e₂})
                  s₁ (applySeq D D.init π₂')
                  rfl h_ev₁_in_C h_ev₂'_in_C h_ev₁_closed h_ev₂'_closed
                  h₁p h₂p' h₁r h₂r' h₁s rfl
              have h_e₂_not_π_ih : e₂ ∉ π_ih := by
                intro h_in
                rcases (hπ_ih_perm.2 e₂).mp h_in with h | ⟨_, hne⟩
                · exact h_e₂_in_ev₁ h
                · exact hne rfl
              refine ⟨π_ih ++ [e₂], ?_, ?_, ?_⟩
              · obtain ⟨hnd_ih, hm_ih⟩ := hπ_ih_perm
                refine ⟨?_, fun a => ?_⟩
                · rw [List.nodup_append]
                  refine ⟨hnd_ih, List.nodup_singleton _, ?_⟩
                  intro x hx y hy
                  rw [List.mem_singleton] at hy; subst y
                  intro heq; subst heq
                  exact h_e₂_not_π_ih hx
                · rw [List.mem_append, List.mem_singleton, Set.mem_union]
                  constructor
                  · rintro (h | rfl)
                    · rcases (hm_ih a).mp h with h_ev | ⟨h_ev, _⟩
                      · exact Or.inl h_ev
                      · exact Or.inr h_ev
                    · exact Or.inr h_e₂_in_ev₂
                  · intro h
                    by_cases hae : a = e₂
                    · exact Or.inr hae
                    · refine Or.inl ((hm_ih a).mpr ?_)
                      rcases h with h | h
                      · exact Or.inl h
                      · exact Or.inr ⟨h, hae⟩
              · unfold respects
                rw [List.pairwise_append]
                refine ⟨hπ_ih_resp, List.pairwise_singleton _ _, ?_⟩
                intro y hy b hb
                rw [List.mem_singleton] at hb; subst b
                have hy_ev : y ∈ ev₁ ∪ (ev₂ \ {e₂}) :=
                  (hπ_ih_perm.2 y).mp hy
                rcases hy_ev with hy_ev₁ | ⟨hy_ev₂, hy_ne⟩
                · -- y ∈ ev₁: use no_lo_of_not_mem_and_rc with rc(e₁,e₂)=Fst.
                  have hy_ne_e₂ : y ≠ e₂ :=
                    fun heq => h_e₂_in_ev₁ (heq ▸ hy_ev₁)
                  exact no_lo_of_not_mem_and_rc hVC h_e₂_in_C
                    h_e₁_in_C h_ev₁_in_C h_e₂_in_ev₁ h_ev₁_closed
                    (Ne.symm h_ne) h_rc_e₁e₂ y hy_ev₁ hy_ne_e₂
                · -- y ∈ ev₂ \ {e₂}: use last_is_lo_maximal on π₂.
                  have hy_π₂' : y ∈ π₂' := by
                    rcases List.mem_append.mp ((h₂p.2 y).mpr hy_ev₂)
                      with h | h
                    · exact h
                    · exact absurd (List.mem_singleton.mp h) hy_ne
                  exact last_is_lo_maximal h₂r y hy_π₂'
              · rw [applySeq_append_single, hπ_ih_state, h_peel]
            · -- rc(e₂,e₁) = Fst: peel e₁ via bottomUp_2op_reachable.
              -- Step 1: distinctness premises for bottomUp_2op_reachable.
              have h_e₁_not_π₁' : e₁ ∉ π₁' := by
                intro h
                have hnd := List.nodup_append.mp h₁p.1
                exact hnd.2.2 e₁ h e₁ (List.mem_singleton.mpr rfl) rfl
              have h_e₂_not_π₂' : e₂ ∉ π₂' := by
                intro h
                have hnd := List.nodup_append.mp h₂p.1
                exact hnd.2.2 e₂ h e₂ (List.mem_singleton.mpr rfl) rfl
              -- All events in π₁' are in C.events (∈ ev₁).
              have h_π₁'_in_C : ∀ y ∈ π₁', y ∈ C.events := by
                intro y hy
                exact h_ev₁_in_C y ((h₁p.2 y).mp
                  (List.mem_append.mpr (Or.inl hy)))
              have h_π₂'_in_C : ∀ y ∈ π₂', y ∈ C.events := by
                intro y hy
                exact h_ev₂_in_C y ((h₂p.2 y).mp
                  (List.mem_append.mpr (Or.inl hy)))
              -- Distinctness of e₁ with each y ∈ π₁'.
              have h_dist_a_e₁ : ∀ y ∈ π₁', distinctOps e₁ y := by
                intro y hy
                obtain ⟨_, _, hL_e₁, hs_e₁⟩ := h_e₁_in_C
                obtain ⟨_, _, hL_y, hs_y⟩ := h_π₁'_in_C y hy
                have hne : e₁ ≠ y := fun heq => h_e₁_not_π₁' (heq ▸ hy)
                exact C.timestamps_distinct hL_e₁ hs_e₁ hL_y hs_y hne
              have h_dist_a_e₂ : ∀ y ∈ π₁', distinctOps e₂ y := by
                intro y hy
                obtain ⟨_, _, hL_e₂, hs_e₂⟩ := h_e₂_in_C
                obtain ⟨_, _, hL_y, hs_y⟩ := h_π₁'_in_C y hy
                have hy_in_ev₁ : y ∈ ev₁ :=
                  (h₁p.2 y).mp (List.mem_append.mpr (Or.inl hy))
                have hne : e₂ ≠ y :=
                  fun heq => h_e₂_in_ev₁ (heq ▸ hy_in_ev₁)
                exact C.timestamps_distinct hL_e₂ hs_e₂ hL_y hs_y hne
              have h_dist_b_e₁ : ∀ y ∈ π₂', distinctOps e₁ y := by
                intro y hy
                obtain ⟨_, _, hL_e₁, hs_e₁⟩ := h_e₁_in_C
                obtain ⟨_, _, hL_y, hs_y⟩ := h_π₂'_in_C y hy
                have hy_in_ev₂ : y ∈ ev₂ :=
                  (h₂p.2 y).mp (List.mem_append.mpr (Or.inl hy))
                have hne : e₁ ≠ y :=
                  fun heq => h_e₁_in_ev₂ (heq ▸ hy_in_ev₂)
                exact C.timestamps_distinct hL_e₁ hs_e₁ hL_y hs_y hne
              have h_dist_b_e₂ : ∀ y ∈ π₂', distinctOps e₂ y := by
                intro y hy
                obtain ⟨_, _, hL_e₂, hs_e₂⟩ := h_e₂_in_C
                obtain ⟨_, _, hL_y, hs_y⟩ := h_π₂'_in_C y hy
                have hne : e₂ ≠ y := fun heq => h_e₂_not_π₂' (heq ▸ hy)
                exact C.timestamps_distinct hL_e₂ hs_e₂ hL_y hs_y hne
              -- Step 2: Apply bottomUp_2op_reachable.
              have h_peel : D.merge s₁ s₂ =
                  D.update (D.merge (applySeq D D.init π₁')
                    (D.update (applySeq D D.init π₂') e₂)) e₁ := by
                rw [← h₁s, ← h₂s, applySeq_append_single,
                    applySeq_append_single]
                exact bottomUp_2op_reachable hVC e₁ e₂ h_rc_e₂e₁
                  h_diff_rep h_dist_e₁e₂ π₁' π₂'
                  h_dist_a_e₁ h_dist_a_e₂ h_dist_b_e₁ h_dist_b_e₂
              -- Note: D.merge a (D.update b e₂) = ... we need to
              -- bring `D.update (applySeq init π₂') e₂ = s₂`.
              have hs₂_form : D.update (applySeq D D.init π₂') e₂ = s₂ := by
                rw [← h₂s, applySeq_append_single]
              rw [hs₂_form] at h_peel
              -- Step 3: listPermOf π₁' (ev₁ \ {e₁})
              have h₁p' : listPermOf π₁' (ev₁ \ {e₁}) := by
                constructor
                · exact (List.nodup_append.mp h₁p.1).1
                · intro a; constructor
                  · intro ha
                    exact ⟨(h₁p.2 a).mp (List.mem_append.mpr (Or.inl ha)),
                      fun heq => h_e₁_not_π₁' (heq ▸ ha)⟩
                  · intro ⟨ha_ev, ha_ne⟩
                    rcases List.mem_append.mp ((h₁p.2 a).mpr ha_ev)
                      with h | h
                    · exact h
                    · exact absurd (List.mem_singleton.mp h) ha_ne
              -- Step 4: respects π₁'
              have h₁r' : respects π₁' (lo C) :=
                (List.pairwise_append.mp h₁r).1
              -- Step 5: closures
              have h_ev₁'_closed : ∀ a b, C.vis a b → ¬ D.commutes a b →
                  b ∈ ev₁ \ {e₁} → a ∈ ev₁ \ {e₁} :=
                closure_preserved_by_tail_peel h₁p h₁r h_ev₁_closed
              -- Step 6: events-in-C
              have h_ev₁'_in_C : ∀ a ∈ ev₁ \ {e₁}, a ∈ C.events :=
                fun a ⟨ha, _⟩ => h_ev₁_in_C a ha
              -- Step 7: length
              have h_len' : π₁'.length + (π₂' ++ [e₂]).length < n := by
                simp only [List.length_append, List.length_singleton]
                  at h_len ⊢
                omega
              -- Step 8: ih
              obtain ⟨π_ih, hπ_ih_perm, hπ_ih_resp, hπ_ih_state⟩ :=
                ih _ h_len' π₁' (π₂' ++ [e₂]) (ev₁ \ {e₁}) ev₂
                  (applySeq D D.init π₁') s₂
                  rfl h_ev₁'_in_C h_ev₂_in_C h_ev₁'_closed h_ev₂_closed
                  h₁p' h₂p h₁r' h₂r rfl h₂s
              -- Step 9: e₁ ∉ π_ih (since π_ih perms (ev₁\{e₁}) ∪ ev₂
              -- and e₁ ∉ both).
              have h_e₁_not_π_ih : e₁ ∉ π_ih := by
                intro h_in
                rcases (hπ_ih_perm.2 e₁).mp h_in with ⟨_, hne⟩ | h
                · exact hne rfl
                · exact h_e₁_in_ev₂ h
              -- Step 10: final witness π_ih ++ [e₁].
              refine ⟨π_ih ++ [e₁], ?_, ?_, ?_⟩
              · -- listPermOf
                obtain ⟨hnd_ih, hm_ih⟩ := hπ_ih_perm
                refine ⟨?_, fun a => ?_⟩
                · rw [List.nodup_append]
                  refine ⟨hnd_ih, List.nodup_singleton _, ?_⟩
                  intro x hx y hy
                  rw [List.mem_singleton] at hy; subst y
                  intro heq; subst heq
                  exact h_e₁_not_π_ih hx
                · rw [List.mem_append, List.mem_singleton, Set.mem_union]
                  constructor
                  · rintro (h | rfl)
                    · rcases (hm_ih a).mp h with ⟨h_ev, _⟩ | h_ev
                      · exact Or.inl h_ev
                      · exact Or.inr h_ev
                    · exact Or.inl h_e₁_in_ev₁
                  · intro h
                    by_cases hae : a = e₁
                    · exact Or.inr hae
                    · refine Or.inl ((hm_ih a).mpr ?_)
                      rcases h with h | h
                      · exact Or.inl ⟨h, hae⟩
                      · exact Or.inr h
              · -- respects
                unfold respects
                rw [List.pairwise_append]
                refine ⟨hπ_ih_resp, List.pairwise_singleton _ _, ?_⟩
                intro y hy b hb
                rw [List.mem_singleton] at hb; subst b
                have hy_ev : y ∈ (ev₁ \ {e₁}) ∪ ev₂ :=
                  (hπ_ih_perm.2 y).mp hy
                rcases hy_ev with ⟨hy_ev₁, hy_ne⟩ | hy_ev₂
                · -- y ∈ ev₁ \ {e₁}: use last_is_lo_maximal on π₁.
                  have hy_π₁' : y ∈ π₁' := by
                    rcases List.mem_append.mp ((h₁p.2 y).mpr hy_ev₁)
                      with h | h
                    · exact h
                    · exact absurd (List.mem_singleton.mp h) hy_ne
                  exact last_is_lo_maximal h₁r y hy_π₁'
                · -- y ∈ ev₂. Need ¬ lo C e₁ y.
                  -- Use no_lo_of_not_mem_and_rc with rc(e₂, e₁) = Fst.
                  have hy_ne_e₁ : y ≠ e₁ :=
                    fun heq => h_e₁_in_ev₂ (heq ▸ hy_ev₂)
                  exact no_lo_of_not_mem_and_rc hVC h_e₁_in_C
                    h_e₂_in_C h_ev₂_in_C h_e₁_in_ev₂ h_ev₂_closed
                    h_ne h_rc_e₂e₁ y hy_ev₂ hy_ne_e₁
              · -- applySeq state equation
                rw [applySeq_append_single, hπ_ih_state, h_peel]

/-- **Merge case of the bridge theorem (existential form).**

Given two RA-linearization witnesses for replicas `r₁` and `r₂`,
there exists a witness for the merged configuration: a list `π`
which is a permutation of `ev₁ ∪ ev₂`, respects `lo C`, and applies
to `D.merge s₁ s₂` when folded into `D.init`. -/
theorem merge_linearization_exists
    {D : CRDTSig} (hVC : SatisfiesVCs D)
    {C : Configuration D}
    {π₁ π₂ : List (Op D.AppOp)} {ev₁ ev₂ : Set (Op D.AppOp)}
    {s₁ s₂ : D.State}
    (h_ev₁_in_C : ∀ a ∈ ev₁, a ∈ C.events)
    (h_ev₂_in_C : ∀ a ∈ ev₂, a ∈ C.events)
    (h_ev₁_closed :
      ∀ a b, C.vis a b → ¬ D.commutes a b → b ∈ ev₁ → a ∈ ev₁)
    (h_ev₂_closed :
      ∀ a b, C.vis a b → ¬ D.commutes a b → b ∈ ev₂ → a ∈ ev₂)
    (h₁_perm : listPermOf π₁ ev₁) (h₂_perm : listPermOf π₂ ev₂)
    (h₁_resp : respects π₁ (lo C)) (h₂_resp : respects π₂ (lo C))
    (h₁_state : applySeq D D.init π₁ = s₁)
    (h₂_state : applySeq D D.init π₂ = s₂) :
    ∃ π, listPermOf π (ev₁ ∪ ev₂) ∧
         respects π (lo C) ∧
         applySeq D D.init π = D.merge s₁ s₂ := by
  suffices gen : ∀ n (π₁ π₂ : List (Op D.AppOp)) (ev₁ ev₂ : Set (Op D.AppOp))
                   (s₁ s₂ : D.State),
      π₁.length + π₂.length = n →
      (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
      (∀ a b, C.vis a b → ¬ D.commutes a b → b ∈ ev₁ → a ∈ ev₁) →
      (∀ a b, C.vis a b → ¬ D.commutes a b → b ∈ ev₂ → a ∈ ev₂) →
      listPermOf π₁ ev₁ → listPermOf π₂ ev₂ →
      respects π₁ (lo C) → respects π₂ (lo C) →
      applySeq D D.init π₁ = s₁ → applySeq D D.init π₂ = s₂ →
      ∃ π, listPermOf π (ev₁ ∪ ev₂) ∧ respects π (lo C) ∧
           applySeq D D.init π = D.merge s₁ s₂ by
    exact gen _ π₁ π₂ ev₁ ev₂ s₁ s₂ rfl h_ev₁_in_C h_ev₂_in_C
      h_ev₁_closed h_ev₂_closed
      h₁_perm h₂_perm h₁_resp h₂_resp h₁_state h₂_state
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro π₁ π₂ ev₁ ev₂ s₁ s₂ h_len h_ev₁_in_C h_ev₂_in_C
      h_ev₁_closed h_ev₂_closed h₁p h₂p h₁r h₂r h₁s h₂s
    rcases List.eq_nil_or_concat' π₁ with rfl | ⟨π₁', e₁, rfl⟩
    · rcases List.eq_nil_or_concat' π₂ with rfl | ⟨π₂', e₂, rfl⟩
      · obtain ⟨_, hm₁⟩ := h₁p
        obtain ⟨_, hm₂⟩ := h₂p
        have hev₁_empty : ev₁ = ∅ := by
          ext a; exact ⟨fun ha => absurd ((hm₁ a).mpr ha) List.not_mem_nil, fun ha => ha.elim⟩
        have hev₂_empty : ev₂ = ∅ := by
          ext a; exact ⟨fun ha => absurd ((hm₂ a).mpr ha) List.not_mem_nil, fun ha => ha.elim⟩
        subst hev₁_empty; subst hev₂_empty
        simp [applySeq] at h₁s h₂s
        subst h₁s; subst h₂s
        refine ⟨[], ⟨List.nodup_nil, fun a => by simp⟩, List.Pairwise.nil, ?_⟩
        simp [applySeq, hVC.merge_idem]
      · simp [applySeq] at h₁s
        obtain ⟨_, hm₁⟩ := h₁p
        have hev₁_empty : ev₁ = ∅ := by
          ext a; exact ⟨fun ha => absurd ((hm₁ a).mpr ha) List.not_mem_nil, fun ha => ha.elim⟩
        subst hev₁_empty; subst h₁s
        refine ⟨_, ?_, h₂r, ?_⟩
        · simpa [Set.empty_union] using h₂p
        · rw [← h₂s]; exact (merge_init_left_reachable hVC _).symm
    · rcases List.eq_nil_or_concat' π₂ with rfl | ⟨π₂', e₂, rfl⟩
      · simp [applySeq] at h₂s
        obtain ⟨_, hm₂⟩ := h₂p
        have hev₂_empty : ev₂ = ∅ := by
          ext a; exact ⟨fun ha => absurd ((hm₂ a).mpr ha) List.not_mem_nil, fun ha => ha.elim⟩
        subst hev₂_empty; subst h₂s
        refine ⟨_, ?_, h₁r, ?_⟩
        · simpa [Set.union_empty] using h₁p
        · rw [← h₁s]; exact (merge_init_right_reachable hVC _).symm
      · -- Both non-empty: π₁ = π₁' ++ [e₁], π₂ = π₂' ++ [e₂].
        by_cases h_same : e₁ = e₂
        · -- Shared last event: factor via lem_0op + recurse via ih.
          subst h_same
          have h_ev₁'_closed :
              ∀ a b, C.vis a b → ¬ D.commutes a b → b ∈ ev₁ \ {e₁} → a ∈ ev₁ \ {e₁} :=
            closure_preserved_by_tail_peel h₁p h₁r h_ev₁_closed
          have h_ev₂'_closed :
              ∀ a b, C.vis a b → ¬ D.commutes a b → b ∈ ev₂ \ {e₁} → a ∈ ev₂ \ {e₁} :=
            closure_preserved_by_tail_peel h₂p h₂r h_ev₂_closed
          obtain ⟨hnd₁, hmem₁⟩ := h₁p
          obtain ⟨hnd₂, hmem₂⟩ := h₂p
          have he₁_in_ev₁ : e₁ ∈ ev₁ := (hmem₁ e₁).mp (by simp)
          have he₁_in_ev₂ : e₁ ∈ ev₂ := (hmem₂ e₁).mp (by simp)
          rw [List.nodup_append] at hnd₁ hnd₂
          have he₁_not_π₁' : e₁ ∉ π₁' := fun h => hnd₁.2.2 e₁ h e₁ (by simp) rfl
          have he₁_not_π₂' : e₁ ∉ π₂' := fun h => hnd₂.2.2 e₁ h e₁ (by simp) rfl
          have hperm₁' : listPermOf π₁' (ev₁ \ {e₁}) := by
            refine ⟨hnd₁.1, fun a => ?_⟩
            simp only [Set.mem_diff, Set.mem_singleton_iff]
            constructor
            · intro ha
              refine ⟨(hmem₁ a).mp (List.mem_append.mpr (Or.inl ha)), ?_⟩
              intro rfl; exact he₁_not_π₁' ha
            · rintro ⟨ha_ev, ha_ne⟩
              rcases List.mem_append.mp ((hmem₁ a).mpr ha_ev) with h | h
              · exact h
              · rw [List.mem_singleton] at h; exact absurd h ha_ne
          have hperm₂' : listPermOf π₂' (ev₂ \ {e₁}) := by
            refine ⟨hnd₂.1, fun a => ?_⟩
            simp only [Set.mem_diff, Set.mem_singleton_iff]
            constructor
            · intro ha
              refine ⟨(hmem₂ a).mp (List.mem_append.mpr (Or.inl ha)), ?_⟩
              intro rfl; exact he₁_not_π₂' ha
            · rintro ⟨ha_ev, ha_ne⟩
              rcases List.mem_append.mp ((hmem₂ a).mpr ha_ev) with h | h
              · exact h
              · rw [List.mem_singleton] at h; exact absurd h ha_ne
          have hresp_split₁ := List.pairwise_append.mp h₁r
          have hresp_split₂ := List.pairwise_append.mp h₂r
          have hresp₁' : respects π₁' (lo C) := hresp_split₁.1
          have hresp₂' : respects π₂' (lo C) := hresp_split₂.1
          rw [applySeq_append_single] at h₁s h₂s
          simp only [List.length_append, List.length_singleton] at h_len
          have hn'lt : π₁'.length + π₂'.length < n := by omega
          have h_ev₁'_in_C : ∀ a ∈ ev₁ \ {e₁}, a ∈ C.events :=
            fun a ha => h_ev₁_in_C a ha.1
          have h_ev₂'_in_C : ∀ a ∈ ev₂ \ {e₁}, a ∈ C.events :=
            fun a ha => h_ev₂_in_C a ha.1
          obtain ⟨π', hπ'perm, hπ'resp, hπ'state⟩ :=
            ih _ hn'lt π₁' π₂' (ev₁ \ {e₁}) (ev₂ \ {e₁}) _ _ rfl
              h_ev₁'_in_C h_ev₂'_in_C h_ev₁'_closed h_ev₂'_closed
              hperm₁' hperm₂' hresp₁' hresp₂' rfl rfl
          refine ⟨π' ++ [e₁], ?_, ?_, ?_⟩
          · obtain ⟨hnd', hm'⟩ := hπ'perm
            refine ⟨?_, fun a => ?_⟩
            · rw [List.nodup_append]
              refine ⟨hnd', List.nodup_singleton _, ?_⟩
              intro x hx y hy
              rw [List.mem_singleton] at hy; subst y
              intro heq; subst heq
              rcases (hm' x).mp hx with ⟨_, hne⟩ | ⟨_, hne⟩ <;> exact hne rfl
            · rw [List.mem_append, List.mem_singleton, Set.mem_union]
              constructor
              · rintro (h | rfl)
                · rcases (hm' a).mp h with ⟨h_ev, _⟩ | ⟨h_ev, _⟩
                  · exact Or.inl h_ev
                  · exact Or.inr h_ev
                · exact Or.inl he₁_in_ev₁
              · intro h
                by_cases hae : a = e₁
                · exact Or.inr hae
                · exact Or.inl ((hm' a).mpr (by
                    rcases h with h | h
                    · exact Or.inl ⟨h, hae⟩
                    · exact Or.inr ⟨h, hae⟩))
          · unfold respects
            rw [List.pairwise_append]
            refine ⟨hπ'resp, List.pairwise_singleton _ _, ?_⟩
            intro x hx y hy
            rw [List.mem_singleton] at hy; subst y
            have hx_ev : x ∈ ev₁ \ {e₁} ∪ ev₂ \ {e₁} := (hπ'perm.2 x).mp hx
            rcases hx_ev with ⟨hx_ev₁, hx_ne⟩ | ⟨hx_ev₂, hx_ne⟩
            · have hx_π₁' : x ∈ π₁' := by
                rcases List.mem_append.mp ((hmem₁ x).mpr hx_ev₁) with h | h
                · exact h
                · rw [List.mem_singleton] at h; exact absurd h hx_ne
              exact hresp_split₁.2.2 x hx_π₁' e₁ (by simp)
            · have hx_π₂' : x ∈ π₂' := by
                rcases List.mem_append.mp ((hmem₂ x).mpr hx_ev₂) with h | h
                · exact h
                · rw [List.mem_singleton] at h; exact absurd h hx_ne
              exact hresp_split₂.2.2 x hx_π₂' e₁ (by simp)
          · rw [applySeq_append_single, hπ'state, ← hVC.lem_0op, h₁s, h₂s]
        · -- Distinct last events e₁ ≠ e₂.
          -- The shared-ol peel property is now a SatisfiesVCs field
          -- (`shared_peel_1op`); discharge each per-CRDT instance.
          exact distinct_last_case hVC ih h_ev₁_in_C h_ev₂_in_C
            h_ev₁_closed h_ev₂_closed h₁p h₂p h₁r h₂r h₁s h₂s h_len h_same
            hVC.shared_peel_1op

end

/-! ### Packaging

Invoke `merge_linearization_exists` to build the merged replica's
witness from the IH witnesses for `r₁` and `r₂`. -/

/-- `Merge` preserves RA-lin. Intended closure of
`RA_Linearizability.RA_lin_preserved_merge`.

Body: destructure the existential from `merge_linearization_exists`
and thread it through. Closes end-to-end once
`merge_linearization_exists` is fully proved. -/
theorem RA_lin_preserved_merge_via_witness
    {D : CRDTSig} {C C' : Configuration D} (hVC : SatisfiesVCs D)
    {r₁ r₂ : Replica} {s₁ s₂ : D.State}
    {ev₁ ev₂ : Set (Op D.AppOp)}
    (h_s₁  : C.N r₁ = some s₁) (h_s₂  : C.N r₂ = some s₂)
    (h_ev₁ : C.L r₁ = some ev₁) (h_ev₂ : C.L r₂ = some ev₂)
    (hN   : C'.N = updateRep C.N r₁ (D.merge s₁ s₂))
    (hL   : C'.L = updateRep C.L r₁ (ev₁ ∪ ev₂))
    (hvis : C'.vis = C.vis)
    (hRA : IsRALinearizable C) :
    IsRALinearizable C' := by
  intro r' s' E' hN' hL'
  rw [hN] at hN'
  rw [hL] at hL'
  by_cases hr' : r' = r₁
  · -- Merged replica.
    subst hr'
    simp [updateRep] at hN' hL'
    obtain ⟨π₁, hp₁, hr₁, hs₁'⟩ := hRA r' s₁ ev₁ h_s₁ h_ev₁
    obtain ⟨π₂, hp₂, hr₂, hs₂'⟩ := hRA r₂ s₂ ev₂ h_s₂ h_ev₂
    have h_ev₁_in_C : ∀ a ∈ ev₁, a ∈ C.events :=
      fun a ha => ⟨r', ev₁, h_ev₁, ha⟩
    have h_ev₂_in_C : ∀ a ∈ ev₂, a ∈ C.events :=
      fun a ha => ⟨r₂, ev₂, h_ev₂, ha⟩
    -- Causal closure of the top-level event sets follows directly
    -- from `Configuration.vis_causal` on each replica. The weaker
    -- closure threaded through the induction (vis ∧ ¬commute) is
    -- implied by the unconditional `vis_causal`.
    have h_ev₁_closed :
        ∀ a b, C.vis a b → ¬ D.commutes a b → b ∈ ev₁ → a ∈ ev₁ :=
      fun a b hv _ hb => C.vis_causal hv h_ev₁ hb
    have h_ev₂_closed :
        ∀ a b, C.vis a b → ¬ D.commutes a b → b ∈ ev₂ → a ∈ ev₂ :=
      fun a b hv _ hb => C.vis_causal hv h_ev₂ hb
    obtain ⟨π, hperm, hresp, hstate⟩ :=
      merge_linearization_exists (D := D) (C := C) hVC
        h_ev₁_in_C h_ev₂_in_C h_ev₁_closed h_ev₂_closed
        hp₁ hp₂ hr₁ hr₂ hs₁' hs₂'
    refine ⟨π, ?_, ?_, ?_⟩
    · rw [← hL']; exact hperm
    · have : lo C' = lo C := by unfold lo; rw [hvis]
      rw [this]; exact hresp
    · rw [← hN']; exact hstate
  · -- Other replica: IH applies directly.
    simp [updateRep, hr'] at hN' hL'
    obtain ⟨π, hperm, hresp, heq⟩ := hRA r' s' E' hN' hL'
    refine ⟨π, hperm, ?_, heq⟩
    have : lo C' = lo C := by unfold lo; rw [hvis]
    rw [this]; exact hresp

open LabeledTS in
/-- **Bridge theorem (Sal paper, bottom-up linearization).** If a CRDT
`D` satisfies the 24 VCs, every configuration reachable in `S_D` is
RA-linearizable.

Proof plan (lin.tex §3.3 + appendix.tex §A.2): induction on the
execution. CreateReplica and Query are immediate; Apply extends the
linearization by one event; Merge delegates to
`RA_lin_preserved_merge_via_witness` which destructures the
`merge_linearization_exists` existential. -/
theorem ra_linearizable_of_vcs
    (D : CRDTSig) (hVC : SatisfiesVCs D)
    (C : Configuration D)
    (hReach : (labeledTS D).ReachableFrom (initConfig D) C) :
    IsRALinearizable C := by
  induction hReach with
  | refl => exact initConfig_RA_lin D
  | tail _ hs ih =>
    obtain ⟨ℓ, hstep⟩ := hs
    cases hstep with
    | createReplica _ _ hN hL hvis =>
      exact RA_lin_preserved_createReplica hN hL hvis ih
    | apply h_s h_ev h_fresh_t _ hN hL hvis =>
      exact RA_lin_preserved_apply h_s h_ev h_fresh_t hN hL hvis ih
    | merge h_s₁ h_s₂ h_ev₁ h_ev₂ _ hN hL hvis =>
      exact RA_lin_preserved_merge_via_witness hVC h_s₁ h_s₂
        h_ev₁ h_ev₂ hN hL hvis ih
    | query _ _ => exact ih

end Sal.Emulation