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

/-- **Merge case of the bridge theorem (existential form).**

Given two RA-linearization witnesses for replicas `r₁` and `r₂`,
there exists a witness for the merged configuration: a list `π`
which is a permutation of `ev₁ ∪ ev₂`, respects `lo C`, and applies
to `D.merge s₁ s₂` when folded into `D.init`.

Paper reference: Lemma 1 / Theorem 1 of lin.tex §3.3, detailed in
appendix §A.2–A.4.

**Proof strategy** (to be mechanised): strong induction on the total
event count `π₁.length + π₂.length`. At each step, pull an event off
the tail of `π₁` or `π₂` and push it through `merge` using the
appropriate VC (`base_2op`, `ind_right_*`, `ind_left_*`, `inter_*`,
`lem_0op`), recursing on the smaller configuration. Base: both lists
empty; `merge_idem` on `D.init` closes it.

Closing this theorem is the main remaining work for Phase 1 — see
`MERGE_PROOF.md` for the case-analysis plan. -/
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
  -- Generalise then strong-induct on π₁.length + π₂.length.
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
      · -- Both empty.
        obtain ⟨_, hm₁⟩ := h₁p
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
      · -- π₁ = [], π₂ = π₂' ++ [e₂].
        simp [applySeq] at h₁s
        obtain ⟨_, hm₁⟩ := h₁p
        have hev₁_empty : ev₁ = ∅ := by
          ext a; exact ⟨fun ha => absurd ((hm₁ a).mpr ha) List.not_mem_nil, fun ha => ha.elim⟩
        subst hev₁_empty; subst h₁s
        refine ⟨_, ?_, h₂r, ?_⟩
        · simpa [Set.empty_union] using h₂p
        · rw [← h₂s]; exact (merge_init_left_reachable hVC _).symm
    · rcases List.eq_nil_or_concat' π₂ with rfl | ⟨π₂', e₂, rfl⟩
      · -- π₁ = π₁' ++ [e₁], π₂ = [].
        simp [applySeq] at h₂s
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
          -- Compute closure preservation BEFORE destructuring h₁p/h₂p,
          -- since `closure_preserved_by_tail_peel` consumes the full
          -- listPermOf hypothesis.
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
          --
          -- Pending: the paper's appendix (§A.2) closes this case via
          -- the L^a / L^b carving — NOT by peeling π_i.last. The
          -- correct peel candidate is a lo-maximal element within a
          -- specific carving layer (M_1^a, M_2^a, or L_top^a),
          -- chosen so its no-lo-successor property is structural
          -- rather than positional. Concretely the appendix's
          -- structure (specialised to 2-way merge by collapsing LCA
          -- to init):
          --
          --   • Outer induction on |L_1^a ∪ L_2^a|.
          --     - Base |L_1^a ∪ L_2^a| = 0: inner induction on
          --       |L_top^a|. Inner base (L_top^a empty) closes via
          --       MergeIdempotence. Inner step pulls a maximal
          --       L_top^a element via BottomUp-0-OP and recurses on
          --       the M_1^a / M_2^a carving for that LCA event.
          --     - Step: pick a maximal element of M_1^a (or M_2^a);
          --       case-split on rc(e_1, e_2) (commute / e_1 →rc e_2
          --       handled by MergeCommutativity, e_2 →rc e_1 by
          --       BottomUp-2-OP); recurse.
          --
          -- Required machinery beyond what's already proved:
          --   1. lo-maximal element existence inside the carving
          --      layers (uses no_rc_chain to bound lo-acyclicity).
          --   2. Convergence-based re-permutation: given the IH
          --      witness for v_i and a chosen maximal e_i, build a
          --      new lo-respecting permutation of L_i ending in e_i.
          --      (Couples to convergence's open overwriter sorry.)
          --   3. The induction structure itself: |L_1^a ∪ L_2^a|
          --      then |L_top^a| then |M_1^a ∪ M_2^a|, NOT
          --      |π_1| + |π_2| as the current `gen` does.
          --
          -- The current `gen` strong-induction on |π₁| + |π₂|
          -- handles both-empty / asymmetric / shared-last cleanly,
          -- but the distinct-last branch needs the paper's
          -- carving-based structure. Restructuring the induction is
          -- the next session's first decision.
          sorry

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
