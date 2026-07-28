import Sal.CRDTs.Metatheory.Convergence_CounterModel

/-!
# Can `inter_lca_2op` linearize the defeater?

This file mechanically decides whether a bottom-up interchange rule of the
catalogue, in particular `inter_lca_2op` (BottomUp-2-OP), can linearize the
defeater execution by peeling a *remove* last. The two candidate answers:

* **No.** No bottom-up interchange rule can peel a *remove* off either
  head of the defeater's final merge, because a side must lie *in the
  image of the remove operation* to have a remove peeled, and neither head
  does (each head has a nonempty live set).

* **Yes.** `inter_lca_2op` applies and linearizes the execution by peeling
  a remove last.

The test is against the add-wins skeleton `AWSet` of
`Sal/CRDTs/Metatheory/Convergence_CounterModel.lean` (state `(A,D)`,
live set `A ∖ D`, `rem` sets `D := A ∪ D`, `merge` = componentwise union
ignoring its LCA argument). The `inter_lca_2op` statement tested against
is the MRDT one (`_references/neem_fstar_repo/.../App_mrdt.fsti`,
lines 137–143), whose conclusion peels `o1` off the **second** merge
argument, which therefore must have the syntactic shape `do (do a ol) o1`
with `o1` outermost.

## The concrete defeater (faithful folds, not hand-set states)

Tags/replicas: `A_p = add@1` on replica 0, `A_q = add@2` on replica 1,
`R_p = rem@3` on replica 0, `R_q = rem@4` on replica 1.

* `head_p = merge(state[A_p,R_p], v_s)` with `v_s = merge({A_p},{A_q})`;
  its live set is `{2}` (its own tag 1 is dead, the merged-in `A_q` lives).
* `head_q = merge(state[A_q,R_q], v_s)`; live set `{1}`.
* `LCA = v_s`; live set `{1,2}` (the honest intersection realized by a
  staging replica).
* the merged version's state is all-dead (live `∅`).

## Verdict (proved below)

**The answer is No.** Each head has a nonempty live set, hence is *not*
in the image of `rem` (`awset_rem_output_empty`), hence cannot be written
`do (do a ol) o1` (resp. `do (do b ol) o2`) with the peeled op a remove
(`no_rem_peelable_from_defeater_heads`, `crux_no_rem_peel_from_defeater`,
`no_inter_lca_2op_rem_peel_of_defeater`). And the merged
linearization `[A_p,R_p,A_q,R_q]`, a valid witness for the all-dead
merged version, restricts on head_q's own event set to a sequence that
folds to the *wrong* state (`crack1_witness`): a valid merged witness that
is not assembled from state-correct side witnesses.

Everything here is kernel-checked with clean axioms
(`propext, Classical.choice, Quot.sound`); the sorries in the
transitively-imported `Merge_Linearization.lean` are *not* touched by any
theorem in this file (verified via `#print axioms`).
-/

namespace Sal.Emulation

open Classical

/-! ## The live set (= `AWSet.query σ ()`) -/

/-- The live set of an AWSet state: `A ∖ D`. Definitionally
`AWSet.query σ ()`. -/
def awLive (σ : AWState) : Set Timestamp := σ.1 \ σ.2

theorem awLive_eq_query (σ : AWState) : awLive σ = AWSet.query σ () := rfl

/-! ## Deliverable 1: the remove operation outputs an empty live set -/

/-- **`awset_rem_output_empty`.** For *any* state `s` and *any* remove
event `e`, the AWSet remove produces an empty live set:
`(A ∖ (A ∪ D)) = ∅`. This is the algebraic heart of the file: a
state is in the image of `rem` only if it is all-dead. -/
theorem awset_rem_output_empty (s : AWState) {e : Op AWOp}
    (he : e.2.2 = AWOp.rem) :
    awLive (AWSet.update s e) = ∅ := by
  simp only [awLive, AWSet_update, awUpdate_rem he]
  ext x
  simp only [Set.mem_diff, Set.mem_union, Set.mem_empty_iff_false,
    iff_false]
  tauto

/-! ## Deliverable 2: the defeater's three states as faithful folds -/

/-- `A_p = add` at replica 0, tag 1. -/
def A_p : Op AWOp := (1, 0, AWOp.add)
/-- `R_p = rem` at replica 0, tag 3 (sees only `A_p`). -/
def R_p : Op AWOp := (3, 0, AWOp.rem)
/-- `A_q = add` at replica 1, tag 2. -/
def A_q : Op AWOp := (2, 1, AWOp.add)
/-- `R_q = rem` at replica 1, tag 4 (sees only `A_q`). -/
def R_q : Op AWOp := (4, 1, AWOp.rem)

theorem hAp : A_p.2.2 = AWOp.add := rfl
theorem hRp : R_p.2.2 = AWOp.rem := rfl
theorem hAq : A_q.2.2 = AWOp.add := rfl
theorem hRq : R_q.2.2 = AWOp.rem := rfl
theorem tAp : A_p.1 = (1 : Timestamp) := rfl
theorem tAq : A_q.1 = (2 : Timestamp) := rfl

/-- `v_s = merge({A_p}, {A_q})`, the staging version, the honest LCA. -/
noncomputable def LCA : AWState :=
  awMerge (applySeq AWSet AWSet.init [A_p]) (applySeq AWSet AWSet.init [A_q])

/-- `state[A_p, R_p]`, replica p's post-remove one-key version (`p2`). -/
noncomputable def sp : AWState := applySeq AWSet AWSet.init [A_p, R_p]
/-- `state[A_q, R_q]`, replica q's post-remove one-key version (`q2`). -/
noncomputable def sq : AWState := applySeq AWSet AWSet.init [A_q, R_q]

/-- `head_p = merge(state[A_p,R_p], v_s)`, the version `p3`. -/
noncomputable def head_p : AWState := awMerge sp LCA
/-- `head_q = merge(state[A_q,R_q], v_s)`, the version `q3`. -/
noncomputable def head_q : AWState := awMerge sq LCA

theorem sp_eq : sp = ((({1} : Set Timestamp)), (({1} : Set Timestamp))) := by
  show awUpdate (awUpdate AWSet.init A_p) R_p = _
  simp only [AWSet_init, awUpdate_add hAp, awUpdate_rem hRp, tAp]
  refine Prod.ext ?_ ?_ <;> ext x <;>
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_empty_iff_false] <;> grind

theorem sq_eq : sq = ((({2} : Set Timestamp)), (({2} : Set Timestamp))) := by
  show awUpdate (awUpdate AWSet.init A_q) R_q = _
  simp only [AWSet_init, awUpdate_add hAq, awUpdate_rem hRq, tAq]
  refine Prod.ext ?_ ?_ <;> ext x <;>
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_empty_iff_false] <;> grind

theorem vp_eq :
    applySeq AWSet AWSet.init [A_p]
      = ((({1} : Set Timestamp)), ((∅ : Set Timestamp))) := by
  show awUpdate AWSet.init A_p = _
  simp only [AWSet_init, awUpdate_add hAp, tAp]
  refine Prod.ext ?_ ?_ <;> ext x <;>
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_empty_iff_false] <;> grind

theorem vq_eq :
    applySeq AWSet AWSet.init [A_q]
      = ((({2} : Set Timestamp)), ((∅ : Set Timestamp))) := by
  show awUpdate AWSet.init A_q = _
  simp only [AWSet_init, awUpdate_add hAq, tAq]
  refine Prod.ext ?_ ?_ <;> ext x <;>
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_empty_iff_false] <;> grind

theorem LCA_eq :
    LCA = ((({1, 2} : Set Timestamp)), ((∅ : Set Timestamp))) := by
  show awMerge (applySeq AWSet AWSet.init [A_p]) (applySeq AWSet AWSet.init [A_q]) = _
  rw [vp_eq, vq_eq]
  simp only [awMerge]
  refine Prod.ext ?_ ?_ <;> ext x <;>
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_empty_iff_false] <;> grind

theorem head_p_eq :
    head_p = ((({1, 2} : Set Timestamp)), (({1} : Set Timestamp))) := by
  show awMerge sp LCA = _
  rw [sp_eq, LCA_eq]
  simp only [awMerge]
  refine Prod.ext ?_ ?_ <;> ext x <;>
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_empty_iff_false] <;> grind

theorem head_q_eq :
    head_q = ((({1, 2} : Set Timestamp)), (({2} : Set Timestamp))) := by
  show awMerge sq LCA = _
  rw [sq_eq, LCA_eq]
  simp only [awMerge]
  refine Prod.ext ?_ ?_ <;> ext x <;>
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_empty_iff_false] <;> grind

/-- Live set of the honest LCA `v_s` is `{1,2}`, the realized
intersection `L(head_p) ∩ L(head_q)`. -/
theorem LCA_live : awLive LCA = (({1, 2} : Set Timestamp)) := by
  simp only [awLive, LCA_eq]
  ext x
  simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_empty_iff_false]
  grind

/-- **head_p lives on exactly `A_q`'s tag**: live set `{2}`, nonempty. -/
theorem head_p_live : awLive head_p = (({2} : Set Timestamp)) := by
  simp only [awLive, head_p_eq]
  ext x
  simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff]
  grind

/-- **head_q lives on exactly `A_p`'s tag**: live set `{1}`, nonempty. -/
theorem head_q_live : awLive head_q = (({1} : Set Timestamp)) := by
  simp only [awLive, head_q_eq]
  ext x
  simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff]
  grind

/-- Tag 2 witnesses that head_p's live set is nonempty. -/
theorem two_live_in_head_p : (2 : Timestamp) ∈ awLive head_p := by
  rw [head_p_live]; simp

/-- Tag 1 witnesses that head_q's live set is nonempty. -/
theorem one_live_in_head_q : (1 : Timestamp) ∈ awLive head_q := by
  rw [head_q_live]; simp

/-! ## Deliverable 3: neither head is in the image of `rem` -/

/-- **`no_rem_peelable_from_defeater_heads`.** Neither defeater head is in
the image of the AWSet remove: for every state `s` and every remove event
`e`, `head_p ≠ do s e` and `head_q ≠ do s e`.

Consequence: `inter_lca_2op`'s conclusion, whose second merge argument is
`do (do a ol) o1` with `o1` outermost, can never be instantiated with a
head as that argument and `o1` a remove, nor can BottomUp-1-OP/0-OP,
which share the same `do … o1` peel shape. -/
theorem no_rem_peelable_from_defeater_heads :
    (∀ (s : AWState) (e : Op AWOp), e.2.2 = AWOp.rem →
        head_p ≠ AWSet.update s e) ∧
    (∀ (s : AWState) (e : Op AWOp), e.2.2 = AWOp.rem →
        head_q ≠ AWSet.update s e) := by
  refine ⟨?_, ?_⟩
  · intro s e he heq
    have h_empty : awLive head_p = ∅ := by
      rw [heq]; exact awset_rem_output_empty s he
    have h2 : (2 : Timestamp) ∈ awLive head_p := two_live_in_head_p
    rw [h_empty] at h2
    exact absurd h2 (by simp)
  · intro s e he heq
    have h_empty : awLive head_q = ∅ := by
      rw [heq]; exact awset_rem_output_empty s he
    have h1 : (1 : Timestamp) ∈ awLive head_q := one_live_in_head_q
    rw [h_empty] at h1
    exact absurd h1 (by simp)

/-! ## Deliverable 4: THE CRUX CHECK

Can `inter_lca_2op`'s conclusion merge

  `merge (do l ol) (do (do a ol) o1) (do (do b ol) o2)`

be made to equal the defeater's actual `merge(LCA, head_p, head_q)` with
`o1` (the peeled op) or `o2` a *remove*?  The AWSet 3-way merge ignores
its LCA argument, so the merge value is determined by the two head
arguments; the rule is nevertheless applied to a *specific* merge whose
second argument is the a-side head written `do (do a ol) o1` and whose
third is the b-side head written `do (do b ol) o2`. If either of those
outermost ops is a remove, the corresponding head is forced into the image
of `rem`, impossible by Deliverable 3. We prove it CANNOT, in every
assignment of the two heads to the two peelable sides. -/

/-- Neither the peeled a-side op `o1` (matched to either head) nor the
b-side op `o2` (matched to either head) can be a remove. Direct corollary
of the headline (take the inner state `s := do a ol`). -/
theorem crux_no_rem_peel_from_defeater :
    (∀ (a : AWState) (ol o1 : Op AWOp), o1.2.2 = AWOp.rem →
        AWSet.update (AWSet.update a ol) o1 ≠ head_p) ∧
    (∀ (b : AWState) (ol o2 : Op AWOp), o2.2.2 = AWOp.rem →
        AWSet.update (AWSet.update b ol) o2 ≠ head_q) ∧
    (∀ (a : AWState) (ol o1 : Op AWOp), o1.2.2 = AWOp.rem →
        AWSet.update (AWSet.update a ol) o1 ≠ head_q) ∧
    (∀ (b : AWState) (ol o2 : Op AWOp), o2.2.2 = AWOp.rem →
        AWSet.update (AWSet.update b ol) o2 ≠ head_p) := by
  obtain ⟨hp, hq⟩ := no_rem_peelable_from_defeater_heads
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ol o1 ho1 heq; exact hp (AWSet.update a ol) o1 ho1 heq.symm
  · intro b ol o2 ho2 heq; exact hq (AWSet.update b ol) o2 ho2 heq.symm
  · intro a ol o1 ho1 heq; exact hq (AWSet.update a ol) o1 ho1 heq.symm
  · intro b ol o2 ho2 heq; exact hp (AWSet.update b ol) o2 ho2 heq.symm

/-- **The crux, on the exact `inter_lca_2op` merge shape.** There is *no*
instantiation of the conclusion `merge (do l ol) (do (do a ol) o1)
(do (do b ol) o2)` matching the defeater's merge `merge(LCA, head_p,
head_q)`, in either assignment of the two heads to the a-side (the side
`o1` is peeled from) and b-side, in which the peeled op `o1` is a remove.
Hence `inter_lca_2op` cannot linearize the defeater by peeling a remove:
the obstruction holds. -/
theorem no_inter_lca_2op_rem_peel_of_defeater :
    (¬ ∃ (a b : AWState) (ol o1 o2 : Op AWOp),
        o1.2.2 = AWOp.rem ∧
        AWSet.update (AWSet.update a ol) o1 = head_p ∧
        AWSet.update (AWSet.update b ol) o2 = head_q) ∧
    (¬ ∃ (a b : AWState) (ol o1 o2 : Op AWOp),
        o1.2.2 = AWOp.rem ∧
        AWSet.update (AWSet.update a ol) o1 = head_q ∧
        AWSet.update (AWSet.update b ol) o2 = head_p) := by
  obtain ⟨cp, _, cq, _⟩ := crux_no_rem_peel_from_defeater
  refine ⟨?_, ?_⟩
  · rintro ⟨a, b, ol, o1, o2, ho1, ha, _⟩; exact cp a ol o1 ho1 ha
  · rintro ⟨a, b, ol, o1, o2, ho1, ha, _⟩; exact cq a ol o1 ho1 ha

/-! ## Deliverable 5: the crack-1 witness

The merged-version linearization `w = [A_p, R_p, A_q, R_q]`:
(i) is a *valid* witness for the merged version, it folds to the all-dead
merged state; yet (ii) its restriction to head_q's own event set folds to
a state whose live set is `∅ ≠ {1} = L(head_q)`. So `w` is a valid
merged-version witness that is *not* assembled from a state-correct witness
for head_q. -/

/-- The merged version's state = `merge(head_p, head_q)` (the 3-way merge
ignores its LCA argument): all-dead. -/
noncomputable def mergedState : AWState := awMerge head_p head_q

theorem mergedState_eq :
    mergedState = ((({1, 2} : Set Timestamp)), (({1, 2} : Set Timestamp))) := by
  show awMerge head_p head_q = _
  rw [head_p_eq, head_q_eq]
  simp only [awMerge]
  refine Prod.ext ?_ ?_ <;> ext x <;>
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] <;>
    grind

theorem mergedState_live : awLive mergedState = (∅ : Set Timestamp) := by
  simp only [awLive, mergedState_eq]
  ext x
  simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_empty_iff_false]
  grind

/-- The linearization of the merged version. -/
def w : List (Op AWOp) := [A_p, R_p, A_q, R_q]

/-- head_q's own event set (as a list): `{A_p, A_q, R_q}`, it merged in
`v_s`, which contains `A_p`; `R_p` is *not* one of its events. -/
def evHeadQ : List (Op AWOp) := [A_p, A_q, R_q]

/-- The restriction of the merged witness to head_q's event set. -/
def wRestrQ : List (Op AWOp) := w.filter (fun e => decide (e ∈ evHeadQ))

/-- The restriction drops `R_p` (which is not one of head_q's events) and
keeps head_q's own `A_p, A_q, R_q` in `w`'s order. -/
theorem wRestrQ_eq : wRestrQ = [A_p, A_q, R_q] := by decide

/-- `w` folds to the all-dead merged state, a valid merged-version
witness. -/
theorem w_fold : applySeq AWSet AWSet.init w
    = ((({1, 2} : Set Timestamp)), (({1, 2} : Set Timestamp))) := by
  show awUpdate (awUpdate (awUpdate (awUpdate AWSet.init A_p) R_p) A_q) R_q = _
  simp only [AWSet_init, awUpdate_add hAp, awUpdate_rem hRp,
    awUpdate_add hAq, awUpdate_rem hRq, tAp, tAq]
  refine Prod.ext ?_ ?_ <;> ext x <;>
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_empty_iff_false] <;> grind

/-- The restriction to head_q's event set folds to the all-dead state
`({1,2},{1,2})`, *not* head_q's actual state `({1,2},{2})`. -/
theorem wRestrQ_fold : applySeq AWSet AWSet.init wRestrQ
    = ((({1, 2} : Set Timestamp)), (({1, 2} : Set Timestamp))) := by
  rw [wRestrQ_eq]
  show awUpdate (awUpdate (awUpdate AWSet.init A_p) A_q) R_q = _
  simp only [AWSet_init, awUpdate_add hAp, awUpdate_add hAq,
    awUpdate_rem hRq, tAp, tAq]
  refine Prod.ext ?_ ?_ <;> ext x <;>
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_empty_iff_false] <;> grind

/-- **`crack1_witness`.** The merged linearization `w`:
(i) folds to the all-dead merged state (live `∅`), valid;
(ii) but its restriction to head_q's event set folds to a state
     `≠ head_q`, whose live set is `∅ ≠ {1} = L(head_q)`.
A valid merged-version witness that is **not** built from a state-correct
head_q witness. -/
theorem crack1_witness :
    -- (i) valid merged-version witness: folds to all-dead merged state.
    awLive (applySeq AWSet AWSet.init w) = ∅ ∧
    applySeq AWSet AWSet.init w = mergedState ∧
    -- (ii) its head_q-restriction is not state-correct for head_q.
    applySeq AWSet AWSet.init wRestrQ ≠ head_q ∧
    awLive (applySeq AWSet AWSet.init wRestrQ) ≠ awLive head_q := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- fold w is all-dead
    rw [w_fold]
    simp only [awLive]
    ext x
    simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_empty_iff_false]
    grind
  · -- fold w = merged state
    rw [w_fold, mergedState_eq]
  · -- restriction ≠ head_q (second components differ: {1,2} ≠ {2})
    rw [wRestrQ_fold, head_q_eq]
    intro h
    rw [Prod.mk.injEq] at h
    have h1 : (1 : Timestamp) ∈ ({1, 2} : Set Timestamp) := by simp
    rw [h.2] at h1
    simp at h1
  · -- live(restriction) = ∅ ≠ {1} = live(head_q)
    rw [wRestrQ_fold, head_q_live]
    intro h
    have h1 : (1 : Timestamp) ∈ ({1} : Set Timestamp) := by simp
    rw [← h] at h1
    simp only [awLive, Set.mem_diff, Set.mem_insert_iff,
      Set.mem_singleton_iff] at h1
    grind

end Sal.Emulation
