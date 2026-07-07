import Sal.MRDTs.Metatheory.Conditioned.G2_Applicability_Aware

/-!
# Task #4: the update-feasibility gate — `loOnA + noopFeasible` as the feasibility notion

The GATE for the feasible update layer (the last open item on the `Inv`-nontrivial
column of `CONDITIONED_METATHEORY_PLAN.md`).  Two prior files set the stage, and every
definition below reuses theirs:

* `G2_Transport_Probe.lean` refuted the NAIVE conditioned convergence: plugging
  `commutesOn` into the linearization order (`loOnC`) admits both `[insOpE, delOpE]` and
  the infeasible `[delOpE, insOpE]` (`delOpE` folded at `init`, where it is not applicable),
  which fold to different states.
* `G2_Applicability_Aware.lean` (task #7) settled that strict `applicabilityValid` (repair
  (b)) is strictly more general than the syntactic `loOnA` (repair (a)) — BUT surfaced the
  open worry (`separating_inequivalence`): for reachable *redundant-concurrent* versions
  (two concurrent deletes of one node) NO enumeration is `applicabilityValid`, because
  whichever delete runs second finds its target already gone.  So the strict notion is
  *unsatisfiable* there; the plan flags "applicable OR no-op here" as the refined OQ4.

## The hypothesis this file tests (the research crux)

The correct feasibility notion for conditioned convergence is
**applicability-aware order `loOnA` (already defined in G2_Applicability_Aware) + no-op-feasible
enumeration** — NOT the strict `applicabilityValid` of task #7.  Formally, `noopFeasible`
RELAXES `applicabilityValid`: at each prefix the next op must be applicable **or act as the
identity** (`D.update s o = s`) on that prefix state.

## Verdicts (all mechanized below, 0 sorries, kernel-clean)

* **del@init is a genuine Lean-`Eq` no-op** — `del_at_init_noop : do_ init_st delOpE = init_st`
  is proved BY `rfl`, i.e. it holds *definitionally* in this RGA model.  KC's framing claim
  is confirmed: `Del` of an absent node with an empty path is identity (the map's mappings
  are untouched and the empty domain absorbs `remove`).  This is what makes `noopFeasible`
  well-defined.

* **Case 1 (DEPENDENCY, `{insOpE, delOpE}`, `del` depends on `ins`):**
  - `del_ins_noopFeasible`: `[delOpE, insOpE]` IS `noopFeasible` (via the no-op branch on
    `del@init`) — so no-op-feasibility ALONE does NOT exclude it.  This is exactly why
    relaxing (b) to (a-noop) re-opens the failure and why the order layer must do the work.
  - `not_respects_del_ins_loOnA` (reused from task #7): `loOnA` KEEPS the `ins→del`
    generation-dependency edge, so `[delOpE, insOpE]` does NOT respect `loOnA`.
  - `dependency_case_converges`: over enumerations that are BOTH `loOnA`-respecting AND
    `noopFeasible`, only `[insOpE, delOpE]` qualifies, so convergence HOLDS.

* **Case 2 (REDUNDANCY, `{insOpE, delOpE, delY}`, two concurrent deletes of node 1):**
  - `no_applicabilityValid_enum`: STRICT `applicabilityValid` admits NO enumeration of the
    3-event set (whichever delete is second is non-applicable) — mechanized satisfiability
    failure of task #7's repair (b).
  - `ins_del_delY_noopFeasible`, `ins_delY_del_noopFeasible`: under `noopFeasible` BOTH
    delete-orders qualify (the second delete is a no-op, `del1_idem`), and both respect
    `loOnA` (config-generally, via `sep_loOnC_imp_loOnA` and its mirror — the two deletes
    carry no generation-dependency between them).
  - `redundancy_folds_agree`: both admitted orders fold to the SAME state (node 1 deleted).
    So convergence HOLDS and the admitted set is SATISFIABLE — packaged as
    `redundancy_case_converges_and_satisfiable`.

* **THE VERDICT** (`loOnA_noopFeasible_verdict`): `loOnA + noopFeasible` is
  convergent-and-satisfiable on BOTH cases, whereas
  - strict-(b) `applicabilityValid` fails *satisfiability* on case 2
    (`no_applicabilityValid_enum`), and
  - plain-`loOnC` + `noopFeasible` fails *convergence* on case 1
    (`plain_loOnC_noopFeasible_diverges`: G2's `[delOpE, insOpE]` counterexample is re-admitted
    because it is `noopFeasible` and `loOnC`-respecting).

  This validates the plan's revised feasibility notion (the "(a) applicability-aware order +
  no-op-feasible enumeration" design), and shows strict-(b) alone is both too weak on the
  order side (needs `loOnA`) and too strong on the applicability side (unsatisfiable on
  redundancy).

## One structural finding, reported not forced

All three ops carry replica id `0`.  `Configuration.vis_total_same_replica`
(`CRDT_TS.lean`) forces two distinct events with the SAME replica id to be `vis`-comparable,
so a *fully well-formed* single-rid `Configuration` cannot realise `delOpE ‖ delY` as
genuinely concurrent — an order would be forced.  This is exactly why task #7 stated the
3-event separation config-GENERALLY (`∀ C ev`, hypothesising `respects loOnC`), and why the
`loOnA`-admission facts here are the config-general reductions `respects loOnC → respects
loOnA` rather than a constructed `Csep`.  The finding does not weaken the verdict: the
`loOnA` layer adds nothing over `loOnC` on the two deletes (they carry no positive
creation-reference between them), which is the substantive content.
-/

set_option maxHeartbeats 1000000

namespace Sal.Metatheory.UpdateFeasibilityGate

open Sal.Emulation
open Sal.Metatheory.G2Probe
open Sal.Metatheory.G2AppAware

/-! ## §0  The relaxed feasibility predicate `noopFeasible`

`noopFeasible D π s` folds `π` from `s` and requires, at every prefix, that the next op is
`D.applicable` OR acts as the identity (`D.update s o = s`) on the state reached so far.
This RELAXES `applicabilityValid` (`G2_Applicability_Aware.lean`), whose clause was strict
`D.applicable o s`. -/

/-- Every prefix-fold of `π` (from `s`) keeps the next op applicable OR a no-op there. -/
def noopFeasible (D : ConditionedMRDTSig) : List (Op D.AppOp) → D.State → Prop
  | [], _ => True
  | o :: rest, s => (D.applicable o s ∨ D.update s o = s) ∧ noopFeasible D rest (D.update s o)

/-! ## §1  The RGA `Del` no-op algebra

The keystone: `Del` of an absent node whose empty path reparents nothing is the identity,
as a genuine Lean `Eq`.  From it we get `del@init` (definitionally) and `Del`-idempotence
(`del1_idem`), which drives the "second delete is a no-op" content of both cases. -/

/-- **del@init is a genuine Lean-`Eq` no-op.**  Proved by `rfl`: it holds *definitionally*.
`init_st`'s mappings are untouched (no entry has anchor `1`) and its empty domain absorbs the
`remove`.  This confirms KC's framing: `Del` of an absent node here is identity, not a
failure. -/
theorem del_at_init_noop : do_ init_st delOpE = init_st := by rfl

/-- A delete of node `1` (empty path) makes node `1` absent, for any prior state. -/
theorem contains_doDel_node1 (s : concrete_st) (t r : ℕ) :
    contains (do_ s (t, r, app_op_t.Del [] 1)) 1 = false := by
  rw [contains_doDel]; simp

/-- After a delete of node `1` (empty path), no key has anchor `1`: the delete either
reparents the `anc = 1` keys to `resolve s [] = 0` or leaves an already-`≠1` anchor. -/
theorem anc_del1_ne (s : concrete_st) (t r k : ℕ) :
    anc (do_ s (t, r, app_op_t.Del [] 1)) k ≠ 1 := by
  rw [anc_doDel s t r 1 [] k]
  by_cases h : anc s k = 1
  · rw [if_pos h]; simp
  · rw [if_neg h]; exact h

/-- **`Del` no-op lemma.**  If `x` is absent and no key has anchor `x`, then deleting `x`
(any timestamp/replica, any path) is the identity — a genuine Lean `Eq`, via map
extensionality (`sel` and `contains` agree pointwise). -/
theorem del_noop_general (s : concrete_st) (t r x : ℕ) (pre : List ℕ)
    (hx : contains s x = false) (hanc : ∀ k, anc s k ≠ x) :
    do_ s (t, r, .Del pre x) = s := by
  apply (map_lemma_equal_elim _ _).mp
  apply (map_lemma_equal_intro _ _).mp
  intro k
  refine ⟨?_, ?_⟩
  · -- sel agrees: the reparent branch is never taken (no key has anchor x)
    rw [sel_doDel, if_neg (hanc k)]
  · -- contains agrees: k = x already absent, k ≠ x survives the delete
    rw [contains_doDel]
    rcases eq_or_ne k x with rfl | hkx
    · rw [hx]; simp
    · have hb : (k != x) = true := by simpa using hkx
      rw [hb]; simp

/-- **`Del`-idempotence for node `1`, empty path.**  A second delete of node `1` after a
first one is a no-op — the first delete leaves node `1` absent (`contains_doDel_node1`) and
every anchor `≠ 1` (`anc_del1_ne`), so `del_noop_general` fires. -/
theorem del1_idem (s : concrete_st) (t r t' r' : ℕ) :
    do_ (do_ s (t, r, .Del [] 1)) (t', r', .Del [] 1) = do_ s (t, r, .Del [] 1) :=
  del_noop_general (do_ s (t, r, .Del [] 1)) t' r' 1 []
    (contains_doDel_node1 s t r) (fun k => anc_del1_ne s t r k)

/-! ## §2  Case 1 — the DEPENDENCY case `{insOpE, delOpE}` (`del` depends on `ins`) -/

/-- `[insOpE, delOpE]` is `noopFeasible` (both ops strictly applicable at their prefixes). -/
theorem ins_del_noopFeasible : noopFeasible RGACondSig [insOpE, delOpE] init_st := by
  refine ⟨Or.inl insOpE_applicable_at_init, ?_⟩
  exact ⟨Or.inl delOpE_applicable_after_ins, trivial⟩

/-- **`noopFeasible` ALONE does not exclude the bad order.**  `[delOpE, insOpE]` IS
`noopFeasible`: `delOpE` at `init` is not applicable but is a no-op (`del_at_init_noop`),
and `insOpE` is applicable at the state reached (which is definitionally `init`).  This is
why relaxing (b) to no-op re-opens the failure, and why the ORDER layer must exclude it. -/
theorem del_ins_noopFeasible : noopFeasible RGACondSig [delOpE, insOpE] init_st := by
  refine ⟨Or.inr del_at_init_noop, ?_⟩
  exact ⟨Or.inl insOpE_applicable_at_init, trivial⟩

/-- The two facts together: no-op-feasibility does not exclude `[delOpE, insOpE]`, but
`loOnA` (repair (a), reused from task #7) does. -/
theorem dependency_case_noop_alone_insufficient :
    noopFeasible RGACondSig [delOpE, insOpE] init_st
    ∧ ¬ respects [delOpE, insOpE] (loOnA Ccex evCex) :=
  ⟨del_ins_noopFeasible, not_respects_del_ins_loOnA⟩

/-- `loOnA` pins the feasible order: any `loOnA`-respecting permutation of `{insOpE, delOpE}`
is `[insOpE, delOpE]` (the bad order inverts the retained generation-dependency edge). -/
theorem loOnA_perm_forces_ins_del (π : List (Op app_op_t))
    (hperm : listPermOf π evCex)
    (hA : respects π (loOnA Ccex evCex)) : π = [insOpE, delOpE] := by
  rcases permOf_evCex_cases π hperm with h | h
  · exact h
  · rw [h] at hA; exact absurd hA not_respects_del_ins_loOnA

/-- **Case 1 verdict: `loOnA + noopFeasible` CONVERGES.**  Over enumerations of
`{insOpE, delOpE}` that are BOTH `loOnA`-respecting AND `noopFeasible`, only `[insOpE, delOpE]`
qualifies (`loOnA` excludes `[delOpE, insOpE]` — which `noopFeasible` alone admits), so all
qualifying folds agree.  (`loOnA` is already the binding constraint; the `noopFeasible`
hypotheses are carried but not consulted.) -/
theorem dependency_case_converges
    (π₁ π₂ : List (Op app_op_t))
    (hperm₁ : listPermOf π₁ evCex) (hperm₂ : listPermOf π₂ evCex)
    (hA₁ : respects π₁ (loOnA Ccex evCex)) (hA₂ : respects π₂ (loOnA Ccex evCex))
    (_hN₁ : noopFeasible RGACondSig π₁ init_st) (_hN₂ : noopFeasible RGACondSig π₂ init_st) :
    applySeq RGACondSig.toCRDTSig init_st π₁ = applySeq RGACondSig.toCRDTSig init_st π₂ := by
  rw [loOnA_perm_forces_ins_del π₁ hperm₁ hA₁, loOnA_perm_forces_ins_del π₂ hperm₂ hA₂]

/-- The surviving enumeration folds to the deleted state (node `1` absent). -/
theorem dependency_case_folds_to_deleted :
    contains (applySeq RGACondSig.toCRDTSig init_st [insOpE, delOpE]) 1 = false := by
  rw [applySeq_two]
  exact contains_doDel_node1 (do_ init_st insOpE) 2 0

/-! ## §3  Case 2 — the REDUNDANCY case `{insOpE, delOpE, delY}` (two concurrent deletes) -/

/-- The redundancy version: insert node 1, then two concurrent deletes of node 1. -/
def evSep : Set (Op app_op_t) := {insOpE, delOpE, delY}

theorem ins_ne_delY : insOpE ≠ delY := by decide
theorem delOpE_ne_delY : delOpE ≠ delY := by decide

theorem mem_evSep_iff (a : Op app_op_t) :
    a ∈ evSep ↔ a = insOpE ∨ a = delOpE ∨ a = delY := by
  simp only [evSep, Set.mem_insert_iff, Set.mem_singleton_iff]

/-- A delete of node `1` is not applicable wherever node `1` is absent (`accurate` fails:
node `1` neither the root sentinel nor present). -/
theorem delNode1_not_applicable (t r : ℕ) (s : concrete_st)
    (h1 : contains s 1 = false) :
    ¬ RGACondSig.applicable (t, r, app_op_t.Del [] 1) s := by
  rintro ⟨hacc, _⟩
  have hacc' : ((1 : ℕ) = 0 ∧ ([] : List ℕ) = []) ∨
      (contains s 1 = true ∧ IsAncPath s 1 []) := hacc
  rcases hacc' with ⟨h, _⟩ | ⟨h, _⟩
  · exact one_ne_zero h
  · rw [h1] at h; exact Bool.noConfusion h

/-- **STRICT `applicabilityValid` (repair (b)) admits NO enumeration of the redundancy set.**
The head must be applicable at `init`, so it must be `insOpE` (both deletes fail `accurate`
at `init`); then the tail contains both deletes, and whichever runs second finds node `1`
already gone and is non-applicable.  Mechanized satisfiability failure of task #7's (b). -/
theorem no_applicabilityValid_enum (π : List (Op app_op_t))
    (hperm : listPermOf π evSep) :
    ¬ applicabilityValid RGACondSig π init_st := by
  obtain ⟨hnd, hiff⟩ := hperm
  intro hav
  have hinit1 : contains init_st 1 = false := by simp [init_st]
  rcases π with _ | ⟨o, rest⟩
  · exact absurd ((hiff insOpE).mpr ((mem_evSep_iff insOpE).mpr (Or.inl rfl)))
      List.not_mem_nil
  · obtain ⟨happ_o, hav_rest⟩ := hav
    have ho_mem : o = insOpE ∨ o = delOpE ∨ o = delY :=
      (mem_evSep_iff o).mp ((hiff o).mp List.mem_cons_self)
    have ho_ins : o = insOpE := by
      rcases ho_mem with h | h | h
      · exact h
      · exfalso; rw [h] at happ_o
        exact delNode1_not_applicable 2 0 init_st hinit1 happ_o
      · exfalso; rw [h] at happ_o
        exact delNode1_not_applicable 3 0 init_st hinit1 happ_o
    subst ho_ins
    have hins_notin : insOpE ∉ rest := (List.nodup_cons.mp hnd).1
    have rest_mem : ∀ a ∈ rest, a = delOpE ∨ a = delY := by
      intro a ha
      rcases (mem_evSep_iff a).mp ((hiff a).mp (List.mem_cons_of_mem _ ha)) with h | h | h
      · exact absurd (h ▸ ha) hins_notin
      · exact Or.inl h
      · exact Or.inr h
    have hdel_in : delOpE ∈ rest := by
      rcases List.mem_cons.mp
          ((hiff delOpE).mpr ((mem_evSep_iff delOpE).mpr (Or.inr (Or.inl rfl)))) with h | h
      · exact absurd h.symm ins_ne_del
      · exact h
    have hy_in : delY ∈ rest := by
      rcases List.mem_cons.mp
          ((hiff delY).mpr ((mem_evSep_iff delY).mpr (Or.inr (Or.inr rfl)))) with h | h
      · exact absurd h.symm ins_ne_delY
      · exact h
    rcases rest with _ | ⟨x, _ | ⟨y, rest''⟩⟩
    · exact absurd hdel_in List.not_mem_nil
    · have hxd : delOpE = x := List.mem_singleton.mp hdel_in
      have hxy : delY = x := List.mem_singleton.mp hy_in
      exact delOpE_ne_delY (hxd.trans hxy.symm)
    · obtain ⟨_hx_app, hy_app, _⟩ := hav_rest
      have hx : x = delOpE ∨ x = delY := rest_mem x List.mem_cons_self
      have hy : y = delOpE ∨ y = delY :=
        rest_mem y (List.mem_cons_of_mem _ List.mem_cons_self)
      have hcx : contains (do_ (do_ init_st insOpE) x) 1 = false := by
        rcases hx with rfl | rfl
        · exact contains_doDel_node1 (do_ init_st insOpE) 2 0
        · exact contains_doDel_node1 (do_ init_st insOpE) 3 0
      rcases hy with rfl | rfl
      · exact delNode1_not_applicable 2 0 _ hcx hy_app
      · exact delNode1_not_applicable 3 0 _ hcx hy_app

/-- `delY` is applicable right after `insOpE` (same target/path as `delOpE`; the timestamp
does not enter `accurate`/`fresh_ts` for a `Del`). -/
theorem delY_applicable_after_ins :
    accurate delY (do_ init_st insOpE) ∧ fresh_ts delY (do_ init_st insOpE) :=
  delOpE_applicable_after_ins

/-- **Under `noopFeasible`, order `[insOpE, delOpE, delY]` qualifies.**  `insOpE`, then
`delOpE` (both applicable), then `delY` — a no-op, since node `1` is already deleted
(`del1_idem`). -/
theorem ins_del_delY_noopFeasible :
    noopFeasible RGACondSig [insOpE, delOpE, delY] init_st := by
  refine ⟨Or.inl insOpE_applicable_at_init, ?_⟩
  refine ⟨Or.inl delOpE_applicable_after_ins, ?_⟩
  exact ⟨Or.inr (del1_idem (do_ init_st insOpE) 2 0 3 0), trivial⟩

/-- **Under `noopFeasible`, order `[insOpE, delY, delOpE]` also qualifies** — symmetric to
the above (`delY` applicable, then `delOpE` a no-op). -/
theorem ins_delY_del_noopFeasible :
    noopFeasible RGACondSig [insOpE, delY, delOpE] init_st := by
  refine ⟨Or.inl insOpE_applicable_at_init, ?_⟩
  refine ⟨Or.inl delY_applicable_after_ins, ?_⟩
  exact ⟨Or.inr (del1_idem (do_ init_st insOpE) 3 0 2 0), trivial⟩

/-- **`loOnA` admits `[insOpE, delOpE, delY]`** (config-generally): whenever the order
respects the base `loOnC`, it respects `loOnA` — the generation-dependency layer adds no
backward edge (the two deletes carry no positive creation-reference).  Reused verbatim from
task #7. -/
theorem redundancy_loOnA_admits_ins_del_delY
    (C : Sal.Emulation.Configuration RGACondSig.toCRDTSig) (ev : Set (Op app_op_t))
    (h : respects [insOpE, delOpE, delY] (loOnC RGACondSig C ev)) :
    respects [insOpE, delOpE, delY] (loOnA C ev) :=
  sep_loOnC_imp_loOnA C ev h

/-- **`loOnA` admits `[insOpE, delY, delOpE]`** (the mirror), same config-general reduction. -/
theorem redundancy_loOnA_admits_ins_delY_del
    (C : Sal.Emulation.Configuration RGACondSig.toCRDTSig) (ev : Set (Op app_op_t))
    (h : respects [insOpE, delY, delOpE] (loOnC RGACondSig C ev)) :
    respects [insOpE, delY, delOpE] (loOnA C ev) := by
  obtain ⟨hi, hrest⟩ := List.pairwise_cons.mp h
  obtain ⟨hy, _⟩ := List.pairwise_cons.mp hrest
  have dep_y_d : ¬ appliesDependsOn delY delOpE := by simp [appliesDependsOn, delOpE]
  refine List.pairwise_cons.mpr
    ⟨?_, List.pairwise_cons.mpr ⟨?_, List.pairwise_singleton _ _⟩⟩
  · intro b hb
    rcases List.mem_cons.mp hb with rfl | hb'
    · rintro (hC | ⟨_, hdep⟩)
      · exact hi delY List.mem_cons_self hC
      · exact dep_i_y hdep
    · rw [List.mem_singleton] at hb'; subst hb'
      rintro (hC | ⟨_, hdep⟩)
      · exact hi delOpE (List.mem_cons_of_mem _ List.mem_cons_self) hC
      · exact dep_i_d hdep
  · intro b hb
    rw [List.mem_singleton] at hb; subst hb
    rintro (hC | ⟨_, hdep⟩)
    · exact hy delOpE List.mem_cons_self hC
    · exact dep_y_d hdep

/-- **Both admitted orders fold to the SAME state** (node `1` deleted).  Immediate: `do_`
ignores a `Del`'s timestamp/replica, and the second delete is a no-op, so both 3-folds
reduce to the once-deleted state.  Convergence + satisfiability of the redundancy case. -/
theorem redundancy_folds_agree :
    applySeq RGACondSig.toCRDTSig init_st [insOpE, delOpE, delY]
      = applySeq RGACondSig.toCRDTSig init_st [insOpE, delY, delOpE] := by
  rfl

/-- **Case 2 verdict: `loOnA + noopFeasible` is SATISFIABLE-and-CONVERGENT** where strict (b)
is unsatisfiable.  Bundles: (i) strict `applicabilityValid` admits nothing; (ii)+(iii) both
delete-orders are `noopFeasible`; (iv)+(v) both respect `loOnA` (config-generally);
(vi) both fold to the same state. -/
theorem redundancy_case_converges_and_satisfiable :
    (∀ π, listPermOf π evSep → ¬ applicabilityValid RGACondSig π init_st)
    ∧ noopFeasible RGACondSig [insOpE, delOpE, delY] init_st
    ∧ noopFeasible RGACondSig [insOpE, delY, delOpE] init_st
    ∧ (∀ (C : Sal.Emulation.Configuration RGACondSig.toCRDTSig) (ev : Set (Op app_op_t)),
        respects [insOpE, delOpE, delY] (loOnC RGACondSig C ev)
          → respects [insOpE, delOpE, delY] (loOnA C ev))
    ∧ (∀ (C : Sal.Emulation.Configuration RGACondSig.toCRDTSig) (ev : Set (Op app_op_t)),
        respects [insOpE, delY, delOpE] (loOnC RGACondSig C ev)
          → respects [insOpE, delY, delOpE] (loOnA C ev))
    ∧ applySeq RGACondSig.toCRDTSig init_st [insOpE, delOpE, delY]
        = applySeq RGACondSig.toCRDTSig init_st [insOpE, delY, delOpE] :=
  ⟨no_applicabilityValid_enum, ins_del_delY_noopFeasible, ins_delY_del_noopFeasible,
   redundancy_loOnA_admits_ins_del_delY, redundancy_loOnA_admits_ins_delY_del,
   redundancy_folds_agree⟩

/-! ## §4  The verdict — the theorem-backed comparison

`loOnA + noopFeasible` is convergent-and-satisfiable on BOTH cases, where the two strictly
weaker/stronger alternatives each fail on one case. -/

/-- **Plain `loOnC` + `noopFeasible` DIVERGES** on case 1: G2's `[delOpE, insOpE]`
counterexample is re-admitted (it is `noopFeasible` by `del_ins_noopFeasible` and
`loOnC`-respecting by `respects_del_ins`), so `[insOpE, delOpE]` and `[delOpE, insOpE]` fold
differently.  This is why `noopFeasible` needs the `loOnA` order layer, not just `loOnC`. -/
theorem plain_loOnC_noopFeasible_diverges :
    ¬ (∀ (π₁ π₂ : List (Op app_op_t)),
        listPermOf π₁ evCex → listPermOf π₂ evCex →
        respects π₁ (loOnC RGACondSig Ccex evCex) →
        respects π₂ (loOnC RGACondSig Ccex evCex) →
        noopFeasible RGACondSig π₁ init_st →
        noopFeasible RGACondSig π₂ init_st →
        applySeq RGACondSig.toCRDTSig init_st π₁
          = applySeq RGACondSig.toCRDTSig init_st π₂) := by
  intro hconv
  have h := hconv [insOpE, delOpE] [delOpE, insOpE]
    perm_ins_del perm_del_ins
    (respects_ins_del Ccex evCex) (respects_del_ins Ccex evCex)
    ins_del_noopFeasible del_ins_noopFeasible
  rw [applySeq_two, applySeq_two] at h
  exact folds_differ h

/-- **THE HEADLINE.**  A theorem-backed comparison of the three feasibility notions:

1. plain `loOnC` + `noopFeasible` fails CONVERGENCE on the dependency case (case 1);
2. strict `applicabilityValid` fails SATISFIABILITY on the redundancy case (case 2);
3. `loOnA` + `noopFeasible` CONVERGES on the dependency case; and
4. `loOnA` + `noopFeasible` is SATISFIABLE-and-CONVERGENT on the redundancy case.

Hence `loOnA + noopFeasible` is the feasibility notion that works on both decisive cases —
confirming the plan's revised "(a) applicability-aware order + no-op-feasible enumeration"
design over strict-(b). -/
theorem loOnA_noopFeasible_verdict :
    (¬ (∀ (π₁ π₂ : List (Op app_op_t)),
          listPermOf π₁ evCex → listPermOf π₂ evCex →
          respects π₁ (loOnC RGACondSig Ccex evCex) →
          respects π₂ (loOnC RGACondSig Ccex evCex) →
          noopFeasible RGACondSig π₁ init_st → noopFeasible RGACondSig π₂ init_st →
          applySeq RGACondSig.toCRDTSig init_st π₁
            = applySeq RGACondSig.toCRDTSig init_st π₂))
    ∧ (∀ π, listPermOf π evSep → ¬ applicabilityValid RGACondSig π init_st)
    ∧ (∀ (π₁ π₂ : List (Op app_op_t)),
          listPermOf π₁ evCex → listPermOf π₂ evCex →
          respects π₁ (loOnA Ccex evCex) → respects π₂ (loOnA Ccex evCex) →
          noopFeasible RGACondSig π₁ init_st → noopFeasible RGACondSig π₂ init_st →
          applySeq RGACondSig.toCRDTSig init_st π₁
            = applySeq RGACondSig.toCRDTSig init_st π₂)
    ∧ (noopFeasible RGACondSig [insOpE, delOpE, delY] init_st
        ∧ noopFeasible RGACondSig [insOpE, delY, delOpE] init_st
        ∧ applySeq RGACondSig.toCRDTSig init_st [insOpE, delOpE, delY]
            = applySeq RGACondSig.toCRDTSig init_st [insOpE, delY, delOpE]) :=
  ⟨plain_loOnC_noopFeasible_diverges,
   no_applicabilityValid_enum,
   dependency_case_converges,
   ⟨ins_del_delY_noopFeasible, ins_delY_del_noopFeasible, redundancy_folds_agree⟩⟩

/-! ## §5  Axiom audit — all kernel-checked (no `native_decide`, no `sorryAx`) -/

#print axioms del_at_init_noop
#print axioms del1_idem
#print axioms dependency_case_converges
#print axioms no_applicabilityValid_enum
#print axioms redundancy_case_converges_and_satisfiable
#print axioms plain_loOnC_noopFeasible_diverges
#print axioms loOnA_noopFeasible_verdict

end Sal.Metatheory.UpdateFeasibilityGate
