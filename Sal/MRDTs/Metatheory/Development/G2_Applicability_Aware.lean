import Sal.MRDTs.Metatheory.Development.G2_Transport_Probe

/-!
# Gate G2 (OQ4), fork: applicability-aware `lo` vs applicability-restricted convergence

Task #7 of `CONDITIONED_METATHEORY_PLAN.md` (the "Gate G2 … verdict in" continuation).

`G2_Transport_Probe.lean` refuted the NAIVE conditioned convergence: swapping
`CRDTSig.commutes ↦ ConditionedMRDTSig.commutesOn` inside the linearization order, keeping
all other convergence hypotheses, is falsified by the 2-event RGA execution `insOpE`
(insert node 1) then `delOpE` (delete node 1).  The two ops are never jointly applicable
(`fresh_ts insOpE` wants node 1 absent, `accurate delOpE` wants it present), so
`commutesOn` is VACUOUSLY true, the conditioned `lo` drops the `ins → del` edge, and the
bad order `[delOpE, insOpE]` — which folds `delOpE` at `init`, where it is NOT applicable —
respects the order yet folds differently.

The refutation quantifies over *all* `loOnC`-respecting enumerations, including
applicability-invalid folds.  Two candidate repairs restore convergence on the feasible
update layer; this file formalizes BOTH on the SAME 2-event instance and then settles the
research question of whether they are the same exclusion.

* **(a) applicability-aware `lo` (`loOnA`)** — a vis-edge `e₁ → e₂` survives whenever `e₂`'s
  applicability *depends on* `e₁` (generation dependency; for the RGA, op-syntactic:
  `e₂` names `e₁`'s Ins-timestamp as its Del-target / Ins-anchor / path member), not only
  when `¬ commutesOn`.  Captured by `appliesDependsOn` + `loOnA`.
* **(b) applicability-restricted convergence (`applicabilityValid`)** — quantify convergence
  only over enumerations whose every prefix keeps the next op applicable from `init`.
  `[delOpE, insOpE]` is then excluded because `delOpE` is not applicable at `init`.

## Verdicts (all mechanized below, 0 sorries, kernel-clean)

* **(b) positive check** — `applicabilityValid_ins_del`, `not_applicabilityValid_del_ins`,
  and `b_convergence_holds`: on the counterexample instance, restricting to
  `applicabilityValid` enumerations leaves ONLY `[insOpE, delOpE]`, so the repaired
  convergence statement HOLDS (is not refuted).  Notably `applicabilityValid` alone pins
  the order down — the `loOnC`-respects hypotheses are not even consulted.
* **(a) positive check** — `loOnA_keeps_edge`, `respects_ins_del_loOnA`,
  `not_respects_del_ins_loOnA`: `loOnA` keeps the `ins → del` edge via the
  generation-dependency disjunct, so the bad order `[delOpE, insOpE]` does not respect
  `loOnA` and is excluded.
* **Instance equivalence** — `instance_equivalence`: over the permutations of
  `{insOpE, delOpE}`, "respects `loOnA`" coincides EXACTLY with
  "`applicabilityValid` ∧ respects `loOnC`".  Both admit exactly `[insOpE, delOpE]`.
* **General verdict: (b) is STRICTLY more general than (a)** — `separating_inequivalence`.
  The 3-event set `{insOpE, delOpE, delY}` (insert node 1, then two concurrent deletes of
  node 1) has an enumeration `[insOpE, delOpE, delY]` that is applicability-invalid (`delY`
  deletes the already-absent node 1) but inverts NO generation-dependency edge — because
  the only Ins (the sole creator) already comes first, and `appliesDependsOn` is blind
  between the two Del's.  So `loOnC`-respecting `⟹` `loOnA`-respecting on this order
  (`sep_loOnC_imp_loOnA`), i.e. (a)'s added edges exclude nothing here, while (b)'s
  `applicabilityValid` correctly rejects it (`not_applicabilityValid_sep`).  The
  applicability failure is a NEGATIVE / anti-dependency ("`delX` must not precede") that a
  positive creation-reference relation cannot express.

## Recommendation (grounded in what is proved below)

Adopt **(b)** as the DEFINITION of feasibility for the update layer's convergence theorem,
and treat **(a)** as a decidable, per-MRDT *sufficient* condition that can be used to
discharge the `applicabilityValid` side-condition wherever the dependencies are purely
positive create-before-use.  Justification:

* On the counterexample instance the two coincide (`instance_equivalence`), so (a) is a
  faithful repair there and (b) loses nothing.
* But (a) is INCOMPLETE: `separating_inequivalence` exhibits an applicability-invalid
  enumeration that (a) fails to exclude — the generation-dependency edge set (the only
  thing `loOnA` adds over `loOnC`) cannot see use-before-delete / anti-dependencies, nor
  combination dependencies.  A convergence theorem quantified by (a) would therefore still
  admit infeasible folds; only (b) captures *all* feasibility.
* The cost of (b) is that `applicabilityValid` is a semantic side-condition the theorem's
  consumers must carry.  (a) is the practical discharge tool: where a data type's
  applicability is a conjunction of positive creation references (RGA's Ins/Del-target,
  Ins-anchor, path membership), `loOnA` makes exactly those edges syntactic and the
  `applicabilityValid` obligation reduces to "respects `loOnA`" (the provable inclusion
  `b ⊆ a`, whose instance is `instance_equivalence`).

**Surfaced research subtlety (open):** for the concurrent-delete version `{insOpE, delOpE,
delY}`, NO enumeration is `applicabilityValid` (whichever delete runs first makes the other
non-applicable), yet the merged state is well-defined.  So (b)'s "strict applicability at
every prefix" can be *unsatisfiable* for genuinely reachable versions with redundant
concurrent ops — the update layer needs an applicability notion that tolerates
idempotent/absorbed re-application (e.g. "applicable OR a no-op here").  See
`G2_FORK_FINDINGS.md`.
-/

set_option maxHeartbeats 1000000

namespace Sal.Metatheory.G2AppAware

open Sal.Emulation
open Sal.Metatheory.G2Probe

/-! ## §1  Repair (b): applicability-restricted convergence

`applicabilityValid D π s` says every prefix-fold of `π` from `s` keeps the next op
`D.applicable` at the state reached so far.  This is the semantic feasibility predicate
that repair (b) uses to restrict the enumerations quantified in convergence. -/

/-- Every prefix-fold of `π` (from `s`) keeps the next op applicable. -/
def applicabilityValid (D : ConditionedMRDTSig) : List (Op D.AppOp) → D.State → Prop
  | [], _ => True
  | o :: rest, s => D.applicable o s ∧ applicabilityValid D rest (D.update s o)

/-- `[insOpE, delOpE]` IS applicability-valid: `insOpE` is applicable at `init`, and
`delOpE` is applicable at the state after `insOpE`. -/
theorem applicabilityValid_ins_del :
    applicabilityValid RGACondSig [insOpE, delOpE] init_st := by
  refine ⟨insOpE_applicable_at_init, delOpE_applicable_after_ins, ?_⟩
  trivial

/-- `[delOpE, insOpE]` is NOT applicability-valid: `delOpE` is not applicable at `init`
(node 1 is absent, so the delete target is not present, so `accurate` fails). -/
theorem not_applicabilityValid_del_ins :
    ¬ applicabilityValid RGACondSig [delOpE, insOpE] init_st := by
  intro h
  have hacc : accurate delOpE init_st := h.1.1
  have hacc' : ((1 : ℕ) = 0 ∧ ([] : List ℕ) = []) ∨
      (contains init_st 1 = true ∧ IsAncPath init_st 1 []) := hacc
  have h0 : contains init_st 1 = false := by simp [init_st]
  rcases hacc' with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact one_ne_zero h1
  · rw [h0] at h1; exact Bool.noConfusion h1

/-! ### The only applicability-valid permutation of `{insOpE, delOpE}` is `[insOpE, delOpE]`

First enumerate the permutations of the 2-event set, then discard `[delOpE, insOpE]` by
applicability-invalidity. -/

/-- A permutation-list of `{insOpE, delOpE}` is one of the two orderings. -/
theorem permOf_evCex_cases (π : List (Op app_op_t)) (hπ : listPermOf π evCex) :
    π = [insOpE, delOpE] ∨ π = [delOpE, insOpE] := by
  obtain ⟨hnd, hiff⟩ := hπ
  rcases π with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · exact absurd ((hiff insOpE).mpr (Set.mem_insert _ _)) List.not_mem_nil
  · -- π = [a]
    have hi : insOpE = a :=
      List.mem_singleton.mp ((hiff insOpE).mpr (Set.mem_insert _ _))
    have hd : delOpE = a :=
      List.mem_singleton.mp ((hiff delOpE).mpr (Set.mem_insert_of_mem _ rfl))
    exact absurd (hi.trans hd.symm) ins_ne_del
  · -- π = [a, b]
    have ha : a = insOpE ∨ a = delOpE := (hiff a).mp List.mem_cons_self
    have hb : b = insOpE ∨ b = delOpE :=
      (hiff b).mp (List.mem_cons_of_mem _ List.mem_cons_self)
    have hab : a ≠ b := fun e => (List.nodup_cons.mp hnd).1 (List.mem_singleton.mpr e)
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd rfl hab
  · -- π = a :: b :: c :: t  — pigeonhole: three distinct elements in a 2-element set
    exfalso
    have ha : a = insOpE ∨ a = delOpE := (hiff a).mp List.mem_cons_self
    have hb : b = insOpE ∨ b = delOpE :=
      (hiff b).mp (List.mem_cons_of_mem _ List.mem_cons_self)
    have hc : c = insOpE ∨ c = delOpE :=
      (hiff c).mp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    obtain ⟨hna, hnd'⟩ := List.nodup_cons.mp hnd
    obtain ⟨hnb, _⟩ := List.nodup_cons.mp hnd'
    have hab : a ≠ b := fun e => hna (List.mem_cons.mpr (Or.inl e))
    have hac : a ≠ c := fun e => hna (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl e))))
    have hbc : b ≠ c := fun e => hnb (List.mem_cons.mpr (Or.inl e))
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
      first
        | exact hab rfl
        | exact hac rfl
        | exact hbc rfl

/-- Applicability-validity forces the unique feasible order on the instance. -/
theorem applicabilityValid_perm_forces_ins_del (π : List (Op app_op_t))
    (hperm : listPermOf π evCex)
    (hav : applicabilityValid RGACondSig π init_st) : π = [insOpE, delOpE] := by
  rcases permOf_evCex_cases π hperm with h | h
  · exact h
  · rw [h] at hav; exact absurd hav not_applicabilityValid_del_ins

/-- **Repair (b), decisive positive check.**  The repaired convergence statement — the
conditioned convergence RESTRICTED to `applicabilityValid`, `loOnC`-respecting enumerations
of `{insOpE, delOpE}` — HOLDS on the very execution that refuted the naive version.  Both
qualifying enumerations collapse to `[insOpE, delOpE]`, so the folds agree.  (The
`loOnC`-respects hypotheses are unused: on this instance `applicabilityValid` is already the
binding constraint.) -/
theorem b_convergence_holds
    (C : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (π₁ π₂ : List (Op app_op_t))
    (hperm₁ : listPermOf π₁ evCex) (hperm₂ : listPermOf π₂ evCex)
    (_hresp₁ : respects π₁ (loOnC RGACondSig C evCex))
    (_hresp₂ : respects π₂ (loOnC RGACondSig C evCex))
    (hav₁ : applicabilityValid RGACondSig π₁ init_st)
    (hav₂ : applicabilityValid RGACondSig π₂ init_st) :
    applySeq RGACondSig.toCRDTSig init_st π₁
      = applySeq RGACondSig.toCRDTSig init_st π₂ := by
  rw [applicabilityValid_perm_forces_ins_del π₁ hperm₁ hav₁,
      applicabilityValid_perm_forces_ins_del π₂ hperm₂ hav₂]

/-- Corollary: adding `applicabilityValid` genuinely breaks the refutation — the bad order
`[delOpE, insOpE]` no longer qualifies. -/
theorem b_repair_breaks_refutation :
    ¬ applicabilityValid RGACondSig [delOpE, insOpE] init_st :=
  not_applicabilityValid_del_ins

/-! ## §2  Repair (a): applicability-aware linearization order `loOnA`

`appliesDependsOn e₂ e₁`: "`e₂`'s applicability depends on `e₁`", i.e. `e₁` is an Ins that
creates a node (its own timestamp) that `e₂` names — as its Del-target / Ins-anchor
(`opLeaf`) or as a path member (`opPath`).  This is the RGA's op-syntactic, per-data-type
generation-dependency relation.  `loOnA` is `loOnC` plus the disjunct
"`vis e₁ e₂ ∧ appliesDependsOn e₂ e₁`". -/

/-- RGA generation dependency: `e₂` names the node created by the Ins `e₁`. -/
def appliesDependsOn : Op app_op_t → Op app_op_t → Prop
  | e₂, (t, _r, .Ins _ _ _) => opLeaf e₂.2.2 = t ∨ t ∈ opPath e₂.2.2
  | _e₂, (_t, _r, .Del _ _) => False

/-- The applicability-aware linearization order for the RGA: `loOnC` with an extra
generation-dependency disjunct on vis-edges. -/
def loOnA (C : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (ev : Set (Op app_op_t)) (e₁ e₂ : Op app_op_t) : Prop :=
  loOnC RGACondSig C ev e₁ e₂ ∨ (C.vis e₁ e₂ ∧ appliesDependsOn e₂ e₁)

/-- `delOpE` depends on `insOpE`: the delete target (node 1) is the node `insOpE` creates. -/
theorem appliesDependsOn_del_ins : appliesDependsOn delOpE insOpE := by
  simp [appliesDependsOn, insOpE, delOpE]

/-- **Repair (a), keeps the edge.**  `loOnA` retains the `insOpE → delOpE` vis-edge that
`loOnC` dropped — via the generation-dependency disjunct, not `commutesOn`. -/
theorem loOnA_keeps_edge : loOnA Ccex evCex insOpE delOpE :=
  Or.inr ⟨⟨rfl, rfl⟩, appliesDependsOn_del_ins⟩

/-- The good order respects `loOnA`: the only edge points forward. -/
theorem respects_ins_del_loOnA : respects [insOpE, delOpE] (loOnA Ccex evCex) := by
  show List.Pairwise (fun a b => ¬ loOnA Ccex evCex b a) [insOpE, delOpE]
  refine List.pairwise_cons.mpr ⟨?_, List.pairwise_singleton _ _⟩
  intro b hb
  rw [List.mem_singleton] at hb
  subst hb
  rintro (hC | ⟨hv, _⟩)
  · exact (no_loOnC_edge Ccex evCex).2 hC
  · exact ins_ne_del hv.1.symm

/-- **Repair (a), excludes the bad order.**  `[delOpE, insOpE]` does NOT respect `loOnA`,
because the retained `insOpE → delOpE` edge is inverted. -/
theorem not_respects_del_ins_loOnA :
    ¬ respects [delOpE, insOpE] (loOnA Ccex evCex) := by
  intro h
  have h1 := (List.pairwise_cons.mp h).1 insOpE List.mem_cons_self
  exact h1 loOnA_keeps_edge

/-! ## §3  The equivalence question, part 1: coincidence on the 2-event instance

Over the permutations of `{insOpE, delOpE}`, repair (a) ("respects `loOnA`") and repair (b)
("`applicabilityValid` ∧ respects `loOnC`") admit EXACTLY the same set — namely
`{[insOpE, delOpE]}`.  So on the counterexample instance the two repairs are the same
exclusion. -/

/-- **Instance equivalence.**  For every permutation `π` of `{insOpE, delOpE}`:
`respects π loOnA ↔ (applicabilityValid π ∧ respects π loOnC)`. -/
theorem instance_equivalence (π : List (Op app_op_t)) (hπ : listPermOf π evCex) :
    respects π (loOnA Ccex evCex)
    ↔ (applicabilityValid RGACondSig π init_st
        ∧ respects π (loOnC RGACondSig Ccex evCex)) := by
  rcases permOf_evCex_cases π hπ with rfl | rfl
  · -- π = [insOpE, delOpE]: both sides hold
    constructor
    · intro _; exact ⟨applicabilityValid_ins_del, respects_ins_del Ccex evCex⟩
    · intro _; exact respects_ins_del_loOnA
  · -- π = [delOpE, insOpE]: both sides fail
    constructor
    · intro h; exact absurd h not_respects_del_ins_loOnA
    · intro h; exact absurd h.1 not_applicabilityValid_del_ins

/-- On the instance the bad order is excluded by BOTH repairs (the same exclusion): it
inverts the generation-dependency edge (so `loOnA` rejects it) AND is applicability-invalid
(so `applicabilityValid` rejects it). -/
theorem instance_claimA :
    (¬ respects [delOpE, insOpE] (loOnA Ccex evCex))
    ∧ (¬ applicabilityValid RGACondSig [delOpE, insOpE] init_st) :=
  ⟨not_respects_del_ins_loOnA, not_applicabilityValid_del_ins⟩

/-! ## §4  The equivalence question, part 2: (b) is STRICTLY more general than (a)

The candidate general claim was:
> an enumeration is applicability-invalid IFF it inverts a generation-dependency edge.

The `⟸` direction ("edge inverted ⇒ invalid") holds structurally: inverting `e₁ → e₂` with
`appliesDependsOn e₂ e₁` puts a reference to node `t` (created only by the Ins `e₁`, by
timestamp uniqueness) before `e₁`, so at `e₂`'s prefix `t` is absent and `accurate e₂` fails.
This is the instance content of `instance_claimA` and it gives the inclusion
`(b)-admitted ⊆ (a)-admitted`.

The `⟹` direction FAILS.  Witness `delY` = a second delete of node 1, and the 3-event set
`{insOpE, delOpE, delY}` (single Ins, two concurrent Del's of the created node).  The order
`[insOpE, delOpE, delY]` is applicability-invalid (`delY` deletes the already-absent node 1)
but inverts NO generation-dependency edge: the sole creator `insOpE` is already first, and
`appliesDependsOn` is identically `False` between two Del's.  Hence `loOnA` cannot exclude
this order beyond what `loOnC` already does — but `applicabilityValid` does exclude it.
The applicability failure is an ANTI-dependency ("`delOpE` must not precede `delY`") that no
positive creation-reference edge can express: `(b)-admitted ⊊ (a)-admitted`, strictly. -/

/-- A second, concurrent delete of node 1 (distinct timestamp `3`). -/
def delY : Op app_op_t := (3, 0, .Del [] 1)

/-- `insOpE` does not depend on `delOpE` (`delOpE` is a Del: creates nothing). -/
theorem dep_i_d : ¬ appliesDependsOn insOpE delOpE := by
  simp [appliesDependsOn, delOpE]

/-- `insOpE` does not depend on `delY`. -/
theorem dep_i_y : ¬ appliesDependsOn insOpE delY := by
  simp [appliesDependsOn, delY]

/-- `delOpE` does not depend on `delY` — the two deletes have no generation dependency
between them, so `loOnA`'s added layer cannot order them. -/
theorem dep_d_y : ¬ appliesDependsOn delOpE delY := by
  simp [appliesDependsOn, delY]

/-- **The generation-dependency layer is BLIND to `[insOpE, delOpE, delY]`.**  No pair is
ordered "backward" by `appliesDependsOn` (the only Ins is first; the two Del's have no
dependency).  Config-independent: this is exactly the extra content `loOnA` carries over
`loOnC`, and it contributes nothing on this order. -/
theorem sep_no_backward_dep :
    List.Pairwise (fun a b => ¬ appliesDependsOn a b) [insOpE, delOpE, delY] := by
  refine List.pairwise_cons.mpr
    ⟨?_, List.pairwise_cons.mpr ⟨?_, List.pairwise_singleton _ _⟩⟩
  · intro b hb
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact dep_i_d
    · rw [List.mem_singleton] at hb'; subst hb'; exact dep_i_y
  · intro b hb
    rw [List.mem_singleton] at hb; subst hb; exact dep_d_y

/-- **The separating order is applicability-invalid.**  `[insOpE, delOpE, delY]` folds
`delY` at a state where node 1 has already been deleted by `delOpE`, so `accurate delY`
fails there. -/
theorem not_applicabilityValid_sep :
    ¬ applicabilityValid RGACondSig [insOpE, delOpE, delY] init_st := by
  intro h
  have happ : RGACondSig.applicable delY (do_ (do_ init_st insOpE) delOpE) := h.2.2.1
  have hacc : accurate delY (do_ (do_ init_st insOpE) delOpE) := happ.1
  have hL : contains (do_ (do_ init_st insOpE) delOpE) 1 = false := by
    show contains (do_ (do_ init_st insOpE) (2, 0, app_op_t.Del [] 1)) 1 = false
    rw [contains_doDel]; simp
  have hacc' : ((1 : ℕ) = 0 ∧ ([] : List ℕ) = []) ∨
      (contains (do_ (do_ init_st insOpE) delOpE) 1 = true
        ∧ IsAncPath (do_ (do_ init_st insOpE) delOpE) 1 []) := hacc
  rcases hacc' with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact one_ne_zero h1
  · rw [hL] at h1; exact Bool.noConfusion h1

/-- **On `[insOpE, delOpE, delY]`, `loOnA` excludes nothing that `loOnC` admits.**  Whenever
the order respects `loOnC` it also respects `loOnA` — the generation-dependency disjunct
never fires backward here (`dep_i_d`, `dep_i_y`, `dep_d_y`).  Config-general. -/
theorem sep_loOnC_imp_loOnA (C : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (ev : Set (Op app_op_t))
    (h : respects [insOpE, delOpE, delY] (loOnC RGACondSig C ev)) :
    respects [insOpE, delOpE, delY] (loOnA C ev) := by
  obtain ⟨hi, hrest⟩ := List.pairwise_cons.mp h
  obtain ⟨hd, _hy⟩ := List.pairwise_cons.mp hrest
  refine List.pairwise_cons.mpr
    ⟨?_, List.pairwise_cons.mpr ⟨?_, List.pairwise_singleton _ _⟩⟩
  · intro b hb
    rcases List.mem_cons.mp hb with rfl | hb'
    · rintro (hC | ⟨_, hdep⟩)
      · exact hi delOpE List.mem_cons_self hC
      · exact dep_i_d hdep
    · rw [List.mem_singleton] at hb'; subst hb'
      rintro (hC | ⟨_, hdep⟩)
      · exact hi delY (List.mem_cons_of_mem _ List.mem_cons_self) hC
      · exact dep_i_y hdep
  · intro b hb
    rw [List.mem_singleton] at hb; subst hb
    rintro (hC | ⟨_, hdep⟩)
    · exact hd delY List.mem_cons_self hC
    · exact dep_d_y hdep

/-- **The decisive separation: (a) and (b) are NOT the same exclusion.**

* `.1`: repair (b) EXCLUDES `[insOpE, delOpE, delY]` (`applicabilityValid` fails).
* `.2`: repair (a) does NOT — for every configuration, whenever the base order `loOnC`
  admits this enumeration, so does `loOnA`; the added generation-dependency edges exclude
  nothing here.

Hence `(b)-admitted ⊊ (a)-admitted`: **(b) is strictly more general than (a)**.  (a), the
VC-shaped syntactic route, cannot capture the anti-dependency feasibility constraint that
(b) enforces. -/
theorem separating_inequivalence :
    (¬ applicabilityValid RGACondSig [insOpE, delOpE, delY] init_st)
    ∧ (∀ (C : Sal.Emulation.Configuration RGACondSig.toCRDTSig) (ev : Set (Op app_op_t)),
        respects [insOpE, delOpE, delY] (loOnC RGACondSig C ev)
        → respects [insOpE, delOpE, delY] (loOnA C ev)) :=
  ⟨not_applicabilityValid_sep, sep_loOnC_imp_loOnA⟩

/-! ## §5  Axiom audit — all kernel-checked (no `native_decide`, no `sorryAx`) -/

#print axioms b_convergence_holds
#print axioms instance_equivalence
#print axioms separating_inequivalence
#print axioms not_applicabilityValid_sep
#print axioms sep_loOnC_imp_loOnA
#print axioms loOnA_keeps_edge

end Sal.Metatheory.G2AppAware
