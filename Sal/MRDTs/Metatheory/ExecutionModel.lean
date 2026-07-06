import Sal.MRDTs.Metatheory.MRDTSig
-- `Set` lemma API (`Set.empty_inter`, …); `MRDTSig`'s transitive imports carry only the
-- `Set` notation, not the basic lemmas. This is a foundational Mathlib file — it does NOT
-- pull in `Sal.Emulation.Merge_Linearization`.
import Mathlib.Data.Set.Basic

/-!
# Ternary execution model: replica-keyed Configuration + ranked-version store (Phase-0 **S2**)

This is step **S2** of the Neem soundness meta-theory (Phase-0, TTL+RV design; see
`Sal/MRDTs/Metatheory/PHASE0_PLAN.md` §1.3, §1.7 and §4 S2). It builds the *execution model* for a
`ConditionedMRDTSig` on top of the S1 foundation (`Sal.Metatheory.MRDTSig`):

* the ternary **`Configuration`** — the *replica-keyed core* (`N`/`L`/`vis` + the six
  invariants ported VERBATIM from `Sal.Emulation.CRDT_TS`), PLUS the *additive* **ranked
  version store** `ver`/`head`/`parents` with the DAG-rank field `parents_lt` and the four
  store-coherence invariants `ver_init`/`head_coherent`/`ver_inv`/`lca_events`;
* **`Reaches`** (reachability in the version DAG) and **`IsLCA`** (the LCA predicate the
  ternary merge reads), together with the fact that `parents_lt` makes the parent-step
  relation **well-founded** (`parentStep_wf` / `Configuration.parents_wf`);
* **`initConfig`** with *every* Configuration invariant — replica-keyed core AND ranked store
  — discharged sorry-free.

**Design (Version = allocation rank).** A `Version` *is* its allocation rank (`Nat`); the DAG
field `parents_lt : p ∈ parents v → p < v` fuses acyclicity and the generation clock into one
decidable fact. This is the structural home for the generation-time id-monotonicity invariant
`AllocMono`/`id_mono` (S5, `RGA_Reachability_Invariant.lean:227`), which plugs onto the store
as a `Configuration D → Prop` — see `AllocMonoTrivial` (the flat-RDT hook) below.

**Exit criteria (PHASE0_PLAN §4 S2), all discharged here:**
1. compiles clean, no `sorry`;
2. `initConfig` satisfies every Configuration invariant (core + store), sorry-free;
3. `Reaches` is well-founded, derived from `parents_lt` (`parentStep_wf`).

**Deferred, per §4 S2 scope note.** `lca_events` maintenance under `Step.merge` is deferred
post-Phase-0 (`appendix.tex:6-37`). Here it is only *discharged for `initConfig`* — where it
holds unconditionally because the only registered version is `0` (all event sets are `∅`), so
**no sorry is needed at S2**.

**Deviation from §1.3 (documented).** `initConfig` takes an extra hypothesis
`hInit : D.Inv D.init`. The store invariant `ver_inv` demands `Inv` of every registered state,
and `ver_init` registers `D.init` at version `0`; for an arbitrary `ConditionedMRDTSig` there
is no free proof of `Inv init`. This is exactly S5's `ReachInv.init_inv`
(`PHASE0_PLAN §1.7`), so threading it here is faithful and unavoidable.
-/

namespace Sal.Metatheory

open Sal.Emulation

/-! ## §1.3 — Version DAG: `Reaches` and `IsLCA` -/

/-- A version id **is** its allocation rank (Design 2). The ranked store keys states by
`Version`, and `parents_lt` orders them, giving the generation clock a decidable home. -/
abbrev Version : Type := Nat

/-- Reachability in the version DAG: the reflexive–transitive closure of the *parent* edge
`a ∈ parents b` (so `Reaches parents anc v` means `anc` is an ancestor of `v`, and — under
`parents_lt` — `anc ≤ v`, see `reaches_le`). -/
def Reaches (parents : Version → List Version) : Version → Version → Prop :=
  Relation.ReflTransGen (fun a b => a ∈ parents b)

/-- `v⊤` is a **least common ancestor** (greatest-rank common ancestor) of `v₁, v₂` in the
version DAG: it reaches both, and dominates every common ancestor. This is the predicate the
ternary `Step.merge` supplies (and proves) and from which the merge reads the LCA state `l`
via `ver v⊤`. -/
def IsLCA (parents : Version → List Version) (v₁ v₂ vT : Version) : Prop :=
  Reaches parents vT v₁ ∧ Reaches parents vT v₂ ∧
    ∀ w, Reaches parents w v₁ → Reaches parents w v₂ → Reaches parents w vT

/-! ## Well-foundedness from `parents_lt`

`parents_lt : p ∈ parents v → p < v` makes the parent-step relation a subrelation of `<` on
`Nat`, hence well-founded. This is the exit-criterion "`Reaches` well-founded, derived from
`parents_lt`": it justifies well-founded recursion over the version DAG (the S6 lex carving
runs above it) and it forces `Reaches` to increase rank (`reaches_le`), so an LCA has strictly
smaller rank than its descendants — the fact `Step.merge`'s `h_alloc : v₁,v₂ < vm` relies on. -/

/-- The parent-step relation `a ∈ parents b` is **well-founded** whenever `parents_lt` holds:
it is a subrelation of `<` on `Nat`. -/
theorem parentStep_wf {parents : Version → List Version}
    (h : ∀ v p, p ∈ parents v → p < v) :
    WellFounded (fun a b : Version => a ∈ parents b) := by
  have hsub : Subrelation (fun a b : Version => a ∈ parents b)
      (fun a b : Version => a < b) := by
    intro a b hab
    exact h b a hab
  exact hsub.wf Nat.lt_wfRel.wf

/-- `Reaches` monotonically increases rank: an ancestor has `≤` rank. Direct consequence of
`parents_lt`; used later to reason that an LCA sits strictly below its descendants. -/
theorem reaches_le {parents : Version → List Version}
    (h : ∀ v p, p ∈ parents v → p < v) {a b : Version}
    (hr : Reaches parents a b) : a ≤ b := by
  induction hr with
  | refl => exact Nat.le_refl a
  | tail _prev hstep ih => exact Nat.le_of_lt (Nat.lt_of_le_of_lt ih (h _ _ hstep))

/-! ## §1.3 — The ternary Configuration

The **replica-keyed core** (`N`/`L`/`vis` + the six invariants) is ported VERBATIM from
`Sal.Emulation.CRDT_TS.Configuration` (`CRDT_TS.lean:39-75`), retyped over `ConditionedMRDTSig`
— this keeps `IsRALinearizable`/the four replica-keyed bridge cases reusable byte-for-byte
(PHASE0_PLAN §1.3 "Why replica-keyed core"). The **ranked version store** is the sole new
structural content and is *additive*: it is read only by the (S3) `Step.merge` and the (S5)
conditioning layer, so it never perturbs the reused cases. -/

/-- A ternary configuration for `D : ConditionedMRDTSig`. -/
structure Configuration (D : ConditionedMRDTSig) where
  -- ── replica-keyed core (ported verbatim from `CRDT_TS.lean:39-75`) ──────────────────────
  /-- Per-replica head state. -/
  N : Replica → Option D.State
  /-- Per-replica set of observed events. -/
  L : Replica → Option (Set (Op D.AppOp))
  /-- Visibility relation over events. -/
  vis : Op D.AppOp → Op D.AppOp → Prop
  /-- Domain of `N` equals domain of `L`. -/
  dom_eq : ∀ r, N r = none ↔ L r = none
  /-- Every edge in `vis` has its source event observed at some replica. -/
  vis_src : ∀ {a b}, vis a b → ∃ r s, L r = some s ∧ s a
  /-- Every edge in `vis` has its target event observed at some replica. -/
  vis_tgt : ∀ {a b}, vis a b → ∃ r s, L r = some s ∧ s b
  /-- Causal closure: `vis a b` and `b` observed at `r` ⇒ `a` observed at `r`. -/
  vis_causal : ∀ {a b r s}, vis a b → L r = some s → s b → s a
  /-- Timestamp uniqueness: distinct events have distinct timestamps.
  Discharged structurally by the Lamport-clock + replica-id timestamp scheme: `a.1 = (lts, rid)`
  with the lexicographic order (compare `lts`, tie-break on `rid`) is unique across events. -/
  timestamps_distinct :
    ∀ {a b : Op D.AppOp} {r s r' s'},
      L r = some s → s a → L r' = some s' → s' b →
      a ≠ b → a.1 ≠ b.1
  /-- **Causal monotonicity**: a causal predecessor has a strictly smaller timestamp. This is the
  fundamental Lamport-clock guarantee (`a → b ⟹ lts(a) < lts(b)`, so the lexicographic `(lts,rid)`
  order strictly increases), threaded generically so the datatype Join never re-derives it. The one
  execution-model fact (with `timestamps_distinct`) the merge VC needs for the generation regime
  (`WfOpGenQ`/reference-causality follow from it + causal closure). -/
  causal_mono : ∀ {a b : Op D.AppOp}, vis a b → a.1 < b.1
  /-- Same-replica totality of `vis`. -/
  vis_total_same_replica :
    ∀ {a b : Op D.AppOp} {r s r' s'},
      L r = some s → s a → L r' = some s' → s' b →
      a ≠ b → a.2.1 = b.2.1 → vis a b ∨ vis b a
  -- ── additive ranked version store (the only new structural content) ─────────────────────
  /-- Version ↦ its `(state, event-set)`. `none` = unallocated. -/
  ver : Version → Option (D.State × Set (Op D.AppOp))
  /-- Replica ↦ its head version id. -/
  head : Replica → Option Version
  /-- The version DAG `G` (each version's parents). -/
  parents : Version → List Version
  /-- DAG rank: a parent has strictly smaller id. Fuses acyclicity with the generation clock;
  makes the parent-step relation well-founded (`parentStep_wf`). -/
  parents_lt : ∀ v p, p ∈ parents v → p < v
  /-- Version `0` is the initial `(init, ∅)`. -/
  ver_init : ver 0 = some (D.init, ∅)
  /-- A replica's head version carries exactly that replica's `(state, event-set)`. -/
  head_coherent : ∀ r v, head r = some v →
    (ver v).map Prod.fst = N r ∧ (ver v).map Prod.snd = L r
  /-- Every registered state satisfies the state-shape `Inv` (so `commutesOn` can fire at any
  registered version — the conditioning discharge in §3 reads this). -/
  ver_inv : ∀ v s e, ver v = some (s, e) → D.Inv s
  /-- **Lemma LCA / N10** (`lin.tex:160`): the LCA's event set is the intersection of the two
  merged event sets. Discharged for `initConfig` here; its `Step.merge` maintenance is deferred
  post-Phase-0 (`appendix.tex:6-37`, PHASE0_PLAN §4 S2 scope note). -/
  lca_events : ∀ {v₁ v₂ vT s₁ e₁ s₂ e₂ sT eT},
    IsLCA parents v₁ v₂ vT →
    ver v₁ = some (s₁, e₁) → ver v₂ = some (s₂, e₂) → ver vT = some (sT, eT) →
    eT = e₁ ∩ e₂

namespace Configuration

variable {D : ConditionedMRDTSig}

/-- Set of all events witnessed anywhere in the configuration (ported from
`CRDT_TS.lean:80`; consumed by S5's `events_applicable`). -/
def events (C : Configuration D) : Set (Op D.AppOp) :=
  fun e => ∃ r s, C.L r = some s ∧ s e

/-- State registered at a version, if any (the ternary merge reads the LCA state `l` as
`C.verState v⊤`). -/
def verState (C : Configuration D) (v : Version) : Option D.State :=
  (C.ver v).map Prod.fst

/-- Event-set registered at a version, if any. -/
def verEvents (C : Configuration D) (v : Version) : Option (Set (Op D.AppOp)) :=
  (C.ver v).map Prod.snd

/-- The parent-step relation of `C` is well-founded (from the `parents_lt` field). This is the
`Configuration`-level form of the S2 well-foundedness exit criterion; it drives well-founded
recursion / induction over `C`'s version DAG in S6. -/
theorem parents_wf (C : Configuration D) :
    WellFounded (fun a b : Version => a ∈ C.parents b) :=
  parentStep_wf C.parents_lt

/-- Ancestors have `≤` rank in `C`'s DAG (the `Configuration`-level form of `reaches_le`). -/
theorem reaches_le' (C : Configuration D) {a b : Version}
    (hr : Reaches C.parents a b) : a ≤ b :=
  reaches_le C.parents_lt hr

/-- The ternary linearization order over the ternary `Configuration` (mirror of
`Sal.Metatheory.lo`, reading this configuration's own `.vis`; the S6 merge induction reads it).
On the flat slice it coincides with `Sal.Metatheory.lo`/`Sal.Emulation.lo` (S1 collapse). -/
def lo (C : Configuration D) (e₁ e₂ : Op D.AppOp) : Prop :=
  (C.vis e₁ e₂ ∧ ¬ D.commutesOn e₁ e₂)
  ∨ ( ¬ C.vis e₁ e₂ ∧ ¬ C.vis e₂ e₁
      ∧ D.rc e₁ e₂ = RcRes.Fst_then_snd
      ∧ ¬ ∃ e₃, C.vis e₂ e₃ ∧ ¬ D.commutesOn e₂ e₃ )

end Configuration

/-! ## Seam for S5: the generation-time `AllocMono` hook

`AllocMono : Configuration D → Prop` is the per-RDT generation-time predicate hosted on the
ranked store (PHASE0_PLAN §1.7). It is established at `apply` (fresh-max id) and maintained
across `merge` (`vm > v₁,v₂`), and it is what `ReachInv.merge_preserves` consumes to close the
`merge_breaks_wf` gap. For RGA it is the id-monotone anchor invariant

  `∀ v t s e, ver v = some (s,e) → contains s t → anc s t = 0 ∨ anc s t < t`
  (`RGA_Reachability_Invariant.lean:227`).

For flat RDTs it collapses to the trivial predicate below. S5 defines the real per-RDT
`AllocMono` over exactly this store shape (`ver`/`parents`/`parents_lt`); S2 only fixes the
seam. -/
def AllocMonoTrivial {D : ConditionedMRDTSig} (_ : Configuration D) : Prop := True

/-! ## §1.3 / §4 S2 — the initial configuration, all invariants discharged

`initConfig D hInit`: a single replica `r₀ = 0` at `D.init` observing no events, with a
one-node version DAG (version `0 = (init, ∅)`, no parents). Every replica-keyed core invariant
(ported verbatim) AND every ranked-store invariant is discharged sorry-free. See the top-of-file
note on the `hInit : D.Inv D.init` hypothesis (this is S5's `init_inv`). -/

/-- The only registered version in `initConfig`'s store is `0`, carrying `(init, ∅)`: a
`ver v = some (s,e)` forces `v = 0`, `s = init`, `e = ∅`. Powers the four store-invariant
discharges below without touching `if`-beta in tactic mode. -/
private theorem initVer_decompose {D : ConditionedMRDTSig}
    {v : Version} {s : D.State} {e : Set (Op D.AppOp)}
    (hv : (if v = 0 then some (D.init, (∅ : Set (Op D.AppOp))) else none) = some (s, e)) :
    v = 0 ∧ s = D.init ∧ e = ∅ := by
  by_cases h : v = 0
  · rw [if_pos h, Option.some.injEq, Prod.mk.injEq] at hv
    exact ⟨h, hv.1.symm, hv.2.symm⟩
  · rw [if_neg h] at hv
    simp at hv

/-- Initial configuration with all invariants discharged. -/
def initConfig (D : ConditionedMRDTSig) (hInit : D.Inv D.init) : Configuration D where
  -- replica-keyed core (values + proofs ported verbatim from `CRDT_TS.lean:147-168`)
  N := fun r => if r = 0 then some D.init else none
  L := fun r => if r = 0 then some ∅ else none
  vis := fun _ _ => False
  dom_eq := by
    intro r
    by_cases h : r = 0
    · subst h; simp
    · simp [h]
  vis_src := fun h => absurd h id
  vis_tgt := fun h => absurd h id
  vis_causal := fun h _ _ => absurd h id
  causal_mono := fun h => absurd h id
  timestamps_distinct := by
    intro a b r s r' s' hLr hsa _ _ _
    by_cases hr : r = 0
    · subst hr; simp at hLr; subst hLr; exact hsa.elim
    · simp [hr] at hLr
  vis_total_same_replica := by
    intro a b r s r' s' hLr hsa _ _ _ _
    by_cases hr : r = 0
    · subst hr; simp at hLr; subst hLr; exact hsa.elim
    · simp [hr] at hLr
  -- ranked version store
  ver := fun v => if v = 0 then some (D.init, ∅) else none
  head := fun r => if r = 0 then some 0 else none
  parents := fun _ => []
  parents_lt := by
    intro v p hp; simp at hp
  ver_init := by simp
  head_coherent := by
    intro r v hr
    by_cases hr0 : r = 0
    · subst hr0
      simp at hr
      subst hr
      refine ⟨?_, ?_⟩ <;> simp
    · simp [hr0] at hr
  ver_inv := by
    intro v s e hv
    have hs := (initVer_decompose hv).2.1
    rw [hs]; exact hInit
  lca_events := by
    intro v₁ v₂ vT s₁ e₁ s₂ e₂ sT eT _hlca hv₁ hv₂ hvT
    have h1 := (initVer_decompose hv₁).2.2
    have h2 := (initVer_decompose hv₂).2.2
    have h3 := (initVer_decompose hvT).2.2
    subst h1; subst h2; subst h3
    -- goal: (∅ : Set _) = ∅ ∩ ∅
    rw [Set.empty_inter]

/-! ## Axiom audit (exit-criterion lemmas) -/

#print axioms parentStep_wf
#print axioms reaches_le
#print axioms initConfig

end Sal.Metatheory
