import Sal.MRDTs.Metatheory.Development.ConditionedConvergence

/-!
# M2 — the conditioned execution model (Phase 0)

*Roadmap `ROADMAP_END_TO_END.md` M2.  Additive; modifies no existing file.*

This file supplies the execution model that **derives** the reachability premises that
`RGA_ConditionedConvergence.lean`'s `RGA_conditioned_convergence_bothFaithful` currently
takes as the `hReady`-shaped hypothesis.  It is stated **generically over an arbitrary
`ConditionedMRDTSig`** — there are no RGA internals here (per the roadmap: M2 is the
generic execution-model milestone).

## The model

`ConditionedConfiguration D` (§1) carries: an event set `events`; a causal-order relation
`vis` that is a strict partial order on the events; and the **generation discipline** as
structural fields —

* `distinct_ts`  — distinct events carry distinct timestamps (global uniqueness, the
  `apply`-rule freshness of `CRDT_TS.lean` accumulated over the run);
* `causal_mono`  — `vis a b → a.1 < b.1`: a causal predecessor was allocated a strictly
  smaller Lamport id (**monotone id allocation across replicas**);
* `inv_init` / `inv_step`  — the state-shape invariant `D.Inv` holds at `init` and is
  preserved by every **applicable** op (the conditioned analogue of the reachability
  invariant that, for the RGA, packages `wf ∧ contains 0 = false ∧ id_mono`).

`BackClosed C E` (§1) is the delivered/backward-closed condition on an event set.  A
*delivery prefix* is a `noopFeasible` list of `E`-events (`noopFeasible` reused verbatim
from `UpdateFeasibility_Gate.lean`: at each prefix the next op is `applicable` **or** a
Lean-`Eq` no-op there).

## What is derived (mapping to the NON-`Faithful` conjuncts of `hReady`)

For every backward-closed `E`, every delivery prefix `pre`, every `vis`-incomparable pair
`a, b ∈ E` pending at `pre`:

| `hReady` conjunct (RGA)                 | generic form derived here                    |
|-----------------------------------------|----------------------------------------------|
| `a.1 ≠ b.1` (distinct ts)               | `distinctTs`  (1)                            |
| `wf ∧ contains 0 = false ∧ id_mono`     | `D.Inv (fold pre)` via `inv_fold`            |
| `fresh_ts a`, `fresh_ts b`              | `freshTs` (3): id-freshness at the fold      |
| `NoFreshClash a b`, `NoFreshClash b a`  | `noFreshClash_concurrent` (4), relocated     |
| `Faithful a`, `Faithful b`              | *NOT derived* — the per-MRDT residue (M1/M3) |

`mono_alloc` (2) is `causal_mono` re-exposed (and `vis_wf`, its well-foundedness).  These
are bundled as **`conditioned_premises`** (§4): the packaged premise-supplier that emits
exactly the non-`Faithful` conjuncts.

## (5) existence of a `loOnA`-respecting `noopFeasible` delivery enumeration

Two independent, mechanized pieces (§5):

* `exists_loOnA_enum` — a generic **topological sort** (`exists_respecting`): from
  acyclicity of `loOnA` on a finite enumeration of `E` (the *satisfiability* condition —
  the same content the two decisive cases of `UpdateFeasibility_Gate.lean` discharge
  concretely) there **exists** a `loOnA`-respecting permutation of `E`.
* `noopFeasible_of_prefixApp` — the born-applicable **delivery discipline** (each op is
  `applicable`-or-no-op at its own prefix fold) is *exactly* `noopFeasible`, packaged as a
  reusable bridge.  `exists_loOnA_noopFeasible_enum` combines the two.

## Signature-level vs derived

Everything above is **derived** from the model's fields.  The RGA-state predicates
`wf`/`id_mono`/`fresh_ts`/`NoFreshClash`/`Faithful` are *not* reached into: `Inv` is the
generic stand-in for the first block, id-freshness/clash are the timestamp-level facts, and
`Faithful` is deliberately left as the per-MRDT residue (the located obstruction of
`RGA_ConditionedConvergence.lean` §6, i.e. M1/M3).  The one genuinely *assumed* input is the
**acyclicity of `loOnA` on `E`** (satisfiability) and the **born-applicable discipline**
(feasibility) that (5) consumes — both are properties a real execution provides by
construction and neither is RGA-specific.
-/

set_option maxHeartbeats 1000000

namespace Sal.Metatheory.ConditionedExecutionModel

open Sal.Emulation
open Sal.Metatheory.ConditionedConvergence (loOnA appliesDependsOn appOrNoop)
open Sal.Metatheory.UpdateFeasibilityGate (noopFeasible)

/-! ## §1  The conditioned configuration and its generation discipline -/

/-- **A conditioned execution configuration** for `D : ConditionedMRDTSig`.

The `events`/`vis` core is a strict partial order (causal order); the four *discipline*
fields (`distinct_ts`, `causal_mono`, `inv_init`, `inv_step`) encode the generation regime:
globally-unique timestamps, Lamport-monotone id allocation, and an `applicable`-preserved
state-shape invariant.  Mirrors the shape of `Sal.Emulation.Configuration` /
`Sal.Metatheory.Configuration` but keeps only what the M2 derivations consume. -/
structure ConditionedConfiguration (D : ConditionedMRDTSig) where
  /-- The events in play. -/
  events : Set (Op D.AppOp)
  /-- Causal-order (visibility) relation over events. -/
  vis : Op D.AppOp → Op D.AppOp → Prop
  /-- `vis` is irreflexive. -/
  vis_irrefl : ∀ {a}, ¬ vis a a
  /-- `vis` is transitive. -/
  vis_trans : ∀ {a b c}, vis a b → vis b c → vis a c
  /-- Every `vis`-edge source is an event. -/
  vis_src_mem : ∀ {a b}, vis a b → a ∈ events
  /-- Every `vis`-edge target is an event. -/
  vis_tgt_mem : ∀ {a b}, vis a b → b ∈ events
  /-- **Global timestamp uniqueness.**  Distinct events carry distinct timestamps. -/
  distinct_ts : ∀ {a b : Op D.AppOp}, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1
  /-- **Monotone id allocation.**  A causal predecessor was allocated a strictly smaller
  Lamport id — the generation clock increases along `vis`. -/
  causal_mono : ∀ {a b : Op D.AppOp}, vis a b → a.1 < b.1
  /-- The state-shape invariant holds at `init`. -/
  inv_init : D.Inv D.init
  /-- The state-shape invariant is preserved by every **applicable** op. -/
  inv_step : ∀ (s : D.State) (o : Op D.AppOp), D.Inv s → D.applicable o s → D.Inv (D.update s o)

namespace ConditionedConfiguration

variable {D : ConditionedMRDTSig}

/-- A delivered event set is **backward-closed** under `vis` and contained in `events`. -/
def BackClosed (C : ConditionedConfiguration D) (E : Set (Op D.AppOp)) : Prop :=
  E ⊆ C.events ∧ ∀ ⦃a b⦄, C.vis a b → b ∈ E → a ∈ E

/-- Two events are **concurrent** (`vis`-incomparable). -/
def Concurrent (C : ConditionedConfiguration D) (a b : Op D.AppOp) : Prop :=
  ¬ C.vis a b ∧ ¬ C.vis b a

/-! ## §2  `mono_alloc` and its well-foundedness (roadmap item (2)) -/

/-- **(2) Monotone allocation**, re-exposed: an ancestor's Lamport id is strictly smaller. -/
theorem mono_alloc (C : ConditionedConfiguration D) {a b : Op D.AppOp} (h : C.vis a b) :
    a.1 < b.1 :=
  C.causal_mono h

/-- `vis` is **well-founded** (hence acyclic): it is a subrelation of `<` on the Lamport id.
This is the acyclicity backbone of the version DAG — the `vis`-part of `loOnA` never cycles;
only its rc-part carries a genuine satisfiability obligation (see §5). -/
theorem vis_wf (C : ConditionedConfiguration D) : WellFounded C.vis := by
  have hsub : Subrelation C.vis (fun a b : Op D.AppOp => a.1 < b.1) := by
    intro a b h; exact C.causal_mono h
  exact hsub.wf (InvImage.wf (fun o : Op D.AppOp => o.1) Nat.lt_wfRel.wf)

/-! ## §3  The four structural derivations (1), Inv-at-fold, (3), (4) -/

/-- **(1) Distinct timestamps** for any two distinct delivered events. -/
theorem distinctTs (C : ConditionedConfiguration D) (E : Set (Op D.AppOp))
    (hE : C.BackClosed E) {a b : Op D.AppOp} (ha : a ∈ E) (hb : b ∈ E) (hne : a ≠ b) :
    a.1 ≠ b.1 :=
  C.distinct_ts (hE.1 ha) (hE.1 hb) hne

/-- **State-shape invariant at the fold.**  `D.Inv` is preserved along any `noopFeasible`
fold: `applicable` steps use `inv_step`, no-op steps preserve `Inv` because the state is
unchanged.  This is the generic stand-in for the RGA's `wf ∧ contains 0 = false ∧ id_mono`
block of `hReady`. -/
theorem inv_fold (C : ConditionedConfiguration D) :
    ∀ (pre : List (Op D.AppOp)) (s : D.State),
      D.Inv s → noopFeasible D pre s → D.Inv (applySeq D.toCRDTSig s pre) := by
  intro pre
  induction pre with
  | nil => intro s hs _; exact hs
  | cons o rest ih =>
    intro s hs hf
    obtain ⟨hstep, hrest⟩ := hf
    have hupd : D.Inv (D.update s o) := by
      rcases hstep with happ | hnoop
      · exact C.inv_step s o hs happ
      · rw [hnoop]; exact hs
    have hcons : applySeq D.toCRDTSig s (o :: rest)
        = applySeq D.toCRDTSig (D.update s o) rest := rfl
    rw [hcons]
    exact ih (D.update s o) hupd hrest

/-- **(3) Freshness at the fold.**  A pending event's timestamp differs from every timestamp
already recorded in a delivery prefix — the id-level content of the RGA's `fresh_ts a s'`. -/
theorem freshTs (C : ConditionedConfiguration D) (E : Set (Op D.AppOp))
    (hE : C.BackClosed E) {a : Op D.AppOp} (ha : a ∈ E)
    (pre : List (Op D.AppOp)) (hpre : ∀ x ∈ pre, x ∈ E) (hanp : a ∉ pre) :
    ∀ x ∈ pre, x.1 ≠ a.1 := by
  intro x hx
  have hxE : x ∈ E := hpre x hx
  have hxa : x ≠ a := by rintro rfl; exact hanp hx
  exact C.distinct_ts (hE.1 hxE) (hE.1 ha) hxa

/-- **(4) `NoFreshClash` for concurrent events**, relocated and generalized from
`RGA_ConditionedConvergence.noFreshClash_concurrent`.  For `b` not a causal ancestor of `a`
(in particular when `a ‖ b`), `b`'s id clashes with none of the ids recorded by `a` (its own
id or any causal ancestor's) — a consequence of global timestamp uniqueness, since every such
recorded event is distinct from `b`. -/
theorem noFreshClash_concurrent (C : ConditionedConfiguration D) {a b : Op D.AppOp}
    (hb : b ∈ C.events) (hab : a ≠ b) (hnba : ¬ C.vis b a) :
    ∀ c, (c = a ∨ C.vis c a) → c ∈ C.events → c.1 ≠ b.1 := by
  intro c hc hcev
  rcases hc with rfl | hvca
  · exact C.distinct_ts hcev hb hab
  · have hcb : c ≠ b := by rintro rfl; exact hnba hvca
    exact C.distinct_ts hcev hb hcb

/-! ## §4  The packaged premise-supplier

`conditioned_premises` emits, for a `vis`-incomparable pair pending at a `noopFeasible`
delivery prefix, exactly the NON-`Faithful` conjuncts of `hReady` (in their generic forms;
see the file header's mapping table).  `Faithful a` / `Faithful b` are deliberately absent —
they are the per-MRDT residue that M1/M3 discharge, not the execution model. -/
theorem conditioned_premises (C : ConditionedConfiguration D) (E : Set (Op D.AppOp))
    (hE : C.BackClosed E)
    (pre : List (Op D.AppOp)) (hpre_sub : ∀ x ∈ pre, x ∈ E)
    (hpre_feas : noopFeasible D pre D.init)
    {a b : Op D.AppOp} (ha : a ∈ E) (hb : b ∈ E) (hab : a ≠ b)
    (hanp : a ∉ pre) (hbnp : b ∉ pre) (hconc : C.Concurrent a b) :
    -- (1) distinct timestamps
    a.1 ≠ b.1
    -- state-shape invariant at the fold (generic `wf ∧ contains 0 = false ∧ id_mono`)
    ∧ D.Inv (applySeq D.toCRDTSig D.init pre)
    -- (3) freshness of `a` and of `b` at the fold (id form of `fresh_ts`)
    ∧ (∀ x ∈ pre, x.1 ≠ a.1)
    ∧ (∀ x ∈ pre, x.1 ≠ b.1)
    -- (4) `NoFreshClash` for the concurrent pair, both directions
    ∧ (∀ c, (c = a ∨ C.vis c a) → c ∈ C.events → c.1 ≠ b.1)
    ∧ (∀ c, (c = b ∨ C.vis c b) → c ∈ C.events → c.1 ≠ a.1) := by
  refine ⟨C.distinctTs E hE ha hb hab, ?_,
    C.freshTs E hE ha pre hpre_sub hanp, C.freshTs E hE hb pre hpre_sub hbnp, ?_, ?_⟩
  · exact C.inv_fold pre D.init C.inv_init hpre_feas
  · exact C.noFreshClash_concurrent (hE.1 hb) hab hconc.2
  · exact C.noFreshClash_concurrent (hE.1 ha) (Ne.symm hab) hconc.1

/-! ## §5  Existence of a `loOnA`-respecting, `noopFeasible` delivery enumeration -/

/-- **Generic topological sort.**  Any finite list `l` admits a permutation that is
`respects`-ordered for `R` (no `R`-edge points backward), provided every nonempty sub-list of
`l` has an `R`-minimal element — the acyclicity/extendability condition.  Proof: strong
induction on length, peeling an `R`-minimal head. -/
theorem exists_respecting {α : Type} [DecidableEq α] (R : α → α → Prop) :
    ∀ (n : ℕ) (l : List α), l.length = n →
      (∀ l', l' ⊆ l → l' ≠ [] → ∃ m, m ∈ l' ∧ ∀ y ∈ l', ¬ R y m) →
      ∃ π, List.Perm π l ∧ respects π R := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l hlen hmin
    rcases l with _ | ⟨x, xs⟩
    · exact ⟨[], List.Perm.refl _, List.Pairwise.nil⟩
    · obtain ⟨m, hm_mem, hm_min⟩ := hmin (x :: xs) (List.Subset.refl _) (List.cons_ne_nil x xs)
      have hsub : (x :: xs).erase m ⊆ (x :: xs) := by
        intro a h; exact List.mem_of_mem_erase h
      have hlen' : ((x :: xs).erase m).length = n - 1 := by
        rw [List.length_erase_of_mem hm_mem, hlen]
      have hlt : n - 1 < n := by
        have hpos : 0 < n := by rw [← hlen]; simp
        omega
      have hmin' : ∀ l', l' ⊆ (x :: xs).erase m → l' ≠ [] →
          ∃ mm, mm ∈ l' ∧ ∀ y ∈ l', ¬ R y mm :=
        fun l' hl' hne => hmin l' (hl'.trans hsub) hne
      obtain ⟨π', hπ'_perm, hπ'_pw⟩ := ih (n - 1) hlt ((x :: xs).erase m) hlen' hmin'
      refine ⟨m :: π', ?_, ?_⟩
      · exact ((List.perm_cons_erase hm_mem).trans (List.Perm.cons m hπ'_perm.symm)).symm
      · show (m :: π').Pairwise (fun a b => ¬ R b a)
        exact List.pairwise_cons.mpr
          ⟨fun y hy => hm_min y (hsub (hπ'_perm.mem_iff.mp hy)), hπ'_pw⟩

/-- **(5a) A `loOnA`-respecting delivery enumeration exists.**  From acyclicity of `loOnA` on
a finite enumeration of the delivered set `E`, `exists_respecting` produces a permutation of
`E` respecting `loOnA`.  Acyclicity is the *satisfiability* half — the very thing
`UpdateFeasibility_Gate.lean` discharges concretely on its two decisive cases. -/
theorem exists_loOnA_enum
    (Cfg : Sal.Emulation.Configuration D.toCRDTSig) (E : Set (Op D.AppOp))
    (lE : List (Op D.AppOp)) (hnd : lE.Nodup) (henum : ∀ a, a ∈ lE ↔ a ∈ E)
    (hacyc : ∀ l', l' ⊆ lE → l' ≠ [] → ∃ m, m ∈ l' ∧ ∀ y ∈ l', ¬ loOnA D Cfg E y m) :
    ∃ π, listPermOf π E ∧ respects π (loOnA D Cfg E) := by
  obtain ⟨π, hperm, hpw⟩ := exists_respecting (loOnA D Cfg E) lE.length lE rfl hacyc
  refine ⟨π, ⟨hperm.nodup_iff.mpr hnd, fun a => ?_⟩, hpw⟩
  rw [hperm.mem_iff]; exact henum a

/-- **The born-applicable delivery discipline is exactly `noopFeasible`.**  If, at every
prefix split `π = pfx ++ o :: rest`, the next op `o` is `applicable`-or-no-op at the prefix
fold, then `π` is `noopFeasible`.  A reusable bridge from the generation discipline to the
feasibility notion the convergence engine consumes. -/
theorem noopFeasible_of_prefixApp (π : List (Op D.AppOp)) (s : D.State)
    (h : ∀ (pfx : List (Op D.AppOp)) (o : Op D.AppOp) (rest : List (Op D.AppOp)),
        π = pfx ++ o :: rest → appOrNoop D o (applySeq D.toCRDTSig s pfx)) :
    noopFeasible D π s := by
  induction π generalizing s with
  | nil => trivial
  | cons o rest ih =>
    refine ⟨?_, ?_⟩
    · simpa [applySeq, appOrNoop] using h [] o rest rfl
    · apply ih
      intro pfx o' rest' hEq
      have hh := h (o :: pfx) o' rest' (by simp [hEq])
      simpa [applySeq] using hh

/-- **(5) A `loOnA`-respecting *and* `noopFeasible` delivery enumeration exists.**  Combines
(5a) — existence from acyclicity — with the born-applicable delivery discipline `hdisc`
(applicable-or-no-op at every `loOnA`-respecting prefix fold).  The two hypotheses are the
satisfiability and feasibility halves respectively; both are properties a genuine execution
supplies, neither is RGA-specific. -/
theorem exists_loOnA_noopFeasible_enum
    (Cfg : Sal.Emulation.Configuration D.toCRDTSig) (E : Set (Op D.AppOp))
    (lE : List (Op D.AppOp)) (hnd : lE.Nodup) (henum : ∀ a, a ∈ lE ↔ a ∈ E)
    (hacyc : ∀ l', l' ⊆ lE → l' ≠ [] → ∃ m, m ∈ l' ∧ ∀ y ∈ l', ¬ loOnA D Cfg E y m)
    (hdisc : ∀ (pfx : List (Op D.AppOp)) (o : Op D.AppOp) (rest : List (Op D.AppOp)),
        listPermOf (pfx ++ o :: rest) E → respects (pfx ++ o :: rest) (loOnA D Cfg E) →
        appOrNoop D o (applySeq D.toCRDTSig D.init pfx)) :
    ∃ π, listPermOf π E ∧ respects π (loOnA D Cfg E) ∧ noopFeasible D π D.init := by
  obtain ⟨π, hperm, hresp⟩ := exists_loOnA_enum Cfg E lE hnd henum hacyc
  refine ⟨π, hperm, hresp, ?_⟩
  apply noopFeasible_of_prefixApp
  intro pfx o rest hsplit
  exact hdisc pfx o rest (hsplit ▸ hperm) (hsplit ▸ hresp)

/-! ## §6  Inhabitance: the empty configuration -/

/-- The empty configuration (no events), witnessing that the model is inhabited for every
`D` whose `Inv` holds at `init` and is preserved by applicable ops.  Mirrors the role of
`initConfig` in `ExecutionModel.lean`. -/
def emptyConfig (D : ConditionedMRDTSig) (hInit : D.Inv D.init)
    (hstep : ∀ (s : D.State) (o : Op D.AppOp), D.Inv s → D.applicable o s → D.Inv (D.update s o)) :
    ConditionedConfiguration D where
  events := (∅ : Set (Op D.AppOp))
  vis := fun _ _ => False
  vis_irrefl := by intro a h; exact h
  vis_trans := by intro a b c h; exact h.elim
  vis_src_mem := by intro a b h; exact h.elim
  vis_tgt_mem := by intro a b h; exact h.elim
  distinct_ts := by intro a b ha _ _; simp only [Set.mem_empty_iff_false] at ha
  causal_mono := by intro a b h; exact h.elim
  inv_init := hInit
  inv_step := hstep

end ConditionedConfiguration

/-! ## §7  Axiom audit — every M2 result kernel-clean

All decls depend only on `propext`, `Classical.choice`, `Quot.sound`: no `sorryAx`, no
`native_decide`.  In particular the `Merge_Linearization_Set` sorries reachable through the
import chain are NOT transitively touched (nothing here uses `convergence_on_u`). -/

#print axioms ConditionedConfiguration.mono_alloc
#print axioms ConditionedConfiguration.vis_wf
#print axioms ConditionedConfiguration.distinctTs
#print axioms ConditionedConfiguration.inv_fold
#print axioms ConditionedConfiguration.freshTs
#print axioms ConditionedConfiguration.noFreshClash_concurrent
#print axioms ConditionedConfiguration.conditioned_premises
#print axioms ConditionedConfiguration.exists_respecting
#print axioms ConditionedConfiguration.exists_loOnA_enum
#print axioms ConditionedConfiguration.noopFeasible_of_prefixApp
#print axioms ConditionedConfiguration.exists_loOnA_noopFeasible_enum
#print axioms ConditionedConfiguration.emptyConfig

end Sal.Metatheory.ConditionedExecutionModel
