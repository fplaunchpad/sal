import Sal.ConditionedMRDTs.Framework.Sigma_LoOn3
import Sal.CRDTs.Metatheory.JoinLemma_Of_CD

/-!
# The VC set for RA-linearizable MRDTs

The bundle in one place. The canonical derivation (all discharged instances except
the Enable-wins flag) is

    CoreVCs3CD + FeasibleDeltaVCs3 + CDVC3  ⇒  JoinLemma3  ⇒  RA-lin

with **eight verification conditions**: the three guarded update-layer fields of
`UpdateVCs` (in `Sigma_LoOn3.lean`), `mergeL_comm`, the three feasible delta
laws, and the causal-delta equation. `DeltaVCs3` is the *unconditional*
on-ramp (group ⊕ lattice classes: Counter, G-Set); `CoreVCs3` is the wider
bundle it rides on; `JoinLemma3F` is the **full-closure** join notion the
Enable-wins derivation uses (counter-comparison merges need full causal closure).
Adequacy of the set is `Adequacy.lean`; the discharges are `MRDT_Instances.lean`.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

section
variable {D : ConditionedMRDTSig}

/-- **The ternary core VC bundle**, exactly what the ternary Join induction consumes:

* the three update-layer fields, unchanged (`update_core`);
* `mergeL_comm` — commutativity in the two *branch* arguments;
* `mergeL_init` — the unit law `mergeL σ₀ σ₀ s = s` (the paper's `MergeIdempotence`
  `mergeL l s s = s` is not consumed anywhere in the induction);
* `lem_0op3` — the ternary 0-OP peel, **with the LCA argument carrying the event**:
  a union-maximal shared event is an LCA event, so all three components peel it.
  This is where ternary-ness is load-bearing: the counter satisfies `lem_0op3`
  but violates the binary `lem_0op`;
* `merge_peel_comm3` — the local peel against fold-shaped LCA and other-branch
  arguments, for events commuting with both. -/
structure CoreVCs3 (D : ConditionedMRDTSig) : Prop where
  update_core : UpdateVCs D.toCRDTSig
  mergeL_comm : ∀ l a b : D.State, D.mergeL l a b = D.mergeL l b a
  mergeL_init : ∀ s : D.State, D.mergeL D.init D.init s = s
  lem_0op3 :
    ∀ (l a b : D.State) (e : Op D.AppOp),
      D.mergeL (D.update l e) (D.update a e) (D.update b e)
        = D.update (D.mergeL l a b) e
  merge_peel_comm3 :
    ∀ (a : D.State) (e : Op D.AppOp) (π₀ π₂ : List (Op D.AppOp)),
      (∀ x ∈ π₀, D.toCRDTSig.commutes e x) →
      (∀ x ∈ π₂, D.toCRDTSig.commutes e x) →
      D.mergeL (applySeq D.toCRDTSig D.init π₀) (D.update a e)
          (applySeq D.toCRDTSig D.init π₂)
        = D.update (D.mergeL (applySeq D.toCRDTSig D.init π₀) a
            (applySeq D.toCRDTSig D.init π₂)) e

/-- **The ternary Join Lemma**: for backward-closed `E₁, E₂` with canonical states
`s₁, s₂` and the canonical state `s₀` of the LCA event set `E₁ ∩ E₂` (which is what the
LCA version holds, by the LCA lemma, `LCA_Lemma.lean`), the ternary merge produces the
canonical state of the union. -/
def JoinLemma3 (D : ConditionedMRDTSig) : Prop :=
  ∀ (C : Sal.Emulation.Configuration D.toCRDTSig)
    (ev₁ ev₂ : Set (Op D.AppOp)) (s₀ s₁ s₂ : D.State),
    (∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c) →
    (∀ a : Op D.AppOp, ¬ C.vis a a) →
    (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
    (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₁ → a ∈ ev₁) →
    (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₂ → a ∈ ev₂) →
    IsCanonicalState C (ev₁ ∩ ev₂) s₀ →
    IsCanonicalState C ev₁ s₁ → IsCanonicalState C ev₂ s₂ →
    IsCanonicalState C (ev₁ ∪ ev₂) (D.mergeL s₀ s₁ s₂)

/-- The ternary Join Lemma **at a single configuration**, the per-`C` body of
`JoinLemma3`. Instances whose join holds only under configuration-level
hypotheses (an honest-history contract, say) supply this directly to
`goodConfig3_merge_at`; `JoinLemma3` is the `∀ C` closure. -/
def JoinLemma3At (D : ConditionedMRDTSig)
    (C : Sal.Emulation.Configuration D.toCRDTSig) : Prop :=
  ∀ (ev₁ ev₂ : Set (Op D.AppOp)) (s₀ s₁ s₂ : D.State),
    (∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c) →
    (∀ a : Op D.AppOp, ¬ C.vis a a) →
    (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
    (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₁ → a ∈ ev₁) →
    (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₂ → a ∈ ev₂) →
    IsCanonicalState C (ev₁ ∩ ev₂) s₀ →
    IsCanonicalState C ev₁ s₁ → IsCanonicalState C ev₂ s₂ →
    IsCanonicalState C (ev₁ ∪ ev₂) (D.mergeL s₀ s₁ s₂)

theorem JoinLemma3.at {D : ConditionedMRDTSig} (h : JoinLemma3 D)
    (C : Sal.Emulation.Configuration D.toCRDTSig) : JoinLemma3At D C :=
  fun ev₁ ev₂ s₀ s₁ s₂ htr hir h1 h2 hc1 hc2 => h C ev₁ ev₂ s₀ s₁ s₂ htr hir h1 h2 hc1 hc2

/-- **The delta contract**, the ternary replacement for the binary lattice
laws (`LatticeVCsPlus`). See the file header for the reading of `mergeL m · c`
as delta application, and for the two classes (group, lattice) that satisfy it
unconditionally. -/
structure DeltaVCs3 (D : ConditionedMRDTSig) : Prop where
  /-- A delta applied to all three components of a merge extracts once; the
  LCA-slot copy cancels the duplicate (the ternary stand-in for
  `merge_idem`). -/
  redistribute :
    ∀ (m x₀ x₁ x₂ c : D.State),
      D.mergeL (D.mergeL m x₀ c) (D.mergeL m x₁ c) (D.mergeL m x₂ c)
        = D.mergeL m (D.mergeL x₀ x₁ x₂) c
  /-- A delta application commutes past an enclosing merge through one branch
  slot. -/
  local_redistribute :
    ∀ (l m x c y : D.State),
      D.mergeL l (D.mergeL m x c) y = D.mergeL m (D.mergeL l x y) c

/-- **(CD3), the ternary causal-delta bound**: the single contextual per-MRDT
obligation of the causal-delta derivation. For a `loOn(U)`-maximal `e`, with
`A = σ(U∖e)` and `B = σ(↓e∖e)`,

    mergeL B A (update B e) = update A e.

Unlike the binary `CDVC` this is an *equation*, not a `⊑`-inequality: the Counter's
degenerate order leaves no antisymmetry to combine two halves. The merge on the left sits
at its honest LCA: the true LCA set of `U∖e` and `↓e` is `(U∖e) ∩ ↓e = ↓e∖{e}`, whose
canonical state is `B`. -/
def CDVC3 (D : ConditionedMRDTSig) : Prop :=
  ∀ (C : Sal.Emulation.Configuration D.toCRDTSig) (U : Set (Op D.AppOp))
    (A B : D.State) (e : Op D.AppOp),
    (∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c) →
    (∀ a : Op D.AppOp, ¬ C.vis a a) →
    (∀ a ∈ U, a ∈ C.events) →
    (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ U → a ∈ U) →
    e ∈ U →
    (∀ x ∈ U, x ≠ e → ¬ loOn C U e x) →
    IsCanonicalState C (U \ {e}) A →
    IsCanonicalState C (downset C e \ {e}) B →
    D.mergeL B A (D.update B e) = D.update A e

/-- The *unconditional* core the CD derivation consumes: update-layer plus
commutativity of `mergeL` in its branch arguments. (`mergeL_init`, `lem_0op3`,
`merge_peel_comm3` of `CoreVCs3` are all feasibility-bounded for real
LCA-sensitive MRDTs and are not required.) -/
structure CoreVCs3CD (D : ConditionedMRDTSig) : Prop where
  update_core : UpdateVCs D.toCRDTSig
  mergeL_comm : ∀ l a b : D.State, D.mergeL l a b = D.mergeL l b a

/-- The slim core from the full ternary bundle. -/
theorem CoreVCs3.toCD (hVC : CoreVCs3 D) : CoreVCs3CD D :=
  ⟨hVC.update_core, hVC.mergeL_comm⟩

/-! ### 1. The feasible-tuple contract -/

/-- **The feasible delta contract**: the redistribution laws (plus the unit law) restricted
to canonical tuples at honest LCAs of a configuration. Field by field:

* `feasible_init` — `mergeL σ₀ σ₀ s = s` for `s` canonical (the raw law is
  false for `EWFlag`: an infeasible state with a set flag but zero counter);
* `feasible_local_redistribute` — the `local_redistribute` instance the
  induction consumes in the local-peel case: `s₀ = σ(E₁∩E₂)`, `B = σ(↓e∖e)`,
  `t₁ = σ(E₁∖e)`, `s₂ = σ(E₂)`, `e` union-maximal and local to side 1. Every
  `mergeL` node of both sides is at its honest LCA: LHS-inner `(E₁∖e) ⊔ ↓e`
  at `↓e∖{e}`, LHS-outer `E₁ ⊔ E₂` at `E₁∩E₂`, RHS-inner `(E₁∖e) ⊔ E₂` at
  `(E₁∖e)∩E₂ = E₁∩E₂`, RHS-outer `(U∖e) ⊔ ↓e` at `↓e∖{e}`;
* `feasible_redistribute` — the shared-peel instance, all three components
  decomposed through the downset delta; honest LCAs throughout
  (`t₀ = σ((E₁∩E₂)∖e)` is the decomposed LCA component). -/
structure FeasibleDeltaVCs3 (D : ConditionedMRDTSig) : Prop where
  feasible_init :
    ∀ (C : Sal.Emulation.Configuration D.toCRDTSig)
      (ev : Set (Op D.AppOp)) (s : D.State),
      (∀ a ∈ ev, a ∈ C.events) →
      IsCanonicalState C ev s →
      D.mergeL D.init D.init s = s
  feasible_local_redistribute :
    ∀ (C : Sal.Emulation.Configuration D.toCRDTSig)
      (ev₁ ev₂ : Set (Op D.AppOp)) (s₀ B t₁ s₂ : D.State) (e : Op D.AppOp),
      (∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c) →
      (∀ a : Op D.AppOp, ¬ C.vis a a) →
      (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
      (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₁ → a ∈ ev₁) →
      (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₂ → a ∈ ev₂) →
      e ∈ ev₁ → e ∉ ev₂ →
      (∀ x ∈ ev₁ ∪ ev₂, x ≠ e → ¬ loOn C (ev₁ ∪ ev₂) e x) →
      IsCanonicalState C (ev₁ ∩ ev₂) s₀ →
      IsCanonicalState C (downset C e \ {e}) B →
      IsCanonicalState C (ev₁ \ {e}) t₁ →
      IsCanonicalState C ev₂ s₂ →
      D.mergeL s₀ (D.mergeL B t₁ (D.update B e)) s₂
        = D.mergeL B (D.mergeL s₀ t₁ s₂) (D.update B e)
  feasible_redistribute :
    ∀ (C : Sal.Emulation.Configuration D.toCRDTSig)
      (ev₁ ev₂ : Set (Op D.AppOp)) (t₀ t₁ t₂ B : D.State) (e : Op D.AppOp),
      (∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c) →
      (∀ a : Op D.AppOp, ¬ C.vis a a) →
      (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
      (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₁ → a ∈ ev₁) →
      (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₂ → a ∈ ev₂) →
      e ∈ ev₁ → e ∈ ev₂ →
      (∀ x ∈ ev₁ ∪ ev₂, x ≠ e → ¬ loOn C (ev₁ ∪ ev₂) e x) →
      IsCanonicalState C ((ev₁ ∩ ev₂) \ {e}) t₀ →
      IsCanonicalState C (downset C e \ {e}) B →
      IsCanonicalState C (ev₁ \ {e}) t₁ →
      IsCanonicalState C (ev₂ \ {e}) t₂ →
      D.mergeL (D.mergeL B t₀ (D.update B e)) (D.mergeL B t₁ (D.update B e))
          (D.mergeL B t₂ (D.update B e))
        = D.mergeL B (D.mergeL t₀ t₁ t₂) (D.update B e)

/-- The ternary Join Lemma under **full causal closure** of the sides, what
`GoodConfig3.ver_causal` supplies. Counter-comparison merges need it: the weak
(`¬commutes`) closure is defeated by commuting same-replica enables. -/
def JoinLemma3F (D : ConditionedMRDTSig) : Prop :=
  ∀ (C : Sal.Emulation.Configuration D.toCRDTSig)
    (ev₁ ev₂ : Set (Op D.AppOp)) (s₀ s₁ s₂ : D.State),
    (∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c) →
    (∀ a : Op D.AppOp, ¬ C.vis a a) →
    (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
    (∀ a b, C.vis a b → b ∈ ev₁ → a ∈ ev₁) →
    (∀ a b, C.vis a b → b ∈ ev₂ → a ∈ ev₂) →
    IsCanonicalState C (ev₁ ∩ ev₂) s₀ →
    IsCanonicalState C ev₁ s₁ → IsCanonicalState C ev₂ s₂ →
    IsCanonicalState C (ev₁ ∪ ev₂) (D.mergeL s₀ s₁ s₂)

/-! ### The rc-free `loOn` collapse

For signatures whose `rc` is everywhere `Either` (no arbitration edges), the
set-relative linearization relation collapses to its `vis` arm and becomes
independent of the event set. Direct-join instances (the mergeable queue) use
this to transfer `respects` obligations between the event sets a ternary
merge juggles (the sides, their intersection, their union). -/

/-- When `rc` is everywhere `Either`, `loOn` collapses to its `vis` arm and
is independent of the event set: the rc arm's `Fst_then_snd` hypothesis is
refuted outright. -/
theorem loOn_iff_of_rc_either {D' : CRDTSig}
    (hrc : ∀ o₁ o₂ : Op D'.AppOp, D'.rc o₁ o₂ = RcRes.Either)
    (C : Sal.Emulation.Configuration D') (ev : Set (Op D'.AppOp))
    (e₁ e₂ : Op D'.AppOp) :
    loOn C ev e₁ e₂ ↔ C.vis e₁ e₂ ∧ ¬ D'.commutes e₁ e₂ := by
  unfold loOn
  constructor
  · rintro (h | ⟨_, _, hfs, _⟩)
    · exact h
    · rw [hrc e₁ e₂] at hfs
      exact RcRes.noConfusion hfs
  · exact Or.inl

/-- With `rc` everywhere `Either`, `respects · (loOn C ev)` is independent of
`ev`. -/
theorem respects_transfer_of_rc_either {D' : CRDTSig}
    (hrc : ∀ o₁ o₂ : Op D'.AppOp, D'.rc o₁ o₂ = RcRes.Either)
    {C : Sal.Emulation.Configuration D'} {ev ev' : Set (Op D'.AppOp)}
    {ρ : List (Op D'.AppOp)}
    (h : respects ρ (loOn C ev)) : respects ρ (loOn C ev') := by
  unfold respects at h ⊢
  refine h.imp ?_
  intro a b hnab hab
  exact hnab ((loOn_iff_of_rc_either hrc C ev b a).mpr
    ((loOn_iff_of_rc_either hrc C ev' b a).mp hab))

end

end Sal.ConditionedMRDTs
