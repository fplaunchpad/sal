import Sal.MRDTs.Framework.ReplayLaws
import Sal.MRDTs.Metatheory.Join.BinaryJoin

/-!
# Contextual Join and reusable proof laws

The public semantic surface has one primitive obligation, `JoinAt D C`.
`JoinOn D Good` restricts it to contexts satisfying an explicit predicate;
`Join D` is the specialization to every replay context.

The structures below are reusable proof inputs, not alternative correctness
notions. `CanonicalJoinLaws` is the common canonical-state contract for the
reusable all-context `Join` induction. Stronger arbitrary-state equations can
be converted to that contract in `Adequacy.lean`. Datatypes may instead prove
`Join` or `JoinOn` directly.
-/

namespace Sal.MRDTs

open Sal.MRDTs.Foundation
open Classical

section
variable {D : MRDTSig}
variable [ReplayPolicy D.toUpdateSig]

/-- The semantic merge-preservation obligation at one replay context. Canonical
states for the branch intersection and two branches must merge to a canonical
state for their union. -/
def JoinAt (D : MRDTSig)
    [P : ReplayPolicy D.toUpdateSig]
    (C : Sal.MRDTs.Foundation.ReplayContext D.toUpdateSig) : Prop :=
  ∀ (ev₁ ev₂ : Set (Op D.AppOp)) (s₀ s₁ s₂ : D.State),
    (∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c) →
    (∀ a : Op D.AppOp, ¬ C.vis a a) →
    (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
    (∀ a b, C.vis a b → ¬ D.toUpdateSig.commutes a b → b ∈ ev₁ → a ∈ ev₁) →
    (∀ a b, C.vis a b → ¬ D.toUpdateSig.commutes a b → b ∈ ev₂ → a ∈ ev₂) →
    @IsCanonicalState _ P C (ev₁ ∩ ev₂) s₀ →
    @IsCanonicalState _ P C ev₁ s₁ → @IsCanonicalState _ P C ev₂ s₂ →
    @IsCanonicalState _ P C (ev₁ ∪ ev₂) (D.merge s₀ s₁ s₂)

/-- Join restricted to replay contexts satisfying `Good`. This keeps the
merge-preservation argument separate from the execution discipline that may
later establish `Good`. -/
def JoinOn (D : MRDTSig)
    [P : ReplayPolicy D.toUpdateSig]
    (Good : Sal.MRDTs.Foundation.ReplayContext D.toUpdateSig → Prop) : Prop :=
  ∀ C, Good C → JoinAt D (P := P) C

/-- All-context Join: the contextual merge obligation holds in every replay
context. -/
def Join (D : MRDTSig)
    [P : ReplayPolicy D.toUpdateSig] : Prop :=
  ∀ C, JoinAt D (P := P) C

theorem Join.at {D : MRDTSig} [P : ReplayPolicy D.toUpdateSig]
    (h : Join D (P := P))
    (C : Sal.MRDTs.Foundation.ReplayContext D.toUpdateSig) :
    JoinAt D (P := P) C := h C

/-- All-context Join supplies Join under any replay-context predicate. -/
theorem Join.toJoinOn {D : MRDTSig} [P : ReplayPolicy D.toUpdateSig]
    (h : Join D (P := P))
    (Good : Sal.MRDTs.Foundation.ReplayContext D.toUpdateSig → Prop) :
    JoinOn D (P := P) Good := fun C _ => h C

theorem joinOn_true_iff (D : MRDTSig) [P : ReplayPolicy D.toUpdateSig] :
    JoinOn D (P := P) (fun _ => True) ↔ Join D (P := P) := by
  constructor
  · intro h C
    exact h C trivial
  · intro h
    exact h.toJoinOn _

/-- Universal merge laws used to construct the canonical-state Join contract.
The equations quantify over all datatype states. -/
structure MergeLaws (D : MRDTSig) [ReplayPolicy D.toUpdateSig] : Prop where
  replay : ReplayLaws D.toUpdateSig
  merge_comm : ∀ l a b : D.State, D.merge l a b = D.merge l b a
  merge_init : ∀ s : D.State, D.merge D.init D.init s = s

/-- Auxiliary law used only to derive `CausalDeltaLaw` when all updates
commute. It is separate from `MergeLaws` because the universal-to-canonical
delta bridge does not consume it. -/
structure CommutingPeelLaw (D : MRDTSig) : Prop where
  commuting_peel :
    ∀ (a : D.State) (e : Op D.AppOp) (π₀ π₂ : List (Op D.AppOp)),
      (∀ x ∈ π₀, D.toUpdateSig.commutes e x) →
      (∀ x ∈ π₂, D.toUpdateSig.commutes e x) →
      D.merge (applySeq D.toUpdateSig D.init π₀) (D.update a e)
          (applySeq D.toUpdateSig D.init π₂)
        = D.update (D.merge (applySeq D.toUpdateSig D.init π₀) a
            (applySeq D.toUpdateSig D.init π₂)) e

/-- **The delta contract**, the ternary replacement for the binary lattice
laws (`BinaryLatticeLawsPlus`). See the file header for the reading of `merge m · c`
as delta application, and for the two classes (group, lattice) that satisfy it
over all states. -/
structure DeltaLaws (D : MRDTSig) : Prop where
  /-- A delta applied to all three components of a merge extracts once; the
  GCA-slot copy cancels the duplicate (the ternary stand-in for
  `merge_idem`). -/
  redistribute :
    ∀ (m x₀ x₁ x₂ c : D.State),
      D.merge (D.merge m x₀ c) (D.merge m x₁ c) (D.merge m x₂ c)
        = D.merge m (D.merge x₀ x₁ x₂) c
  /-- A delta application commutes past an enclosing merge through one branch
  slot. -/
  local_redistribute :
    ∀ (l m x c y : D.State),
      D.merge l (D.merge m x c) y = D.merge m (D.merge l x y) c

/-- **The causal-delta law**: the single contextual per-MRDT
obligation of the causal-delta derivation. For a `loOn(U)`-maximal `e`, with
`A = σ(U∖e)` and `B = σ(↓e∖e)`,

    merge B A (update B e) = update A e.

Unlike the binary `BinaryCausalDeltaLaw` this is an *equation*, not a `⊑`-inequality: the Counter's
degenerate order leaves no antisymmetry to combine two halves. The merge on the left sits
at its honest GCA: the true GCA set of `U∖e` and `↓e` is `(U∖e) ∩ ↓e = ↓e∖{e}`, whose
canonical state is `B`. -/
def CausalDeltaLaw (D : MRDTSig) [ReplayPolicy D.toUpdateSig] : Prop :=
  ∀ (C : Sal.MRDTs.Foundation.ReplayContext D.toUpdateSig) (U : Set (Op D.AppOp))
    (A B : D.State) (e : Op D.AppOp),
    (∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c) →
    (∀ a : Op D.AppOp, ¬ C.vis a a) →
    (∀ a ∈ U, a ∈ C.events) →
    (∀ a b, C.vis a b → ¬ D.toUpdateSig.commutes a b → b ∈ U → a ∈ U) →
    e ∈ U →
    (∀ x ∈ U, x ≠ e → ¬ loOn C U e x) →
    IsCanonicalState C (U \ {e}) A →
    IsCanonicalState C (downset C e \ {e}) B →
    D.merge B A (D.update B e) = D.update A e

/-- The common core consumed by the feasible-state derivation: update-layer
laws plus commutativity of `merge` in its branch arguments. -/
structure JoinCoreLaws (D : MRDTSig) [ReplayPolicy D.toUpdateSig] : Prop where
  replay : ReplayLaws D.toUpdateSig
  merge_comm : ∀ l a b : D.State, D.merge l a b = D.merge l b a

/-- The slim core from the full ternary bundle. -/
theorem MergeLaws.toJoinCore (hVC : MergeLaws D) : JoinCoreLaws D :=
  ⟨hVC.replay, hVC.merge_comm⟩

/-! ### 1. The feasible-tuple contract -/

/-- **The feasible delta contract**: the redistribution laws (plus the unit law) restricted
to canonical tuples at honest GCAs of a configuration. Field by field:

* `init`: `merge σ₀ σ₀ s = s` for `s` canonical (the raw law is
  false for `EWFlag`: an infeasible state with a set flag but zero counter);
* `local_redistribute`: the `local_redistribute` instance the
  induction consumes in the local-peel case: `s₀ = σ(E₁∩E₂)`, `B = σ(↓e∖e)`,
  `t₁ = σ(E₁∖e)`, `s₂ = σ(E₂)`, `e` union-maximal and local to side 1. Every
  `merge` node of both sides is at its honest GCA: LHS-inner `(E₁∖e) ⊔ ↓e`
  at `↓e∖{e}`, LHS-outer `E₁ ⊔ E₂` at `E₁∩E₂`, RHS-inner `(E₁∖e) ⊔ E₂` at
  `(E₁∖e)∩E₂ = E₁∩E₂`, RHS-outer `(U∖e) ⊔ ↓e` at `↓e∖{e}`;
* `redistribute`: the shared-peel instance, all three components
  decomposed through the downset delta; honest GCAs throughout
  (`t₀ = σ((E₁∩E₂)∖e)` is the decomposed GCA component). -/
structure FeasibleDeltaLaws (D : MRDTSig) [ReplayPolicy D.toUpdateSig] : Prop where
  init :
    ∀ (C : Sal.MRDTs.Foundation.ReplayContext D.toUpdateSig)
      (ev : Set (Op D.AppOp)) (s : D.State),
      (∀ a ∈ ev, a ∈ C.events) →
      IsCanonicalState C ev s →
      D.merge D.init D.init s = s
  local_redistribute :
    ∀ (C : Sal.MRDTs.Foundation.ReplayContext D.toUpdateSig)
      (ev₁ ev₂ : Set (Op D.AppOp)) (s₀ B t₁ s₂ : D.State) (e : Op D.AppOp),
      (∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c) →
      (∀ a : Op D.AppOp, ¬ C.vis a a) →
      (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
      (∀ a b, C.vis a b → ¬ D.toUpdateSig.commutes a b → b ∈ ev₁ → a ∈ ev₁) →
      (∀ a b, C.vis a b → ¬ D.toUpdateSig.commutes a b → b ∈ ev₂ → a ∈ ev₂) →
      e ∈ ev₁ → e ∉ ev₂ →
      (∀ x ∈ ev₁ ∪ ev₂, x ≠ e → ¬ loOn C (ev₁ ∪ ev₂) e x) →
      IsCanonicalState C (ev₁ ∩ ev₂) s₀ →
      IsCanonicalState C (downset C e \ {e}) B →
      IsCanonicalState C (ev₁ \ {e}) t₁ →
      IsCanonicalState C ev₂ s₂ →
      D.merge s₀ (D.merge B t₁ (D.update B e)) s₂
        = D.merge B (D.merge s₀ t₁ s₂) (D.update B e)
  redistribute :
    ∀ (C : Sal.MRDTs.Foundation.ReplayContext D.toUpdateSig)
      (ev₁ ev₂ : Set (Op D.AppOp)) (t₀ t₁ t₂ B : D.State) (e : Op D.AppOp),
      (∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c) →
      (∀ a : Op D.AppOp, ¬ C.vis a a) →
      (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
      (∀ a b, C.vis a b → ¬ D.toUpdateSig.commutes a b → b ∈ ev₁ → a ∈ ev₁) →
      (∀ a b, C.vis a b → ¬ D.toUpdateSig.commutes a b → b ∈ ev₂ → a ∈ ev₂) →
      e ∈ ev₁ → e ∈ ev₂ →
      (∀ x ∈ ev₁ ∪ ev₂, x ≠ e → ¬ loOn C (ev₁ ∪ ev₂) e x) →
      IsCanonicalState C ((ev₁ ∩ ev₂) \ {e}) t₀ →
      IsCanonicalState C (downset C e \ {e}) B →
      IsCanonicalState C (ev₁ \ {e}) t₁ →
      IsCanonicalState C (ev₂ \ {e}) t₂ →
      D.merge (D.merge B t₀ (D.update B e)) (D.merge B t₁ (D.update B e))
          (D.merge B t₂ (D.update B e))
        = D.merge B (D.merge t₀ t₁ t₂) (D.update B e)

/-- The single instance-facing law bundle for the reusable canonical-state
Join induction. Datatypes may prove these laws natively or obtain them from
stronger arbitrary-state equations. -/
structure CanonicalJoinLaws (D : MRDTSig) [ReplayPolicy D.toUpdateSig] : Prop where
  core : JoinCoreLaws D
  delta : FeasibleDeltaLaws D
  causal_delta : CausalDeltaLaw D

/-- The ternary Join Lemma under **full causal closure** of the sides, what
`CanonicalConfig.version_events_causal` supplies. Counter-comparison merges need it: the weak
(`¬commutes`) closure is defeated by commuting same-replica enables. -/
def CausalJoin (D : MRDTSig)
    [P : ReplayPolicy D.toUpdateSig] : Prop :=
  ∀ (C : Sal.MRDTs.Foundation.ReplayContext D.toUpdateSig)
    (ev₁ ev₂ : Set (Op D.AppOp)) (s₀ s₁ s₂ : D.State),
    (∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c) →
    (∀ a : Op D.AppOp, ¬ C.vis a a) →
    (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
    (∀ a b, C.vis a b → b ∈ ev₁ → a ∈ ev₁) →
    (∀ a b, C.vis a b → b ∈ ev₂ → a ∈ ev₂) →
    @IsCanonicalState _ P C (ev₁ ∩ ev₂) s₀ →
    @IsCanonicalState _ P C ev₁ s₁ → @IsCanonicalState _ P C ev₂ s₂ →
    @IsCanonicalState _ P C (ev₁ ∪ ev₂) (D.merge s₀ s₁ s₂)

/-! ### The rc-free `loOn` collapse -/

/-- When `rc` is everywhere `Either`, `loOn` is empty. Visibility contributes
an edge only for a pair that `rc` classifies as conflicting. -/
theorem loOn_iff_of_rc_either {D' : UpdateSig}
    (hrc : ∀ o₁ o₂ : Op D'.AppOp, D'.replayOrder o₁ o₂ = RcRes.Either)
    (C : Sal.MRDTs.Foundation.ReplayContext D') (ev : Set (Op D'.AppOp))
    (e₁ e₂ : Op D'.AppOp) :
    loOn C ev e₁ e₂ ↔ False := by
  unfold loOn
  constructor
  · rintro (⟨_, hrc'⟩ | ⟨_, _, hfs, _⟩)
    · rcases hrc' with hfs | hfs
      · change D'.replayOrder e₁ e₂ = RcRes.Fst_then_snd at hfs
        rw [hrc e₁ e₂] at hfs
        exact RcRes.noConfusion hfs
      · change D'.replayOrder e₂ e₁ = RcRes.Fst_then_snd at hfs
        rw [hrc e₂ e₁] at hfs
        exact RcRes.noConfusion hfs
    · change D'.replayOrder e₁ e₂ = RcRes.Fst_then_snd at hfs
      rw [hrc e₁ e₂] at hfs
      exact RcRes.noConfusion hfs
  · exact False.elim

/-- With `rc` everywhere `Either`, `respects · (loOn C ev)` is independent of
`ev`. -/
theorem respects_transfer_of_rc_either {D' : UpdateSig}
    (hrc : ∀ o₁ o₂ : Op D'.AppOp, D'.replayOrder o₁ o₂ = RcRes.Either)
    {C : Sal.MRDTs.Foundation.ReplayContext D'} {ev ev' : Set (Op D'.AppOp)}
    {ρ : List (Op D'.AppOp)}
    (h : respects ρ (loOn C ev)) : respects ρ (loOn C ev') := by
  unfold respects at h ⊢
  exact h.imp fun {a b} _ hab =>
    ((loOn_iff_of_rc_either hrc C ev' b a).mp hab).elim

end

end Sal.MRDTs
