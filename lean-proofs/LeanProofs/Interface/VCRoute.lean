import LeanProofs1.Interface.Laws
import Artifact.MRDTs.Framework.MergeLaws
import Artifact.MRDTs.Paper1.ConcreteReplay

/-!
# The canonical join laws, and the obligation bundle

The five verification conditions of Section 5, which every row discharges.
There is no other way to a join lemma here: nothing supplies one of its own
to `Soundness/`.

The file has two halves, and they are two *readings* of one route, not two
routes.

* **Part I** states VC1 to VC5 at `IsCanOn`, canonicity measured against the
  framework's `EventOrder`, which is built from `rc`. This is the form both
  rows prove, because it is the form the framework's canonical machinery is
  phrased in.
* **Part II** states the same five at `IsPaperCan`, canonicity measured
  against the relation Section 4 displays, which reads `~(e1 <-> e2)`
  directly. This is the form the metatheory consumes, and it is where
  `ExecutionOrder` and the obligation bundle live.

`CanonicalJoinLawsOn.toPaperOn` carries a row's proofs from the first
reading to the second. It is sound exactly when `rc` relates every
non-commuting pair, which both rows here establish and which
`Obligations.ofUniform` asks of them.

## These are the paper's conditions, as the paper states them

VC1 is over arbitrary states, as `proof_strategy.tex` has it, and the paper
notes it is the only one that is. VC2 to VC5 carry the paper's premises:
`Admissible`, `Maximal`, and the equalities pinning each state to the
canonical state of a particular event set. Nothing here is a universal
strengthening of a canonical statement.

The paper's notation maps onto the fields as follows.

* `can_C(E) = s` is `IsCanOn D C E s`.
* `Admissible_C(E)` is the pair of conditions that `E` lies in `C.events`
  and is weakly closed under `vis` at non-commuting pairs, which is
  `SupportedOn` and `WeaklyClosed`.
* `Maximal^C_{E}(e)` is `MaximalOn D C E e`: no other event of `E` is above
  `e` in `lo^C_E`.
* `downset C e \ {e}` is the paper's `(down e) \ {e}`, and `e(m)` is
  `D.do_ m e`.

## What is not here

`commuting_peel` used to be a sixth field. It is not one of the paper's
conditions, so it is gone: every row now proves VC4 in the form Section 5
states it. A row whose events all commute reaches it through
`downset_diff_self_of_commuting` below, which supplies the one context fact
such a row needs. The conditions in this file are exactly VC1 to VC5, under
each of the two readings.
-/

namespace LeanProofs1.Interface

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1

variable {type : MRDTType} (D : Impl type)

/-! # Part I. The five conditions at the framework's `EventOrder` -/

/-! ## The paper's side conditions, named -/

/-- A replay context of `D`, which is what the paper's `C` contributes to
the verification conditions. -/
abbrev Ctx (D : Impl type) : Type :=
  ReplayContext D.toMRDTSig.toUpdateSig

/-- `can_C(E) = s`. -/
abbrev IsCanOn (C : Ctx D) (E : Set D.Event) (s : D.Sigma) : Prop :=
  @IsCanonicalState D.toMRDTSig.toUpdateSig (rcOrder D) C E s

/-- Half of `Admissible_C(E)`: every event of `E` is observed in `C`. -/
abbrev SupportedOn (C : Ctx D) (E : Set D.Event) : Prop :=
  ∀ a ∈ E, a ∈ C.events

/-- The other half of `Admissible_C(E)`: `E` is closed under `vis`
predecessors that do not commute. This is the paper's `WeakClosed_C(E)`. -/
abbrev WeaklyClosed (C : Ctx D) (E : Set D.Event) : Prop :=
  ∀ a b, C.vis a b → ¬ D.Commutes a b → b ∈ E → a ∈ E

/-- `Maximal^C_E(e)`: no other event of `E` sits above `e` in `lo^C_E`. -/
abbrev MaximalOn (C : Ctx D) (E : Set D.Event) (e : D.Event) : Prop :=
  ∀ x ∈ E, x ≠ e → ¬ @loOn D.toMRDTSig.toUpdateSig (rcOrder D) C E e x

/-- `vis` is a strict partial order, which the paper assumes of every
configuration. -/
abbrev VisStrict (C : Ctx D) : Prop :=
  (∀ {a b c : D.Event}, C.vis a b → C.vis b c → C.vis a c) ∧
    (∀ a : D.Event, ¬ C.vis a a)

/-- The union of two weakly closed sets is weakly closed. -/
theorem weaklyClosed_union {D : Impl type} {C : Ctx D} {E₁ E₂ : Set D.Event}
    (c₁ : WeaklyClosed D C E₁) (c₂ : WeaklyClosed D C E₂) :
    WeaklyClosed D C (E₁ ∪ E₂) := by
  rintro a b hv hnc (hb | hb)
  · exact Or.inl (c₁ a b hv hnc hb)
  · exact Or.inr (c₂ a b hv hnc hb)

/-- **A commuting row's downsets are singletons.** `lo^C_E` consults `rc`
and non-commutation, and a row where every pair of events commutes supplies
neither, so `down(e)` is `{e}` and `down(e) \ {e}` is empty.

This is the one context fact VC4 needs from such a row. Isolating it here
lets the row state VC4 the way Section 5 states it, premises and all, and
still discharge it in two steps: rewrite `B` to `sigma0`, then close by the
row's own merge identity. -/
theorem downset_diff_self_of_commuting {D : Impl type}
    (hcomm : ∀ e₁ e₂ : D.Event, D.Commutes e₁ e₂) (C : Ctx D) (e : D.Event) :
    downset C e \ {e} = (∅ : Set D.Event) := by
  ext x
  simp only [Set.mem_diff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
    iff_false, not_and]
  rintro (hx | hx)
  · exact fun hne => hne hx
  · intro _
    exfalso
    cases hx with
    | single h' => exact h'.2 (hcomm _ _)
    | tail _ h' => exact h'.2 (hcomm _ _)

/-! ## VC1 to VC5 -/

/-- **VC1 to VC5 at the contexts `Good` admits.** The five conditions of
Section 5, each one that mentions a context asking it of `Good` contexts
only. A row with no issuance guard instantiates `Good` at `fun _ => True`
and the hypothesis costs it an underscore. -/
structure CanonicalJoinLawsOn (Good : Ctx D → Prop) : Prop where
  /-- **VC1** MERGE-COMM. No context appears, so no side condition does. -/
  vc1_merge_comm : ∀ l a b : D.Sigma, D.merge l a b = D.merge l b a
  /-- **VC2** MERGE-INIT. -/
  vc2_merge_init : ∀ (C : Ctx D) (E : Set D.Event) (s : D.Sigma),
    Good C → SupportedOn D C E → IsCanOn D C E s →
    D.merge D.sigma0 D.sigma0 s = s
  /-- **VC3** LOCAL-REDISTRIBUTE. -/
  vc3_local_redistribute : ∀ (C : Ctx D) (E₁ E₂ : Set D.Event)
    (l m x y : D.Sigma) (e : D.Event),
    Good C → VisStrict D C →
    SupportedOn D C E₁ → SupportedOn D C E₂ →
    WeaklyClosed D C E₁ → WeaklyClosed D C E₂ →
    e ∈ E₁ → e ∉ E₂ → MaximalOn D C (E₁ ∪ E₂) e →
    IsCanOn D C (E₁ ∩ E₂) l →
    IsCanOn D C (downset C e \ {e}) m →
    IsCanOn D C (E₁ \ {e}) x →
    IsCanOn D C E₂ y →
    D.merge l (D.merge m x (D.do_ m e)) y
      = D.merge m (D.merge l x y) (D.do_ m e)
  /-- **VC4** CAUSAL-DELTA, written out rather than taken from the framework,
  since the framework's `CausalDeltaLaw` admits every context. -/
  vc4_causal_delta : ∀ (C : Ctx D) (U : Set D.Event) (A B : D.Sigma)
    (e : D.Event),
    Good C → VisStrict D C →
    SupportedOn D C U → WeaklyClosed D C U →
    e ∈ U → MaximalOn D C U e →
    IsCanOn D C (U \ {e}) A →
    IsCanOn D C (downset C e \ {e}) B →
    D.merge B A (D.do_ B e) = D.do_ A e
  /-- **VC5** REDISTRIBUTE. -/
  vc5_redistribute : ∀ (C : Ctx D) (E₁ E₂ : Set D.Event)
    (x₀ x₁ x₂ m : D.Sigma) (e : D.Event),
    Good C → VisStrict D C →
    SupportedOn D C E₁ → SupportedOn D C E₂ →
    WeaklyClosed D C E₁ → WeaklyClosed D C E₂ →
    e ∈ E₁ → e ∈ E₂ → MaximalOn D C (E₁ ∪ E₂) e →
    IsCanOn D C ((E₁ ∩ E₂) \ {e}) x₀ →
    IsCanOn D C (downset C e \ {e}) m →
    IsCanOn D C (E₁ \ {e}) x₁ →
    IsCanOn D C (E₂ \ {e}) x₂ →
    D.merge (D.merge m x₀ (D.do_ m e)) (D.merge m x₁ (D.do_ m e))
        (D.merge m x₂ (D.do_ m e))
      = D.merge m (D.merge x₀ x₁ x₂) (D.do_ m e)

/-! # Part II. The same five conditions, stated at `lo^C_E` itself

Part I above states VC1 to VC5 at `IsCanOn`, the canonical state of the
framework's `EventOrder`, which is built from `rc`. Section 4 does
not display that relation. It displays `lo^C_E`, which reads
`~(e1 <-> e2)` directly, and the conditions below are VC1 to VC5 again with
`can^C(E)` and `Maximal^C_E(e)` read off it.

The two readings agree exactly when `rc` relates **every** non-commuting
pair, which is `loOn_iff_paperOrder`. Both rows here satisfy that, so each
discharges the conditions at `IsCanOn`, where they are easier to reason
about, and `CanonicalJoinLawsOn.toPaperOn` carries them across. The
displayed reading is still the one the metatheory consumes, because it is
the only one that stays true for a row whose RC-NON-COMM is guarded: two
`add x` events of one replica do not commute and carry one operation, so no
`rc` relates them, yet a replica's own events are causally ordered and
`lo^C_E` never consults `rc` about them.

The paper's notation maps onto the fields as follows.

* `can_C(E) = s` is `IsPaperCan D C E s`.
* `Admissible_C(E)` is `SupportedOn` and `WeaklyClosed`, as before.
* `Maximal^C_E(e)` is `PaperMaximalOn D C E e`.
* `downset C e \ {e}` and `e(m)` are unchanged.
-/

/-! ## `lo^C_E` as Section 4 displays it -/

/-- `can_C(E) = s`, at the relation Section 4 displays: a linear extension
of `lo^C_E` folded from `sigma0`, with `lo^C_E` reading `~(e1 <-> e2)`
rather than `rc`. -/
abbrev IsPaperCan (C : Ctx D) (E : Set D.Event) (s : D.Sigma) : Prop :=
  ConcreteMRDT.Canonical (policy D) C E s

/-- `Maximal^C_E(e)`: no other event of `E` sits above `e` in `lo^C_E`. -/
abbrev PaperMaximalOn (C : Ctx D) (E : Set D.Event) (e : D.Event) : Prop :=
  ∀ x ∈ E, x ≠ e → ¬ paperOrder (policy D) C E e x

/-! ## Working with `lo^C_E`

Four facts about the displayed relation, none of them about a datatype.
They are its counterparts of `downset_max`, `closure_diff_of_max` and
`isCanonicalState_snoc`, which a row on the route of `VCRoute.lean` takes
from the framework. -/

/-- `lo^C_E` grows as `E` shrinks: the absorber clause quantifies over `E`,
so a smaller `E` offers fewer absorbers and keeps more edges. -/
theorem paperOrder_shrink {D : Impl type} {C : Ctx D} {E U : Set D.Event}
    (sub : E ⊆ U) {a b : D.Event} (h : paperOrder (policy D) C U a b) :
    paperOrder (policy D) C E a b := by
  rcases h with h | ⟨hab, hba, pol, free⟩
  · exact Or.inl h
  · exact Or.inr ⟨hab, hba, pol, fun ⟨c, hc, hv, hnc⟩ => free ⟨c, sub hc, hv, hnc⟩⟩

/-- **A maximal event extends a canonical replay.** If `A` is the canonical
state of `E \ {e}` and `e` is maximal in `E`, then `e(A)` is the canonical
state of `E`. -/
theorem isPaperCan_snoc {D : Impl type} {C : Ctx D} {E : Set D.Event}
    {A : D.Sigma} {e : D.Event} (he : e ∈ E) (hmax : PaperMaximalOn D C E e)
    (hA : IsPaperCan D C (E \ {e}) A) : IsPaperCan D C E (D.do_ A e) := by
  obtain ⟨π, hp, hr, hf⟩ := hA
  refine ⟨π ++ ([e] : List (Op D.toMRDTSig.AppOp)), ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨hp.1, by simp, ?_⟩
    intro x hx y hy hxy
    have hye : y = e := by simpa using hy
    subst y; subst x
    exact ((hp.2 e).mp hx).2 rfl
  · intro x
    simp only [List.mem_append, List.mem_singleton, hp.2 x, Set.mem_diff,
      Set.mem_singleton_iff]
    constructor
    · rintro (⟨hx, -⟩ | rfl) <;> [exact hx; exact he]
    · intro hx
      by_cases hxe : x = e
      · exact Or.inr hxe
      · exact Or.inl ⟨hx, hxe⟩
  · change (π ++ ([e] : List (Op D.toMRDTSig.AppOp))).Pairwise _
    rw [List.pairwise_append]
    refine ⟨hr.imp (fun {_ _} hno hedge => hno (paperOrder_shrink Set.diff_subset hedge)),
      by simp, ?_⟩
    intro x hx y hy
    have hye : y = e := by simpa using hy
    subst y
    exact hmax x ((hp.2 x).mp hx).1 ((hp.2 x).mp hx).2
  · rw [applySeq_append_single, hf]
    rfl

/-! ## VC1 to VC5 -/

/-- **`e` is maximal in its own downset.** Anything else in the downset is
strictly below `e` under `vis`, and `lo^C_E` never points back up. -/
theorem paperMaximalOn_downset {D : Impl type} {C : Ctx D}
    (hvs : VisStrict D C) (e : D.Event) : PaperMaximalOn D C (downset C e) e := by
  obtain ⟨htr, hirr⟩ := hvs
  intro x hx hne
  have hv : C.vis x e := downset_vis (fun {_ _ _} hab hbc => htr hab hbc) hx hne
  rintro (⟨hve, -⟩ | ⟨-, hvx, -, -⟩)
  · exact hirr e (htr hve hv)
  · exact hvx hv

/-- **Removing a maximal event keeps weak closure.** The only edge that could
leave `S \ {e}` unclosed would point into `e`, and `e` is maximal. -/
theorem weaklyClosed_diff_of_max {D : Impl type} {C : Ctx D} {S T : Set D.Event}
    (hcl : WeaklyClosed D C S) (hsub : S ⊆ T) {e : D.Event}
    (hmax : PaperMaximalOn D C T e) : WeaklyClosed D C (S \ {e}) := by
  rintro a b hv hnc ⟨hbS, hbe⟩
  refine ⟨hcl a b hv hnc hbS, ?_⟩
  intro ha
  have hae : a = e := ha
  subst hae
  exact hmax b (hsub hbS) hbe (Or.inl ⟨hv, hnc⟩)

/-- **The canonical join laws at `lo^C_E` itself, at the contexts `Good`
admits.** `Good = fun _ => True` is how both rows here use it; a row whose
join lemma depends on an issuance guard states its conditions at the
contexts that guard admits instead. Field for field the
conditions of `CanonicalJoinLawsOn`, with `IsCanOn` replaced by `IsPaperCan`
and `MaximalOn` by `PaperMaximalOn`. Nothing else differs, and for a row
whose RC-NON-COMM holds unguarded nothing differs at all. -/
structure PaperJoinLawsOn (Good : Ctx D → Prop) : Prop where
  /-- **VC1** MERGE-COMM, over arbitrary states. -/
  vc1_merge_comm : ∀ l a b : D.Sigma, D.merge l a b = D.merge l b a
  /-- **VC2** MERGE-INIT. -/
  vc2_merge_init : ∀ (C : Ctx D) (E : Set D.Event) (s : D.Sigma),
    Good C → SupportedOn D C E → IsPaperCan D C E s →
    D.merge D.sigma0 D.sigma0 s = s
  /-- **VC3** LOCAL-REDISTRIBUTE, for a maximal `e` in `E1` only. -/
  vc3_local_redistribute : ∀ (C : Ctx D) (E₁ E₂ : Set D.Event)
    (l m x y : D.Sigma) (e : D.Event),
    Good C → VisStrict D C →
    SupportedOn D C E₁ → SupportedOn D C E₂ →
    WeaklyClosed D C E₁ → WeaklyClosed D C E₂ →
    e ∈ E₁ → e ∉ E₂ → PaperMaximalOn D C (E₁ ∪ E₂) e →
    IsPaperCan D C (E₁ ∩ E₂) l →
    IsPaperCan D C (downset C e \ {e}) m →
    IsPaperCan D C (E₁ \ {e}) x →
    IsPaperCan D C E₂ y →
    D.merge l (D.merge m x (D.do_ m e)) y
      = D.merge m (D.merge l x y) (D.do_ m e)
  /-- **VC4** CAUSAL-DELTA, for a maximal `e` of `E`. -/
  vc4_causal_delta : ∀ (C : Ctx D) (U : Set D.Event) (A B : D.Sigma)
    (e : D.Event),
    Good C → VisStrict D C →
    SupportedOn D C U → WeaklyClosed D C U →
    e ∈ U → PaperMaximalOn D C U e →
    IsPaperCan D C (U \ {e}) A →
    IsPaperCan D C (downset C e \ {e}) B →
    D.merge B A (D.do_ B e) = D.do_ A e
  /-- **VC5** REDISTRIBUTE, for a maximal `e` in both branches. -/
  vc5_redistribute : ∀ (C : Ctx D) (E₁ E₂ : Set D.Event)
    (x₀ x₁ x₂ m : D.Sigma) (e : D.Event),
    Good C → VisStrict D C →
    SupportedOn D C E₁ → SupportedOn D C E₂ →
    WeaklyClosed D C E₁ → WeaklyClosed D C E₂ →
    e ∈ E₁ → e ∈ E₂ → PaperMaximalOn D C (E₁ ∪ E₂) e →
    IsPaperCan D C ((E₁ ∩ E₂) \ {e}) x₀ →
    IsPaperCan D C (downset C e \ {e}) m →
    IsPaperCan D C (E₁ \ {e}) x₁ →
    IsPaperCan D C (E₂ \ {e}) x₂ →
    D.merge (D.merge m x₀ (D.do_ m e)) (D.merge m x₁ (D.do_ m e))
        (D.merge m x₂ (D.do_ m e))
      = D.merge m (D.merge x₀ x₁ x₂) (D.do_ m e)

/-! ## The join lemma -/

/-- **VC1 to VC5 at `lo^C_E`**, at every context. -/
abbrev PaperJoinLaws (D : Impl type) : Prop := PaperJoinLawsOn D (fun _ => True)

/-- **Lemma (Join)**, read at `lo^C_E`. For admissible `E1` and `E2`,
merging `can(E1 n E2)`, `can(E1)` and `can(E2)` gives `can(E1 u E2)`.

This is the framework's `Join` with canonicity read at the displayed
relation instead of at `rc`. The framework's own `Join` cannot serve: it is
stated through `IsCanonicalState`, which is indexed by an `EventOrder`, and
for a row on this route no `EventOrder` built from `rc` describes `lo^C_E`.
The premises are the ones `Join` carries, written out. -/
def PaperJoinOn (D : Impl type) (Good : Ctx D → Prop) : Prop :=
  ∀ (C : Ctx D) (E₁ E₂ : Set D.Event) (l a b : D.Sigma),
    Good C → VisStrict D C →
    SupportedOn D C E₁ → SupportedOn D C E₂ →
    (∀ e f : D.Event, C.vis e f → f ∈ E₁ → e ∈ E₁) →
    (∀ e f : D.Event, C.vis e f → f ∈ E₂ → e ∈ E₂) →
    IsPaperCan D C (E₁ ∩ E₂) l → IsPaperCan D C E₁ a → IsPaperCan D C E₂ b →
    IsPaperCan D C (E₁ ∪ E₂) (D.merge l a b)

/-- **An execution order for `D`.** A proof device, not a second `rc`. -/
structure ExecutionOrder (D : Impl type) where
  /-- The order itself. -/
  order : EventOrder D.toMRDTSig.toUpdateSig
  /-- It relates exactly the non-commuting pairs of observed events. This is
  RC-NON-COMM with no guard at all, which is why `rc` cannot serve. -/
  exact : ∀ (C : Ctx D) (a b : D.Event), a ∈ C.events → b ∈ C.events →
    (¬ D.Commutes a b ↔ order.Before a b ∨ order.Before b a)
  /-- On the pairs `lo^C_E` consults an order about, which are the
  concurrent ones, it agrees with `rc`. -/
  concurrent : ∀ (C : Ctx D) (a b : D.Event), a ∈ C.events → b ∈ C.events →
    ¬ C.vis a b → ¬ C.vis b a → (order.Before a b ↔ D.EventRcBefore a b)

/-- The two canonicity predicates agree when `rc` relates every
non-commuting pair. -/
theorem isPaperCan_iff_isCanOn {D : Impl type}
    (hres : RestrictedLaws D.toMRDTSig.toUpdateSig (policy D))
    (C : Ctx D) (E : Set D.Event) (s : D.Sigma) :
    IsPaperCan D C E s ↔ IsCanOn D C E s := by
  letI : EventOrder D.toMRDTSig.toUpdateSig := rcOrder D
  constructor
  · rintro ⟨π, hp, hr, hf⟩
    exact ⟨π, hp, hr.imp (fun {_ _} hno h =>
      hno ((paperOrder_iff_loOn hres C E _ _).mpr h)), hf⟩
  · rintro ⟨π, hp, hr, hf⟩
    exact ⟨π, hp, hr.imp (fun {_ _} hno h =>
      hno ((paperOrder_iff_loOn hres C E _ _).mp h)), hf⟩

/-- So do the two maximality predicates. -/
theorem paperMaximalOn_iff_maximalOn {D : Impl type}
    (hres : RestrictedLaws D.toMRDTSig.toUpdateSig (policy D))
    (C : Ctx D) (E : Set D.Event) (e : D.Event) :
    PaperMaximalOn D C E e ↔ MaximalOn D C E e := by
  letI : EventOrder D.toMRDTSig.toUpdateSig := rcOrder D
  constructor
  · exact fun h x hx hne hlo => h x hx hne ((paperOrder_iff_loOn hres C E e x).mpr hlo)
  · exact fun h x hx hne hpo => h x hx hne ((paperOrder_iff_loOn hres C E e x).mp hpo)

/-- **The five conditions, reread at `lo^C_E`.** Nothing is reproved: each
field is the row's own, with its canonicity and maximality hypotheses
carried across. -/
theorem CanonicalJoinLawsOn.toPaperOn {D : Impl type} {Good : Ctx D → Prop}
    (h : Laws D) (hru : UniformRcNonComm D) (hcc : UniformCondComm D)
    (vcs : CanonicalJoinLawsOn D Good) : PaperJoinLawsOn D Good := by
  letI : EventOrder D.toMRDTSig.toUpdateSig := rcOrder D
  have hres := h.toRestricted hru hcc
  have hcan := isPaperCan_iff_isCanOn hres
  have hmax := paperMaximalOn_iff_maximalOn hres
  refine ⟨vcs.vc1_merge_comm, ?_, ?_, ?_, ?_⟩
  · exact fun C E s hg hsup hs => vcs.vc2_merge_init C E s hg hsup ((hcan C E s).mp hs)
  · exact fun C E₁ E₂ l m x y e hg hvs h₁ h₂ hc₁ hc₂ he₁ he₂ hm hl hmm hx hy =>
      vcs.vc3_local_redistribute C E₁ E₂ l m x y e hg hvs h₁ h₂ hc₁ hc₂ he₁ he₂
        ((hmax C (E₁ ∪ E₂) e).mp hm) ((hcan C _ l).mp hl) ((hcan C _ m).mp hmm)
        ((hcan C _ x).mp hx) ((hcan C E₂ y).mp hy)
  · exact fun C U A B e hg hvs hsup hcl heU hm hA hB =>
      vcs.vc4_causal_delta C U A B e hg hvs hsup hcl heU
        ((hmax C U e).mp hm) ((hcan C _ A).mp hA) ((hcan C _ B).mp hB)
  · exact fun C E₁ E₂ x₀ x₁ x₂ m e hg hvs h₁ h₂ hc₁ hc₂ he₁ he₂ hm h0 hmm h1 h2 =>
      vcs.vc5_redistribute C E₁ E₂ x₀ x₁ x₂ m e hg hvs h₁ h₂ hc₁ hc₂ he₁ he₂
        ((hmax C (E₁ ∪ E₂) e).mp hm) ((hcan C _ x₀).mp h0) ((hcan C _ m).mp hmm)
        ((hcan C _ x₁).mp h1) ((hcan C _ x₂).mp h2)

/-- **A row whose RC-NON-COMM holds unguarded uses `rc` itself.** Its two
conditions are then the unguarded law and a definitional unfolding. -/
noncomputable def ExecutionOrder.ofUniform {D : Impl type}
    (hru : UniformRcNonComm D) : ExecutionOrder D where
  order := rcOrder D
  exact := fun _ a b _ _ => by
    have hb : ∀ x y : D.Event, (rcOrder D).Before x y ↔ D.EventRcBefore x y :=
      fun x y => @OperationPolicy.lift_replayOrder_iff
        D.toMRDTSig.toUpdateSig (policy D) x y
    rw [hb, hb]
    exact hru a b
  concurrent := fun _ a b _ _ _ _ =>
    @OperationPolicy.lift_replayOrder_iff D.toMRDTSig.toUpdateSig (policy D) a b

/-! ## The bundle -/

/-- **The obligation bundle**, for any implementation.

Two fields are the paper's: `Laws(D_type)` and the five conditions of
Section 5, read at `lo^C_E`. The other three are what the framework's
guarded contract asks for beyond them, and each is a single case the paper's
guards exclude rather than a restated law.

Nothing here asks the events to commute, and nothing asks for an unguarded
RC-NON-COMM. `ofUniform` below builds the whole bundle for a row whose
RC-NON-COMM does hold unguarded, so such a row proves exactly what it
proved before. -/
structure ObligationsOn (Good : Ctx D → Prop) : Prop where
  /-- `Laws(D_type)`: RC-NON-COMM, NO-RC-CHAIN and COND-COMM. -/
  laws : Laws D
  /-- The case RC-NON-COMM's `o1 /= o2` conjunct excludes. -/
  equal_op_commutes : EqualOpCommutes D
  /-- The case COND-COMM's replica guard excludes. -/
  same_rep_cond_comm : SameReplicaCondComm D
  /-- VC1 to VC5 of Section 5, at `lo^C_E`. -/
  joinLaws : PaperJoinLawsOn D Good
  /-- The order the execution induction is indexed by. -/
  executionOrder : Nonempty (ExecutionOrder D)

/-- **The obligation bundle**, at every context. -/
abbrev Obligations (D : Impl type) : Prop := ObligationsOn D (fun _ => True)

/-- **The bundle for a row whose RC-NON-COMM holds unguarded.** Both rows
here are such rows, and each supplies `Laws`, the two unguarded readings,
and the five conditions at `IsCanOn`. The three remaining fields follow. -/
theorem ObligationsOn.ofUniform {D : Impl type} {Good : Ctx D → Prop}
    (h : Laws D) (hru : UniformRcNonComm D) (hcc : UniformCondComm D)
    (vcs : CanonicalJoinLawsOn D Good) : ObligationsOn D Good :=
  ⟨h, EqualOpCommutes.of_concurrent h.no_rc_chain hru.toConcurrent,
    hcc.toSameReplica, vcs.toPaperOn h hru hcc,
    ⟨ExecutionOrder.ofUniform hru⟩⟩

/-- The same, for a row whose conditions hold at every context. -/
theorem Obligations.ofUniform {D : Impl type} (h : Laws D)
    (hru : UniformRcNonComm D) (hcc : UniformCondComm D)
    (vcs : CanonicalJoinLawsOn D (fun _ => True)) : Obligations D :=
  ObligationsOn.ofUniform h hru hcc vcs

/-- **`rc` is empty when every pair of events commutes.** An edge would have
to relate two operations, and RC-NON-COMM read right to left at any pair of
events carrying them would then deny that they commute. -/
theorem rc_empty_of_commuting {D : Impl type} (h : Laws D)
    (all_comm : ∀ e₁ e₂ : D.Event, D.Commutes e₁ e₂) (o₁ o₂ : type.OType) :
    ¬ D.RcBefore o₁ o₂ := by
  intro hb
  have hne := (h.rc_non_comm ((0, 0, o₁) : D.Event) ((1, 1, o₂) : D.Event)
    (by simp [Impl.time, Op.time]) (by simp [Impl.rep, Op.rep])).mpr (Or.inl hb)
  exact hne.1 (all_comm _ _)

/-- **The bundle for a row whose events all commute.** `Laws(D_type)` then
forces `rc` to be empty, so the two cases `Laws` leaves open are vacuous and
`rc` itself is an execution order. Such a row supplies the paper's two
obligations and the fact that its operations commute, and nothing else. -/
theorem Obligations.ofCommuting {D : Impl type} (h : Laws D)
    (all_comm : ∀ e₁ e₂ : D.Event, D.Commutes e₁ e₂)
    (vcs : CanonicalJoinLawsOn D (fun _ => True)) : Obligations D := by
  have hempty := rc_empty_of_commuting h all_comm
  refine Obligations.ofUniform h (fun e₁ e₂ => ?_)
    (fun _ e e' _ _ hrc _ => (hempty e.op e'.op hrc).elim) vcs
  exact ⟨fun hn => absurd (all_comm e₁ e₂) hn,
    fun hb => hb.elim (fun x => (hempty _ _ x).elim) (fun x => (hempty _ _ x).elim)⟩

end LeanProofs1.Interface
