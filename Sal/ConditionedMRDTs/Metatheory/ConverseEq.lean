import Sal.ConditionedMRDTs.Metatheory.GenericEqQuotient

/-!
# The conditioned converse of adequacy — the `eqObs`-quotient lift (task #122, phase 2)

The flat converse (`Metatheory/Converse.lean`) settled that a *canonical
RA-linearizable* flat MRDT satisfies the four core VCs on its reachable,
weakly-closed event sets. This file lifts the completeness picture to the
CONDITIONED framework — RA-linearizability read up to the observational
equivalence `eqObs` (`≈`), at every reachable `Inv`-configuration — following the
verdicts settled pen-and-paper + Python in phase 1
(`whiteboard/conditioned-converse-note.md`, harness
`whiteboard/litmus/conditioned_converse_check.py`).

The headline of the note is the *lift* of the flat core/shell split, with one new
phenomenon (antitonicity) made concrete:

* **vc:merge (the conditioned Join) is FORCED** by existence-plus-convergence-up-to
  `≈`, exactly as the flat Join was — `converse_vc_merge` below, on the
  reachable-realizable domain (the one CONJECTURED domain step is an explicit
  hypothesis, per the note, not forced).
* **vc:comm + vc:inv (the swap oracle) are NOT forced.** They are a *sufficient
  device* strictly stronger than the convergence content RA-lin forces. Refuted by
  the RESET witness (`Refutations/EqSwap_Not_Forced.lean`, `eqswap_not_forced`).
* **vc:disc (the Inv discipline) is EXTRA.** Its universal preservation clause is
  `Inv`-dependent: the two-Inv G-set witness (`vc_disc_extra`) is RA-lin under both
  invariants, green under one and red under the other.

This file carries the SHARED definitions consumed by both the positive direction
and the refutations (`EqSwap`, `ConvergesEq`, `EqSwapOracle`, `CanonicalRALin3Eq`),
the positive residue of vc:comm (`sig_peel_maximal_eq` — what convergence *does*
force, the maximal swap packaged as a fold-peel), the vc:merge lift
(`converse_vc_merge`), and the #123 abstract-arbitration experiment
(`loOnArb`, `IsRALinearizable3ArbEq`, `loOnEq_isArb`).
-/

namespace Sal.ConditionedMRDTs
namespace GenericEqQuotient

open Sal.Emulation
open Classical

variable {D : ConditionedMRDTSig}

/-! ## §1. The shared conditioned-converse vocabulary

These four are the `eqObs`-conditioned readings of the notions the flat converse
used over `=`. They are `def`s (not theorems), so this file compiles regardless of
how far the positive direction below closes; the refutations import them. -/

/-- **`EqSwap` (vc:comm, the local swap witness).** The `≈`-relaxed local
commutation `do (do s a) b ≈ do (do s b) a`, at a single enabling state `s`. The
generic form of the RGA's `EqSwap`; the whole conditioned commutation VC is this
witness owed at the reorder states pinned by vc:inv. -/
def EqSwap (E : EqEquiv D) (a b : Op D.AppOp) (s : D.State) : Prop :=
  E.eqv (D.update (D.update s a) b) (D.update (D.update s b) a)

/-- **`ConvergesEq` (the convergence-up-to-`≈` content of conditioned RA-lin).**
On an event set `ev`, all `loOnEq`-respecting raw folds land `≈`-equal, so the
canonical class `σcan≈(ev)` is single-valued up to `≈`. This is the `converges`
half the note determines the faithful conditioned hypothesis to be — the
`eqObs`-lift of `Converse.Converges`, read over `IsCanonicalStateEq`. -/
def ConvergesEq (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (vis : Op D.AppOp → Op D.AppOp → Prop) (ev : Set (Op D.AppOp)) : Prop :=
  ∀ s s' : D.State,
    IsCanonicalStateEq E W vis ev s → IsCanonicalStateEq E W vis ev s' → E.eqv s s'

/-- **`EqSwapOracle` (vc:comm + vc:inv jointly, the swap oracle of `thm:eqconv`).**
For a duplicate-free `loOnEq(ev)`-respecting prefix `π` drawn from `ev` and a pair
`a, b ∈ ev` that is `loOnEq(ev)`-incomparable and both *enabled* at `π` (every
`loOnEq(ev)`-predecessor already in `π`), the oracle supplies `EqSwap(a, b, fold π)`.
This is the exact content of VC~vc:inv (`sal-mrdts.tex`, `sec:cvcs`): the swap is
consulted only at the prefixes a linearization repair visits. RESET reddens it at
`π = []` while converging (`eqswap_not_forced`). -/
def EqSwapOracle (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (vis : Op D.AppOp → Op D.AppOp → Prop) (ev : Set (Op D.AppOp)) : Prop :=
  ∀ (a b : Op D.AppOp) (π : List (Op D.AppOp)),
    a ∈ ev → b ∈ ev → a ≠ b →
    ¬ loOnEq E W vis ev a b → ¬ loOnEq E W vis ev b a →
    π.Nodup → (∀ x ∈ π, x ∈ ev) → respects π (loOnEq E W vis ev) →
    (∀ z ∈ ev, z ≠ a → loOnEq E W vis ev z a → z ∈ π) →
    (∀ z ∈ ev, z ≠ b → loOnEq E W vis ev z b → z ∈ π) →
    EqSwap E a b (applySeq D.toCRDTSig D.init π)

/-- **`Discipline` (the load-bearing clause of vc:disc).** `Inv` holds at `init`
and is preserved by the raw `update` on *applicable* operations. The generation
half of vc:disc is carried by the `ConditionedConfiguration` execution model
(presupposed by the converse statement, per the note), so this is the clause a
datatype's *chosen* `Inv` decides; the two-Inv witness separates it. -/
def Discipline (D : ConditionedMRDTSig) : Prop :=
  D.Inv D.init ∧
    ∀ (s : D.State) (o : Op D.AppOp), D.Inv s → D.applicable o s → D.Inv (D.update s o)

/-! ## §2. Antitonicity of `loOnEq` and `≈`-closure of canonicity (T3 support)

The two structural facts the positive direction rests on, lifted from the flat
`loOn_mono` / the `IsCanonicalState` closure. `loOnEq` has FEWER edges on a larger
set (growing the set only adds absorbers — the rc-arm's `¬∃` clause weakens), and
`IsCanonicalStateEq` is closed under `≈` on its state (existence read up to `≈`). -/

/-- **Antitonicity of `loOnEq`** (the note's central new phenomenon, made concrete):
`loOnEq` is monotone-decreasing in the event set — the exact `eqObs`-lift of the
flat `loOn_mono`. The vis arm is set-free; the rc arm's absorber clause `¬∃ e₃ ∈ ev`
only weakens as `ev` grows. -/
theorem loOnEq_mono {E : EqEquiv D} {W : Op D.AppOp → D.State → Prop}
    {vis : Op D.AppOp → Op D.AppOp → Prop} {ev ev' : Set (Op D.AppOp)}
    (h_sub : ev ⊆ ev') {e₁ e₂ : Op D.AppOp}
    (h : loOnEq E W vis ev' e₁ e₂) : loOnEq E W vis ev e₁ e₂ := by
  rcases h with h | ⟨h₁, h₂, h₃, h₄⟩
  · exact Or.inl h
  · exact Or.inr ⟨h₁, h₂, h₃,
      fun ⟨e₃, he₃, hv, hnc⟩ => h₄ ⟨e₃, h_sub he₃, hv, hnc⟩⟩

/-- **`≈`-closure of canonicity.** If some canonical state `u` of `ev` is `≈` to
`s`, then `s` is also canonical of `ev`. (`IsCanonicalStateEq` reads existence up
to `≈`, so it descends to the whole `≈`-class.) -/
theorem isCanonicalStateEq_congr {E : EqEquiv D} {W : Op D.AppOp → D.State → Prop}
    {vis : Op D.AppOp → Op D.AppOp → Prop} {ev : Set (Op D.AppOp)} {s u : D.State}
    (h : IsCanonicalStateEq E W vis ev u) (heq : E.eqv s u) :
    IsCanonicalStateEq E W vis ev s := by
  obtain ⟨ρ, hp, hr, hf⟩ := h
  exact ⟨ρ, hp, hr, E.equiv.trans hf (E.equiv.symm heq)⟩

/-! ## §3. The fold-peel `sig_peel_maximal_eq` (T3 — the positive residue of vc:comm)

The `eqObs`-lift of `Converse.sig_peel_maximal`. What convergence-up-to-`≈` DOES
force is the *maximal* swap, packaged as `σcan≈(U) ≈ do (σcan≈(U∖e)) e` for a
`loOnEq(U)`-maximal `e`. The one place the `eqObs` relaxation costs more than the
flat proof: appending `e` to the punctured fold needs `update` to respect `≈`
(`CongVC.update_congr`), which needs `Inv` at both folds — supplied here as the
explicit `hInvUe` / `hInvFold` premises (the framework discharges the latter from
`WfOpReachable` along reachable folds; stated explicitly here, as the flat
converse stated `converges`). -/

/-- The `eqObs`-lift of `isCanonicalState_snoc`: append a `loOnEq(U)`-maximal `e`
to a canonical fold of `U∖e`. Uses `loOnEq_mono` (antitonicity) for the respects
transfer and `CongVC.update_congr` for the fold step. -/
theorem isCanonicalStateEq_snoc {E : EqEquiv D} {W : Op D.AppOp → D.State → Prop}
    (hC : CongVC D E) {vis : Op D.AppOp → Op D.AppOp → Prop}
    {U : Set (Op D.AppOp)} {e : Op D.AppOp} {sUe : D.State}
    (h_e_in : e ∈ U)
    (h_max : ∀ x ∈ U, x ≠ e → ¬ loOnEq E W vis U e x)
    (hInvUe : D.Inv sUe)
    (hInvFold : ∀ π : List (Op D.AppOp), listPermOf π (U \ {e}) →
        respects π (loOnEq E W vis (U \ {e})) → D.Inv (applySeq D.toCRDTSig D.init π))
    (h : IsCanonicalStateEq E W vis (U \ {e}) sUe) :
    IsCanonicalStateEq E W vis U (D.update sUe e) := by
  obtain ⟨ρ, hp, hr, hf⟩ := h
  have h_e_notin : e ∉ ρ := fun hmem => ((hp.2 e).mp hmem).2 rfl
  refine ⟨ρ ++ [e], ⟨?_, fun a => ?_⟩, ?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨hp.1, List.nodup_singleton _, ?_⟩
    intro x hx y hy heq
    rw [List.mem_singleton] at hy; subst hy; subst heq
    exact h_e_notin hx
  · rw [List.mem_append, List.mem_singleton]
    constructor
    · rintro (h' | rfl)
      · exact ((hp.2 a).mp h').1
      · exact h_e_in
    · intro ha
      by_cases hae : a = e
      · exact Or.inr hae
      · exact Or.inl ((hp.2 a).mpr ⟨ha, hae⟩)
  · unfold respects
    rw [List.pairwise_append]
    refine ⟨hr.imp (fun hn hlo => hn (loOnEq_mono Set.diff_subset hlo)),
      List.pairwise_singleton _ _, ?_⟩
    intro y hy b hb
    rw [List.mem_singleton] at hb; subst hb
    obtain ⟨hy_ev, hy_ne⟩ := (hp.2 y).mp hy
    exact h_max y hy_ev hy_ne
  · rw [applySeq_append_single]
    exact hC.update_congr e (hInvFold ρ hp hr) hInvUe hf

/-- **`sig_peel_maximal_eq`** — `σcan≈(U) ≈ do (σcan≈(U∖e)) e` for a
`loOnEq(U)`-maximal `e`, from convergence and antitonicity, exactly as
`Converse.sig_peel_maximal`. This is the positive residue of vc:comm: convergence
forces precisely the maximal swap. -/
theorem sig_peel_maximal_eq {E : EqEquiv D} {W : Op D.AppOp → D.State → Prop}
    (hC : CongVC D E) {vis : Op D.AppOp → Op D.AppOp → Prop}
    {U : Set (Op D.AppOp)} {e : Op D.AppOp} {sU sUe : D.State}
    (hconv : ConvergesEq E W vis U)
    (h_e_in : e ∈ U)
    (h_max : ∀ x ∈ U, x ≠ e → ¬ loOnEq E W vis U e x)
    (hInvUe : D.Inv sUe)
    (hInvFold : ∀ π : List (Op D.AppOp), listPermOf π (U \ {e}) →
        respects π (loOnEq E W vis (U \ {e})) → D.Inv (applySeq D.toCRDTSig D.init π))
    (hU : IsCanonicalStateEq E W vis U sU)
    (hUe : IsCanonicalStateEq E W vis (U \ {e}) sUe) :
    E.eqv sU (D.update sUe e) :=
  hconv sU (D.update sUe e) hU
    (isCanonicalStateEq_snoc hC h_e_in h_max hInvUe hInvFold hUe)

/-! ## §4. The conditioned RA-lin hypothesis and the vc:merge lift (T3)

`CanonicalRALin3Eq` is the faithful conditioned converse hypothesis, following the
flat `Converse.CanonicalRALin3` but WITHOUT a Join field: the conditioned framework
takes the Join as a primitive VC, and existence+convergence *derives* it, so
packaging it in would be circular (per the note). The one gap the note flags —
that every abstract `GenDisc` fully-closed `Inv` merge tuple is realized as a
reachable merge whose merge state is `≈` a canonical fold of the union — is the
`MergeRealizable` hypothesis below, stated EXPLICITLY (not forced), as the note
directs. The vc:merge lift then follows by `≈`-closure. -/

/-- **`CanonicalRALin3Eq`** — the faithful conditioned-converse hypothesis:
convergence up to `≈` on every fully-closed set (the canonical class is
single-valued up to `≈`). The `eqObs`-lift of `Converse.CanonicalRALin3` minus its
`join` field (vc:merge is derived, not assumed). -/
structure CanonicalRALin3Eq (D : ConditionedMRDTSig) (E : EqEquiv D)
    (W : Op D.AppOp → D.State → Prop) : Prop where
  /-- Convergence up to `≈` on every fully causally-closed set. -/
  converges : ∀ (vis : Op D.AppOp → Op D.AppOp → Prop) (ev : Set (Op D.AppOp)),
    fullClosureRel vis ev → ConvergesEq E W vis ev

/-- **`MergeRealizable`** — the CONJECTURED domain-realizability step of vc:merge,
made an explicit hypothesis (per the note, "stated as an explicit hypothesis, as
the flat converse stated `converges`"). Over every abstract `GenDisc` fully-closed
`Inv` merge tuple of `EqJoinLemma3C`'s domain, the merge state `mergeL s₀ s₁ s₂`
is `≈` to a canonical fold of the union — the config-free stand-in for "the merge
tuple is a reachable merge version whose existence RA-lin asserts." This is the one
step NOT forced (the abstract Join domain is not automatically a reachable-config
domain), which is exactly the note's CONJECTURED label. -/
def MergeRealizable (D : ConditionedMRDTSig) (E : EqEquiv D)
    (W : Op D.AppOp → D.State → Prop)
    (GenDisc : (Op D.AppOp → Op D.AppOp → Prop) → Set (Op D.AppOp) → Prop) : Prop :=
  ∀ (vis : Op D.AppOp → Op D.AppOp → Prop) (events ev₁ ev₂ : Set (Op D.AppOp))
    (s₀ s₁ s₂ : D.State),
    D.Inv s₀ → D.Inv s₁ → D.Inv s₂ →
    (∀ {a b c : Op D.AppOp}, vis a b → vis b c → vis a c) →
    (∀ a : Op D.AppOp, ¬ vis a a) →
    (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
    fullClosureRel vis ev₁ → fullClosureRel vis ev₂ →
    GenDisc vis ev₁ → GenDisc vis ev₂ → GenDisc vis (ev₁ ∪ ev₂) →
    IsCanonicalStateEq E W vis (ev₁ ∩ ev₂) s₀ →
    IsCanonicalStateEq E W vis ev₁ s₁ → IsCanonicalStateEq E W vis ev₂ s₂ →
    ∃ u : D.State,
      IsCanonicalStateEq E W vis (ev₁ ∪ ev₂) u ∧ E.eqv (D.mergeL s₀ s₁ s₂) u

/-- **`converse_vc_merge` (the vc:merge lift, T3).** Conditioned RA-lin plus the
explicit realizability step forces the conditioned Join `EqJoinLemma3C`. The
derivation is the flat `converse_VC6`/`_VC8` Join step transported through `≈`: the
merge lands `≈` a canonical fold of the union (`MergeRealizable`), hence IS a
canonical state of the union by `≈`-closure (`isCanonicalStateEq_congr`).
Convergence (`CanonicalRALin3Eq`) secures well-definedness of the canonical class
the realizability names; the realizability itself is the CONJECTURED domain step,
not forced. -/
theorem converse_vc_merge {E : EqEquiv D} {W : Op D.AppOp → D.State → Prop}
    {GenDisc : (Op D.AppOp → Op D.AppOp → Prop) → Set (Op D.AppOp) → Prop}
    (_hconv : CanonicalRALin3Eq D E W) (hR : MergeRealizable D E W GenDisc) :
    EqJoinLemma3C D E W GenDisc := by
  intro vis events ev₁ ev₂ s₀ s₁ s₂ hs₀ hs₁ hs₂ htr hirr hin₁ hin₂ hcl₁ hcl₂
    hgd₁ hgd₂ hgdU hc₀ hc₁ hc₂
  obtain ⟨u, hu, hmu⟩ := hR vis events ev₁ ev₂ s₀ s₁ s₂ hs₀ hs₁ hs₂ htr hirr
    hin₁ hin₂ hcl₁ hcl₂ hgd₁ hgd₂ hgdU hc₀ hc₁ hc₂
  exact isCanonicalStateEq_congr hu hmu

/-! ## §5. The #123 experiment: RA-lin over an abstract antitone arbitration (T4)

The rc-free recast (`ra-lin-definition-note.md`, #123): replace `rc`/`loOnEq` by an
abstract arbitration `arb`, required only acyclic and (here) antitone. The
convergence engine (`eq_convergence`) is already order-agnostic, so the swap oracle
over an abstract `arb` feeds it unchanged. This section lands the abstraction and
the transport shape; the residue is named at the end. -/

/-- The concrete arbitration `loOnEq` uses: `rc = Fst_then_snd`. -/
def rcArb (D : ConditionedMRDTSig) : Op D.AppOp → Op D.AppOp → Prop :=
  fun e₁ e₂ => D.rc e₁ e₂ = RcRes.Fst_then_snd

/-- **`loOnArb`** — `loOnEq` with the rc-arm's `rc = Fst_then_snd` replaced by an
abstract arbitration `arb`. The vis arm and the absorber are unchanged. -/
def loOnArb (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (vis : Op D.AppOp → Op D.AppOp → Prop) (arb : Op D.AppOp → Op D.AppOp → Prop)
    (ev : Set (Op D.AppOp)) (e₁ e₂ : Op D.AppOp) : Prop :=
  (vis e₁ e₂ ∧ ¬ eqCommutesOn E W e₁ e₂)
  ∨ ( ¬ vis e₁ e₂ ∧ ¬ vis e₂ e₁ ∧ arb e₁ e₂
      ∧ ¬ ∃ e₃ ∈ ev, vis e₂ e₃ ∧ ¬ eqCommutesOn E W e₂ e₃ )

/-- **Transport in**: `loOnEq` IS `loOnArb` at the concrete arbitration `rcArb`.
So `loOnEq` is one acyclic antitone arbitration, and everything stated over
`loOnArb` specializes to the conditioned layer. -/
theorem loOnEq_isArb (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (vis : Op D.AppOp → Op D.AppOp → Prop) (ev : Set (Op D.AppOp))
    (e₁ e₂ : Op D.AppOp) :
    loOnEq E W vis ev e₁ e₂ ↔ loOnArb E W vis (rcArb D) ev e₁ e₂ := Iff.rfl

/-- **Antitonicity is free**: `loOnArb` is monotone-decreasing in the event set for
ANY `arb` (the absorber clause is the only set-dependence). This is the structural
property the recast must carry (the gap between owed swaps and available
convergence is an antitonicity gap), and it holds for every arbitration. -/
theorem loOnArb_mono {E : EqEquiv D} {W : Op D.AppOp → D.State → Prop}
    {vis : Op D.AppOp → Op D.AppOp → Prop} {arb : Op D.AppOp → Op D.AppOp → Prop}
    {ev ev' : Set (Op D.AppOp)} (h_sub : ev ⊆ ev') {e₁ e₂ : Op D.AppOp}
    (h : loOnArb E W vis arb ev' e₁ e₂) : loOnArb E W vis arb ev e₁ e₂ := by
  rcases h with h | ⟨h₁, h₂, h₃, h₄⟩
  · exact Or.inl h
  · exact Or.inr ⟨h₁, h₂, h₃,
      fun ⟨e₃, he₃, hv, hnc⟩ => h₄ ⟨e₃, h_sub he₃, hv, hnc⟩⟩

/-- Arb-relative canonical state (the recast's `Can≈`, over `loOnArb`). -/
def IsCanonicalStateArbEq (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (vis : Op D.AppOp → Op D.AppOp → Prop) (arb : Op D.AppOp → Op D.AppOp → Prop)
    (ev : Set (Op D.AppOp)) (s : D.State) : Prop :=
  ∃ ρ : List (Op D.AppOp),
    listPermOf ρ ev ∧ respects ρ (loOnArb E W vis arb ev) ∧
    E.eqv (applySeq D.toCRDTSig D.init ρ) s

/-- The `loOnEq`-canonical state IS the arb-canonical state at `arb = rcArb`
(pointwise the same relation, by `loOnEq_isArb`). -/
theorem isCanonicalStateEq_iff_arb (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (vis : Op D.AppOp → Op D.AppOp → Prop) (ev : Set (Op D.AppOp)) (s : D.State) :
    IsCanonicalStateEq E W vis ev s ↔ IsCanonicalStateArbEq E W vis (rcArb D) ev s :=
  Iff.rfl

/-- **`IsRALinearizable3ArbEq`** — the #123 recast of RA-linearizability over an
abstract arbitration: every stored version's state is an `arb`-respecting canonical
fold of its event set (existence-only per version, read up to `≈`). `versions ev s`
abstracts "`ev` is a stored version's event set with state `s`"; keeping it abstract
is what makes the statement config-agnostic, hence order-agnostic. -/
def IsRALinearizable3ArbEq (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (vis : Op D.AppOp → Op D.AppOp → Prop) (arb : Op D.AppOp → Op D.AppOp → Prop)
    (versions : Set (Op D.AppOp) → D.State → Prop) : Prop :=
  ∀ (ev : Set (Op D.AppOp)) (s : D.State),
    versions ev s → IsCanonicalStateArbEq E W vis arb ev s

/-- **The recast admits the conditioned layer.** The conditioned per-version RA-lin
(over `loOnEq`) IS the abstract-arbitration RA-lin at `arb = rcArb`: the two
canonical-state notions coincide (`isCanonicalStateEq_iff_arb`), so the forward
(adequacy) direction transports with no rc-specific residue. This is the #123
pivot's YES for the conditioned layer.

**Residue.** The FULL framework-wide adequacy — the `GoodConfig3` reachability
induction (`goodConfig3_of_reachF_wfgen`) re-threaded so that every merge step's
Join runs over the abstract `arb` rather than `loOnEq` — is the same mechanical
re-derivation named for the flat recast (#119 / #123, the `B-full` re-thread): a
copy of the reachability layer over `loOnArb`, not a composition. It carries no new
mathematical obstruction (the engine is order-agnostic and `loOnArb_mono` supplies
antitonicity for any `arb`), so it is deferred, exactly as `Converse.flat_completeness`
defers the tight biconditional to #119. -/
theorem ra_lin_arb_transport (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (vis : Op D.AppOp → Op D.AppOp → Prop)
    (versions : Set (Op D.AppOp) → D.State → Prop) :
    (∀ ev s, versions ev s → IsCanonicalStateEq E W vis ev s)
      ↔ IsRALinearizable3ArbEq E W vis (rcArb D) versions :=
  Iff.rfl

/-! ## §6. Axiom audit -/

#print axioms loOnEq_mono
#print axioms sig_peel_maximal_eq
#print axioms converse_vc_merge
#print axioms loOnArb_mono
#print axioms ra_lin_arb_transport

end GenericEqQuotient
end Sal.ConditionedMRDTs
