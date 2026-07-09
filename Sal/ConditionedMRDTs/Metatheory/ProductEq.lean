import Sal.ConditionedMRDTs.Metatheory.Product
import Sal.ConditionedMRDTs.Metatheory.GoodConfig3H
import Sal.ConditionedMRDTs.Metatheory.FlatGeneric_Bridge

/-!
# The product `≈`-lift kit — the quotient layer composes at the pragmatic cut

Mechanizes the `≈`-lift phase of `Development/COMPOSITION_PENPAPER.md` (§2.5,
obligations O16–O20 of its §5.5 plan) **at the pragmatic cut** (§2.5.7,
adopted): component 1 carries a full quotient bundle
`(E₁, W₁, hP₁, hC₁, hA₁, H₁, HonJ₁, …)`; component 2 is FLAT and enters
through `FlatGeneric_Bridge`'s identity instantiation
(`≈₂ = Eq` via `eqOfEq`, `W₂ = ⊤` via `WTop`, `Inv₂ = ⊤` via `hInvT₂`,
`H₂ = ⊤`). This is all Peritext (RGA-TF ⊗ flat MarkStore) needs; the
symmetric general `E₁ × E₂` form is explicitly out of scope (same proofs,
double the plumbing — memo §2.5.7).

Contents, by memo obligation:

* **O16** — the product bundle: `prodEqEquiv` (`E⊗ := ≈₁ × Eq`), `prodW`
  (`W⊗` reads component 1 on `inl`, `⊤` on `inr`), `prodWfOpGen`, and the
  lifted VC bundle `prodInvPres`/`prodCongVC`/`prodInvInvVC`/`prodInvCong`,
  each discharged per the memo's §2.5.1 table (componentwise; the untouched
  side of an update is definitional, the flat side's congruences are
  rewriting).
* **O17** — `eqCommutesOn` localization (memo §2.5.2): `doW⊗` leaves the
  untouched component fixed in BOTH branches of the `W`-guard, so cross
  pairs `≈`-commute by reflexivity (`eqCommutesOn_prod_cross`/`'`); same-side
  `inl` pairs are component 1's (`eqCommutesOn_prod_inl_iff` — the `⇒`
  direction instantiates `.2 := D₂.init`, `Inv₂ = ⊤` supplying the side
  condition); `inr` pairs degenerate to structural commutation
  (`eqCommutesOn_prod_inr_iff`), which is the flat identity instantiation's
  `eqCommutesOn` (`…_iff_flat`). Hence `loOnEq` localizes exactly as the raw
  `loOn` did (`loOnEq_prod_cross_lr`/`_rl`, `loOnEq_prod_inl_iff`,
  `loOnEq_prod_inr_iff`), absorber existential included.
* **O18** — `wfOpReachable_prod` (memo §2.5.5): the interleaving induction
  `wfChain_prod_of_proj` threads component 1's `WfChain` through a mixed
  list; `W₂ = ⊤` makes the `inr` steps trivial at the cut.
* **O19** — `eqJoinLemma3C_H_prod` (memo §2.5.4 — easier than the raw F4:
  no configuration at all): the abstract-`(vis, events)` gluing with
  `H⊗ ρ := H₁ (π₁ ρ)` (`H₂ = ⊤` at the cut) and
  `HonJ⊗ := HonJ₁∘res₁ ∧ HonJ₂∘res₂`; premises project
  (`isCanonicalStateEqH_proj₁`/`₂`), the witness is the plain concatenation
  (`eqCanonicalH_glue` — mixed `loOnEq` edges dead, `H⊗` of the
  concatenation is `H₁ ρ¹` by roundtrip), and the fold clause needs no
  congruence chasing (raw F1 `applySeq_prod` + `E⊗` componentwise).
* **O20** — the product `≈`-capstone `prod_ra_linearizable_up_to_eq_H`:
  the generic `RA_linearizable_up_to_eq_H` instantiated at the product
  parameters, consuming the component-1 bundle, the flat side's
  full-closure Join Lemma through `eqJoinH_of_joinC`, and the
  reachability-derived supplies (`hHon₁`/`hHext`/`hBA` — the §2.5.6 rerun,
  Peritext-phase) as hypotheses; the flat half of `HonJ⊗` is discharged
  STRUCTURALLY (`prodFlatHonJ` — same-replica `vis`-totality is a field of
  every configuration). Plus the premise-discharge wrappers
  `prodHext_of_hext₁` (config-free component extension ⟹ the product
  `hHext` obligation; `inr` steps are free — `π₁` drops them) and
  `prodGenW_of_genW₁` (the state-free half of `hBA`).

Layering: imports `Metatheory.Product` (the raw kit), the
`GenericEqQuotient` family via `GoodConfig3H`, and `FlatGeneric_Bridge`
(the identity bundles). No instance files. Per memo §2.5.3, everything
works directly at `QSig (prodSig D₁ D₂) E⊗ …` — no `QSig₁ ⊗ QSig₂`, no
signature isomorphism.
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs.ProductEq

open Sal.Emulation
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.GoodConfig3H
open Sal.ConditionedMRDTs.FlatGeneric
open Classical

variable {D₁ D₂ : ConditionedMRDTSig}

/-! ## §O16a  The product bundle data at the cut -/

/-- `vis` restricted to component 1 along `ι₁` (the abstract-`vis` analogue of
`projCore₁`'s visibility; memo §2.5.4). -/
def visRes₁ (vis : Op (D₁.AppOp ⊕ D₂.AppOp) → Op (D₁.AppOp ⊕ D₂.AppOp) → Prop) :
    Op D₁.AppOp → Op D₁.AppOp → Prop :=
  fun a b => vis (inlOp a) (inlOp b)

/-- `vis` restricted to component 2 along `ι₂`. -/
def visRes₂ (vis : Op (D₁.AppOp ⊕ D₂.AppOp) → Op (D₁.AppOp ⊕ D₂.AppOp) → Prop) :
    Op D₂.AppOp → Op D₂.AppOp → Prop :=
  fun a b => vis (inrOp a) (inrOp b)

variable (E₁ : EqEquiv D₁) (W₁ : Op D₁.AppOp → D₁.State → Prop)

/-- **`E⊗ := ≈₁ × Eq`** — the product observational equivalence at the
pragmatic cut: component 1's `≈₁` on firsts, literal equality on seconds
(memo §2.5.1, §2.5.7). -/
def prodEqEquiv : EqEquiv (prodSig D₁ D₂) where
  eqv := fun s s' => E₁.eqv s.1 s'.1 ∧ s.2 = s'.2
  equiv :=
    ⟨fun s => ⟨E₁.equiv.refl s.1, rfl⟩,
     fun h => ⟨E₁.equiv.symm h.1, h.2.symm⟩,
     fun h₁ h₂ => ⟨E₁.equiv.trans h₁.1 h₂.1, h₁.2.trans h₂.2⟩⟩

/-- **`W⊗`** — the product wellformedness guard at the cut: `W₁` at `.1` on
`inl` ops, `⊤` on `inr` ops (`W₂ = ⊤`). Componentwise BY DESIGN (memo
§2.5.2's trap: `doW` reads `W`, and `eqCommutesOn`/`loOnEq` localization
dies the moment a guard reads the other component). -/
def prodW : Op (D₁.AppOp ⊕ D₂.AppOp) → (prodSig D₁ D₂).State → Prop :=
  fun e s =>
    match e.2.2 with
    | Sum.inl o => W₁ (e.1, e.2.1, o) s.1
    | Sum.inr _ => True

/-- **`WfOpGen⊗`** — per-event generation wellformedness: component 1's on
`inl`, `⊤` on `inr` (the flat side has no generation discipline at the cut). -/
def prodWfOpGen (WfOpGen₁ : Op D₁.AppOp → Prop) : Op (D₁.AppOp ⊕ D₂.AppOp) → Prop :=
  fun e =>
    match e.2.2 with
    | Sum.inl o => WfOpGen₁ (e.1, e.2.1, o)
    | Sum.inr _ => True

/-- **`H⊗ ρ := H₁ (π₁ ρ)`** — the product witness discipline at the cut
(`H₂ = ⊤`, so the memo's conjunction `H₁ (π₁ ρ) ∧ H₂ (π₂ ρ)` collapses to
its first conjunct; memo §2.5.4). -/
def prodH (H₁ : List (Op D₁.AppOp) → Prop) :
    List (Op (D₁.AppOp ⊕ D₂.AppOp)) → Prop :=
  fun ρ => H₁ (projList₁ ρ)

/-- **`HonJ⊗`** — the product join context: the conjunction of the two
components' contexts at the restrictions (memo §2.5.4; the supply obligation
moves to the capstone's `hHon` premise — §2.5.6). -/
def prodHonJ
    (HonJ₁ : (Op D₁.AppOp → Op D₁.AppOp → Prop) → Set (Op D₁.AppOp) → Prop)
    (HonJ₂ : (Op D₂.AppOp → Op D₂.AppOp → Prop) → Set (Op D₂.AppOp) → Prop) :
    (Op (D₁.AppOp ⊕ D₂.AppOp) → Op (D₁.AppOp ⊕ D₂.AppOp) → Prop) →
      Set (Op (D₁.AppOp ⊕ D₂.AppOp)) → Prop :=
  fun vis ev => HonJ₁ (visRes₁ vis) (evRes₁ ev) ∧ HonJ₂ (visRes₂ vis) (evRes₂ ev)

/-! ### The guarded-step kit: `doW⊗` acts componentwise -/

/-- `doW` at the product on an `inl` op: the guard `W⊗` reads only `.1`, so
BOTH branches leave `.2` at `s.2` — the guarded step is `(doW₁, id)`. This
single fact is what keeps cross pairs `≈`-commuting (memo §2.5.2). -/
theorem doW_prod_inl (e : Op D₁.AppOp) (s : (prodSig D₁ D₂).State) :
    doW (prodSig D₁ D₂) (prodW W₁) (inlOp e) s = (doW D₁ W₁ e s.1, s.2) := by
  by_cases h : W₁ e s.1
  · have h1 : doW (prodSig D₁ D₂) (prodW W₁) (inlOp e) s
        = (prodSig D₁ D₂).update s (inlOp e) :=
      if_pos (show prodW (D₂ := D₂) W₁ (inlOp e) s from h)
    have h2 : doW D₁ W₁ e s.1 = D₁.update s.1 e := if_pos h
    rw [h1, h2]
    exact prodSig_update_inl s e
  · have h1 : doW (prodSig D₁ D₂) (prodW W₁) (inlOp e) s = s :=
      if_neg (show ¬ prodW (D₂ := D₂) W₁ (inlOp e) s from h)
    have h2 : doW D₁ W₁ e s.1 = s.1 := if_neg h
    rw [h1, h2]
    rfl

/-- `doW` at the product on an `inr` op: the guard is `⊤`, so the step is the
raw component-2 update, `.1` untouched. -/
theorem doW_prod_inr (f : Op D₂.AppOp) (s : (prodSig D₁ D₂).State) :
    doW (prodSig D₁ D₂) (prodW W₁) (inrOp f) s = (s.1, D₂.update s.2 f) := by
  have h1 : doW (prodSig D₁ D₂) (prodW W₁) (inrOp f) s
      = (prodSig D₁ D₂).update s (inrOp f) :=
    if_pos (show prodW (D₂ := D₂) W₁ (inrOp f) s from True.intro)
  rw [h1]
  exact prodSig_update_inr s f

/-! ## §O16b  The lifted VC bundle (memo §2.5.1 table) -/

/-- **`InvPres⊗`** — `Inv⊗ = Inv₁ ∧ ⊤`: `inl` updates step component 1 with
`W⊗ = W₁` at `.1` and leave `.2` untouched; `inr` updates leave `.1`
untouched and `Inv₂ = ⊤` absorbs the rest; `mergeL` is componentwise. -/
theorem prodInvPres (hP₁ : InvPres D₁ W₁) (hInvT₂ : ∀ s : D₂.State, D₂.Inv s) :
    InvPres (prodSig D₁ D₂) (prodW W₁) where
  inv_init := ⟨hP₁.inv_init, hInvT₂ _⟩
  inv_update := fun s o hs hw => by
    rcases o with ⟨t, r, o⟩
    cases o with
    | inl o₁ => exact ⟨hP₁.inv_update s.1 (t, r, o₁) hs.1 hw, hInvT₂ _⟩
    | inr o₂ => exact ⟨hs.1, hInvT₂ _⟩
  inv_mergeL := fun l a b hl ha hb =>
    ⟨hP₁.inv_mergeL l.1 a.1 b.1 hl.1 ha.1 hb.1, hInvT₂ _⟩

/-- **`CongVC⊗`** — component congruence on the stepped side, the carried
`≈`/`Eq` fact on the other; the flat side's congruence is rewriting; the sum
`query` reads one side (memo §2.5.1 table rows `update_congr`,
`mergeL_congr`, `query_congr`). -/
theorem prodCongVC (hC₁ : CongVC D₁ E₁) :
    CongVC (prodSig D₁ D₂) (prodEqEquiv E₁) where
  update_congr := fun o {s s'} hs hs' h => by
    rcases o with ⟨t, r, o⟩
    cases o with
    | inl o₁ =>
      exact ⟨hC₁.update_congr (t, r, o₁) hs.1 hs'.1 h.1, h.2⟩
    | inr o₂ =>
      exact ⟨h.1, congrArg (fun x => D₂.update x (t, r, o₂)) h.2⟩
  mergeL_congr := fun {l l' a a' b b'} hl hl' ha ha' hb hb' hle hae hbe =>
    ⟨hC₁.mergeL_congr hl.1 hl'.1 ha.1 ha'.1 hb.1 hb'.1 hle.1 hae.1 hbe.1,
     by show D₂.mergeL l.2 a.2 b.2 = D₂.mergeL l'.2 a'.2 b'.2
        rw [hle.2, hae.2, hbe.2]⟩
  query_congr := fun q {s s'} hs hs' h => by
    cases q with
    | inl q₁ => exact congrArg Sum.inl (hC₁.query_congr q₁ hs.1 hs'.1 h.1)
    | inr q₂ => exact congrArg (fun x => Sum.inr (D₂.query x q₂)) h.2

/-- **`InvInvVC⊗`** — `W⊗` and `applicable⊗` each read one side (the base
combinator's `applicable` is componentwise — memo §1.1; read-coupled guards
are §3's L2 territory, out of scope here): component 1's congruences on
`inl`, rewriting on `inr`. -/
theorem prodInvInvVC (hA₁ : InvInvVC D₁ E₁ W₁) :
    InvInvVC (prodSig D₁ D₂) (prodEqEquiv E₁) (prodW W₁) where
  wf_congr := fun o {s s'} hs hs' h => by
    rcases o with ⟨t, r, o⟩
    cases o with
    | inl o₁ =>
      show W₁ (t, r, o₁) s.1 ↔ W₁ (t, r, o₁) s'.1
      exact hA₁.wf_congr (t, r, o₁) hs.1 hs'.1 h.1
    | inr o₂ => exact Iff.rfl
  applicable_congr := fun o {s s'} hs hs' h => by
    rcases o with ⟨t, r, o⟩
    cases o with
    | inl o₁ =>
      show D₁.applicable (t, r, o₁) s.1 ↔ D₁.applicable (t, r, o₁) s'.1
      exact hA₁.applicable_congr (t, r, o₁) hs.1 hs'.1 h.1
    | inr o₂ =>
      show D₂.applicable (t, r, o₂) s.2 ↔ D₂.applicable (t, r, o₂) s'.2
      rw [h.2]

/-- **`hInvCong⊗`** — `Inv⊗` is `E⊗`-invariant: component 1's invariance on
firsts, `Inv₂ = ⊤` on seconds. -/
theorem prodInvCong
    (hInvCong₁ : ∀ {s s' : D₁.State}, E₁.eqv s s' → D₁.Inv s → D₁.Inv s')
    (hInvT₂ : ∀ s : D₂.State, D₂.Inv s) :
    ∀ {s s' : (prodSig D₁ D₂).State},
      (prodEqEquiv E₁).eqv s s' → (prodSig D₁ D₂).Inv s → (prodSig D₁ D₂).Inv s' :=
  fun h hi => ⟨hInvCong₁ h.1 hi.1, hInvT₂ _⟩

/-! ## §O17  `eqCommutesOn` localization (memo §2.5.2) -/

/-- **Cross pairs `≈`-commute.** `doW⊗ (ι₁ e)` leaves `.2` fixed in both
branches of the `W`-guard and `doW⊗ (ι₂ f)` leaves `.1` fixed, so the two
composites are literally the same pair — `E⊗`-reflexivity closes it. This is
the quotient analogue of the raw (D-cross), and the one place the quotient
layer is more fragile than the raw one: it needs `W⊗` componentwise (memo
§2.5.2). -/
theorem eqCommutesOn_prod_cross (e : Op D₁.AppOp) (f : Op D₂.AppOp) :
    eqCommutesOn (prodEqEquiv E₁) (prodW W₁) (inlOp e) (inrOp f) := by
  intro s _
  simp only [doW_prod_inl, doW_prod_inr]
  exact ⟨E₁.equiv.refl _, rfl⟩

/-- Cross pairs `≈`-commute, other orientation. -/
theorem eqCommutesOn_prod_cross' (f : Op D₂.AppOp) (e : Op D₁.AppOp) :
    eqCommutesOn (prodEqEquiv E₁) (prodW W₁) (inrOp f) (inlOp e) := by
  intro s _
  simp only [doW_prod_inl, doW_prod_inr]
  exact ⟨E₁.equiv.refl _, rfl⟩

/-- **Same-side `inl` `≈`-commutation is component 1's.** (⇐) componentwise
with the carried side reflexive; (⇒) instantiate `.2 := D₂.init` — `Inv₂ = ⊤`
at the cut supplies the `Inv⊗` side condition with no appeal to component 2
data (memo §2.5.2). -/
theorem eqCommutesOn_prod_inl_iff (hInvT₂ : ∀ s : D₂.State, D₂.Inv s)
    (a b : Op D₁.AppOp) :
    eqCommutesOn (prodEqEquiv (D₂ := D₂) E₁) (prodW W₁) (inlOp a) (inlOp b)
      ↔ eqCommutesOn E₁ W₁ a b := by
  constructor
  · intro h s₁ hs₁
    have h2 := h (s₁, D₂.init) ⟨hs₁, hInvT₂ _⟩
    simp only [doW_prod_inl] at h2
    exact h2.1
  · intro h s hs
    simp only [doW_prod_inl]
    exact ⟨h s.1 hs.1, rfl⟩

/-- **Same-side `inr` `≈`-commutation degenerates to structural commutation**:
the guard is `⊤` (so `doW⊗` is the raw component-2 update), `E⊗` on seconds
is `Eq`, and the `Inv⊗`-conditioning is total (`Inv₂ = ⊤`; the `.1` slot is
inhabited by `D₁.init` with `hP₁.inv_init`). -/
theorem eqCommutesOn_prod_inr_iff (hP₁ : InvPres D₁ W₁)
    (hInvT₂ : ∀ s : D₂.State, D₂.Inv s) (a b : Op D₂.AppOp) :
    eqCommutesOn (prodEqEquiv E₁) (prodW W₁) (inrOp a) (inrOp b)
      ↔ D₂.toCRDTSig.commutes a b := by
  constructor
  · intro h s₂
    have h2 := h (D₁.init, s₂) ⟨hP₁.inv_init, hInvT₂ s₂⟩
    simp only [doW_prod_inr] at h2
    exact h2.2
  · intro h s _
    simp only [doW_prod_inr]
    exact ⟨E₁.equiv.refl _, h s.2⟩

/-- The `inr` localization phrased at the flat identity instantiation — the
form the flat side's `IsCanonicalStateEqH` witnesses actually carry
(`eqCommutesOn (eqOfEq D₂) (WTop D₂)`, via `eqCommutesOn_iff_commutes`). -/
theorem eqCommutesOn_prod_inr_iff_flat (hP₁ : InvPres D₁ W₁)
    (hInvT₂ : ∀ s : D₂.State, D₂.Inv s) (a b : Op D₂.AppOp) :
    eqCommutesOn (prodEqEquiv E₁) (prodW W₁) (inrOp a) (inrOp b)
      ↔ eqCommutesOn (eqOfEq D₂) (WTop D₂) a b :=
  (eqCommutesOn_prod_inr_iff E₁ W₁ hP₁ hInvT₂ a b).trans
    (eqCommutesOn_iff_commutes hInvT₂ a b).symm

/-! ### `loOnEq` localization (memo §2.2.1 rerun with `eqCommutesOn`) -/

/-- **Mixed pairs carry no `loOnEq` edge** (`inl → inr`): arm 1's
`¬eqCommutesOn` is refuted by the cross lemma; arm 2's mixed `rc` is `Either`
by definition. -/
theorem loOnEq_prod_cross_lr
    {vis : Op (D₁.AppOp ⊕ D₂.AppOp) → Op (D₁.AppOp ⊕ D₂.AppOp) → Prop}
    {ev : Set (Op (D₁.AppOp ⊕ D₂.AppOp))} (a : Op D₁.AppOp) (b : Op D₂.AppOp) :
    ¬ loOnEq (prodEqEquiv E₁) (prodW W₁) vis ev (inlOp a) (inrOp b) := by
  rintro (⟨_, hnc⟩ | ⟨_, _, hrc, _⟩)
  · exact hnc (eqCommutesOn_prod_cross E₁ W₁ a b)
  · exact RcRes.noConfusion ((prodSig_rc_inl_inr a b) ▸ hrc)

/-- Mixed pairs carry no `loOnEq` edge (`inr → inl`). -/
theorem loOnEq_prod_cross_rl
    {vis : Op (D₁.AppOp ⊕ D₂.AppOp) → Op (D₁.AppOp ⊕ D₂.AppOp) → Prop}
    {ev : Set (Op (D₁.AppOp ⊕ D₂.AppOp))} (b : Op D₂.AppOp) (a : Op D₁.AppOp) :
    ¬ loOnEq (prodEqEquiv E₁) (prodW W₁) vis ev (inrOp b) (inlOp a) := by
  rintro (⟨_, hnc⟩ | ⟨_, _, hrc, _⟩)
  · exact hnc (eqCommutesOn_prod_cross' E₁ W₁ b a)
  · exact RcRes.noConfusion ((prodSig_rc_inr_inl b a) ▸ hrc)

/-- **Same-side `inl` `loOnEq` edges coincide with component 1's** at the
restricted `(vis, ev)`. The absorber existential transfers both ways: a
component absorber lifts along `ι₁`; a product absorber of an `inl` event
must itself be `inl` — an `inr` candidate `≈`-commutes by the cross lemma —
and then projects (memo §2.5.2, mirroring the raw §2.2.1). -/
theorem loOnEq_prod_inl_iff (hInvT₂ : ∀ s : D₂.State, D₂.Inv s)
    {vis : Op (D₁.AppOp ⊕ D₂.AppOp) → Op (D₁.AppOp ⊕ D₂.AppOp) → Prop}
    {ev : Set (Op (D₁.AppOp ⊕ D₂.AppOp))} (a b : Op D₁.AppOp) :
    loOnEq (prodEqEquiv E₁) (prodW W₁) vis ev (inlOp a) (inlOp b)
      ↔ loOnEq E₁ W₁ (visRes₁ vis) (evRes₁ ev) a b := by
  constructor
  · rintro (⟨hv, hnc⟩ | ⟨hnv, hnv', hrc, habs⟩)
    · exact Or.inl ⟨hv, fun hc =>
        hnc ((eqCommutesOn_prod_inl_iff E₁ W₁ hInvT₂ a b).mpr hc)⟩
    · refine Or.inr ⟨hnv, hnv', hrc, ?_⟩
      rintro ⟨e₃, h₃, hv₃, hnc₃⟩
      exact habs ⟨inlOp e₃, h₃, hv₃, fun hc =>
        hnc₃ ((eqCommutesOn_prod_inl_iff E₁ W₁ hInvT₂ b e₃).mp hc)⟩
  · rintro (⟨hv, hnc⟩ | ⟨hnv, hnv', hrc, habs⟩)
    · exact Or.inl ⟨hv, fun hc =>
        hnc ((eqCommutesOn_prod_inl_iff E₁ W₁ hInvT₂ a b).mp hc)⟩
    · refine Or.inr ⟨hnv, hnv', hrc, ?_⟩
      rintro ⟨e₃, h₃, hv₃, hnc₃⟩
      rcases op_sum_cases e₃ with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · exact habs ⟨c, h₃, hv₃, fun hc =>
          hnc₃ ((eqCommutesOn_prod_inl_iff E₁ W₁ hInvT₂ b c).mpr hc)⟩
      · exact hnc₃ (eqCommutesOn_prod_cross E₁ W₁ b c)

/-- **Same-side `inr` `loOnEq` edges coincide with the flat identity
instantiation's** at the restricted `(vis, ev)` — the order the flat side's
witnesses respect (`loOnEq (eqOfEq D₂) (WTop D₂)`). -/
theorem loOnEq_prod_inr_iff (hP₁ : InvPres D₁ W₁)
    (hInvT₂ : ∀ s : D₂.State, D₂.Inv s)
    {vis : Op (D₁.AppOp ⊕ D₂.AppOp) → Op (D₁.AppOp ⊕ D₂.AppOp) → Prop}
    {ev : Set (Op (D₁.AppOp ⊕ D₂.AppOp))} (a b : Op D₂.AppOp) :
    loOnEq (prodEqEquiv E₁) (prodW W₁) vis ev (inrOp a) (inrOp b)
      ↔ loOnEq (eqOfEq D₂) (WTop D₂) (visRes₂ vis) (evRes₂ ev) a b := by
  constructor
  · rintro (⟨hv, hnc⟩ | ⟨hnv, hnv', hrc, habs⟩)
    · exact Or.inl ⟨hv, fun hc =>
        hnc ((eqCommutesOn_prod_inr_iff_flat E₁ W₁ hP₁ hInvT₂ a b).mpr hc)⟩
    · refine Or.inr ⟨hnv, hnv', hrc, ?_⟩
      rintro ⟨e₃, h₃, hv₃, hnc₃⟩
      exact habs ⟨inrOp e₃, h₃, hv₃, fun hc =>
        hnc₃ ((eqCommutesOn_prod_inr_iff_flat E₁ W₁ hP₁ hInvT₂ b e₃).mp hc)⟩
  · rintro (⟨hv, hnc⟩ | ⟨hnv, hnv', hrc, habs⟩)
    · exact Or.inl ⟨hv, fun hc =>
        hnc ((eqCommutesOn_prod_inr_iff_flat E₁ W₁ hP₁ hInvT₂ a b).mp hc)⟩
    · refine Or.inr ⟨hnv, hnv', hrc, ?_⟩
      rintro ⟨e₃, h₃, hv₃, hnc₃⟩
      rcases op_sum_cases e₃ with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · exact hnc₃ (eqCommutesOn_prod_cross' E₁ W₁ b c)
      · exact habs ⟨c, h₃, hv₃, fun hc =>
          hnc₃ ((eqCommutesOn_prod_inr_iff_flat E₁ W₁ hP₁ hInvT₂ b c).mpr hc)⟩

/-- `respects (loOnEq⊗)` projects onto component 1 along `π₁`. -/
theorem respects_loOnEq_projList₁ (hInvT₂ : ∀ s : D₂.State, D₂.Inv s)
    {vis : Op (D₁.AppOp ⊕ D₂.AppOp) → Op (D₁.AppOp ⊕ D₂.AppOp) → Prop}
    {ev : Set (Op (D₁.AppOp ⊕ D₂.AppOp))} {ρ : List (Op (D₁.AppOp ⊕ D₂.AppOp))}
    (h : respects ρ (loOnEq (prodEqEquiv E₁) (prodW W₁) vis ev)) :
    respects (projList₁ ρ) (loOnEq E₁ W₁ (visRes₁ vis) (evRes₁ ev)) := by
  unfold respects at h ⊢
  unfold projList₁
  rw [List.pairwise_filterMap]
  refine h.imp ?_
  intro x y hxy a hxa b hyb
  rw [oplOp_eq_some] at hxa hyb
  subst hxa; subst hyb
  exact fun hlo => hxy ((loOnEq_prod_inl_iff E₁ W₁ hInvT₂ b a).mpr hlo)

/-- `respects (loOnEq⊗)` projects onto component 2 (flat parameters) along
`π₂`. -/
theorem respects_loOnEq_projList₂ (hP₁ : InvPres D₁ W₁)
    (hInvT₂ : ∀ s : D₂.State, D₂.Inv s)
    {vis : Op (D₁.AppOp ⊕ D₂.AppOp) → Op (D₁.AppOp ⊕ D₂.AppOp) → Prop}
    {ev : Set (Op (D₁.AppOp ⊕ D₂.AppOp))} {ρ : List (Op (D₁.AppOp ⊕ D₂.AppOp))}
    (h : respects ρ (loOnEq (prodEqEquiv E₁) (prodW W₁) vis ev)) :
    respects (projList₂ ρ)
      (loOnEq (eqOfEq D₂) (WTop D₂) (visRes₂ vis) (evRes₂ ev)) := by
  unfold respects at h ⊢
  unfold projList₂
  rw [List.pairwise_filterMap]
  refine h.imp ?_
  intro x y hxy a hxa b hyb
  rw [oprOp_eq_some] at hxa hyb
  subst hxa; subst hyb
  exact fun hlo => hxy ((loOnEq_prod_inr_iff E₁ W₁ hP₁ hInvT₂ b a).mpr hlo)

/-! ## §O19a  `H`-disciplined canonical states project and glue -/

/-- The product `H⊗`-witness projects onto component 1: `π₁` of the witness
is Nodup, enumerates `ev↾₁`, respects `loOnEq₁` (localization), carries
`H₁ (π₁ ρ)` — which IS `H⊗ ρ` — and its raw fold is `.1` of the product fold
(F1) with `E⊗ ⟹ E₁` on firsts (memo §2.5.4 premise projection). -/
theorem isCanonicalStateEqH_proj₁ (hInvT₂ : ∀ s : D₂.State, D₂.Inv s)
    {H₁ : List (Op D₁.AppOp) → Prop}
    {vis : Op (D₁.AppOp ⊕ D₂.AppOp) → Op (D₁.AppOp ⊕ D₂.AppOp) → Prop}
    {ev : Set (Op (D₁.AppOp ⊕ D₂.AppOp))} {s : (prodSig D₁ D₂).State}
    (h : IsCanonicalStateEqH (prodH H₁) (prodEqEquiv E₁) (prodW W₁) vis ev s) :
    IsCanonicalStateEqH H₁ E₁ W₁ (visRes₁ vis) (evRes₁ ev) s.1 := by
  obtain ⟨ρ, hp, hr, hH, hf⟩ := h
  rw [applySeq_prod] at hf
  exact ⟨projList₁ ρ, listPermOf_projList₁ hp,
    respects_loOnEq_projList₁ E₁ W₁ hInvT₂ hr, hH, hf.1⟩

/-- The product `H⊗`-witness projects onto component 2 at the flat
parameters: the discipline clause is `⊤`, the fold clause is the literal
`.2`-equality (`E⊗`'s second component is `Eq`). -/
theorem isCanonicalStateEqH_proj₂ (hP₁ : InvPres D₁ W₁)
    (hInvT₂ : ∀ s : D₂.State, D₂.Inv s)
    {H₁ : List (Op D₁.AppOp) → Prop}
    {vis : Op (D₁.AppOp ⊕ D₂.AppOp) → Op (D₁.AppOp ⊕ D₂.AppOp) → Prop}
    {ev : Set (Op (D₁.AppOp ⊕ D₂.AppOp))} {s : (prodSig D₁ D₂).State}
    (h : IsCanonicalStateEqH (prodH H₁) (prodEqEquiv E₁) (prodW W₁) vis ev s) :
    IsCanonicalStateEqH (fun _ => True) (eqOfEq D₂) (WTop D₂)
      (visRes₂ vis) (evRes₂ ev) s.2 := by
  obtain ⟨ρ, hp, hr, _, hf⟩ := h
  rw [applySeq_prod] at hf
  exact ⟨projList₂ ρ, listPermOf_projList₂ hp,
    respects_loOnEq_projList₂ E₁ W₁ hP₁ hInvT₂ hr, trivial, hf.2⟩

/-- **The `≈`-glue is a plain concatenation** `ι₁ρ¹ ++ ι₂ρ²` (memo §2.5.4):
component `H`-witnesses at the restrictions assemble into the product
`H⊗`-witness at the mixed set. `respects loOnEq⊗` as in the raw gluing —
mixed `loOnEq` edges are dead in both directions, within-block edges
transfer along the same-side iffs; `H⊗` of the concatenation is `H₁ ρ¹` by
the `π₁`-roundtrip; the fold clause is raw F1 plus `E⊗` componentwise — NO
congruence chasing. -/
theorem eqCanonicalH_glue (hP₁ : InvPres D₁ W₁)
    (hInvT₂ : ∀ s : D₂.State, D₂.Inv s)
    {H₁ : List (Op D₁.AppOp) → Prop}
    {vis : Op (D₁.AppOp ⊕ D₂.AppOp) → Op (D₁.AppOp ⊕ D₂.AppOp) → Prop}
    {U : Set (Op (D₁.AppOp ⊕ D₂.AppOp))} {m₁ : D₁.State} {m₂ : D₂.State}
    (h₁ : IsCanonicalStateEqH H₁ E₁ W₁ (visRes₁ vis) (evRes₁ U) m₁)
    (h₂ : IsCanonicalStateEqH (fun _ => True) (eqOfEq D₂) (WTop D₂)
      (visRes₂ vis) (evRes₂ U) m₂) :
    IsCanonicalStateEqH (prodH H₁) (prodEqEquiv E₁) (prodW W₁) vis U
      ((m₁, m₂) : (prodSig D₁ D₂).State) := by
  obtain ⟨ρ₁, hp₁, hr₁, hH₁, hf₁⟩ := h₁
  obtain ⟨ρ₂, hp₂, hr₂, _, hf₂⟩ := h₂
  refine ⟨ρ₁.map inlOp ++ ρ₂.map inrOp, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · -- Nodup: injective images, disjoint blocks (payload tags differ)
    rw [List.nodup_append]
    refine ⟨hp₁.1.map inlOp_injective, hp₂.1.map inrOp_injective, ?_⟩
    intro x hx y hy
    rw [List.mem_map] at hx hy
    obtain ⟨a, _, rfl⟩ := hx
    obtain ⟨b, _, rfl⟩ := hy
    exact inlOp_ne_inrOp a b
  · -- membership: each event lands in the matching block (roundtrip)
    intro x
    rw [List.mem_append, List.mem_map, List.mem_map]
    constructor
    · rintro (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
      · exact (hp₁.2 a).mp ha
      · exact (hp₂.2 b).mp hb
    · intro hx
      rcases op_sum_cases x with ⟨a, rfl⟩ | ⟨b, rfl⟩
      · exact Or.inl ⟨a, (hp₁.2 a).mpr hx, rfl⟩
      · exact Or.inr ⟨b, (hp₂.2 b).mpr hx, rfl⟩
  · -- respects loOnEq⊗: blocks via the same-side iffs, cross pairs edge-free
    unfold respects
    rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.pairwise_map]
      exact hr₁.imp fun {x y} h hlo =>
        h ((loOnEq_prod_inl_iff E₁ W₁ hInvT₂ y x).mp hlo)
    · rw [List.pairwise_map]
      exact hr₂.imp fun {x y} h hlo =>
        h ((loOnEq_prod_inr_iff E₁ W₁ hP₁ hInvT₂ y x).mp hlo)
    · intro x hx y hy
      rw [List.mem_map] at hx hy
      obtain ⟨a, _, rfl⟩ := hx
      obtain ⟨b, _, rfl⟩ := hy
      exact loOnEq_prod_cross_rl E₁ W₁ b a
  · -- H⊗: π₁ of the concatenation is ρ₁ (roundtrip)
    show H₁ (projList₁ (ρ₁.map inlOp ++ ρ₂.map inrOp))
    rw [projList₁_append, projList₁_map_inlOp, projList₁_map_inrOp,
      List.append_nil]
    exact hH₁
  · -- fold: raw F1 + roundtrips, then E⊗ componentwise
    rw [applySeq_prod, projList₁_append, projList₂_append,
      projList₁_map_inlOp, projList₁_map_inrOp,
      projList₂_map_inlOp, projList₂_map_inrOp,
      List.append_nil, List.nil_append]
    exact ⟨hf₁, hf₂⟩

/-! ## §O19b  The `≈`-join gluing (memo §2.5.4) -/

/-- **`EqJoinLemma3C_H` glues** (easier than the raw F4 — no configuration
at all): if component 1's `≈`-join holds at `(E₁, W₁, H₁, HonJ₁)` and the
flat side's holds at the identity instantiation
(`eqOfEq/WTop/⊤`, e.g. via `eqJoinH_of_joinC`), then the product satisfies
`EqJoinLemma3C_H` at `(E⊗, W⊗, H⊗, HonJ⊗)`. Premise projection: `vis`
trans/irrefl restrict; distinct timestamps restrict (`ι` is injective and
timestamp-preserving); `fullClosureRel` restricts (component edges are
product edges); `Inv⊗ ⟹ Invᵢ`; canonical states project. The witness is
the concatenation glue. -/
theorem eqJoinLemma3C_H_prod (hP₁ : InvPres D₁ W₁)
    (hInvT₂ : ∀ s : D₂.State, D₂.Inv s)
    {H₁ : List (Op D₁.AppOp) → Prop}
    {HonJ₁ : (Op D₁.AppOp → Op D₁.AppOp → Prop) → Set (Op D₁.AppOp) → Prop}
    {HonJ₂ : (Op D₂.AppOp → Op D₂.AppOp → Prop) → Set (Op D₂.AppOp) → Prop}
    (hJ₁ : EqJoinLemma3C_H D₁ E₁ W₁ H₁ HonJ₁)
    (hJ₂ : EqJoinLemma3C_H D₂ (eqOfEq D₂) (WTop D₂) (fun _ => True) HonJ₂) :
    EqJoinLemma3C_H (prodSig D₁ D₂) (prodEqEquiv E₁) (prodW W₁) (prodH H₁)
      (prodHonJ HonJ₁ HonJ₂) := by
  intro vis events ev₁ ev₂ s₀ s₁ s₂ hHonJ hI₀ hI₁ hI₂ htr hirr hdts
    hin₁ hin₂ hcl₁ hcl₂ hc₀ hc₁ hc₂
  have g₁ := hJ₁ (visRes₁ vis) (evRes₁ events) (evRes₁ ev₁) (evRes₁ ev₂)
    s₀.1 s₁.1 s₂.1 hHonJ.1 hI₀.1 hI₁.1 hI₂.1
    (fun {a b c} hab hbc => htr hab hbc)
    (fun a hv => hirr (inlOp a) hv)
    (fun a b ha hb hne => hdts (inlOp a) (inlOp b) ha hb
      (fun h => hne (inlOp_injective h)))
    (fun a ha => hin₁ (inlOp a) ha)
    (fun a ha => hin₂ (inlOp a) ha)
    (fun a b hv hb => hcl₁ (inlOp a) (inlOp b) hv hb)
    (fun a b hv hb => hcl₂ (inlOp a) (inlOp b) hv hb)
    (isCanonicalStateEqH_proj₁ E₁ W₁ hInvT₂ hc₀)
    (isCanonicalStateEqH_proj₁ E₁ W₁ hInvT₂ hc₁)
    (isCanonicalStateEqH_proj₁ E₁ W₁ hInvT₂ hc₂)
  have g₂ := hJ₂ (visRes₂ vis) (evRes₂ events) (evRes₂ ev₁) (evRes₂ ev₂)
    s₀.2 s₁.2 s₂.2 hHonJ.2 (hInvT₂ _) (hInvT₂ _) (hInvT₂ _)
    (fun {a b c} hab hbc => htr hab hbc)
    (fun a hv => hirr (inrOp a) hv)
    (fun a b ha hb hne => hdts (inrOp a) (inrOp b) ha hb
      (fun h => hne (inrOp_injective h)))
    (fun a ha => hin₁ (inrOp a) ha)
    (fun a ha => hin₂ (inrOp a) ha)
    (fun a b hv hb => hcl₁ (inrOp a) (inrOp b) hv hb)
    (fun a b hv hb => hcl₂ (inrOp a) (inrOp b) hv hb)
    (isCanonicalStateEqH_proj₂ E₁ W₁ hP₁ hInvT₂ hc₀)
    (isCanonicalStateEqH_proj₂ E₁ W₁ hP₁ hInvT₂ hc₁)
    (isCanonicalStateEqH_proj₂ E₁ W₁ hP₁ hInvT₂ hc₂)
  exact eqCanonicalH_glue E₁ W₁ hP₁ hInvT₂ g₁ g₂

/-! ## §O18  `WfOpReachable⊗` (memo §2.5.5) -/

/-- The interleaving induction: a component-1 `WfChain` along `π₁ ρ` threads
through the mixed list. An `inl` head demands `W₁` at `.1` of the running
fold — exactly the component chain's head clause (F1 keeps `.1` in sync);
an `inr` head demands `⊤` (`W₂ = ⊤` at the cut) and leaves `.1` untouched. -/
theorem wfChain_prod_of_proj (ρ : List (Op (D₁.AppOp ⊕ D₂.AppOp))) :
    ∀ s : (prodSig D₁ D₂).State,
      WfChain D₁ W₁ s.1 (projList₁ ρ) →
      WfChain (prodSig D₁ D₂) (prodW W₁) s ρ := by
  induction ρ with
  | nil =>
    intro s _
    exact trivial
  | cons e ρ ih =>
    intro s h
    rcases e with ⟨t, r, o⟩
    cases o with
    | inl o₁ =>
      have h' : W₁ (t, r, o₁) s.1
          ∧ WfChain D₁ W₁ (D₁.update s.1 (t, r, o₁)) (projList₁ ρ) := h
      exact ⟨h'.1, ih ((prodSig D₁ D₂).update s (t, r, Sum.inl o₁)) h'.2⟩
    | inr o₂ =>
      exact ⟨True.intro, ih ((prodSig D₁ D₂).update s (t, r, Sum.inr o₂)) h⟩

/-- **`WfOpReachable⊗` from component 1's** (memo §2.5.5): any Nodup,
distinct-timestamp, all-`WfOpGen⊗` product enumeration `WfChain⊗`s from
`init⊗` — `π₁ ρ` inherits Nodup/distinct-ts/`WfOpGen₁` through the injective,
timestamp-preserving `ι₁`, component 1's VC yields `WfChain₁`, and the
interleaving lemma threads it through. No mixing. -/
theorem wfOpReachable_prod {WfOpGen₁ : Op D₁.AppOp → Prop}
    (hW₁ : WfOpReachable D₁ W₁ WfOpGen₁) :
    WfOpReachable (prodSig D₁ D₂) (prodW W₁) (prodWfOpGen WfOpGen₁) := by
  intro ρ hnd hdts hgen
  refine wfChain_prod_of_proj W₁ ρ (prodSig D₁ D₂).init
    (hW₁ (projList₁ ρ) (nodup_projList₁ hnd) ?_ ?_)
  · intro a ha b hb hne
    exact hdts (inlOp a) (mem_projList₁.mp ha) (inlOp b) (mem_projList₁.mp hb)
      (fun h => hne (inlOp_injective h))
  · intro o ho
    exact hgen (inlOp o) (mem_projList₁.mp ho)

/-! ## §O20a  Premise-discharge wrappers (memo §2.5.1 rows `hHext`/`hBA`) -/

/-- **`hHext⊗` wrapper**: a CONFIG-FREE component-1 extension discipline
("`applicable` at the witness fold extends `H₁`" — the RGA's
`canonFoldOK_append` shape) discharges the product extension obligation.
An `inl` op extends `π₁ ρ` — its `applicable⊗` at the product fold reads
`D₁.applicable` at `.1 = fold₁ (π₁ ρ)` (F1); an `inr` op is FREE — `π₁`
drops it, so `H⊗` is untouched (`H₂ = ⊤` at the cut). -/
theorem prodHext_of_hext₁ {H₁ : List (Op D₁.AppOp) → Prop}
    (hHextC₁ : ∀ (e : Op D₁.AppOp) (ev : Set (Op D₁.AppOp))
      (ρ₁ : List (Op D₁.AppOp)), listPermOf ρ₁ ev → H₁ ρ₁ →
      D₁.applicable e (applySeq D₁.toCRDTSig D₁.init ρ₁) → H₁ (ρ₁ ++ [e]))
    {evh : Set (Op (D₁.AppOp ⊕ D₂.AppOp))}
    (t : Timestamp) (r : Replica) (o : D₁.AppOp ⊕ D₂.AppOp)
    (ρ : List (Op (D₁.AppOp ⊕ D₂.AppOp)))
    (hperm : listPermOf ρ evh) (hH : prodH H₁ ρ)
    (happ : (prodSig D₁ D₂).applicable (t, r, o)
      (applySeq (prodSig D₁ D₂).toCRDTSig (prodSig D₁ D₂).init ρ)) :
    prodH H₁ (ρ ++ [(t, r, o)]) := by
  cases o with
  | inl o₁ =>
    show H₁ (projList₁ (ρ ++ [(t, r, Sum.inl o₁)]))
    rw [projList₁_append]
    show H₁ (projList₁ ρ ++ [(t, r, o₁)])
    refine hHextC₁ (t, r, o₁) (evRes₁ evh) (projList₁ ρ)
      (listPermOf_projList₁ hperm) hH ?_
    rw [applySeq_prod] at happ
    exact happ
  | inr o₂ =>
    show H₁ (projList₁ (ρ ++ [(t, r, Sum.inr o₂)]))
    rw [projList₁_append]
    show H₁ (projList₁ ρ ++ [])
    rw [List.append_nil]
    exact hH

/-- **The state-free half of `hBA⊗`**: component 1's "applicable implies
wellformed" fact gives the product's — `inl` ops read `.1` on both sides
(the quantifier over product states specializes componentwise), `inr` ops
have `W⊗ = ⊤`. The `qapplicable` half of `hBA` is the per-step honest
delivery on the PRODUCT LTS (memo §2.5.6) and stays a capstone premise. -/
theorem prodGenW_of_genW₁
    (hgenW₁ : ∀ (e : Op D₁.AppOp) (s₁ : D₁.State), D₁.applicable e s₁ → W₁ e s₁)
    (e : Op (D₁.AppOp ⊕ D₂.AppOp)) :
    ∀ s' : (prodSig D₁ D₂).State,
      (prodSig D₁ D₂).applicable e s' → prodW W₁ e s' := by
  intro s' happ
  rcases e with ⟨t, r, o⟩
  cases o with
  | inl o₁ => exact hgenW₁ (t, r, o₁) s'.1 happ
  | inr o₂ => exact True.intro

/-! ## §O20b  The product `≈`-capstone (memo §2.5.7) -/

section Capstone

variable (hP₁ : InvPres D₁ W₁) (hC₁ : CongVC D₁ E₁) (hA₁ : InvInvVC D₁ E₁ W₁)
variable (hInvT₂ : ∀ s : D₂.State, D₂.Inv s)

/-- The quotient signature of the product at the pragmatic cut — `QSig` at
`(E⊗, W⊗)` with the lifted bundle. Reducible so downstream statements match
`QSig …` syntactically (memo §2.5.3: work directly here, never form
`QSig₁ ⊗ QSig₂`). -/
noncomputable abbrev prodQSig : ConditionedMRDTSig :=
  QSig (prodEqEquiv E₁) (prodW W₁) (prodInvPres W₁ hP₁ hInvT₂)
    (prodCongVC E₁ hC₁) (prodInvInvVC E₁ W₁ hA₁)

/-- **The flat half of `HonJ⊗` is structural**: same-replica `vis`-totality
restricted along `ι₂` is a field of EVERY configuration
(`vis_total_same_replica`), so the capstone's `hHon` premise only owes the
component-1 context (the §2.5.6 supply rerun). -/
theorem prodFlatHonJ
    (Cb : Sal.Emulation.Configuration
      (prodQSig E₁ W₁ hP₁ hC₁ hA₁ hInvT₂).toCRDTSig) :
    flatHonJ D₂ (visRes₂ Cb.vis) (evRes₂ Cb.events) := by
  intro a b ha hb hne hrep
  obtain ⟨ra, sa, hLa, hsa⟩ := ha
  obtain ⟨rb, sb, hLb, hsb⟩ := hb
  exact Cb.vis_total_same_replica hLa hsa hLb hsb
    (fun h => hne (inrOp_injective h)) hrep

/-- **THE PRODUCT `≈`-CAPSTONE (pragmatic cut)** — memo §2.5.7: the generic
`RA_linearizable_up_to_eq_H` instantiated at the product parameters
`(E⊗ = ≈₁ × Eq, W⊗, H⊗ = H₁ ∘ π₁, HonJ⊗)`, consuming

* the **component-1 bundle**: `(E₁, W₁, hP₁, hC₁, hA₁, hInvCong₁)` and its
  `≈`-join `hJ₁ : EqJoinLemma3C_H D₁ E₁ W₁ H₁ HonJ₁`;
* the **flat side** through `FlatGeneric_Bridge`'s identity bundles: its
  full-closure Join Lemma `hJoin₂` enters as
  `eqJoinH_of_joinC hInvT₂ hJoin₂` (at `eqOfEq/WTop/⊤/flatHonJ`), and the
  flat half of `HonJ⊗` is discharged structurally (`prodFlatHonJ`);
* the **reachability-derived supplies over the PRODUCT LTS** as hypotheses
  (`hHon₁`, `hHext`, `hBA` — the §2.5.6 rerun is instance-phase, not the
  kit's; `hHnil` is `H₁ []` since `π₁ [] = []`).

Conclusion: `IsRALinearizable3Eq` at the product — every version of a
reachable product-`QSig` configuration is `qmk` of a representative that is
the RAW product fold of a `lo`-respecting linearization of its events, up to
`E⊗` (component 1 up to `≈₁`, component 2 literally). This is what
composes: the certificate bundle re-fed to the one generic capstone — NOT
the finished component theorems (reachability does not project, memo
§2.1.4). -/
theorem prod_ra_linearizable_up_to_eq_H
    {H₁ : List (Op D₁.AppOp) → Prop}
    {HonJ₁ : (Op D₁.AppOp → Op D₁.AppOp → Prop) → Set (Op D₁.AppOp) → Prop}
    (hInvCong₁ : ∀ {s s' : D₁.State}, E₁.eqv s s' → D₁.Inv s → D₁.Inv s')
    (hJ₁ : EqJoinLemma3C_H D₁ E₁ W₁ H₁ HonJ₁)
    (hJoin₂ : JoinLemma3C D₂ (fullClosure D₂.toCRDTSig))
    (hHon₁ : ∀ {C₀ : Configuration (prodQSig E₁ W₁ hP₁ hC₁ hA₁ hInvT₂)},
      (labeledTS3 (prodQSig E₁ W₁ hP₁ hC₁ hA₁ hInvT₂)).ReachableFrom
        (initConfig (prodQSig E₁ W₁ hP₁ hC₁ hA₁ hInvT₂) trivial) C₀ →
      HonJ₁ (visRes₁ C₀.core.vis) (evRes₁ C₀.core.events))
    (hHnil : H₁ [])
    (hHext : ∀ {C₀ C₁ : Configuration (prodQSig E₁ W₁ hP₁ hC₁ hA₁ hInvT₂)}
      {t : Timestamp} {r : Replica} {o : D₁.AppOp ⊕ D₂.AppOp}
      {v : Version} {sh : QState (prodSig D₁ D₂) (prodEqEquiv E₁)}
      {evh : Set (Op (D₁.AppOp ⊕ D₂.AppOp))},
      (labeledTS3 (prodQSig E₁ W₁ hP₁ hC₁ hA₁ hInvT₂)).ReachableFrom
        (initConfig (prodQSig E₁ W₁ hP₁ hC₁ hA₁ hInvT₂) trivial) C₀ →
      Step3 (prodQSig E₁ W₁ hP₁ hC₁ hA₁ hInvT₂) C₀ (Label3.apply t r o) C₁ →
      C₀.head r = some v → C₀.ver v = some (sh, evh) →
      ∀ ρ : List (Op (D₁.AppOp ⊕ D₂.AppOp)), listPermOf ρ evh → prodH H₁ ρ →
        (prodSig D₁ D₂).applicable (t, r, o)
          (applySeq (prodSig D₁ D₂).toCRDTSig (prodSig D₁ D₂).init ρ) →
        prodH H₁ (ρ ++ [(t, r, o)]))
    (hBA : ∀ {C₀ C₁ : Configuration (prodQSig E₁ W₁ hP₁ hC₁ hA₁ hInvT₂)}
      {t : Timestamp} {r : Replica} {o : D₁.AppOp ⊕ D₂.AppOp}
      {v : Version} {sh : QState (prodSig D₁ D₂) (prodEqEquiv E₁)}
      {evh : Set (Op (D₁.AppOp ⊕ D₂.AppOp))},
      (labeledTS3 (prodQSig E₁ W₁ hP₁ hC₁ hA₁ hInvT₂)).ReachableFrom
        (initConfig (prodQSig E₁ W₁ hP₁ hC₁ hA₁ hInvT₂) trivial) C₀ →
      Step3 (prodQSig E₁ W₁ hP₁ hC₁ hA₁ hInvT₂) C₀ (Label3.apply t r o) C₁ →
      C₀.head r = some v → C₀.ver v = some (sh, evh) →
      qapplicable (prodEqEquiv E₁) (prodW W₁) (prodInvInvVC E₁ W₁ hA₁)
          (t, r, o) sh ∧
        (∀ s' : (prodSig D₁ D₂).State,
          (prodSig D₁ D₂).applicable (t, r, o) s' → prodW W₁ (t, r, o) s'))
    (C : Configuration (prodQSig E₁ W₁ hP₁ hC₁ hA₁ hInvT₂))
    (hReach : (labeledTS3 (prodQSig E₁ W₁ hP₁ hC₁ hA₁ hInvT₂)).ReachableFrom
        (initConfig (prodQSig E₁ W₁ hP₁ hC₁ hA₁ hInvT₂) trivial) C) :
    IsRALinearizable3Eq (prodEqEquiv E₁) (prodW W₁)
      (prodInvPres W₁ hP₁ hInvT₂) (prodCongVC E₁ hC₁)
      (prodInvInvVC E₁ W₁ hA₁) C :=
  RA_linearizable_up_to_eq_H (prodH H₁)
    (prodHonJ HonJ₁ (flatHonJ D₂))
    (prodEqEquiv E₁) (prodW W₁) (prodInvPres W₁ hP₁ hInvT₂)
    (prodCongVC E₁ hC₁) (prodInvInvVC E₁ W₁ hA₁)
    (prodInvCong E₁ hInvCong₁ hInvT₂)
    (eqJoinLemma3C_H_prod E₁ W₁ hP₁ hInvT₂ hJ₁ (eqJoinH_of_joinC hInvT₂ hJoin₂))
    (fun {C₀} hr =>
      ⟨hHon₁ hr, prodFlatHonJ E₁ W₁ hP₁ hC₁ hA₁ hInvT₂ C₀.core⟩)
    hHnil
    hHext
    hBA
    C hReach

end Capstone

/-! ## Axiom audit -/

#print axioms eqJoinLemma3C_H_prod
#print axioms wfOpReachable_prod
#print axioms prodHext_of_hext₁
#print axioms prodGenW_of_genW₁
#print axioms prod_ra_linearizable_up_to_eq_H

end Sal.ConditionedMRDTs.ProductEq
