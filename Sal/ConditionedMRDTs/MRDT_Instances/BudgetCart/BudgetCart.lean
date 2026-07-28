import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.SDiff
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Sal.ConditionedMRDTs.MRDT_Instances.ORSetCore.ORSetCore
import Sal.ConditionedMRDTs.Metatheory.GenericSafety

/-!
# BudgetCart, a shopping cart with per-replica budgets

A conditioned MRDT built **by instantiation of the payload-parametric OR-set
core** (`MRDT_Instances/ORSetCore/ORSetCore.lean`, composition level L0): an
OR-set of live purchase *instances* `(ts, rep, (item, price))` (the adding
event's timestamp and replica, and the `(item, price)` payload) with a
static per-replica budget function `alloc : ℕ → ℕ`. The per-replica spend is
**derived** from the state (`bcartSpend`), not carried as a ledger: removing
an instance automatically refunds its adder.

* `add (item, price)` inserts the instance `(e.ts, e.rep, (item, price))`;
* `rem item` removes ALL live instances of `item` (production OR-set
  semantics: the effect is state-dependent);
* the three-way merge is the OR-set shape `(l ∩ a ∩ b) ∪ (a ∖ l) ∪ (b ∖ l)`;
* `rc` is add-wins: a concurrent `rem item` is linearized before an `add` of
  the same item; all other pairs are `Either`.

Three layers:

* **§1 Convergence, by instantiation.** `BudgetCart alloc` IS
  `OSCore (ℕ × ℕ) Prod.fst ℕ ℕ …`, payload `(item, price)`, key = item, the
  remaining-budget query. `add`/`rem` of the same item genuinely do not
  commute, so the discharge is the OR-set's route (`CoreVCs3CD` +
  `FeasibleDeltaVCs3` + `CDVC3` ⇒ `JoinLemma3`), proved ONCE, parametrically,
  in `ORSetCore.lean`: every convergence theorem below is a one-line
  instantiation. End-to-end: `bcart_ra_linearizable3`; catalogue capstone
  `BCart_ra_linearizable3_eq` (identity instantiation of the generic
  framework: the sig-level `Inv`/`applicable` are `⊤` per repo convention;
  the budget contract lives beside the signature, as with the bounded
  counter).
* **§9 The client contract.** `bcartSpend` (the derived per-replica spend),
  `BCartInv` (every replica within its budget), `bcartApplicable` (an `add`
  needs slack in the issuer's own budget; a `rem` needs a live instance of
  the item), plus the monotonicity lemmas: others' events never raise my
  spend, own fresh adds raise it by exactly the price.
* **§10 Safety, hypothesis-gated.** The full `SafetyStepOn` is **false** for
  the BudgetCart (see the docstring of `BCartSpendMono` for the two-event
  refutation): `CausalFold` pins only `vis`-respect, and for an rc-nontrivial
  datatype the fold of a set with concurrent same-item `add`/`rem` pairs is
  enumeration-dependent, so the issuer-spend need not transfer between the
  prefix fold and the causal-past fold. `bcart_safetyStep_of_spend_mono`
  proves `SafetyStepOn` from the explicitly-hypothesized transfer
  (`BCartSpendMono`), and `bcart_version_inv_gated` composes it with the
  generic metatheorem, gated on `CausalCanonical`, which is open for
  rc-nontrivial datatypes (the witness-maintenance species, `JoinLemma3AtC`).
  BudgetCart is the instance that forces that gate.
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

/-! ## §1. The datatype, an `OSCore` instantiation

The op/state types are DEFINITIONALLY the parametric OR-set core's at payload
`(item, price)`: `BCartElem = ℕ × ℕ × (ℕ × ℕ) = ℕ × ℕ × ℕ × ℕ` (`×` is
right-associative), so instances read exactly as
`(ts, rep, item, price)` with `q.2.2.1` the item and `q.2.2.2` the price. -/

/-- BudgetCart ops: `add (item, price)` stakes a priced instance; `rem item`
removes every live instance of `item`. Definitionally `OSOp (ℕ × ℕ)`. -/
abbrev BCartOp : Type := OSOp (ℕ × ℕ)

/-- A live purchase instance: `(ts, rep, item, price)`, the adding event's
timestamp and replica, the item, the price. Definitionally
`OSElem (ℕ × ℕ)`. -/
abbrev BCartElem : Type := OSElem (ℕ × ℕ)

/-- BudgetCart state: the finite set of live instances. -/
abbrev BCartState : Type := OSState (ℕ × ℕ)

/-- `add (item, price)` at `(ts, rep)` inserts `(ts, rep, item, price)`;
`rem item` filters every instance of `item` present at application time.
The OR-set core's update at key = item (`Prod.fst` of the payload). -/
abbrev bcartUpdate : BCartState → Op BCartOp → BCartState :=
  osUpdate Prod.fst

/-- The OR-set three-way merge on instances:
`(l ∩ a ∩ b) ∪ (a ∖ l) ∪ (b ∖ l)`. -/
abbrev bcartMergeL : BCartState → BCartState → BCartState → BCartState :=
  osMergeL

/-- Add-wins `rc`: `add`-vs-`rem` on the same item is ordered rem-first;
all other pairs `Either`. -/
abbrev bcartRc : Op BCartOp → Op BCartOp → RcRes :=
  osRc Prod.fst

/-- The derived per-replica spend: the sum of `price` over live instances
staked by replica `r`. No ledger: removing an instance refunds its adder. -/
def bcartSpend (r : ℕ) (s : BCartState) : ℕ :=
  (s.filter (fun q => q.2.1 = r)).sum (fun q => q.2.2.2)

/-- **The BudgetCart MRDT**, parameterized by the static per-replica budget
`alloc`, the OR-set core at payload `(item, price)` and key = item. The
sig-level `Inv`/`applicable` are `⊤` (repo convention: the budget contract
lives beside the signature, §9–§10); `alloc` is read by the query, which
reports the remaining budget of a replica. -/
def BudgetCart (alloc : ℕ → ℕ) : ConditionedMRDTSig :=
  OSCore (ℕ × ℕ) Prod.fst ℕ ℕ (fun s r => alloc r - bcartSpend r s)

section
variable {alloc : ℕ → ℕ}

theorem BCart_update_eq (s : BCartState) (o : Op BCartOp) :
    (BudgetCart alloc).update s o = bcartUpdate s o := rfl

theorem BCart_mergeL_eq (l a b : BCartState) :
    (BudgetCart alloc).mergeL l a b = bcartMergeL l a b := rfl

theorem BCart_init_eq : (BudgetCart alloc).init = (∅ : BCartState) := rfl

/-! ## §2–§8. Convergence, inherited from the OR-set core

Every theorem of the OR-set-route discharge (`ORSetCore.lean` §2–§8)
instantiates at `β := ℕ × ℕ`, `key := Prod.fst`: the VC bundles, the Join
Lemma, and the capstones below. Nothing item/price-specific remains to
prove. -/

theorem BCart_updateVCs : UpdateVCs (BudgetCart alloc).toCRDTSig :=
  OSCore_updateVCs

theorem BCart_coreVCs3CD : CoreVCs3CD (BudgetCart alloc) :=
  OSCore_coreVCs3CD

/-- **The feasible delta contract for the BudgetCart.** -/
theorem BCart_feasibleDeltaVCs3 : FeasibleDeltaVCs3 (BudgetCart alloc) :=
  OSCore_feasibleDeltaVCs3

/-- **`CDVC3` for the BudgetCart**, the OR-set core's maximal-event
analysis, instantiated. -/
theorem BCart_cdVC3 : CDVC3 (BudgetCart alloc) :=
  OSCore_cdVC3

/-- The ternary Join Lemma for the BudgetCart, the OR-set's route. -/
theorem BCart_joinLemma3 : JoinLemma3 (BudgetCart alloc) :=
  OSCore_joinLemma3

open LabeledTS in
/-- **End-to-end RA-linearizability for the BudgetCart** (convergence half),
for every `alloc`, by instantiation of the parametric OR-set core. -/
theorem bcart_ra_linearizable3
    (C : Configuration (BudgetCart alloc))
    (hReach : (labeledTS3 (BudgetCart alloc)).ReachableFrom
      (initConfig (BudgetCart alloc) trivial) C) :
    IsRALinearizable3 C :=
  oscore_ra_linearizable3 C hReach

end

/-! ### The conditioned capstone, identity instantiation of the generic
framework -/

section
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.GoodConfig3H
open Sal.ConditionedMRDTs.FlatGeneric

/-- **BudgetCart over the generic framework** (the catalogue capstone),
universally in `alloc`, by instantiation of the parametric OR-set core. -/
theorem BCart_ra_linearizable3_eq (alloc : ℕ → ℕ)
    (C : Configuration (QSig (eqOfEq (BudgetCart alloc))
      (WTop (BudgetCart alloc)) (invPresTop fun _ => trivial)
      (congVCEq (BudgetCart alloc)) (invInvVCTop (BudgetCart alloc))))
    (hReach : (labeledTS3 _).ReachableFrom (initConfig _ trivial) C) :
    IsRALinearizable3Eq (eqOfEq (BudgetCart alloc)) (WTop (BudgetCart alloc))
      (invPresTop fun _ => trivial) (congVCEq (BudgetCart alloc))
      (invInvVCTop (BudgetCart alloc)) C :=
  OSCore_ra_linearizable3_eq (ℕ × ℕ) Prod.fst ℕ ℕ
    (fun s r => alloc r - bcartSpend r s) C hReach

end

/-! ## §9. The client contract: derived spend, invariant, applicability -/

section
variable {alloc : ℕ → ℕ}

/-- The budget invariant: every replica's derived spend is within its
allocation. -/
def BCartInv (alloc : ℕ → ℕ) (s : BCartState) : Prop :=
  ∀ r, bcartSpend r s ≤ alloc r

/-- The client check: an `add` needs slack in the issuing replica's OWN
budget, checkable against the issuing replica's state; a `rem` needs a live
instance of the item. -/
def bcartApplicable (alloc : ℕ → ℕ) (o : Op BCartOp) (s : BCartState) : Prop :=
  match o.2.2 with
  | .add (_, price) => bcartSpend o.2.1 s + price ≤ alloc o.2.1
  | .rem item => ∃ q ∈ s, q.2.2.1 = item

theorem bcart_inv_init : BCartInv alloc (∅ : BCartState) := by
  intro r
  show bcartSpend r ∅ ≤ alloc r
  simp [bcartSpend]

/-- Spend is monotone under state inclusion (prices are non-negative). -/
theorem bcartSpend_le_of_subset {s t : BCartState} (h : s ⊆ t) (r : ℕ) :
    bcartSpend r s ≤ bcartSpend r t :=
  Finset.sum_le_sum_of_subset (Finset.filter_subset_filter _ h)

/-- A rem never raises anyone's spend: removing an instance refunds its
adder. -/
theorem bcartSpend_update_rem_le (s : BCartState) (ts rr item r : ℕ) :
    bcartSpend r (bcartUpdate s (ts, rr, OSOp.rem item)) ≤ bcartSpend r s :=
  bcartSpend_le_of_subset (Finset.filter_subset _ s) r

/-- Others' adds don't touch my spend: the inserted instance carries its own
replica. -/
theorem bcartSpend_update_add_other {r rr : ℕ} (hne : rr ≠ r)
    (s : BCartState) (ts item price : ℕ) :
    bcartSpend r (bcartUpdate s (ts, rr, OSOp.add (item, price)))
      = bcartSpend r s := by
  show bcartSpend r (insert (ts, rr, item, price) s) = bcartSpend r s
  unfold bcartSpend
  rw [Finset.filter_insert, if_neg]
  exact hne

/-- An own fresh add raises my spend by exactly the price (timestamps are
unique in executions, so the fresh-instance hypothesis is what the execution
supplies). -/
theorem bcartSpend_update_add_fresh {s : BCartState} {ts r item price : ℕ}
    (hfresh : ((ts, r, item, price) : BCartElem) ∉ s) :
    bcartSpend r (bcartUpdate s (ts, r, OSOp.add (item, price)))
      = bcartSpend r s + price := by
  show bcartSpend r (insert (ts, r, item, price) s) = bcartSpend r s + price
  unfold bcartSpend
  rw [Finset.filter_insert, if_pos rfl,
    Finset.sum_insert (fun h => hfresh (Finset.mem_of_mem_filter _ h))]
  exact Nat.add_comm _ _

/-- The unconditional add bound: an add raises my spend by at most the price
(exactly, when fresh and own; not at all otherwise). -/
theorem bcartSpend_update_add_le (s : BCartState) (ts rr item price r : ℕ) :
    bcartSpend r (bcartUpdate s (ts, rr, OSOp.add (item, price)))
      ≤ bcartSpend r s + price := by
  by_cases hr : rr = r
  · subst hr
    by_cases hmem : ((ts, rr, item, price) : BCartElem) ∈ s
    · have : bcartUpdate s (ts, rr, OSOp.add (item, price)) = s := by
        show insert (ts, rr, item, price) s = s
        exact Finset.insert_eq_self.mpr hmem
      rw [this]
      omega
    · rw [bcartSpend_update_add_fresh hmem]
  · rw [bcartSpend_update_add_other hr]
    omega

/-- An applicable step preserves the budget invariant at the SAME state: the
contract is locally maintainable at the issuing replica. -/
theorem bcartApplicable_inv_pres {s : BCartState} {o : Op BCartOp}
    (hInv : BCartInv alloc s) (happ : bcartApplicable alloc o s) :
    BCartInv alloc (bcartUpdate s o) := by
  obtain ⟨ts, rr, op⟩ := o
  intro r
  cases op with
  | add ip =>
    obtain ⟨item, price⟩ := ip
    by_cases hr : rr = r
    · subst hr
      have h1 : bcartSpend rr s + price ≤ alloc rr := happ
      have h2 := bcartSpend_update_add_le s ts rr item price rr
      omega
    · rw [bcartSpend_update_add_other hr]
      exact hInv r
  | rem item =>
    exact le_trans (bcartSpend_update_rem_le s ts rr item r) (hInv r)

/-! ## §10. Safety, hypothesis-gated

The BudgetCart's safety argument is monotone rather than equality-based:
between the causal-past fold `σP` and the prefix fold `σS`, the extras are
concurrent events, and concurrent events can only LOWER the issuer's spend
(others' adds carry their own replica; rems only remove). That argument is
sound for **canonical** (rc-respecting) folds, but `SafetyStepOn`'s
`CausalFold` hypotheses pin only `vis`-respect, and for an rc-nontrivial
datatype the fold of a set containing concurrent same-item `add`/`rem` pairs
is enumeration-dependent. The full `SafetyStepOn (BudgetCart alloc)
(BCartInv alloc) (bcartApplicable alloc)` is in fact **false**; see
`BCartSpendMono`. -/

/-- **The open transfer obligation** (the honest gap): under `SafetyStepOn`'s
prefix hypotheses, the issuer's spend at the prefix fold is bounded by its
spend at the causal-past fold.

This is NOT provable from the stated hypotheses: it is refuted by a
two-event configuration. Take `alloc r = 10`,
`past(e) = {a, k}` with `a = (1, r, add x 10)`, `k = (2, r', rem x)`
concurrent to each other, both vis-before `e = (3, r, add x' 10)`, and
`S = past(e)`. The vis-respecting enumeration `[a, k]` folds to `∅`
(spend `0`); the vis-respecting enumeration `[k, a]` folds to
`{(1, r, x, 10)}` (spend `10`). With `σP` the first fold and `σS` the
second, every `SafetyStepOn` hypothesis holds, `bcartApplicable` accepts `e`
at `σP`, `BCartInv` holds at `σS`, and `update σS e` has spend `20 > 10`.
The transfer (hence the ungated `SafetyStepOn`) fails precisely because
`CausalFold` does not orient the concurrent `rem`-before-`add` (add-wins)
pair; folds along `loOn`-respecting (rc-oriented) enumerations DO satisfy it,
which is the same witness-maintenance territory as `CausalCanonical` for
rc-nontrivial datatypes (OQ8). A fold characterization for rc-respecting
causal enumerations would discharge this hypothesis; it is left open here
and threaded explicitly. -/
def BCartSpendMono (alloc : ℕ → ℕ) : Prop :=
  ∀ (C : Configuration (BudgetCart alloc)) (E S : Set (Op BCartOp))
    (e : Op BCartOp) (σS σP : BCartState),
    (∀ a ∈ E, a ∈ C.events) →
    (∀ a b, C.vis a b → b ∈ E → a ∈ E) →
    e ∈ E → S ⊆ E → e ∉ S →
    (∀ a b, C.vis a b → b ∈ S → a ∈ S) →
    (∀ x ∈ S, ¬ C.vis e x) →
    (∀ x, C.vis x e → x ∈ S) →
    CausalFold (Configuration.core C) S σS →
    CausalFold (Configuration.core C) {e' ∈ C.events | C.vis e' e} σP →
    bcartSpend e.2.1 σS ≤ bcartSpend e.2.1 σP

/-- **The fused stability obligation, gated on the spend transfer**
(`SafetyStepOn` in its exact form, from the explicitly-hypothesized
`BCartSpendMono`): a `rem` only lowers spends; for an `add` by `r`, the
issuer's slack check at the causal-past fold transfers to the prefix fold by
the hypothesized monotonicity, and the add bound closes. The ungated
`bcart_safetyStep` does not exist: it is false (see `BCartSpendMono`). -/
theorem bcart_safetyStep_of_spend_mono (hMono : BCartSpendMono alloc) :
    SafetyStepOn (BudgetCart alloc) (BCartInv alloc) (bcartApplicable alloc) := by
  intro C E S e σS σP hEev hEcl heE hSsub heS hScl hfut hpast hσS hσP hInv happ
  obtain ⟨ts, rr, op⟩ := e
  have hmono : bcartSpend rr σS ≤ bcartSpend rr σP :=
    hMono C E S (ts, rr, op) σS σP hEev hEcl heE hSsub heS hScl hfut hpast
      hσS hσP
  intro r
  cases op with
  | add ip =>
    obtain ⟨item, price⟩ := ip
    by_cases hr : rr = r
    · subst hr
      have happ' : bcartSpend rr σP + price ≤ alloc rr := happ
      have h2 := bcartSpend_update_add_le σS ts rr item price rr
      show bcartSpend rr (bcartUpdate σS (ts, rr, OSOp.add (item, price)))
          ≤ alloc rr
      omega
    · show bcartSpend r (bcartUpdate σS (ts, rr, OSOp.add (item, price)))
          ≤ alloc r
      rw [bcartSpend_update_add_other hr]
      exact hInv r
  | rem item =>
    show bcartSpend r (bcartUpdate σS (ts, rr, OSOp.rem item)) ≤ alloc r
    exact le_trans (bcartSpend_update_rem_le σS ts rr item r) (hInv r)

/-- **The budget bound at every version, hypothesis-gated**: the composition of
the generic safety metatheorem (`version_inv_on_of_causal_canonical`) with the
gated SafetyStep.

The `CausalCanonical` hypothesis is **open for rc-nontrivial datatypes**: its
known discharges are the pointwise species (all-comm + `rc ≡ Either`,
unavailable here, the BudgetCart has a genuine `rc`) and the witness-maintenance
species (`JoinLemma3AtC`), which is unproven. The BudgetCart is the instance
that forces that gate. `BCartSpendMono` is the additional (kindred) open
transfer this instance needs because `SafetyStepOn`'s interface forgets the
rc-orientation of its folds. -/
theorem bcart_version_inv_gated (hMono : BCartSpendMono alloc)
    {C : Configuration (BudgetCart alloc)}
    (hCC : CausalCanonical C)
    (hHon : HonestAppOn (BudgetCart alloc) (bcartApplicable alloc) C)
    (hG : GoodConfig3 C) :
    ∀ (v : Version) (s : BCartState) (E : Set (Op BCartOp)),
      C.ver v = some (s, E) → BCartInv alloc s :=
  version_inv_on_of_causal_canonical bcart_inv_init
    (bcart_safetyStep_of_spend_mono hMono) hG hCC hHon

end

/-! ## Axiom audit -/

#print axioms bcart_ra_linearizable3
#print axioms BCart_ra_linearizable3_eq
#print axioms bcart_safetyStep_of_spend_mono
#print axioms bcart_version_inv_gated

end Sal.ConditionedMRDTs
