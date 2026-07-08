import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.SDiff
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Sal.ConditionedMRDTs.Metatheory.Adequacy
import Sal.ConditionedMRDTs.Metatheory.FlatGeneric_Bridge
import Sal.ConditionedMRDTs.Metatheory.GenericSafety

/-!
# BudgetCart — a shopping cart with per-replica budgets

A conditioned MRDT built directly (non-compositionally): an OR-set of live
purchase *instances* `(ts, rep, item, price)` — the adding event's timestamp
and replica, the item, the price — with a static per-replica budget function
`alloc : ℕ → ℕ`. The per-replica spend is **derived** from the state
(`bcartSpend`), not carried as a ledger: removing an instance automatically
refunds its adder.

* `add item price` inserts the instance `(e.ts, e.rep, item, price)`;
* `rem item` removes ALL live instances of `item` (production OR-set
  semantics: the effect is state-dependent);
* the three-way merge is the OR-set shape `(l ∩ a ∩ b) ∪ (a ∖ l) ∪ (b ∖ l)`;
* `rc` is add-wins: a concurrent `rem item` is linearized before an `add` of
  the same item; all other pairs are `Either`.

Three layers:

* **§1–§8 Convergence.** `add`/`rem` of the same item genuinely do not
  commute, so the discharge is the OR-set's route (`CoreVCs3CD` +
  `FeasibleDeltaVCs3` + `CDVC3` ⇒ `JoinLemma3`), re-proved over the `Finset`
  representation. End-to-end: `bcart_ra_linearizable3`; catalogue capstone
  `BCart_ra_linearizable3_eq` (identity instantiation of the generic
  framework — the sig-level `Inv`/`applicable` are `⊤` per repo convention;
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
  generic metatheorem — gated on `CausalCanonical`, which is OPEN for
  rc-nontrivial datatypes (OQ8 / `JoinLemma3AtC`, the witness-maintenance
  species of `Development/GENERIC_SAFETY_PENPAPER.md` §4.2 (P1)). BudgetCart
  is the instance that forces that gate.
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

/-! ## §1. The datatype -/

/-- BudgetCart ops: `add item price` stakes a priced instance; `rem item`
removes every live instance of `item`. -/
inductive BCartOp : Type where
  | add : ℕ → ℕ → BCartOp
  | rem : ℕ → BCartOp
deriving DecidableEq

/-- A live purchase instance: `(ts, rep, item, price)` — the adding event's
timestamp and replica, the item, the price. -/
abbrev BCartElem : Type := ℕ × ℕ × ℕ × ℕ

/-- BudgetCart state: the finite set of live instances. -/
abbrev BCartState : Type := Finset BCartElem

/-- `add item price` at `(ts, rep)` inserts `(ts, rep, item, price)`;
`rem item` filters every instance of `item` present at application time. -/
def bcartUpdate (s : BCartState) (o : Op BCartOp) : BCartState :=
  match o.2.2 with
  | .add item price => insert (o.1, o.2.1, item, price) s
  | .rem item => s.filter (fun q => q.2.2.1 ≠ item)

/-- The OR-set three-way merge on instances:
`(l ∩ a ∩ b) ∪ (a ∖ l) ∪ (b ∖ l)`. -/
def bcartMergeL (l a b : BCartState) : BCartState :=
  ((l ∩ a) ∩ b) ∪ ((a \ l) ∪ (b \ l))

/-- Add-wins `rc`: `add`-vs-`rem` on the same item is ordered rem-first;
all other pairs `Either`. -/
def bcartRc (o₁ o₂ : Op BCartOp) : RcRes :=
  match o₁.2.2, o₂.2.2 with
  | .add x _, .rem y => if x = y then RcRes.Snd_then_fst else RcRes.Either
  | .rem x, .add y _ => if x = y then RcRes.Fst_then_snd else RcRes.Either
  | _, _ => RcRes.Either

/-- The derived per-replica spend: the sum of `price` over live instances
staked by replica `r`. No ledger — removing an instance refunds its adder. -/
def bcartSpend (r : ℕ) (s : BCartState) : ℕ :=
  (s.filter (fun q => q.2.1 = r)).sum (fun q => q.2.2.2)

/-- **The BudgetCart MRDT**, parameterized by the static per-replica budget
`alloc`. The sig-level `Inv`/`applicable` are `⊤` (repo convention — the
budget contract lives beside the signature, §9–§10); `alloc` is read by the
query, which reports the remaining budget of a replica. -/
def BudgetCart (alloc : ℕ → ℕ) : ConditionedMRDTSig where
  State := BCartState
  dec_state := inferInstance
  init := (∅ : BCartState)
  AppOp := BCartOp
  dec_op := inferInstance
  Query := ℕ
  Value := ℕ
  update := bcartUpdate
  merge := fun a b => bcartMergeL ∅ a b
  query := fun s r => alloc r - bcartSpend r s
  rc := bcartRc
  mergeL := bcartMergeL
  merge_init_slice := fun _ _ => rfl
  Inv := fun _ => True
  applicable := fun _ _ => True

section
variable {alloc : ℕ → ℕ}

theorem BCart_update_eq (s : BCartState) (o : Op BCartOp) :
    (BudgetCart alloc).update s o = bcartUpdate s o := rfl

theorem BCart_mergeL_eq (l a b : BCartState) :
    (BudgetCart alloc).mergeL l a b = bcartMergeL l a b := rfl

theorem BCart_init_eq : (BudgetCart alloc).init = (∅ : BCartState) := rfl

/-! Membership characterizations — everything downstream is propositional
logic over these. -/

theorem mem_bcartUpdate_add {s : BCartState} {q : BCartElem}
    {ts r item price : ℕ} :
    q ∈ bcartUpdate s (ts, r, BCartOp.add item price)
      ↔ q = (ts, r, item, price) ∨ q ∈ s := by
  show q ∈ insert (ts, r, item, price) s ↔ _
  exact Finset.mem_insert

theorem mem_bcartUpdate_rem {s : BCartState} {q : BCartElem} {ts r item : ℕ} :
    q ∈ bcartUpdate s (ts, r, BCartOp.rem item) ↔ q ∈ s ∧ q.2.2.1 ≠ item := by
  show q ∈ s.filter (fun q => q.2.2.1 ≠ item) ↔ _
  exact Finset.mem_filter

theorem mem_bcartMergeL {l a b : BCartState} {q : BCartElem} :
    q ∈ bcartMergeL l a b ↔
      (q ∈ l ∧ q ∈ a ∧ q ∈ b) ∨ (q ∈ a ∧ q ∉ l) ∨ (q ∈ b ∧ q ∉ l) := by
  unfold bcartMergeL
  rw [Finset.mem_union, Finset.mem_union, Finset.mem_inter, Finset.mem_inter,
    Finset.mem_sdiff, Finset.mem_sdiff]
  tauto

/-- BudgetCart `mergeL` is commutative in its branch arguments. -/
theorem BCart_mergeL_comm (l a b : (BudgetCart alloc).State) :
    (BudgetCart alloc).mergeL l a b = (BudgetCart alloc).mergeL l b a := by
  show bcartMergeL l a b = bcartMergeL l b a
  apply Finset.ext
  intro q
  rw [mem_bcartMergeL, mem_bcartMergeL]
  tauto

/-! ## §2. The fold over the concrete state, and pointwise transport -/

/-- The fold of an event list, stated over `BCartState` (definitionally
`applySeq (BudgetCart alloc).toCRDTSig`, but `Finset` instances resolve). -/
def bcartFold (s : BCartState) (π : List (Op BCartOp)) : BCartState :=
  π.foldl bcartUpdate s

theorem bcartFold_eq_applySeq (s : BCartState) (π : List (Op BCartOp)) :
    applySeq (BudgetCart alloc).toCRDTSig s π = bcartFold s π := rfl

theorem bcartFold_append_single (s : BCartState) (π : List (Op BCartOp))
    (o : Op BCartOp) :
    bcartFold s (π ++ [o]) = bcartUpdate (bcartFold s π) o := by
  simp [bcartFold, List.foldl_append]

/-- Updates transport pointwise membership agreement. -/
theorem bcartUpdate_pointwise (a b : BCartState) (o : Op BCartOp)
    (q : BCartElem) (h : q ∈ a ↔ q ∈ b) :
    q ∈ bcartUpdate a o ↔ q ∈ bcartUpdate b o := by
  rcases o with ⟨ts, r, op⟩
  cases op with
  | add item price => rw [mem_bcartUpdate_add, mem_bcartUpdate_add, h]
  | rem item => rw [mem_bcartUpdate_rem, mem_bcartUpdate_rem, h]

/-- Folds transport pointwise membership agreement. -/
theorem bcartFold_agree {a b : BCartState}
    (π : List (Op BCartOp)) (q : BCartElem) (h : q ∈ a ↔ q ∈ b) :
    q ∈ bcartFold a π ↔ q ∈ bcartFold b π := by
  induction π generalizing a b with
  | nil => exact h
  | cons o π ih => exact ih (bcartUpdate_pointwise a b o q h)

/-! ## §3. Commutation classification -/

theorem BCart_commutes_symm {o₁ o₂ : Op (BudgetCart alloc).AppOp}
    (h : (BudgetCart alloc).toCRDTSig.commutes o₁ o₂) :
    (BudgetCart alloc).toCRDTSig.commutes o₂ o₁ :=
  fun s => (h s).symm

theorem BCart_comm_add_add (ts₁ r₁ x₁ p₁ ts₂ r₂ x₂ p₂ : ℕ) :
    (BudgetCart alloc).toCRDTSig.commutes (ts₁, r₁, BCartOp.add x₁ p₁)
      (ts₂, r₂, BCartOp.add x₂ p₂) := by
  intro s
  show bcartUpdate (bcartUpdate s (ts₁, r₁, BCartOp.add x₁ p₁))
        (ts₂, r₂, BCartOp.add x₂ p₂)
      = bcartUpdate (bcartUpdate s (ts₂, r₂, BCartOp.add x₂ p₂))
        (ts₁, r₁, BCartOp.add x₁ p₁)
  apply Finset.ext
  intro q
  simp only [mem_bcartUpdate_add]
  tauto

theorem BCart_comm_rem_rem (ts₁ r₁ x₁ ts₂ r₂ x₂ : ℕ) :
    (BudgetCart alloc).toCRDTSig.commutes (ts₁, r₁, BCartOp.rem x₁)
      (ts₂, r₂, BCartOp.rem x₂) := by
  intro s
  show bcartUpdate (bcartUpdate s (ts₁, r₁, BCartOp.rem x₁))
        (ts₂, r₂, BCartOp.rem x₂)
      = bcartUpdate (bcartUpdate s (ts₂, r₂, BCartOp.rem x₂))
        (ts₁, r₁, BCartOp.rem x₁)
  apply Finset.ext
  intro q
  rw [mem_bcartUpdate_rem, mem_bcartUpdate_rem, mem_bcartUpdate_rem,
    mem_bcartUpdate_rem]
  tauto

theorem BCart_comm_add_rem_ne (ts₁ r₁ x p ts₂ r₂ y : ℕ) (hxy : x ≠ y) :
    (BudgetCart alloc).toCRDTSig.commutes (ts₁, r₁, BCartOp.add x p)
      (ts₂, r₂, BCartOp.rem y) := by
  intro s
  show bcartUpdate (bcartUpdate s (ts₁, r₁, BCartOp.add x p))
        (ts₂, r₂, BCartOp.rem y)
      = bcartUpdate (bcartUpdate s (ts₂, r₂, BCartOp.rem y))
        (ts₁, r₁, BCartOp.add x p)
  apply Finset.ext
  intro q
  rw [mem_bcartUpdate_rem, mem_bcartUpdate_add, mem_bcartUpdate_add,
    mem_bcartUpdate_rem]
  constructor
  · rintro ⟨rfl | hq, hne⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨hq, hne⟩
  · rintro (rfl | ⟨hq, hne⟩)
    · exact ⟨Or.inl rfl, hxy⟩
    · exact ⟨Or.inr hq, hne⟩

/-- Same-item `add`/`rem` genuinely do not commute (witness: the empty
cart). -/
theorem BCart_ncomm_add_rem (ts₁ r₁ x p ts₂ r₂ : ℕ) :
    ¬ (BudgetCart alloc).toCRDTSig.commutes (ts₁, r₁, BCartOp.add x p)
      (ts₂, r₂, BCartOp.rem x) := by
  intro h
  have h0 : bcartUpdate (bcartUpdate (∅ : BCartState)
        (ts₁, r₁, BCartOp.add x p)) (ts₂, r₂, BCartOp.rem x)
      = bcartUpdate (bcartUpdate (∅ : BCartState)
        (ts₂, r₂, BCartOp.rem x)) (ts₁, r₁, BCartOp.add x p) :=
    h (∅ : BCartState)
  have hmem : ((ts₁, r₁, x, p) : BCartElem)
      ∈ bcartUpdate (bcartUpdate (∅ : BCartState)
        (ts₂, r₂, BCartOp.rem x)) (ts₁, r₁, BCartOp.add x p) := by
    rw [mem_bcartUpdate_add]
    exact Or.inl rfl
  rw [← h0, mem_bcartUpdate_rem] at hmem
  exact hmem.2 rfl

/-- The classification: an `add x _` fails to commute only with `rem x`. -/
theorem BCart_ncomm_add_dest {ts r x p : ℕ} {o : Op (BudgetCart alloc).AppOp}
    (h : ¬ (BudgetCart alloc).toCRDTSig.commutes (ts, r, BCartOp.add x p) o) :
    o.2.2 = BCartOp.rem x := by
  rcases o with ⟨ts', r', op⟩
  cases op with
  | add y q => exact absurd (BCart_comm_add_add ts r x p ts' r' y q) h
  | rem y =>
    by_cases hxy : x = y
    · subst hxy; rfl
    · exact absurd (BCart_comm_add_rem_ne ts r x p ts' r' y hxy) h

/-- The classification: a `rem x` fails to commute only with an `add x _`. -/
theorem BCart_ncomm_rem_dest {ts r x : ℕ} {o : Op (BudgetCart alloc).AppOp}
    (h : ¬ (BudgetCart alloc).toCRDTSig.commutes (ts, r, BCartOp.rem x) o) :
    ∃ p, o.2.2 = BCartOp.add x p := by
  rcases o with ⟨ts', r', op⟩
  cases op with
  | add y q =>
    by_cases hyx : y = x
    · subst hyx; exact ⟨q, rfl⟩
    · exact absurd
        (BCart_commutes_symm (BCart_comm_add_rem_ne ts' r' y q ts r x hyx)) h
  | rem y => exact absurd (BCart_comm_rem_rem ts r x ts' r' y) h

/-! ## §4. The update layer of `CoreVCs3CD` -/

theorem BCart_no_rc_chain :
    ∀ o₁ o₂ o₃ : Op (BudgetCart alloc).AppOp,
      distinctOps o₁ o₂ → distinctOps o₂ o₃ →
      ¬ ((BudgetCart alloc).toCRDTSig.rc o₁ o₂ = RcRes.Fst_then_snd ∧
         (BudgetCart alloc).toCRDTSig.rc o₂ o₃ = RcRes.Fst_then_snd) := by
  rintro ⟨ts₁, r₁, op₁⟩ ⟨ts₂, r₂, op₂⟩ ⟨ts₃, r₃, op₃⟩ _ _ ⟨h1, h2⟩
  cases op₂ with
  | add x₂ p₂ =>
    cases op₃ with
    | add x₃ p₃ => exact RcRes.noConfusion (show RcRes.Either = _ from h2)
    | rem x₃ =>
      have h2' : (if x₂ = x₃ then RcRes.Snd_then_fst else RcRes.Either)
          = RcRes.Fst_then_snd := h2
      by_cases hx : x₂ = x₃
      · rw [if_pos hx] at h2'; exact RcRes.noConfusion h2'
      · rw [if_neg hx] at h2'; exact RcRes.noConfusion h2'
  | rem x₂ =>
    cases op₁ with
    | add x₁ p₁ =>
      have h1' : (if x₁ = x₂ then RcRes.Snd_then_fst else RcRes.Either)
          = RcRes.Fst_then_snd := h1
      by_cases hx : x₁ = x₂
      · rw [if_pos hx] at h1'; exact RcRes.noConfusion h1'
      · rw [if_neg hx] at h1'; exact RcRes.noConfusion h1'
    | rem x₁ => exact RcRes.noConfusion (show RcRes.Either = _ from h1)

theorem BCart_rc_non_comm_directional :
    ∀ o₁ o₂ : Op (BudgetCart alloc).AppOp,
      distinctOps o₁ o₂ → differentReplicas o₁ o₂ →
      (¬ (BudgetCart alloc).toCRDTSig.commutes o₁ o₂ ↔
       ((BudgetCart alloc).toCRDTSig.rc o₁ o₂ = RcRes.Fst_then_snd ∨
        (BudgetCart alloc).toCRDTSig.rc o₂ o₁ = RcRes.Fst_then_snd)) := by
  intro o₁ o₂ _ _
  constructor
  · intro hnc
    rcases o₁ with ⟨ts₁, r₁, op₁⟩
    cases op₁ with
    | add x p =>
      have h2 := BCart_ncomm_add_dest hnc
      rcases o₂ with ⟨ts₂, r₂, op₂⟩
      have h2' : op₂ = BCartOp.rem x := h2
      subst h2'
      right
      show (if x = x then RcRes.Fst_then_snd else RcRes.Either)
          = RcRes.Fst_then_snd
      rw [if_pos rfl]
    | rem x =>
      obtain ⟨p, h2⟩ := BCart_ncomm_rem_dest hnc
      rcases o₂ with ⟨ts₂, r₂, op₂⟩
      have h2' : op₂ = BCartOp.add x p := h2
      subst h2'
      left
      show (if x = x then RcRes.Fst_then_snd else RcRes.Either)
          = RcRes.Fst_then_snd
      rw [if_pos rfl]
  · rintro (h | h)
    · rcases o₁ with ⟨ts₁, r₁, op₁⟩
      rcases o₂ with ⟨ts₂, r₂, op₂⟩
      cases op₁ with
      | add x₁ p₁ =>
        exfalso
        cases op₂ with
        | add x₂ p₂ => exact RcRes.noConfusion (show RcRes.Either = _ from h)
        | rem x₂ =>
          have h' : (if x₁ = x₂ then RcRes.Snd_then_fst else RcRes.Either)
              = RcRes.Fst_then_snd := h
          by_cases hx : x₁ = x₂
          · rw [if_pos hx] at h'; exact RcRes.noConfusion h'
          · rw [if_neg hx] at h'; exact RcRes.noConfusion h'
      | rem x₁ =>
        cases op₂ with
        | add x₂ p₂ =>
          have h' : (if x₁ = x₂ then RcRes.Fst_then_snd else RcRes.Either)
              = RcRes.Fst_then_snd := h
          by_cases hx : x₁ = x₂
          · subst hx
            intro hc
            exact BCart_ncomm_add_rem ts₂ r₂ x₁ p₂ ts₁ r₁
              (BCart_commutes_symm hc)
          · rw [if_neg hx] at h'
            exact absurd h' (fun hh => RcRes.noConfusion hh)
        | rem x₂ =>
          exact absurd (show RcRes.Either = _ from h)
            (fun hh => RcRes.noConfusion hh)
    · rcases o₁ with ⟨ts₁, r₁, op₁⟩
      rcases o₂ with ⟨ts₂, r₂, op₂⟩
      cases op₂ with
      | add x₂ p₂ =>
        exfalso
        cases op₁ with
        | add x₁ p₁ => exact RcRes.noConfusion (show RcRes.Either = _ from h)
        | rem x₁ =>
          have h' : (if x₂ = x₁ then RcRes.Snd_then_fst else RcRes.Either)
              = RcRes.Fst_then_snd := h
          by_cases hx : x₂ = x₁
          · rw [if_pos hx] at h'; exact RcRes.noConfusion h'
          · rw [if_neg hx] at h'; exact RcRes.noConfusion h'
      | rem x₂ =>
        cases op₁ with
        | add x₁ p₁ =>
          have h' : (if x₂ = x₁ then RcRes.Fst_then_snd else RcRes.Either)
              = RcRes.Fst_then_snd := h
          by_cases hx : x₂ = x₁
          · subst hx
            exact BCart_ncomm_add_rem ts₁ r₁ x₂ p₁ ts₂ r₂
          · rw [if_neg hx] at h'
            exact absurd h' (fun hh => RcRes.noConfusion hh)
        | rem x₁ =>
          exact absurd (show RcRes.Either = _ from h)
            (fun hh => RcRes.noConfusion hh)

/-- `cond_comm_lift`: the `rem x`/`add x p` swap perturbs the state by at most
the fresh instance; the perturbation is invisible off that instance, and the
final non-commuting `e''` (= `rem x`) erases it. -/
theorem BCart_cond_comm_lift :
    ∀ (s : (BudgetCart alloc).State) (e e' e'' : Op (BudgetCart alloc).AppOp)
      (π : List (Op (BudgetCart alloc).AppOp)),
      distinctOps e e' → distinctOps e e'' → distinctOps e' e'' →
      (BudgetCart alloc).toCRDTSig.rc e e' = RcRes.Fst_then_snd →
      ¬ (BudgetCart alloc).toCRDTSig.commutes e' e'' →
      (BudgetCart alloc).update (applySeq (BudgetCart alloc).toCRDTSig
          ((BudgetCart alloc).update ((BudgetCart alloc).update s e') e) π) e''
        = (BudgetCart alloc).update (applySeq (BudgetCart alloc).toCRDTSig
            ((BudgetCart alloc).update ((BudgetCart alloc).update s e) e') π)
            e'' := by
  intro s e e' e'' π _ _ _ hrc hnc
  rcases e with ⟨ts₁, r₁, op₁⟩
  rcases e' with ⟨ts₂, r₂, op₂⟩
  -- rc = Fst forces (rem x, add x p)
  cases op₁ with
  | add x₁ p₁ =>
    exfalso
    cases op₂ with
    | add x₂ p₂ => exact RcRes.noConfusion (show RcRes.Either = _ from hrc)
    | rem x₂ =>
      have h' : (if x₁ = x₂ then RcRes.Snd_then_fst else RcRes.Either)
          = RcRes.Fst_then_snd := hrc
      by_cases hx : x₁ = x₂
      · rw [if_pos hx] at h'; exact RcRes.noConfusion h'
      · rw [if_neg hx] at h'; exact RcRes.noConfusion h'
  | rem x₁ =>
    cases op₂ with
    | rem x₂ =>
      exact absurd (show RcRes.Either = _ from hrc)
        (fun hh => RcRes.noConfusion hh)
    | add x₂ p₂ =>
      have h' : (if x₁ = x₂ then RcRes.Fst_then_snd else RcRes.Either)
          = RcRes.Fst_then_snd := hrc
      by_cases hx : x₁ = x₂
      swap
      · rw [if_neg hx] at h'; exact absurd h' (fun hh => RcRes.noConfusion hh)
      · subst hx
        -- e'' = rem x₁
        have hdest := BCart_ncomm_add_dest hnc
        rcases e'' with ⟨ts₃, r₃, op₃⟩
        have hdest' : op₃ = BCartOp.rem x₁ := hdest
        subst hdest'
        show bcartUpdate (bcartFold
            (bcartUpdate (bcartUpdate s (ts₂, r₂, BCartOp.add x₁ p₂))
              (ts₁, r₁, BCartOp.rem x₁)) π) (ts₃, r₃, BCartOp.rem x₁)
          = bcartUpdate (bcartFold
              (bcartUpdate (bcartUpdate s (ts₁, r₁, BCartOp.rem x₁))
                (ts₂, r₂, BCartOp.add x₁ p₂)) π) (ts₃, r₃, BCartOp.rem x₁)
        apply Finset.ext
        intro q
        rw [mem_bcartUpdate_rem, mem_bcartUpdate_rem]
        by_cases hq : q.2.2.1 = x₁
        · simp [hq]
        · have hagree :
              q ∈ bcartUpdate (bcartUpdate s (ts₂, r₂, BCartOp.add x₁ p₂))
                (ts₁, r₁, BCartOp.rem x₁)
              ↔ q ∈ bcartUpdate (bcartUpdate s (ts₁, r₁, BCartOp.rem x₁))
                (ts₂, r₂, BCartOp.add x₁ p₂) := by
            have hqp : q ≠ ((ts₂, r₂, x₁, p₂) : BCartElem) := by
              intro h
              exact hq (by rw [h])
            rw [mem_bcartUpdate_rem, mem_bcartUpdate_add,
              mem_bcartUpdate_add, mem_bcartUpdate_rem]
            simp [hqp]
          rw [bcartFold_agree π q hagree]

/-! ## §5. Fold facts -/

/-- **Bound**: a live instance names its adding event, which is in the
list. -/
theorem BCart_fold_bound : ∀ {ρ : List (Op BCartOp)} {q : BCartElem},
    q ∈ bcartFold ∅ ρ → (q.1, q.2.1, BCartOp.add q.2.2.1 q.2.2.2) ∈ ρ := by
  intro ρ
  induction ρ using List.reverseRecOn with
  | nil => intro q h; exact absurd h (Finset.notMem_empty q)
  | append_singleton ρ o ih =>
    intro q h
    rw [bcartFold_append_single] at h
    rcases o with ⟨ts, rid, op⟩
    cases op with
    | add item price =>
      rcases mem_bcartUpdate_add.mp h with hq | hq
      · subst hq
        exact List.mem_append_right _ List.mem_cons_self
      · exact List.mem_append_left _ (ih hq)
    | rem item =>
      exact List.mem_append_left _ (ih (mem_bcartUpdate_rem.mp h).1)

/-- A dead instance stays dead if its (unique) adding event does not occur. -/
theorem BCart_fold_stays_out {q : BCartElem} :
    ∀ (β : List (Op BCartOp)) (s : BCartState), q ∉ s →
      (∀ o ∈ β, o ≠ (q.1, q.2.1, BCartOp.add q.2.2.1 q.2.2.2)) →
      q ∉ bcartFold s β := by
  intro β
  induction β with
  | nil => intro s hs _; exact hs
  | cons o β ih =>
    intro s hs hβ
    have hupd : q ∉ bcartUpdate s o := by
      rcases o with ⟨ts, rid, op⟩
      cases op with
      | add item price =>
        intro h
        rcases mem_bcartUpdate_add.mp h with hq | hq
        · exact hβ _ List.mem_cons_self (by rw [hq])
        · exact hs hq
      | rem item =>
        intro h
        exact hs (mem_bcartUpdate_rem.mp h).1
    exact ih (bcartUpdate s o) hupd
      (fun o' ho' => hβ o' (List.mem_cons_of_mem _ ho'))

/-- A live instance stays live if no same-item rem follows. -/
theorem BCart_fold_stays_in {q : BCartElem} :
    ∀ (β : List (Op BCartOp)) (s : BCartState), q ∈ s →
      (∀ o ∈ β, o.2.2 ≠ BCartOp.rem q.2.2.1) →
      q ∈ bcartFold s β := by
  intro β
  induction β with
  | nil => intro s hs _; exact hs
  | cons o β ih =>
    intro s hs hβ
    have hupd : q ∈ bcartUpdate s o := by
      rcases o with ⟨ts, rid, op⟩
      cases op with
      | add item price =>
        rw [mem_bcartUpdate_add]
        exact Or.inr hs
      | rem item =>
        rw [mem_bcartUpdate_rem]
        refine ⟨hs, ?_⟩
        intro h
        exact hβ _ List.mem_cons_self (by rw [h])
    exact ih (bcartUpdate s o) hupd
      (fun o' ho' => hβ o' (List.mem_cons_of_mem _ ho'))

/-! ## §6. The canonical-state σ-facts -/

/-- Live instances come from adds of the set. -/
theorem BCart_canonical_bound
    {C : Sal.Emulation.Configuration (BudgetCart alloc).toCRDTSig}
    {F : Set (Op BCartOp)} {s : BCartState} {q : BCartElem}
    (hs : IsCanonicalState C F s) (hq : q ∈ s) :
    (q.1, q.2.1, BCartOp.add q.2.2.1 q.2.2.2) ∈ F := by
  obtain ⟨ρ, hperm, -, hfold⟩ := hs
  have hf : bcartFold ∅ ρ = s := hfold
  rw [← hf] at hq
  exact (hperm.2 _).mp (BCart_fold_bound hq)

/-- **Kill**: a live instance admits no same-item rem vis-after its add. -/
theorem BCart_live_no_later_rem
    {C : Sal.Emulation.Configuration (BudgetCart alloc).toCRDTSig}
    {F : Set (Op BCartOp)} {s : BCartState} {q : BCartElem}
    (hs : IsCanonicalState C F s) (hq : q ∈ s)
    (haF : (q.1, q.2.1, BCartOp.add q.2.2.1 q.2.2.2) ∈ F)
    {tsr rdr : ℕ}
    (hrF : (tsr, rdr, BCartOp.rem q.2.2.1) ∈ F)
    (hvis : C.vis (q.1, q.2.1, BCartOp.add q.2.2.1 q.2.2.2)
      (tsr, rdr, BCartOp.rem q.2.2.1)) :
    False := by
  obtain ⟨ρ, hperm, hresp, hfold⟩ := hs
  have hf : bcartFold ∅ ρ = s := hfold
  rw [← hf] at hq
  have hne_ar : ((q.1, q.2.1, BCartOp.add q.2.2.1 q.2.2.2) : Op BCartOp)
      ≠ (tsr, rdr, BCartOp.rem q.2.2.1) := by
    intro h
    have := congrArg (fun o : Op BCartOp => o.2.2) h
    exact BCartOp.noConfusion this
  have hnc : ¬ (BudgetCart alloc).toCRDTSig.commutes
      (q.1, q.2.1, BCartOp.add q.2.2.1 q.2.2.2)
      (tsr, rdr, BCartOp.rem q.2.2.1) :=
    BCart_ncomm_add_rem q.1 q.2.1 q.2.2.1 q.2.2.2 tsr rdr
  have hedge : loOn C F (q.1, q.2.1, BCartOp.add q.2.2.1 q.2.2.2)
      (tsr, rdr, BCartOp.rem q.2.2.1) := Or.inl ⟨hvis, hnc⟩
  have hrρ : ((tsr, rdr, BCartOp.rem q.2.2.1) : Op BCartOp) ∈ ρ :=
    (hperm.2 _).mpr hrF
  obtain ⟨α, β, hsplit⟩ := List.append_of_mem hrρ
  subst hsplit
  have haρ : ((q.1, q.2.1, BCartOp.add q.2.2.1 q.2.2.2) : Op BCartOp)
      ∈ α ++ (tsr, rdr, BCartOp.rem q.2.2.1) :: β := (hperm.2 _).mpr haF
  have hmid := List.pairwise_cons.mp (List.pairwise_append.mp hresp).2.1
  have haα : ((q.1, q.2.1, BCartOp.add q.2.2.1 q.2.2.2) : Op BCartOp) ∈ α := by
    rcases List.mem_append.mp haρ with h | h
    · exact h
    · rcases List.mem_cons.mp h with h | h
      · exact absurd h hne_ar
      · exact absurd hedge (hmid.1 _ h)
  have hstep : bcartFold ∅ (α ++ (tsr, rdr, BCartOp.rem q.2.2.1) :: β)
      = bcartFold (bcartUpdate (bcartFold ∅ α)
          (tsr, rdr, BCartOp.rem q.2.2.1)) β := by
    simp [bcartFold, List.foldl_append]
  rw [hstep] at hq
  have hkill : q ∉ bcartUpdate (bcartFold ∅ α)
      (tsr, rdr, BCartOp.rem q.2.2.1) := by
    intro h
    exact (mem_bcartUpdate_rem.mp h).2 rfl
  have hnoadd : ∀ o ∈ β,
      o ≠ (q.1, q.2.1, BCartOp.add q.2.2.1 q.2.2.2) := by
    intro o ho hoa
    rw [hoa] at ho
    have hnd := hperm.1
    rw [List.nodup_append] at hnd
    exact hnd.2.2 _ haα _ (List.mem_cons_of_mem _ ho) rfl
  exact BCart_fold_stays_out β _ hkill hnoadd hq

/-- **Live**: an add with no same-item rem vis-after it yields a live
instance. -/
theorem BCart_no_later_kill_live
    {C : Sal.Emulation.Configuration (BudgetCart alloc).toCRDTSig}
    {F : Set (Op BCartOp)} {s : BCartState} {q : BCartElem}
    (hs : IsCanonicalState C F s)
    (haF : (q.1, q.2.1, BCartOp.add q.2.2.1 q.2.2.2) ∈ F)
    (hno : ∀ r ∈ F, (r : Op BCartOp).2.2 = BCartOp.rem q.2.2.1 →
      ¬ C.vis (q.1, q.2.1, BCartOp.add q.2.2.1 q.2.2.2) r) :
    q ∈ s := by
  obtain ⟨ρ, hperm, hresp, hfold⟩ := hs
  have hf : bcartFold ∅ ρ = s := hfold
  rw [← hf]
  have haρ : ((q.1, q.2.1, BCartOp.add q.2.2.1 q.2.2.2) : Op BCartOp) ∈ ρ :=
    (hperm.2 _).mpr haF
  obtain ⟨α, β, hsplit⟩ := List.append_of_mem haρ
  subst hsplit
  have hcons := List.pairwise_cons.mp (List.pairwise_append.mp hresp).2.1
  -- no same-item rem in β
  have hnorem : ∀ o ∈ β, (o : Op BCartOp).2.2 ≠ BCartOp.rem q.2.2.1 := by
    intro o ho hoT
    have hoF : o ∈ F := (hperm.2 o).mp
      (List.mem_append_right _ (List.mem_cons_of_mem _ ho))
    have hnovis : ¬ C.vis (q.1, q.2.1, BCartOp.add q.2.2.1 q.2.2.2) o :=
      hno o hoF hoT
    rcases o with ⟨tso, rdo, opo⟩
    have hoT' : opo = BCartOp.rem q.2.2.1 := hoT
    subst hoT'
    have hnc_oa : ¬ (BudgetCart alloc).toCRDTSig.commutes
        (tso, rdo, BCartOp.rem q.2.2.1)
        (q.1, q.2.1, BCartOp.add q.2.2.1 q.2.2.2) :=
      fun h => BCart_ncomm_add_rem q.1 q.2.1 q.2.2.1 q.2.2.2 tso rdo
        (BCart_commutes_symm h)
    have hedge : loOn C F (tso, rdo, BCartOp.rem q.2.2.1)
        (q.1, q.2.1, BCartOp.add q.2.2.1 q.2.2.2) := by
      by_cases hvo : C.vis (tso, rdo, BCartOp.rem q.2.2.1)
          (q.1, q.2.1, BCartOp.add q.2.2.1 q.2.2.2)
      · exact Or.inl ⟨hvo, hnc_oa⟩
      · refine Or.inr ⟨hvo, hnovis, ?_, ?_⟩
        · show (if q.2.2.1 = q.2.2.1 then RcRes.Fst_then_snd else RcRes.Either)
            = RcRes.Fst_then_snd
          rw [if_pos rfl]
        · rintro ⟨e₃, he₃F, hve₃, hnce₃⟩
          have h₃T := BCart_ncomm_add_dest hnce₃
          exact hno e₃ he₃F h₃T hve₃
    exact hcons.1 _ ho hedge
  have hstep : bcartFold ∅
      (α ++ (q.1, q.2.1, BCartOp.add q.2.2.1 q.2.2.2) :: β)
      = bcartFold (bcartUpdate (bcartFold ∅ α)
          (q.1, q.2.1, BCartOp.add q.2.2.1 q.2.2.2)) β := by
    simp [bcartFold, List.foldl_append]
  rw [hstep]
  refine BCart_fold_stays_in β _ ?_ hnorem
  rw [mem_bcartUpdate_add]
  exact Or.inl rfl

/-! ## §7. The maximal-rem trichotomy and `CDVC3` -/

/-- For a maximal `rem x`, every live `x`-instance of `σ(U∖e)` is live in the
punctured downset. -/
theorem BCart_rem_max_trichotomy
    {C : Sal.Emulation.Configuration (BudgetCart alloc).toCRDTSig}
    {U : Set (Op BCartOp)} {A B : BCartState}
    {ts rid x : ℕ}
    (h_cl : ∀ a b, C.vis a b → ¬ (BudgetCart alloc).toCRDTSig.commutes a b →
      b ∈ U → a ∈ U)
    (h_e : (ts, rid, BCartOp.rem x) ∈ U)
    (h_max : ∀ y ∈ U, y ≠ (ts, rid, BCartOp.rem x) →
      ¬ loOn C U (ts, rid, BCartOp.rem x) y)
    (hA : IsCanonicalState C (U \ {(ts, rid, BCartOp.rem x)}) A)
    (hB : IsCanonicalState C
      (downset C (ts, rid, BCartOp.rem x) \ {(ts, rid, BCartOp.rem x)}) B)
    {q : BCartElem} (hqx : q.2.2.1 = x) (hqA : q ∈ A) :
    q ∈ B := by
  subst hqx
  have h_dsub : downset C (ts, rid, BCartOp.rem q.2.2.1) ⊆ U :=
    downset_subset h_cl h_e
  -- the (unique, self-naming) add of the live instance
  have haU' := BCart_canonical_bound hA hqA
  have hane : ((q.1, q.2.1, BCartOp.add q.2.2.1 q.2.2.2) : Op BCartOp)
      ≠ (ts, rid, BCartOp.rem q.2.2.1) := haU'.2
  have hnc_ae : ¬ (BudgetCart alloc).toCRDTSig.commutes
      (q.1, q.2.1, BCartOp.add q.2.2.1 q.2.2.2)
      (ts, rid, BCartOp.rem q.2.2.1) :=
    BCart_ncomm_add_rem q.1 q.2.1 q.2.2.1 q.2.2.2 ts rid
  by_cases hva : C.vis (q.1, q.2.1, BCartOp.add q.2.2.1 q.2.2.2)
      (ts, rid, BCartOp.rem q.2.2.1)
  · -- vis-before: the add is in the punctured downset and live there
    have haD : ((q.1, q.2.1, BCartOp.add q.2.2.1 q.2.2.2) : Op BCartOp)
        ∈ downset C (ts, rid, BCartOp.rem q.2.2.1)
          \ {(ts, rid, BCartOp.rem q.2.2.1)} :=
      ⟨Or.inr (Relation.TransGen.single ⟨hva, hnc_ae⟩), hane⟩
    refine BCart_no_later_kill_live hB haD ?_
    intro r hrD hrT hvar
    have hrU' : r ∈ U \ {(ts, rid, BCartOp.rem q.2.2.1)} :=
      ⟨h_dsub hrD.1, hrD.2⟩
    rcases r with ⟨tsr, rdr, opr⟩
    have hrT' : opr = BCartOp.rem q.2.2.1 := hrT
    subst hrT'
    exact BCart_live_no_later_rem hA hqA haU' hrU' hvar
  · by_cases hvea : C.vis (ts, rid, BCartOp.rem q.2.2.1)
        (q.1, q.2.1, BCartOp.add q.2.2.1 q.2.2.2)
    · -- vis-after the maximal rem: a vis-edge out of e — contradiction
      exfalso
      have hnc_ea : ¬ (BudgetCart alloc).toCRDTSig.commutes
          (ts, rid, BCartOp.rem q.2.2.1)
          (q.1, q.2.1, BCartOp.add q.2.2.1 q.2.2.2) :=
        fun h => hnc_ae (BCart_commutes_symm h)
      exact h_max _ haU'.1 hane (Or.inl ⟨hvea, hnc_ea⟩)
    · -- concurrent: the rc-edge is unabsorbed — contradiction
      exfalso
      refine h_max _ haU'.1 hane (Or.inr ⟨hvea, hva, ?_, ?_⟩)
      · show (if q.2.2.1 = q.2.2.1 then RcRes.Fst_then_snd else RcRes.Either)
            = RcRes.Fst_then_snd
        rw [if_pos rfl]
      · rintro ⟨e₃, he₃U, hve₃, hnce₃⟩
        have h₃T := BCart_ncomm_add_dest hnce₃
        have h₃ne : e₃ ≠ (ts, rid, BCartOp.rem q.2.2.1) := by
          intro h
          rw [h] at hve₃
          exact hva hve₃
        rcases e₃ with ⟨ts₃, rd₃, op₃⟩
        have h₃T' : op₃ = BCartOp.rem q.2.2.1 := h₃T
        subst h₃T'
        exact BCart_live_no_later_rem hA hqA haU' ⟨he₃U, h₃ne⟩ hve₃

/-- **`CDVC3` for the BudgetCart.** `add`-maximal: set algebra plus
instance freshness (the instance names its adder, which would have to be the
maximal event itself). `rem`-maximal: the trichotomy. -/
theorem BCart_cdVC3 : CDVC3 (BudgetCart alloc) := by
  intro C U A B e _ _ _ h_cl h_e h_max hA hB
  -- rebind the projection-typed states at the concrete type, so that
  -- `Finset` instances resolve
  obtain ⟨A, hA'⟩ : ∃ A' : BCartState, A' = A := ⟨A, rfl⟩
  subst hA'
  obtain ⟨B, hB'⟩ : ∃ B' : BCartState, B' = B := ⟨B, rfl⟩
  subst hB'
  rcases e with ⟨ts, rid, op⟩
  cases op with
  | add x p =>
    have hBt : ((ts, rid, x, p) : BCartElem) ∉ B := by
      intro hBt
      exact (BCart_canonical_bound hB hBt).2 rfl
    show bcartMergeL B A (bcartUpdate B (ts, rid, BCartOp.add x p))
        = bcartUpdate A (ts, rid, BCartOp.add x p)
    apply Finset.ext
    intro q
    simp only [mem_bcartMergeL, mem_bcartUpdate_add]
    by_cases hqp : q = ((ts, rid, x, p) : BCartElem)
    · subst hqp
      simp [hBt]
    · by_cases hqA : q ∈ A <;> by_cases hqB : q ∈ B <;>
        simp [hqp, hqA, hqB]
  | rem x =>
    have himp : ∀ q : BCartElem, q.2.2.1 = x → q ∈ A → q ∈ B :=
      fun q hqx hqA =>
        BCart_rem_max_trichotomy h_cl h_e h_max hA hB hqx hqA
    show bcartMergeL B A (bcartUpdate B (ts, rid, BCartOp.rem x))
        = bcartUpdate A (ts, rid, BCartOp.rem x)
    apply Finset.ext
    intro q
    simp only [mem_bcartMergeL, mem_bcartUpdate_rem]
    by_cases hx : q.2.2.1 = x
    · by_cases hqA : q ∈ A
      · have hqB : q ∈ B := himp q hx hqA
        simp [hqA, hqB, hx]
      · simp [hqA, hx]
    · by_cases hqA : q ∈ A <;> by_cases hqB : q ∈ B <;>
        simp [hqA, hqB, hx]

/-! ## §8. The feasible delta laws, the bundles, and the capstones -/

/-- The redistribution law is a propositional tautology for the OR-set-shaped
merge — **unconditional**, all five states arbitrary. -/
theorem bcartMergeL_redistribute (B t₀ t₁ t₂ u : BCartState) :
    bcartMergeL (bcartMergeL B t₀ u) (bcartMergeL B t₁ u) (bcartMergeL B t₂ u)
      = bcartMergeL B (bcartMergeL t₀ t₁ t₂) u := by
  apply Finset.ext
  intro q
  simp only [mem_bcartMergeL]
  by_cases hb : q ∈ B <;> by_cases h0 : q ∈ t₀ <;> by_cases h1 : q ∈ t₁ <;>
    by_cases h2 : q ∈ t₂ <;> by_cases hu : q ∈ u <;>
    simp [hb, h0, h1, h2, hu]

/-- **The feasible delta contract for the BudgetCart.** -/
theorem BCart_feasibleDeltaVCs3 : FeasibleDeltaVCs3 (BudgetCart alloc) := by
  refine ⟨?_, ?_, ?_⟩
  · -- feasible_init (holds unconditionally for the OR-set shape)
    intro C ev s _ _
    show bcartMergeL ∅ ∅ s = s
    apply Finset.ext
    intro q
    rw [mem_bcartMergeL]
    simp
  · -- feasible_local_redistribute
    intro C ev₁ ev₂ s₀ B t₁ s₂ e _ _ _ _ h_cl₁ _ he₁ he₂ _ hc₀ hB _ hc₂
    -- rebind the projection-typed states at the concrete type
    obtain ⟨s₀, h₀'⟩ : ∃ s₀' : BCartState, s₀' = s₀ := ⟨s₀, rfl⟩
    subst h₀'
    obtain ⟨B, hB'⟩ : ∃ B' : BCartState, B' = B := ⟨B, rfl⟩
    subst hB'
    obtain ⟨t₁, ht₁'⟩ : ∃ t₁' : BCartState, t₁' = t₁ := ⟨t₁, rfl⟩
    subst ht₁'
    obtain ⟨s₂, h₂'⟩ : ∃ s₂' : BCartState, s₂' = s₂ := ⟨s₂, rfl⟩
    subst h₂'
    rcases e with ⟨ts, rid, op⟩
    cases op with
    | add x p =>
      -- instance freshness against B and s₀
      have hBt : ((ts, rid, x, p) : BCartElem) ∉ B := by
        intro hBt
        exact (BCart_canonical_bound hB hBt).2 rfl
      have hs₀t : ((ts, rid, x, p) : BCartElem) ∉ s₀ := by
        intro hs₀t
        exact he₂ (BCart_canonical_bound hc₀ hs₀t).2
      show bcartMergeL s₀
          (bcartMergeL B t₁ (bcartUpdate B (ts, rid, BCartOp.add x p))) s₂
        = bcartMergeL B (bcartMergeL s₀ t₁ s₂)
            (bcartUpdate B (ts, rid, BCartOp.add x p))
      apply Finset.ext
      intro q
      simp only [mem_bcartMergeL, mem_bcartUpdate_add]
      by_cases hqp : q = ((ts, rid, x, p) : BCartElem)
      · subst hqp
        simp [hBt, hs₀t]
      · by_cases hb : q ∈ B <;> by_cases h0 : q ∈ s₀ <;>
          by_cases h1 : q ∈ t₁ <;> by_cases h2 : q ∈ s₂ <;>
          simp [hqp, hb, h0, h1, h2]
    | rem x =>
      -- the X2 exclusion via the σ-facts
      have himp : ∀ q : BCartElem, q.2.2.1 = x → q ∈ B → q ∈ s₂ →
          q ∈ s₀ := by
        intro q hqx hqB hqs₂
        subst hqx
        have ha' := BCart_canonical_bound hB hqB
        have ha'' := BCart_canonical_bound hc₂ hqs₂
        have haU : ((q.1, q.2.1, BCartOp.add q.2.2.1 q.2.2.2) : Op BCartOp)
            ∈ ev₁ ∩ ev₂ := ⟨downset_subset h_cl₁ he₁ ha'.1, ha''⟩
        refine BCart_no_later_kill_live hc₀ haU ?_
        intro r hr₀ hrT hvar
        rcases r with ⟨tsr, rdr, opr⟩
        have hrT' : opr = BCartOp.rem q.2.2.1 := hrT
        subst hrT'
        exact BCart_live_no_later_rem hc₂ hqs₂ ha'' hr₀.2 hvar
      show bcartMergeL s₀
          (bcartMergeL B t₁ (bcartUpdate B (ts, rid, BCartOp.rem x))) s₂
        = bcartMergeL B (bcartMergeL s₀ t₁ s₂)
            (bcartUpdate B (ts, rid, BCartOp.rem x))
      apply Finset.ext
      intro q
      simp only [mem_bcartMergeL, mem_bcartUpdate_rem]
      by_cases hx : q.2.2.1 = x
      · by_cases hb : q ∈ B
        · by_cases h2 : q ∈ s₂
          · have h0 : q ∈ s₀ := himp q hx hb h2
            by_cases h1 : q ∈ t₁ <;> simp [hb, h2, h0, h1, hx]
          · by_cases h0 : q ∈ s₀ <;> by_cases h1 : q ∈ t₁ <;>
              simp [hb, h2, h0, h1, hx]
        · by_cases h0 : q ∈ s₀ <;> by_cases h1 : q ∈ t₁ <;>
            by_cases h2 : q ∈ s₂ <;> simp [hb, h0, h1, h2, hx]
      · by_cases hb : q ∈ B <;> by_cases h0 : q ∈ s₀ <;>
          by_cases h1 : q ∈ t₁ <;> by_cases h2 : q ∈ s₂ <;>
          simp [hb, h0, h1, h2, hx]
  · -- feasible_redistribute: the unconditional tautology
    intro C ev₁ ev₂ t₀ t₁ t₂ B e _ _ _ _ _ _ _ _ _ _ _ _ _
    exact bcartMergeL_redistribute B t₀ t₁ t₂ ((BudgetCart alloc).update B e)

theorem BCart_updateVCs : UpdateVCs (BudgetCart alloc).toCRDTSig :=
  ⟨BCart_rc_non_comm_directional, BCart_no_rc_chain, BCart_cond_comm_lift⟩

theorem BCart_coreVCs3CD : CoreVCs3CD (BudgetCart alloc) :=
  ⟨BCart_updateVCs, BCart_mergeL_comm⟩

/-- The ternary Join Lemma for the BudgetCart — the OR-set's route. -/
theorem BCart_joinLemma3 : JoinLemma3 (BudgetCart alloc) :=
  join_lemma3_of_cd_feasible BCart_coreVCs3CD BCart_feasibleDeltaVCs3
    BCart_cdVC3

open LabeledTS in
/-- **End-to-end RA-linearizability for the BudgetCart** (convergence half),
for every `alloc`. -/
theorem bcart_ra_linearizable3
    (C : Configuration (BudgetCart alloc))
    (hReach : (labeledTS3 (BudgetCart alloc)).ReachableFrom
      (initConfig (BudgetCart alloc) trivial) C) :
    IsRALinearizable3 C :=
  ra_linearizable3_of_join BCart_joinLemma3 C hReach

end

/-! ### The conditioned capstone — identity instantiation of the generic
framework -/

section
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.GoodConfig3H
open Sal.ConditionedMRDTs.FlatGeneric

/-- **BudgetCart over the generic framework** (the catalogue capstone),
universally in `alloc`. -/
theorem BCart_ra_linearizable3_eq (alloc : ℕ → ℕ)
    (C : Configuration (QSig (eqOfEq (BudgetCart alloc))
      (WTop (BudgetCart alloc)) (invPresTop fun _ => trivial)
      (congVCEq (BudgetCart alloc)) (invInvVCTop (BudgetCart alloc))))
    (hReach : (labeledTS3 _).ReachableFrom (initConfig _ trivial) C) :
    IsRALinearizable3Eq (eqOfEq (BudgetCart alloc)) (WTop (BudgetCart alloc))
      (invPresTop fun _ => trivial) (congVCEq (BudgetCart alloc))
      (invInvVCTop (BudgetCart alloc)) C :=
  flat_ra_linearizable3_eq (fun _ => trivial) (fun _ _ => trivial)
    (contractJoinFull (ConditionedContract.ofVCs (BudgetCart alloc)
      BCart_coreVCs3CD BCart_feasibleDeltaVCs3 BCart_cdVC3 trivial))
    C hReach

end

/-! ## §9. The client contract: derived spend, invariant, applicability -/

section
variable {alloc : ℕ → ℕ}

/-- The budget invariant: every replica's derived spend is within its
allocation. -/
def BCartInv (alloc : ℕ → ℕ) (s : BCartState) : Prop :=
  ∀ r, bcartSpend r s ≤ alloc r

/-- The client check: an `add` needs slack in the issuing replica's OWN
budget — checkable against the issuing replica's state; a `rem` needs a live
instance of the item. -/
def bcartApplicable (alloc : ℕ → ℕ) (o : Op BCartOp) (s : BCartState) : Prop :=
  match o.2.2 with
  | .add _ price => bcartSpend o.2.1 s + price ≤ alloc o.2.1
  | .rem item => ∃ q ∈ s, q.2.2.1 = item

theorem bcart_inv_init : BCartInv alloc (∅ : BCartState) := by
  intro r
  show bcartSpend r ∅ ≤ alloc r
  simp [bcartSpend]

/-- Spend is monotone under state inclusion (prices are non-negative). -/
theorem bcartSpend_le_of_subset {s t : BCartState} (h : s ⊆ t) (r : ℕ) :
    bcartSpend r s ≤ bcartSpend r t :=
  Finset.sum_le_sum_of_subset (Finset.filter_subset_filter _ h)

/-- A rem never raises anyone's spend — removing an instance refunds its
adder. -/
theorem bcartSpend_update_rem_le (s : BCartState) (ts rr item r : ℕ) :
    bcartSpend r (bcartUpdate s (ts, rr, BCartOp.rem item)) ≤ bcartSpend r s :=
  bcartSpend_le_of_subset (Finset.filter_subset _ s) r

/-- Others' adds don't touch my spend: the inserted instance carries its own
replica. -/
theorem bcartSpend_update_add_other {r rr : ℕ} (hne : rr ≠ r)
    (s : BCartState) (ts item price : ℕ) :
    bcartSpend r (bcartUpdate s (ts, rr, BCartOp.add item price))
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
    bcartSpend r (bcartUpdate s (ts, r, BCartOp.add item price))
      = bcartSpend r s + price := by
  show bcartSpend r (insert (ts, r, item, price) s) = bcartSpend r s + price
  unfold bcartSpend
  rw [Finset.filter_insert, if_pos rfl,
    Finset.sum_insert (fun h => hfresh (Finset.mem_of_mem_filter _ h))]
  exact Nat.add_comm _ _

/-- The unconditional add bound: an add raises my spend by at most the price
(exactly, when fresh and own; not at all otherwise). -/
theorem bcartSpend_update_add_le (s : BCartState) (ts rr item price r : ℕ) :
    bcartSpend r (bcartUpdate s (ts, rr, BCartOp.add item price))
      ≤ bcartSpend r s + price := by
  by_cases hr : rr = r
  · subst hr
    by_cases hmem : ((ts, rr, item, price) : BCartElem) ∈ s
    · have : bcartUpdate s (ts, rr, BCartOp.add item price) = s := by
        show insert (ts, rr, item, price) s = s
        exact Finset.insert_eq_self.mpr hmem
      rw [this]
      omega
    · rw [bcartSpend_update_add_fresh hmem]
  · rw [bcartSpend_update_add_other hr]
    omega

/-- An applicable step preserves the budget invariant at the SAME state — the
contract is locally maintainable at the issuing replica. -/
theorem bcartApplicable_inv_pres {s : BCartState} {o : Op BCartOp}
    (hInv : BCartInv alloc s) (happ : bcartApplicable alloc o s) :
    BCartInv alloc (bcartUpdate s o) := by
  obtain ⟨ts, rr, op⟩ := o
  intro r
  cases op with
  | add item price =>
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
sound for **canonical** (rc-respecting) folds — but `SafetyStepOn`'s
`CausalFold` hypotheses pin only `vis`-respect, and for an rc-nontrivial
datatype the fold of a set containing concurrent same-item `add`/`rem` pairs
is enumeration-dependent. The full `SafetyStepOn (BudgetCart alloc)
(BCartInv alloc) (bcartApplicable alloc)` is in fact **false**; see
`BCartSpendMono`. -/

/-- **The open transfer obligation** (the honest gap): under `SafetyStepOn`'s
prefix hypotheses, the issuer's spend at the prefix fold is bounded by its
spend at the causal-past fold.

This is NOT provable from the stated hypotheses — it is refuted by a
two-event configuration. Take `alloc r = 10`,
`past(e) = {a, k}` with `a = (1, r, add x 10)`, `k = (2, r', rem x)`
concurrent to each other, both vis-before `e = (3, r, add x' 10)`, and
`S = past(e)`. The vis-respecting enumeration `[a, k]` folds to `∅`
(spend `0`); the vis-respecting enumeration `[k, a]` folds to
`{(1, r, x, 10)}` (spend `10`). With `σP` the first fold and `σS` the
second, every `SafetyStepOn` hypothesis holds, `bcartApplicable` accepts `e`
at `σP`, `BCartInv` holds at `σS` — and `update σS e` has spend `20 > 10`.
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
`bcart_safetyStep` does not exist — it is false (see `BCartSpendMono`). -/
theorem bcart_safetyStep_of_spend_mono (hMono : BCartSpendMono alloc) :
    SafetyStepOn (BudgetCart alloc) (BCartInv alloc) (bcartApplicable alloc) := by
  intro C E S e σS σP hEev hEcl heE hSsub heS hScl hfut hpast hσS hσP hInv happ
  obtain ⟨ts, rr, op⟩ := e
  have hmono : bcartSpend rr σS ≤ bcartSpend rr σP :=
    hMono C E S (ts, rr, op) σS σP hEev hEcl heE hSsub heS hScl hfut hpast
      hσS hσP
  intro r
  cases op with
  | add item price =>
    by_cases hr : rr = r
    · subst hr
      have happ' : bcartSpend rr σP + price ≤ alloc rr := happ
      have h2 := bcartSpend_update_add_le σS ts rr item price rr
      show bcartSpend rr (bcartUpdate σS (ts, rr, BCartOp.add item price))
          ≤ alloc rr
      omega
    · show bcartSpend r (bcartUpdate σS (ts, rr, BCartOp.add item price))
          ≤ alloc r
      rw [bcartSpend_update_add_other hr]
      exact hInv r
  | rem item =>
    show bcartSpend r (bcartUpdate σS (ts, rr, BCartOp.rem item)) ≤ alloc r
    exact le_trans (bcartSpend_update_rem_le σS ts rr item r) (hInv r)

/-- **The budget bound at every version, hypothesis-gated** — the composition
of the generic safety metatheorem (`version_inv_on_of_causal_canonical`) with
the gated SafetyStep.

The `CausalCanonical` hypothesis is **open for rc-nontrivial datatypes**:
its known discharges are the pointwise species (all-comm + `rc ≡ Either` —
unavailable here, the BudgetCart has a genuine `rc`) and the
witness-maintenance species (OQ8 / `JoinLemma3AtC`,
`Development/GENERIC_SAFETY_PENPAPER.md` §4.2 (P1)), which is unproven.
The BudgetCart is the instance that forces that gate. `BCartSpendMono` is
the additional (kindred) open transfer this instance needs because
`SafetyStepOn`'s interface forgets the rc-orientation of its folds. -/
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
