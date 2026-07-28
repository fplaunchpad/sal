import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.SDiff
import Sal.ConditionedMRDTs.Metatheory.Adequacy
import Sal.ConditionedMRDTs.Metatheory.FlatGeneric_Bridge

/-!
# The payload-parametric OR-set core (composition level L0)

The OR-set-of-instances convergence discharge, parametric in the payload. The
proofs nowhere depend on the payload type, only on three structural facts:

* instances are `(ts, rep, payload)` triples, so an instance **names its
  adding event** (the self-naming/freshness property every σ-fact rides on);
* `rem` targets a KEY computed from the payload (`key : β → ℕ`), removing
  every live instance of that key;
* `rc` is add-wins on same-key `add`/`rem` pairs (`Snd_then_fst`/
  `Fst_then_snd`), `Either` everywhere else.

The pieces:

* `OSOp β` / `OSElem β` / `OSState β`, ops, instances, states;
* `osUpdate key` / `osMergeL` / `osRc key`, the OR-set dynamics: `add b`
  inserts `(e.ts, e.rep, b)`; `rem k` filters the live `k`-instances
  (production OR-set semantics: the effect is state-dependent); the
  three-way merge is `(l ∩ a ∩ b) ∪ (a ∖ l) ∪ (b ∖ l)`;
* `OSCore β key Q V qy`, the `ConditionedMRDTSig`, with the query
  (`Q`/`V`/`qy`) **also a parameter**: the convergence discharge never
  touches the query, so quantifying over it lets any concrete datatype BE an
  instantiation, definitionally;
* §2–§8: the full OR-set-route discharge (`CoreVCs3CD` +
  `FeasibleDeltaVCs3` + `CDVC3` ⇒ `JoinLemma3`) over the `Finset`
  representation, ending in `oscore_ra_linearizable3` and the conditioned
  capstone `OSCore_ra_linearizable3_eq`.

**Composition level L0** (payload instantiation): a client datatype defines
its op/state types AS `OSOp γ`/`OSState γ` for its payload `γ`, its sig as
`OSCore γ key Q V qy`, and inherits every convergence capstone by
instantiation, with zero convergence proof obligations. The BudgetCart is a
client (payload `(item, price)`, key `Prod.fst`).
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

/-! ## §1. The parametric datatype -/

/-- OR-set-core ops: `add b` stakes an instance carrying payload `b`;
`rem k` removes every live instance whose payload has key `k`. -/
inductive OSOp (β : Type) : Type where
  | add : β → OSOp β
  | rem : ℕ → OSOp β
deriving DecidableEq

/-- A live instance: `(ts, rep, payload)`, the adding event's timestamp and
replica, and the payload. An instance names its adding event. -/
abbrev OSElem (β : Type) : Type := ℕ × ℕ × β

/-- OR-set-core state: the finite set of live instances. -/
abbrev OSState (β : Type) : Type := Finset (OSElem β)

/-- `add b` at `(ts, rep)` inserts `(ts, rep, b)`; `rem k` filters every
instance of key `k` present at application time. -/
def osUpdate {β : Type} [DecidableEq β] (key : β → ℕ)
    (s : OSState β) (o : Op (OSOp β)) : OSState β :=
  match o.2.2 with
  | .add b => insert (o.1, o.2.1, b) s
  | .rem k => s.filter (fun q => key q.2.2 ≠ k)

/-- The OR-set three-way merge on instances:
`(l ∩ a ∩ b) ∪ (a ∖ l) ∪ (b ∖ l)`. -/
def osMergeL {β : Type} [DecidableEq β] (l a b : OSState β) : OSState β :=
  ((l ∩ a) ∩ b) ∪ ((a \ l) ∪ (b \ l))

/-- Add-wins `rc`: `add`-vs-`rem` on the same key is ordered rem-first;
all other pairs `Either`. -/
def osRc {β : Type} (key : β → ℕ) (o₁ o₂ : Op (OSOp β)) : RcRes :=
  match o₁.2.2, o₂.2.2 with
  | .add b, .rem y => if key b = y then RcRes.Snd_then_fst else RcRes.Either
  | .rem x, .add b => if x = key b then RcRes.Fst_then_snd else RcRes.Either
  | _, _ => RcRes.Either

/-- The fold of an event list, stated over `OSState β` (definitionally
`applySeq (OSCore β key Q V qy).toCRDTSig`, but `Finset` instances
resolve). -/
def osFold {β : Type} [DecidableEq β] (key : β → ℕ)
    (s : OSState β) (π : List (Op (OSOp β))) : OSState β :=
  π.foldl (osUpdate key) s

/-- **The payload-parametric OR-set core**, as a `ConditionedMRDTSig`. The
sig-level `Inv`/`applicable` are `⊤` (repo convention: a client's contract
lives beside ITS signature, as with the BudgetCart's budget); the query is a
parameter the convergence discharge does not use. -/
def OSCore (β : Type) [DecidableEq β] (key : β → ℕ)
    (Q V : Type) (qy : OSState β → Q → V) : ConditionedMRDTSig where
  State := OSState β
  dec_state := inferInstance
  init := (∅ : OSState β)
  AppOp := OSOp β
  dec_op := inferInstance
  Query := Q
  Value := V
  update := osUpdate key
  merge := fun a b => osMergeL ∅ a b
  query := qy
  rc := osRc key
  mergeL := osMergeL
  merge_init_slice := fun _ _ => rfl
  Inv := fun _ => True
  applicable := fun _ _ => True

section
variable {β : Type} [DecidableEq β] {key : β → ℕ} {Q V : Type}
  {qy : OSState β → Q → V}

theorem OSCore_update_eq (s : OSState β) (o : Op (OSOp β)) :
    (OSCore β key Q V qy).update s o = osUpdate key s o := rfl

theorem OSCore_mergeL_eq (l a b : OSState β) :
    (OSCore β key Q V qy).mergeL l a b = osMergeL l a b := rfl

theorem OSCore_init_eq : (OSCore β key Q V qy).init = (∅ : OSState β) := rfl

/-! Membership characterizations: everything downstream is propositional
logic over these. -/

theorem mem_osUpdate_add {s : OSState β} {q : OSElem β} {ts r : ℕ} {b : β} :
    q ∈ osUpdate key s (ts, r, OSOp.add b)
      ↔ q = (ts, r, b) ∨ q ∈ s := by
  show q ∈ insert (ts, r, b) s ↔ _
  exact Finset.mem_insert

theorem mem_osUpdate_rem {s : OSState β} {q : OSElem β} {ts r k : ℕ} :
    q ∈ osUpdate key s (ts, r, OSOp.rem k) ↔ q ∈ s ∧ key q.2.2 ≠ k := by
  show q ∈ s.filter (fun q => key q.2.2 ≠ k) ↔ _
  exact Finset.mem_filter

theorem mem_osMergeL {l a b : OSState β} {q : OSElem β} :
    q ∈ osMergeL l a b ↔
      (q ∈ l ∧ q ∈ a ∧ q ∈ b) ∨ (q ∈ a ∧ q ∉ l) ∨ (q ∈ b ∧ q ∉ l) := by
  unfold osMergeL
  rw [Finset.mem_union, Finset.mem_union, Finset.mem_inter, Finset.mem_inter,
    Finset.mem_sdiff, Finset.mem_sdiff]
  tauto

/-- `osMergeL` is commutative in its branch arguments. -/
theorem OSCore_mergeL_comm (l a b : (OSCore β key Q V qy).State) :
    (OSCore β key Q V qy).mergeL l a b
      = (OSCore β key Q V qy).mergeL l b a := by
  show osMergeL l a b = osMergeL l b a
  apply Finset.ext
  intro q
  rw [mem_osMergeL, mem_osMergeL]
  tauto

/-! ## §2. The fold over the concrete state, and pointwise transport -/

theorem osFold_eq_applySeq (s : OSState β) (π : List (Op (OSOp β))) :
    applySeq (OSCore β key Q V qy).toCRDTSig s π = osFold key s π := rfl

theorem osFold_append_single (s : OSState β) (π : List (Op (OSOp β)))
    (o : Op (OSOp β)) :
    osFold key s (π ++ [o]) = osUpdate key (osFold key s π) o := by
  simp [osFold, List.foldl_append]

/-- Updates transport pointwise membership agreement. -/
theorem osUpdate_pointwise (a b : OSState β) (o : Op (OSOp β))
    (q : OSElem β) (h : q ∈ a ↔ q ∈ b) :
    q ∈ osUpdate key a o ↔ q ∈ osUpdate key b o := by
  rcases o with ⟨ts, r, op⟩
  cases op with
  | add c => rw [mem_osUpdate_add, mem_osUpdate_add, h]
  | rem k => rw [mem_osUpdate_rem, mem_osUpdate_rem, h]

/-- Folds transport pointwise membership agreement. -/
theorem osFold_agree {a b : OSState β}
    (π : List (Op (OSOp β))) (q : OSElem β) (h : q ∈ a ↔ q ∈ b) :
    q ∈ osFold key a π ↔ q ∈ osFold key b π := by
  induction π generalizing a b with
  | nil => exact h
  | cons o π ih => exact ih (osUpdate_pointwise a b o q h)

/-! ## §3. Commutation classification -/

theorem OSCore_commutes_symm {o₁ o₂ : Op (OSCore β key Q V qy).AppOp}
    (h : (OSCore β key Q V qy).toCRDTSig.commutes o₁ o₂) :
    (OSCore β key Q V qy).toCRDTSig.commutes o₂ o₁ :=
  fun s => (h s).symm

theorem OSCore_comm_add_add (ts₁ r₁ : ℕ) (b₁ : β) (ts₂ r₂ : ℕ) (b₂ : β) :
    (OSCore β key Q V qy).toCRDTSig.commutes (ts₁, r₁, OSOp.add b₁)
      (ts₂, r₂, OSOp.add b₂) := by
  intro s
  show osUpdate key (osUpdate key s (ts₁, r₁, OSOp.add b₁))
        (ts₂, r₂, OSOp.add b₂)
      = osUpdate key (osUpdate key s (ts₂, r₂, OSOp.add b₂))
        (ts₁, r₁, OSOp.add b₁)
  apply Finset.ext
  intro q
  simp only [mem_osUpdate_add]
  tauto

theorem OSCore_comm_rem_rem (ts₁ r₁ x₁ ts₂ r₂ x₂ : ℕ) :
    (OSCore β key Q V qy).toCRDTSig.commutes (ts₁, r₁, OSOp.rem x₁)
      (ts₂, r₂, OSOp.rem x₂) := by
  intro s
  show osUpdate key (osUpdate key s (ts₁, r₁, OSOp.rem x₁))
        (ts₂, r₂, OSOp.rem x₂)
      = osUpdate key (osUpdate key s (ts₂, r₂, OSOp.rem x₂))
        (ts₁, r₁, OSOp.rem x₁)
  apply Finset.ext
  intro q
  rw [mem_osUpdate_rem, mem_osUpdate_rem, mem_osUpdate_rem,
    mem_osUpdate_rem]
  tauto

theorem OSCore_comm_add_rem_ne (ts₁ r₁ : ℕ) (b : β) (ts₂ r₂ y : ℕ)
    (hxy : key b ≠ y) :
    (OSCore β key Q V qy).toCRDTSig.commutes (ts₁, r₁, OSOp.add b)
      (ts₂, r₂, OSOp.rem y) := by
  intro s
  show osUpdate key (osUpdate key s (ts₁, r₁, OSOp.add b))
        (ts₂, r₂, OSOp.rem y)
      = osUpdate key (osUpdate key s (ts₂, r₂, OSOp.rem y))
        (ts₁, r₁, OSOp.add b)
  apply Finset.ext
  intro q
  rw [mem_osUpdate_rem, mem_osUpdate_add, mem_osUpdate_add,
    mem_osUpdate_rem]
  constructor
  · rintro ⟨rfl | hq, hne⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨hq, hne⟩
  · rintro (rfl | ⟨hq, hne⟩)
    · exact ⟨Or.inl rfl, hxy⟩
    · exact ⟨Or.inr hq, hne⟩

/-- Same-key `add`/`rem` genuinely do not commute (witness: the empty
state). -/
theorem OSCore_ncomm_add_rem (ts₁ r₁ : ℕ) (b : β) (ts₂ r₂ : ℕ) :
    ¬ (OSCore β key Q V qy).toCRDTSig.commutes (ts₁, r₁, OSOp.add b)
      (ts₂, r₂, OSOp.rem (key b)) := by
  intro h
  have h0 : osUpdate key (osUpdate key (∅ : OSState β)
        (ts₁, r₁, OSOp.add b)) (ts₂, r₂, OSOp.rem (key b))
      = osUpdate key (osUpdate key (∅ : OSState β)
        (ts₂, r₂, OSOp.rem (key b))) (ts₁, r₁, OSOp.add b) :=
    h (∅ : OSState β)
  have hmem : ((ts₁, r₁, b) : OSElem β)
      ∈ osUpdate key (osUpdate key (∅ : OSState β)
        (ts₂, r₂, OSOp.rem (key b))) (ts₁, r₁, OSOp.add b) := by
    rw [mem_osUpdate_add]
    exact Or.inl rfl
  rw [← h0, mem_osUpdate_rem] at hmem
  exact hmem.2 rfl

/-- The classification: an `add b` fails to commute only with
`rem (key b)`. -/
theorem OSCore_ncomm_add_dest {ts r : ℕ} {b : β}
    {o : Op (OSCore β key Q V qy).AppOp}
    (h : ¬ (OSCore β key Q V qy).toCRDTSig.commutes (ts, r, OSOp.add b) o) :
    o.2.2 = OSOp.rem (key b) := by
  rcases o with ⟨ts', r', op⟩
  cases op with
  | add b' => exact absurd (OSCore_comm_add_add ts r b ts' r' b') h
  | rem y =>
    by_cases hxy : key b = y
    · subst hxy; rfl
    · exact absurd (OSCore_comm_add_rem_ne ts r b ts' r' y hxy) h

/-- The classification: a `rem x` fails to commute only with an `add` of an
`x`-keyed payload. -/
theorem OSCore_ncomm_rem_dest {ts r x : ℕ}
    {o : Op (OSCore β key Q V qy).AppOp}
    (h : ¬ (OSCore β key Q V qy).toCRDTSig.commutes (ts, r, OSOp.rem x) o) :
    ∃ b, o.2.2 = OSOp.add b ∧ key b = x := by
  rcases o with ⟨ts', r', op⟩
  cases op with
  | add b =>
    by_cases hyx : key b = x
    · exact ⟨b, rfl, hyx⟩
    · exact absurd
        (OSCore_commutes_symm (OSCore_comm_add_rem_ne ts' r' b ts r x hyx)) h
  | rem y => exact absurd (OSCore_comm_rem_rem ts r x ts' r' y) h

/-! ## §4. The update layer of `CoreVCs3CD` -/

theorem OSCore_no_rc_chain :
    ∀ o₁ o₂ o₃ : Op (OSCore β key Q V qy).AppOp,
      distinctOps o₁ o₂ → distinctOps o₂ o₃ →
      ¬ ((OSCore β key Q V qy).toCRDTSig.rc o₁ o₂ = RcRes.Fst_then_snd ∧
         (OSCore β key Q V qy).toCRDTSig.rc o₂ o₃ = RcRes.Fst_then_snd) := by
  rintro ⟨ts₁, r₁, op₁⟩ ⟨ts₂, r₂, op₂⟩ ⟨ts₃, r₃, op₃⟩ _ _ ⟨h1, h2⟩
  cases op₂ with
  | add b₂ =>
    cases op₃ with
    | add b₃ => exact RcRes.noConfusion (show RcRes.Either = _ from h2)
    | rem x₃ =>
      have h2' : (if key b₂ = x₃ then RcRes.Snd_then_fst else RcRes.Either)
          = RcRes.Fst_then_snd := h2
      by_cases hx : key b₂ = x₃
      · rw [if_pos hx] at h2'; exact RcRes.noConfusion h2'
      · rw [if_neg hx] at h2'; exact RcRes.noConfusion h2'
  | rem x₂ =>
    cases op₁ with
    | add b₁ =>
      have h1' : (if key b₁ = x₂ then RcRes.Snd_then_fst else RcRes.Either)
          = RcRes.Fst_then_snd := h1
      by_cases hx : key b₁ = x₂
      · rw [if_pos hx] at h1'; exact RcRes.noConfusion h1'
      · rw [if_neg hx] at h1'; exact RcRes.noConfusion h1'
    | rem x₁ => exact RcRes.noConfusion (show RcRes.Either = _ from h1)

theorem OSCore_rc_non_comm_directional :
    ∀ o₁ o₂ : Op (OSCore β key Q V qy).AppOp,
      distinctOps o₁ o₂ → differentReplicas o₁ o₂ →
      (¬ (OSCore β key Q V qy).toCRDTSig.commutes o₁ o₂ ↔
       ((OSCore β key Q V qy).toCRDTSig.rc o₁ o₂ = RcRes.Fst_then_snd ∨
        (OSCore β key Q V qy).toCRDTSig.rc o₂ o₁ = RcRes.Fst_then_snd)) := by
  intro o₁ o₂ _ _
  constructor
  · intro hnc
    rcases o₁ with ⟨ts₁, r₁, op₁⟩
    cases op₁ with
    | add b =>
      have h2 := OSCore_ncomm_add_dest hnc
      rcases o₂ with ⟨ts₂, r₂, op₂⟩
      have h2' : op₂ = OSOp.rem (key b) := h2
      subst h2'
      right
      show (if key b = key b then RcRes.Fst_then_snd else RcRes.Either)
          = RcRes.Fst_then_snd
      rw [if_pos rfl]
    | rem x =>
      obtain ⟨b, h2, hkb⟩ := OSCore_ncomm_rem_dest hnc
      rcases o₂ with ⟨ts₂, r₂, op₂⟩
      have h2' : op₂ = OSOp.add b := h2
      subst h2'
      left
      show (if x = key b then RcRes.Fst_then_snd else RcRes.Either)
          = RcRes.Fst_then_snd
      rw [if_pos hkb.symm]
  · rintro (h | h)
    · rcases o₁ with ⟨ts₁, r₁, op₁⟩
      rcases o₂ with ⟨ts₂, r₂, op₂⟩
      cases op₁ with
      | add b₁ =>
        exfalso
        cases op₂ with
        | add b₂ => exact RcRes.noConfusion (show RcRes.Either = _ from h)
        | rem x₂ =>
          have h' : (if key b₁ = x₂ then RcRes.Snd_then_fst else RcRes.Either)
              = RcRes.Fst_then_snd := h
          by_cases hx : key b₁ = x₂
          · rw [if_pos hx] at h'; exact RcRes.noConfusion h'
          · rw [if_neg hx] at h'; exact RcRes.noConfusion h'
      | rem x₁ =>
        cases op₂ with
        | add b₂ =>
          have h' : (if x₁ = key b₂ then RcRes.Fst_then_snd else RcRes.Either)
              = RcRes.Fst_then_snd := h
          by_cases hx : x₁ = key b₂
          · subst hx
            intro hc
            exact OSCore_ncomm_add_rem ts₂ r₂ b₂ ts₁ r₁
              (OSCore_commutes_symm hc)
          · rw [if_neg hx] at h'
            exact absurd h' (fun hh => RcRes.noConfusion hh)
        | rem x₂ =>
          exact absurd (show RcRes.Either = _ from h)
            (fun hh => RcRes.noConfusion hh)
    · rcases o₁ with ⟨ts₁, r₁, op₁⟩
      rcases o₂ with ⟨ts₂, r₂, op₂⟩
      cases op₂ with
      | add b₂ =>
        exfalso
        cases op₁ with
        | add b₁ => exact RcRes.noConfusion (show RcRes.Either = _ from h)
        | rem x₁ =>
          have h' : (if key b₂ = x₁ then RcRes.Snd_then_fst else RcRes.Either)
              = RcRes.Fst_then_snd := h
          by_cases hx : key b₂ = x₁
          · rw [if_pos hx] at h'; exact RcRes.noConfusion h'
          · rw [if_neg hx] at h'; exact RcRes.noConfusion h'
      | rem x₂ =>
        cases op₁ with
        | add b₁ =>
          have h' : (if x₂ = key b₁ then RcRes.Fst_then_snd else RcRes.Either)
              = RcRes.Fst_then_snd := h
          by_cases hx : x₂ = key b₁
          · subst hx
            exact OSCore_ncomm_add_rem ts₁ r₁ b₁ ts₂ r₂
          · rw [if_neg hx] at h'
            exact absurd h' (fun hh => RcRes.noConfusion hh)
        | rem x₁ =>
          exact absurd (show RcRes.Either = _ from h)
            (fun hh => RcRes.noConfusion hh)

/-- `cond_comm_lift`: the `rem k`/`add b` swap perturbs the state by at most
the fresh instance; the perturbation is invisible off that instance, and the
final non-commuting `e''` (= `rem (key b)`) erases it. -/
theorem OSCore_cond_comm_lift :
    ∀ (s : (OSCore β key Q V qy).State)
      (e e' e'' : Op (OSCore β key Q V qy).AppOp)
      (π : List (Op (OSCore β key Q V qy).AppOp)),
      distinctOps e e' → distinctOps e e'' → distinctOps e' e'' →
      (OSCore β key Q V qy).toCRDTSig.rc e e' = RcRes.Fst_then_snd →
      ¬ (OSCore β key Q V qy).toCRDTSig.commutes e' e'' →
      (OSCore β key Q V qy).update (applySeq (OSCore β key Q V qy).toCRDTSig
          ((OSCore β key Q V qy).update
            ((OSCore β key Q V qy).update s e') e) π) e''
        = (OSCore β key Q V qy).update (applySeq (OSCore β key Q V qy).toCRDTSig
            ((OSCore β key Q V qy).update
              ((OSCore β key Q V qy).update s e) e') π) e'' := by
  intro s e e' e'' π _ _ _ hrc hnc
  rcases e with ⟨ts₁, r₁, op₁⟩
  rcases e' with ⟨ts₂, r₂, op₂⟩
  -- rc = Fst forces (rem (key b), add b)
  cases op₁ with
  | add b₁ =>
    exfalso
    cases op₂ with
    | add b₂ => exact RcRes.noConfusion (show RcRes.Either = _ from hrc)
    | rem x₂ =>
      have h' : (if key b₁ = x₂ then RcRes.Snd_then_fst else RcRes.Either)
          = RcRes.Fst_then_snd := hrc
      by_cases hx : key b₁ = x₂
      · rw [if_pos hx] at h'; exact RcRes.noConfusion h'
      · rw [if_neg hx] at h'; exact RcRes.noConfusion h'
  | rem x₁ =>
    cases op₂ with
    | rem x₂ =>
      exact absurd (show RcRes.Either = _ from hrc)
        (fun hh => RcRes.noConfusion hh)
    | add b₂ =>
      have h' : (if x₁ = key b₂ then RcRes.Fst_then_snd else RcRes.Either)
          = RcRes.Fst_then_snd := hrc
      by_cases hx : x₁ = key b₂
      swap
      · rw [if_neg hx] at h'; exact absurd h' (fun hh => RcRes.noConfusion hh)
      · subst hx
        -- e'' = rem (key b₂)
        have hdest := OSCore_ncomm_add_dest hnc
        rcases e'' with ⟨ts₃, r₃, op₃⟩
        have hdest' : op₃ = OSOp.rem (key b₂) := hdest
        subst hdest'
        show osUpdate key (osFold key
            (osUpdate key (osUpdate key s (ts₂, r₂, OSOp.add b₂))
              (ts₁, r₁, OSOp.rem (key b₂))) π) (ts₃, r₃, OSOp.rem (key b₂))
          = osUpdate key (osFold key
              (osUpdate key (osUpdate key s (ts₁, r₁, OSOp.rem (key b₂)))
                (ts₂, r₂, OSOp.add b₂)) π) (ts₃, r₃, OSOp.rem (key b₂))
        apply Finset.ext
        intro q
        rw [mem_osUpdate_rem, mem_osUpdate_rem]
        by_cases hq : key q.2.2 = key b₂
        · simp [hq]
        · have hagree :
              q ∈ osUpdate key (osUpdate key s (ts₂, r₂, OSOp.add b₂))
                (ts₁, r₁, OSOp.rem (key b₂))
              ↔ q ∈ osUpdate key (osUpdate key s (ts₁, r₁, OSOp.rem (key b₂)))
                (ts₂, r₂, OSOp.add b₂) := by
            have hqp : q ≠ ((ts₂, r₂, b₂) : OSElem β) := by
              intro h
              exact hq (by rw [h])
            rw [mem_osUpdate_rem, mem_osUpdate_add,
              mem_osUpdate_add, mem_osUpdate_rem]
            simp [hqp]
          rw [osFold_agree π q hagree]

/-! ## §5. Fold facts -/

/-- **Bound**: a live instance names its adding event, which is in the
list. -/
theorem OSCore_fold_bound : ∀ {ρ : List (Op (OSOp β))} {q : OSElem β},
    q ∈ osFold key ∅ ρ → (q.1, q.2.1, OSOp.add q.2.2) ∈ ρ := by
  intro ρ
  induction ρ using List.reverseRecOn with
  | nil => intro q h; exact absurd h (Finset.notMem_empty q)
  | append_singleton ρ o ih =>
    intro q h
    rw [osFold_append_single] at h
    rcases o with ⟨ts, rid, op⟩
    cases op with
    | add b =>
      rcases mem_osUpdate_add.mp h with hq | hq
      · subst hq
        exact List.mem_append_right _ List.mem_cons_self
      · exact List.mem_append_left _ (ih hq)
    | rem k =>
      exact List.mem_append_left _ (ih (mem_osUpdate_rem.mp h).1)

/-- A dead instance stays dead if its (unique) adding event does not occur. -/
theorem OSCore_fold_stays_out {q : OSElem β} :
    ∀ (π : List (Op (OSOp β))) (s : OSState β), q ∉ s →
      (∀ o ∈ π, o ≠ (q.1, q.2.1, OSOp.add q.2.2)) →
      q ∉ osFold key s π := by
  intro π
  induction π with
  | nil => intro s hs _; exact hs
  | cons o π ih =>
    intro s hs hπ
    have hupd : q ∉ osUpdate key s o := by
      rcases o with ⟨ts, rid, op⟩
      cases op with
      | add b =>
        intro h
        rcases mem_osUpdate_add.mp h with hq | hq
        · exact hπ _ List.mem_cons_self (by rw [hq])
        · exact hs hq
      | rem k =>
        intro h
        exact hs (mem_osUpdate_rem.mp h).1
    exact ih (osUpdate key s o) hupd
      (fun o' ho' => hπ o' (List.mem_cons_of_mem _ ho'))

/-- A live instance stays live if no same-key rem follows. -/
theorem OSCore_fold_stays_in {q : OSElem β} :
    ∀ (π : List (Op (OSOp β))) (s : OSState β), q ∈ s →
      (∀ o ∈ π, o.2.2 ≠ OSOp.rem (key q.2.2)) →
      q ∈ osFold key s π := by
  intro π
  induction π with
  | nil => intro s hs _; exact hs
  | cons o π ih =>
    intro s hs hπ
    have hupd : q ∈ osUpdate key s o := by
      rcases o with ⟨ts, rid, op⟩
      cases op with
      | add b =>
        rw [mem_osUpdate_add]
        exact Or.inr hs
      | rem k =>
        rw [mem_osUpdate_rem]
        refine ⟨hs, ?_⟩
        intro h
        exact hπ _ List.mem_cons_self (by rw [h])
    exact ih (osUpdate key s o) hupd
      (fun o' ho' => hπ o' (List.mem_cons_of_mem _ ho'))

/-! ## §6. The canonical-state σ-facts -/

/-- Live instances come from adds of the set. -/
theorem OSCore_canonical_bound
    {C : Sal.Emulation.Configuration (OSCore β key Q V qy).toCRDTSig}
    {F : Set (Op (OSOp β))} {s : OSState β} {q : OSElem β}
    (hs : IsCanonicalState C F s) (hq : q ∈ s) :
    (q.1, q.2.1, OSOp.add q.2.2) ∈ F := by
  obtain ⟨ρ, hperm, -, hfold⟩ := hs
  have hf : osFold key ∅ ρ = s := hfold
  rw [← hf] at hq
  exact (hperm.2 _).mp (OSCore_fold_bound hq)

/-- **Kill**: a live instance admits no same-key rem vis-after its add. -/
theorem OSCore_live_no_later_rem
    {C : Sal.Emulation.Configuration (OSCore β key Q V qy).toCRDTSig}
    {F : Set (Op (OSOp β))} {s : OSState β} {q : OSElem β}
    (hs : IsCanonicalState C F s) (hq : q ∈ s)
    (haF : (q.1, q.2.1, OSOp.add q.2.2) ∈ F)
    {tsr rdr : ℕ}
    (hrF : (tsr, rdr, OSOp.rem (key q.2.2)) ∈ F)
    (hvis : C.vis (q.1, q.2.1, OSOp.add q.2.2)
      (tsr, rdr, OSOp.rem (key q.2.2))) :
    False := by
  obtain ⟨ρ, hperm, hresp, hfold⟩ := hs
  have hf : osFold key ∅ ρ = s := hfold
  rw [← hf] at hq
  have hne_ar : ((q.1, q.2.1, OSOp.add q.2.2) : Op (OSOp β))
      ≠ (tsr, rdr, OSOp.rem (key q.2.2)) := by
    intro h
    have h22 : (OSOp.add q.2.2 : OSOp β) = OSOp.rem (key q.2.2) :=
      congrArg (fun o : Op (OSOp β) => o.2.2) h
    cases h22
  have hnc : ¬ (OSCore β key Q V qy).toCRDTSig.commutes
      (q.1, q.2.1, OSOp.add q.2.2)
      (tsr, rdr, OSOp.rem (key q.2.2)) :=
    OSCore_ncomm_add_rem q.1 q.2.1 q.2.2 tsr rdr
  have hedge : loOn C F (q.1, q.2.1, OSOp.add q.2.2)
      (tsr, rdr, OSOp.rem (key q.2.2)) := Or.inl ⟨hvis, hnc⟩
  have hrρ : ((tsr, rdr, OSOp.rem (key q.2.2)) : Op (OSOp β)) ∈ ρ :=
    (hperm.2 _).mpr hrF
  obtain ⟨α, γ, hsplit⟩ := List.append_of_mem hrρ
  subst hsplit
  have haρ : ((q.1, q.2.1, OSOp.add q.2.2) : Op (OSOp β))
      ∈ α ++ (tsr, rdr, OSOp.rem (key q.2.2)) :: γ := (hperm.2 _).mpr haF
  have hmid := List.pairwise_cons.mp (List.pairwise_append.mp hresp).2.1
  have haα : ((q.1, q.2.1, OSOp.add q.2.2) : Op (OSOp β)) ∈ α := by
    rcases List.mem_append.mp haρ with h | h
    · exact h
    · rcases List.mem_cons.mp h with h | h
      · exact absurd h hne_ar
      · exact absurd hedge (hmid.1 _ h)
  have hstep : osFold key ∅ (α ++ (tsr, rdr, OSOp.rem (key q.2.2)) :: γ)
      = osFold key (osUpdate key (osFold key ∅ α)
          (tsr, rdr, OSOp.rem (key q.2.2))) γ := by
    simp [osFold, List.foldl_append]
  rw [hstep] at hq
  have hkill : q ∉ osUpdate key (osFold key ∅ α)
      (tsr, rdr, OSOp.rem (key q.2.2)) := by
    intro h
    exact (mem_osUpdate_rem.mp h).2 rfl
  have hnoadd : ∀ o ∈ γ,
      o ≠ (q.1, q.2.1, OSOp.add q.2.2) := by
    intro o ho hoa
    rw [hoa] at ho
    have hnd := hperm.1
    rw [List.nodup_append] at hnd
    exact hnd.2.2 _ haα _ (List.mem_cons_of_mem _ ho) rfl
  exact OSCore_fold_stays_out γ _ hkill hnoadd hq

/-- **Live**: an add with no same-key rem vis-after it yields a live
instance. -/
theorem OSCore_no_later_kill_live
    {C : Sal.Emulation.Configuration (OSCore β key Q V qy).toCRDTSig}
    {F : Set (Op (OSOp β))} {s : OSState β} {q : OSElem β}
    (hs : IsCanonicalState C F s)
    (haF : (q.1, q.2.1, OSOp.add q.2.2) ∈ F)
    (hno : ∀ r ∈ F, (r : Op (OSOp β)).2.2 = OSOp.rem (key q.2.2) →
      ¬ C.vis (q.1, q.2.1, OSOp.add q.2.2) r) :
    q ∈ s := by
  obtain ⟨ρ, hperm, hresp, hfold⟩ := hs
  have hf : osFold key ∅ ρ = s := hfold
  rw [← hf]
  have haρ : ((q.1, q.2.1, OSOp.add q.2.2) : Op (OSOp β)) ∈ ρ :=
    (hperm.2 _).mpr haF
  obtain ⟨α, γ, hsplit⟩ := List.append_of_mem haρ
  subst hsplit
  have hcons := List.pairwise_cons.mp (List.pairwise_append.mp hresp).2.1
  -- no same-key rem in γ
  have hnorem : ∀ o ∈ γ, (o : Op (OSOp β)).2.2 ≠ OSOp.rem (key q.2.2) := by
    intro o ho hoT
    have hoF : o ∈ F := (hperm.2 o).mp
      (List.mem_append_right _ (List.mem_cons_of_mem _ ho))
    have hnovis : ¬ C.vis (q.1, q.2.1, OSOp.add q.2.2) o :=
      hno o hoF hoT
    rcases o with ⟨tso, rdo, opo⟩
    have hoT' : opo = OSOp.rem (key q.2.2) := hoT
    subst hoT'
    have hnc_oa : ¬ (OSCore β key Q V qy).toCRDTSig.commutes
        (tso, rdo, OSOp.rem (key q.2.2))
        (q.1, q.2.1, OSOp.add q.2.2) :=
      fun h => OSCore_ncomm_add_rem q.1 q.2.1 q.2.2 tso rdo
        (OSCore_commutes_symm h)
    have hedge : loOn C F (tso, rdo, OSOp.rem (key q.2.2))
        (q.1, q.2.1, OSOp.add q.2.2) := by
      by_cases hvo : C.vis (tso, rdo, OSOp.rem (key q.2.2))
          (q.1, q.2.1, OSOp.add q.2.2)
      · exact Or.inl ⟨hvo, hnc_oa⟩
      · refine Or.inr ⟨hvo, hnovis, ?_, ?_⟩
        · show (if key q.2.2 = key q.2.2
              then RcRes.Fst_then_snd else RcRes.Either)
            = RcRes.Fst_then_snd
          rw [if_pos rfl]
        · rintro ⟨e₃, he₃F, hve₃, hnce₃⟩
          have h₃T := OSCore_ncomm_add_dest hnce₃
          exact hno e₃ he₃F h₃T hve₃
    exact hcons.1 _ ho hedge
  have hstep : osFold key ∅
      (α ++ (q.1, q.2.1, OSOp.add q.2.2) :: γ)
      = osFold key (osUpdate key (osFold key ∅ α)
          (q.1, q.2.1, OSOp.add q.2.2)) γ := by
    simp [osFold, List.foldl_append]
  rw [hstep]
  refine OSCore_fold_stays_in γ _ ?_ hnorem
  rw [mem_osUpdate_add]
  exact Or.inl rfl

/-! ## §7. The maximal-rem trichotomy and `CDVC3` -/

/-- For a maximal `rem x`, every live `x`-keyed instance of `σ(U∖e)` is live
in the punctured downset. -/
theorem OSCore_rem_max_trichotomy
    {C : Sal.Emulation.Configuration (OSCore β key Q V qy).toCRDTSig}
    {U : Set (Op (OSOp β))} {A B : OSState β}
    {ts rid x : ℕ}
    (h_cl : ∀ a b, C.vis a b →
      ¬ (OSCore β key Q V qy).toCRDTSig.commutes a b → b ∈ U → a ∈ U)
    (h_e : (ts, rid, OSOp.rem x) ∈ U)
    (h_max : ∀ y ∈ U, y ≠ (ts, rid, OSOp.rem x) →
      ¬ loOn C U (ts, rid, OSOp.rem x) y)
    (hA : IsCanonicalState C (U \ {(ts, rid, OSOp.rem x)}) A)
    (hB : IsCanonicalState C
      (downset C (ts, rid, OSOp.rem x) \ {(ts, rid, OSOp.rem x)}) B)
    {q : OSElem β} (hqx : key q.2.2 = x) (hqA : q ∈ A) :
    q ∈ B := by
  subst hqx
  have h_dsub : downset C (ts, rid, OSOp.rem (key q.2.2)) ⊆ U :=
    downset_subset h_cl h_e
  -- the (unique, self-naming) add of the live instance
  have haU' := OSCore_canonical_bound hA hqA
  have hane : ((q.1, q.2.1, OSOp.add q.2.2) : Op (OSOp β))
      ≠ (ts, rid, OSOp.rem (key q.2.2)) := haU'.2
  have hnc_ae : ¬ (OSCore β key Q V qy).toCRDTSig.commutes
      (q.1, q.2.1, OSOp.add q.2.2)
      (ts, rid, OSOp.rem (key q.2.2)) :=
    OSCore_ncomm_add_rem q.1 q.2.1 q.2.2 ts rid
  by_cases hva : C.vis (q.1, q.2.1, OSOp.add q.2.2)
      (ts, rid, OSOp.rem (key q.2.2))
  · -- vis-before: the add is in the punctured downset and live there
    have haD : ((q.1, q.2.1, OSOp.add q.2.2) : Op (OSOp β))
        ∈ downset C (ts, rid, OSOp.rem (key q.2.2))
          \ {(ts, rid, OSOp.rem (key q.2.2))} :=
      ⟨Or.inr (Relation.TransGen.single ⟨hva, hnc_ae⟩), hane⟩
    refine OSCore_no_later_kill_live hB haD ?_
    intro r hrD hrT hvar
    have hrU' : r ∈ U \ {(ts, rid, OSOp.rem (key q.2.2))} :=
      ⟨h_dsub hrD.1, hrD.2⟩
    rcases r with ⟨tsr, rdr, opr⟩
    have hrT' : opr = OSOp.rem (key q.2.2) := hrT
    subst hrT'
    exact OSCore_live_no_later_rem hA hqA haU' hrU' hvar
  · by_cases hvea : C.vis (ts, rid, OSOp.rem (key q.2.2))
        (q.1, q.2.1, OSOp.add q.2.2)
    · -- vis-after the maximal rem: a vis-edge out of e, contradiction
      exfalso
      have hnc_ea : ¬ (OSCore β key Q V qy).toCRDTSig.commutes
          (ts, rid, OSOp.rem (key q.2.2))
          (q.1, q.2.1, OSOp.add q.2.2) :=
        fun h => hnc_ae (OSCore_commutes_symm h)
      exact h_max _ haU'.1 hane (Or.inl ⟨hvea, hnc_ea⟩)
    · -- concurrent: the rc-edge is unabsorbed, contradiction
      exfalso
      refine h_max _ haU'.1 hane (Or.inr ⟨hvea, hva, ?_, ?_⟩)
      · show (if key q.2.2 = key q.2.2
            then RcRes.Fst_then_snd else RcRes.Either)
            = RcRes.Fst_then_snd
        rw [if_pos rfl]
      · rintro ⟨e₃, he₃U, hve₃, hnce₃⟩
        have h₃T := OSCore_ncomm_add_dest hnce₃
        have h₃ne : e₃ ≠ (ts, rid, OSOp.rem (key q.2.2)) := by
          intro h
          rw [h] at hve₃
          exact hva hve₃
        rcases e₃ with ⟨ts₃, rd₃, op₃⟩
        have h₃T' : op₃ = OSOp.rem (key q.2.2) := h₃T
        subst h₃T'
        exact OSCore_live_no_later_rem hA hqA haU' ⟨he₃U, h₃ne⟩ hve₃

/-- **`CDVC3` for the OR-set core.** `add`-maximal: set algebra plus instance
freshness (the instance names its adder, which would have to be the maximal
event itself). `rem`-maximal: the trichotomy. -/
theorem OSCore_cdVC3 : CDVC3 (OSCore β key Q V qy) := by
  intro C U A B e _ _ _ h_cl h_e h_max hA hB
  -- rebind the projection-typed states at the concrete type, so that
  -- `Finset` instances resolve
  obtain ⟨A, hA'⟩ : ∃ A' : OSState β, A' = A := ⟨A, rfl⟩
  subst hA'
  obtain ⟨B, hB'⟩ : ∃ B' : OSState β, B' = B := ⟨B, rfl⟩
  subst hB'
  rcases e with ⟨ts, rid, op⟩
  cases op with
  | add b =>
    have hBt : ((ts, rid, b) : OSElem β) ∉ B := by
      intro hBt
      exact (OSCore_canonical_bound hB hBt).2 rfl
    show osMergeL B A (osUpdate key B (ts, rid, OSOp.add b))
        = osUpdate key A (ts, rid, OSOp.add b)
    apply Finset.ext
    intro q
    simp only [mem_osMergeL, mem_osUpdate_add]
    by_cases hqp : q = ((ts, rid, b) : OSElem β)
    · subst hqp
      simp [hBt]
    · by_cases hqA : q ∈ A <;> by_cases hqB : q ∈ B <;>
        simp [hqp, hqA, hqB]
  | rem x =>
    have himp : ∀ q : OSElem β, key q.2.2 = x → q ∈ A → q ∈ B :=
      fun q hqx hqA =>
        OSCore_rem_max_trichotomy h_cl h_e h_max hA hB hqx hqA
    show osMergeL B A (osUpdate key B (ts, rid, OSOp.rem x))
        = osUpdate key A (ts, rid, OSOp.rem x)
    apply Finset.ext
    intro q
    simp only [mem_osMergeL, mem_osUpdate_rem]
    by_cases hx : key q.2.2 = x
    · by_cases hqA : q ∈ A
      · have hqB : q ∈ B := himp q hx hqA
        simp [hqA, hqB, hx]
      · simp [hqA, hx]
    · by_cases hqA : q ∈ A <;> by_cases hqB : q ∈ B <;>
        simp [hqA, hqB, hx]

/-! ## §8. The feasible delta laws, the bundles, and the capstones -/

/-- The redistribution law is a propositional tautology for the OR-set-shaped
merge, **unconditional**, all five states arbitrary. -/
theorem osMergeL_redistribute (B t₀ t₁ t₂ u : OSState β) :
    osMergeL (osMergeL B t₀ u) (osMergeL B t₁ u) (osMergeL B t₂ u)
      = osMergeL B (osMergeL t₀ t₁ t₂) u := by
  apply Finset.ext
  intro q
  simp only [mem_osMergeL]
  by_cases hb : q ∈ B <;> by_cases h0 : q ∈ t₀ <;> by_cases h1 : q ∈ t₁ <;>
    by_cases h2 : q ∈ t₂ <;> by_cases hu : q ∈ u <;>
    simp [hb, h0, h1, h2, hu]

/-- **The feasible delta contract for the OR-set core.** -/
theorem OSCore_feasibleDeltaVCs3 : FeasibleDeltaVCs3 (OSCore β key Q V qy) := by
  refine ⟨?_, ?_, ?_⟩
  · -- feasible_init (holds unconditionally for the OR-set shape)
    intro C ev s _ _
    show osMergeL ∅ ∅ s = s
    apply Finset.ext
    intro q
    rw [mem_osMergeL]
    simp
  · -- feasible_local_redistribute
    intro C ev₁ ev₂ s₀ B t₁ s₂ e _ _ _ _ h_cl₁ _ he₁ he₂ _ hc₀ hB _ hc₂
    -- rebind the projection-typed states at the concrete type
    obtain ⟨s₀, h₀'⟩ : ∃ s₀' : OSState β, s₀' = s₀ := ⟨s₀, rfl⟩
    subst h₀'
    obtain ⟨B, hB'⟩ : ∃ B' : OSState β, B' = B := ⟨B, rfl⟩
    subst hB'
    obtain ⟨t₁, ht₁'⟩ : ∃ t₁' : OSState β, t₁' = t₁ := ⟨t₁, rfl⟩
    subst ht₁'
    obtain ⟨s₂, h₂'⟩ : ∃ s₂' : OSState β, s₂' = s₂ := ⟨s₂, rfl⟩
    subst h₂'
    rcases e with ⟨ts, rid, op⟩
    cases op with
    | add b =>
      -- instance freshness against B and s₀
      have hBt : ((ts, rid, b) : OSElem β) ∉ B := by
        intro hBt
        exact (OSCore_canonical_bound hB hBt).2 rfl
      have hs₀t : ((ts, rid, b) : OSElem β) ∉ s₀ := by
        intro hs₀t
        exact he₂ (OSCore_canonical_bound hc₀ hs₀t).2
      show osMergeL s₀
          (osMergeL B t₁ (osUpdate key B (ts, rid, OSOp.add b))) s₂
        = osMergeL B (osMergeL s₀ t₁ s₂)
            (osUpdate key B (ts, rid, OSOp.add b))
      apply Finset.ext
      intro q
      simp only [mem_osMergeL, mem_osUpdate_add]
      by_cases hqp : q = ((ts, rid, b) : OSElem β)
      · subst hqp
        simp [hBt, hs₀t]
      · by_cases hb : q ∈ B <;> by_cases h0 : q ∈ s₀ <;>
          by_cases h1 : q ∈ t₁ <;> by_cases h2 : q ∈ s₂ <;>
          simp [hqp, hb, h0, h1, h2]
    | rem x =>
      -- the X2 exclusion via the σ-facts
      have himp : ∀ q : OSElem β, key q.2.2 = x → q ∈ B → q ∈ s₂ →
          q ∈ s₀ := by
        intro q hqx hqB hqs₂
        subst hqx
        have ha' := OSCore_canonical_bound hB hqB
        have ha'' := OSCore_canonical_bound hc₂ hqs₂
        have haU : ((q.1, q.2.1, OSOp.add q.2.2) : Op (OSOp β))
            ∈ ev₁ ∩ ev₂ := ⟨downset_subset h_cl₁ he₁ ha'.1, ha''⟩
        refine OSCore_no_later_kill_live hc₀ haU ?_
        intro r hr₀ hrT hvar
        rcases r with ⟨tsr, rdr, opr⟩
        have hrT' : opr = OSOp.rem (key q.2.2) := hrT
        subst hrT'
        exact OSCore_live_no_later_rem hc₂ hqs₂ ha'' hr₀.2 hvar
      show osMergeL s₀
          (osMergeL B t₁ (osUpdate key B (ts, rid, OSOp.rem x))) s₂
        = osMergeL B (osMergeL s₀ t₁ s₂)
            (osUpdate key B (ts, rid, OSOp.rem x))
      apply Finset.ext
      intro q
      simp only [mem_osMergeL, mem_osUpdate_rem]
      by_cases hx : key q.2.2 = x
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
    exact osMergeL_redistribute B t₀ t₁ t₂ ((OSCore β key Q V qy).update B e)

theorem OSCore_updateVCs : UpdateVCs (OSCore β key Q V qy).toCRDTSig :=
  ⟨OSCore_rc_non_comm_directional, OSCore_no_rc_chain, OSCore_cond_comm_lift⟩

theorem OSCore_coreVCs3CD : CoreVCs3CD (OSCore β key Q V qy) :=
  ⟨OSCore_updateVCs, OSCore_mergeL_comm⟩

/-- The ternary Join Lemma for the OR-set core, the OR-set's route. -/
theorem OSCore_joinLemma3 : JoinLemma3 (OSCore β key Q V qy) :=
  join_lemma3_of_cd_feasible OSCore_coreVCs3CD OSCore_feasibleDeltaVCs3
    OSCore_cdVC3

open LabeledTS in
/-- **End-to-end RA-linearizability for the OR-set core** (convergence half),
for every payload, key, and query. -/
theorem oscore_ra_linearizable3
    (C : Configuration (OSCore β key Q V qy))
    (hReach : (labeledTS3 (OSCore β key Q V qy)).ReachableFrom
      (initConfig (OSCore β key Q V qy) trivial) C) :
    IsRALinearizable3 C :=
  ra_linearizable3_of_join OSCore_joinLemma3 C hReach

end

/-! ### The conditioned capstone, identity instantiation of the generic
framework -/

section
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.GoodConfig3H
open Sal.ConditionedMRDTs.FlatGeneric

/-- **The OR-set core over the generic framework** (the catalogue-capstone
form), universally in the payload, key, and query. -/
theorem OSCore_ra_linearizable3_eq (β : Type) [DecidableEq β] (key : β → ℕ)
    (Q V : Type) (qy : OSState β → Q → V)
    (C : Configuration (QSig (eqOfEq (OSCore β key Q V qy))
      (WTop (OSCore β key Q V qy)) (invPresTop fun _ => trivial)
      (congVCEq (OSCore β key Q V qy)) (invInvVCTop (OSCore β key Q V qy))))
    (hReach : (labeledTS3 _).ReachableFrom (initConfig _ trivial) C) :
    IsRALinearizable3Eq (eqOfEq (OSCore β key Q V qy))
      (WTop (OSCore β key Q V qy))
      (invPresTop fun _ => trivial) (congVCEq (OSCore β key Q V qy))
      (invInvVCTop (OSCore β key Q V qy)) C :=
  flat_ra_linearizable3_eq (fun _ => trivial) (fun _ _ => trivial)
    (contractJoinFull (ConditionedContract.ofVCs (OSCore β key Q V qy)
      OSCore_coreVCs3CD OSCore_feasibleDeltaVCs3 OSCore_cdVC3 trivial))
    C hReach

end

/-! ## Axiom audit -/

#print axioms oscore_ra_linearizable3
#print axioms OSCore_ra_linearizable3_eq

end Sal.ConditionedMRDTs
