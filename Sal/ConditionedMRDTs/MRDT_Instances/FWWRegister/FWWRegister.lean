import Sal.ConditionedMRDTs.Metatheory.Adequacy
import Sal.ConditionedMRDTs.Metatheory.ArbAdequacyReach
import Sal.ConditionedMRDTs.Metatheory.FlatGeneric_Bridge
import Sal.ConditionedMRDTs.Metatheory.HonestReach
import Sal.ConditionedMRDTs.Metatheory.GenHonest
import Mathlib.Order.WithBot
import Mathlib.Data.Prod.Lex
import Mathlib.Data.List.MinMax

/-!
# FWW reservation register — payload arbitration, and what honesty cannot buy

A register that can be **claimed once**: a seat reservation, a username, a
coupon code. Sequentially, the first `claim` sets it and later claims are
no-ops. Concurrently, the winner is the claim that is *first in Lamport
time*: the state carries the claim's timestamp and the merge takes the
minimum. This is the **positive complement** to the metadata-free kill-test
(`Refutations/LWW_Merge_Needs_Timestamps.lean`): arbitration whose key is
not in the state is impossible; arbitration whose key IS in the state is a
semilattice triviality. Since timestamps respect causality
(`vis a b → a.1 < b.1`), a causally later claim can never displace an
installed one — the min-rule only ever arbitrates between *concurrent*
claims, and it must (keeping the locally-first claim would make the outcome
delivery-order-dependent).

The state is `WithTop (ℕ ×ₗ ℕ ×ₗ ℕ)` — `⊤` for "unset", otherwise the
winning claim `(ts, replica, value)` under the lexicographic order — so the
entire convergence discharge is Mathlib's `min` algebra, and the safety
characterization (`fww_version_min`) is `List.minimum`: **at every version
of every reachable configuration, the register holds exactly the min-ts
claim of its event set** (`⊤` iff the set is empty). No honesty hypothesis:
folds of a semilattice are enumeration-free.

The generation discipline exists (`fwwApplicable`: claim only when unset —
what a well-behaved client checks) but note what it does **not** buy: two
honest concurrent claimants both see `⊤` and both claim; each locally wins
until the merge disabuses one. "Unset" is not stable under concurrent
honest extension — contrast the bounded counter's own-slot slack, which is.
A reservation is confirmed only at causal stability; a merge-based register
is never a mutex. (Formal contract shape: `GenHonest FWW fwwApplicable`;
no theorem consumes it, and per the safety memo none should.)
-/

set_option maxHeartbeats 400000

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

/-! ## §1  The datatype -/

inductive FWWOp : Type where
  | claim (v : ℕ)
deriving DecidableEq

/-- A claim, ordered lexicographically: timestamp first (the arbitration
key), then replica and value (deterministic tiebreak; distinct events have
distinct timestamps anyway). -/
abbrev FWWClaim : Type := Lex (ℕ × Lex (ℕ × ℕ))

/-- `⊤` = unset; otherwise the currently winning claim. -/
abbrev FWWState : Type := WithTop FWWClaim

def fwwVal (e : Op FWWOp) : ℕ :=
  match e.2.2 with
  | .claim v => v

/-- The claim triple an event installs. -/
def fwwClaim (e : Op FWWOp) : FWWClaim :=
  toLex (e.1, toLex (e.2.1, fwwVal e))

def fwwUpdate (s : FWWState) (e : Op FWWOp) : FWWState :=
  min s ↑(fwwClaim e)

/-- Peepul-style three-way merge, degenerate: the state only ever moves
down the semilattice, so the LCA slot is redundant — `min` of the branches. -/
def fwwMergeL (_l a b : FWWState) : FWWState := min a b

noncomputable def FWW : ConditionedMRDTSig where
  State := FWWState
  dec_state := inferInstance
  init := ⊤
  AppOp := FWWOp
  dec_op := inferInstance
  Query := Unit
  Value := FWWState
  update := fwwUpdate
  merge := fun a b => fwwMergeL ⊤ a b
  query := fun s _ => s
  rc := fun _ _ => RcRes.Either
  mergeL := fwwMergeL
  merge_init_slice := fun _ _ => rfl
  Inv := fun _ => True
  applicable := fun _ _ => True

theorem FWW_update_eq (s : FWWState) (e : Op FWWOp) :
    FWW.update s e = min s ↑(fwwClaim e) := rfl

theorem FWW_mergeL_eq (l a b : FWWState) : FWW.mergeL l a b = min a b := rfl

theorem FWW_init_eq : FWW.init = (⊤ : FWWState) := rfl

theorem FWW_rc_either : ∀ o₁ o₂ : Op FWW.AppOp,
    FWW.toCRDTSig.rc o₁ o₂ = RcRes.Either := fun _ _ => rfl

/-! ## §2  The flat discharge (pure `min` algebra) -/

theorem FWW_all_comm : ∀ a b : Op FWW.AppOp, FWW.toCRDTSig.commutes a b := by
  intro a b s
  show fwwUpdate (fwwUpdate s a) b = fwwUpdate (fwwUpdate s b) a
  unfold fwwUpdate
  simp [min_comm, min_assoc, min_left_comm]

theorem FWW_updateVCs : UpdateVCs FWW.toCRDTSig := by
  refine ⟨?_, ?_, ?_⟩
  · intro o₁ o₂ _ _
    constructor
    · intro h
      exact absurd (FWW_all_comm o₁ o₂) h
    · rintro (h | h) <;>
        (rw [FWW_rc_either] at h; exact RcRes.noConfusion h)
  · intro o₁ o₂ o₃ _ _
    rintro ⟨h, _⟩
    rw [FWW_rc_either] at h
    exact RcRes.noConfusion h
  · intro s e e' e'' π _ _ _ h_rc _
    rw [FWW_rc_either] at h_rc
    exact RcRes.noConfusion h_rc

theorem FWW_coreVCs3 : CoreVCs3 FWW := by
  refine ⟨FWW_updateVCs, ?_, ?_, ?_, ?_⟩
  · intro l a b
    show fwwMergeL l a b = fwwMergeL l b a
    unfold fwwMergeL
    exact min_comm (α := FWWState) a b
  · intro s
    show fwwMergeL ⊤ ⊤ s = s
    unfold fwwMergeL
    exact min_eq_right le_top
  · rintro l a b e
    show fwwMergeL (fwwUpdate l e) (fwwUpdate a e) (fwwUpdate b e)
        = fwwUpdate (fwwMergeL l a b) e
    unfold fwwMergeL fwwUpdate
    simp [min_assoc, min_left_comm]
  · rintro a e π₀ π₂ _ _
    generalize applySeq FWW.toCRDTSig FWW.init π₀ = X
    generalize applySeq FWW.toCRDTSig FWW.init π₂ = Y
    show fwwMergeL X (fwwUpdate a e) Y = fwwUpdate (fwwMergeL X a Y) e
    unfold fwwMergeL fwwUpdate
    simp [min_comm, min_assoc, min_left_comm]

theorem FWW_deltaVCs3 : DeltaVCs3 FWW := by
  constructor
  · intro m x₀ x₁ x₂ c
    show fwwMergeL (fwwMergeL m x₀ c) (fwwMergeL m x₁ c) (fwwMergeL m x₂ c)
        = fwwMergeL m (fwwMergeL x₀ x₁ x₂) c
    unfold fwwMergeL
    simp [min_comm, min_left_comm]
  · intro l m x c y
    show fwwMergeL l (fwwMergeL m x c) y = fwwMergeL m (fwwMergeL l x y) c
    unfold fwwMergeL
    simp [min_comm, min_left_comm]

open LabeledTS in
/-- End-to-end RA-linearizability (convergence) for the FWW register. -/
theorem fww_ra_linearizable3
    (C : Configuration FWW)
    (hReach : (labeledTS3 FWW).ReachableFrom (initConfig FWW trivial) C) :
    IsRALinearizable3 C :=
  ra_linearizable3_via_capstone FWW_coreVCs3.toCD FWW_coreVCs3.update_core
    (feasibleDeltaVCs3_of_delta FWW_coreVCs3 FWW_deltaVCs3)
    (cdVC3_of_all_comm FWW_coreVCs3 FWW_all_comm) C hReach

/-! ## §3  The fold is a list minimum; the version characterization -/

/-- Folding from any accumulator computes the minimum of the accumulator and
the claims. -/
theorem fww_fold_acc : ∀ (ρ : List (Op FWWOp)) (acc : FWWState),
    applySeq FWW.toCRDTSig acc ρ = min acc (ρ.map fwwClaim).minimum := by
  intro ρ
  induction ρ with
  | nil =>
    intro acc
    show acc = min acc (List.minimum (List.map fwwClaim []))
    rw [List.map_nil, List.minimum_nil, min_eq_left le_top]
  | cons e ρ ih =>
    intro acc
    show applySeq FWW.toCRDTSig (fwwUpdate acc e) ρ = _
    rw [ih]
    unfold fwwUpdate
    rw [List.map_cons, List.minimum_cons, min_assoc]

/-- The fold from the initial (unset) register is exactly the minimum claim. -/
theorem fww_fold_minimum (ρ : List (Op FWWOp)) :
    applySeq FWW.toCRDTSig FWW.init ρ = (ρ.map fwwClaim).minimum := by
  rw [fww_fold_acc, FWW_init_eq]
  exact min_eq_right (le_top (α := FWWState))

open LabeledTS in
/-- `GoodConfig3` for the register: the generic honest-reachability induction
under the trivial contract (the Join is unconditional — the CD route). -/
theorem fww_goodConfig3
    (C : Configuration FWW)
    (hReach : (labeledTS3 FWW).ReachableFrom (initConfig FWW trivial) C) :
    GoodConfig3 C :=
  goodConfig3_of_honest_reach
    (fun _ _ => (join_lemma3_of_cd FWW_coreVCs3 FWW_deltaVCs3
      (cdVC3_of_all_comm FWW_coreVCs3 FWW_all_comm)).at _)
    (honestReach_of_reachable hReach)

open LabeledTS in
/-- **The register holds exactly the min-timestamp claim of its event set, at
every version of every reachable configuration**: it is a lower bound on all
claims, it is attained by one of them, and it is unset exactly on the empty
set. Deterministic first-writer-wins, with "first" arbitrated in Lamport
time among concurrent claimants. No honesty hypothesis — semilattice folds
are enumeration-free. -/
theorem fww_version_min
    (C : Configuration FWW)
    (hReach : (labeledTS3 FWW).ReachableFrom (initConfig FWW trivial) C) :
    ∀ (v : Version) (s : FWWState) (E : Set (Op FWWOp)),
      C.ver v = some (s, E) →
      (∀ e ∈ E, s ≤ ↑(fwwClaim e)) ∧
      (s = ⊤ ↔ E = ∅) ∧
      (∀ m : FWWClaim, s = ↑m → ∃ e ∈ E, fwwClaim e = m) := by
  intro v s E hv
  obtain ⟨ρ, hperm, _, hfold⟩ := (fww_goodConfig3 C hReach).canonical v s E hv
  have hs : s = (ρ.map fwwClaim).minimum := by
    rw [← hfold, fww_fold_minimum]
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    rw [hs]
    exact List.minimum_le_of_mem' (List.mem_map_of_mem ((hperm.2 e).mpr he))
  · constructor
    · intro htop
      rw [hs] at htop
      have hnil : ρ.map fwwClaim = [] := List.minimum_eq_top.mp htop
      have hρnil : ρ = [] := List.map_eq_nil_iff.mp hnil
      ext e
      simp only [Set.mem_empty_iff_false, iff_false]
      intro he
      rw [← List.mem_nil_iff e, ← hρnil]
      exact (hperm.2 e).mpr he
    · intro hE
      rw [hs]
      have hρnil : ρ = [] := by
        cases ρ with
        | nil => rfl
        | cons e ρ' =>
          exact absurd (hE ▸ (hperm.2 e).mp List.mem_cons_self)
            (by simp)
      rw [hρnil]
      rfl
  · intro m hm
    rw [hs] at hm
    have hmem : m ∈ ρ.map fwwClaim := List.minimum_mem hm
    obtain ⟨e, he, hce⟩ := List.mem_map.mp hmem
    exact ⟨e, (hperm.2 e).mp he, hce⟩

/-! ## §4  The generation discipline, and its honest limits -/

/-- What a well-behaved client checks before claiming: the register is unset
in its causal past. Contract shape: `GenHonest FWW fwwApplicable`.

Deliberately, **no theorem consumes this**: "unset" is not stable under
concurrent honest extension (two honest claimants both see `⊤`), so honesty
buys no exclusivity — the min-timestamp payload arbitrates, and
`fww_version_min` holds without any honesty hypothesis. The check's value is
client-side (don't waste a claim that will lose to a causally earlier one);
exclusivity exists only after causal stability. This is the boundary the
safety memo (`Development/GENERIC_SAFETY_PENPAPER.md`) draws: conditioning
delivers safety exactly for invariants stable under concurrent honest
extension. -/
def fwwApplicable (_e : Op FWWOp) (s : FWWState) : Prop := s = ⊤

section
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.GoodConfig3H
open Sal.ConditionedMRDTs.FlatGeneric

/-- **FWW register over the generic framework** (identity instantiation). -/
theorem FWW_ra_linearizable3_eq
    (C : Configuration (QSig (eqOfEq Sal.ConditionedMRDTs.FWW) (WTop Sal.ConditionedMRDTs.FWW)
      (invPresTop fun _ => trivial) (congVCEq Sal.ConditionedMRDTs.FWW)
      (invInvVCTop Sal.ConditionedMRDTs.FWW)))
    (hReach : (labeledTS3 _).ReachableFrom (initConfig _ trivial) C) :
    IsRALinearizable3Eq (eqOfEq Sal.ConditionedMRDTs.FWW) (WTop Sal.ConditionedMRDTs.FWW)
      (invPresTop fun _ => trivial) (congVCEq Sal.ConditionedMRDTs.FWW)
      (invInvVCTop Sal.ConditionedMRDTs.FWW) C :=
  flat_ra_linearizable3_eq (fun _ => trivial) (fun _ _ => trivial)
    (contractJoinFull (ConditionedContract.ofVCs Sal.ConditionedMRDTs.FWW
      Sal.ConditionedMRDTs.FWW_coreVCs3.toCD
      (Sal.ConditionedMRDTs.feasibleDeltaVCs3_of_delta Sal.ConditionedMRDTs.FWW_coreVCs3
        Sal.ConditionedMRDTs.FWW_deltaVCs3)
      (Sal.ConditionedMRDTs.cdVC3_of_all_comm Sal.ConditionedMRDTs.FWW_coreVCs3
        Sal.ConditionedMRDTs.FWW_all_comm) trivial)) C hReach

end

#print axioms fww_ra_linearizable3
#print axioms fww_version_min
#print axioms FWW_ra_linearizable3_eq

end Sal.ConditionedMRDTs
