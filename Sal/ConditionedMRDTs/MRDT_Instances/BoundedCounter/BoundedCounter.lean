import Sal.ConditionedMRDTs.Metatheory.Adequacy
import Sal.ConditionedMRDTs.Metatheory.ArbAdequacyReach
import Sal.ConditionedMRDTs.Metatheory.FlatGeneric_Bridge
import Sal.ConditionedMRDTs.Metatheory.HonestReach
import Sal.ConditionedMRDTs.Metatheory.GenHonest
import Sal.ConditionedMRDTs.Metatheory.GenericSafety
import Sal.ConditionedMRDTs.Metatheory.EscrowSafety

/-!
# Bounded Counter: convergence, the client contract, and the bound as a theorem

A genuinely conditioned MRDT instance. Mirror of `Sal/CRDTs/Bounded_Counter`
(Sypytkowski's state-based bounded counter, per-replica escrow; transfers
omitted here): state is a pair of per-replica grow-only tallies `(incs, decs)`,
`Inc`/`Dec` bump the issuing replica's own slot, and the three-way merge is
per-slot group merge `a + b − l` (inclusion–exclusion on event counts).

Three layers:

* **§1–§2 Convergence (flat).** All operations commute (distinct slots, or
  addition on the same slot), so the eight VCs discharge along the PN-Counter's
  route and the instance rides the generic framework at the identity
  instantiation (`BC_ra_linearizable3_eq`).
* **§3 The client contract.** The CRDT file enforces the bound "operationally
  by well-behaved clients". Here that is formal: `BCInv` (per-replica
  `0 ≤ decs r ≤ incs r`), `bcApplicable` (a `Dec` needs slack in the issuing
  replica's own slots, positive and checkable against the issuing replica's
  state), the conditioned signature `BCCond` packaging them, and
  `bcApplicable_inv_pres`: an applicable step preserves the invariant.
* **§4–§6 The bound as a reachability theorem.** `BCHonest C` says every `Dec`
  in the configuration's history was applicable at the fold of its causal past,
  "well-behaved clients", stated on the execution. The headline
  `bc_version_inv`: at every reachable configuration, **every version of every
  honest execution satisfies the invariant**; corollary `bc_value_nonneg`, the
  counter's value (over any finite set of replicas) is non-negative. It is a
  corollary of the generic safety metatheorem
  (`version_inv_on_of_causal_canonical`): the counter discharges
  `CausalCanonical` pointwise (all ops commute, `rc ≡ Either`) and the fused
  stability obligation `SafetyStepOn`, whose residue is that extras in a causal
  prefix are cross-replica, slots are order-free per-slot event counts (§4),
  and the guard reads only the issuer's own slots.
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

/-! ## §1  The mirror -/

inductive BCOp : Type where
  | inc
  | dec
deriving DecidableEq

abbrev BCState : Type := (ℕ → ℤ) × (ℕ → ℤ)

/-- Bump `f` at slot `r`. -/
def bcBump (f : ℕ → ℤ) (r : ℕ) : ℕ → ℤ := fun k => if k = r then f k + 1 else f k

def bcUpdate (s : BCState) (o : Op BCOp) : BCState :=
  match o.2.2 with
  | .inc => (bcBump s.1 o.2.1, s.2)
  | .dec => (s.1, bcBump s.2 o.2.1)

def bcMergeL (l a b : BCState) : BCState :=
  (fun k => a.1 k + b.1 k - l.1 k, fun k => a.2 k + b.2 k - l.2 k)

noncomputable def BC : ConditionedMRDTSig where
  State := BCState
  dec_state := fun a b => Classical.propDecidable (a = b)
  init := (fun _ => 0, fun _ => 0)
  AppOp := BCOp
  dec_op := inferInstance
  Query := ℕ
  Value := ℤ
  update := bcUpdate
  merge := fun a b => bcMergeL (fun _ => 0, fun _ => 0) a b
  query := fun s r => s.1 r - s.2 r
  rc := fun _ _ => RcRes.Either
  mergeL := bcMergeL
  merge_init_slice := fun _ _ => rfl
  Inv := fun _ => True
  applicable := fun _ _ => True

/-! Component-level reduction lemmas: everything downstream is `omega` on
these. -/

theorem bcBump_apply (f : ℕ → ℤ) (r k : ℕ) :
    bcBump f r k = f k + (if k = r then 1 else 0) := by
  by_cases h : k = r <;> simp [bcBump, h]

theorem bcUpdate_inc_fst (s : BCState) (ts r k : ℕ) :
    (bcUpdate s (ts, r, BCOp.inc)).1 k = s.1 k + (if k = r then 1 else 0) := by
  by_cases h : k = r <;> simp [bcUpdate, bcBump, h]

theorem bcUpdate_inc_snd (s : BCState) (ts r k : ℕ) :
    (bcUpdate s (ts, r, BCOp.inc)).2 k = s.2 k := rfl

theorem bcUpdate_dec_fst (s : BCState) (ts r k : ℕ) :
    (bcUpdate s (ts, r, BCOp.dec)).1 k = s.1 k := rfl

theorem bcUpdate_dec_snd (s : BCState) (ts r k : ℕ) :
    (bcUpdate s (ts, r, BCOp.dec)).2 k = s.2 k + (if k = r then 1 else 0) := by
  by_cases h : k = r <;> simp [bcUpdate, bcBump, h]

theorem bcMergeL_fst (l a b : BCState) (k : ℕ) :
    (bcMergeL l a b).1 k = a.1 k + b.1 k - l.1 k := rfl

theorem bcMergeL_snd (l a b : BCState) (k : ℕ) :
    (bcMergeL l a b).2 k = a.2 k + b.2 k - l.2 k := rfl

theorem BC_update_eq (s : BCState) (o : Op BCOp) :
    BC.update s o = bcUpdate s o := rfl

theorem BC_mergeL_eq (l a b : BCState) : BC.mergeL l a b = bcMergeL l a b := rfl

theorem BC_init_fst (k : ℕ) : BC.init.1 k = 0 := rfl

theorem BC_init_snd (k : ℕ) : BC.init.2 k = 0 := rfl

theorem BC_rc_either : ∀ o₁ o₂ : Op BC.AppOp,
    BC.toCRDTSig.rc o₁ o₂ = RcRes.Either := fun _ _ => rfl

/-- Two `BCState`s with equal slot values are equal. -/
theorem bcState_ext {s t : BCState}
    (h1 : ∀ k, s.1 k = t.1 k) (h2 : ∀ k, s.2 k = t.2 k) : s = t := by
  obtain ⟨s1, s2⟩ := s
  obtain ⟨t1, t2⟩ := t
  simp only [Prod.mk.injEq]
  exact ⟨funext h1, funext h2⟩

/-! ## §2  The flat discharge (the PN-Counter's route, pointwise) -/

theorem BC_all_comm : ∀ a b : Op BC.AppOp, BC.toCRDTSig.commutes a b := by
  rintro ⟨tsa, ra, opa⟩ ⟨tsb, rb, opb⟩ s
  show bcUpdate (bcUpdate s (tsa, ra, opa)) (tsb, rb, opb)
      = bcUpdate (bcUpdate s (tsb, rb, opb)) (tsa, ra, opa)
  cases opa <;> cases opb <;>
    refine bcState_ext (fun k => ?_) (fun k => ?_) <;>
    simp only [bcUpdate_inc_fst, bcUpdate_inc_snd, bcUpdate_dec_fst,
      bcUpdate_dec_snd] <;>
    split_ifs <;> omega

theorem BC_updateVCs : UpdateVCs BC.toCRDTSig := by
  refine ⟨?_, ?_, ?_⟩
  · intro o₁ o₂ _ _
    constructor
    · intro h
      exact absurd (BC_all_comm o₁ o₂) h
    · rintro (h | h) <;>
        (rw [BC_rc_either] at h; exact RcRes.noConfusion h)
  · intro o₁ o₂ o₃ _ _
    rintro ⟨h, _⟩
    rw [BC_rc_either] at h
    exact RcRes.noConfusion h
  · intro s e e' e'' π _ _ _ h_rc _
    rw [BC_rc_either] at h_rc
    exact RcRes.noConfusion h_rc

theorem BC_coreVCs3 : CoreVCs3 BC := by
  refine ⟨BC_updateVCs, ?_, ?_, ?_, ?_⟩
  · intro l a b
    refine bcState_ext (fun k => ?_) (fun k => ?_) <;>
      simp only [BC_mergeL_eq, bcMergeL_fst, bcMergeL_snd] <;> omega
  · intro s
    refine bcState_ext (fun k => ?_) (fun k => ?_) <;>
      simp only [BC_mergeL_eq, bcMergeL_fst, bcMergeL_snd, BC_init_fst,
        BC_init_snd] <;> omega
  · rintro l a b ⟨ts, r, op⟩
    show bcMergeL (bcUpdate l (ts, r, op)) (bcUpdate a (ts, r, op))
        (bcUpdate b (ts, r, op)) = bcUpdate (bcMergeL l a b) (ts, r, op)
    cases op <;>
      refine bcState_ext (fun k => ?_) (fun k => ?_) <;>
      simp only [bcMergeL_fst, bcMergeL_snd,
        bcUpdate_inc_fst, bcUpdate_inc_snd, bcUpdate_dec_fst,
        bcUpdate_dec_snd] <;>
      omega
  · rintro a ⟨ts, r, op⟩ π₀ π₂ _ _
    generalize applySeq BC.toCRDTSig BC.init π₀ = X
    generalize applySeq BC.toCRDTSig BC.init π₂ = Y
    show bcMergeL X (bcUpdate a (ts, r, op)) Y
        = bcUpdate (bcMergeL X a Y) (ts, r, op)
    cases op <;>
      refine bcState_ext (fun k => ?_) (fun k => ?_) <;>
      simp only [bcMergeL_fst, bcMergeL_snd,
        bcUpdate_inc_fst, bcUpdate_inc_snd, bcUpdate_dec_fst,
        bcUpdate_dec_snd] <;>
      omega

theorem BC_deltaVCs3 : DeltaVCs3 BC := by
  constructor
  · intro m x₀ x₁ x₂ c
    refine bcState_ext (fun k => ?_) (fun k => ?_) <;>
      simp only [BC_mergeL_eq, bcMergeL_fst, bcMergeL_snd] <;> omega
  · intro l m x c y
    refine bcState_ext (fun k => ?_) (fun k => ?_) <;>
      simp only [BC_mergeL_eq, bcMergeL_fst, bcMergeL_snd] <;> omega

open LabeledTS in
/-- End-to-end RA-linearizability (convergence half) for the bounded counter. -/
theorem bc_ra_linearizable3
    (C : Configuration BC)
    (hReach : (labeledTS3 BC).ReachableFrom
      (initConfig BC trivial) C) :
    IsRALinearizable3 C :=
  ra_linearizable3_via_capstone BC_coreVCs3.toCD BC_coreVCs3.update_core
    (feasibleDeltaVCs3_of_delta BC_coreVCs3 BC_deltaVCs3)
    (cdVC3_of_all_comm BC_coreVCs3 BC_all_comm) C hReach

/-! ## §3  The client contract: invariant and applicability -/

/-- Per-replica escrow invariant: every replica's decrement tally is
non-negative and within its own increment tally. The counter's global value is
the sum of the per-replica slacks, hence non-negative (`bc_value_nonneg`). -/
def BCInv (s : BCState) : Prop := ∀ r, 0 ≤ s.2 r ∧ s.2 r ≤ s.1 r

/-- The client check of the CRDT file, made formal: a `Dec` needs slack in the
issuing replica's OWN slots, positive, and checkable against the issuing
replica's state. `Inc` is always legal. -/
def bcApplicable (o : Op BCOp) (s : BCState) : Prop :=
  match o.2.2 with
  | .inc => True
  | .dec => s.2 o.2.1 + 1 ≤ s.1 o.2.1

/-- The conditioned signature: the same datatype, carrying its contract. -/
noncomputable def BCCond : ConditionedMRDTSig where
  toMRDTSig := BC.toMRDTSig
  Inv := BCInv
  applicable := bcApplicable

/-- An applicable step preserves the invariant: the contract is locally
maintainable at the issuing replica. -/
theorem bcApplicable_inv_pres {s : BCState} {o : Op BCOp}
    (hInv : BCInv s) (happ : bcApplicable o s) :
    BCInv (bcUpdate s o) := by
  obtain ⟨ts, r, op⟩ := o
  intro k
  have h1 := hInv k
  cases op with
  | inc =>
    rw [bcUpdate_inc_fst, bcUpdate_inc_snd]
    split_ifs <;> omega
  | dec =>
    have h2 : s.2 r + 1 ≤ s.1 r := happ
    rw [bcUpdate_dec_fst, bcUpdate_dec_snd]
    by_cases hk : k = r
    · subst hk
      rw [if_pos rfl]
      omega
    · rw [if_neg hk]
      omega

/-! ## §4  Fold states are per-slot event counts -/

def bcIsIncAt (r : ℕ) (e : Op BCOp) : Bool :=
  match e.2.2 with
  | .inc => decide (e.2.1 = r)
  | .dec => false

def bcIsDecAt (r : ℕ) (e : Op BCOp) : Bool :=
  match e.2.2 with
  | .inc => false
  | .dec => decide (e.2.1 = r)

theorem bc_fold_incs (π : List (Op BCOp)) (s : BCState) (r : ℕ) :
    (applySeq BC.toCRDTSig s π).1 r = s.1 r + (π.countP (bcIsIncAt r) : ℤ) := by
  induction π generalizing s with
  | nil => simp [applySeq]
  | cons o π ih =>
    obtain ⟨ts, ro, op⟩ := o
    have hstep : applySeq BC.toCRDTSig s ((ts, ro, op) :: π)
        = applySeq BC.toCRDTSig (bcUpdate s (ts, ro, op)) π := rfl
    rw [hstep, ih, List.countP_cons]
    cases op with
    | inc =>
      rw [bcUpdate_inc_fst]
      by_cases h : ro = r
      · subst h
        simp only [bcIsIncAt, decide_true, if_true]
        push_cast
        omega
      · have h' : ¬ (r = ro) := fun hh => h hh.symm
        simp only [bcIsIncAt, h, decide_false, if_neg h']
        push_cast
        omega
    | dec =>
      rw [bcUpdate_dec_fst]
      simp only [bcIsIncAt]
      push_cast
      omega

theorem bc_fold_decs (π : List (Op BCOp)) (s : BCState) (r : ℕ) :
    (applySeq BC.toCRDTSig s π).2 r = s.2 r + (π.countP (bcIsDecAt r) : ℤ) := by
  induction π generalizing s with
  | nil => simp [applySeq]
  | cons o π ih =>
    obtain ⟨ts, ro, op⟩ := o
    have hstep : applySeq BC.toCRDTSig s ((ts, ro, op) :: π)
        = applySeq BC.toCRDTSig (bcUpdate s (ts, ro, op)) π := rfl
    rw [hstep, ih, List.countP_cons]
    cases op with
    | dec =>
      rw [bcUpdate_dec_snd]
      by_cases h : ro = r
      · subst h
        simp only [bcIsDecAt, decide_true, if_true]
        push_cast
        omega
      · have h' : ¬ (r = ro) := fun hh => h hh.symm
        simp only [bcIsDecAt, h, decide_false, if_neg h']
        push_cast
        omega
    | inc =>
      rw [bcUpdate_inc_snd]
      simp only [bcIsDecAt]
      push_cast
      omega

/-! ## §5  The safety obligations discharged

`bc_version_inv` is a corollary of the generic
`version_inv_on_of_causal_canonical` (`Metatheory/GenericSafety.lean`). The
per-instance residue is: extras in a causal prefix are cross-replica (the
generic `countP_prefix_eq_causal_past`), slots are order-free counts
(`bc_fold_incs`/`bc_fold_decs`), and the guard reads only the issuer's own
slots (`bcApplicable_inv_pres` closes). -/

theorem bc_inv_init : BCInv BC.init := fun _ => ⟨le_refl 0, le_refl 0⟩

private theorem bcIsIncAt_rep {r : ℕ} {x : Op BCOp}
    (h : bcIsIncAt r x = true) : x.2.1 = r := by
  obtain ⟨ts, ro, op⟩ := x
  cases op with
  | inc => simpa [bcIsIncAt] using h
  | dec => simp [bcIsIncAt] at h

private theorem bcIsDecAt_rep {r : ℕ} {x : Op BCOp}
    (h : bcIsDecAt r x = true) : x.2.1 = r := by
  obtain ⟨ts, ro, op⟩ := x
  cases op with
  | inc => simp [bcIsDecAt] at h
  | dec => simpa [bcIsDecAt] using h

/-- **The fused stability obligation** for the counter's conditioning pair
`(BCInv, bcApplicable)`: an `inc` needs no guard; for a `dec` by `r`, both
`r`-slots agree between the causal-prefix fold and the causal-past fold (the
slots are event counts and every extra event of the prefix is cross-replica),
so the issuer's own slack check transfers and `bcApplicable_inv_pres` closes. -/
theorem bc_safetyStep : SafetyStepOn BC BCInv bcApplicable := by
  intro C E S e σS σP hEev hEcl heE hSsub heS hScl hfut hpast hσS hσP hInv happ
  obtain ⟨ts, r, op⟩ := e
  cases op with
  | inc => exact bcApplicable_inv_pres (o := (ts, r, BCOp.inc)) hInv trivial
  | dec =>
    obtain ⟨ρS, hpS, _hrS, hfS⟩ := hσS
    obtain ⟨ρP, hpP, _hrP, hfP⟩ := hσP
    have hinc : ρS.countP (bcIsIncAt r) = ρP.countP (bcIsIncAt r) :=
      countP_prefix_eq_causal_past hEev hSsub heE heS hfut hpast hpS hpP
        (bcIsIncAt r) (fun _ hx => bcIsIncAt_rep hx)
    have hdec : ρS.countP (bcIsDecAt r) = ρP.countP (bcIsDecAt r) :=
      countP_prefix_eq_causal_past hEev hSsub heE heS hfut hpast hpS hpP
        (bcIsDecAt r) (fun _ hx => bcIsDecAt_rep hx)
    have hfS' : applySeq BC.toCRDTSig BC.init ρS = σS := hfS
    have hfP' : applySeq BC.toCRDTSig BC.init ρP = σP := hfP
    have hS1 : σS.1 r = (ρS.countP (bcIsIncAt r) : ℤ) := by
      rw [← hfS', bc_fold_incs, BC_init_fst]; omega
    have hS2 : σS.2 r = (ρS.countP (bcIsDecAt r) : ℤ) := by
      rw [← hfS', bc_fold_decs, BC_init_snd]; omega
    have hP1 : σP.1 r = (ρP.countP (bcIsIncAt r) : ℤ) := by
      rw [← hfP', bc_fold_incs, BC_init_fst]; omega
    have hP2 : σP.2 r = (ρP.countP (bcIsDecAt r) : ℤ) := by
      rw [← hfP', bc_fold_decs, BC_init_snd]; omega
    have happ' : σP.2 r + 1 ≤ σP.1 r := happ
    have happS : bcApplicable (ts, r, BCOp.dec) σS := by
      show σS.2 r + 1 ≤ σS.1 r
      omega
    exact bcApplicable_inv_pres hInv happS

/-! ## §6  Honest histories and the bound -/

/-- **The client contract, on the execution**: every decrement in the
configuration's history was applicable at the fold of its causal past: the
issuing replica checked its own slack against what it had seen. (This is the
bounded counter's `HonestDelivery`; the CRDT file's "the bound is enforced
operationally by well-behaved clients", stated formally.) -/
def BCHonest (C : Configuration BC) : Prop :=
  ∀ e ∈ C.events, e.2.2 = BCOp.dec →
    ∀ π : List (Op BCOp),
      listPermOf π {e' ∈ C.events | C.vis e' e} →
      bcApplicable e (applySeq BC.toCRDTSig BC.init π)

/-- `BCHonest` is exactly the generic honesty shape at `P := bcApplicable`:
the `dec`-guard of `BCHonest` is immaterial because `bcApplicable` is `True`
on `inc`. -/
theorem BCHonest_iff_genHonest (C : Configuration BC) :
    BCHonest C ↔ GenHonest BC bcApplicable C := by
  constructor
  · intro hHon e he π hπ
    obtain ⟨ts, r, op⟩ := e
    cases op with
    | inc => show True; trivial
    | dec => exact hHon (ts, r, BCOp.dec) he rfl π hπ
  · intro hGen e he _hdec π hπ
    exact hGen e he π hπ

open LabeledTS in
/-- The reachability invariant for the bounded counter: the generic
honest-reachability induction (`goodConfig3_of_honest_reach`) under the
trivial contract: the counter's Join is unconditional (the CD route). -/
theorem bc_goodConfig3
    (C : Configuration BC)
    (hReach : (labeledTS3 BC).ReachableFrom (initConfig BC trivial) C) :
    GoodConfig3 C :=
  goodConfig3_of_honest_reach
    (fun _ _ => (join_lemma3_of_cd BC_coreVCs3 BC_deltaVCs3
      (cdVC3_of_all_comm BC_coreVCs3 BC_all_comm)).at _)
    (honestReach_of_reachable hReach)

/-- The ∃-form honesty (`HonestAppOn`) from the client contract: `BCHonest`'s
∀-enumeration form covers in particular the causal enumeration of each causal
past, which exists because every observed set is registered
(`ObservedRegistered`) and versions carry causal witnesses
(`CausalCanonical`), the generic bridge `honestAppOn_of_genHonest`. -/
theorem bc_honestAppOn {C : Configuration BC}
    (hObs : ObservedRegistered C) (hCC : CausalCanonical C)
    (hHon : BCHonest C) : HonestAppOn BC bcApplicable C :=
  honestAppOn_of_genHonest hObs hCC ((BCHonest_iff_genHonest C).mp hHon)

open LabeledTS in
/-- **The bound, as a reachability theorem.** In every reachable configuration
whose history is honest, every version (heads, LCAs, everything the store ever
registered) satisfies the escrow invariant. What the CRDT development could
only promise operationally is here a consequence of the formal client
contract. Corollary of the generic safety metatheorem: the counter's
`CausalCanonical` comes pointwise from all-comm + `rc ≡ Either`, and its
`SafetyStepOn`/`HonestAppOn` discharges are §5 and `bc_honestAppOn`. -/
theorem bc_version_inv
    (C : Configuration BC)
    (hReach : (labeledTS3 BC).ReachableFrom (initConfig BC trivial) C)
    (hHon : BCHonest C) :
    ∀ (v : Version) (s : BCState) (E : Set (Op BCOp)),
      C.ver v = some (s, E) → BCInv s := by
  have hGood : GoodConfig3 C := bc_goodConfig3 C hReach
  have hCC : CausalCanonical C :=
    causalCanonical_of_all_comm_rc_either BC_all_comm BC_rc_either hGood
  have hObs : ObservedRegistered C :=
    observedRegistered_of_honest_reach (honestReach_of_reachable hReach)
  exact version_inv_on_of_causal_canonical bc_inv_init bc_safetyStep hGood hCC
    (bc_honestAppOn hObs hCC hHon)

/-- **Corollary: the counter's value is non-negative**, over any finite set of
replicas, at every version of every reachable honest configuration. -/
theorem bc_value_nonneg
    (C : Configuration BC)
    (hReach : (labeledTS3 BC).ReachableFrom (initConfig BC trivial) C)
    (hHon : BCHonest C)
    (v : Version) (s : BCState) (E : Set (Op BCOp))
    (hv : C.ver v = some (s, E))
    (rs : List ℕ) :
    0 ≤ (rs.map (fun r => s.1 r - s.2 r)).sum := by
  have hInv := bc_version_inv C hReach hHon v s E hv
  induction rs with
  | nil => simp
  | cons r rs ih =>
    have := hInv r
    simp only [List.map_cons, List.sum_cons]
    omega

/-! ## §7  The conditioned capstone, identity instantiation of the generic
framework (convergence half of the catalogue entry) -/

section
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.GoodConfig3H
open Sal.ConditionedMRDTs.FlatGeneric

/-- **Bounded counter over the generic framework.** -/
theorem BC_ra_linearizable3_eq
    (C : Configuration (QSig (eqOfEq Sal.ConditionedMRDTs.BC) (WTop Sal.ConditionedMRDTs.BC)
      (invPresTop fun _ => trivial) (congVCEq Sal.ConditionedMRDTs.BC)
      (invInvVCTop Sal.ConditionedMRDTs.BC)))
    (hReach : (labeledTS3 _).ReachableFrom (initConfig _ trivial) C) :
    IsRALinearizable3Eq (eqOfEq Sal.ConditionedMRDTs.BC) (WTop Sal.ConditionedMRDTs.BC)
      (invPresTop fun _ => trivial) (congVCEq Sal.ConditionedMRDTs.BC)
      (invInvVCTop Sal.ConditionedMRDTs.BC) C :=
  flat_ra_linearizable3_eq (fun _ => trivial) (fun _ _ => trivial)
    (contractJoinFull (ConditionedContract.ofVCs Sal.ConditionedMRDTs.BC
      Sal.ConditionedMRDTs.BC_coreVCs3.toCD
      (Sal.ConditionedMRDTs.feasibleDeltaVCs3_of_delta Sal.ConditionedMRDTs.BC_coreVCs3
        Sal.ConditionedMRDTs.BC_deltaVCs3)
      (Sal.ConditionedMRDTs.cdVC3_of_all_comm Sal.ConditionedMRDTs.BC_coreVCs3
        Sal.ConditionedMRDTs.BC_all_comm) trivial)) C hReach

end

/-! ## §8  Cross-check: the escrow metatheorem instance

The counting shape of the `bc_version_inv` proof generalizes to the escrow
metatheorem (`Metatheory/EscrowSafety.lean`), which needs neither a causal
witness nor `Inv`-preservation: the counter is *measured* (its slots are
affine event counts, (B1) below is `bc_fold_incs`/`bc_fold_decs` in structural
form), and the bound re-derives from (B1)–(B5). `bc_version_inv_escrow` is an
independent derivation of `bc_version_inv`'s statement. -/

/-- The counter's observation family: slot `k.2` of the `inc` (resp. `dec`)
tally. -/
def bcObs (k : BCOp × ℕ) (s : BCState) : ℤ :=
  match k.1 with
  | .inc => s.1 k.2
  | .dec => s.2 k.2

/-- Per-op weights: does `e` bump slot `k`? -/
def bcMu (k : BCOp × ℕ) (e : Op BCOp) : ℕ :=
  match k.1 with
  | .inc => if bcIsIncAt k.2 e then 1 else 0
  | .dec => if bcIsDecAt k.2 e then 1 else 0

/-- The bounded counter is measured ((B1): slot updates are affine). -/
noncomputable def BCM : Measured BC (BCOp × ℕ) where
  obs := bcObs
  μ := bcMu
  obs_init := by
    rintro ⟨op, r⟩
    cases op <;> rfl
  obs_update := by
    rintro ⟨op, r⟩ s ⟨ts, ro, eop⟩
    cases op with
    | inc =>
      cases eop with
      | inc =>
        show (bcUpdate s (ts, ro, BCOp.inc)).1 r
          = s.1 r + ↑(if bcIsIncAt r (ts, ro, BCOp.inc) then (1 : ℕ) else 0)
        rw [bcUpdate_inc_fst]
        by_cases h : ro = r
        · subst h
          simp [bcIsIncAt]
        · have h' : ¬ (r = ro) := fun hh => h hh.symm
          simp [bcIsIncAt, h, h']
      | dec =>
        show (bcUpdate s (ts, ro, BCOp.dec)).1 r
          = s.1 r + ↑(if bcIsIncAt r (ts, ro, BCOp.dec) then (1 : ℕ) else 0)
        rw [bcUpdate_dec_fst]
        simp [bcIsIncAt]
    | dec =>
      cases eop with
      | inc =>
        show (bcUpdate s (ts, ro, BCOp.inc)).2 r
          = s.2 r + ↑(if bcIsDecAt r (ts, ro, BCOp.inc) then (1 : ℕ) else 0)
        rw [bcUpdate_inc_snd]
        simp [bcIsDecAt]
      | dec =>
        show (bcUpdate s (ts, ro, BCOp.dec)).2 r
          = s.2 r + ↑(if bcIsDecAt r (ts, ro, BCOp.dec) then (1 : ℕ) else 0)
        rw [bcUpdate_dec_snd]
        by_cases h : ro = r
        · subst h
          simp [bcIsDecAt]
        · have h' : ¬ (r = ro) := fun hh => h hh.symm
          simp [bcIsDecAt, h, h']

/-- A consuming weight of `1` names a `dec` at the class's slot. -/
private theorem bcMu_dec_rep {r : ℕ} {e : Op BCOp}
    (h : bcMu (BCOp.dec, r) e = 1) : bcIsDecAt r e = true := by
  by_cases hd : bcIsDecAt r e = true
  · exact hd
  · exfalso
    have h' : (if bcIsDecAt r e = true then (1 : ℕ) else 0) = 1 := h
    rw [if_neg hd] at h'
    omega

open LabeledTS in
/-- **The bound, re-derived through the escrow metatheorem**
(`escrow_version_inv`): same statement as `bc_version_inv`, no causal witness
and no `bcApplicable_inv_pres`. (B3) is `bcApplicable`'s definition, (B4) is
issuer-determined classes (`class_total_of_same_rep`), (B5) is `BCHonest`
verbatim (the ∀-form is exactly the measured-guard shape). -/
theorem bc_version_inv_escrow
    (C : Configuration BC)
    (hReach : (labeledTS3 BC).ReachableFrom (initConfig BC trivial) C)
    (hHon : BCHonest C) :
    ∀ (v : Version) (s : BCState) (E : Set (Op BCOp)),
      C.ver v = some (s, E) → BCInv s := by
  intro v s E hv r
  exact escrow_version_inv BCM (BCOp.dec, r) (BCOp.inc, r) bcApplicable
    (by
      intro e
      show (if bcIsDecAt r e = true then (1 : ℕ) else 0) ≤ 1
      split <;> omega)
    (by
      rintro ⟨ts, ro, eop⟩ σ hμ happ
      have hd := bcMu_dec_rep hμ
      cases eop with
      | inc => simp [bcIsDecAt] at hd
      | dec =>
        have hro : ro = r := by simpa [bcIsDecAt] using hd
        subst hro
        exact happ)
    (bc_goodConfig3 C hReach)
    (class_total_of_same_rep
      (fun e hμe => bcIsDecAt_rep (bcMu_dec_rep hμe)))
    ((BCHonest_iff_genHonest C).mp hHon) v s E hv

/-! ## Axiom audit -/

#print axioms bc_ra_linearizable3
#print axioms BC_ra_linearizable3_eq
#print axioms bc_version_inv
#print axioms bc_value_nonneg
#print axioms bc_version_inv_escrow

end Sal.ConditionedMRDTs
