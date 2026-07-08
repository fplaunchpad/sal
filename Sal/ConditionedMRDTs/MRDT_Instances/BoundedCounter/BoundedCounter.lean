import Sal.ConditionedMRDTs.Metatheory.Adequacy
import Sal.ConditionedMRDTs.Metatheory.FlatGeneric_Bridge
import Sal.ConditionedMRDTs.Metatheory.HonestReach

/-!
# Bounded Counter — convergence, the client contract, and the bound as a theorem

The second genuinely conditioned MRDT instance (after the tombstone-free RGA).
Mirror of `Sal/CRDTs/Bounded_Counter` (Sypytkowski's state-based bounded
counter, per-replica escrow; transfers omitted in this first instance): state
is a pair of per-replica grow-only tallies `(incs, decs)`, `Inc`/`Dec` bump the
issuing replica's own slot, and the three-way merge is per-slot group merge
`a + b − l` (inclusion–exclusion on event counts).

Three layers:

* **§1–§2 Convergence (flat).** All operations commute (distinct slots, or
  addition on the same slot), so the eight VCs discharge along the PN-Counter's
  route and the instance rides the generic framework at the identity
  instantiation (`BC_ra_linearizable3_eq`).
* **§3 The client contract.** The CRDT file enforces the bound "operationally
  by well-behaved clients". Here that is formal: `BCInv` (per-replica
  `0 ≤ decs r ≤ incs r`), `bcApplicable` (a `Dec` needs slack in the issuing
  replica's own slots — positive and checkable against the issuing replica's
  state), the conditioned signature `BCCond` packaging them, and
  `bcApplicable_inv_pres`: an applicable step preserves the invariant.
* **§4–§6 The bound as a reachability theorem.** `BCHonest C` says every `Dec`
  in the configuration's history was applicable at the fold of its causal past
  — "well-behaved clients", stated on the execution. The headline
  `bc_version_inv`: at every reachable configuration, **every version of every
  honest execution satisfies the invariant**; corollary `bc_value_nonneg`, the
  counter's value (over any finite set of replicas) is non-negative. The proof
  characterizes fold states as per-slot event counts (§4) and bounds the
  decrement count by the increment count using the vis-maximal decrement's
  honesty at its own causal past (§6) — the version's event set is causally
  closed (`GoodConfig3.ver_causal`), so that causal past lies inside the
  version.
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

/-! Component-level reduction lemmas — everything downstream is `omega` on
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
  ra_linearizable_of_core_delta_cd3 BC_coreVCs3 BC_deltaVCs3
    (cdVC3_of_all_comm BC_coreVCs3 BC_all_comm) C hReach

/-! ## §3  The client contract: invariant and applicability -/

/-- Per-replica escrow invariant: every replica's decrement tally is
non-negative and within its own increment tally. The counter's global value is
the sum of the per-replica slacks, hence non-negative (`bc_value_nonneg`). -/
def BCInv (s : BCState) : Prop := ∀ r, 0 ≤ s.2 r ∧ s.2 r ≤ s.1 r

/-- The client check of the CRDT file, made formal: a `Dec` needs slack in the
issuing replica's OWN slots — positive, and checkable against the issuing
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

/-- An applicable step preserves the invariant — the contract is locally
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

/-! ## §5  A vis-maximal element of a finite totally-ordered family -/

/-- Any nonempty duplicate-free list whose elements are pairwise comparable by
a transitive relation `R` has an `R`-maximal element. -/
theorem exists_rel_max {α : Type} (R : α → α → Prop)
    (htrans : ∀ {a b c}, R a b → R b c → R a c) :
    ∀ (l : List α), l ≠ [] → l.Nodup →
      (∀ a ∈ l, ∀ b ∈ l, a ≠ b → R a b ∨ R b a) →
      ∃ e ∈ l, ∀ d ∈ l, d ≠ e → R d e := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons a l ih =>
    intro _ hnd htot
    by_cases hl : l = []
    · subst hl
      refine ⟨a, List.mem_cons_self, ?_⟩
      intro d hd hne
      rcases List.mem_cons.mp hd with rfl | h
      · exact absurd rfl hne
      · exact absurd h List.not_mem_nil
    · have hnd' : l.Nodup := (List.nodup_cons.mp hnd).2
      have hanotin : a ∉ l := (List.nodup_cons.mp hnd).1
      have htot' : ∀ x ∈ l, ∀ y ∈ l, x ≠ y → R x y ∨ R y x := fun x hx y hy =>
        htot x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
      obtain ⟨e, he, hmax⟩ := ih hl hnd' htot'
      have hane : a ≠ e := fun h => hanotin (h ▸ he)
      rcases htot a List.mem_cons_self e (List.mem_cons_of_mem _ he) hane
        with hae | hea
      · refine ⟨e, List.mem_cons_of_mem _ he, ?_⟩
        intro d hd hne
        rcases List.mem_cons.mp hd with rfl | hdl
        · exact hae
        · exact hmax d hdl hne
      · refine ⟨a, List.mem_cons_self, ?_⟩
        intro d hd hne
        rcases List.mem_cons.mp hd with rfl | hdl
        · exact absurd rfl hne
        · by_cases hde : d = e
          · subst hde; exact hea
          · exact htrans (hmax d hdl hde) hea

/-- In a duplicate-free list, a predicate satisfied only by `e` counts at most
once. -/
theorem countP_le_one_of_unique {α : Type} {l : List α} {p : α → Bool} {e : α}
    (hnd : l.Nodup) (h : ∀ x ∈ l, p x = true → x = e) :
    l.countP p ≤ 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hnd' : l.Nodup := (List.nodup_cons.mp hnd).2
    have hanotin : a ∉ l := (List.nodup_cons.mp hnd).1
    rw [List.countP_cons]
    by_cases hpa : p a = true
    · have hae : a = e := h a List.mem_cons_self hpa
      have hzero : l.countP p = 0 := by
        rw [List.countP_eq_zero]
        intro x hx hpx
        have hxe : x = e := h x (List.mem_cons_of_mem _ hx) hpx
        rw [← hae] at hxe
        exact absurd (hxe ▸ hx) hanotin
      simp [hpa, hzero]
    · have hih := ih hnd' (fun x hx hpx => h x (List.mem_cons_of_mem _ hx) hpx)
      have hpa' : p a = false := by
        cases hp : p a
        · rfl
        · exact absurd hp hpa
      simp only [hpa', Bool.false_eq_true, if_false]
      omega

/-- Splitting a count along a second predicate. -/
theorem countP_split {α : Type} (l : List α) (p q : α → Bool) :
    l.countP p
      = l.countP (fun x => p x && q x) + l.countP (fun x => p x && !(q x)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons]
    cases p a <;> cases q a <;> simp <;> omega

/-! ## §6  Honest histories and the bound -/

/-- **The client contract, on the execution**: every decrement in the
configuration's history was applicable at the fold of its causal past — the
issuing replica checked its own slack against what it had seen. (This is the
bounded counter's `HonestDelivery`; the CRDT file's "the bound is enforced
operationally by well-behaved clients", stated formally.) -/
def BCHonest (C : Configuration BC) : Prop :=
  ∀ e ∈ C.events, e.2.2 = BCOp.dec →
    ∀ π : List (Op BCOp),
      listPermOf π {e' ∈ C.events | C.vis e' e} →
      bcApplicable e (applySeq BC.toCRDTSig BC.init π)

open LabeledTS in
/-- The reachability invariant for the bounded counter: the generic
honest-reachability induction (`goodConfig3_of_honest_reach`) under the
trivial contract — the counter's Join is unconditional (the CD route). -/
theorem bc_goodConfig3
    (C : Configuration BC)
    (hReach : (labeledTS3 BC).ReachableFrom (initConfig BC trivial) C) :
    GoodConfig3 C :=
  goodConfig3_of_honest_reach
    (fun _ _ => (join_lemma3_of_cd BC_coreVCs3 BC_deltaVCs3
      (cdVC3_of_all_comm BC_coreVCs3 BC_all_comm)).at _)
    (honestReach_of_reachable hReach)

open LabeledTS in
/-- **The bound, as a reachability theorem.** In every reachable configuration
whose history is honest, every version — heads, LCAs, everything the store
ever registered — satisfies the escrow invariant. What the CRDT development
could only promise operationally is here a consequence of the formal client
contract. -/
theorem bc_version_inv
    (C : Configuration BC)
    (hReach : (labeledTS3 BC).ReachableFrom (initConfig BC trivial) C)
    (hHon : BCHonest C) :
    ∀ (v : Version) (s : BCState) (E : Set (Op BCOp)),
      C.ver v = some (s, E) → BCInv s := by
  classical
  intro v s E hv
  have hGood : GoodConfig3 C := bc_goodConfig3 C hReach
  obtain ⟨π, hperm, _, hfold⟩ := hGood.canonical v s E hv
  intro r
  have hdecs : s.2 r = (π.countP (bcIsDecAt r) : ℤ) := by
    rw [← hfold, bc_fold_decs, BC_init_snd]
    omega
  have hincs : s.1 r = (π.countP (bcIsIncAt r) : ℤ) := by
    rw [← hfold, bc_fold_incs, BC_init_fst]
    omega
  refine ⟨by rw [hdecs]; exact_mod_cast Nat.zero_le _, ?_⟩
  rw [hdecs, hincs]
  suffices h : π.countP (bcIsDecAt r) ≤ π.countP (bcIsIncAt r) by
    exact_mod_cast h
  by_cases hz : π.countP (bcIsDecAt r) = 0
  · omega
  · -- there is a decrement by `r`; take the vis-maximal one
    have hmem_events : ∀ x ∈ π, x ∈ C.events := fun x hx =>
      hGood.ver_events_sub v s E hv x ((hperm.2 x).mp hx)
    have hdecs_ne : π.filter (bcIsDecAt r) ≠ [] := by
      intro h
      apply hz
      rw [List.countP_eq_length_filter, h]
      rfl
    have hdecs_nd : (π.filter (bcIsDecAt r)).Nodup := hperm.1.filter _
    have hdecs_sub : ∀ x ∈ π.filter (bcIsDecAt r), x ∈ π := fun x hx =>
      List.mem_of_mem_filter hx
    have hdec_shape : ∀ x ∈ π.filter (bcIsDecAt r),
        x.2.2 = BCOp.dec ∧ x.2.1 = r := by
      intro x hx
      have hpx : bcIsDecAt r x = true := List.of_mem_filter hx
      obtain ⟨ts, ro, op⟩ := x
      cases op with
      | inc => exact absurd hpx (by simp [bcIsDecAt])
      | dec =>
        refine ⟨rfl, ?_⟩
        simpa [bcIsDecAt] using hpx
    have htot : ∀ a ∈ π.filter (bcIsDecAt r), ∀ b ∈ π.filter (bcIsDecAt r),
        a ≠ b → C.vis a b ∨ C.vis b a := by
      intro a ha b hb hne
      obtain ⟨ra, sa, hLa, hsa⟩ := hmem_events a (hdecs_sub a ha)
      obtain ⟨rb, sb, hLb, hsb⟩ := hmem_events b (hdecs_sub b hb)
      exact C.vis_total_same_replica hLa hsa hLb hsb hne
        (((hdec_shape a ha).2).trans ((hdec_shape b hb).2).symm)
    obtain ⟨e, he_mem, he_max⟩ :=
      exists_rel_max C.vis (fun hab hbc => hGood.vis_trans hab hbc)
        (π.filter (bcIsDecAt r)) hdecs_ne hdecs_nd htot
    obtain ⟨tse, re, ope⟩ := e
    have hope : ope = BCOp.dec := (hdec_shape _ he_mem).1
    subst hope
    set e : Op BCOp := (tse, re, BCOp.dec) with he_def
    have he_π : e ∈ π := hdecs_sub e he_mem
    have he_E : e ∈ E := (hperm.2 e).mp he_π
    have he_events : e ∈ C.events := hmem_events e he_π
    have he_dec : e.2.2 = BCOp.dec := (hdec_shape e he_mem).1
    have he_r : e.2.1 = r := (hdec_shape e he_mem).2
    -- enumeration of `e`'s causal past, inside the (closed) version
    have hπP_perm : listPermOf (π.filter (fun x => decide (C.vis x e)))
        {e' ∈ C.events | C.vis e' e} := by
      constructor
      · exact hperm.1.filter _
      · intro x
        constructor
        · intro hx
          have hxπ : x ∈ π := List.mem_of_mem_filter hx
          have hvis : C.vis x e := by
            have := List.of_mem_filter hx
            simpa using this
          exact ⟨hmem_events x hxπ, hvis⟩
        · rintro ⟨hxev, hvis⟩
          refine List.mem_filter.mpr ⟨?_, by simpa using hvis⟩
          exact (hperm.2 x).mpr (hGood.ver_causal v s E hv x e hvis he_E)
    have happ := hHon e he_events he_dec _ hπP_perm
    -- honesty at the causal past, in counting form
    have hP_counts :
        (π.filter (fun x => decide (C.vis x e))).countP (bcIsDecAt r) + 1
          ≤ (π.filter (fun x => decide (C.vis x e))).countP (bcIsIncAt r) := by
      have h2 : (applySeq BC.toCRDTSig BC.init
            (π.filter (fun x => decide (C.vis x e)))).2 re + 1
          ≤ (applySeq BC.toCRDTSig BC.init
            (π.filter (fun x => decide (C.vis x e)))).1 re := happ
      have hre : re = r := he_r
      rw [bc_fold_decs, bc_fold_incs, BC_init_fst, BC_init_snd, hre] at h2
      omega
    -- every r-decrement of the version is in the past of `e`, or is `e`
    have hsplit : π.countP (bcIsDecAt r)
        = π.countP (fun x => bcIsDecAt r x && decide (C.vis x e))
          + π.countP (fun x => bcIsDecAt r x && !(decide (C.vis x e))) :=
      countP_split π (bcIsDecAt r) (fun x => decide (C.vis x e))
    have hstray :
        π.countP (fun x => bcIsDecAt r x && !(decide (C.vis x e))) ≤ 1 := by
      refine countP_le_one_of_unique (e := e) hperm.1 ?_
      intro x hx hpx
      have hpx' : bcIsDecAt r x = true ∧ !(decide (C.vis x e)) = true := by
        simpa using hpx
      have hxdec : bcIsDecAt r x = true := hpx'.1
      have hxnvis : ¬ C.vis x e := by simpa using hpx'.2
      by_contra hne
      exact hxnvis (he_max x (List.mem_filter.mpr ⟨hx, hxdec⟩) hne)
    have hfiltP : (π.filter (fun x => decide (C.vis x e))).countP (bcIsDecAt r)
        = π.countP (fun x => bcIsDecAt r x && decide (C.vis x e)) := by
      rw [List.countP_filter]
    have hπP_sub : (π.filter (fun x => decide (C.vis x e))).countP (bcIsIncAt r)
        ≤ π.countP (bcIsIncAt r) :=
      List.Sublist.countP_le List.filter_sublist
    omega

/-- **Corollary: the counter's value is non-negative** — over any finite set of
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

/-! ## §7  The conditioned capstone — identity instantiation of the generic
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

/-! ## Axiom audit -/

#print axioms bc_ra_linearizable3
#print axioms BC_ra_linearizable3_eq
#print axioms bc_version_inv
#print axioms bc_value_nonneg

end Sal.ConditionedMRDTs
