import Sal.ConditionedMRDTs.Metatheory.Adequacy
import Sal.ConditionedMRDTs.Metatheory.Arbitration_Refactor
import Sal.ConditionedMRDTs.Metatheory.ArbAdequacy
import Sal.ConditionedMRDTs.Metatheory.ArbAdequacyReach
import Sal.ConditionedMRDTs.Metatheory.FlatGeneric_Bridge
import Sal.ConditionedMRDTs.Metatheory.HonestReach
import Sal.ConditionedMRDTs.Metatheory.GenHonest
import Mathlib.Order.WithBot
import Mathlib.Data.Prod.Lex
import Mathlib.Data.List.MinMax

/-!
# LWW register — last-writer-wins, conditioned and kernel-clean end-to-end

The max twin of `FWWRegister`. A register whose value is the write with the
**largest** timestamp: last writer wins, "last" arbitrated in Lamport time.
The arbitration key lives in the payload (a `(ts, replica, value)` triple);
`update` and `merge` are `max` on that lex order, so the state is a
`max`-semilattice and the entire eight-VC discharge is `max`-algebra.

Two points of contrast worth stating, because they are the whole reason this
instance exists as a *conditioned* datatype rather than a flat CRDT:

* **Genuinely mechanized end-to-end.** The flat CRDT LWW
  (`Sal/CRDTs/LWW_*`) proves its 24 VCs kernel-cleanly, but the generic
  bridge from those VCs to RA-linearizability
  (`Sal/CRDTs/Metatheory/Merge_Linearization.lean`) still carries `sorry`s,
  so flat "LWW is RA-linearizable" rests on the paper meta-theorem. This
  conditioned instance instead rides the framework's *mechanized* bridge
  (`ra_linearizable_of_core_delta_cd3` / the `≈`-quotient capstone), so
  `lww_ra_linearizable3` and `LWW_ra_linearizable3_eq` are genuine
  end-to-end theorems, kernel-clean (axioms ⊆ {propext, Classical.choice,
  Quot.sound}).

* **The purest payload-arbitration register — no discipline at all.** FWW
  carries a (decorative, theorem-free) claim-when-unset discipline. LWW
  carries *none*: a write is always allowed and always overwrites a
  causally-earlier one (timestamps respect causality, so a causally later
  write has a larger ts and wins), while concurrent writes are arbitrated by
  the max-ts payload. So `applicable = ⊤` genuinely, and the winner
  characterization `lww_version_max` is honesty-free: every version holds
  the max-timestamp write of its event set (`⊥` iff the set is empty).

This is the positive complement, on the "last" side, to the metadata-free
kill-test `Refutations/LWW_Merge_Needs_Timestamps.lean`: metadata-free
arbitration is impossible; with-metadata arbitration is a semilattice
triviality.
-/

set_option maxHeartbeats 400000

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

/-! ## §1  The datatype -/

inductive LWWOp : Type where
  | write (v : ℕ)
deriving DecidableEq

/-- A write, ordered lexicographically: timestamp first (the arbitration
key), then replica and value (deterministic tiebreak; distinct events have
distinct timestamps anyway). -/
abbrev LWWWrite : Type := Lex (ℕ × Lex (ℕ × ℕ))

/-- `⊥` = unset; otherwise the current winning (largest-timestamp) write. -/
abbrev LWWState : Type := WithBot LWWWrite

def lwwVal (e : Op LWWOp) : ℕ :=
  match e.2.2 with
  | .write v => v

/-- The write triple an event installs. -/
def lwwWrite (e : Op LWWOp) : LWWWrite :=
  toLex (e.1, toLex (e.2.1, lwwVal e))

def lwwUpdate (s : LWWState) (e : Op LWWOp) : LWWState :=
  max s ↑(lwwWrite e)

/-- Three-way merge, degenerate: the state only ever moves *up* the
semilattice, so the LCA slot is redundant — `max` of the branches. -/
def lwwMergeL (_l a b : LWWState) : LWWState := max a b

noncomputable def LWW : ConditionedMRDTSig where
  State := LWWState
  dec_state := inferInstance
  init := ⊥
  AppOp := LWWOp
  dec_op := inferInstance
  Query := Unit
  Value := LWWState
  update := lwwUpdate
  merge := fun a b => lwwMergeL ⊥ a b
  query := fun s _ => s
  rc := fun _ _ => RcRes.Either
  mergeL := lwwMergeL
  merge_init_slice := fun _ _ => rfl
  Inv := fun _ => True
  applicable := fun _ _ => True

theorem LWW_update_eq (s : LWWState) (e : Op LWWOp) :
    LWW.update s e = max s ↑(lwwWrite e) := rfl

theorem LWW_mergeL_eq (l a b : LWWState) : LWW.mergeL l a b = max a b := rfl

theorem LWW_init_eq : LWW.init = (⊥ : LWWState) := rfl

theorem LWW_rc_either : ∀ o₁ o₂ : Op LWW.AppOp,
    LWW.toCRDTSig.rc o₁ o₂ = RcRes.Either := fun _ _ => rfl

/-! ## §2  The flat discharge (pure `max` algebra) -/

theorem LWW_all_comm : ∀ a b : Op LWW.AppOp, LWW.toCRDTSig.commutes a b := by
  intro a b s
  show lwwUpdate (lwwUpdate s a) b = lwwUpdate (lwwUpdate s b) a
  unfold lwwUpdate
  simp [max_comm, max_assoc, max_left_comm]

theorem LWW_updateVCs : UpdateVCs LWW.toCRDTSig := by
  refine ⟨?_, ?_, ?_⟩
  · intro o₁ o₂ _ _
    constructor
    · intro h
      exact absurd (LWW_all_comm o₁ o₂) h
    · rintro (h | h) <;>
        (rw [LWW_rc_either] at h; exact RcRes.noConfusion h)
  · intro o₁ o₂ o₃ _ _
    rintro ⟨h, _⟩
    rw [LWW_rc_either] at h
    exact RcRes.noConfusion h
  · intro s e e' e'' π _ _ _ h_rc _
    rw [LWW_rc_either] at h_rc
    exact RcRes.noConfusion h_rc

theorem LWW_coreVCs3 : CoreVCs3 LWW := by
  refine ⟨LWW_updateVCs, ?_, ?_, ?_, ?_⟩
  · intro l a b
    show lwwMergeL l a b = lwwMergeL l b a
    unfold lwwMergeL
    exact max_comm (α := LWWState) a b
  · intro s
    show lwwMergeL ⊥ ⊥ s = s
    unfold lwwMergeL
    exact max_eq_right bot_le
  · rintro l a b e
    show lwwMergeL (lwwUpdate l e) (lwwUpdate a e) (lwwUpdate b e)
        = lwwUpdate (lwwMergeL l a b) e
    unfold lwwMergeL lwwUpdate
    simp [max_assoc, max_left_comm]
  · rintro a e π₀ π₂ _ _
    generalize applySeq LWW.toCRDTSig LWW.init π₀ = X
    generalize applySeq LWW.toCRDTSig LWW.init π₂ = Y
    show lwwMergeL X (lwwUpdate a e) Y = lwwUpdate (lwwMergeL X a Y) e
    unfold lwwMergeL lwwUpdate
    simp [max_comm, max_assoc, max_left_comm]

theorem LWW_deltaVCs3 : DeltaVCs3 LWW := by
  constructor
  · intro m x₀ x₁ x₂ c
    show lwwMergeL (lwwMergeL m x₀ c) (lwwMergeL m x₁ c) (lwwMergeL m x₂ c)
        = lwwMergeL m (lwwMergeL x₀ x₁ x₂) c
    unfold lwwMergeL
    simp [max_comm, max_left_comm]
  · intro l m x c y
    show lwwMergeL l (lwwMergeL m x c) y = lwwMergeL m (lwwMergeL l x y) c
    unfold lwwMergeL
    simp [max_comm, max_left_comm]

open LabeledTS in
/-- End-to-end RA-linearizability (convergence) for the LWW register —
through the framework's *mechanized* bridge, not the flat CRDT's
sorry-carrying one. -/
theorem lww_ra_linearizable3
    (C : Configuration LWW)
    (hReach : (labeledTS3 LWW).ReachableFrom (initConfig LWW trivial) C) :
    IsRALinearizable3 C :=
  ra_linearizable3_via_capstone LWW_coreVCs3.toCD LWW_coreVCs3.update_core
    (feasibleDeltaVCs3_of_delta LWW_coreVCs3 LWW_deltaVCs3)
    (cdVC3_of_all_comm LWW_coreVCs3 LWW_all_comm) C hReach

/-! ## §3  The fold is a list maximum; the version characterization -/

/-- Folding from any accumulator computes the maximum of the accumulator and
the writes. -/
theorem lww_fold_acc : ∀ (ρ : List (Op LWWOp)) (acc : LWWState),
    applySeq LWW.toCRDTSig acc ρ = max acc (ρ.map lwwWrite).maximum := by
  intro ρ
  induction ρ with
  | nil =>
    intro acc
    show acc = max acc (List.maximum (List.map lwwWrite []))
    rw [List.map_nil, List.maximum_nil, max_eq_left bot_le]
  | cons e ρ ih =>
    intro acc
    show applySeq LWW.toCRDTSig (lwwUpdate acc e) ρ = _
    rw [ih]
    unfold lwwUpdate
    rw [List.map_cons, List.maximum_cons, max_assoc]

/-- The fold from the initial (unset) register is exactly the maximum write. -/
theorem lww_fold_maximum (ρ : List (Op LWWOp)) :
    applySeq LWW.toCRDTSig LWW.init ρ = (ρ.map lwwWrite).maximum := by
  rw [lww_fold_acc, LWW_init_eq]
  exact max_eq_right (bot_le (α := LWWState))

open LabeledTS in
/-- `GoodConfig3` for the register: the generic honest-reachability induction
under the trivial contract (the Join is unconditional — the CD route). -/
theorem lww_goodConfig3
    (C : Configuration LWW)
    (hReach : (labeledTS3 LWW).ReachableFrom (initConfig LWW trivial) C) :
    GoodConfig3 C :=
  goodConfig3_of_honest_reach
    (fun _ _ => (join_lemma3_of_cd LWW_coreVCs3 LWW_deltaVCs3
      (cdVC3_of_all_comm LWW_coreVCs3 LWW_all_comm)).at _)
    (honestReach_of_reachable hReach)

open LabeledTS in
/-- **The register holds exactly the max-timestamp write of its event set, at
every version of every reachable configuration**: it is an upper bound on all
writes, it is attained by one of them, and it is unset exactly on the empty
set. Deterministic last-writer-wins, with "last" arbitrated in Lamport time
among concurrent writers. No honesty hypothesis — writes are unconditional
and semilattice folds are enumeration-free. -/
theorem lww_version_max
    (C : Configuration LWW)
    (hReach : (labeledTS3 LWW).ReachableFrom (initConfig LWW trivial) C) :
    ∀ (v : Version) (s : LWWState) (E : Set (Op LWWOp)),
      C.ver v = some (s, E) →
      (∀ e ∈ E, ↑(lwwWrite e) ≤ s) ∧
      (s = ⊥ ↔ E = ∅) ∧
      (∀ m : LWWWrite, s = ↑m → ∃ e ∈ E, lwwWrite e = m) := by
  intro v s E hv
  obtain ⟨ρ, hperm, _, hfold⟩ := (lww_goodConfig3 C hReach).canonical v s E hv
  have hs : s = (ρ.map lwwWrite).maximum := by
    rw [← hfold, lww_fold_maximum]
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    rw [hs]
    exact List.le_maximum_of_mem' (List.mem_map_of_mem ((hperm.2 e).mpr he))
  · constructor
    · intro hbot
      rw [hs] at hbot
      have hnil : ρ.map lwwWrite = [] := List.maximum_eq_bot.mp hbot
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
    have hmem : m ∈ ρ.map lwwWrite := List.maximum_mem hm
    obtain ⟨e, he, hce⟩ := List.mem_map.mp hmem
    exact ⟨e, (hperm.2 e).mp he, hce⟩

/-! ## §4  The generic-framework capstone

No `applicable` discipline: LWW writes are unconditional (`applicable = ⊤`).
The register is the purest payload-arbitration instance — arbitration is
entirely in the max-ts payload, nothing is conditioned. -/

section
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.GoodConfig3H
open Sal.ConditionedMRDTs.FlatGeneric

/-- **LWW register over the generic framework** (identity instantiation);
genuine end-to-end RA-linearizability up to `≈` (here `≈ = =`), kernel-clean. -/
theorem LWW_ra_linearizable3_eq
    (C : Configuration (QSig (eqOfEq Sal.ConditionedMRDTs.LWW) (WTop Sal.ConditionedMRDTs.LWW)
      (invPresTop fun _ => trivial) (congVCEq Sal.ConditionedMRDTs.LWW)
      (invInvVCTop Sal.ConditionedMRDTs.LWW)))
    (hReach : (labeledTS3 _).ReachableFrom (initConfig _ trivial) C) :
    IsRALinearizable3Eq (eqOfEq Sal.ConditionedMRDTs.LWW) (WTop Sal.ConditionedMRDTs.LWW)
      (invPresTop fun _ => trivial) (congVCEq Sal.ConditionedMRDTs.LWW)
      (invInvVCTop Sal.ConditionedMRDTs.LWW) C :=
  flat_ra_linearizable3_eq (fun _ => trivial) (fun _ _ => trivial)
    (contractJoinFull (ConditionedContract.ofVCs Sal.ConditionedMRDTs.LWW
      Sal.ConditionedMRDTs.LWW_coreVCs3.toCD
      (Sal.ConditionedMRDTs.feasibleDeltaVCs3_of_delta Sal.ConditionedMRDTs.LWW_coreVCs3
        Sal.ConditionedMRDTs.LWW_deltaVCs3)
      (Sal.ConditionedMRDTs.cdVC3_of_all_comm Sal.ConditionedMRDTs.LWW_coreVCs3
        Sal.ConditionedMRDTs.LWW_all_comm) trivial)) C hReach

end

/-! ## §5  The arbitration refactor: LWW's arbitration is NATIVE, not in `rc`

Task #114 phase 3b (`Metatheory/Arbitration_Refactor.lean`). LWW confirms
`oq:rcchain`: a total-order arbitration policy is inexpressible in the `rc`
mechanism, and LWW does not try — it makes its writes *commute* (`max` is
commutative) and moves the arbitration into the payload fold. Two consequences,
both proved below, together the LWW-native discovery:

* `lww_loOn_empty`: the linearization order `loOn` is **empty** on LWW. Each of
  its arms needs a non-commuting pair (`vis` arm) or an `rc`-resolved concurrent
  pair (`rc` arm), and LWW has neither (`LWW_all_comm`, `rc = Either`). So the
  `rc` mechanism produces the *discrete* arbitration — no order at all.
* `lwwTsArbitration` : the timestamp total order **is** an `AcyclicArbitration`,
  a genuinely non-trivial arbitration `rc` cannot express, and
  `lww_isRALinearizable3Arb_ts` shows LWW is RA-linearizable against it. LWW's
  arbitration lives in `do_`/`mergeL` (the `max` on the lex-timestamp payload),
  not in `loOn`. The abstraction admits it; the published `loOn`-form does not. -/

open Sal.Emulation in
/-- `loOn` is empty on LWW: all writes commute and `rc = Either`, so neither
`loOn` arm can fire. The `rc` mechanism yields the discrete arbitration. -/
theorem lww_loOn_empty (C : Configuration LWW) {E : Set (Op LWWOp)}
    {x y : Op LWWOp} (hx : x ∈ (Configuration.core C).events)
    (hy : y ∈ (Configuration.core C).events) (hne : x ≠ y) :
    ¬ loOn (Configuration.core C) E x y :=
  loOn_empty_of_all_comm_u LWW_updateVCs LWW_all_comm hx hy hne

/-- The timestamp arbitration: order writes by their lex-timestamp payload. This
is the arbitration `rc` cannot express (it is a total order on concurrent
writes). -/
def lwwArb (_E : Set (Op LWWOp)) (a b : Op LWWOp) : Prop := lwwWrite a < lwwWrite b

/-- **The timestamp order is an `AcyclicArbitration`** — for *every* LWW
configuration, with no hypotheses. Acyclicity is strictness of `<` lifted through
`TransGen`; extends-`vis` is vacuous (LWW has no non-commuting pairs). This is the
native arbitration the `rc` mechanism (which gives the empty `loOn`) cannot
supply. -/
def lwwTsArbitration (C : Configuration LWW) : AcyclicArbitration C where
  arb := lwwArb
  extends_vis := by intro _E a b _ha _hb _hv hnc; exact absurd (LWW_all_comm a b) hnc
  acyclic := by
    intro E _hin a hcyc
    have hlt : ∀ p q : Op LWWOp,
        Relation.TransGen (arbNe E lwwArb) p q → lwwWrite p < lwwWrite q := by
      intro p q h
      induction h with
      | single hpq => exact hpq.2.2.2
      | tail _ hpq ih => exact lt_trans ih hpq.2.2.2
    exact absurd (hlt a a hcyc) (lt_irrefl _)

open LabeledTS in
/-- **LWW is RA-linearizable against its native timestamp arbitration.** For every
version, the timestamp-sorted enumeration of its event set respects `lwwArb` and
folds (order-independently, by `lww_fold_maximum`) to the stored max-timestamp
write. So the abstraction `IsRALinearizable3Arb` admits the timestamp total order,
an arbitration strictly finer than the empty `loOn` the `rc` mechanism produces. -/
theorem lww_isRALinearizable3Arb_ts (C : Configuration LWW)
    (hReach : (labeledTS3 LWW).ReachableFrom (initConfig LWW trivial) C) :
    IsRALinearizable3Arb C lwwArb := by
  classical
  intro v s E hv
  obtain ⟨l, hpl, _, hsl⟩ := (lww_goodConfig3 C hReach).canonical v s E hv
  let r : Op LWWOp → Op LWWOp → Prop := fun x y => lwwWrite x ≤ lwwWrite y
  haveI : DecidableRel r := fun a b => inferInstanceAs (Decidable (lwwWrite a ≤ lwwWrite b))
  haveI : IsTrans (Op LWWOp) r := ⟨fun _ _ _ hab hbc => le_trans hab hbc⟩
  haveI : Std.Total r := ⟨fun a b => le_total (lwwWrite a) (lwwWrite b)⟩
  have hperm : List.Perm (List.insertionSort r l) l := List.perm_insertionSort r l
  refine ⟨List.insertionSort r l, ⟨hperm.nodup_iff.mpr hpl.1,
      fun a => hperm.mem_iff.trans (hpl.2 a)⟩, ?_, ?_⟩
  · -- respects lwwArb: the sorted list is `≤`-pairwise, so never `<`-reversed.
    exact (List.pairwise_insertionSort r l).imp (fun hab => not_lt.mpr hab)
  · -- fold: order-independent (`= maximum`), and the maps are perms of `E`.
    rw [lww_fold_maximum, ← hsl, lww_fold_maximum]
    exact List.Perm.maximum_eq (hperm.map lwwWrite)

/-- `loOn` is the empty relation on LWW, for **all** pairs (not just distinct
events): the `vis` arm needs a non-commuting pair (`LWW_all_comm`) and the `rc`
arm needs `rc = Fst_then_snd` (`LWW_rc_either` gives `Either`). Neither fires. -/
theorem lww_loOn_false (C : Configuration LWW) (E : Set (Op LWWOp))
    (a b : Op LWWOp) : ¬ loOn (Configuration.core C) E a b := by
  rintro (⟨_, hnc⟩ | ⟨_, _, hrc, _⟩)
  · exact hnc (LWW_all_comm a b)
  · rw [LWW_rc_either] at hrc; exact RcRes.noConfusion hrc

open LabeledTS in
/-- **LWW's timestamp arbitration, certified via the GENERIC adequacy theorem.**
`lwwArb` refines the empty `loOn` (`lww_loOn_false`, vacuously), and it is an
`AcyclicArbitration` (`lwwTsArbitration`), so
`isRALinearizable3Arb_of_acyclicArb_refines_loOn` applies: LWW is
RA-linearizable against its native timestamp total order through the *same*
generic engine that certifies `loOn` (`loOn_isRALinearizable3Arb_via_generic`).
Compare `lww_isRALinearizable3Arb_ts`, which proved the same conclusion directly
via the `max`-fold; here the fold-uniqueness is delegated to the generic
theorem's reuse of `loOn` convergence. -/
theorem lww_isRALinearizable3Arb_ts_via_generic (C : Configuration LWW)
    (hReach : (labeledTS3 LWW).ReachableFrom (initConfig LWW trivial) C) :
    IsRALinearizable3Arb C lwwArb :=
  isRALinearizable3Arb_of_acyclicArb_refines_loOn LWW_updateVCs
    (lwwTsArbitration C)
    (by intro E a b hlo; exact absurd hlo (lww_loOn_false C E a b))
    (lww_goodConfig3 C hReach)

/-! ## §5  The timestamp arbitration through the FULLY-GENERIC engine

`lww_isRALinearizable3Arb_ts_via_generic` (§4) routes through the loOn-*refining*
partial (`isRALinearizable3Arb_of_acyclicArb_refines_loOn`), which still reuses `loOn`
convergence as the fold oracle. Here `lwwArb` is certified through the *fully*-generic
`ra_linearizable3Arb_of_core_feasible_cd` — the arbitration order **and** the fold
uniqueness are both the abstract timestamp order (`ArbConvergence` from all-commute), with
`loOn` absent from the certificate. -/

/-- `Lex` compares the timestamp component first, so a smaller first component is a
smaller write. -/
theorem lwwWrite_lt_of_fst_lt {a b : Op LWWOp} (h : a.1 < b.1) :
    lwwWrite a < lwwWrite b := by
  unfold lwwWrite
  rw [Prod.Lex.toLex_lt_toLex]
  exact Or.inl h

/-- **`lwwArb` is vis-consistent** — Lamport-monotone, from the configuration's
`causal_mono` field: `vis b a ⟹ b.1 < a.1 ⟹ lwwWrite b < lwwWrite a`, so `a` is never
timestamp-ordered before an event it observed. This is the clause the generic apply pillar
consumes; LWW discharges it through the Lamport clock (no honesty hypothesis). -/
theorem lww_vis_consistent (C : Configuration LWW) :
    VisConsistentArbitration C lwwArb := by
  intro E a b _ha _hb hvis hlt
  have hba : b.1 < a.1 := C.causal_mono hvis
  exact absurd hlt (not_lt.mpr (le_of_lt (lwwWrite_lt_of_fst_lt hba)))

/-- **`lwwArb` is convergent** — all LWW writes commute, so the fold of any enumeration is
the maximum write (`lww_fold_acc`), and two enumerations of the same set are permutations
(`listPermOf_perm`) hence have equal maximum. -/
theorem lww_arbConvergence (C : Configuration LWW) : ArbConvergence C lwwArb := by
  intro E s₀ π₁ π₂ _hin hp₁ hp₂ _hr₁ _hr₂
  rw [lww_fold_acc, lww_fold_acc]
  congr 1
  exact List.Perm.maximum_eq ((listPermOf_perm hp₁ hp₂).map lwwWrite)

/-- **The LWW timestamp family**: `lwwArb` (config- and set-independent) discharges all
six `ArbFamily` clauses — acyclicity via `lwwTsArbitration`, extends-`vis` vacuously
(`LWW_all_comm`), antitone/vis-local trivially (set-independent), vis-consistency via the
Lamport clock, convergence via the `max` fold. -/
def lwwFamily : ArbFamily LWW where
  arb := fun _C => lwwArb
  extends_vis := by intro C E a b _ha _hb _hv hnc; exact absurd (LWW_all_comm a b) hnc
  acyclic := by intro C _h_tr _h_ir E h_in a; exact (lwwTsArbitration C).acyclic E h_in a
  antitone := by intro C E' E'' a b _hsub h; exact h
  vis_consistent := by intro C _h_tr _h_ir; exact lww_vis_consistent C
  convergent := by intro C; exact lww_arbConvergence C
  vis_local := by intro C C' E _hva a _ha b _hb; exact Iff.rfl

open LabeledTS in
/-- **LWW's timestamp arbitration through the FULLY-GENERIC capstone.** Every reachable
configuration is RA-linearizable against the abstract timestamp total order `lwwArb` via
`ra_linearizable3Arb_of_core_feasible_cd`, the fold pinned by `lwwArb`'s own
`ArbConvergence` (all-commute) rather than by `loOn`. The arb-form VCs come from the
all-commuting converters (`cdvc3Arb_of_all_comm`, `feasibleDeltaVCs3Arb_of_delta`). -/
theorem lww_isRALinearizable3Arb_ts_via_capstone (C : Configuration LWW)
    (hReach : (labeledTS3 LWW).ReachableFrom (initConfig LWW trivial) C) :
    IsRALinearizable3Arb C lwwArb :=
  ra_linearizable3Arb_of_core_feasible_cd lwwFamily LWW_coreVCs3.toCD.mergeL_comm
    (fun C' => cdvc3Arb_of_all_comm LWW_coreVCs3 LWW_all_comm C' lwwArb)
    (fun C' => feasibleDeltaVCs3Arb_of_delta LWW_coreVCs3 LWW_deltaVCs3 C' lwwArb)
    C hReach

#print axioms lww_ra_linearizable3
#print axioms lww_version_max
#print axioms LWW_ra_linearizable3_eq
#print axioms lww_loOn_empty
#print axioms lwwTsArbitration
#print axioms lww_isRALinearizable3Arb_ts
#print axioms lww_isRALinearizable3Arb_ts_via_generic
#print axioms lww_isRALinearizable3Arb_ts_via_capstone

end Sal.ConditionedMRDTs
