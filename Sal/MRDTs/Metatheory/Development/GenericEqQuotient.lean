import Sal.MRDTs.Metatheory.Development.ConditionedContract

/-!
# The generic `≈`-quotient functor and the conditioned metatheorem up to `≈`

`Development/GENERIC_FRAMEWORK_DESIGN.md`, steps 1–3. Everything here is
generic over an abstract `D : ConditionedMRDTSig` — no datatype specifics.

* **§1** the VC bundle a datatype supplies for the `≈`-route: `EqEquiv D`
  (the observational relation with its equivalence proof), `InvPres D`
  (`Inv` holds initially, is preserved by `update` **on `applicable` ops**,
  and by `mergeL` — the datatype's `inv_step`, which `ConditionedMRDTSig`
  does not carry as a field; the `applicable`-conditioning on `update` is
  forced — `update` breaks `Inv` on non-`applicable` ops, so the quotient's
  `update` is the guarded `apply-when-applicable` step `qdo`/`doApp`),
  `CongVC D E` (`update`/`mergeL`/`query` respect `≈` **on
  `Inv`-states** — conditioned, per `merge_eq_congr_l_fails`), and
  `InvInvVC D E` (`applicable` is `≈`-invariant on `Inv`-states; `Inv`
  itself needs no invariance VC — the subtype quotient carries it).
* **§2** the functor `D ↦ D≈`: `QState` is the quotient of the
  `Inv`-subtype `{s // D.Inv s}` by `≈` (the subtype — not the plain —
  quotient, so `CongVC`'s `Inv` hypotheses are in scope at every lift),
  with `qdo`/`qmergeL`/`qquery`/`qapplicable` lifted and the signature
  `QSig` assembled (`Inv := True` upstairs: every class already carries a
  proof of `Inv` downstairs).
* **§3** the transfer: `=` on `QState` *is* `≈` downstairs, so the
  datatype's `≈`-Join (`EqJoinLemma3C`, stated over `D`'s own
  configurations with the `≈`-conditioned linearization order `loOnEq`)
  becomes the literal `JoinLemma3C (QSig …)` — `joinC_quotient`.
* **§4** the metatheorem `RA_linearizable_up_to_eq`:
  `ra_linearizable3_of_joinC (QSig …) ∘ joinC_quotient`, plus the explicit
  readback `RA_linearizable_up_to_eq_readback` — every version state of a
  reachable `QSig`-configuration is `≈` to a fold of an `lo`-respecting
  enumeration of its event set. RA-linearizability up to `≈`.
* **§5** the `app`-conditioning audit (documentation, end of file).
-/

namespace Sal.Metatheory
namespace GenericEqQuotient

open Sal.Emulation
open Classical

variable {D : ConditionedMRDTSig}

/-! ## §1. The VC bundle -/

/-- **`EqEquiv D`** — the observational relation `≈` the datatype supplies,
with its equivalence proof (RGA: `eq` + `eq_equiv`; flat MRDTs: `Eq`). -/
structure EqEquiv (D : ConditionedMRDTSig) where
  /-- The observational relation `≈` on states. -/
  eqv : D.State → D.State → Prop
  /-- `≈` is an equivalence. -/
  equiv : Equivalence eqv

/-- **`InvPres D`** — `Inv` holds at `init`, is preserved by `update` **on
`applicable` ops**, and is preserved by `mergeL`. This is the datatype's
`inv_step`; `ConditionedMRDTSig` does not carry it as a field, so it is an
explicit VC here. It is what lets the `Inv`-subtype quotient receive the lifted
operations.

`inv_update` is `applicable`-CONDITIONED — the honest form for a state-dependent
MRDT. A `ConditionedMRDTSig`'s `update` need not preserve `Inv` on a
NON-`applicable` op (the RGA's `do_` breaks root-freeness on an inaccurate/stale
`Ins`), so demanding unconditional preservation would make `InvPres`
UNSATISFIABLE by the very datatypes this framework exists to host. The quotient's
lifted `update` (`qdo`) therefore applies `D.update` only when `applicable` and
is the identity otherwise (`doApp`) — a non-`applicable` event is recorded in the
event set but has no effect on state. `inv_mergeL` stays unconditional: the
hosting datatype is expected to pick an `Inv` strong enough to close it (the RGA
uses `qInv = wf ∧ root-free ∧ id_mono`, whose `id_mono` discharges `Inv_merge`;
`RGA_VCPackage.rga_inv_mergeL_of_idmono`). -/
structure InvPres (D : ConditionedMRDTSig) : Prop where
  inv_init : D.Inv D.init
  inv_update : ∀ (s : D.State) (o : Op D.AppOp),
    D.Inv s → D.applicable o s → D.Inv (D.update s o)
  inv_mergeL : ∀ l a b : D.State,
    D.Inv l → D.Inv a → D.Inv b → D.Inv (D.mergeL l a b)

/-- **`CongVC D E`** — the congruence VC: `update`, `mergeL` and `query`
respect `≈` **on `Inv`-states**. The conditioning on `Inv` is forced: the
full-type `mergeL` congruence is FALSE for the RGA
(`RGA_EqQuotient.merge_eq_congr_l_fails`); it holds only on the reachable
subfamily, which `Inv` over-approximates. `query_congr` is not consumed by
the metatheorem — it only carries the `query` field through the quotient
(and is the literal reading of "`≈` is observational equivalence"). -/
structure CongVC (D : ConditionedMRDTSig) (E : EqEquiv D) : Prop where
  update_congr : ∀ (o : Op D.AppOp) {s s' : D.State},
    D.Inv s → D.Inv s' → E.eqv s s' → E.eqv (D.update s o) (D.update s' o)
  mergeL_congr : ∀ {l l' a a' b b' : D.State},
    D.Inv l → D.Inv l' → D.Inv a → D.Inv a' → D.Inv b → D.Inv b' →
    E.eqv l l' → E.eqv a a' → E.eqv b b' →
    E.eqv (D.mergeL l a b) (D.mergeL l' a' b')
  query_congr : ∀ (q : D.Query) {s s' : D.State},
    D.Inv s → D.Inv s' → E.eqv s s' → D.query s q = D.query s' q

/-- **`InvInvVC D E`** — `applicable` is `≈`-invariant on `Inv`-states, so it
descends to the quotient (RGA: `accurate_eq_iff ∧ fresh_ts_eq_iff`). `Inv`
itself needs NO invariance VC: the quotient is taken over the `Inv`-subtype,
so every class carries `Inv` by construction and the lifted `Inv` is `True`. -/
structure InvInvVC (D : ConditionedMRDTSig) (E : EqEquiv D) : Prop where
  applicable_congr : ∀ (o : Op D.AppOp) {s s' : D.State},
    D.Inv s → D.Inv s' → E.eqv s s' → (D.applicable o s ↔ D.applicable o s')

/-! ## §2. The functor `D ↦ D≈` (the `Inv`-subtype quotient) -/

/-- The `Inv`-subtype: the carrier of the quotient. Carrying `Inv` in the
carrier is what puts `CongVC`'s `Inv` hypotheses in scope at every
`Quotient.lift` (the reachable-subfamily refinement). -/
abbrev InvState (D : ConditionedMRDTSig) : Type := { s : D.State // D.Inv s }

/-- The setoid on the `Inv`-subtype induced by `≈`. -/
def EqEquiv.setoid (E : EqEquiv D) : Setoid (InvState D) :=
  ⟨fun a b => E.eqv a.1 b.1,
    ⟨fun a => E.equiv.refl a.1,
     fun h => E.equiv.symm h,
     fun h₁ h₂ => E.equiv.trans h₁ h₂⟩⟩

/-- The quotient state type of `D≈`. -/
def QState (D : ConditionedMRDTSig) (E : EqEquiv D) : Type :=
  Quotient E.setoid

/-- Class of an `Inv`-state. -/
def qmk (E : EqEquiv D) (s : D.State) (hs : D.Inv s) : QState D E :=
  Quotient.mk E.setoid ⟨s, hs⟩

/-- `=` upstairs is `≈` downstairs — the whole point of the quotient. -/
theorem qmk_eq_iff (E : EqEquiv D) {s s' : D.State}
    {hs : D.Inv s} {hs' : D.Inv s'} :
    qmk E s hs = qmk E s' hs' ↔ E.eqv s s' :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-! ### The `apply-when-applicable` guarded step

`ConditionedMRDTSig.update` need not preserve `Inv` on a NON-`applicable` op, and
the execution model (`Step3.apply`, `LCA_Lemma.lean`) applies events with NO
`applicable` guard. So the quotient's `update` cannot lift `D.update` blindly: it
applies `D.update` only when the op is `applicable`, and is the identity
otherwise (`doApp`). A NON-`applicable` event is thereby recorded in the event
set but has no effect on state — the honest semantics of a conditioned MRDT — and
this is what makes the `applicable`-conditioned `InvPres.inv_update` sufficient to
keep the quotient inside the `Inv`-subtype. -/

/-- One guarded step: apply `o` when `applicable`, else keep the state. -/
noncomputable def doApp (D : ConditionedMRDTSig) (o : Op D.AppOp) (s : D.State) :
    D.State :=
  if D.applicable o s then D.update s o else s

/-- `doApp` preserves `Inv` UNCONDITIONALLY in `o`: the applicable branch is the
`applicable`-conditioned `inv_update`; the identity branch keeps `Inv`. -/
theorem InvPres.inv_doApp (hP : InvPres D) (o : Op D.AppOp) (s : D.State)
    (hs : D.Inv s) : D.Inv (doApp D o s) := by
  unfold doApp
  by_cases h : D.applicable o s
  · rw [if_pos h]; exact hP.inv_update s o hs h
  · rw [if_neg h]; exact hs

/-- The guarded step respects `≈` on `Inv`-states: `applicable` agrees across `≈`
(`InvInvVC`), and each branch is congruent (`update_congr` / reflexivity). This is
what makes `qdo` well-defined on the quotient. -/
theorem doApp_congr (E : EqEquiv D) (hC : CongVC D E) (hA : InvInvVC D E)
    (o : Op D.AppOp) {s s' : D.State} (hs : D.Inv s) (hs' : D.Inv s')
    (h : E.eqv s s') : E.eqv (doApp D o s) (doApp D o s') := by
  unfold doApp
  by_cases hp : D.applicable o s
  · have hp' : D.applicable o s' := (hA.applicable_congr o hs hs' h).mp hp
    rw [if_pos hp, if_pos hp']
    exact hC.update_congr o hs hs' h
  · have hp' : ¬ D.applicable o s' :=
      fun c => hp ((hA.applicable_congr o hs hs' h).mpr c)
    rw [if_neg hp, if_neg hp']
    exact h

/-- Guarded fold: `applySeq` with each step guarded by `applicable`. This is what
the quotient's `update`-fold computes downstairs (`qapplySeq`), and the state the
`≈`-route's canonical states / readback are stated against. -/
noncomputable def applySeqApp (D : ConditionedMRDTSig) (s : D.State)
    (ρ : List (Op D.AppOp)) : D.State :=
  ρ.foldl (fun s o => doApp D o s) s

/-- `Inv` is preserved by a guarded fold, UNCONDITIONALLY in `ρ` (each step is
`inv_doApp`). -/
theorem InvPres.applySeqApp (hP : InvPres D) (ρ : List (Op D.AppOp))
    (s : D.State) (hs : D.Inv s) : D.Inv (applySeqApp D s ρ) := by
  induction ρ generalizing s with
  | nil => exact hs
  | cons o ρ ih => exact ih (doApp D o s) (hP.inv_doApp o s hs)

section Functor
variable (E : EqEquiv D) (hP : InvPres D) (hC : CongVC D E) (hA : InvInvVC D E)

/-- `update` lifted to the quotient — the `apply-when-applicable` guarded step
(`doApp`) lifted. Well-defined by `doApp_congr` (whose `Inv` hypotheses are
supplied by the subtype); it lands in the subtype by `InvPres.inv_doApp`, which
needs only the `applicable`-conditioned `inv_update` (the non-`applicable` branch
is the identity, keeping `Inv` for free). `noncomputable` via `doApp`'s classical
`applicable`-guard. -/
noncomputable def qdo (q : QState D E) (o : Op D.AppOp) : QState D E :=
  Quotient.lift
    (fun sp : InvState D => qmk E (doApp D o sp.1) (hP.inv_doApp o sp.1 sp.2))
    (fun sp sp' h => Quotient.sound (doApp_congr E hC hA o sp.2 sp'.2 h)) q

@[simp] theorem qdo_qmk (o : Op D.AppOp) (s : D.State) (hs : D.Inv s) :
    qdo E hP hC hA (qmk E s hs) o
      = qmk E (doApp D o s) (hP.inv_doApp o s hs) := rfl

/-- Ternary `mergeL` lifted to the quotient: `Quotient.liftOn₂` in `(l, a)`
nested with a `Quotient.liftOn` in `b`, each leg discharged by
`CongVC.mergeL_congr` (with `≈`-reflexivity filling the fixed slots) and
landed in the subtype by `InvPres.inv_mergeL`. -/
def qmergeL (l a b : QState D E) : QState D E :=
  Quotient.liftOn₂ l a
    (fun lp ap =>
      Quotient.liftOn b
        (fun bp => qmk E (D.mergeL lp.1 ap.1 bp.1)
          (hP.inv_mergeL lp.1 ap.1 bp.1 lp.2 ap.2 bp.2))
        (fun bp bp' hb => Quotient.sound
          (hC.mergeL_congr lp.2 lp.2 ap.2 ap.2 bp.2 bp'.2
            (E.equiv.refl lp.1) (E.equiv.refl ap.1) hb)))
    (fun lp ap lp' ap' hl ha =>
      Quotient.inductionOn b (fun bp => Quotient.sound
        (hC.mergeL_congr lp.2 lp'.2 ap.2 ap'.2 bp.2 bp.2
          hl ha (E.equiv.refl bp.1))))

@[simp] theorem qmergeL_qmk {l a b : D.State}
    (hl : D.Inv l) (ha : D.Inv a) (hb : D.Inv b) :
    qmergeL E hP hC (qmk E l hl) (qmk E a ha) (qmk E b hb)
      = qmk E (D.mergeL l a b) (hP.inv_mergeL l a b hl ha hb) := rfl

/-- `query` lifted to the quotient (via `CongVC.query_congr`). -/
def qquery (q : QState D E) (qu : D.Query) : D.Value :=
  Quotient.lift (fun sp : InvState D => D.query sp.1 qu)
    (fun sp sp' h => hC.query_congr qu sp.2 sp'.2 h) q

/-- `applicable` lifted to the quotient (via `InvInvVC.applicable_congr`). -/
def qapplicable (o : Op D.AppOp) (q : QState D E) : Prop :=
  Quotient.lift (fun sp : InvState D => D.applicable o sp.1)
    (fun sp sp' h => propext (hA.applicable_congr o sp.2 sp'.2 h)) q

/-- **The functor `D ↦ D≈`.** State is the `Inv`-subtype quotient; the
operations are the lifts above; `AppOp`/`Query`/`Value`/`rc` are unchanged;
the binary `merge` is pinned to the `init`-LCA slice of `qmergeL`
(`merge_init_slice` is `rfl`); `Inv` is `True` (every class carries `Inv`
downstairs by construction) and `applicable` is the lift. `noncomputable`
only for the classical `DecidableEq` on the quotient. -/
noncomputable def QSig : ConditionedMRDTSig where
  State := QState D E
  dec_state := fun _ _ => Classical.propDecidable _
  init := qmk E D.init hP.inv_init
  AppOp := D.AppOp
  dec_op := D.dec_op
  Query := D.Query
  Value := D.Value
  update := fun q o => qdo E hP hC hA q o
  merge := fun a b => qmergeL E hP hC (qmk E D.init hP.inv_init) a b
  query := fun q qu => qquery E hC q qu
  rc := D.rc
  mergeL := fun l a b => qmergeL E hP hC l a b
  merge_init_slice := fun _ _ => rfl
  Inv := fun _ => True
  applicable := fun o q => qapplicable E hA o q

/-- `applySeq` commutes with the quotient: folding the lifted (guarded) `update`
over a class is the class of the guarded fold `applySeqApp`. The guard `doApp` is
baked into BOTH sides — `qdo` upstairs, `doApp` downstairs — so this holds
UNCONDITIONALLY in `ρ` (no applicability hypothesis on the enumeration is needed,
which is exactly what the unguarded execution model cannot provide). -/
theorem qapplySeq (ρ : List (Op D.AppOp)) (s : D.State) (hs : D.Inv s) :
    Sal.Emulation.applySeq (QSig E hP hC hA).toCRDTSig (qmk E s hs) ρ
      = qmk E (applySeqApp D s ρ) (hP.applySeqApp ρ s hs) := by
  induction ρ generalizing s with
  | nil => rfl
  | cons o ρ ih => exact ih (doApp D o s) (hP.inv_doApp o s hs)

/-- `qapplySeq` at the initial state, keyed on `(QSig …).init` so it rewrites
the `IsCanonicalState`/`IsRALinearizable3` folds syntactically. -/
theorem qapplySeq_init (ρ : List (Op D.AppOp)) :
    Sal.Emulation.applySeq (QSig E hP hC hA).toCRDTSig
        (QSig E hP hC hA).init ρ
      = qmk E (applySeqApp D D.init ρ)
          (hP.applySeqApp ρ D.init hP.inv_init) :=
  qapplySeq E hP hC hA ρ D.init hP.inv_init

end Functor

/-! ## §3. Downstairs readings of the quotient's `commutes`/`loOn`, and the
configuration transport -/

/-- **`≈`-commutation on `Inv`-states** — exactly what `(QSig …).commutes`
means downstairs. The steps are the GUARDED steps (`doApp`), because the
quotient's `update` is `qdo` (`apply-when-applicable`): on `applicable` ops at
`applicable` states `doApp = update`, so this is real commutation there, and a
non-`applicable` op commutes with everything as a no-op. Conditioned on `Inv`
only, NOT on `applicable` — quotient states carry no applicability, so this (and
not `commutesOn`) is the commutation notion the `≈`-route's Join is proved
against. -/
def eqCommutesOn (E : EqEquiv D) (o₁ o₂ : Op D.AppOp) : Prop :=
  ∀ s : D.State, D.Inv s →
    E.eqv (doApp D o₂ (doApp D o₁ s)) (doApp D o₁ (doApp D o₂ s))

section Transfer
variable (E : EqEquiv D) (hP : InvPres D) (hC : CongVC D E) (hA : InvInvVC D E)

/-- The quotient's structural `commutes` IS `≈`-commutation-on-`Inv`. -/
theorem qcommutes_iff (o₁ o₂ : Op D.AppOp) :
    (QSig E hP hC hA).toCRDTSig.commutes o₁ o₂ ↔ eqCommutesOn E o₁ o₂ := by
  constructor
  · intro h s hs
    exact Quotient.exact (h (qmk E s hs))
  · intro h q
    exact Quotient.inductionOn q
      (fun sp => Quotient.sound (h sp.1 sp.2))

/-- `Sal.Emulation.loOn` with an abstract `vis` graph and `commutes` replaced
by `≈`-commutation-on-`Inv`: the linearization order the datatype's `≈`-Join
enumerations must respect. Reads only `vis` and `D.rc`. -/
def loOnEq (E : EqEquiv D) (vis : Op D.AppOp → Op D.AppOp → Prop)
    (ev : Set (Op D.AppOp)) (e₁ e₂ : Op D.AppOp) : Prop :=
  (vis e₁ e₂ ∧ ¬ eqCommutesOn E e₁ e₂)
  ∨ ( ¬ vis e₁ e₂ ∧ ¬ vis e₂ e₁
      ∧ D.rc e₁ e₂ = RcRes.Fst_then_snd
      ∧ ¬ ∃ e₃ ∈ ev, vis e₂ e₃ ∧ ¬ eqCommutesOn E e₂ e₃ )

/-- Global (`ev`-unrestricted) variant, mirroring `Sal.Emulation.lo`. -/
def loEq (E : EqEquiv D) (vis : Op D.AppOp → Op D.AppOp → Prop)
    (e₁ e₂ : Op D.AppOp) : Prop :=
  (vis e₁ e₂ ∧ ¬ eqCommutesOn E e₁ e₂)
  ∨ ( ¬ vis e₁ e₂ ∧ ¬ vis e₂ e₁
      ∧ D.rc e₁ e₂ = RcRes.Fst_then_snd
      ∧ ¬ ∃ e₃, vis e₂ e₃ ∧ ¬ eqCommutesOn E e₂ e₃ )

/-- `loOn` of a `QSig`-configuration reads back as `loOnEq` over its `vis`. -/
theorem loOn_qsig_iff
    (Cq : Sal.Emulation.Configuration (QSig E hP hC hA).toCRDTSig)
    (ev : Set (Op D.AppOp)) (e₁ e₂ : Op D.AppOp) :
    Sal.Emulation.loOn Cq ev e₁ e₂ ↔ loOnEq E Cq.vis ev e₁ e₂ := by
  unfold Sal.Emulation.loOn loOnEq
  simp only [qcommutes_iff E hP hC hA]
  exact Iff.rfl

/-- `lo` of a `QSig`-configuration reads back as `loEq` over its `vis`. -/
theorem lo_qsig_iff
    (Cq : Sal.Emulation.Configuration (QSig E hP hC hA).toCRDTSig)
    (e₁ e₂ : Op D.AppOp) :
    Sal.Emulation.lo Cq e₁ e₂ ↔ loEq E Cq.vis e₁ e₂ := by
  unfold Sal.Emulation.lo loEq
  simp only [qcommutes_iff E hP hC hA]
  exact Iff.rfl

end Transfer

/-- `respects` transports across pointwise-equivalent relations. -/
theorem respects_congr {α : Type} {π : List α} {R S : α → α → Prop}
    (h : ∀ a b, R a b ↔ S a b) : respects π R ↔ respects π S := by
  unfold respects
  constructor
  · exact fun hp => hp.imp (fun hn hs => hn ((h _ _).mpr hs))
  · exact fun hp => hp.imp (fun hn hr => hn ((h _ _).mp hr))

/-! ## §4. The datatype's `≈`-Join, the transfer, and the metatheorem -/

/-- Full causal closure as a bare relation on `vis` (what `fullClosure`
unfolds to; keeps the datatype's `≈`-Join free of `Configuration`). -/
def fullClosureRel (vis : Op D.AppOp → Op D.AppOp → Prop)
    (ev : Set (Op D.AppOp)) : Prop :=
  ∀ a b, vis a b → b ∈ ev → a ∈ ev

/-- **Canonical state up to `≈`**: some `loOnEq`-respecting enumeration of `ev`,
folded `apply-when-applicable` from `D.init` (`applySeqApp`), lands `≈`-equal to
`s`. This is `IsCanonicalState` with `=` relaxed to `≈`, `loOn`'s `commutes`
replaced by `≈`-commutation-on-`Inv` (`loOnEq`), and the fold guarded by
`applicable` (`applySeqApp`) — exactly what the quotient's `IsCanonicalState`
becomes, since the quotient's `update` is the guarded step (`qdo`/`doApp`). -/
def IsCanonicalStateEq (E : EqEquiv D)
    (vis : Op D.AppOp → Op D.AppOp → Prop)
    (ev : Set (Op D.AppOp)) (s : D.State) : Prop :=
  ∃ ρ : List (Op D.AppOp),
    listPermOf ρ ev ∧ respects ρ (loOnEq E vis ev) ∧
    E.eqv (applySeqApp D D.init ρ) s

/-- **The datatype's `≈`-Join Lemma** (`EqJoinLemma3C`), the sole
convergence VC of the `≈`-route. `JoinLemma3F`/`JoinLemma3C … fullClosure`
with `=` relaxed to `≈`, over an abstract `vis`/`events`, with the sides
required `Inv` (the reachable subfamily the RGA's `≈`-Join lives on).
Fully closed sides so the quotient's `𝒞 := fullClosure` matches. -/
def EqJoinLemma3C (D : ConditionedMRDTSig) (E : EqEquiv D) : Prop :=
  ∀ (vis : Op D.AppOp → Op D.AppOp → Prop) (events : Set (Op D.AppOp))
    (ev₁ ev₂ : Set (Op D.AppOp)) (s₀ s₁ s₂ : D.State),
    D.Inv s₀ → D.Inv s₁ → D.Inv s₂ →
    (∀ {a b c : Op D.AppOp}, vis a b → vis b c → vis a c) →
    (∀ a : Op D.AppOp, ¬ vis a a) →
    (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
    fullClosureRel vis ev₁ → fullClosureRel vis ev₂ →
    IsCanonicalStateEq E vis (ev₁ ∩ ev₂) s₀ →
    IsCanonicalStateEq E vis ev₁ s₁ → IsCanonicalStateEq E vis ev₂ s₂ →
    IsCanonicalStateEq E vis (ev₁ ∪ ev₂) (D.mergeL s₀ s₁ s₂)

section Transfer2
variable (E : EqEquiv D) (hP : InvPres D) (hC : CongVC D E) (hA : InvInvVC D E)

/-- The bridge: `IsCanonicalState` of a `QSig`-configuration at a class
`qmk E s hs` IS the datatype's `IsCanonicalStateEq` at the representative —
the quotient makes `=` into `≈` (`qmk_eq_iff`) and `loOn` into `loOnEq`
(`loOn_qsig_iff`), and the fold commutes with `qmk` (`qapplySeq_init`). -/
theorem isCanonicalState_qsig_iff
    (Cq : Sal.Emulation.Configuration (QSig E hP hC hA).toCRDTSig)
    (ev : Set (Op D.AppOp)) (s : D.State) (hs : D.Inv s) :
    Sal.Emulation.IsCanonicalState Cq ev (qmk E s hs)
      ↔ IsCanonicalStateEq E Cq.vis ev s := by
  unfold Sal.Emulation.IsCanonicalState IsCanonicalStateEq
  constructor
  · rintro ⟨ρ, hperm, hresp, hfold⟩
    refine ⟨ρ, hperm, (respects_congr (loOn_qsig_iff E hP hC hA Cq ev)).mp hresp, ?_⟩
    rw [qapplySeq_init E hP hC hA ρ] at hfold
    exact (qmk_eq_iff E).mp hfold
  · rintro ⟨ρ, hperm, hresp, hfold⟩
    refine ⟨ρ, hperm, (respects_congr (loOn_qsig_iff E hP hC hA Cq ev)).mpr hresp, ?_⟩
    rw [qapplySeq_init E hP hC hA ρ]
    exact (qmk_eq_iff E).mpr hfold

end Transfer2

/-- **`joinC_quotient`** — the transfer theorem. The datatype's `≈`-Join
(`EqJoinLemma3C`) yields the structural `JoinLemma3C` of the quotient
signature at `𝒞 := fullClosure` (over Lean `=` on `QState`). Pure quotient
bookkeeping: induct the three canonical states to representatives, rewrite
each `IsCanonicalState` through `isCanonicalState_qsig_iff`, apply the
`≈`-Join, and rewrite the `qmergeL` conclusion back. NO datatype specifics. -/
theorem joinC_quotient
    (E : EqEquiv D) (hP : InvPres D) (hC : CongVC D E) (hA : InvInvVC D E)
    (hJoinEq : EqJoinLemma3C D E) :
    JoinLemma3C (QSig E hP hC hA) (fullClosure (QSig E hP hC hA).toCRDTSig) := by
  intro Cq ev₁ ev₂ s₀ s₁ s₂ htr hir hin₁ hin₂ hcl₁ hcl₂ hc₀ hc₁ hc₂
  revert hc₀ hc₁ hc₂
  refine Quotient.inductionOn₃ s₀ s₁ s₂ ?_
  rintro ⟨l, hl⟩ ⟨a, ha⟩ ⟨b, hb⟩ hc₀ hc₁ hc₂
  have g₀ := (isCanonicalState_qsig_iff E hP hC hA Cq (ev₁ ∩ ev₂) l hl).mp hc₀
  have g₁ := (isCanonicalState_qsig_iff E hP hC hA Cq ev₁ a ha).mp hc₁
  have g₂ := (isCanonicalState_qsig_iff E hP hC hA Cq ev₂ b hb).mp hc₂
  have gm := hJoinEq Cq.vis Cq.events ev₁ ev₂ l a b hl ha hb
    htr hir hin₁ hin₂ hcl₁ hcl₂ g₀ g₁ g₂
  exact (isCanonicalState_qsig_iff E hP hC hA Cq (ev₁ ∪ ev₂)
    (D.mergeL l a b) (hP.inv_mergeL l a b hl ha hb)).mpr gm

/-- **`RA_linearizable_up_to_eq`** — THE generic conditioned metatheorem.
A `ConditionedMRDTSig` `D` supplying the `≈`-route VCs — `EqEquiv` (the
observational relation), `InvPres` (`Inv` preserved by `init`/`update`/
`mergeL`), `CongVC` (`update`/`mergeL` `≈`-congruent on `Inv`), `InvInvVC`
(`applicable` `≈`-invariant), and `EqJoinLemma3C` (the `≈`-Join) — makes
its quotient signature `QSig` per-version RA-linearizable on every
reachable configuration. `ra_linearizable3_of_joinC (QSig …)` at
`𝒞 := fullClosure` composed with `joinC_quotient`. Hypotheses are EXACTLY
the datatype's VCs; nothing else. -/
theorem RA_linearizable_up_to_eq
    (E : EqEquiv D) (hP : InvPres D) (hC : CongVC D E) (hA : InvInvVC D E)
    (hJoinEq : EqJoinLemma3C D E)
    (C : Configuration (QSig E hP hC hA))
    (hReach : (labeledTS3 (QSig E hP hC hA)).ReachableFrom
        (initConfig (QSig E hP hC hA) trivial) C) :
    IsRALinearizable3 C :=
  ra_linearizable3_of_joinC (fullClosure (QSig E hP hC hA).toCRDTSig)
    (fun _ _ h => h)
    (joinC_quotient E hP hC hA hJoinEq)
    (hInit := trivial) C hReach

/-- **Readback — the "up to `≈`" content, spelled out.** For a reachable
`QSig`-configuration, a version whose registered state is the class of a
concrete `D`-state `σ` admits an enumeration `π` of its event set that
respects the `≈`-conditioned linearization order (`loEq`) and, folded
`apply-when-applicable` from `D.init` (`applySeqApp` — each op applied only if
`applicable` at that point, non-`applicable` ops being recorded no-ops), lands
`≈`-equal to `σ`. This is per-version RA-linearizability *up to observational
`≈`* (Def-lin relaxed to `≈`, over the guarded semantics the conditioned MRDT
actually runs), obtained by reading `RA_linearizable_up_to_eq` back through the
quotient (`qmk_eq_iff`, `lo_qsig_iff`, `qapplySeq_init`). -/
theorem RA_linearizable_up_to_eq_readback
    (E : EqEquiv D) (hP : InvPres D) (hC : CongVC D E) (hA : InvInvVC D E)
    (hJoinEq : EqJoinLemma3C D E)
    (C : Configuration (QSig E hP hC hA))
    (hReach : (labeledTS3 (QSig E hP hC hA)).ReachableFrom
        (initConfig (QSig E hP hC hA) trivial) C)
    (v : Version) (σ : D.State) (hσ : D.Inv σ) (Ev : Set (Op D.AppOp))
    (hver : C.ver v = some (qmk E σ hσ, Ev)) :
    ∃ π : List (Op D.AppOp),
      listPermOf π Ev ∧
      respects π (loEq E (Configuration.core C).vis) ∧
      E.eqv (applySeqApp D D.init π) σ := by
  obtain ⟨π, hperm, hresp, hfold⟩ :=
    RA_linearizable_up_to_eq E hP hC hA hJoinEq C hReach v (qmk E σ hσ) Ev hver
  refine ⟨π, hperm, ?_, ?_⟩
  · exact (respects_congr (lo_qsig_iff E hP hC hA (Configuration.core C))).mp hresp
  · rw [qapplySeq_init E hP hC hA π] at hfold
    exact (qmk_eq_iff E).mp hfold

/-! ## §5. `app`-conditioning audit (corrected)

An earlier version of this audit claimed `applicable` "gates only the execution
model (`Step3.apply`'s generation-time guard)" and that "the datatype's own
reachable events are `applicable` by construction of the execution model". **That
is false**: `Step3.apply` (`LCA_Lemma.lean:451`) applies `D.update s (t,r,o)` with
NO `applicable` precondition — its hypotheses are only head/version lookup and
timestamp freshness. So a reachable configuration may hold events that are NOT
`applicable`, and the metatheorem cannot assume otherwise.

This forces the honest design used here. A `ConditionedMRDTSig`'s `update` need
not preserve `Inv` on a non-`applicable` op (verified: the RGA's `do_` breaks
root-freeness on an inaccurate/stale `Ins`, `RGA_VCPackage`), so an UNCONDITIONAL
`InvPres.inv_update` is UNSATISFIABLE by the datatypes this framework hosts. The
resolution is entirely internal to the quotient functor:

* `InvPres.inv_update` is `applicable`-conditioned
  (`Inv s → applicable o s → Inv (update s o)`) — satisfiable, and matched
  verbatim by `RGA_VCPackage.rga_inv_update_of_applicable`.
* The quotient's `update` is the GUARDED step `qdo`/`doApp`: apply `D.update`
  when `applicable`, else the identity. A non-`applicable` event is recorded in
  the version's event set but has no effect on state. `doApp` preserves `Inv`
  unconditionally in `o` (`InvPres.inv_doApp`), so `qdo` stays inside the
  `Inv`-subtype for arbitrary ops — exactly what a total lifted `update` needs
  under the unguarded execution model.
* The guard is baked into BOTH the upstairs fold (`qdo`) and the downstairs fold
  (`applySeqApp`, `apply-when-applicable`), so `qapplySeq` holds UNCONDITIONALLY
  in the enumeration — no "all events applicable" hypothesis has to be threaded
  through `joinC_quotient` / `RA_linearizable_up_to_eq` (which the unguarded
  execution model could not supply anyway). Correspondingly `eqCommutesOn`,
  `loOnEq`/`loEq`, `IsCanonicalStateEq`, `EqJoinLemma3C`, and the readback are all
  stated over the guarded step; on `applicable` ops at `applicable` states the
  guard is transparent (`doApp = update`), so this coincides with the intended
  semantics exactly where it matters.

**Verdict:** `applicable` IS load-bearing in this transfer — but only as the
guard that defines the quotient's `update`, discharged once and for all inside the
functor. `inv_mergeL` stays unconditional: the hosting datatype supplies an `Inv`
strong enough (the RGA's `qInv`, carrying `id_mono`;
`RGA_VCPackage.rga_inv_mergeL_of_idmono`). The metatheorem's conclusion
(`IsRALinearizable3`) and premises are unchanged apart from `InvPres`'s now-honest
shape. -/

#print axioms RA_linearizable_up_to_eq
#print axioms joinC_quotient
#print axioms RA_linearizable_up_to_eq_readback
#print axioms QSig

end GenericEqQuotient
end Sal.Metatheory
