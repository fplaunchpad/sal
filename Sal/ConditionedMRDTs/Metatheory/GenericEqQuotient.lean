import Sal.ConditionedMRDTs.Metatheory.ConditionedContract

/-!
# The generic `≈`-quotient functor and the conditioned metatheorem up to `≈`

`Development/GENERIC_FRAMEWORK_DESIGN.md`, steps 1–3. Everything here is
generic over an abstract `D : ConditionedMRDTSig` — no datatype specifics.

* **§1** the VC bundle a datatype supplies for the `≈`-route, over a
  datatype-declared operation-wellformedness predicate `W` (`WfOp`): `EqEquiv D`
  (the observational relation with its equivalence proof), `InvPres D W`
  (`Inv` holds initially, is preserved by the RAW `update` **on `W`-well-formed
  ops** — `W` is WEAKER than `applicable`, and is what the execution model's
  timestamp freshness actually guarantees — and by `mergeL`), `CongVC D E`
  (`update`/`mergeL`/`query` respect `≈` **on `Inv`-states** — conditioned, per
  `merge_eq_congr_l_fails`), `InvInvVC D E W` (`W` and `applicable` are
  `≈`-invariant on `Inv`-states), and `WfOpReachable D W` (the datatype VC that
  seats each fold step: any distinct-timestamp enumeration folds from `init` with
  `W` at every prefix — the RGA discharges this from monotone ids / path
  structure). `Inv` itself needs no invariance VC — the subtype quotient carries
  it.

  **Why a guard survives inside `qdo` (honest note).** `ConditionedMRDTSig.update`
  is TOTAL and `applySeq` folds it unconditionally, so `qdo : QState → Op →
  QState` must be total into the `Inv`-subtype quotient; with RAW `update` that
  needs `Inv (update s o)`, i.e. `W o s`, which is a reachability-level fact
  `qdo` (a signature field) cannot see. So `qdo` retains a totality guard `doW`
  (identity on `¬W`) — NOT the earlier `applicable`-guard. The un-distortion:
  `doW` is TRANSPARENT on every reachable fold (`W` holds at each prefix by
  `WfOpReachable`), so `applySeqW = applySeq` (raw) there, and `IsCanonicalStateEq`
  / `EqJoinLemma3C` / the readback are all stated over the RAW `applySeq`,
  matching the RGA's raw `applySeqR`.
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

namespace Sal.ConditionedMRDTs
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

/-- **`InvPres D W`** — `Inv` holds at `init`, is preserved by the RAW `update`
**on `W`-well-formed ops** (`W` = the datatype-declared operation-wellformedness
predicate, `WfOp`), and is preserved by `mergeL`. This is the datatype's
`inv_step`; `ConditionedMRDTSig` does not carry it as a field, so it is an
explicit VC here.

`inv_update` is `W`-CONDITIONED, **not** `applicable`-conditioned — this is the
un-distortion. The EXECUTION MODEL (`Step3.apply`, `LCA_Lemma.lean:451`) applies
the RAW `D.update s (t,r,o)` with NO `applicable` guard, but WITH timestamp
freshness (`h_fresh_t`/`h_fresh_store`). So the guarantee the runtime actually
provides for each applied event is *well-formedness* `W` — weaker than
`applicable` — not `applicable`. `W` is datatype-SPECIFIC (RGA: `id ≠ 0 ∧
Ins-freshness ∧ the `Del`-resolve fact`; the `Ins` part comes from
Step3-freshness, the `Del` part from the datatype's own `id_mono`/path structure)
and is discharged along reachable folds by the `WfOpReachable` VC below. A
`ConditionedMRDTSig`'s `update` need not preserve `Inv` on a `¬W` op, so demanding
unconditional preservation would make `InvPres` UNSATISFIABLE by the very
datatypes this framework hosts. `inv_mergeL` stays unconditional: the hosting
datatype picks an `Inv` strong enough (the RGA's `qInv`, carrying `id_mono`;
`RGA_VCPackage.rga_inv_mergeL_of_idmono`). -/
structure InvPres (D : ConditionedMRDTSig)
    (W : Op D.AppOp → D.State → Prop) : Prop where
  inv_init : D.Inv D.init
  inv_update : ∀ (s : D.State) (o : Op D.AppOp),
    D.Inv s → W o s → D.Inv (D.update s o)
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

/-- **`InvInvVC D E W`** — `≈`-invariance VCs, on `Inv`-states, for the two
state-dependent predicates that descend to the quotient: the guard predicate `W`
(`WfOp`, needed to lift the guarded step `doW`), and `applicable` (carried through
as `QSig.applicable`). RGA: `wf`/`fresh`-`eq_iff` for `W`,
`accurate_eq_iff ∧ fresh_ts_eq_iff` for `applicable`. `Inv` itself needs NO
invariance VC: the quotient is the `Inv`-subtype, so every class carries `Inv`. -/
structure InvInvVC (D : ConditionedMRDTSig) (E : EqEquiv D)
    (W : Op D.AppOp → D.State → Prop) : Prop where
  wf_congr : ∀ (o : Op D.AppOp) {s s' : D.State},
    D.Inv s → D.Inv s' → E.eqv s s' → (W o s ↔ W o s')
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

/-! ### The `WfOp`-guarded step (a TOTALITY device) and the raw-fold bridge

`ConditionedMRDTSig.update : State → Op → State` is TOTAL, and the emulation's
`applySeq D s π = π.foldl D.update s` folds it unconditionally. So the quotient's
`update` (`qdo`) must be a TOTAL `QState → Op → QState`; since `QState` is the
`Inv`-subtype quotient, every output must carry an `Inv` proof of its
representative. With RAW `D.update` that proof is `Inv (D.update s o)`, which the
`W`-conditioned `inv_update` supplies only given `W o s`. `W o s` is a
per-`(o,s)` fact the runtime provides only at the CONFIGURATION/reachability
level — strictly downstream of `qdo`, which is a signature field with no access
to any configuration. **So `qdo` cannot be a guard-free raw lift; the guard
`doW` (identity on `¬W`) is FORCED by totality**, independent of whether the
guard is on `applicable` or `W`. This is not silent: the guard is a pure totality
artifact, and — crucially — it is TRANSPARENT on every fold the execution model
produces, because those folds carry `W` at every prefix (`WfOpReachable`), so the
guarded fold `applySeqW` EQUALS the raw fold `applySeq`
(`applySeqW_eq_applySeq_of_wfChain`). That equality is what lets
`IsCanonicalStateEq`/`EqJoinLemma3C`/readback be stated over RAW `applySeq`
(matching the RGA's raw `applySeqR`) even though `qdo` internally guards. The
un-distortion vs. the earlier `applicable`-guard: `doW` skips only `¬W`
(non-fresh) ops the runtime NEVER applies, whereas the `applicable`-guard skipped
`applicable`-but-fresh ops the runtime DOES apply. -/

/-- One `W`-guarded step: apply `o` when `W`-well-formed, else keep the state.
Identity fallback is the forced totality device (see the `§` note above). -/
noncomputable def doW (D : ConditionedMRDTSig)
    (W : Op D.AppOp → D.State → Prop) (o : Op D.AppOp) (s : D.State) : D.State :=
  if W o s then D.update s o else s

/-- `doW` preserves `Inv` UNCONDITIONALLY in `o`: the `W` branch is the
`W`-conditioned `inv_update`; the identity branch keeps `Inv`. -/
theorem InvPres.inv_doW {W : Op D.AppOp → D.State → Prop} (hP : InvPres D W)
    (o : Op D.AppOp) (s : D.State) (hs : D.Inv s) : D.Inv (doW D W o s) := by
  unfold doW
  by_cases h : W o s
  · rw [if_pos h]; exact hP.inv_update s o hs h
  · rw [if_neg h]; exact hs

/-- The guarded step respects `≈` on `Inv`-states: `W` agrees across `≈`
(`InvInvVC.wf_congr`), and each branch is congruent (`update_congr` /
reflexivity). This is what makes `qdo` well-defined on the quotient. -/
theorem doW_congr (E : EqEquiv D) {W : Op D.AppOp → D.State → Prop}
    (hC : CongVC D E) (hA : InvInvVC D E W)
    (o : Op D.AppOp) {s s' : D.State} (hs : D.Inv s) (hs' : D.Inv s')
    (h : E.eqv s s') : E.eqv (doW D W o s) (doW D W o s') := by
  unfold doW
  by_cases hp : W o s
  · have hp' : W o s' := (hA.wf_congr o hs hs' h).mp hp
    rw [if_pos hp, if_pos hp']
    exact hC.update_congr o hs hs' h
  · have hp' : ¬ W o s' :=
      fun c => hp ((hA.wf_congr o hs hs' h).mpr c)
    rw [if_neg hp, if_neg hp']
    exact h

/-- Guarded fold: `applySeq` with each step guarded by `W`. What the quotient's
`update`-fold computes downstairs (`qapplySeq`); provably `= applySeq` (raw) on
every reachable enumeration (`applySeqW_eq_applySeq_of_wfChain`). -/
noncomputable def applySeqW (D : ConditionedMRDTSig)
    (W : Op D.AppOp → D.State → Prop) (s : D.State)
    (ρ : List (Op D.AppOp)) : D.State :=
  ρ.foldl (fun s o => doW D W o s) s

/-- `WfChain D W s ρ` — `W` holds at every prefix-state of folding `ρ` from `s`.
The per-fold-state well-formedness the execution model guarantees along a
reachable trace; `WfOpReachable` discharges it for the linearizations that
appear. -/
def WfChain (D : ConditionedMRDTSig) (W : Op D.AppOp → D.State → Prop) :
    D.State → List (Op D.AppOp) → Prop
  | _, [] => True
  | s, o :: ρ => W o s ∧ WfChain D W (D.update s o) ρ

/-- **Guard transparency.** On a `WfChain` enumeration the guarded fold IS the raw
fold: every step's `W` holds, so `doW = update` throughout. This is the bridge
that carries the metatheorem's conclusions onto RAW `applySeq`. -/
theorem applySeqW_eq_applySeq_of_wfChain {W : Op D.AppOp → D.State → Prop}
    {s : D.State} {ρ : List (Op D.AppOp)} (hc : WfChain D W s ρ) :
    applySeqW D W s ρ = applySeq D.toCRDTSig s ρ := by
  induction ρ generalizing s with
  | nil => rfl
  | cons o ρ ih =>
    obtain ⟨hw, hrest⟩ := hc
    have hstep : doW D W o s = D.update s o := if_pos hw
    show applySeqW D W (doW D W o s) ρ = applySeq D.toCRDTSig (D.update s o) ρ
    rw [hstep]; exact ih hrest

/-- The RAW fold preserves `Inv` along a `WfChain` (each step is `inv_update` at a
`W`-well-formed state). Seats the raw fold in the `Inv`-subfamily. -/
theorem InvPres.inv_applySeq_of_wfChain {W : Op D.AppOp → D.State → Prop}
    (hP : InvPres D W) {s : D.State} {ρ : List (Op D.AppOp)}
    (hs : D.Inv s) (hc : WfChain D W s ρ) :
    D.Inv (applySeq D.toCRDTSig s ρ) := by
  induction ρ generalizing s with
  | nil => exact hs
  | cons o ρ ih =>
    obtain ⟨hw, hrest⟩ := hc
    exact ih (hP.inv_update s o hs hw) hrest

/-- **`WfOpReachable D W WfOpGen`** — the datatype VC that seats each fold step,
carrying a per-event **generation-wellformedness** premise `WfOpGen`. Any `Nodup`
enumeration with pairwise-distinct timestamps AND all-`WfOpGen` events folds from
`init` with `W` at every prefix. `WfOpGen` is the honest per-op side condition a
real execution supplies (via `applicable` at generation) that `Nodup +
distinct-ts` alone do NOT (RGA: `Ins` needs `t ≠ 0`; `Del pre x` needs `x ∉ pre ∧
x ≠ 0`). Without it the VC is UNSATISFIABLE — a genuinely-applicable root delete
`Del [] 0` is `Nodup`/distinct-ts-legal yet `resolve init [] = 0 = x`, so `W`
fails (kernel-refuted as `RGA_WfOpReachable.rga_wfOpReachable_false` against the
old 2-argument shape). With the premise the datatype discharges it: RGA's
`rga_wfChain_of_genuine` proves exactly `∀ ρ, Nodup → distinct-ts →
(∀ o ∈ ρ, WfOpGen o) → WfChain`. `W`/`WfOpGen` are datatype-SPECIFIC. -/
def WfOpReachable (D : ConditionedMRDTSig)
    (W : Op D.AppOp → D.State → Prop) (WfOpGen : Op D.AppOp → Prop) : Prop :=
  ∀ ρ : List (Op D.AppOp), ρ.Nodup →
    (∀ a ∈ ρ, ∀ b ∈ ρ, a ≠ b → Op.time a ≠ Op.time b) →
    (∀ o ∈ ρ, WfOpGen o) →
    WfChain D W D.init ρ

/-- Distinct timestamps of any `listPermOf` of an event set whose members are all
witnessed in `Cq` — read off `Configuration.timestamps_distinct`. Feeds
`WfOpReachable` at every use site. -/
theorem distinct_ts_of_perm
    (Cq : Sal.Emulation.Configuration D.toCRDTSig)
    {ev : Set (Op D.AppOp)} {ρ : List (Op D.AppOp)}
    (hsub : ∀ a ∈ ev, a ∈ Cq.events) (hperm : listPermOf ρ ev) :
    ∀ a ∈ ρ, ∀ b ∈ ρ, a ≠ b → Op.time a ≠ Op.time b := by
  intro a ha b hb hne
  obtain ⟨r, s, hLr, hsa⟩ := hsub a ((hperm.2 a).mp ha)
  obtain ⟨r', s', hLr', hsb⟩ := hsub b ((hperm.2 b).mp hb)
  exact Cq.timestamps_distinct hLr hsa hLr' hsb hne

/-- `Inv` is preserved by a guarded fold, UNCONDITIONALLY in `ρ` (each step is
`inv_doW`). -/
theorem InvPres.applySeqW {W : Op D.AppOp → D.State → Prop} (hP : InvPres D W)
    (ρ : List (Op D.AppOp))
    (s : D.State) (hs : D.Inv s) : D.Inv (applySeqW D W s ρ) := by
  induction ρ generalizing s with
  | nil => exact hs
  | cons o ρ ih => exact ih (doW D W o s) (hP.inv_doW o s hs)

section Functor
variable (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
  (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)

/-- `update` lifted to the quotient — the `W`-guarded step (`doW`) lifted.
Well-defined by `doW_congr` (whose `Inv` hypotheses are supplied by the subtype);
it lands in the subtype by `InvPres.inv_doW`, which needs only the `W`-conditioned
`inv_update` (the `¬W` branch is the identity, keeping `Inv` for free). The `¬W`
identity fallback is the forced totality device (§ note above); it is transparent
on all reachable folds. `noncomputable` via `doW`'s classical `W`-guard. -/
noncomputable def qdo (q : QState D E) (o : Op D.AppOp) : QState D E :=
  Quotient.lift
    (fun sp : InvState D => qmk E (doW D W o sp.1) (hP.inv_doW o sp.1 sp.2))
    (fun sp sp' h => Quotient.sound (doW_congr E hC hA o sp.2 sp'.2 h)) q

@[simp] theorem qdo_qmk (o : Op D.AppOp) (s : D.State) (hs : D.Inv s) :
    qdo E W hP hC hA (qmk E s hs) o
      = qmk E (doW D W o s) (hP.inv_doW o s hs) := rfl

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
    qmergeL E W hP hC (qmk E l hl) (qmk E a ha) (qmk E b hb)
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
  update := fun q o => qdo E W hP hC hA q o
  merge := fun a b => qmergeL E W hP hC (qmk E D.init hP.inv_init) a b
  query := fun q qu => qquery E hC q qu
  rc := D.rc
  mergeL := fun l a b => qmergeL E W hP hC l a b
  merge_init_slice := fun _ _ => rfl
  Inv := fun _ => True
  applicable := fun o q => qapplicable E W hA o q

/-- `applySeq` commutes with the quotient: folding the lifted (guarded) `update`
over a class is the class of the guarded fold `applySeqW`. The guard `doW` is
baked into BOTH sides — `qdo` upstairs, `doW` downstairs — so this holds
UNCONDITIONALLY in `ρ` (the totality guard is on both sides). The bridge to the
RAW fold happens later, at the use sites, via `applySeqW_eq_applySeq_of_wfChain`
fed by `WfOpReachable`. -/
theorem qapplySeq (ρ : List (Op D.AppOp)) (s : D.State) (hs : D.Inv s) :
    Sal.Emulation.applySeq (QSig E W hP hC hA).toCRDTSig (qmk E s hs) ρ
      = qmk E (applySeqW D W s ρ) (hP.applySeqW ρ s hs) := by
  induction ρ generalizing s with
  | nil => rfl
  | cons o ρ ih => exact ih (doW D W o s) (hP.inv_doW o s hs)

/-- `qapplySeq` at the initial state, keyed on `(QSig …).init` so it rewrites
the `IsCanonicalState`/`IsRALinearizable3` folds syntactically. -/
theorem qapplySeq_init (ρ : List (Op D.AppOp)) :
    Sal.Emulation.applySeq (QSig E W hP hC hA).toCRDTSig
        (QSig E W hP hC hA).init ρ
      = qmk E (applySeqW D W D.init ρ)
          (hP.applySeqW ρ D.init hP.inv_init) :=
  qapplySeq E W hP hC hA ρ D.init hP.inv_init

end Functor

/-! ## §3. Downstairs readings of the quotient's `commutes`/`loOn`, and the
configuration transport -/

/-- **`≈`-commutation on `Inv`-states** — exactly what `(QSig …).commutes`
means downstairs. The steps are the `W`-guarded steps (`doW`), because the
quotient's `update` is `qdo`: on `W`-well-formed ops `doW = update`, so this is
real commutation there, and a `¬W` op commutes as a no-op (a state the execution
model never reaches). Conditioned on `Inv` only — quotient states carry no `W`,
so this (not `commutesOn`) is the commutation notion the `≈`-route's Join is
proved against. -/
def eqCommutesOn (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (o₁ o₂ : Op D.AppOp) : Prop :=
  ∀ s : D.State, D.Inv s →
    E.eqv (doW D W o₂ (doW D W o₁ s)) (doW D W o₁ (doW D W o₂ s))

section Transfer
variable (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
  (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)

/-- The quotient's structural `commutes` IS `≈`-commutation-on-`Inv`. -/
theorem qcommutes_iff (o₁ o₂ : Op D.AppOp) :
    (QSig E W hP hC hA).toCRDTSig.commutes o₁ o₂ ↔ eqCommutesOn E W o₁ o₂ := by
  constructor
  · intro h s hs
    exact Quotient.exact (h (qmk E s hs))
  · intro h q
    exact Quotient.inductionOn q
      (fun sp => Quotient.sound (h sp.1 sp.2))

/-- `Sal.Emulation.loOn` with an abstract `vis` graph and `commutes` replaced
by `≈`-commutation-on-`Inv`: the linearization order the datatype's `≈`-Join
enumerations must respect. Reads only `vis` and `D.rc`. -/
def loOnEq (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (vis : Op D.AppOp → Op D.AppOp → Prop)
    (ev : Set (Op D.AppOp)) (e₁ e₂ : Op D.AppOp) : Prop :=
  (vis e₁ e₂ ∧ ¬ eqCommutesOn E W e₁ e₂)
  ∨ ( ¬ vis e₁ e₂ ∧ ¬ vis e₂ e₁
      ∧ D.rc e₁ e₂ = RcRes.Fst_then_snd
      ∧ ¬ ∃ e₃ ∈ ev, vis e₂ e₃ ∧ ¬ eqCommutesOn E W e₂ e₃ )

/-- Global (`ev`-unrestricted) variant, mirroring `Sal.Emulation.lo`. -/
def loEq (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (vis : Op D.AppOp → Op D.AppOp → Prop)
    (e₁ e₂ : Op D.AppOp) : Prop :=
  (vis e₁ e₂ ∧ ¬ eqCommutesOn E W e₁ e₂)
  ∨ ( ¬ vis e₁ e₂ ∧ ¬ vis e₂ e₁
      ∧ D.rc e₁ e₂ = RcRes.Fst_then_snd
      ∧ ¬ ∃ e₃, vis e₂ e₃ ∧ ¬ eqCommutesOn E W e₂ e₃ )

/-- `loOn` of a `QSig`-configuration reads back as `loOnEq` over its `vis`. -/
theorem loOn_qsig_iff
    (Cq : Sal.Emulation.Configuration (QSig E W hP hC hA).toCRDTSig)
    (ev : Set (Op D.AppOp)) (e₁ e₂ : Op D.AppOp) :
    Sal.Emulation.loOn Cq ev e₁ e₂ ↔ loOnEq E W Cq.vis ev e₁ e₂ := by
  unfold Sal.Emulation.loOn loOnEq
  simp only [qcommutes_iff E W hP hC hA]
  exact Iff.rfl

/-- `lo` of a `QSig`-configuration reads back as `loEq` over its `vis`. -/
theorem lo_qsig_iff
    (Cq : Sal.Emulation.Configuration (QSig E W hP hC hA).toCRDTSig)
    (e₁ e₂ : Op D.AppOp) :
    Sal.Emulation.lo Cq e₁ e₂ ↔ loEq E W Cq.vis e₁ e₂ := by
  unfold Sal.Emulation.lo loEq
  simp only [qcommutes_iff E W hP hC hA]
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
folded from `D.init` by the RAW `applySeq` (`= π.foldl D.update`, matching the
RGA's `applySeqR`), lands `≈`-equal to `s`. This is `IsCanonicalState` with `=`
relaxed to `≈` and `loOn`'s `commutes` replaced by `≈`-commutation-on-`Inv`
(`loOnEq`). The fold is RAW — the quotient's internal `doW`-guard is discharged
(guarded `= raw`) at the transfer via `WfOpReachable`, so the datatype states its
`≈`-Join over its own raw update, not a guarded surrogate. -/
def IsCanonicalStateEq (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (vis : Op D.AppOp → Op D.AppOp → Prop)
    (ev : Set (Op D.AppOp)) (s : D.State) : Prop :=
  ∃ ρ : List (Op D.AppOp),
    listPermOf ρ ev ∧ respects ρ (loOnEq E W vis ev) ∧
    E.eqv (applySeq D.toCRDTSig D.init ρ) s

/-- **The datatype's `≈`-Join Lemma** (`EqJoinLemma3C`), the sole
convergence VC of the `≈`-route. `JoinLemma3F`/`JoinLemma3C … fullClosure`
with `=` relaxed to `≈`, over an abstract `vis`/`events`, with the sides
required `Inv` (the reachable subfamily the RGA's `≈`-Join lives on). Canonical
states fold the RAW `applySeq`. Fully closed sides so the quotient's
`𝒞 := fullClosure` matches. -/
def EqJoinLemma3C (D : ConditionedMRDTSig) (E : EqEquiv D)
    (W : Op D.AppOp → D.State → Prop)
    (GenDisc : (Op D.AppOp → Op D.AppOp → Prop) → Set (Op D.AppOp) → Prop) : Prop :=
  ∀ (vis : Op D.AppOp → Op D.AppOp → Prop) (events : Set (Op D.AppOp))
    (ev₁ ev₂ : Set (Op D.AppOp)) (s₀ s₁ s₂ : D.State),
    D.Inv s₀ → D.Inv s₁ → D.Inv s₂ →
    (∀ {a b c : Op D.AppOp}, vis a b → vis b c → vis a c) →
    (∀ a : Op D.AppOp, ¬ vis a a) →
    (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
    fullClosureRel vis ev₁ → fullClosureRel vis ev₂ →
    GenDisc vis ev₁ → GenDisc vis ev₂ → GenDisc vis (ev₁ ∪ ev₂) →
    IsCanonicalStateEq E W vis (ev₁ ∩ ev₂) s₀ →
    IsCanonicalStateEq E W vis ev₁ s₁ → IsCanonicalStateEq E W vis ev₂ s₂ →
    IsCanonicalStateEq E W vis (ev₁ ∪ ev₂) (D.mergeL s₀ s₁ s₂)

section Transfer2
variable (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
  (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
  (WfOpGen : Op D.AppOp → Prop) (hWFR : WfOpReachable D W WfOpGen)
include hWFR

/-- The bridge: `IsCanonicalState` of a `QSig`-configuration at a class
`qmk E s hs` IS the datatype's `IsCanonicalStateEq` (over the RAW `applySeq`) at
the representative — the quotient makes `=` into `≈` (`qmk_eq_iff`) and `loOn`
into `loOnEq` (`loOn_qsig_iff`), the fold commutes with `qmk` (`qapplySeq_init`),
and the internal `doW`-guard is discharged (`applySeqW = applySeq`) via
`WfOpReachable`. Its `WfOpGen` premise is fed by `hGenEv` (every event of `ev` is
`WfOpGen`, an HONEST execution condition — see `RA_linearizable_up_to_eq`), and
its distinct-timestamp premise by `ev`'s members (`hsub` +
`Configuration.timestamps_distinct`). This is where guarded folds become raw. -/
theorem isCanonicalState_qsig_iff
    (Cq : Sal.Emulation.Configuration (QSig E W hP hC hA).toCRDTSig)
    (ev : Set (Op D.AppOp)) (hsub : ∀ a ∈ ev, a ∈ Cq.events)
    (hGenEv : ∀ o ∈ ev, WfOpGen o)
    (s : D.State) (hs : D.Inv s) :
    Sal.Emulation.IsCanonicalState Cq ev (qmk E s hs)
      ↔ IsCanonicalStateEq E W Cq.vis ev s := by
  unfold Sal.Emulation.IsCanonicalState IsCanonicalStateEq
  constructor
  · rintro ⟨ρ, hperm, hresp, hfold⟩
    have heq : applySeqW D W D.init ρ = applySeq D.toCRDTSig D.init ρ :=
      applySeqW_eq_applySeq_of_wfChain
        (hWFR ρ hperm.1 (distinct_ts_of_perm Cq hsub hperm)
          (fun o ho => hGenEv o ((hperm.2 o).mp ho)))
    refine ⟨ρ, hperm,
      (respects_congr (loOn_qsig_iff E W hP hC hA Cq ev)).mp hresp, ?_⟩
    rw [qapplySeq_init E W hP hC hA ρ] at hfold
    have hev := (qmk_eq_iff E).mp hfold
    rw [heq] at hev
    exact hev
  · rintro ⟨ρ, hperm, hresp, hfold⟩
    have heq : applySeqW D W D.init ρ = applySeq D.toCRDTSig D.init ρ :=
      applySeqW_eq_applySeq_of_wfChain
        (hWFR ρ hperm.1 (distinct_ts_of_perm Cq hsub hperm)
          (fun o ho => hGenEv o ((hperm.2 o).mp ho)))
    refine ⟨ρ, hperm,
      (respects_congr (loOn_qsig_iff E W hP hC hA Cq ev)).mpr hresp, ?_⟩
    rw [qapplySeq_init E W hP hC hA ρ]
    refine (qmk_eq_iff E).mpr ?_
    rw [heq]; exact hfold

end Transfer2

/-- **The conditioned closure index.** The quotient Join runs at `fullClosure`
PLUS a per-event `WfOpGen` side-condition on the event set. `WfOpGen` cannot be
dropped: `isCanonicalState_qsig_iff`'s guarded-to-raw bridge fails on a set
containing a non-`WfOpGen` event (e.g. an RGA root delete, where the guarded fold
skips but the raw fold does not — `rga_wfOpReachable_false`), so the quotient Join
is GENUINELY conditioned. This index is NOT implied by `fullClosure`, so it does
NOT feed `ra_linearizable3_of_joinC` (which demands `fullClosure ⟹ 𝒞`); the
metatheorem re-threads it through the reachability induction instead. -/
def wfGenFull (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (WfOpGen : Op D.AppOp → Prop) :
    ClosurePred (QSig E W hP hC hA).toCRDTSig :=
  fun C ev => fullClosure (QSig E W hP hC hA).toCRDTSig C ev ∧ (∀ o ∈ ev, WfOpGen o)

/-- **The config-relative generation-discipline supply** (agreement-parameterized).
The datatype's `GenDisc` holds for every backward-closed delivered set `ev ⊆
Cfg.events`, evaluated at ANY `vis` that AGREES with `Cfg.vis` on `ev`. Mentions
`Cfg` — config-relative, mirroring `hGenC`'s `∀ o ∈ Cfg.events, WfOpGen o`, and
SATISFIABLE (the discipline is only asserted for genuine, delivered sets, not for
arbitrary/fabricated ones). The agreement clause is what lets the reachability
re-threading move the supply from a config to its predecessor: an `apply` step's
new `vis` edges only target the FRESH event, which is OUTSIDE any `ev ⊆
Cfg.events`, so `vis` restricted to such an `ev` is invariant (`vis_agree_of_step`).
A `vis`-local `GenDisc` (e.g. the RGA's `GenDisc2CEq`, which reads only
`vis`-edges internal to `ev`) discharges it from the honest-execution condition. -/
def GDSupply (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (GenDisc : (Op D.AppOp → Op D.AppOp → Prop) → Set (Op D.AppOp) → Prop)
    (Cfg : Sal.Emulation.Configuration (QSig E W hP hC hA).toCRDTSig) : Prop :=
  ∀ (vis : Op D.AppOp → Op D.AppOp → Prop) (ev : Set (Op D.AppOp)),
    (∀ a b, a ∈ ev → b ∈ ev → (vis a b ↔ Cfg.vis a b)) →
    fullClosureRel vis ev → (∀ a ∈ ev, a ∈ Cfg.events) → GenDisc vis ev

/-- **`joinC_quotient`** — the per-configuration transfer theorem. For a FIXED
`QSig`-configuration `Cq`, the datatype's `≈`-Join (`EqJoinLemma3C`) yields the
merged canonical state, given each side's `wfGenFull` closure PLUS the datatype
genuineness `GenDisc` for the two sides AND their union, supplied explicitly. The
union genuineness is NOT a `JoinLemma3C` side-hypothesis (which only carries the
two sides), so it must be supplied per-config — which is why the caller
(`goodConfig3_merge_wfgen`) feeds all three from the reachable config's `GDSupply`,
rather than from a config-generic premise (that would be unsatisfiable on
fabricated configs). Pure quotient bookkeeping otherwise: induct the three
canonical states to representatives, rewrite each `IsCanonicalState` through
`isCanonicalState_qsig_iff`, apply the `≈`-Join, rewrite the `qmergeL` back. -/
theorem joinC_quotient
    (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (WfOpGen : Op D.AppOp → Prop) (hWFR : WfOpReachable D W WfOpGen)
    (GenDisc : (Op D.AppOp → Op D.AppOp → Prop) → Set (Op D.AppOp) → Prop)
    (hJoinEq : EqJoinLemma3C D E W GenDisc)
    (Cq : Sal.Emulation.Configuration (QSig E W hP hC hA).toCRDTSig)
    (ev₁ ev₂ : Set (Op D.AppOp)) (s₀ s₁ s₂ : (QSig E W hP hC hA).State)
    (htr : ∀ {a b c : Op D.AppOp}, Cq.vis a b → Cq.vis b c → Cq.vis a c)
    (hir : ∀ a : Op D.AppOp, ¬ Cq.vis a a)
    (hin₁ : ∀ a ∈ ev₁, a ∈ Cq.events) (hin₂ : ∀ a ∈ ev₂, a ∈ Cq.events)
    (hcl₁ : wfGenFull E W hP hC hA WfOpGen Cq ev₁)
    (hcl₂ : wfGenFull E W hP hC hA WfOpGen Cq ev₂)
    (hgd₁ : GenDisc Cq.vis ev₁) (hgd₂ : GenDisc Cq.vis ev₂)
    (hgdU : GenDisc Cq.vis (ev₁ ∪ ev₂))
    (hc₀ : IsCanonicalState Cq (ev₁ ∩ ev₂) s₀)
    (hc₁ : IsCanonicalState Cq ev₁ s₁) (hc₂ : IsCanonicalState Cq ev₂ s₂) :
    IsCanonicalState Cq (ev₁ ∪ ev₂) ((QSig E W hP hC hA).mergeL s₀ s₁ s₂) := by
  obtain ⟨hcl₁f, hgen₁⟩ := hcl₁
  obtain ⟨hcl₂f, hgen₂⟩ := hcl₂
  have hgenI : ∀ o ∈ ev₁ ∩ ev₂, WfOpGen o := fun o ho => hgen₁ o ho.1
  have hgenU : ∀ o ∈ ev₁ ∪ ev₂, WfOpGen o := fun o ho => ho.elim (hgen₁ o) (hgen₂ o)
  revert hc₀ hc₁ hc₂
  refine Quotient.inductionOn₃ s₀ s₁ s₂ ?_
  rintro ⟨l, hl⟩ ⟨a, ha⟩ ⟨b, hb⟩ hc₀ hc₁ hc₂
  have g₀ := (isCanonicalState_qsig_iff E W hP hC hA WfOpGen hWFR Cq (ev₁ ∩ ev₂)
    (fun x hx => hin₁ x (And.left hx)) hgenI l hl).mp hc₀
  have g₁ := (isCanonicalState_qsig_iff E W hP hC hA WfOpGen hWFR Cq ev₁
    hin₁ hgen₁ a ha).mp hc₁
  have g₂ := (isCanonicalState_qsig_iff E W hP hC hA WfOpGen hWFR Cq ev₂
    hin₂ hgen₂ b hb).mp hc₂
  have gm := hJoinEq Cq.vis Cq.events ev₁ ev₂ l a b hl ha hb
    htr hir hin₁ hin₂ hcl₁f hcl₂f hgd₁ hgd₂ hgdU g₀ g₁ g₂
  exact (isCanonicalState_qsig_iff E W hP hC hA WfOpGen hWFR Cq (ev₁ ∪ ev₂)
    (fun x hx => Or.elim hx (hin₁ x) (hin₂ x)) hgenU
    (D.mergeL l a b) (hP.inv_mergeL l a b hl ha hb)).mpr gm

/-! ### Re-threading the conditioned Join through reachability

Because `wfGenFull` is NOT implied by `fullClosure`, the conditioned Join cannot
feed `ra_linearizable3_of_joinC`. Instead the metatheorem re-derives the
`GoodConfig3` reachability induction, threading a per-config `WfOpGen`-on-events
premise (monotone along the trace, discharged by the honest execution hypothesis
`∀ o ∈ C.events, WfOpGen o`). The merge step applies `joinC_quotient` at the
predecessor's core, supplying `WfOpGen` for the two sides from the threaded
premise. The other three step lemmas are the public `Adequacy` ones. -/

/-- Event universe grows under a `L`-map update whose new set covers the old. -/
theorem events_mono_of_updateRep {D' : ConditionedMRDTSig}
    {C C' : Configuration D'} {r : Replica} {X : Set (Op D'.AppOp)}
    (hL : C'.L = updateRep C.L r X)
    (hsub : ∀ s, C.L r = some s → s ⊆ X) :
    ∀ x, x ∈ C.events → x ∈ C'.events := by
  rintro x ⟨r'', s'', hLr'', hx⟩
  by_cases hr'' : r'' = r
  · subst hr''
    exact ⟨r'', X, by rw [hL]; simp [updateRep], hsub s'' hLr'' hx⟩
  · refine ⟨r'', s'', ?_, hx⟩
    rw [hL]; simp only [updateRep, if_neg hr'']; exact hLr''

/-- Event universe grows along any `Step3` transition. -/
theorem events_mono_of_step {D' : ConditionedMRDTSig}
    {b c : Configuration D'} {ℓ : Label3 D'} (hstep : Step3 D' b ℓ c) :
    ∀ x, x ∈ b.events → x ∈ c.events := by
  cases hstep with
  | createReplica h_fresh C' hN hL hvis hver hhead hparents =>
    exact events_mono_of_updateRep hL
      (fun s hs => by rw [(b.dom_eq _).mp h_fresh] at hs; exact absurd hs (by simp))
  | apply h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank C'
      hN hL hvis hver hhead hparents =>
    have hco := (b.head_coherent _ _ h_head).2
    rw [h_ver] at hco; simp only [Option.map_some] at hco
    exact events_mono_of_updateRep hL
      (fun s hs => by rw [← hco, Option.some.injEq] at hs; subst hs
                      exact Set.subset_union_left)
  | merge h_head₁ h_head₂ h_ver₁ h_ver₂ h_lca h_verT h_vm h_rank₁
      h_rank₂ C' hN hL hvis hver hhead hparents =>
    have hco := (b.head_coherent _ _ h_head₁).2
    rw [h_ver₁] at hco; simp only [Option.map_some] at hco
    exact events_mono_of_updateRep hL
      (fun s hs => by rw [← hco, Option.some.injEq] at hs; subst hs
                      exact Set.subset_union_left)
  | query h_s h_val => exact fun x hx => hx

/-- **`vis` agrees across a `Step3` on the predecessor's event universe.** The only
transition that changes `vis` is `Apply`, whose new edges all TARGET the fresh
event `(t, r, o)`; timestamp freshness (`h_fresh_t`) keeps that event out of
`C.events`, so on pairs of already-existing events the two `vis` relations
coincide. This is the fact the `GDSupply` re-threading uses to move the
generation-discipline supply from a config to its predecessor. -/
theorem vis_agree_of_step {D' : ConditionedMRDTSig}
    {b c : Configuration D'} {ℓ : Label3 D'} (hstep : Step3 D' b ℓ c) :
    ∀ a x, a ∈ b.events → x ∈ b.events → (b.vis a x ↔ c.vis a x) := by
  cases hstep with
  | createReplica h_fresh C' hN hL hvis hver hhead hparents =>
    intro a x _ _; rw [hvis]
  | apply h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank C'
      hN hL hvis hver hhead hparents =>
    intro a x _ hx; rw [hvis]
    refine ⟨Or.inl, ?_⟩
    rintro (h | ⟨-, hxeq⟩)
    · exact h
    · exact absurd (by simp [hxeq, Op.time]) (h_fresh_t x hx)
  | merge h_head₁ h_head₂ h_ver₁ h_ver₂ h_lca h_verT h_vm h_rank₁
      h_rank₂ C' hN hL hvis hver hhead hparents =>
    intro a x _ _; rw [hvis]
  | query h_s h_val => intro a x _ _; exact Iff.rfl

/-- **The merge step, factored on its merged canonical state.** `goodConfig3` is
preserved by a ternary-merge transition once the merged version's state is shown
canonical — the join-lemma application is the ONLY thing this factors out
(everything else is store bookkeeping, verbatim `Adequacy.goodConfig3_mergeF`).
The conditioned metatheorem supplies `h_merged` from `joinC_quotient`. -/
theorem goodConfig3_merge_of_canonical {D' : ConditionedMRDTSig}
    {C C' : Configuration D'} {r₁ : Replica} {v₁ v₂ vm : Version}
    {s₁ s₂ sT : D'.State} {ev₁ ev₂ : Set (Op D'.AppOp)}
    (h_head₁ : C.head r₁ = some v₁)
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂))
    (hL : C'.L = updateRep C.L r₁ (ev₁ ∪ ev₂))
    (hvis : C'.vis = C.vis)
    (hver : C'.ver = fun w => if w = vm
      then some (D'.mergeL sT s₁ s₂, ev₁ ∪ ev₂) else C.ver w)
    (h : GoodConfig3 C)
    (h_merged : IsCanonicalState (Configuration.core C) (ev₁ ∪ ev₂)
      (D'.mergeL sT s₁ s₂)) :
    GoodConfig3 C' := by
  have hco := C.head_coherent r₁ v₁ h_head₁
  have hLr₁ : C.L r₁ = some ev₁ := by rw [← hco.2, h_ver₁]; rfl
  have hver_new : C'.ver vm = some (D'.mergeL sT s₁ s₂, ev₁ ∪ ev₂) := by
    rw [hver]; simp
  have hver_old : ∀ w, w ≠ vm → C'.ver w = C.ver w := by
    intro w hw; rw [hver]; simp [hw]
  have h_same : ∀ (E' : Set (Op D'.AppOp)) (s' : D'.State),
      IsCanonicalState (Configuration.core C) E' s' →
      IsCanonicalState (Configuration.core C') E' s' := by
    intro E' s' hcs
    refine isCanonicalState_congr (fun a _ b _ => ?_) hcs
    rw [core_vis, core_vis, hvis]
  have hL'r₁ : C'.L r₁ = some (ev₁ ∪ ev₂) := by rw [hL]; simp [updateRep]
  have h_events : ∀ x, x ∈ C.events → x ∈ C'.events := by
    rintro x ⟨r'', s'', hLr'', hx⟩
    by_cases hr'' : r'' = r₁
    · subst hr''
      rw [hLr₁, Option.some.injEq] at hLr''
      exact ⟨r'', ev₁ ∪ ev₂, hL'r₁, Or.inl (hLr'' ▸ hx)⟩
    · refine ⟨r'', s'', ?_, hx⟩
      rw [hL]; simp only [updateRep, if_neg hr'']; exact hLr''
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w s' E' hw
    by_cases hwn : w = vm
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.1, ← hw.2]
      exact h_same _ _ h_merged
    · rw [hver_old w hwn] at hw
      exact h_same E' s' (h.canonical w s' E' hw)
  · intro a b c hab hbc
    rw [hvis] at hab hbc ⊢
    exact h.vis_trans hab hbc
  · intro a ha
    rw [hvis] at ha
    exact h.vis_irrefl a ha
  · intro w s' E' hw a ha
    by_cases hwn : w = vm
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.2] at ha
      exact ⟨r₁, ev₁ ∪ ev₂, hL'r₁, ha⟩
    · rw [hver_old w hwn] at hw
      exact h_events a (h.ver_events_sub w s' E' hw a ha)
  · intro w s' E' hw a b hab hb
    rw [hvis] at hab
    by_cases hwn : w = vm
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.2] at hb ⊢
      rcases hb with hb | hb
      · exact Or.inl (h.ver_causal v₁ s₁ ev₁ h_ver₁ a b hab hb)
      · exact Or.inr (h.ver_causal v₂ s₂ ev₂ h_ver₂ a b hab hb)
    · rw [hver_old w hwn] at hw
      exact h.ver_causal w s' E' hw a b hab hb

/-- **The conditioned merge step lemma** (QSig-specialized). Mirrors
`Adequacy.goodConfig3_mergeF`, but derives the merged canonical state from the
per-config `joinC_quotient` (index `wfGenFull`) instead of an unconditional
`JoinLemma3F`: the two sides' `WfOpGen` facts (required by `wfGenFull`) are read
off `hGenC` via `ver_events_sub`, and the datatype genuineness for BOTH sides AND
their union is read off the config-relative `hGDc` (`GDSupply` for the predecessor
core), whose backward-closure / `⊆ events` obligations are exactly `ver_causal` /
`ver_events_sub` (agreement is reflexive here — `Iff.rfl`). The merge data (`ev₁`,
`sT`, …) are implicit, inferred from the step hypotheses. -/
theorem goodConfig3_merge_wfgen
    (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (WfOpGen : Op D.AppOp → Prop) (hWFR : WfOpReachable D W WfOpGen)
    (GenDisc : (Op D.AppOp → Op D.AppOp → Prop) → Set (Op D.AppOp) → Prop)
    (hJoinEq : EqJoinLemma3C D E W GenDisc)
    {C C' : Configuration (QSig E W hP hC hA)} {r₁ : Replica}
    {v₁ v₂ vT vm : Version}
    {s₁ s₂ sT : (QSig E W hP hC hA).State} {ev₁ ev₂ evT : Set (Op D.AppOp)}
    (h_head₁ : C.head r₁ = some v₁)
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂))
    (h_lca : IsLCA C.parents v₁ v₂ vT)
    (h_verT : C.ver vT = some (sT, evT))
    (hL : C'.L = updateRep C.L r₁ (ev₁ ∪ ev₂))
    (hvis : C'.vis = C.vis)
    (hver : C'.ver = fun w => if w = vm
      then some ((QSig E W hP hC hA).mergeL sT s₁ s₂, ev₁ ∪ ev₂) else C.ver w)
    (hGenC : ∀ o ∈ (Configuration.core C).events, WfOpGen o)
    (hGDc : GDSupply E W hP hC hA GenDisc (Configuration.core C))
    (h : GoodConfig3 C) : GoodConfig3 C' := by
  have hcT : IsCanonicalState (Configuration.core C) (ev₁ ∩ ev₂) sT := by
    rw [← C.lca_events h_lca h_ver₁ h_ver₂ h_verT]
    exact h.canonical vT sT evT h_verT
  have hcl₁f : fullClosureRel (Configuration.core C).vis ev₁ :=
    fun a b hab hb => h.ver_causal v₁ s₁ ev₁ h_ver₁ a b hab hb
  have hcl₂f : fullClosureRel (Configuration.core C).vis ev₂ :=
    fun a b hab hb => h.ver_causal v₂ s₂ ev₂ h_ver₂ a b hab hb
  have hsub₁ : ∀ a ∈ ev₁, a ∈ (Configuration.core C).events :=
    h.ver_events_sub v₁ s₁ ev₁ h_ver₁
  have hsub₂ : ∀ a ∈ ev₂, a ∈ (Configuration.core C).events :=
    h.ver_events_sub v₂ s₂ ev₂ h_ver₂
  have hclU : fullClosureRel (Configuration.core C).vis (ev₁ ∪ ev₂) :=
    fun a b hab hb => Or.elim hb
      (fun h' => Or.inl (hcl₁f a b hab h')) (fun h' => Or.inr (hcl₂f a b hab h'))
  have hsubU : ∀ a ∈ ev₁ ∪ ev₂, a ∈ (Configuration.core C).events :=
    fun a ha => Or.elim ha (hsub₁ a) (hsub₂ a)
  have h_merged := joinC_quotient E W hP hC hA WfOpGen hWFR GenDisc hJoinEq
    (Configuration.core C) ev₁ ev₂ sT s₁ s₂
    (fun hab hbc => h.vis_trans hab hbc)
    (fun a ha => h.vis_irrefl a ha)
    hsub₁ hsub₂
    ⟨hcl₁f, fun o ho => hGenC o (hsub₁ o ho)⟩
    ⟨hcl₂f, fun o ho => hGenC o (hsub₂ o ho)⟩
    (hGDc (Configuration.core C).vis ev₁ (fun _ _ _ _ => Iff.rfl) hcl₁f hsub₁)
    (hGDc (Configuration.core C).vis ev₂ (fun _ _ _ _ => Iff.rfl) hcl₂f hsub₂)
    (hGDc (Configuration.core C).vis (ev₁ ∪ ev₂) (fun _ _ _ _ => Iff.rfl) hclU hsubU)
    hcT (h.canonical v₁ s₁ ev₁ h_ver₁) (h.canonical v₂ s₂ ev₂ h_ver₂)
  exact goodConfig3_merge_of_canonical h_head₁ h_ver₁ h_ver₂ hL hvis hver h h_merged

open LabeledTS in
/-- **`GoodConfig3` re-derived from reachability under the conditioned Join.**
Threads TWO honest-execution conditions on the events, monotone along the trace:
`∀ o ∈ C.events, WfOpGen o` (per-event, via `events_mono_of_step`) and the
config-relative generation discipline `GDSupply` (per-delivered-set). The
predecessor's `GDSupply` is rebuilt from the successor's using
`vis_agree_of_step`: a step's new `vis` edges only reach the fresh event, so on
any `ev ⊆` the predecessor's events the two `vis` agree, and the agreement clause
of `GDSupply` absorbs exactly this. Neither premise is execution-guaranteed
generically (the RGA supplies both from its generation invariants), so both are
hypotheses. The merge step feeds both to `goodConfig3_merge_wfgen`. -/
theorem goodConfig3_of_reachF_wfgen
    (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (WfOpGen : Op D.AppOp → Prop) (hWFR : WfOpReachable D W WfOpGen)
    (GenDisc : (Op D.AppOp → Op D.AppOp → Prop) → Set (Op D.AppOp) → Prop)
    (hJoinEq : EqJoinLemma3C D E W GenDisc)
    (C : Configuration (QSig E W hP hC hA))
    (hReach : (labeledTS3 (QSig E W hP hC hA)).ReachableFrom
        (initConfig (QSig E W hP hC hA) trivial) C)
    (hGenC : ∀ o ∈ (Configuration.core C).events, WfOpGen o)
    (hGDc : GDSupply E W hP hC hA GenDisc (Configuration.core C)) :
    GoodConfig3 C := by
  revert hGenC hGDc
  induction hReach with
  | refl => intro _ _; exact goodConfig3_init trivial
  | tail _ hs ih =>
    intro hGenc hGDcurr
    obtain ⟨ℓ, hstep⟩ := hs
    have hmono := events_mono_of_step hstep
    have hvagree := vis_agree_of_step hstep
    -- The predecessor inherits both discipline premises (events monotone;
    -- `GDSupply` moved back across the step via `vis`-agreement on delivered sets).
    have hGDpred : GDSupply E W hP hC hA GenDisc (Configuration.core _) :=
      fun vis ev hag hcl hsub =>
        hGDcurr vis ev
          (fun a x ha hx => (hag a x ha hx).trans (hvagree a x (hsub a ha) (hsub x hx)))
          hcl (fun a ha => hmono a (hsub a ha))
    cases hstep with
    | createReplica h_fresh C' hN hL hvis hver hhead hparents =>
      exact goodConfig3_createReplica h_fresh hL hvis hver
        (ih (fun o ho => hGenc o (hmono o ho)) hGDpred)
    | apply h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank C'
        hN hL hvis hver hhead hparents =>
      exact goodConfig3_apply h_head h_ver h_fresh_t h_vnew hL hvis hver
        (ih (fun o ho => hGenc o (hmono o ho)) hGDpred)
    | merge h_head₁ h_head₂ h_ver₁ h_ver₂ h_lca h_verT h_vm h_rank₁
        h_rank₂ C' hN hL hvis hver hhead hparents =>
      exact goodConfig3_merge_wfgen E W hP hC hA WfOpGen hWFR GenDisc hJoinEq
        h_head₁ h_ver₁ h_ver₂ h_lca h_verT hL hvis hver
        (fun o ho => hGenc o (hmono o ho)) hGDpred
        (ih (fun o ho => hGenc o (hmono o ho)) hGDpred)
    | query h_s h_val => exact ih (fun o ho => hGenc o (hmono o ho)) hGDpred

/-- **`RA_linearizable_up_to_eq`** — THE generic conditioned metatheorem.
A `ConditionedMRDTSig` `D` supplying the `≈`-route VCs — `EqEquiv`, `InvPres`,
`CongVC`, `InvInvVC`, `WfOpReachable D W WfOpGen` (now carrying the per-event
generation-wellformedness premise), and `EqJoinLemma3C` — makes its quotient
signature `QSig` per-version RA-linearizable on every reachable configuration
whose events are all `WfOpGen`. The last hypothesis `hGenC` is the HONEST
execution condition: the reachable config's events were generated sensibly (the
RGA discharges it via `wfOpGen_ins`/`wfOpGen_del_live`). It CANNOT be dropped —
`WfOpReachable` is unsatisfiable without it (`rga_wfOpReachable_false`) — and it
is scoped to the config's events (a global `∀ o, WfOpGen o` would be false for the
RGA, making the theorem vacuous). Proof: `goodConfig3_of_reachF_wfgen` then
`isRALinearizable3_of_good`. -/
theorem RA_linearizable_up_to_eq
    (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (WfOpGen : Op D.AppOp → Prop) (hWFR : WfOpReachable D W WfOpGen)
    (GenDisc : (Op D.AppOp → Op D.AppOp → Prop) → Set (Op D.AppOp) → Prop)
    (hJoinEq : EqJoinLemma3C D E W GenDisc)
    (C : Configuration (QSig E W hP hC hA))
    (hReach : (labeledTS3 (QSig E W hP hC hA)).ReachableFrom
        (initConfig (QSig E W hP hC hA) trivial) C)
    (hGenC : ∀ o ∈ (Configuration.core C).events, WfOpGen o)
    (hGenDisc : GDSupply E W hP hC hA GenDisc (Configuration.core C)) :
    IsRALinearizable3 C :=
  isRALinearizable3_of_good
    (goodConfig3_of_reachF_wfgen E W hP hC hA WfOpGen hWFR GenDisc
      hJoinEq C hReach hGenC hGenDisc)

/-- **Readback — the "up to `≈`" content, over the RAW fold.** For a reachable
`QSig`-configuration, a version whose registered state is the class of a concrete
`D`-state `σ` admits an enumeration `π` of its event set that respects the
`≈`-conditioned linearization order (`loEq`) and, folded from `D.init` by the RAW
`applySeq` (`π.foldl D.update`, matching the RGA's `applySeqR`), lands `≈`-equal
to `σ`. Per-version RA-linearizability *up to observational `≈`*, over the
datatype's REAL raw update. The quotient's internal `doW`-guard is discharged
here (`applySeqW = applySeq`) via `WfOpReachable`, fed by the version's
timestamp-distinctness (`GoodConfig3.ver_events_sub` + the config's
`timestamps_distinct`). -/
theorem RA_linearizable_up_to_eq_readback
    (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (WfOpGen : Op D.AppOp → Prop) (hWFR : WfOpReachable D W WfOpGen)
    (GenDisc : (Op D.AppOp → Op D.AppOp → Prop) → Set (Op D.AppOp) → Prop)
    (hJoinEq : EqJoinLemma3C D E W GenDisc)
    (C : Configuration (QSig E W hP hC hA))
    (hReach : (labeledTS3 (QSig E W hP hC hA)).ReachableFrom
        (initConfig (QSig E W hP hC hA) trivial) C)
    (hGenC : ∀ o ∈ (Configuration.core C).events, WfOpGen o)
    (hGenDisc : GDSupply E W hP hC hA GenDisc (Configuration.core C))
    (v : Version) (σ : D.State) (hσ : D.Inv σ) (Ev : Set (Op D.AppOp))
    (hver : C.ver v = some (qmk E σ hσ, Ev)) :
    ∃ π : List (Op D.AppOp),
      listPermOf π Ev ∧
      respects π (loEq E W (Configuration.core C).vis) ∧
      E.eqv (applySeq D.toCRDTSig D.init π) σ := by
  have hgood :=
    goodConfig3_of_reachF_wfgen E W hP hC hA WfOpGen hWFR GenDisc
      hJoinEq C hReach hGenC hGenDisc
  obtain ⟨π, hperm, hresp, hfold⟩ :=
    isRALinearizable3_of_good hgood v (qmk E σ hσ) Ev hver
  have hsub : ∀ a ∈ Ev, a ∈ (Configuration.core C).events :=
    hgood.ver_events_sub v (qmk E σ hσ) Ev hver
  have hGenEv : ∀ o ∈ Ev, WfOpGen o := fun o ho => hGenC o (hsub o ho)
  have heq : applySeqW D W D.init π = applySeq D.toCRDTSig D.init π :=
    applySeqW_eq_applySeq_of_wfChain
      (hWFR π hperm.1 (distinct_ts_of_perm (Configuration.core C) hsub hperm)
        (fun o ho => hGenEv o ((hperm.2 o).mp ho)))
  refine ⟨π, hperm, ?_, ?_⟩
  · exact (respects_congr (lo_qsig_iff E W hP hC hA (Configuration.core C))).mp hresp
  · rw [qapplySeq_init E W hP hC hA π] at hfold
    have hev := (qmk_eq_iff E).mp hfold
    rw [heq] at hev
    exact hev

/-! ## §5. `WfOp`-conditioning audit (option 2)

`Step3.apply` (`LCA_Lemma.lean:451`) applies the RAW `D.update s (t,r,o)` with NO
`applicable` precondition — its guard is timestamp FRESHNESS (`h_fresh_t` /
`h_fresh_store`), not applicability. So the guarantee the execution model provides
for each applied event is a WEAKER *well-formedness* `W` (`WfOp`), not
`applicable`. Conditioning `InvPres.inv_update` on `applicable` (the previous
design) therefore over-restricted the update and DISTORTED the metatheorem: its
guarded fold skipped `applicable`-but-fresh ops that the runtime DOES apply.

Option 2 fixes this by conditioning on `W` and characterizing the REAL raw update:

* `InvPres.inv_update` is `W`-conditioned (`Inv s → W o s → Inv (update s o)`) —
  weaker premise, and matched by the RGA's `rgaInv_doOp_fresh`.
* `W` is datatype-SPECIFIC (RGA: `id ≠ 0 ∧ Ins-freshness ∧ Del-resolve ≠ x`); the
  `Ins` part comes from Step3 freshness, the `Del` part from the RGA's own
  `id_mono`/path structure. So `W` is NOT extracted generically from the execution
  model — the datatype DECLARES it and discharges `WfOpReachable D W` (distinct
  timestamps ⟹ `W` at every fold prefix), which the transfer consumes to seat each
  raw fold step.
* **The one guard that survives is a TOTALITY device, not a semantic choice.**
  `ConditionedMRDTSig.update : State → Op → State` is total and `applySeq` folds it
  unconditionally, so `qdo` must be a total map into the `Inv`-subtype quotient;
  with raw `update` that needs `Inv (update s o)`, i.e. `W o s`, a
  reachability-level fact a signature field cannot see. Hence `qdo` keeps the
  `¬W`-identity fallback `doW`. But `doW` is transparent on every reachable fold
  (`WfOpReachable` gives `W` at each prefix), so `applySeqW = applySeq` there, and
  `IsCanonicalStateEq`/`EqJoinLemma3C`/the readback are stated over the RAW
  `applySeq D.toCRDTSig D.init π` (= `π.foldl D.update`, matching the RGA's
  `applySeqR`). The distinctness that fires `WfOpReachable` is read off the
  configuration (`Configuration.timestamps_distinct` + `GoodConfig3.ver_events_sub`,
  re-derived from reachability by `goodConfig3_of_reachF`).

**Verdict.** `W`/`WfOpReachable` is the load-bearing content — the datatype-VC
route (freshness alone is insufficient because of the `Del` part). The guard is
now the correct `W`-guard, forced only by totality and provably transparent on the
execution model's domain. `inv_mergeL` stays unconditional (RGA's `qInv`/`id_mono`,
`RGA_VCPackage.rga_inv_mergeL_of_idmono`). The metatheorem's conclusion
(`IsRALinearizable3`) is unchanged; its readback is over the datatype's REAL raw
update. -/

#print axioms RA_linearizable_up_to_eq
#print axioms joinC_quotient
#print axioms RA_linearizable_up_to_eq_readback
#print axioms QSig

end GenericEqQuotient
end Sal.ConditionedMRDTs
