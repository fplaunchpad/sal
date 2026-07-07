import Sal.MRDTs.Metatheory.Development.RGA_hCanon_Glue
import Sal.MRDTs.Metatheory.Conditioned.Base.CRDT_Signature
import Sal.MRDTs.Metatheory.Conditioned.Base.CRDT_TS
import Sal.MRDTs.Metatheory.Conditioned.Base.Labeled_TS
import Sal.MRDTs.Metatheory.Conditioned.BornApplicable_Guard
import Sal.MRDTs.Metatheory.Conditioned.G2_Transport_Probe
import Sal.MRDTs.Metatheory.Conditioned.GenericEqQuotient
import Sal.MRDTs.Metatheory.Conditioned.RGA_CanonConvergence
import Sal.MRDTs.Metatheory.Conditioned.RGA_ChainFaithful_doDel
import Sal.MRDTs.Metatheory.Conditioned.RGA_ConditionedConvergence
import Sal.MRDTs.Metatheory.Conditioned.RGA_EqQuotient
import Sal.MRDTs.Metatheory.Conditioned.RGA_Instance
import Sal.MRDTs.Metatheory.Conditioned.RGA_InvUpdateQ
import Sal.MRDTs.Metatheory.Conditioned.RGA_MergeFoldChain
import Sal.MRDTs.Metatheory.Conditioned.RGA_MergeLinearization
import Sal.MRDTs.Metatheory.Conditioned.RGA_WfOpA_VCs
import Sal.MRDTs.Metatheory.Conditioned.UpdateFeasibility_Gate
import Sal.MRDTs.Metatheory.Development.RGA_CanonMatch_Reachable
import Sal.MRDTs.Metatheory.Development.RGA_EndToEnd
import Sal.MRDTs.Metatheory.Development.RGA_NoopFeasible_CanonFold

/-!
# The RGA end-to-end SKELETON — pushed to the precise leaf set, wired to `IsRALinearizable3`

*Additive; modifies no existing file; 0 `sorry`.*

Skeleton-first discipline (KC): admit the residual as EXPLICIT named hypotheses, wire the whole chain
to the UNCONDITIONAL conclusion `IsRALinearizable3 C`, verify it typechecks kernel-clean (the admitted
leaves are ordinary hypotheses, NOT `sorry`), and only THEN discharge. The point is to lock every type
now so discharge cannot hit a type mismatch.

The chain already had: `rga_RA_linearizable_end_to_end` (gated on `hEnum` + `hCanon`) ←
`hCanon_of_leaves` (reduces `hCanon` to `hFoldCanon` + `hMergeInputs`) ← `canonMatch_merge_of_inputs`
(merge glue) and `canonMatch_reachable_of_facts` (the generic fold engine). What is added here:

* `EngineReady events E ρ` — the exact input the fold engine consumes for ONE fold: `E ⊆ events`,
  `listPermOf ρ E`, born-applicability (`noopFeasible ρ init_st`), and a reference order `R` witnessing
  `RefEdge`/`respects` plus the generation discipline (`hids0`/`hgen`).
* `canonMatch_of_engineReady` — `EngineReady` ⟹ `CanonMatch ρ (applySeqR init_st ρ)`; the sole place
  the `RGACondSig'`⇄`RGACondSig` `noopFeasible` transport and the `E ⊆ events` `hdts`-restriction live.
* `hFoldCanon_of_engineReady` — **bridge #1**, LOCKED: the four `EngineReady` folds ⟹ `hFoldCanon`'s
  exact four-`CanonMatch` shape (the union fold via `applySeqR_append`). This is where an engine→shape
  type mismatch would surface; it does not.
* `rga_RA_linearizable_skeleton` — the capstone: `hEnum` + `hReady` (4× `EngineReady`) + `hMergeInputs`
  (merge atoms) + the honest-execution premises ⟹ `IsRALinearizable3 C`, kernel-clean, 0 `sorry`.

Residual after this file (all as named hypotheses, to discharge next):
* `hEnum` — the δ-enum (generic born-applicable delivery; framework's job).
* `hReady` — per-fold `{perm, born-applicability, RefEdge, respects, hids0, hgen}` (the reachability
  plumbing: perms/born-applicability flow from `hEnum`'s context, `RefEdge`/`respects`/`hids0`/`hgen`
  from the framework's Lamport-clock `causal_mono`/`distinct_ts` + `WfOpGenQ`).
* `hMergeInputs` — σ-forest invariants + per-id causal set-algebra + per-survivor membership + the
  per-survivor `CanonBirthBridge` (`hbridge`; further reduced to the four carriers by the already-typed
  `RGABirthBridge.canonBirthBridge_per_survivor`, whose only deep sub-residual is `BranchInv`-I4).
-/

set_option maxHeartbeats 1000000

open Classical

namespace Sal.Metatheory.RGASkeleton

open Sal.Emulation
open Sal.Metatheory.GenericEqQuotient
open Sal.Metatheory.RGAInstance (RGACondSig' rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)
open Sal.Metatheory.UpdateFeasibilityGate (noopFeasible)
open RGAMergeLinearization (applySeqR)
open RGACanonConvergence (CanonMatch survP insertedIn deletedIn)
open RGAMergeFoldChain (CanonBirthBridge)
open Sal.Metatheory.RGAInvUpdateQ (WfOpGenQ)
open Sal.Metatheory.G2Probe (RGACondSig)
open Sal.Metatheory.RGANoopFeasible (RefEdge)
open Sal.Metatheory.RGAConditionedConvergence (applySeqR_append)
open Sal.Metatheory.RGACanonMatchReachable (canonMatch_reachable_of_facts)
open Sal.Metatheory.RGAEndToEnd (hCanon_of_leaves rga_RA_linearizable_end_to_end)

/-- **`noopFeasible` is signature-`Inv`-independent.**  `RGACondSig'` and `G2Probe.RGACondSig` share
`toMRDTSig := RGAM` and the same `applicable`; they differ only in `Inv`, which `noopFeasible` never
reads. For a variable list both sides are stuck, so — exactly like `RGA_Instance.wfChain_transport` —
this one-line induction makes the transport explicit. -/
theorem noopFeasible_transport (ρ : List op_t) (s : concrete_st) :
    noopFeasible RGACondSig' ρ s = noopFeasible RGACondSig ρ s := by
  induction ρ generalizing s with
  | nil => rfl
  | cons o ρ ih =>
    have e1 : RGACondSig'.update s o = RGACondSig.update s o := rfl
    have e2 : RGACondSig'.applicable o s = RGACondSig.applicable o s := rfl
    show ((RGACondSig'.applicable o s ∨ RGACondSig'.update s o = s)
          ∧ noopFeasible RGACondSig' ρ (RGACondSig'.update s o))
       = ((RGACondSig.applicable o s ∨ RGACondSig.update s o = s)
          ∧ noopFeasible RGACondSig ρ (RGACondSig.update s o))
    rw [e1, e2, ih (RGACondSig.update s o)]

/-- **Engine-ready fold.**  Exactly what the generic canonical-fold engine consumes for one fold `ρ`
of the event set `E ⊆ events`: `ρ` enumerates `E`, `ρ` is born-applicable from `init_st`, and there is
a reference order `R` under which `E`'s references become order edges (`RefEdge`) that `ρ` respects,
together with the generation discipline (nonzero ids, `WfOpGenQ`). Born-applicability is stated at the
source signature `RGACondSig'`; the engine's `RGACondSig` view is reached by `noopFeasible_transport`. -/
def EngineReady (events E : Set op_t) (ρ : List op_t) : Prop :=
  E ⊆ events ∧
  listPermOf ρ E ∧
  noopFeasible RGACondSig' ρ init_st ∧
  ∃ R : op_t → op_t → Prop,
    (∀ o ∈ E, o.1 ≠ 0) ∧ (∀ o ∈ E, WfOpGenQ o) ∧ RefEdge E R ∧ respects ρ R

/-- **`EngineReady` ⟹ `CanonMatch`.**  Feeds the packaged fold engine
`RGACanonMatchReachable.canonMatch_reachable_of_facts`. The only glue: restrict the framework's
`events`-level id-distinctness to `E` (via `E ⊆ events`) and transport `noopFeasible` across the two
signatures. -/
theorem canonMatch_of_engineReady
    (events E : Set op_t) (ρ : List op_t)
    (hdtsEv : ∀ a b : op_t, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1)
    (h : EngineReady events E ρ) :
    CanonMatch ρ (applySeqR init_st ρ) := by
  obtain ⟨hsub, hperm, hnf, R, hids0, hgen, href, hresp⟩ := h
  have hdtsE : ∀ a b : op_t, a ∈ E → b ∈ E → a ≠ b → a.1 ≠ b.1 :=
    fun a b ha hb hne => hdtsEv a b (hsub ha) (hsub hb) hne
  have hnf' : noopFeasible RGACondSig ρ init_st := (noopFeasible_transport ρ init_st) ▸ hnf
  exact canonMatch_reachable_of_facts E R ρ hdtsE hids0 hgen href hperm hresp hnf'

/-- **Bridge #1 — LOCKED.**  The four engine-ready folds (`ρ₀` over `ev₁∩ev₂`, `ρ₁` over `ev₁`, `ρ₂`
over `ev₂`, `ρ₀++π₀` over `ev₁∪ev₂`) assemble into exactly `hFoldCanon`'s four-`CanonMatch` shape that
`hCanon_of_leaves` consumes. The union fold's state `applySeqR (applySeqR init_st ρ₀) π₀` is reached
from the engine's `applySeqR init_st (ρ₀++π₀)` by `applySeqR_append`. -/
theorem hFoldCanon_of_engineReady
    (hReady : ∀ (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t) (ρ₀ ρ₁ ρ₂ π₀ : List op_t),
        (∀ {a b c : op_t}, vis a b → vis b c → vis a c) → (∀ a : op_t, ¬ vis a a) →
        (∀ a b : op_t, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1) →
        (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
        fullClosureRel (D := RGACondSig') vis ev₁ → fullClosureRel (D := RGACondSig') vis ev₂ →
        listPermOf ρ₀ (ev₁ ∩ ev₂) → listPermOf ρ₁ ev₁ → listPermOf ρ₂ ev₂ →
        listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) →
        respects π₀ (loOnEq rgaEqEquiv' WfOpA vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) →
        noopFeasible RGACondSig' π₀ (applySeqR init_st ρ₀) →
        EngineReady events (ev₁ ∩ ev₂) ρ₀ ∧ EngineReady events ev₁ ρ₁
          ∧ EngineReady events ev₂ ρ₂ ∧ EngineReady events (ev₁ ∪ ev₂) (ρ₀ ++ π₀)) :
    ∀ (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t) (ρ₀ ρ₁ ρ₂ π₀ : List op_t),
        (∀ {a b c : op_t}, vis a b → vis b c → vis a c) → (∀ a : op_t, ¬ vis a a) →
        (∀ a b : op_t, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1) →
        (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
        fullClosureRel (D := RGACondSig') vis ev₁ → fullClosureRel (D := RGACondSig') vis ev₂ →
        listPermOf ρ₀ (ev₁ ∩ ev₂) → listPermOf ρ₁ ev₁ → listPermOf ρ₂ ev₂ →
        listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) →
        respects π₀ (loOnEq rgaEqEquiv' WfOpA vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) →
        noopFeasible RGACondSig' π₀ (applySeqR init_st ρ₀) →
        CanonMatch ρ₀ (applySeqR init_st ρ₀) ∧ CanonMatch ρ₁ (applySeqR init_st ρ₁)
          ∧ CanonMatch ρ₂ (applySeqR init_st ρ₂)
          ∧ CanonMatch (ρ₀ ++ π₀) (applySeqR (applySeqR init_st ρ₀) π₀) := by
  intro vis events ev₁ ev₂ ρ₀ ρ₁ ρ₂ π₀ htr hir hdts hev1 hev2 hcl1 hcl2 h0p h1p h2p hπp hπr hnfπ
  obtain ⟨hr0, hr1, hr2, hru⟩ :=
    hReady vis events ev₁ ev₂ ρ₀ ρ₁ ρ₂ π₀ htr hir hdts hev1 hev2 hcl1 hcl2 h0p h1p h2p hπp hπr hnfπ
  refine ⟨canonMatch_of_engineReady events (ev₁ ∩ ev₂) ρ₀ hdts hr0,
    canonMatch_of_engineReady events ev₁ ρ₁ hdts hr1,
    canonMatch_of_engineReady events ev₂ ρ₂ hdts hr2, ?_⟩
  have hu := canonMatch_of_engineReady events (ev₁ ∪ ev₂) (ρ₀ ++ π₀) hdts hru
  have happ : applySeqR init_st (ρ₀ ++ π₀) = applySeqR (applySeqR init_st ρ₀) π₀ := by
    simp only [applySeqR, List.foldl_append]
  rw [← happ]
  exact hu

/-- **The capstone skeleton.**  RGA per-version RA-linearizability up to `≈`, plugged END-TO-END to the
unconditional `IsRALinearizable3 C`, gated on the precise named residual:

* `hEnum` — a canonical δ-enum exists (generic delivery);
* `hReady` — the four folds are engine-ready (reachability plumbing);
* `hMergeInputs` — the merge glue's leaf bundle (σ-forest invariants, per-id causal set-algebra,
  per-survivor membership, per-survivor `CanonBirthBridge`);
* `hBA`/`hReach`/`hgenW` — the honest-execution premises the metatheorem already requires.

`hFoldCanon` is DISCHARGED here from `hReady` (bridge #1); `hCanon` is assembled by `hCanon_of_leaves`;
the rest is the proved metatheorem chain. 0 `sorry`; axioms `⊆ {propext, Classical.choice, Quot.sound}`. -/
theorem rga_RA_linearizable_skeleton
    (hEnum : ∀ (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t) (ρ₀ ρ₁ ρ₂ : List op_t),
        (∀ {a b c : op_t}, vis a b → vis b c → vis a c) → (∀ a : op_t, ¬ vis a a) →
        (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
        fullClosureRel (D := RGACondSig') vis ev₁ → fullClosureRel (D := RGACondSig') vis ev₂ →
        listPermOf ρ₀ (ev₁ ∩ ev₂) → respects ρ₀ (loOnEq rgaEqEquiv' WfOpA vis (ev₁ ∩ ev₂)) →
          noopFeasible RGACondSig' ρ₀ init_st →
        listPermOf ρ₁ ev₁ → respects ρ₁ (loOnEq rgaEqEquiv' WfOpA vis ev₁) →
          noopFeasible RGACondSig' ρ₁ init_st →
        listPermOf ρ₂ ev₂ → respects ρ₂ (loOnEq rgaEqEquiv' WfOpA vis ev₂) →
          noopFeasible RGACondSig' ρ₂ init_st →
        ∃ π₀ : List op_t,
          listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) ∧
          respects π₀ (loOnEq rgaEqEquiv' WfOpA vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) ∧
          noopFeasible RGACondSig' π₀ (applySeqR init_st ρ₀))
    (hReady : ∀ (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t) (ρ₀ ρ₁ ρ₂ π₀ : List op_t),
        (∀ {a b c : op_t}, vis a b → vis b c → vis a c) → (∀ a : op_t, ¬ vis a a) →
        (∀ a b : op_t, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1) →
        (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
        fullClosureRel (D := RGACondSig') vis ev₁ → fullClosureRel (D := RGACondSig') vis ev₂ →
        listPermOf ρ₀ (ev₁ ∩ ev₂) → listPermOf ρ₁ ev₁ → listPermOf ρ₂ ev₂ →
        listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) →
        respects π₀ (loOnEq rgaEqEquiv' WfOpA vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) →
        noopFeasible RGACondSig' π₀ (applySeqR init_st ρ₀) →
        EngineReady events (ev₁ ∩ ev₂) ρ₀ ∧ EngineReady events ev₁ ρ₁
          ∧ EngineReady events ev₂ ρ₂ ∧ EngineReady events (ev₁ ∪ ev₂) (ρ₀ ++ π₀))
    (hMergeInputs : ∀ (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t) (ρ₀ ρ₁ ρ₂ π₀ : List op_t),
        (∀ {a b c : op_t}, vis a b → vis b c → vis a c) → (∀ a : op_t, ¬ vis a a) →
        (∀ a b : op_t, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1) →
        (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
        fullClosureRel (D := RGACondSig') vis ev₁ → fullClosureRel (D := RGACondSig') vis ev₂ →
        listPermOf ρ₀ (ev₁ ∩ ev₂) → listPermOf ρ₁ ev₁ → listPermOf ρ₂ ev₂ →
        listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) →
        respects π₀ (loOnEq rgaEqEquiv' WfOpA vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) →
        noopFeasible RGACondSig' π₀ (applySeqR init_st ρ₀) →
        (∀ y, contains (applySeqR init_st ρ₀) y = true → y ≠ 0 → anc (applySeqR init_st ρ₀) y < y)
        ∧ (∀ y, contains (applySeqR init_st ρ₀) y = true →
            (anc (applySeqR init_st ρ₀) y = 0 ∨ contains (applySeqR init_st ρ₀) (anc (applySeqR init_st ρ₀) y) = true))
        ∧ contains (applySeqR init_st ρ₀) 0 = false
        ∧ (∀ c, (insertedIn ρ₀ c ↔ insertedIn ρ₁ c ∧ insertedIn ρ₂ c)
            ∧ (deletedIn ρ₁ c → insertedIn ρ₁ c) ∧ (deletedIn ρ₂ c → insertedIn ρ₂ c)
            ∧ (deletedIn ρ₀ c → deletedIn ρ₁ c) ∧ (deletedIn ρ₀ c → deletedIn ρ₂ c)
            ∧ (insertedIn (ρ₀ ++ π₀) c ↔ insertedIn ρ₁ c ∨ insertedIn ρ₂ c)
            ∧ (deletedIn (ρ₀ ++ π₀) c ↔ deletedIn ρ₁ c ∨ deletedIn ρ₂ c))
        ∧ (∀ (t r e a : ℕ) (p : List ℕ),
            (t, r, .Ins e p a) ∈ ρ₀ ++ π₀ → survP (ρ₀ ++ π₀) t →
            (contains (applySeqR init_st ρ₀) t = true → (t, r, .Ins e p a) ∈ ρ₀)
            ∧ (contains (applySeqR init_st ρ₁) t = true → (t, r, .Ins e p a) ∈ ρ₁)
            ∧ (contains (applySeqR init_st ρ₂) t = true → (t, r, .Ins e p a) ∈ ρ₂)
            ∧ (contains (applySeqR init_st ρ₀) t = true ∨ contains (applySeqR init_st ρ₁) t = true
                ∨ contains (applySeqR init_st ρ₂) t = true))
        ∧ (∀ (t r e a : ℕ) (p : List ℕ),
            (t, r, .Ins e p a) ∈ ρ₀ ++ π₀ → survP (ρ₀ ++ π₀) t →
            CanonBirthBridge (applySeqR init_st ρ₀) (ρ₀ ++ π₀)
                (birthAnc (applySeqR init_st ρ₀) (applySeqR init_st ρ₁) (applySeqR init_st ρ₂) t) (a :: p)
            ∧ (birthAnc (applySeqR init_st ρ₀) (applySeqR init_st ρ₁) (applySeqR init_st ρ₂) t = 0
                ∨ survivors (applySeqR init_st ρ₀) (applySeqR init_st ρ₁) (applySeqR init_st ρ₂)
                    (birthAnc (applySeqR init_st ρ₀) (applySeqR init_st ρ₁) (applySeqR init_st ρ₂) t) = true)))
    (hBA : ∀ {C₀ C₁ : Sal.Metatheory.Configuration
        (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)}
      {t : Sal.Emulation.Timestamp} {r : Sal.Emulation.Replica} {o : app_op_t}
      {v : Sal.Metatheory.Version}
      {sh : QState RGACondSig' rgaEqEquiv'} {evh : Set (Op app_op_t)},
      (labeledTS3 (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)).ReachableFrom
        (Sal.Metatheory.initConfig
          (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA) trivial) C₀ →
      Sal.Metatheory.Step3 (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)
        C₀ (Sal.Metatheory.Label3.apply t r o) C₁ →
      C₀.head r = some v → C₀.ver v = some (sh, evh) →
      qapplicable rgaEqEquiv' WfOpA rgaInvInvVCA (t, r, o) sh ∧
        (∀ s', RGACondSig'.applicable (t, r, o) s' → WfOpA (t, r, o) s'))
    (C : Sal.Metatheory.Configuration
        (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA))
    (hReach : (labeledTS3 (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)).ReachableFrom
        (Sal.Metatheory.initConfig
          (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA) trivial) C)
    (hgenW : ∀ o ∈ (Sal.Metatheory.Configuration.core C).events,
        ∀ s', RGACondSig'.applicable o s' → WfOpA o s') :
    Sal.Metatheory.IsRALinearizable3 C :=
  rga_RA_linearizable_end_to_end hEnum
    (hCanon_of_leaves (hFoldCanon_of_engineReady hReady) hMergeInputs)
    hBA C hReach hgenW

/-! ## Axiom audit -/

#print axioms noopFeasible_transport
#print axioms canonMatch_of_engineReady
#print axioms hFoldCanon_of_engineReady
#print axioms rga_RA_linearizable_skeleton

end Sal.Metatheory.RGASkeleton
