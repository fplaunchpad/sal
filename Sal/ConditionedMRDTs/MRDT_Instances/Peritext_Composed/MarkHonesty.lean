import Sal.ConditionedMRDTs.MRDT_Instances.Peritext_Composed.Peritext_Composed

/-!
# Peritext gap 1 — does the honesty contract compose across a read-coupled boundary?

The composite `Peritext_Composed := RGA_TF ⊗ MarkStore` proves convergence and safety
(`peritextComposed_ra_linearizable_up_to_eq`) under a premise
(`PeritextHonestDelivery`) that constrains **character** operations only —
mark operations are entirely unguarded. The RGA's discipline is *born
accuracy*: a character op's recorded ancestor path is the true chain in the
RGA state at issue. Marks carry the analogous data — each endpoint is a
character id plus its recorded path — but the composite assumes nothing about
it. This file asks whether that discipline **composes**: can the honesty
contract be strengthened with a mark-side accuracy clause, and does the
strengthening go through the product machinery?

## The finding

**Yes — honesty composes, but through the *free-standing premise*, not the
product signature; and for a component whose convergence is unconditional it
is decorative for linearizability and load-bearing only for the read layer.**
Three facts, each mechanized below:

1. **Structural: the signature cannot express it, the premise can.** The
   product signature's `applicable` is *componentwise*
   (`applicable⊗ (inr o) s = applicable₂ o s.2`), so a mark guard structurally
   cannot read the character component — a cross-reading guard is not an
   instance of the clean product. But `PeritextHonestDelivery` is a bespoke
   `Prop` over the product LTS (`Supplies.lean`), exactly as the RGA's own
   born-accuracy is (it reads a causal fold of the `inl` fragment, not the
   signature's `applicable`). So the coupling lives where memo §3.4 said it
   could: in the premise. `MarkAccurate` (below) reads the character
   component of the mark op's causal-past fold freely.

2. **Well-formed on the quotient.** `MarkAccurate` reads only `contains`/`anc`
   of the RGA component, which the RGA's observational `≈₁` fixes, so it
   respects `≈₁ × Eq` (`markAccurate_congr₁`). It is therefore a legitimate
   predicate on the quotiented state the capstone speaks about — the
   composition is structurally sound, not a quotient violation.

3. **Decorative for linearizability, load-bearing for the read.** The
   strengthened contract still yields the capstone
   (`peritextComposed_ra_linearizable_honest`) — because the linearizability proof
   consumes only the *character* clause: marks are an OR-set and converge and
   linearize regardless of path accuracy. So the mark clause is an *unused*
   hypothesis for linearizability, exactly as the FWW register's unset-check
   and BudgetCart's rem-observed check are decorative for their capstones.
   Where it becomes load-bearing is the read layer: `endpointAccurate_resolve`
   shows that at an accurate state resolution lands on the recorded character
   itself — the seed of the render-intent theorems (gap 2, `#55`), which is
   where mark-anchor honesty pays for itself.

The general lesson, lifting the FWW/BudgetCart taxonomy to the compositional
setting: **a component's honesty discipline is load-bearing exactly where the
coupled read depends on it, not where convergence does** — and the read-coupled
boundary carries honesty precisely because the honesty predicate is free of
the signature's componentwise `applicable`.
-/

set_option maxHeartbeats 1000000

open Classical

namespace Sal.ConditionedMRDTs.Peritext_Composed

open Sal.Emulation
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.GoodConfig3H
open Sal.ConditionedMRDTs.ProductEq
open Sal.ConditionedMRDTs (Configuration Version Step3 Label3 initConfig labeledTS3
  prodSig inlOp evRes₁)
open Sal.ConditionedMRDTs.RGAInstance (RGACondSig' rgaEqEquiv' WfOpA rgaInvPresA
  rgaCongVC' rgaInvInvVCA)
open RGAMergeLinearization (applySeqR)

local notation "PQD" => Sal.ConditionedMRDTs.ProductEq.prodQSig
  rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA markInvT
local notation "PCfg" => Sal.ConditionedMRDTs.Configuration
  (Sal.ConditionedMRDTs.ProductEq.prodQSig
    rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA markInvT)
local notation "PReach" => LabeledTS.ReachableFrom
  (Sal.ConditionedMRDTs.labeledTS3 (Sal.ConditionedMRDTs.ProductEq.prodQSig
    rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA markInvT))
  (Sal.ConditionedMRDTs.initConfig (Sal.ConditionedMRDTs.ProductEq.prodQSig
    rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA markInvT) trivial)

/-! ## §1  Mark-anchor accuracy -/

/-- A mark endpoint `(char, path)` is **accurate** in RGA state `σ` when it is
the RGA's own born-accuracy shape read for that endpoint: either the degenerate
root endpoint, or `char` is live and `path` is its true ancestor chain
(`IsAncPath`). This is `accurate` (`RGA_Tombstone_Free_MRDT.lean:319`)
specialized to a `(leaf, path)` pair. -/
def EndpointAccurate (σ : concrete_st) (ep : ℕ × List ℕ) : Prop :=
  (ep.1 = 0 ∧ ep.2 = []) ∨
  (contains σ ep.1 = true ∧ IsAncPath σ ep.1 ep.2)

/-- A mark record is **anchor-accurate** in `σ` when both its endpoints are:
the recorded start/end character ids and paths are the true chains in the RGA
component at issue. The mark-side analogue of the RGA's born accuracy. -/
def MarkAccurate (σ : concrete_st) (m : MarkPayload) : Prop :=
  EndpointAccurate σ m.2.2.1 ∧ EndpointAccurate σ m.2.2.2

/-! ## §2  Well-formedness: `MarkAccurate` respects the RGA's `≈` -/

/-- `IsAncPath` reads only `contains`/`anc`, which the framework's `eq` fixes
on live ids — so it transfers across `≈₁`-related RGA states. -/
theorem isAncPath_congr {σ σ' : concrete_st} (h : eq σ σ') :
    ∀ (leaf : ℕ) (path : List ℕ), contains σ leaf = true →
      (IsAncPath σ leaf path ↔ IsAncPath σ' leaf path) := by
  intro leaf path
  induction path generalizing leaf with
  | nil =>
    intro hlive
    have hanc : anc σ leaf = anc σ' leaf := congrArg Prod.snd ((h leaf).2 hlive)
    show (anc σ leaf = 0) ↔ (anc σ' leaf = 0)
    rw [hanc]
  | cons p ps ih =>
    intro hlive
    have hanc : anc σ leaf = anc σ' leaf := congrArg Prod.snd ((h leaf).2 hlive)
    have hcp : contains σ p = contains σ' p := (h p).1
    show (anc σ leaf = p ∧ contains σ p = true ∧ IsAncPath σ p ps)
       ↔ (anc σ' leaf = p ∧ contains σ' p = true ∧ IsAncPath σ' p ps)
    rw [hanc, hcp]
    refine and_congr_right (fun _ => and_congr_right (fun hp2 => ?_))
    exact ih p (by rw [hcp]; exact hp2)

theorem endpointAccurate_congr₁ {σ σ' : concrete_st} (h : eq σ σ')
    (ep : ℕ × List ℕ) : EndpointAccurate σ ep ↔ EndpointAccurate σ' ep := by
  unfold EndpointAccurate
  by_cases hz : ep.1 = 0 ∧ ep.2 = []
  · simp [hz]
  · have hcc : contains σ ep.1 = contains σ' ep.1 := (h ep.1).1
    constructor
    · rintro (hd | ⟨hl, hp⟩)
      · exact absurd hd hz
      · exact Or.inr ⟨by rw [← hcc]; exact hl, (isAncPath_congr h ep.1 ep.2 hl).mp hp⟩
    · rintro (hd | ⟨hl, hp⟩)
      · exact absurd hd hz
      · have hl₁ : contains σ ep.1 = true := by rw [hcc]; exact hl
        exact Or.inr ⟨hl₁, (isAncPath_congr h ep.1 ep.2 hl₁).mpr hp⟩

/-- **`MarkAccurate` respects the RGA's observational `≈`**: it reads only the
character component's `contains`/`anc`, which `≈₁` fixes. Hence it is a
well-defined honesty predicate on the quotient the capstone speaks about —
the read-coupled honesty clause does not violate the quotient. -/
theorem markAccurate_congr₁ {σ σ' : concrete_st} (h : eq σ σ')
    (m : MarkPayload) : MarkAccurate σ m ↔ MarkAccurate σ' m :=
  and_congr (endpointAccurate_congr₁ h m.2.2.1) (endpointAccurate_congr₁ h m.2.2.2)

/-! ## §3  The strengthened contract, and that the capstone survives it -/

/-- The honest-delivery contract **strengthened with mark-anchor accuracy**:
`PeritextHonestDelivery` (character born accuracy + applicable delivery) *and*
that every delivered mark record is `MarkAccurate` against a causal fold of
the RGA fragment of the head version's events — the exact mirror of the
character clause, now on the `inr` (mark-add) steps the base contract leaves
free. The removal ops (`OSOp.rem`) carry no record, so they are unconstrained.

Stated as a conjunction so that `→ PeritextHonestDelivery` is immediate: this
is what makes the strengthening *compose* — the base capstone consumes the
first conjunct and is blind to the second. -/
def PeritextHonestDeliveryPlus : Prop :=
  PeritextHonestDelivery ∧
  ∀ {C₀ C₁ : PCfg} {t : Timestamp} {r : Replica} {rec : MarkPayload}
    {v : Version}
    {sh : QState (prodSig RGACondSig' MarkStore) (prodEqEquiv rgaEqEquiv')}
    {evh : Set POp},
    PReach C₀ →
    Step3 PQD C₀ (Label3.apply t r (Sum.inr (OSOp.add rec))) C₁ →
    C₀.head r = some v → C₀.ver v = some (sh, evh) →
    ∃ π : List op_t, listPermOf π (evRes₁ evh) ∧
      respects π (fun a b : op_t => C₀.vis (inlOp a) (inlOp b)) ∧
      MarkAccurate (applySeqR init_st π) rec

/-- The strengthening implies the base contract (first projection). -/
theorem honestDeliveryPlus_imp (h : PeritextHonestDeliveryPlus) :
    PeritextHonestDelivery := h.1

/-- **The composition theorem for honesty.** The cross-component
mark-anchor-accuracy strengthening is a *valid premise*: the composite capstone
holds under it, unchanged. Its proof consumes only the character clause
(`h.1`) — marks converge and linearize as an OR-set regardless of path
accuracy — so the mark clause rides along, decorative for linearizability and
reserved for the read-layer intent theorems (gap 2). This is honesty composing
across the read-coupled (L2) boundary. -/
theorem peritextComposed_ra_linearizable_honest
    (hHD : PeritextHonestDeliveryPlus)
    (C : Configuration PQD)
    (hReach : (labeledTS3 PQD).ReachableFrom (initConfig PQD trivial) C) :
    IsRALinearizable3Eq (prodEqEquiv (D₂ := MarkStore) rgaEqEquiv')
      (prodW (D₂ := MarkStore) WfOpA)
      (prodInvPres (D₁ := RGACondSig') (D₂ := MarkStore) WfOpA rgaInvPresA markInvT)
      (prodCongVC (D₂ := MarkStore) rgaEqEquiv' rgaCongVC')
      (prodInvInvVC (D₂ := MarkStore) rgaEqEquiv' WfOpA rgaInvInvVCA) C :=
  peritextComposed_ra_linearizable_up_to_eq (honestDeliveryPlus_imp hHD) C hReach

/-! ## §4  Where accuracy is load-bearing: the read-layer seed

The mark clause buys nothing for linearizability; it buys the read layer. At
an **accurate** state, an endpoint resolves to the recorded character itself —
`resolve` short-circuits on the live endpoint before ever consulting the
recorded path. This is the base case the render-intent theorems (gap 2) will
propagate through reachability: accuracy at issue pins resolution, and honest
delivery carries it to read time. -/

/-- At an accurate state, resolving a live endpoint returns the recorded
character (`resolve` short-circuits). The seed of render intent. -/
theorem endpointAccurate_resolve {σ : concrete_st} {ep : ℕ × List ℕ}
    (hlive : contains σ ep.1 = true) :
    resolve σ (ep.1 :: ep.2) = ep.1 := by
  simp only [resolve, hlive, if_true]

/-- Consequently, at a state where both endpoints of an anchor-accurate mark
are live, the mark renders to its recorded endpoints exactly — no rehoming has
happened yet. (The non-degenerate branch of `MarkAccurate` gives liveness.) -/
theorem markAccurate_resolveMark {σ : concrete_st} {m : MarkPayload}
    (hs : contains σ m.2.2.1.1 = true) (he : contains σ m.2.2.2.1 = true) :
    resolveMark σ m = (m.1, m.2.1, m.2.2.1.1, m.2.2.2.1) := by
  unfold resolveMark
  rw [endpointAccurate_resolve (ep := m.2.2.1) hs,
      endpointAccurate_resolve (ep := m.2.2.2) he]

/-! ## Axiom audit -/

#print axioms peritextComposed_ra_linearizable_honest
#print axioms markAccurate_congr₁
#print axioms markAccurate_resolveMark

end Sal.ConditionedMRDTs.Peritext_Composed
