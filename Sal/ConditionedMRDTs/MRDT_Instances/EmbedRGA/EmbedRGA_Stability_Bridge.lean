import Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA_Recoding
import Sal.ConditionedMRDTs.Metatheory.Stability_VC

/-!
# The eRecode ⇄ SettledAt bridge (task #96 stage 4, connecting #97)

The re-coding cluster (`eRecode_applySeq` and friends) is *cut-parametric*: it
takes the cut as data — a state whose coordinates the stable-prefix map
covers, and a continuation whose mints factor at the map (`MintAt`). This file
discharges the standing cut hypothesis **by `SettledAt`**, to the extent
provable today:

* `settledAt_dichotomy` — **the epoch boundary is causally sharp**: at a
  settled event set, every existing event outside it has the *whole* cut in
  its causal past. This is the class-(a)/(b) collapse for the remap species:
  there are no in-flight ops straddling a settled cut; everything beyond it
  was minted in the new epoch. (New; proved from `SettledAtOn` alone.)
* `AnchorsFactorBeyond` — the *named residue*: ops minted with the cut in
  their causal past carry anchor prefixes that factor at the stable-prefix
  map. This is the re-based-honesty obligation recorded as open in
  `EmbedRGA_Recoding.lean` §6 ("the protocol half choosing a common cut …
  it takes all-heads visibility") — deriving it needs the epoch-geometry of
  honestly minted coordinates, out of scope here.
* `eRecode_settled_bridge` — **the bridge**: at a `SettledAt` cut whose state
  the map covers, given `AnchorsFactorBeyond`, every continuation of events
  existing beyond the cut reads identically under the re-map — the remap
  species meets the stability interface's observation clause (VC-S2) with the
  gate supplied by the #96 contract instead of by bare data. `vc_step`'s
  analogue is `eUpdate_remap`, already in the cluster.

**Achieved strength, honestly**: VC-S1/S2/S3-analogues of the `StabilityVC`
interface hold for the remap species at a `SettledAt` cut, with the mint
hypothesis reduced (via the dichotomy) to `AnchorsFactorBeyond`. The **merge
clause (VC-S4) is not bridged**: `eRecode` is stated at fold/state level and
the embed RGA's merge-vs-remap congruence belongs to the deferred protocol
half, together with the discharge of `AnchorsFactorBeyond` itself.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Sal.EmbedRGA (OrderedPrefixCode)

variable {α : Type} [DecidableEq α] [Inhabited α]

/-! ## §1 The dichotomy: settled cuts are causally sharp -/

/-- **At a settled event set, everything outside it saw the whole cut**: an
existing event `e ∉ E` is concurrent with no cut member (settledness), never
below one (downward closure), so every cut member is in its causal past. -/
theorem settledAt_dichotomy {D : ConditionedMRDTSig} {C : Configuration D}
    {E S : Set (Op D.AppOp)} (hset : SettledAtOn C E S) :
    ∀ e ∈ C.events, e ∉ E → ∀ a ∈ S, C.vis a e := by
  intro e he hnotE a ha
  by_cases hae : C.vis a e
  · exact hae
  · exfalso
    by_cases hea : C.vis e a
    · exact hnotE (hset.sub (hset.down e a hea ha))
    · by_cases heq : e = a
      · exact hnotE (hset.sub (heq ▸ ha))
      · exact hnotE (hset.conc e he ⟨a, ha, heq, hea, hae⟩)

/-! ## §2 The named residue and the bridge -/

/-- **The open half, as a hypothesis with a name**: every existing op minted
with the whole cut in its causal past carries an anchor prefix that factors
at the stable-prefix map. Deriving this from honest delivery is the
re-based-honesty work recorded as open in `EmbedRGA_Recoding.lean` §6. -/
def AnchorsFactorBeyond (Γ : OrderedPrefixCode) (F : StablePrefixMap Γ)
    (C : Configuration (E Γ α)) (S : Set (Op (EOp α))) : Prop :=
  ∀ o ∈ C.events, (∀ a ∈ S, C.vis a o) →
    ∀ (e : α) (π : List Bool) (d : ℕ),
      o.2.2 = EOp.ins e π d → F.MintAt π (o.1 - d)

/-- **The bridge**: the re-coding theorem's standing cut hypothesis,
discharged by `SettledAt`. At a settled cut version `v` whose state the map
covers, any continuation of events existing *beyond* `E(v)` folds and reads
identically under the lazy translation — the mint obligation is discharged by
the dichotomy plus the named residue. -/
theorem eRecode_settled_bridge {Γ : OrderedPrefixCode}
    (F : StablePrefixMap Γ)
    {C : Configuration (E Γ α)} {v : Version} {S : Set (Op (EOp α))}
    {s : EState α} {Ev : Set (Op (EOp α))}
    (_hv : C.ver v = some (s, Ev))
    (hsettled : SettledAtOn C Ev S)
    (hAF : AnchorsFactorBeyond Γ F C S)
    (hrest : ∀ x ∈ s, F.Dom x.2.2)
    (τ : List (Op (EOp α)))
    (hτ_beyond : ∀ o ∈ τ, o ∈ C.events ∧ o ∉ Ev) :
    applySeq (E Γ α).toCRDTSig (eRemapSt F.f s) (τ.map (eRemapOp F.f))
        = eRemapSt F.f (applySeq (E Γ α).toCRDTSig s τ) ∧
      (E Γ α).query
          (applySeq (E Γ α).toCRDTSig (eRemapSt F.f s)
            (τ.map (eRemapOp F.f))) ()
        = (E Γ α).query (applySeq (E Γ α).toCRDTSig s τ) () := by
  have hτ : ∀ o ∈ τ, ∀ (e : α) (π : List Bool) (d : ℕ),
      o.2.2 = EOp.ins e π d → F.MintAt π (o.1 - d) := by
    intro o ho
    obtain ⟨hev, hnot⟩ := hτ_beyond o ho
    exact hAF o hev (settledAt_dichotomy hsettled o hev hnot)
  exact ⟨eRecode_applySeq F τ s hrest hτ,
    eRecode_reads_identical F s τ hrest hτ⟩

/-- The version-level packaging: the gate is the same `SettledAt` the OR-set
instance consumes — one frontier, three consumers (note §2). -/
theorem eRecode_settled_bridge' {Γ : OrderedPrefixCode}
    (F : StablePrefixMap Γ)
    {C : Configuration (E Γ α)} {v : Version} {S : Set (Op (EOp α))}
    (hsettled : SettledAt C v S)
    (hAF : AnchorsFactorBeyond Γ F C S) :
    ∀ {s : EState α} {Ev : Set (Op (EOp α))}, C.ver v = some (s, Ev) →
      (∀ x ∈ s, F.Dom x.2.2) →
      ∀ τ : List (Op (EOp α)), (∀ o ∈ τ, o ∈ C.events ∧ o ∉ Ev) →
      (E Γ α).query
          (applySeq (E Γ α).toCRDTSig (eRemapSt F.f s)
            (τ.map (eRemapOp F.f))) ()
        = (E Γ α).query (applySeq (E Γ α).toCRDTSig s τ) () := by
  intro s Ev hv hrest τ hτ
  obtain ⟨s', Ev', hv', hset⟩ := hsettled
  rw [hv] at hv'
  injection hv' with hv'
  have hEv : Ev' = Ev := (congrArg Prod.snd hv').symm
  rw [hEv] at hset
  exact (eRecode_settled_bridge F hv hset hAF hrest τ hτ).2

/-! ## Axiom audit -/

#print axioms settledAt_dichotomy
#print axioms eRecode_settled_bridge
#print axioms eRecode_settled_bridge'

end Sal.ConditionedMRDTs
