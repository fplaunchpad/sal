import Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA_MultiEpoch
import Sal.ConditionedMRDTs.Metatheory.EvidenceDischarge

/-!
# The CompatChain protocol half at the epoch boundary (#97, attempted)

`EmbedRGA_MultiEpoch.lean` closes the *order-iso* half of multi-epoch
composition: two `StablePrefixMap`s compose (`StablePrefixMap.comp`) at their
surviving domain (`CompatOn`), and the n-fold `chainSPM`/`multiEpoch_settled_reads`
give reads-preservation across a whole tower — **once** `CompatOn` (or the
full-domain `CompatChain`) is supplied. What was left open (recoding note
Addendum 4, final paragraph) is discharging `CompatChain`/`CompatOn` for two
consecutive `compactRanked` maps at **nested settled cuts, directly from honest
reachability**. This file records how far that goes and pins the exact blocker.

## What closes: the causal-stability input

The metatheory (`EvidenceDischarge.lean`) already provides the causal-stability
layer that the nested-cut step consumes: one all-heads frontier certificate at
the finer cut `S'` discharges settledness at *both* cuts `S ⊆ S'`
(`settledAt_compatStep` via `allHeardSince_antitone`). `nested_cuts_settled`
specializes this to the embed configuration: from a single `AllHeardSince C v S'`
we get `SettledAt C v S ∧ SettledAt C v S'`, so both epochs' single-epoch
theorems (`compactRanked_settled_reads`) are individually applicable. The
order-iso freshness half also closes: `rED_hocc_fresh` (from
`rED_fresh_dominates`) shows epoch-2's kids-or-fresh `hocc` survives the epoch-1
renumbering — a delta fresh against epoch-1's *original* sibling deltas is fresh
against the *renumbered ordinals*, without inspecting their meaning.

## What blocks: the re-based-honesty chain-image obligation

`CompatOn F₁ F₂ Rest' MintAt'` needs `restG` / `mintG`: every epoch-1 survivor,
once `F₁`-remapped, is **`F₂`-at-hand** — i.e. is a coordinate of some chain in
epoch-2's domain `𝒟₂ = EAtHand Γ C₂ …`. But `compactRanked`'s domain is
quantified over an **honest** configuration `C₂` through
`eAnchored_exists hGen hEnum` (it needs `GenHonest`/`CausalPastEnumerable` to
pin each event's birth chain via `chainOf`). The epoch-2 configuration is the
epoch-1 *compaction*, and that is **not** a native honest configuration:
compaction deliberately forgets dead chain segments, so `EHonest.chain_gen`
fails for a renumbered coordinate (exactly the gap flagged in
`eRecode_ra_transport`'s docstring and recoding note §5/§6). Concretely, the
blocking obligation is:

> **`(⋆)` re-based honesty**: exhibit an honest configuration `C₂` (honest
> *modulo the order-embedding `F₁`* of coordinates) whose anchored chain
> structure is `F₁.f ∘ chainOf₁` — so that `eAnchored_exists` re-derives at
> epoch 2 and `𝒟₂`'s coordinates are provably the `F₁`-images of the epoch-1
> survivors.

Without `(⋆)`, `restG`/`mintG` cannot be discharged: the epoch-2 `EAtHand`
domain is not known to be the `F₁`-image domain, so `F₁.f c ∈ 𝒟₂`-coordinates is
unprovable. `(⋆)` is the *same* deferred protocol layer as the single-epoch
`AnchorsFactorBeyond`/`eRecode_ra_transport` gap, now relocated to the epoch
boundary. The order-iso side (this file's `rED_hocc_fresh`,
`rED_le_self`/`rED_fresh_dominates` in MultiEpoch) is genuinely in hand; the
residue is honesty re-basing, not the coordinate arithmetic.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Sal.EmbedRGA (OrderedPrefixCode PosChain)

set_option linter.unusedSectionVars false

variable {α : Type} [DecidableEq α] [Inhabited α]

/-! ## §1 The causal-stability input (closes): one frontier, two nested cuts -/

/-- **Both nested cuts settle from a single frontier certificate.** On an
evidence-reachable embed configuration, `AllHeardSince C v S'` at the finer cut
`S' ⊇ S` discharges `SettledAt` at both cuts simultaneously — the causal
input the epoch-boundary `CompatChain` step consumes (`settledAt_compatStep` +
`allHeardSince_antitone`, `EvidenceDischarge.lean`). This is what lets one
"heard from everyone" observation cover epoch 1's cut `S` and epoch 2's cut
`S'` at once. -/
theorem nested_cuts_settled {Γ : OrderedPrefixCode}
    {C : Configuration (E Γ α)} (hInvE : ReachInvE C)
    {v : Version} {s : EState α} {E S S' : Set (Op (EOp α))}
    (hv : C.ver v = some (s, E)) (hSS : S ⊆ S')
    (hdS : ∀ a b, C.vis a b → b ∈ S → a ∈ S)
    (hdS' : ∀ a b, C.vis a b → b ∈ S' → a ∈ S')
    (hAll : AllHeardSince C v S') :
    SettledAt C v S ∧ SettledAt C v S' :=
  ⟨settledAt_compatStep hInvE hv hSS hdS hAll,
   settledAt_of_allHeard hInvE hv hdS' hAll⟩

/-! ## §2 The order-iso half (closes): epoch-2 freshness survives the epoch-1
renumbering -/

/-- **Epoch-2's kids-or-fresh, freshness branch, on renumbered ordinals.** A
beyond-epoch-2 delta `d` that dominates every epoch-1 *original* kept sibling
delta dominates every epoch-1 *renumbered ordinal* `rED keep inflight p e` too.
This is precisely the `hocc` fresh branch that epoch 2's `compactRanked` (via
`rED_iso`) needs on the already-renumbered coordinates — discharged from
`rED_fresh_dominates` with no generation-discipline wall. -/
theorem rED_hocc_fresh {keep inflight : List (List ℕ)}
    (hKpos : ∀ k ∈ keep, PosChain k) {p : List ℕ} {d : ℕ}
    (hfresh : ∀ k, (p ++ [k]) ∈ keep → k < d) :
    ∀ e, (p ++ [e]) ∈ keep → rED keep inflight p e < d :=
  fun _ he => rED_fresh_dominates hKpos hfresh he

/-! ## §3 The reduction, with the blocker isolated

`CompatOn` reduces to four field obligations. `restF`/`mintF` (the composite's
surviving coordinates are epoch-1-at-hand) are definitional in the survivor
domain. `restG`/`mintG` (their `F₁`-images are epoch-2-at-hand) are the blocker
`(⋆)` above. The following packages the composite once the four are supplied —
making explicit that the *only* residue over the closed causal/order-iso parts
is the chain-image correspondence `hRG`/`hMG`. -/

/-- **The composite, given the chain-image correspondence.** This is the
`CompatOn` constructor exhibited at the two `compactRanked` epochs: everything
upstream (the two settled cuts via `nested_cuts_settled`, the freshness via
`rED_hocc_fresh`) is discharged; the residual hypotheses `hRG`/`hMG` are exactly
the re-based-honesty obligation `(⋆)`. Consuming this with a proof of `(⋆)`
would close the epoch-boundary `CompatChain`. -/
theorem compatOn_two_epoch {Γ : OrderedPrefixCode} (F₁ F₂ : StablePrefixMap Γ)
    (Rest' : List Bool → Prop) (MintAt' : List Bool → ℕ → Prop)
    (hRF : ∀ c, Rest' c → F₁.Dom c)
    (hRG : ∀ c, Rest' c → F₂.Dom (F₁.f c))
    (hMF : ∀ π d, MintAt' π d → F₁.MintAt π d)
    (hMG : ∀ π d, MintAt' π d → F₂.MintAt (F₁.f π) d) :
    CompatOn F₁ F₂ Rest' MintAt' :=
  ⟨hRF, hRG, hMF, hMG⟩

/-! ## §4 Axiom audit -/

#print axioms nested_cuts_settled
#print axioms rED_hocc_fresh
#print axioms compatOn_two_epoch

end Sal.ConditionedMRDTs
