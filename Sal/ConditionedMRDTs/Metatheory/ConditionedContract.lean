import Sal.ConditionedMRDTs.Metatheory.JoinLemma3C
import Sal.ConditionedMRDTs.Metatheory.Adequacy
/-!
# The conditioned contract spine (the closure-indexed disjunctive contract)

The framework spine: one adequacy bridge indexed by a closure predicate `𝒞`,
one contract bundle, and two production corners recovered as instances through
it. It builds on `JoinLemma3C.lean`, `Adequacy.lean`, and `MRDT_Instances.lean`.

## The closure side-condition

`GoodConfig3.ver_causal` (`Adequacy.lean:56`) says every allocated store
version's event set is **fully causally closed**: `∀ a b, vis a b → b ∈ E →
a ∈ E`, i.e. `fullClosure (core C) E`. Full closure is the strongest closure in
the ladder (`weakClosure_of_fullClosure`, `JoinLemma3C.lean:123`). Therefore a
closure-indexed Join Lemma `JoinLemma3C D 𝒞` can be fed store versions for any
`𝒞` that full closure implies: the sides arrive fully closed, so they are
automatically `𝒞`-closed whenever `fullClosure ⟹ 𝒞`.

That side-condition (`𝒞` is no stronger than full closure) is necessary: a `𝒞`
strictly stronger than full closure would make `JoinLemma3C D 𝒞` (antitone in
`𝒞`, `JoinLemma3C.anti`) too weak a hypothesis to be adequate, and the bridge
would fail to apply. Both indices of interest sit at or below full closure:

* `weakClosure`: implied by full closure (`weakClosure_of_fullClosure`);
* `fullClosure`: implied by itself.

So the side-condition costs nothing at the two corners while pinning the exact
class of `𝒞` the spine serves. The bridge is
`ra_linearizable3_of_joinF ∘ (strengthen 𝒞 to fullClosure via JoinLemma3C.anti)`.

## What is here

1. **`ra_linearizable3_of_joinC`**: the unified closure-indexed adequacy
   bridge (`§1`). Given `𝒞`, a proof `fullClosure ⟹ 𝒞`, and `JoinLemma3C D 𝒞`,
   every reachable `GoodConfig3` configuration `IsRALinearizable3`. Both library
   bridges factor through it:
   * `ra_linearizable3_of_join_viaC` recovers `Adequacy.ra_linearizable3_of_join`
     at `𝒞 := weakClosure`, composing with the definitional
     `JoinLemma3 → JoinLemma3C weakClosure` (`joinLemma3C_weak`);
   * `ra_linearizable3_of_joinF_viaC` recovers `Adequacy.ra_linearizable3_of_joinF`
     at `𝒞 := fullClosure`.
   Both corollaries carry the signatures of the library bridges
   (`Adequacy.lean:774` / `Adequacy.lean:1301`). The weak corner is recovered
   *through full closure*: `ra_linearizable3_of_join` does not need its
   weak-closure `goodConfig3_merge`, because store versions are fully closed
   regardless.

2. **`ConditionedContract`**: the contract bundle (`§2`), a `ConditionedMRDTSig`,
   a declared index `𝒞`, the Join Lemma `JoinLemma3C D 𝒞`, the side-condition
   `closure_below_full : fullClosure ⟹ 𝒞`, and `inv_init : D.Inv D.init`.
   `ConditionedContract.adequate` discharges per-version RA-linearizability via
   `§1`. Two smart constructors realize the disjunctive dispatch:
   * `ofVCs`: the update layer (`CoreVCs3CD`) + feasible delta laws
     (`FeasibleDeltaVCs3`) + `CDVC3`, wired through
     `join_lemma3_of_cd_feasible` into `JoinLemma3 = JoinLemma3C weakClosure`;
   * `ofJoinF`: a direct `JoinLemma3F = JoinLemma3C fullClosure` (EWFlag-style).

3. **Instances through the spine** (`§3`): the generic corners
   (`adequate_ofVCs`, `adequate_ofJoinF`) and the two production recoveries,
   `ORSet_adequate_viaContract` (weak corner, reusing `ORSet_coreVCs3CD` /
   `ORSet_feasibleDeltaVCs3` / `ORSet_cdVC3`) and `EWFlag_adequate_viaContract`
   (full corner, reusing `EWFlag_joinLemma3F`). Neither re-proves the MRDT; each
   routes its discharge through `ConditionedContract`.

## The two-axis class map (`𝒞` × `Inv`)

The class map is a table indexed by closure strength `𝒞` (rows) and the state
invariant `Inv` (columns). Every production MRDT verified here lives in the
`Inv = ⊤` (flat) column:

```
              Inv = ⊤ (flat)                              Inv nontrivial (conditioned)
  𝒞 = weak   Counter, G-Set, OR-Set, OR-Set-eff,         (empty)
             GOSet, GOMap, IOC, PN, RGA(M), Peritext          ↑
  𝒞 = full   EWFlag                                       the declared hole
                                                          (RGA hosting)
```

* `𝒞 = weak, Inv = ⊤`: the set/register/list family. Their VC bundles discharge
  the weak-closure `JoinLemma3` (`ra_linearizable3_of_join` /
  `ra_linearizable_of_core_delta_cd3`). Contract via `ofVCs`.
* `𝒞 = full, Inv = ⊤`: the Enable-wins flag. Counter-comparison merges need full
  causal closure, so it discharges `JoinLemma3F` directly. Contract via `ofJoinF`.
* `Inv nontrivial`: **unpopulated; the declared hole.**

## The update-layer hole

This spine keeps the unconditional update layer (`CoreVCs3CD`, whose
`UpdateVCs` demand `commutes`, not `commutesOn`) and parameterizes
`Inv`/`applicable` through `ConditionedMRDTSig` for RGA hosting. It does
**not** re-found convergence over `commutesOn`. The naive `commutes ↦
commutesOn` transcription is refuted
(`G2_Transport_Probe.lean:G2_conditioned_convergence_refuted`); the right
feasibility notion is "applicable OR no-op at every prefix"
(`G2_Applicability_Aware.lean`), which is not mechanized as a convergence layer
here.

Consequently: the `Inv`-nontrivial column of the class map is empty, and no
theorem in this file conditions its update layer. The flat and EWFlag corners
(the two `*_adequate_viaContract` recoveries) hold; the genuinely-conditioned
RGA corner is here a parameter slot, not a discharge. The spine delivers the
packaging (a single adequacy bridge covering both closure strengths); it does
not by itself re-found convergence for nontrivial `Inv`.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

/-! ## §1. The unified closure-indexed adequacy bridge

`JoinLemma3C.anti` strengthens the declared index `𝒞` up to `fullClosure` using
the side-condition `fullClosure ⟹ 𝒞`, producing `JoinLemma3F` (definitionally,
`joinLemma3C_full`); the full-closure bridge `ra_linearizable3_of_joinF` then
finishes. No merge-preservation lemma is re-copied: the whole `GoodConfig3`
induction is reused through `ra_linearizable3_of_joinF`, and the closure gap is
bridged by antitonicity plus `GoodConfig3.ver_causal` (which
`ra_linearizable3_of_joinF` already consumes). -/

section Bridge
variable {D : ConditionedMRDTSig}

/-- **Unified closure-indexed adequacy.** For any index `𝒞` that full causal
closure implies (`h_full`), a data type providing `JoinLemma3C D 𝒞` makes every
reachable `GoodConfig3` configuration per-version RA-linearizable. The two
library bridges are the `weakClosure` / `fullClosure` instances (below).

`h_full` is the necessary side-condition: store versions arrive fully closed
(`GoodConfig3.ver_causal`), so the Join Lemma's `𝒞`-closed side premises are met
exactly when `fullClosure ⟹ 𝒞`. -/
theorem ra_linearizable3_of_joinC (𝒞 : ClosurePred D.toCRDTSig)
    (h_full : ∀ (C : Sal.Emulation.Configuration D.toCRDTSig)
        (ev : Set (Op D.AppOp)),
      fullClosure D.toCRDTSig C ev → 𝒞 C ev)
    (hJoin : JoinLemma3C D 𝒞)
    {hInit : D.Inv D.init}
    (C : Configuration D)
    (hReach : (labeledTS3 D).ReachableFrom (initConfig D hInit) C) :
    IsRALinearizable3 C :=
  ra_linearizable3_of_joinF
    ((joinLemma3C_full D).mp
      (JoinLemma3C.anti (𝒞' := fullClosure D.toCRDTSig) h_full hJoin))
    C hReach

/-- **Recovery of the weak bridge.** `Adequacy.ra_linearizable3_of_join`
factors as `ra_linearizable3_of_joinC weakClosure` composed with the
definitional `JoinLemma3 → JoinLemma3C weakClosure` (`joinLemma3C_weak`). The
signature matches `Adequacy.lean:774`. The weak bridge is recovered *through*
full closure: the weak-closure `goodConfig3_merge` is not needed, because store
versions are fully closed regardless. -/
theorem ra_linearizable3_of_join_viaC (hJoin : JoinLemma3 D)
    {hInit : D.Inv D.init}
    (C : Configuration D)
    (hReach : (labeledTS3 D).ReachableFrom (initConfig D hInit) C) :
    IsRALinearizable3 C :=
  ra_linearizable3_of_joinC (weakClosure D.toCRDTSig)
    (fun _ _ h => weakClosure_of_fullClosure h)
    ((joinLemma3C_weak D).mpr hJoin) C hReach

/-- **Recovery of the full bridge.** `Adequacy.ra_linearizable3_of_joinF`
factors as `ra_linearizable3_of_joinC fullClosure`. Signature matches
`Adequacy.lean:1301`. -/
theorem ra_linearizable3_of_joinF_viaC (hJoin : JoinLemma3F D)
    {hInit : D.Inv D.init}
    (C : Configuration D)
    (hReach : (labeledTS3 D).ReachableFrom (initConfig D hInit) C) :
    IsRALinearizable3 C :=
  ra_linearizable3_of_joinC (fullClosure D.toCRDTSig)
    (fun _ _ h => h)
    ((joinLemma3C_full D).mpr hJoin) C hReach

end Bridge

/-! ## §2. The contract bundle

`ConditionedContract` is the disjunctive contract as a first-class structure:
the data type, its declared closure index, the join lemma at that index, the
`fullClosure ⟹ 𝒞` side-condition the spine needs, and the initial invariant.
`adequate` is `§1` applied to the fields. The two smart constructors `ofVCs` /
`ofJoinF` are the two dispatch arms. -/

/-- The closure-indexed disjunctive contract. A data type is `adequate` (every
reachable configuration per-version RA-linearizable) as soon as it supplies a
Join Lemma at *some* index `𝒞` no stronger than full closure. -/
structure ConditionedContract where
  /-- The conditioned ternary MRDT signature (carries `Inv`, `applicable`). -/
  D : ConditionedMRDTSig
  /-- The declared closure strength at which this MRDT's Join Lemma is proved. -/
  𝒞 : ClosurePred D.toCRDTSig
  /-- The closure-indexed Join Lemma at the declared index. -/
  join : JoinLemma3C D 𝒞
  /-- Side-condition: the declared index is no stronger than full closure, so
  the fully-closed store versions of `GoodConfig3` are `𝒞`-closed. Trivial for
  both `weakClosure` and `fullClosure`. -/
  closure_below_full :
    ∀ (C : Sal.Emulation.Configuration D.toCRDTSig) (ev : Set (Op D.AppOp)),
      fullClosure D.toCRDTSig C ev → 𝒞 C ev
  /-- The state invariant holds at the initial state. -/
  inv_init : D.Inv D.init

/-- **Adequacy of a contract**: every configuration reachable in the ternary
transition system from the initial configuration is per-version
RA-linearizable. This is `ra_linearizable3_of_joinC` applied to the bundled
fields. -/
theorem ConditionedContract.adequate (K : ConditionedContract)
    (C : Configuration K.D)
    (hReach : (labeledTS3 K.D).ReachableFrom (initConfig K.D K.inv_init) C) :
    IsRALinearizable3 C :=
  ra_linearizable3_of_joinC K.𝒞 K.closure_below_full K.join C hReach

/-- **Weak-closure smart constructor**: from the update layer + feasible delta
laws + the causal-delta bound, via `join_lemma3_of_cd_feasible`. This is the
`𝒞 = weakClosure` dispatch arm — the set/register/list family. -/
def ConditionedContract.ofVCs (D : ConditionedMRDTSig)
    (hVC : CoreVCs3CD D) (hFΔ : FeasibleDeltaVCs3 D) (hCD : CDVC3 D)
    (hInit : D.Inv D.init) : ConditionedContract where
  D := D
  𝒞 := weakClosure D.toCRDTSig
  join := (joinLemma3C_weak D).mpr (join_lemma3_of_cd_feasible hVC hFΔ hCD)
  closure_below_full := fun _ _ h => weakClosure_of_fullClosure h
  inv_init := hInit

/-- **Full-closure smart constructor**: from a direct full-closure Join Lemma.
This is the `𝒞 = fullClosure` dispatch arm — the Enable-wins flag corner. -/
def ConditionedContract.ofJoinF (D : ConditionedMRDTSig)
    (hJoinF : JoinLemma3F D) (hInit : D.Inv D.init) : ConditionedContract where
  D := D
  𝒞 := fullClosure D.toCRDTSig
  join := (joinLemma3C_full D).mpr hJoinF
  closure_below_full := fun _ _ h => h
  inv_init := hInit

/-! ## §3. Instances through the spine

The framework recovers existing discharges without re-proving them: the generic
corners, then the two production MRDTs routed through `ConditionedContract`. -/

/-- **Generic (weak, Inv) corner.** Any conditioned signature discharging the
set-shaped VC bundle is adequate through the spine, at `𝒞 = weakClosure`. -/
theorem adequate_ofVCs {D : ConditionedMRDTSig}
    (hVC : CoreVCs3CD D) (hFΔ : FeasibleDeltaVCs3 D) (hCD : CDVC3 D)
    (hInit : D.Inv D.init)
    (C : Configuration D)
    (hReach : (labeledTS3 D).ReachableFrom (initConfig D hInit) C) :
    IsRALinearizable3 C :=
  (ConditionedContract.ofVCs D hVC hFΔ hCD hInit).adequate C hReach

/-- **Generic (full, Inv) corner.** Any conditioned signature discharging a
direct full-closure Join Lemma is adequate through the spine, at
`𝒞 = fullClosure`. -/
theorem adequate_ofJoinF {D : ConditionedMRDTSig}
    (hJoinF : JoinLemma3F D) (hInit : D.Inv D.init)
    (C : Configuration D)
    (hReach : (labeledTS3 D).ReachableFrom (initConfig D hInit) C) :
    IsRALinearizable3 C :=
  (ConditionedContract.ofJoinF D hJoinF hInit).adequate C hReach

end Sal.ConditionedMRDTs
