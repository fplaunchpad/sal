import Sal.ConditionedMRDTs.Metatheory.ConditionedContract
import Sal.ConditionedMRDTs.MRDT_Instances.MRDT_Instances

/-!
# Routing the ENTIRE discharged catalogue through the closure-indexed contract

Task #5 of `Development/CONDITIONED_METATHEORY_PLAN.md`. `ConditionedContract.lean`
built the framework spine (route (c)) and recovered TWO example corners through
it — the OR-Set at `(weak,⊤)` and the Enable-wins flag at `(full,⊤)`. This file
VALIDATES that spine by routing **every** production MRDT that has an end-to-end
`_ra_linearizable3` discharge through `ConditionedContract` — nine in total. Each
`_adequate_viaContract` theorem re-derives `IsRALinearizable3` for the same
configuration class as the MRDT's own `_ra_linearizable3`, but SOLELY through
`ConditionedContract.adequate` / `.ofVCs` / `.ofJoinF`, reusing the existing
per-MRDT VC discharges verbatim (no VC is re-proved). The mere existence of each
theorem is a machine-checked proof that the framework subsumes that MRDT.

## The nine MRDTs and how each routes

| MRDT | its `_ra_linearizable3` on-ramp | routed via | index |
|---|---|---|---|
| OR-Set | `join_lemma3_of_cd_feasible` (`CoreVCs3CD+FeasibleDeltaVCs3+CDVC3`) | `ofVCs` | `weak` |
| OR-Set-eff | `join_lemma3_of_cd_feasible` | `ofVCs` | `weak` |
| Enable-wins flag | `ra_linearizable3_of_joinF` (`JoinLemma3F`) | `ofJoinF` | `full` |
| Grow-Only Set | `ra_linearizable_of_core_delta_cd3` (`CoreVCs3+DeltaVCs3+CDVC3`) | `ofVCs`* | `weak` |
| Grow-Only Map | `ra_linearizable_of_core_delta_cd3` | `ofVCs`* | `weak` |
| Increment-Only Counter | `ra_linearizable_of_core_delta_cd3` | `ofVCs`* | `weak` |
| PN-Counter | `ra_linearizable_of_core_delta_cd3` | `ofVCs`* | `weak` |
| RGA (tombstone) | `ra_linearizable_of_core_delta_cd3` | `ofVCs`* | `weak` |
| Peritext | `ra_linearizable_of_core_delta_cd3` | `ofVCs`* | `weak` |

## The one adaptation (`*`) — no new constructor, an existing adapter suffices

The six "unconditional-tier" types (grow-only unions + counter groups) do NOT
discharge the `CoreVCs3CD + FeasibleDeltaVCs3 + CDVC3` bundle that `ofVCs`
consumes; they discharge the *wider* unconditional bundle
`CoreVCs3 + DeltaVCs3 + CDVC3` and ride `ra_linearizable_of_core_delta_cd3`
(`Adequacy.lean:800`). At first glance this is a different entry point — a
candidate framework finding. But the spine already contains the exact adapters
that close the gap, so **no new smart constructor is needed**; `ofVCs` fits once
the wider bundle is downcast:

* `CoreVCs3.toCD` (`VC_Set.lean:127`) — `CoreVCs3 D → CoreVCs3CD D`;
* `feasibleDeltaVCs3_of_delta` (`Adequacy.lean:812`) — `CoreVCs3 D → DeltaVCs3 D
  → FeasibleDeltaVCs3 D` (the unconditional delta laws imply their
  context-restricted feasible forms, since the feasible laws merely discard the
  configuration hypotheses);
* `cdVC3_of_all_comm` (`Adequacy.lean:743`) — the commuting class gets `CDVC3`
  for free (already used by each `_ra_linearizable3`).

So each unconditional-tier type routes through `ofVCs` as
`ofVCs D (h_coreVCs3.toCD) (feasibleDeltaVCs3_of_delta h_coreVCs3 h_deltaVCs3)
(cdVC3_of_all_comm h_coreVCs3 h_all_comm) trivial`. This is exactly the factoring
`join_lemma3_of_cd' = join_lemma3_of_cd_feasible ∘ toCD ∘ feasibleDeltaVCs3_of_delta`
(`Adequacy.lean:1190`) that already proves the unconditional route is a corollary
of the feasible route — the contract simply repackages it. The headline finding
is therefore: **all nine route, all eight weak-tier through the single `ofVCs`
arm, EWFlag through `ofJoinF`; the framework's existing on-ramps are sufficient,
no gap.**

Every MRDT here has `Inv = ⊤` (the `initConfig … trivial` column of the class
map); the `Inv`-nontrivial column remains the declared update-layer hole
(task #4), untouched by this validation.
-/

namespace Sal.ConditionedMRDTs.AllMRDTs

open Sal.Emulation
open Classical

/-! ## §1. Weak-tier corner, feasible on-ramp — OR-Set, OR-Set-efficient

These two already discharge `CoreVCs3CD + FeasibleDeltaVCs3 + CDVC3`, exactly the
inputs `ofVCs` consumes; the routing is the smart constructor applied to the
existing lemmas. -/

/-- **OR-Set through the contract**, `(weak,⊤)`. Reuses `ORSet_coreVCs3CD`,
`ORSet_feasibleDeltaVCs3`, `ORSet_cdVC3` — the same triple `ORSet_ra_linearizable3`
consumes. -/
theorem ORSet_adequate_viaContract
    (C : Configuration ORSet)
    (hReach : (labeledTS3 ORSet).ReachableFrom (initConfig ORSet trivial) C) :
    IsRALinearizable3 C :=
  (ConditionedContract.ofVCs ORSet ORSet_coreVCs3CD ORSet_feasibleDeltaVCs3
    ORSet_cdVC3 trivial).adequate C hReach

/-- **OR-Set-efficient through the contract**, `(weak,⊤)`. Reuses
`ORSetE_coreVCs3CD`, `ORSetE_feasibleDeltaVCs3`, `ORSetE_cdVC3`. -/
theorem ORSetE_adequate_viaContract
    (C : Configuration ORSetE)
    (hReach : (labeledTS3 ORSetE).ReachableFrom (initConfig ORSetE trivial) C) :
    IsRALinearizable3 C :=
  (ConditionedContract.ofVCs ORSetE ORSetE_coreVCs3CD ORSetE_feasibleDeltaVCs3
    ORSetE_cdVC3 trivial).adequate C hReach

/-! ## §2. Full-tier corner — Enable-wins flag

The only MRDT whose merge (counter comparison) needs full causal closure; it
discharges `JoinLemma3F` directly, so it routes through `ofJoinF`. -/

/-- **Enable-wins flag through the contract**, `(full,⊤)`. Reuses
`EWFlag_joinLemma3F` — the same direct full-closure join `EWFlag_ra_linearizable3`
consumes. -/
theorem EWFlag_adequate_viaContract
    (C : Configuration EWFlag)
    (hReach : (labeledTS3 EWFlag).ReachableFrom (initConfig EWFlag trivial) C) :
    IsRALinearizable3 C :=
  (ConditionedContract.ofJoinF EWFlag EWFlag_joinLemma3F trivial).adequate C hReach

/-! ## §3. Weak-tier corner, unconditional on-ramp — the commuting six

Grow-Only Set/Map, Increment-Only + PN Counters, tombstone RGA, Peritext. Each
discharges the *wider* `CoreVCs3 + DeltaVCs3 + CDVC3` bundle and rides
`ra_linearizable_of_core_delta_cd3`. They route through the same `ofVCs` arm via
the existing adapters (`CoreVCs3.toCD`, `feasibleDeltaVCs3_of_delta`,
`cdVC3_of_all_comm`) — no new constructor, and no VC re-proved. -/

/-- **Grow-Only Set through the contract**, `(weak,⊤)`. `GOSet_coreVCs3`,
`GOSet_deltaVCs3`, `GOSet_all_comm` adapted into the `ofVCs` inputs. -/
theorem GOSet_adequate_viaContract
    (C : Configuration GOSet)
    (hReach : (labeledTS3 GOSet).ReachableFrom (initConfig GOSet trivial) C) :
    IsRALinearizable3 C :=
  (ConditionedContract.ofVCs GOSet GOSet_coreVCs3.toCD
    (feasibleDeltaVCs3_of_delta GOSet_coreVCs3 GOSet_deltaVCs3)
    (cdVC3_of_all_comm GOSet_coreVCs3 GOSet_all_comm) trivial).adequate C hReach

/-- **Grow-Only Map through the contract**, `(weak,⊤)`. -/
theorem GOMap_adequate_viaContract
    (C : Configuration GOMap)
    (hReach : (labeledTS3 GOMap).ReachableFrom (initConfig GOMap trivial) C) :
    IsRALinearizable3 C :=
  (ConditionedContract.ofVCs GOMap GOMap_coreVCs3.toCD
    (feasibleDeltaVCs3_of_delta GOMap_coreVCs3 GOMap_deltaVCs3)
    (cdVC3_of_all_comm GOMap_coreVCs3 GOMap_all_comm) trivial).adequate C hReach

/-- **Increment-Only Counter through the contract**, `(weak,⊤)`. -/
theorem IOC_adequate_viaContract
    (C : Configuration IOC)
    (hReach : (labeledTS3 IOC).ReachableFrom (initConfig IOC trivial) C) :
    IsRALinearizable3 C :=
  (ConditionedContract.ofVCs IOC IOC_coreVCs3.toCD
    (feasibleDeltaVCs3_of_delta IOC_coreVCs3 IOC_deltaVCs3)
    (cdVC3_of_all_comm IOC_coreVCs3 IOC_all_comm) trivial).adequate C hReach

/-- **PN-Counter through the contract**, `(weak,⊤)`. -/
theorem PN_adequate_viaContract
    (C : Configuration PN)
    (hReach : (labeledTS3 PN).ReachableFrom (initConfig PN trivial) C) :
    IsRALinearizable3 C :=
  (ConditionedContract.ofVCs PN PN_coreVCs3.toCD
    (feasibleDeltaVCs3_of_delta PN_coreVCs3 PN_deltaVCs3)
    (cdVC3_of_all_comm PN_coreVCs3 PN_all_comm) trivial).adequate C hReach

/-- **Tombstone RGA through the contract**, `(weak,⊤)`. -/
theorem RGAM_adequate_viaContract
    (C : Configuration RGAM)
    (hReach : (labeledTS3 RGAM).ReachableFrom (initConfig RGAM trivial) C) :
    IsRALinearizable3 C :=
  (ConditionedContract.ofVCs RGAM RGAM_coreVCs3.toCD
    (feasibleDeltaVCs3_of_delta RGAM_coreVCs3 RGAM_deltaVCs3)
    (cdVC3_of_all_comm RGAM_coreVCs3 RGAM_all_comm) trivial).adequate C hReach

/-- **Peritext through the contract**, `(weak,⊤)`. -/
theorem Peritext_adequate_viaContract
    (C : Configuration Peritext)
    (hReach :
      (labeledTS3 Peritext).ReachableFrom (initConfig Peritext trivial) C) :
    IsRALinearizable3 C :=
  (ConditionedContract.ofVCs Peritext Peritext_coreVCs3.toCD
    (feasibleDeltaVCs3_of_delta Peritext_coreVCs3 Peritext_deltaVCs3)
    (cdVC3_of_all_comm Peritext_coreVCs3 Peritext_all_comm) trivial).adequate
    C hReach

end Sal.ConditionedMRDTs.AllMRDTs
