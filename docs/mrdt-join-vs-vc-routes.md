# MRDT instances: direct Join proofs vs. VC proofs

Every MRDT instance's convergence obligation (`replayAdequacy` inside
`VerifiedMRDT`) terminates in the single semantic `JoinAt` obligation
(`Sal/MRDTs/Framework/MergeLaws.lean`). Instances discharge it one of two ways:

1. **Direct Join** — the instance proves the ternary `Join` / `JoinAt` / `JoinOn`
   itself, per replay context, then packages it with
   `ReplayAdequacyCertificate.ofJoin` / `.ofJoinOn`
  (`Sal/MRDTs/Metatheory/Correctness.lean:98`) or a hand-rolled `soundV`.
2. **VCs (verification conditions)** — the instance only supplies reusable raw
   merge equations; a generic induction converts them into `Join`. Three VC
   bundles exist:
   - `MergeLaws` + `DeltaLaws` → `JoinProof.ofArbitraryStateLaws` (arbitrary-state
     equations),
   - `CanonicalJoinLaws` with `FeasibleDeltaLaws` (canonical-state contract),
   - Paper1's five-equation `Raw.MergeVCs` — `merge_comm`, `init`,
     `causal_delta`, `local_redistribute`, `shared` — discharged by
     `representationJoin_of_vcs` (`Sal/MRDTs/Paper1/ConcreteJoin.lean:379`).

Both routes end in the same `JoinAt`; the VC route factors the per-context work
into one generic induction (`join_at_sizes`) so each datatype only verifies raw
equations.

---

## Instances proving Join directly

| Instance | Evidence |
|---|---|
| Queue | `q_join_at` proved directly (`Instances/Queue.lean:698`; header: "the ternary **Join Lemma directly**"), packaged via `ofJoinOn` in `Instances/QueueCertificates.lean:92` |
| EmbedRGA | `e_join_at`, a direct ternary `JoinAt` under honesty (`Instances/EmbedRGA.lean:926`), `ofJoinOn` at line 1235 |
| SidedEmbedRGA | `s_join_at` (`Instances/SidedEmbedRGA.lean:1263`, `ofJoinOn`) |
| ProductionRGA, Peritext | re-export the EmbedRGA / SidedEmbedRGA certificates (`Instances/ProductionRGA.lean`, `Instances/Peritext.lean:34`) |
| FugueMax | per-context `join_of_mint`, direct `soundV` (`Instances/FugueMaxReplayProof.lean:421`); `FugueMaxContract` reuses it; `FugueMaxReplay.lean:1007` adds `fmReplayAdequacy` (`ofJoinOn` with `f_join_at`) |
| SidedPeritext | `core_join_at` via `ofJoinOn` (`Instances/SidedPeritext.lean:516`, rich variant at 874) |
| EfficientORSet | direct `soundV` by induction over the certified execution, using the per-context `represents_merge` lemma (`Instances/EfficientORSetCertified.lean:126`; lemma in `Instances/EfficientORSetHistory.lean:64`) |
| MVRLive | same pattern with `MVRLiveHistory.represents_merge` (`Instances/MVRLiveCertified.lean:107`) |
| Paper1 exact OR-set | `join` proved directly ("Honest ancestor merge preserves the canonical union state directly", `Paper1/ORSetCanonical.lean:206`); consumed by `Paper1/ORSetVerified.lean` and `Paper1/ORSetSpecification.lean` |

## Instances proved via VCs

### Framework law bundles (`MergeLaws`+`DeltaLaws` → `JoinProof.ofArbitraryStateLaws`, or `CanonicalJoinLaws`)

| Instance | Evidence |
|---|---|
| AddStore | `Instances/AddStore.lean:69` |
| FlatGrowOnly (G-Set / G-Map) | `Instances/FlatGrowOnly.lean:64` |
| FlatCounters (PN-Counter) | `Instances/FlatCounters.lean:81` |
| FinsetStore | `Instances/FinsetStore.lean:61` |
| TreeMove | `Instances/TreeMove.lean:264` |
| AegisSheet | `Instances/AegisSheet.lean:475`; the public package in `AegisSheetSequential.lean` reuses it |
| RGA (RGAM) | `Instances/RGA.lean:131` (`RGAM_mergeLaws`, `RGAM_deltaLaws`); `RGASequential.lean`'s `verified` consumes the same `join` |
| LWWRegister | `Instances/LWWRegister.lean:136` |
| MVR | `CanonicalJoinLaws` + `FeasibleDeltaLaws` → `CanonicalJoinLaws.join` (`Instances/MVR.lean:472–477`); `MVRContract` reuses it |
| TreeMoveIncremental | five-VC + `CommutingPort.automatedJoinAt all_comm fiveVC` (`Instances/TreeMoveIncrementalMRDT.lean:162–168`), packaged with `ofJoin` in `TreeMoveIncrementalCertificate.lean:183` |
| NotionCore family (core, structural, rich) | `fiveVCs` transported through the commuting port / query lift (`Instances/NotionCoreMRDT.lean:42`, `NotionCoreStructuralVC.lean:48`, `NotionCoreRichMRDT.lean:36`) |

### Paper1 certified case studies (five-equation `Raw.MergeVCs` → `representationJoin_of_vcs`)

| Case study | Evidence |
|---|---|
| RemoveWinsSet (Neem) | `Paper1/RemoveWinsSetVC.lean:165` (`fiveVC`), certificate in `RemoveWinsSetCertificate.lean` |
| SetWinsMap | `Paper1/SetWinsMapVC.lean:95` |
| OptionalRegister | `Paper1/OptionalRegisterVC.lean:331` |
| AddWinsPriorityQueue (+ Full) | `Paper1/AddWinsPriorityQueueVC.lean:157`, `AddWinsPriorityQueueFullCertificate.lean:16` |
| PriorityQueueSameRecord | `Paper1/PriorityQueueSameRecordVC.lean:53` |
| BalegasBoundedCounter | `Paper1/BalegasBoundedCounterVC.lean:140` |
| EnableWinsFlag / NeemFlag | `Paper1/EnableWinsFlagVC.lean:200` (three variants), reused by `NeemFlagCertificate.lean` |
| AnchoredQueue | `Paper1/AnchoredQueue.lean:187` (`mergeVCs`) |
| Fugue (certified port) | `Paper1/CertifiedFugueVC.lean:15` |
| MVR (certified port) | `Paper1/CertifiedMVRVC.lean:86` (via `mrdt_verify` automation) |
| Peritext (certified ports) | `Paper1/CertifiedPeritextVC.lean:12`, `CertifiedPeritextInvariantCertificate.lean:111` |
| RGA (four certified ports) | `Paper1/CertifiedRGAVC.lean:12`, `CertifiedRGACoreMergeVC.lean:19`, `CertifiedRGASidedVC.lean:11`, `CertifiedRGARichVC.lean:9` |
| Guarded raw OR-set | `Paper1/GuardedRawORSetVC.lean:122`, joined in `GuardedRawORSetJoin.lean` |
| Generic commuting port | `Paper1/ConcreteCommutingVCReplay.lean:109` |

---

## Boundary notes

- `Metatheory/Join/HistoricalVCs24.lean` is **not** used by any instance. It
  transcribes the original SAL artifact's 24 verification conditions purely as a
  metatheory experiment checking that they imply the corrected set-relative
  ternary Join.
- The empirical pattern: datatypes whose merge is a simple union/sum (counters,
  grow-only stores, event sets) or whose updates all commute use the VC bundles;
  datatypes whose merge depends on replay ordering, survivor calculation, or
  honesty side-conditions (Queue, RGA embeddings, Fugue, metadata-carrying
  OR-sets) prove Join directly.
