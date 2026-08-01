# Metatheory consolidation roadmap

This is the executable migration order for the simplifications described in
`sal-mrdts.tex`. Each phase must preserve the current theorem names until all
production instances have moved.

## Completed foundation

- [x] State the single history/specification/representation correctness stack.
- [x] Inventory the Join-family interfaces and their independent axes.
- [x] Factor the common plain/witness ternary Join geometry as `JoinKitAt`.
- [x] Supply definitional adapters for `JoinLemma3At` and `JoinLemma3AtW`.
- [x] Factor contract-indexed reachability as `ContractReach`.
- [x] Supply equivalences for `HonestReach` and `HonestReachV`.

## Next proof migrations

- [x] Express arbitration canonicity as a doctrine over a generic ambient
  visibility structure; the current arbitration API uses a ternary
  `Configuration`, while plain `JoinLemma3At` uses its replica-keyed core.
- [x] Move one unconditional instance and one `W`-instance through `JoinKitAt`
  as positive and negative canaries.
- [x] Generalize the `GoodConfig3` reachability induction over
  `ContractReach`; retain the existing `Step3` and `Step3V` public names.
- [x] Separate Join geometry from doctrine-specific premises (`Inv`, full
  closure, generation discipline, timestamp uniqueness).
- [x] Add observational-equivalence and coherent-witness doctrines only after
  those premises have explicit fields; do not weaken their counterexample-
  justified hypotheses.

## Higher layers

- [x] Identify the common mint-time provenance judgment: the existing
  `GenHonest D P` already states `P` at every fold of an event's causal past.
- [x] Route the common causal-fold provenance used by EmbedRGA, SidedRGA, and
  MergeableQueue through `GenHonest.exists_causalFold`.
- [x] Repackage the observational epoch core of `StabilityVC` as a
  world-indexed simulation over settled cuts.
- [x] Derive arbitrary finite multi-epoch collapse from world monotonicity.
- [x] Package Join correctness, sequential refinement, product composition,
  and continuation-aware runtime recoding as verified-datatype certificates.
- [x] Define continuation equivalence and restate the sibling-splice
  countermodel as a representation-independent retention lower bound.
- [x] Package the rehoming and unsafe mark-compaction countermodels through the same
  continuation interface.
- [x] Pursue information lower bounds from the resulting distinguishability
  classes.
