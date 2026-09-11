# Efficient OR-set minimum-timestamp collection

## Enquiry

Goal: determine whether globally present records for one element can be
coalesced by retaining the record with the smallest timestamp.

Candidate claim (refuted): removing the larger record locally, with no
change to the efficient OR-set update and merge operations, preserves set
observations through subsequent execution. Collection may affect a
materialization subsequently used as a merge base. Replicas need not collect
simultaneously.

Falsifier: two replicas start with both records, one collects and then removes
the element, and a subsequent merge disagrees with the uncollected execution.

Formal oracle: `EfficientORSetGCSPOT.lean`, using the existing `update`,
`merge`, and `elements` definitions. Test unequal fresh timestamps and both
compacted and uncollected merge-base materializations.

Reality oracle: hand-derived observed-remove outcomes and the cached F★
`_references/neem_fstar_repo/code/mrdts/OR-set-efficient/App_mrdt.fst`.
The F★ source defines add as replacement by replica/element, remove as
filtering all records for the element, and the same three-way merge as Lean.

Source authority: current Lean operation definitions; checked theorem
statements; the executable campaign; this research note. The cached F★ source
independently confirms the operation equations, but does not implement GC.

Positive control: collection preserves immediate membership and really
decreases record count; an observed removal remains removed with the original
merge base.

Negative control: a compacted merge base and an uncollected branch must expose
the classification of an old redundant record as a new addition.

Residual: a protocol that retains original bases or translates every merge
operand consistently is a different candidate. No general collector
certificate is claimed at this stage.

## Result: mixed merge-base materializations resurrect the element

Status: machine-checked counterexample to the candidate above.

Let `a = (0,1,7)` and `b = (1,2,7)`. Replica 0 adds `a`; replica 1
observes that addition and adds `b`; replica 0 synchronizes. Both heads
contain `S = {a,b}`. Timestamps are distinct and increase with causality.

Replica 0 collects its local materialization of the common version to
`C = {a}`, then issues `remove 7` at timestamp 3, producing the empty state.
Replica 1 has not collected and still supplies `S`. If the local merge-base
materialization is `C`, the existing merge computes

```
merge C {} S = S \\ C = {b}
```

The uncollected execution computes `merge S {} S = {}`. The removal observed
both additions; the observed-remove specification therefore requires absence.
The larger record is incorrectly classified as an addition after the base.
There is no disagreement about which timestamp is smallest.

This counterexample concerns collection of a materialization later used as a
merge base. It does **not** refute a protocol that preserves the original base
or arranges compatible epochs before merging. The original-base control passes
this trace; that control is not a general proof of the original-base strategy.
The tests execute datatype operations along the described schedule; they do
not construct a full `MintCertifiedReachV` configuration witness.

## Repair candidate: a common erasure epoch

Status: algebraic components machine-checked; bounded continuations tested;
distributed collector and general query-preservation invariant staged.

Record a fixed discarded record `d`, and normalize all three merge operands
by erasing `d`. The following equations hold for arbitrary states:

```
erase d (merge L A B) = merge (erase d L) (erase d A) (erase d B)
erase d (update S e) = update (erase d S) e     if time(e) != time(d)
```

`erase_elements` additionally proves query preservation when a distinct
record for the same element remains. A continuation may replace the original
minimum record with a newer record, so the required invariant is existence of
a surviving witness, not permanent retention of the original minimum.

An epoch protocol must establish that invariant for all permitted future
heads, translate incoming branches and bases consistently, and account for
the storage and lifetime of the erasure evidence. Repeated collections,
different cuts, and asynchronous epoch admission remain unproved. The existing
production registry correctly remains an exact-state baseline; this research
does not introduce a `StateGCCertificate` or `StateGCProtocol` instance.

## Theorem catalogue

All declarations are in
`Sal/MRDTs/Instances/EfficientORSetGCSPOT.lean`, namespace
`Sal.MRDTs.Instances.EfficientORSet.GCResearch`.

| Declaration | Evidence |
| --- | --- |
| `timestamps_fresh_and_ordered` | The generated three-event family has positive, distinct, causally increasing timestamps. |
| `collection_really_shrinks` | Two records become the minimum singleton with unchanged immediate membership. |
| `observed_remove_control`, `mixed_base_resurrects`, `naive_min_gc_refuted` | The literal counterexample and refutation of the universally quantified trace-family claim. |
| `original_base_control`, `uniform_translation_control` | Both repairs avoid this particular resurrection. |
| `concurrent_add_control` | A fresh concurrent addition survives, ruling out constant-empty behavior. |
| `erase_merge`, `erase_update` | General fixed-erasure commutation; update requires freshness. |
| `erase_elements` | General query equality with an explicit distinct surviving witness. |
| `exhaustive_controls` | Kernel-checked enumeration of 512 clock/element cases. |
| `continuation_controls`, `exhaustive_continuations` | Directed examples and 1,296 enumerated fork/join continuations. |

## Campaign and validation scope

Plausible uses seeds 17 and 91, `numInst = 500`, `maxSize = 30`.
The naive claim fails on the first case for both seeds: `x = t = gap = 0`,
with zero shrinking steps. The harness treats unexpected success or `gaveUp`
as an error.

The corrected trace controls pass 500 cases per seed, with no `gaveUp`.
The uniform-epoch continuation campaign also passes 500 cases per seed,
with no `gaveUp`. It starts with both replicas holding the two records,
collects both into the same epoch, then generates up to six fresh add/remove
operations per branch across three elements before one merge. It compares
both full and compact results with an independent observed-remove event
history model, and checks exact equality to the uniformly erased full result.
It does not sample repeated epochs or unrestricted DAGs.

The deterministic continuation backstop enumerates four choices from six
add/remove operations (1,296 cases); each branch receives two variable
operations, and the left branch also has four fixed adds to another element.
No test filters inputs with logical implications.

The cached F★ source was read to compare the trusted Lean add/remove/merge
equations. No F★ extraction or differential runtime execution was performed.
The independent history oracle checks only the specified generated scope.

Run:

```
lake build Sal.MRDTs.Instances.EfficientORSetGCSPOT
```

The theorem axiom audits report only `propext`, `Classical.choice`, and
`Quot.sound`. There are no new axioms, admits, `sorry`s, or `native_decide`
proofs in this module.
