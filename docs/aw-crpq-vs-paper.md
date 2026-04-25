# Add-Win CRPQ in Sal vs. the paper

Cross-reference between the Lean formalization in
`Sal/CRDTs/Add_Win_Priority_Queue/Add_Win_Priority_Queue_CRDT.lean` (state-based CRDT),
`Sal/MRDTs/Add_Win_Priority_Queue/Add_Win_Priority_Queue_MRDT.lean` (state-based MRDT), and
their read-side companions, against:

> Yuqi Zhang, Lingzhi Ouyang, Yu Huang, Xiaoxing Ma. *Conflict-free
> Replicated Priority Queue: Design, Verification and Evaluation.*
> Internetware 2023, ACM. <https://doi.org/10.1145/3609437.3609452>

This document is the AW-CRPQ counterpart of `peritext-vs-paper.md`.
The local copy of the paper is at
`_references/3609437.3609452 (1).pdf`; the algorithm references
below cite that paper's Algorithm 2 (Add-Win CRPQ).

## Headline differences from the paper

| Aspect | Paper | Our Lean | Faithful? |
|---|---|---|---|
| Element model | `e = (id, priority)` (§2.2) | `elem : ℕ` plays the `id` role; priority computed from state | ✅ Consistent. |
| Update ops | `add(e, x)`, `inc(e, i)`, `rmv(e)` | `Add e v`, `Inc e amount`, `Rmv e D` (CRDT) / `Rmv e` (MRDT) | ✅ Same op set. |
| Query ops | `empty()`, `lookup(e)`, `get_pri(e)`, `get_max()` (§2.2) | All four lifted as propositional specs: `is_empty`, `lookup`, `is_priority` (= `is_innate_record` + `is_acquired`), `is_get_max` | ✅ All four; convergence proved on each. |
| Add-Win state (Alg 2 line 1) | `A : set of (e, t, x, inc, count)` 5-tuples; `R : set of (e, t)` | CRDT splits into `A : map (elem, add_ts) → ℕ` + separate `I : set (elem, inc_ts, ℤ)` + `R : set (elem, add_ts)` | ⚠️ State decomposed differently — see §"State-shape divergence" below. |
| Add-Win semantics (Alg 2) | Innate = LWW by `t`; acquired = **Most-Change-Win** by `count` | Innate = LWW (faithful); acquired = `Σ amount` over I-records-for-e | ⚠️ Faithful **under the flat-observation simplification**: in our flat state every live add-record observes every inc-record, so MCW collapses to Σ. See "Why our acquired-Σ rule is paper-faithful in our state model" below. |
| Verification | TLA+/PlusCal + TLC model checking, bounded by small-scope hypothesis (3 replicas, 2–8 client requests) | Full Lean theorem proving, unbounded state, 24 RA-linearizability VCs | Different — neither subsumes the other. |

## State-shape divergence

The paper bundles per-add-record state: `A : set of (e, t, x, inc, count)`,
where every add-record carries its accumulated `inc` value and the
`count` (sum of `|i|` magnitudes ever applied to that record). When a
new `inc(e, i)` arrives, the paper's effect (Alg 2 line 24) iterates
over the snapshotted live timestamps `O` and rewrites *every*
matching record's `inc` and `count` in-place.

Our Sal port flattens this into two separate components: `A` keyed
only by `(elem, add_ts) → innate_value`, and a standalone
`I : set (elem, inc_ts, amount)` for increments. This was a
deliberate simplification documented in the CRDT file's docstring
(`Add_Win_Priority_Queue_CRDT.lean:41–49`), made to keep
`do_`-level commutativity and `rc := Either` everywhere. The
trade-off:

- **Preserved:** Add-Wins resolution of Add vs concurrent Rmv;
  commutativity / associativity / idempotence of `merge`; LWW
  semantics for innate.
- **Lost:** the paper's per-record accumulation of `inc` and `count`,
  and therefore the Most-Change-Win acquired-value rule.

## The Most-Change-Win rule (paper) vs sum (Sal docstring)

Paper Algorithm 2 line 8, the `inc` selector inside `get_pri`:

```
let inc : (e, t, x, inc, count) ∈ A ∧ (e, t) ∉ R
       ∧ ∀t' : ((e, t', x', inc', count') ∈ A ∧ (e, t') ∉ R) → count' ≤ count
```

In words: pick the live record with the **maximum `count`** (the
record that has accumulated the most change magnitude). The paper
calls this **Most-Change-Win** and motivates it in §3.3.2 as
"preserving the user's intention as much as we can."

Our Sal CRDT docstring at `Add_Win_Priority_Queue_CRDT.lean:55` says

> `acquired(e) := Σ over I records with elem = e, amount`

which is **a sum over all matching records**, not paper's MCW. We
never formalized `acquired` as a Lean definition or theorem, so
there is no verified-incorrect statement leaking — but the docstring
is misleading and should be tagged as "intent: not specified by the
paper, simplified bookkeeping" in a follow-up cleanup. (It cannot
actually implement MCW with our state shape: there is no per-record
`count` field to maximize over.)

## Intent-preservation: paper claims ↔ Lean theorems

| Claim | Paper anchor | Lean theorem (CRDT) | Lean theorem (MRDT) | Faithful? |
|---|---|---|---|---|
| **Lookup convergence.** Equal states give equal `lookup`. | Implicit in §2.1 strong eventual consistency | `lookup_convergent` | `lookup_convergent` | ✅ |
| **Add-wins headline.** A concurrent Add survives a Rmv whose snapshot does not include its record. | Alg 2 lines 30–35 (`prepare` snapshots `O`, `effect` unions `{e} × O` into `R`) | `add_wins_over_concurrent_rmv` (premise: `D (e, ts) = false`) | `add_wins_over_concurrent_rmv` (premise: `(ts, e, v) ∉ l`, sits in `a \ l`) | ✅ |
| **Lookup after Add.** Fresh Add immediately makes the element live. | Alg 2 line 14 effect | `lookup_after_add` | `lookup_after_add` | ✅ |
| **Innate is LWW (uniqueness).** Max-`t` live record uniquely determines the innate value. | Alg 2 line 7 (`get_pri`'s `x` selector) | `innate_record_unique` returns `ts1 = ts2 ∧ v1 = v2` | `innate_record_unique` returns `ts1 = ts2` | ✅ The MRDT version returns just `ts1 = ts2` because in the set-of-triples representation a separate `mem`-uniqueness step is needed for `v1 = v2`; can be added on demand. |
| **Innate convergence.** Equal states give equivalent `is_innate_record` predicates. | Implicit in §2.1 | `is_innate_record_convergent` | `is_innate_record_convergent` | ✅ |
| **Acquired-value resolution.** | Alg 2 line 8 (`get_pri`'s `inc` selector via max `count`) | `is_acquired` (propositional `Σ` via list witness) + `is_acquired_convergent` | `is_acquired` + `is_acquired_convergent` | ⚠️ Faithful **under the flat-observation simplification** — see below. |
| **`get_pri` = innate + acquired.** | Alg 2 line 9 (`return x + inc`) | `is_priority` + `is_priority_convergent` | `is_priority` + `is_priority_convergent` | ✅ Composes innate-LWW with `is_acquired`. |
| **`get_max`** — peek-max well-defined under concurrency. | §2.2 query op | `is_get_max` + `is_get_max_convergent` | `is_get_max` + `is_get_max_convergent` | ✅ Propositional spec: `e_max` is live and every other live element's priority is ≤ `p_max`. |
| **`empty()`** | §2.2 query op | `is_empty` + `is_empty_convergent` + `is_empty_init` | `is_empty` + `is_empty_convergent` + `is_empty_init` | ✅ Renamed from `empty` to avoid collision with `Set_Extended.empty`. |
| **Inc creates an inc-record.** | Alg 2 lines 24–28 (effect of `inc`) | `inc_creates_inc_record` | `inc_creates_inc_record` | ✅ Sanity tying `Inc` to its observable effect. |

## Concurrency premise — state-based stand-in

The paper's Add-Wins claim is a happens-before claim: "if Add
happens before Rmv, the Rmv's snapshot includes the Add and the Add
is removed; if Add is concurrent with or after Rmv, the snapshot
does not include the Add and the Add survives." In the state-based
model a happens-before relation cannot be recovered from a merged
state, so we use the same convention as `peritext-vs-paper.md`:

- **CRDT side:** the concurrency premise is encoded as
  `D (e, ts) = false` — the prepare-time snapshot literally does not
  contain the Add's record. This is the closest observable analogue.
- **MRDT side:** the premise is encoded as
  `mem (ts, e, v) (Prod.fst l) = false` — the Add's record was not
  present in the LCA `l`, so it sits in `a \ l` and bypasses the
  Rmv branch.

## Closing the gap — what's now formalized

The four paper queries (`empty`, `lookup`, `get_pri`, `get_max`) all
have propositional Lean specs in our readside files, with
convergence theorems for each. Definitions are relational rather
than `noncomputable` functional to sidestep `Finset` machinery —
the codebase deliberately avoids `Finset` to keep `grind` and
`aesop` effective on the convergence VCs. The list-witness pattern
in `is_acquired` enumerates the matching inc-records via a `Nodup`
list bijecting with the I-component-restricted-to-`e`; the sum
over the list is a permutation invariant, so `v` is unique up to
the spec.

### Why our acquired-Σ rule is paper-faithful in our state model

Paper's MCW (Alg 2 line 8) selects the live add-record with the
maximum accumulated change-magnitude `count` and returns its
`inc`-field. The paper's per-record `count` is incremented by `|i|`
each time an `inc(e, i)` op observes that record at prepare time
(Alg 2 line 24).

In our flattened state model, every `Inc e amount` writes a single
global tuple to `I`; there is no per-record observation set. This
is equivalent to assuming **every live add-record for `e` observes
every inc-record for `e`** — in the paper's model, that would mean
every record has the same `count` (Σ |amount| over all incs for `e`)
and the same `inc`-field (Σ amount over all incs for `e`). Under
that universally-observed assumption, MCW selects any live record —
they're all tied — and returns the inc-field, which is the sum.

So `is_acquired = Σ amount` is paper-faithful for our state model.
It diverges from the paper only in scenarios where the paper would
distinguish records by their observation history; our flat I-set
collapses those distinctions deliberately, in exchange for
`rc := Either` everywhere and the simpler `do_` that gives us all
24 RA-linearizability VCs by `by sal`.

### Still deferred

- **Per-record observation tracking.** The full paper algorithm
  (where different add-records can have different `count`/`inc`
  fields) requires migrating `A` to `map (e, t) → (Option ℕ × set
  (inc_op_id × ℤ))` and reworking `do_`/`merge`/the 24 VCs. The
  flat-observation variant is sufficient for any application that
  doesn't rely on the MCW distinction.
- **Increment-record convergence under merge.** A theorem that `Inc`
  records accumulate consistently across replicas is implicit in
  the pointwise-union merge of `I`, but is not yet stated separately.
- ~~**`Inc` priority intent theorem.**~~ Closed: `inc_increases_acquired`
  is now proved on both CRDT and MRDT sides via the list-witness
  `cons` construction. Premise: `(e, ts, amount) ∉ I` in the
  pre-state (true by `distinct_ops` for any reachable state).
  Conclusion: `is_acquired s e v → is_acquired (do_ s (Inc e amount)) e (v + amount)`.

## Files at a glance

| Purpose | Path |
|---|---|
| State-based CRDT (24 VCs) | `Sal/CRDTs/Add_Win_Priority_Queue/Add_Win_Priority_Queue_CRDT.lean` |
| State-based MRDT (24 VCs, with Blaster admits) | `Sal/MRDTs/Add_Win_Priority_Queue/Add_Win_Priority_Queue_MRDT.lean` |
| CRDT read-side (full paper query set) | `Sal/CRDTs/Add_Win_Priority_Queue/Add_Win_Priority_Queue_ReadSide.lean` |
| MRDT read-side (full paper query set) | `Sal/MRDTs/Add_Win_Priority_Queue/Add_Win_Priority_Queue_ReadSide.lean` |
| Op-based porting reference | `docs/porting-op-based-crdts.md` |
| Local copy of the paper | `_references/3609437.3609452 (1).pdf` |
