# Neem paper and F* induction audit

Audit of the checked-in references, 2026-10-08. Source locations below are
relative to the repository. This is source inspection, not a fresh F* run.

## What the artifact actually checks

`_references/neem_fstar_repo/code/interface/App_mrdt.fsti` is a manually written
interface of local proof obligations, not an implementation of the generic
soundness theorem or a VC generator. Its only recursive function is `apply_log`
(45–48). All state operations, equivalence, policy and lemma obligations are
declared with `val`. Application `App_mrdt.fst` files provide their implementations.
The unit bodies `let lemma ... = ()` are SMT-checked against the interface's
`Lemma (requires ...) (ensures ...)` contracts; they are not runtime tests and
should not be called unproved axioms merely because their bodies are unit.
Conversely, checking the interface alone does not discharge these contracts.

`verify_mrdts.sh:2–14` checks/caches the interfaces and collection implementations;
36–45 checks each application implementation with the shared include directory
and exits on application failure. Both OR sets are listed at 26–27. Z3 is pinned
to 4.13.3. Existing `log/mrdt_output:58–62,99–100` reports verification of the two
OR sets (3 s and 357 s); this audit did not reproduce that run. The script has no
`set -e`, so its preliminary interface commands are less robust than its explicit
application failure checks. No generic operational semantics or generic
VC-to-linearizability soundness proof is implemented in the inspected F* code
tree. The paper supplies that argument in prose.

## Exact obligation inventory

Interface line references are to `App_mrdt.fsti`.

| Family | Members and starting lines | Count |
|---|---|---:|
| Equivalence | `symmetric` 14, `transitive` 18, `eq_is_equiv` 22 | 3 |
| Policy restrictions | `rc_non_comm` 64, `no_rc_chain` 68, `cond_comm_base` 72, `cond_comm_ind` 77 | 4 |
| Merge algebra | `merge_comm` 85, `merge_idem` 88 | 2 |
| Two-operation induction | `base_2op` 93, `ind_lca_2op` 98, `inter_right_base_2op` 105, `inter_left_base_2op` 113, `inter_right_2op` 119, `inter_left_2op` 128, `inter_lca_2op` 137, `ind_right_2op` 145, `ind_left_2op` 151 | 9 |
| One-operation induction | `base_1op` 159, `ind_lca_1op` 162, `inter_right_base_1op` 168, `inter_left_base_1op` 175, `inter_right_1op` 181, `inter_left_1op` 189, `inter_lca_1op` 197, `ind_left_1op` 206, `ind_right_1op` 211 | 9 |
| Zero-operation collapse | `lem_0op` 220 | 1 |

Thus **21 merge obligations**, **25 including policy restrictions**, **28
including equivalence**. The obsolete skill's blanket “24 VCs” must not determine
the count for this interface or the current production framework.

Paper `lemmas.tex:155–225` gives nine generic induction schemata. Its concrete
appendix table `appendix.tex:860–1034` lists two merge algebra obligations,
nine two-op, eight one-op (no mirrored right one-op suffix extension), and seven
zero-op obligations: **26 merge obligations as printed**. F* adds the mirrored
one-op suffix obligation and collapses seven zero-op obligations into one
stronger unconditional equation (explicit comment at interface 216–217).
These are distinct inventories, not interchangeable counts.

## Paper's nested induction and actual hypotheses

`lemmas.tex:226–236` explicitly freezes the events in the template sequences
and quantifies the local VC variables universally. “All sets empty” is modulo
these frozen events. It builds feasible states in this order:

1. Initial state and common-before-local LCA prefix `L_top^b`.
2. LCA events after some local event `L_top^a`.
3. For each such LCA event, left/right local blocks before it `L_i^b`:
   first an `rc` predecessor, then further events before that predecessor.
4. Left/right local suffixes after LCA `L_i^a`.

This is a logical proof decomposition. It is not an induction tactic in F*.
For example, write `u_o(s)=do s o` and

```
Q2(l,a,b;p,q) := eq (merge l (u_p a) (u_q b))
                        (u_p (merge l a (u_q b)))
Q1(l,a,b;p)   := eq (merge l (u_p a) b) (u_p (merge l a b))
```

The explicit F* IHs are:

| Obligation | IH(s), then extension |
|---|---|
| `ind_lca_2op` | `Q2(l,l,l;p,q)` **and** `Q1(u_h l,u_h l,u_h l;p)`; conclude `Q2(u_h l,u_h l,u_h l;p,q)` |
| `inter_lca_2op` | `Q2(l,a,b;p,q)` **and** `Q1(u_h l,u_h a,u_h b;p)`; conclude `Q2(u_h l,u_h a,u_h b;p,q)` |
| `inter_right_base_2op` | `Q2(l,a,b;p,q)`, `Q2(l,a,u_r b;p,q)`, `Q2(u_h l,u_h a,u_h b;p,q)`; conclude `Q2(u_h l,u_h a,u_h(u_r b);p,q)` |
| `inter_left_base_2op` | `Q2(u_h l,u_h a,u_h b;p,q)`; conclude `Q2(u_h l,u_h(u_r a),u_h b;p,q)` |
| `inter_right_2op` | `Q2(u_h l,u_h a,u_h(u_r b);p,q)`; replace `b` under `r` by `u_o b` |
| `inter_left_2op` | `Q2(u_h l,u_h(u_r a),u_h b;p,q)`; replace `a` under `r` by `u_o a` |
| `ind_left_2op` / `ind_right_2op` | `Q2(l,a,b;p,q)`; replace `a` by `u_o a` / `b` by `u_o b`, **before** the fixed last event |
| `ind_lca_1op` | `Q1(l,l,l;p)`; conclude `Q1(u_h l,u_h l,u_h l;p)` |
| `inter_left_base_1op` | `Q1(u_h l,u_h a,u_h b;p)`; insert `r` before `h` in `a` |
| `inter_right_base_1op` | same common-event IH, plus `rc(r,p)=Fst_then_snd -> Q2(l,a,b;p,r)`; insert `r` before `h` in `b` |
| `inter_left_1op` / `inter_right_1op` | corresponding already-inserted-`r` one-op IH; insert `o` before `r` |
| `inter_lca_1op` | `Q1(u_i l,u_i a,u_i b;p)` **and** `Q1(u_h l,u_h a,u_h b;p)`; conclude `Q1(u_h(u_i l),u_h(u_i a),u_h(u_i b);p)` |
| `ind_left_1op` | `Q1(u_h l,a,u_h b;p)`; replace `a` by `u_o a` |
| `ind_right_1op` | mirrored equation peeling the last event of `b`, with common `h` on `l,a`; insert `o` before that last event |

The base equations use `init_st`. `lem_0op` has no IH and says
`merge (u_h l) (u_h a) (u_h b) ≈ u_h (merge l a b)` for arbitrary states.
The conditional commutation IH is a separate log equation (77–81): equality
after `p;q;log;h` versus `q;p;log;h`, extended by inserting another event
immediately before final `h`. Its arbitrary inserted event has no freshness
guard in that signature.

The active appendix proof is `appendix.tex:377–537`; it inducts on executions,
then local suffix size, LCA-after-local size, and the per-LCA local blocks.
Its smaller-merge IH constructs a linearizing sequence, which is extended by
the peeled last event (e.g. 500–529). Large subsequent alternate drafts at
539–712, 717–765 and 770–859 are inside LaTeX `comment` environments. In
particular, pending `VS` annotations there are not active published proof text.
The paper's main soundness statements are `lemmas.tex:142–144,238–239`.

## Guards: do not silently copy the paper table

F* `op_t` is `(positive timestamp,(natural replica ID,application op))` (30).
`distinct_ops` means **different timestamps**, not merely different triples (34).
All relevant tuples in merge induction lemmas are pairwise timestamp distinct.
Two-op equations generally require different replicas for `p,q`; intermediate
blocks also require different replicas for `r,h`. These provenance conditions
are absent from the printed algebra table.

Specific differences requiring a derivation rather than blind translation:

- `ind_lca_2op:101` adds the one-op IH at the extended LCA, marked `EXTRA!!`.
- `inter_lca_2op:141` likewise adds a one-op IH at the extended LCA.
- Left intermediate two-op base/extension (114,129) and right suffix two-op
  extension (146) require **strict** `rc(q,p)=Fst_then_snd`; the corresponding
  paper table rows allow “strict order or commute”.
- `inter_right_base_2op:108–110` has three IH equations where the printed
  appendix row has one.
- Intermediate further-predecessor steps require
  `not Either(rc(o,r)) or Fst_then_snd(rc(o,h))`, plus `rid(o) != rid(h)`
  (121–125,130–134,183–186,191–194). The generic main-paper table only prints
  noncommutation; appendix left two-op and one-op rows print the disjunction.
  Appendix right two-op row at 917–922 is visibly inconsistent: it omits that
  guard and repeats a left-side-looking equation. Treat it as a source
  discrepancy, not executable authority.
- `ind_lca_1op:164` adds `rid(p) != rid(h) or ts(h) < ts(p)`, marked `EXTRA!!`.
  This matters for the efficient OR set: adding again for the same replica and
  element overwrites its old timestamp.
- `inter_right_base_1op:171` adds the conditional two-op IH.
- `inter_lca_1op:197–204` requires two existential predecessor guards and two
  common-event IHs, yielding a two-common-event composition; the paper row
  at 955–961 prints a single existential and a different asymmetric state
  presentation. Establish equivalence or keep interfaces distinct.
- `rc_non_comm:65` is guarded by timestamp distinctness and unequal replica
  IDs. This restriction is crucial: efficient same-replica Adds to the same
  element do not commute even though `rc` returns `Either`.

## The two OR sets

Exact OR set `code/mrdts/OR-set/App_mrdt.fst:6–19,38–56` stores a predicate set
of `(timestamp,element)`, equality is actual state equality, Add inserts a fresh
tag, Rem filters all tags for that element, and merge is
`(l ∩ a ∩ b) ∪ (a \\ l) ∪ (b \\ l)`. `rc` orders same-element Rem before Add
(44–48). Its helper proves noncommutation using the empty state as witness
(61–67). All merge/induction bodies are unit, with SMT options
`--z3rlimit 100 --max_ifuel 3` (60–119).

Efficient OR set `code/mrdts/OR-set-efficient/App_mrdt.fst:11–17,43–49` stores
triples `(replica,timestamp,element)`. Add first filters the same
`(replica,element)`, then inserts the new tag. Rem filters the element across
all replicas. It uses the same tuple-level merge formula (69–74), policy
(63–67), and equality (23–24). The asserted example at 51–60 explicitly
checks repeated same-replica Add overwrites and different-replica Add retains
both witnesses. It does **not** encode per-replica uniqueness as a refinement
of `concrete_st`; it is a state-shape consequence of well-formed executions.
Neither artifact is a log-carrying wrapper and neither computes max timestamps
inside merge. The policy/guard and valid-history reasoning must explain the
bounded-state claim; a tuple-union formula alone does not establish it for
arbitrary malformed inputs.

The collection substrate is predicate sets with functional extensionality:
`code/interface/Set_extended.fst:3–18`. Its membership and equality lemmas
also have concrete checked unit implementations (20–35). This substrate is
close to Sal's pointwise set reasoning, but Lean proofs remain kernel checked.

## Mapping to current Sal and implementation prescription

`Sal/MRDTs/Paper1/ConcreteJoin.lean:39–72` has five **different**, indexed
equations: guarded commutativity, initial join, causal delta, local
redistribution, and shared redistribution. Its `Context:8–18` carries support,
metadata closure, semantic maximality and metadata maximality. Local/shared
fields receive representations of reconstructed sides and the smaller union
merge. These are evidence from the outer finite-union induction, not global
unrestricted join assumptions. `JoinAtSize:97–103` exposes that outer IH.

There is no direct 21-to-five projection:

- Neem commutativity implies Sal's guarded equation when equality is actual
  equality, but Neem idempotence is not Sal's arbitrary represented initial
  join (`merge init init s = s`).
- Neem one/two-op equations move `do` through merge. Sal local/shared
  equations redistribute nested **causal merges** and use indexed states.
  A bridge must first obtain causal reconstruction equations and identify the
  histories represented by these terms.
- Neem's universal state equalities and finite frozen-event IHs can guide
  auxiliary equations, but Sal's metadata scheme and `Representation` need
  their own construction and preservation proofs. Support, timestamp
  freshness, per-replica issuance and maximality must justify each extra F*
  guard if using the artifact's weaker local obligations.

Concrete next step: choose one Sal field and write an explicit proposition
for each needed reconstruction/one-step update case, with all representation
indices and guards. Expose existing representation evidence by its inductive
constructors or replay equations; select a genuine decreasing history
parameter; derive update/merge equalities pointwise; then assemble that field.
Do not recursively destruct arbitrary state terms and call it Neem induction.
Do not introduce a universal `Join` premise to make the assembly easy. Keep
the outer smaller-union IH and the inner history-building IH distinct.

For an exploratory Lean port of **Neem itself**, mirror `Q1/Q2`, the exact F*
guards, and the explicit extra IHs above in a separate interface first. Prove
why feasible histories supply those IHs and guards before claiming generic
soundness. A tactic may unfold selected constructors and normalize these
finite equations, but its soundness is inherited from the Lean proof it
constructs; no induction automation was found in the F* artifact.
