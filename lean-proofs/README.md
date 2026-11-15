# lean-proofs

The MRDT proofs of the paper, restructured into the three-way split used by
the reference F* development, with every name taken from the paper.

Eleven implementations are restructured, covering ten rows of Table 1:
Counter, Grow-only set (mathematical and enumerable carriers), Grow-only map,
LWW register, OR-set, Efficient OR-set, Set-wins multimap, Enable-wins flag,
Disable-wins flag and Remove-wins set.

One further row, the Multivalue register, is defined but **not** certified,
for the reason set out under **The omitted conjunct** below.

They divide along the two axes Table 1 records.

* The first four have `rc` empty, no issuance guard and no execution-scoped
  bridge, so they fit the `Obligations` bundle and the unrestricted premise
  `SpecSound`.
* The **LWW register** is the first that does not fit the unrestricted
  premise: its answer is the greatest write key, which an arbitrary replay
  order does not explain, so it uses the scoped premise `HistorySound` and
  selects a chronological witness. That is the `E = Y` column of Table 1.
* The **OR-set**, the **set-wins multimap** and the **two flags** have a
  nonempty `rc`, so they prove `Laws(D_type)` themselves, and they prove the
  join lemma directly rather than through the five VCs.
* The **two flags** are the same algorithm at opposite polarities, which is
  why Table 1 gives them identical counts. Each row carries its own full
  development, specialised to its initial bit and to whether the client reads
  that bit or its negation.
* The **remove-wins set** is the first row with an **issuance guard**, the
  `I = Y` column of Table 1. Timestamp `0` is reserved for the tags its
  initial state carries, so `G(e, s) <=> 0 < time(e)`, and the join lemma
  consumes that through `MintHonest`.

No datatype in the artifact is modified. The remaining rows need more than
this; see **Scope** below.

## Layout

```
LeanProofs/
  Interface/                     common to every implementation
    Implementation.lean          MRDTType and the tuple D_type = <Sigma, sigma0, do, merge, query, rc>
    Laws.lean                    Laws(D_type), common to both routes
    VCRoute.lean                 the canonical join laws and Obligations
    DirectRoute.lean             the join lemma's statements and DirectObligations
  Metatheory/                    proved once, for every implementation
    Adequacy.lean                Laws + VCs => the join lemma
  Soundness/                     proved once, for every implementation
    Common.lean                  Definition 4, and the names its two clauses share
    LinearExtension.lean         clause 1: pi is a linear extension of (E, lo^C_E)
    SequentialSpec.lean          clause 2: ops(pi) . (q => b) is in Spec
    RALinearizability.lean       the adequacy theorem, which needs both clauses
  Implementations/               one folder per implementation
    FlatCounter/
      Definition.lean            the counter's D_type, no proofs
      Laws.lean                  the obligations, each closed by omega
      LinearExtension.lean       issuance, the join lemma from the obligations
      SequentialSpec.lean        Spec, the abstraction function, SpecSound
      Certificate.lean           Definition 4
    GrowOnlySet/
      Definition.lean            the set's D_type, no proofs
      Laws.lean                  the obligations, each a set identity
      LinearExtension.lean       issuance, the join lemma from the obligations
      SequentialSpec.lean        Spec, SpecSound
      Certificate.lean           Definition 4
    FiniteGrowOnlySet/
      Definition.lean            the enumerable (Finset) carrier
      Laws.lean                  the obligations, each a Finset identity
      LinearExtension.lean       issuance, the join lemma from the obligations
      SequentialSpec.lean        Spec, SpecSound
      Certificate.lean           Definition 4
    FlatGrowOnlyMap/
      Definition.lean            the map's D_type, no proofs
      Laws.lean                  the obligations, each a Boolean identity
      LinearExtension.lean       issuance, the join lemma, the replay lemma fold_eq
      SequentialSpec.lean        Spec, SpecSound
      Certificate.lean           Definition 4
    LWWRegister/
      Definition.lean            the register's D_type, no proofs
      Laws.lean                  the obligations, each a max lemma
      LinearExtension.lean       issuance, the join lemma from the obligations
      SequentialSpec.lean        Spec, the chronological witness, HistorySound
      Certificate.lean           Definition 4
    ORSet/
      Definition.lean            the OR-set's D_type, rc nonempty
      Laws.lean                  RC-NON-COMM, NO-RC-CHAIN, COND-COMM
      LinearExtension.lean       liveness and the direct join lemma
      SequentialSpec.lean        Spec, the view function, SpecSound
      Certificate.lean           Definition 4
    SetWinsMap/
      Definition.lean            the multimap's D_type, rc nonempty
      Laws.lean                  RC-NON-COMM, NO-RC-CHAIN, COND-COMM
      LinearExtension.lean       liveness and the direct join lemma
      SequentialSpec.lean        Spec, the view function, SpecSound
      Certificate.lean           Definition 4
    EnableWinsFlag/
      Definition.lean            the flag's D_type, enable wins, rc nonempty
      Laws.lean                  RC-NON-COMM, NO-RC-CHAIN, COND-COMM
      LinearExtension.lean       counters, liveness, issuance, the direct join lemma
      SequentialSpec.lean        Spec, active_foldl, SpecSound
      Certificate.lean           Definition 4
    DisableWinsFlag/
      Definition.lean            the flag's D_type, disable wins, rc nonempty
      Laws.lean                  RC-NON-COMM, NO-RC-CHAIN, COND-COMM
      LinearExtension.lean       counters, liveness, issuance, the direct join lemma
      SequentialSpec.lean        Spec, active_foldl, SpecSound
      Certificate.lean           Definition 4
    RemoveWinsSet/
      Definition.lean            the set's D_type, rc nonempty, issuance guard
      Laws.lean                  RC-NON-COMM, NO-RC-CHAIN, COND-COMM
      LinearExtension.lean       liveness, issuance, the scoped join lemma
      SequentialSpec.lean        Spec, the view function, SpecSound
      Certificate.lean           Definition 4
    EfficientORSet/              certified outside Interface/, see below
      Definition.lean            D_type, rc, Spec, sequential correctness
      History.lean               Represents, and that it survives update and merge
      Virtual.lean               the representation invariant at virtual merge bases
      Certificate.lean           RepConfig on reachable configurations, VerifiedMRDT
    MVRegister/                  defined, not certified
      Definition.lean            the row's D_type, for an arbitrary rc
```

The split is enforced by content, not only by folder. `Interface/` and
`Metatheory/` name no datatype. `Implementations/FlatCounter/` never mentions
a configuration, an execution, `lo^C_E`, `can`, or the join lemma; the two
nonempty-`rc` folders do mention them, because they prove the join lemma
themselves.

Every declaration is a definition or a proof the paper calls for. There are
no tests, no concrete executions and no `decide` goals.

## Paper terms

Section 3, the implementation tuple. `Impl` is the paper's six-tuple field
for field, and `MRDTType` is the paper's `type`. Lean reserves the bare name
`Type`, hence `MRDTType` for the structure; the variable is `type`.

| paper              | here                 |
| ------------------ | -------------------- |
| `type`             | `MRDTType`           |
| `O_type`           | `MRDTType.OType`     |
| `Q_type`           | `MRDTType.QType`     |
| `Val_type`         | `MRDTType.ValType`   |
| `E = T x R x O_type` | `MRDTType.Event`   |
| `D_type`           | `Impl type`          |
| `Sigma`            | `Impl.Sigma`         |
| `sigma0`           | `Impl.sigma0`        |
| `do`               | `Impl.do_`           |
| `merge`            | `Impl.merge`         |
| `query`            | `Impl.query`         |
| `rc`               | `Impl.rc`            |
| `time(e)`, `rep(e)` | `Impl.time`, `Impl.rep` |
| `pi(sigma)`        | `Impl.applyList`     |
| `e1 <-> e2`        | `Impl.Commutes`      |
| `o1 --rc--> o2`    | `Impl.RcBefore`      |
| `e1 --rc--> e2`    | `Impl.EventRcBefore` |
| `rc_res`           | `OrderResult`        |

`rc` relates **operations**, because every law of Section 4 is stated over
operations. `Impl.EventRcBefore` is the lifting to events that Section 3
writes `e1 --rc--> e2`, and `Interface.policy` is the same relation in the
form the framework's Definition 4 is indexed by.

`Impl` carries two fields the paper leaves implicit, `decSigma` and
`decOType`, both marked as Lean bookkeeping in their docstrings.
`Impl.toMRDTSig` sends the tuple to the shared framework's representation;
nothing else in this development mentions `MRDTSig`.

Section 4, `Laws(D_type, Spec)`:

| paper             | here                   |
| ----------------- | ---------------------- |
| RC-NON-COMM       | `Laws.rc_non_comm`     |
| NO-RC-CHAIN       | `Laws.no_rc_chain`     |
| COND-COMM         | `Laws.cond_comm`       |
| SPEC-NON-COMM     | `FlatCounter.spec_non_comm` (it relates the implementation to `Spec`) |

Section 5, the canonical join laws:

| paper                      | here                                   |
| -------------------------- | -------------------------------------- |
| VC1 MERGE-COMM             | `CanonicalJoinLaws.vc1_merge_comm`     |
| VC2 MERGE-INIT             | `CanonicalJoinLaws.vc2_merge_init`     |
| VC3 LOCAL-REDISTRIBUTE     | `CanonicalJoinLaws.vc3_local_redistribute` |
| VC4 CAUSAL-DELTA           | `Metatheory.vc4_causal_delta` (derived, see below) |
| VC5 REDISTRIBUTE           | `CanonicalJoinLaws.vc5_redistribute`   |
| the join lemma, from the VCs | `Metatheory.joinLemma_of_vcs`        |
| the join lemma, proved directly | `ORSet.joinLemma`, `SetWinsMap.joinLemma`, `EnableWinsFlag.joinLemma` |
| what a direct-route row supplies | `Interface.DirectObligations` |
| what a VC-route row supplies     | `Interface.Obligations` |
| canonical correctness      | inside `Soundness.certifiedRA_of_laws`, via the vendored `certifiedRA_of_join_total` |

Section 4's Definition 4 and Section 5's adequacy theorem, in `Soundness/`:

| paper                             | here                            |
| --------------------------------- | ------------------------------- |
| over every certified execution    | `Soundness.CertifiedRA`         |
| the sequential premise `ops(pi) . (q => b)` in `Spec` | `Soundness.SpecSound` |
| Section 6's abstraction function `alpha` | `Soundness.Abstraction.alpha` |
| conditions (i), (ii), (iii) on `alpha` | `Abstraction.init`, `.step`, `.observes` |
| `alpha(pi(sigma0)) = ops(pi)(phi0)`, by induction | `Abstraction.fold` |
| the premise, from the three conditions | `Abstraction.specSound` |
| the same premise, scoped to an execution | `Soundness.HistorySound` |
| the adequacy theorem              | `Soundness.certifiedRA_of_laws` |
| its direct-route form             | `Soundness.certifiedRA_direct`  |
| its all-commuting specialisation  | `Soundness.certifiedRA`         |
| its scoped form                   | `Soundness.certifiedRA_scoped`  |

Lean reserves `do` and `Type`, so those two are spelled `do_` and
`MRDTType`. Everything else keeps the paper's spelling.

## Two deliberate departures from the paper

**The VCs are stated over arbitrary states.** The paper states VC2 to VC5
over canonical states, under `Admissible` and `Maximal` premises. This
development states the arbitrary-state strengthenings, which is what the
all-commuting family satisfies and what lets the counter close each one with
`omega`. VC1 is already over arbitrary states in the paper, so it is
reproduced verbatim. VC3 and VC5 have exactly the paper's equations with
`can(E)` replaced by an arbitrary state and `e(m)` by an arbitrary state `c`.

This is a real restriction, and five rows do not meet it.

* The OR-set, the set-wins multimap and the remove-wins set read `merge` as
  intersection where the ancestor holds a record and as union where it does
  not, and VC3 LOCAL-REDISTRIBUTE fails on the resulting Boolean at `l = 1`,
  `m = 0`, `x = 0`, `c = 1`, `y = 0`.
* The **enable-wins flag** fails earlier still: VC2 MERGE-INIT does not
  hold, because a set bit is only reachable together with a positive counter
  and the arbitrary-state law quantifies over `(0, true)` anyway.
* The **disable-wins flag** does satisfy VC2, since its initial bit is set,
  but its `rc` is nonempty, so `Obligations` cannot be formed at all.

All five therefore take the other route Section 5 allows and prove the join
lemma directly, as `Interface/DirectRoute.lean` asks. Both routes end at the
same theorem, so nothing downstream can tell them apart.

## The index of every statement is a configuration

Section 5 indexes every obligation by a configuration, and so does this
development. `Interface/DirectRoute.lean` defines the paper's statements,
`IsCan`, `JoinAtConfig` and `JoinConfig`, and every row's join lemma and
every signature in `Soundness/` is stated at one of them. The word "replay
context" appears in no statement here.

The vendored proof layer underneath runs on `C.replayContext`, the pair
`<L, vis>` with `L = headEvents`. That projection is an implementation
detail and appears in no statement this development owns.

### The omitted conjunct

The paper states RC-NON-COMM as

```
  forall o1 o2. not (o1 <-> o2) and o1 /= o2   <=>   o1 --rc--> o2 or o2 --rc--> o1
```

`Laws.rc_non_comm` here **drops the `o1 /= o2` conjunct**, following the
framework's uniform adapter `RestrictedLaws` rather than its event-guarded
contract `GuardedReplay.Laws`, which requires exactness only at distinct
timestamps on distinct replicas. All nine rows that go through `Interface/`
satisfy the stronger form, so nothing above depends on the difference.

Two rows do not, and the reason is structural rather than incidental: their
non-commutation is *internal to one operation*. In the efficient OR-set two
`add x` events issued by one replica do not commute, because each drops the
other's record; the uniform RC-NON-COMM demands an edge for the pair, the
only available edge is `add x --rc--> add x`, and NO-RC-CHAIN forbids it.
The optional register fails the same way, for the same reason.

The multivalue register fails for a stronger reason, and restoring the
conjunct would not help. Whether two writes commute depends on their
**timestamps**, not on their payloads, while RC-NON-COMM is an equivalence
over operations, so one instance of a pair forces an `rc` edge and another
forbids one.

### The third route

`EfficientORSet/` is certified anyway, and it is the one folder that does not
use `Interface/` at all. It proves neither `Laws` nor `ReplayLaws` --
`all_state_replay_laws_unavailable` records that the latter fails for its own
`rc` -- and reaches `VerifiedMRDT` another way.

Instead of a replay contract that holds at every state, it carries a
**representation invariant**. `History.Represents` relates a concrete state to
the events that produced it; `History` shows the relation survives `update`
and `merge`, `Virtual` shows it survives a virtual merge base, and
`Certificate.represented_of_mintCertifiedV` shows it therefore holds at every
configuration a certified execution can reach. Canonicity follows on those
configurations, which is all `ReplayAdequacyCertificate` needs.

This is the route the paper's artifact uses for the rows whose commutation is
not a function of their operations. It costs one more vendored framework
module, `Artifact/MRDTs/Metatheory/AdequacyResult.lean`.

The multivalue register would need a third contract again, a concurrent-event
scope, which this development does not vendor.

## Scope

Of Table 1's twenty-four rows, ten are here. What the rest need falls into
two kinds, and both kinds now have a route through `Metatheory/` and
`Soundness/`; what is missing is the datatype work, not the plumbing.

**A weaker replay contract** (efficient OR-set, optional register,
multivalue register, and every row whose commutation is not a function of its
payloads). The first two need `Metatheory/` and `Soundness/` rebuilt over
`GuardedReplay.Laws`; the third needs a concurrent-event scope that the
framework expresses separately again. Vendoring the artifact's own route for
the efficient OR-set would add five modules and about a thousand lines; its
guarded VC route, a hundred and seventeen modules and thirty thousand.

**An issuance guard** (`I = Y` in Table 1). Fifteen rows restrict which
events a replica may mint, and the remove-wins set is the first of them here.
Its `joinAt` takes a `MintHonest` premise and reads `0 < time(e)` off it, so
the route is now exercised rather than merely available; the remaining
fourteen rows need their own guards and their own uses of them.

**The `Representation` layer.** In the artifact every one of the fifteen
remaining rows is discharged through it: the VCs are stated against a
predicate relating states to event sets rather than against states directly.
That layer is not vendored here. It does not follow that each of those rows
needs it, since the artifact routes the set-wins multimap, both flags and the
remove-wins set through it too and the direct proofs here do without. Which
rows admit a direct argument is a question per datatype, open for all
fifteen.

## What each implementation supplies

| | Counter | Grow-only set | Grow-only map | LWW register | OR-set | Set-wins map | Flags | Remove-wins set |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `Sigma` | the integers | a set | a Boolean function | a write key or bottom | tagged add records | tagged bindings | a counter and bit per replica | tagged removal tags |
| `sigma0` | `0` | empty | constantly false | bottom | empty | empty | all rows clear or set | **one tag per element** |
| `do` | `z + delta(o)` | `S union {o}` | `S(x) or (x = o)` | `max(s, key(e))` | insert or filter | insert or filter | bump and set, or clear all | insert or filter |
| `merge` | `a + b - l` | `a union b` | `l(x) or a(x) or b(x)` | `max(a, b)` | the three-way OR shape | the three-way OR shape | sum the counters, compare for the bit | the three-way OR shape |
| `rc` | empty | empty | empty | empty | `remove x` before `add x` | `del k` before `set k v` | `reset` before `winning` | `add x` before `remove x` |
| issuance | `True` | `True` | `True` | `True` | `True` | `True` | `True` | **`0 < time(e)`** |
| join lemma | five VCs | five VCs | five VCs | five VCs | **direct** | **direct** | **direct** | **direct** |
| sequential premise | `SpecSound` | `SpecSound` | `SpecSound` | `HistorySound` | `SpecSound` | `SpecSound` | `SpecSound` | `SpecSound` |

Each supplies a `Definition.lean` (the tuple, no proofs), a `Laws.lean`, and
then the same three-file split as `Soundness/`: a `LinearExtension.lean` for
clause 1, a `SequentialSpec.lean` for clause 2, and a `Certificate.lean` that
combines them. Everything else is inherited from `Interface/`, `Metatheory/`
and `Soundness/`.

Most mark `type` `@[reducible]`, so that
`(type A).OType` unfolds during instance search; without
it the `Insert`, `Union` and `Membership` instances are not found. The
mathematical set and the Boolean map use `Classical.propDecidable` for
`decSigma`, since equality of mathematical sets and of Boolean functions is
not decidable.

The grow-only map is the only one whose specification uses a different
carrier from the implementation: `Spec` stores a finite set and answers with
its characteristic function, while the implementation stores the Boolean
function directly. The bridge is `fold_eq`.

The five nonempty-`rc` rows share one argument, stated in each folder for
its own records. A record is *live* in an event set when the event that
created it is in the set and no removal in the set observes that event.
Liveness depends only on the event set, so every replay of the set agrees,
and the merge becomes order-free; causal closure is what rules out the corner
where a branch holds a removal but not the creation it covers.

The remove-wins set is that argument in the mirror: removal tags in place of
add records, `add` in place of `remove`, and a client view that is a
complement. It adds one clause, because its initial state already carries a
tag for every element, so a tag can be live for a second reason: it is an
initial one and no `add` for its element is in the set. The issuance guard is
what keeps those two reasons apart. Timestamp `0` marks the initial tags, and
`MintHonest` says no minted event carries it, so a tag has exactly one
possible origin.

The flags are the same argument with the records replaced by counters. A
`winning` is live when no `reset` observes it, and `mergeFlag`'s test
`a.1 > l.1` says the branch holds a `winning` the ancestor did not, which is
what `(a \ l)` says in the OR-set. Two things are new there. The counter
half of the merge is inclusion-exclusion over the event sets, proved through
`winOf` as a `Finset`. And the bit half needs `vis` to be total on one
replica's events, because the two branches' surviving `winning` events are
issued by the same replica and the argument turns on which came first.

## Build

This is a self-contained Lake package. Build it from **this** directory:

```sh
cd lean-proofs && lake build
```

In an editor, open `lean-proofs` as its own workspace folder. The Lean
extension picks the project root from the workspace folder, so opening the
repository root instead gives these files the wrong search path and every
`import LeanProofs.*` fails with `unknown module prefix`.

The build reports that `joinLemma` and `raLinearizable` for
each implementation depend on `propext`, `Classical.choice` and `Quot.sound`,
and nothing else.

## The vendored framework

`Artifact/` holds the 41 modules of the paper artifact's shared framework and
metatheory that this development imports, copied verbatim:

```
Artifact/MRDTs/Framework/        10 modules   the signature, replay and merge laws
Artifact/MRDTs/Metatheory/       13 modules   correctness and the join machinery
Artifact/MRDTs/Paper1/           18 modules   RA-linearizability and the event bridge
```

They are copies and are never edited here. `artifact-provenance.json` records
each file's SHA-256 as shipped in `paper-artifact.tar.gz`, so drift from the
artifact is detectable:

```sh
python3 - <<'PYEOF'
import hashlib, json
prov = json.load(open('artifact-provenance.json'))['sha256']
bad = [f for f, h in prov.items()
       if hashlib.sha256(open(f,'rb').read()).hexdigest() != h]
print('changed:', bad or 'none')
PYEOF
```

Vendoring keeps this package independent of any sibling directory, so it
builds on a fresh clone with no setup step.
