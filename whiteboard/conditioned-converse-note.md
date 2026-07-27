# The conditioned converse of adequacy (task #122, phase 1)

## What this note settles

The flat converse (`whiteboard/converse-note.md`, mechanized in
`Sal/ConditionedMRDTs/Metatheory/Converse.lean`) settled the completeness
direction for flat MRDTs: canonical RA-linearizability, read as existence plus
convergence, forces the four flat core VCs on reachable states, the Join giving
three and the Join plus a fold-peel giving the fourth. This note attacks the
generalization to the conditioned framework: does conditioned
RA-linearizability (`IsRALinearizable3Eq`, RA-lin read up to the observational
equivalence `eqObs`, at every reachable `Inv`-satisfying configuration) imply
the four conditioned VCs of `sec:cvcs` (vc:disc, vc:comm, vc:inv, vc:merge)?

**Headline.** The conditioned converse is the *lift* of the flat converse's
core/shell split, with one new phenomenon (antitonicity) made concrete.

* **vc:merge (the conditioned Join) is FORCED** by existence plus
  convergence-up-to-`eqObs`, on reachable merge tuples, exactly as the flat Join
  was. PROVEN-ON-PAPER, modulo realizability of the Join's quantified domain.
* **vc:comm and vc:inv (the swap oracle) are NOT forced.** They are a
  *sufficient device* for convergence, strictly stronger than the convergence
  content RA-lin actually forces. The obstruction is structural and exact:
  convergence pins the local swap `EqSwap(a,b,s)` only when the pair `(a,b)` is
  lo-*maximal*; at a non-maximal incomparable pair it leaves a suffix-burdened
  equality that does not cancel. A finite witness (datatype RESET,
  `whiteboard/litmus/conditioned_converse_check.py`) inhabits the gap and, being
  machine-verified globally convergent up to `eqObs` (5418 configurations,
  51072 weakly-closed sets, zero non-convergent), is a clean refutation, not a
  per-config artifact: RESET is conditioned RA-linearizable at every reachable
  configuration yet its swap oracle fails at a non-maximal enabled pair. H-comm
  is REFUTED. PROVEN-ON-PAPER (structural) and PROVEN-BY-WITNESS (global).
* **vc:disc (the Inv discipline) is genuinely EXTRA.** Its universal
  Inv-preservation clause is not forced: the two-Inv witness (datatype GSET)
  gives one datatype, one RA-lin verdict, two Inv choices, and only one
  satisfies vc:disc. The generation discipline is presupposed by the ambient
  execution model, not derived. PROVEN-ON-PAPER (the direct conditioned analog
  of the flat shell VC3/VC4 surplus).

**Consequence for #123 (the rc-free recast).** The recast ADMITS the conditioned
layer, and it does so as a *sound abstraction of the sufficient swap-oracle
device*, not as a biconditional characterization of RA-lin. The convergence
engine (`thm:eqconv`, `eq_convergence`) is already order-agnostic in its order
relation, so stating vc:comm and vc:inv over an abstract acyclic antitone
arbitration `arb` (rc replaced by `arb`) goes through for the forward direction.
The bound is that RA-lin does not force this device back (the RESET witness), so
the recast is not a characterization of RA-lin, and the abstraction must carry
antitonicity, which is exactly where the gap lives.

Method, per project discipline: goals and falsifiable hypotheses first; every
claim marked PROVEN-ON-PAPER / CONJECTURED / OPEN; every claim tested against a
concrete instance (the rehoming RGA, the OR-set, and a purpose-built finite
datatype) rather than reasoned purely abstractly; the finite probe supplies its
own hand-derived expected values and is PASS+FAIL.

## Goals and the four falsifiable hypotheses

For each conditioned VC, the hypothesis is that conditioned RA-lin forces it on
the reachable-canonical domain. A refutation is a datatype that is conditioned
RA-linearizable yet reddens the VC on a reachable input; such a hit BOUNDS the
framework (an RA-lin datatype the VC set cannot certify) and is a first-class
result, not a failure.

* **H-merge.** Conditioned RA-lin forces vc:merge (the `eqObs`-Join
  `EqJoinLemma3C`) on reachable merge tuples.
* **H-comm.** Conditioned RA-lin forces vc:comm and vc:inv (the swap oracle
  `EqSwap` at enabled reorder states).
* **H-disc.** Conditioned RA-lin forces vc:disc (Inv discipline plus generation
  discipline).
* **H-recast (the #123 pivot).** The content conditioned RA-lin forces of
  vc:comm is exactly *acyclic, antitone, convergent up to `eqObs`*, with no
  rc-specific residue, so the abstract-arbitration recast admits the conditioned
  layer.

Prior expectations (to be tested, not assumed): H-merge YES; H-comm NO (the swap
oracle is a device, like the flat shell VC3); H-disc NO (Inv is datatype-chosen,
like the flat shell VC3/VC4 all-states surplus); H-recast YES-but-bounded.

## The conditioned RA-lin hypothesis, determined faithfully

The Lean `IsRALinearizable3Eq` (`Metatheory/GoodConfig3H.lean:297`) reads: for
every stored version `v` with `C.ver v = some (s, Ev)`, there exist a
representative `σ` with `Inv σ` and a list `π` that enumerates `Ev`, respects the
paper order `lo`, and folds raw from `init` to `σ` up to `eqObs`:

    ∃ σ, Inv σ ∧ s = ⟦σ⟧ ∧ ∃ π, listPermOf π Ev ∧ respects π lo ∧ (fold init π) ≈ σ .

This is *existence only* and *per configuration*, exactly the shape the flat
`IsRALinearizable3` had, now read up to `eqObs` and with the witness
representative required to satisfy `Inv`. As in the flat case it is too weak on
its own to be the converse hypothesis: it supplies neither the Join (a merge
lands on the canonical class of the union) nor convergence (folds are unique up
to `eqObs`, so the canonical class is a function). Following the flat converse's
determination of `CanonicalRALin3`, the faithful conditioned hypothesis is

**`CanonicalRALin3Eq`** = existence (`IsRALinearizable3Eq` at every reachable
`Inv`-configuration) together with

* **convergence up to `eqObs`**: on every reachable weakly-closed set whose sides
  are `Inv`-satisfying and generation-disciplined, all `loOnEq`-respecting raw
  folds are `eqObs`-equal, so the canonical class `σcan≈(E)` is well defined
  (`IsCanonicalStateEq` is single-valued up to `eqObs`).

Unlike the flat converse, we do *not* also assume the Join. The conditioned
framework already takes the Join as a primitive VC (vc:merge is `EqJoinLemma3C`),
and existence at reachable merge versions plus convergence *derives* it (below),
so packaging it in would be circular. This is the one place the conditioned
picture is cleaner than the flat one: vc:merge is a theorem of the hypothesis,
not a field of it.

`loOnEq` (`Metatheory/GenericEqQuotient.lean:425`) is `loOn` with `commutes`
replaced by `eqCommutesOn` (commutation up to `eqObs` quantified over
`Inv`-states); it retains the vis arm, the rc arm, and the absorber, and it is
antitone in the event set. `IsCanonicalStateEq` is a `loOnEq`-respecting raw fold
landing `eqObs`-equal to the state. `EqJoinLemma3C` is the `eqObs`-relaxed Join
over fully-closed `Inv` sides with a generation-discipline premise `GenDisc`.

## The core/shell lift: the map from the flat converse

The conditioned four VCs are a *repackaging* of the flat eight, and the converse
verdicts lift accordingly. This map is the organizing result of the note.

| flat VC (role)                            | conditioned VC              | flat converse verdict | conditioned verdict |
|-------------------------------------------|-----------------------------|-----------------------|---------------------|
| VC5,VC6,VC7,VC8 (delta core, reduce to Join) | vc:merge (Join taken directly) | core, FORCED via Join   | FORCED              |
| VC3 cond_comm_lift, VC4 mergeL_comm (commutation) | vc:comm + vc:inv (Inv-scoped) | shell, NOT forced       | NOT forced          |
| VC1,VC2 (rc pool) + all-states surplus    | vc:disc (Inv + generation)  | shell, NOT forced       | EXTRA / presupposed |

The conditioned framework performed the flat converse's forward reduction
(delta laws to Join) up front by taking the Join as vc:merge, and it lifted the
flat commutation shell VC3/VC4 to the Inv-conditioned swap oracle vc:comm plus
vc:inv, and the flat rc-pool plus execution discipline to vc:disc. At the flat
boundary (`Inv = app = ⊤`, `eqObs = =`) the conditioned VCs collapse to the flat
ones (`FlatGeneric_Bridge`): vc:comm becomes unconditioned commutation (flat
VC3/VC4), vc:inv becomes `J = ⊤`, vc:merge becomes the ordinary Join. So the
conditioned verdicts must, and do, agree with the flat verdicts there.

## The per-VC verdict table

| VC       | verdict                                    | confidence                       | concrete probe |
|----------|--------------------------------------------|----------------------------------|----------------|
| vc:merge | FORCED (reducible to existence+convergence) | PROVEN-ON-PAPER, mod realizability | RGA Join; GSET Probe B |
| vc:comm  | NOT forced (sufficient device)             | PROVEN-ON-PAPER + PROVEN-BY-WITNESS (global) | RESET Probe C; RGA delete-absorber |
| vc:inv   | NOT forced (device precondition + aux invariant) | PROVEN-BY-WITNESS (shares RESET) | as vc:comm; RGA born-applicability |
| vc:disc  | EXTRA (universal preservation) / presupposed (generation) | PROVEN-ON-PAPER          | GSET two-Inv Probe A; RGA Inv |

## vc:merge: FORCED (the conditioned Join from existence and convergence)

Take a reachable merge version with LCA `l` and branches `a, b`, event sets
`E1 ∩ E2`, `E1`, `E2` (the LCA lemma `lem:lca` gives the LCA set as the
intersection). Existence at the merge version says its state `mergeL(l,a,b)` is a
`loOnEq`-respecting raw fold of `E1 ∪ E2`, hence, by convergence up to `eqObs`,
`mergeL(l,a,b) ≈ σcan≈(E1 ∪ E2)`. Existence at the LCA and branches plus
convergence says `l ≈ σcan≈(E1 ∩ E2)`, `a ≈ σcan≈(E1)`, `b ≈ σcan≈(E2)`.
`eqObs`-congruence of `mergeL` (the `CongVC` field of the signature) rewrites the
literal stored states to the canonical folds, and chaining gives

    mergeL(σcan≈(E1 ∩ E2), σcan≈(E1), σcan≈(E2)) ≈ σcan≈(E1 ∪ E2) ,

which is `EqJoinLemma3C` at that tuple. This is the flat Join step of
`converse_VC6`/`_VC8` transported through `eqObs`-congruence and the LCA lemma,
so the derivation is the flat one with `=` relaxed to `≈`. **PROVEN-ON-PAPER.**

The one gap is domain. `EqJoinLemma3C` quantifies over any `GenDisc` fully-closed
`Inv` sides, not only over the specific merge tuples of one execution. This is
the flat converse's stated-versus-reachable subtlety. It closes if every
`GenDisc` fully-closed `Inv` pair is realized as a reachable merge tuple of some
honest execution (deliver `E1` to one replica, `E2` to another, merge). That
realizability is the conditioned analog of the flat converse's
reachable-canonical closure and it is standard, but it is not proved here, so the
domain-closure step is **CONJECTURED**.

Mechanized sharpening (`mergeRealizable_iff_join`, kernel-clean). The abstract
realizability statement `MergeRealizable` (every `GenDisc` fully-closed `Inv` tuple
has a canonical fold `u` of the union with `mergeL(s0,s1,s2) ≈ u`) is *equivalent*
to `EqJoinLemma3C` (the merge IS a canonical fold of the union): the forward is
`≈`-congruence, the reverse takes `u := mergeL(s0,s1,s2)` with reflexivity. Two
consequences. First, convergence is not consumed by the abstract step: the
`CanonicalRALin3Eq` hypothesis of `converse_vc_merge` is dead code, because the two
propositions are already interchangeable. Convergence does its real work on the
*reachable* side, where existence at the merge version says `mergeL(l,a,b)` is a
raw fold and convergence promotes it to `≈ σcan≈`. Second, "is `MergeRealizable`
dischargeable?" has a definite answer: no in general, because it is the datatype's
own merge=fold obligation, not a theorem about an arbitrary signature. So vc:merge
is forced in exactly the flat converse's reachability-relative sense (RA-lin asserts
every merge version is a fold of its event set); over the abstract tuple domain it
is not forced (the same abstract-versus-reachable gap the full flat converse
refutes). The flat `CanonicalRALin3` already carries `join` as an assumed field of
the RA-lin hypothesis with no apology; the conditioned "conjectured realizability
step" is that same Join under a different name.

Probe: the OR-set and the rehoming RGA both discharge their Join in production
(`ORSetE_join`, `RGA_EqJoin_NF`); the converse says RA-lin would recover it. GSET
Probe B confirms the checker forces the Join on a convergent datatype and detects
a Join violation (drop-branch merge) as a calibration negative.

## vc:comm and vc:inv: NOT forced (the antitone gap and the RESET witness)

vc:comm asks for the swap witness `EqSwap(a,b,s): do(do s a) b ≈ do(do s b) a` at
concurrent `a,b` and enabled `Inv`-states `s`. vc:inv scopes it: the joint
content of vc:comm and vc:inv is the *swap oracle* of the convergence engine
(`thm:eqconv`), consulted at a duplicate-free `loOnEq(E)`-respecting prefix `π`
and a pair `a,b ∈ E ∖ π` that is `loOnEq(E)`-incomparable and enabled at `π`
(every `loOnEq(E)`-predecessor already in `π`).

**The structural fact (PROVEN-ON-PAPER): convergence forces `EqSwap` only at
maximal pairs.** Two `loOnEq(E)`-respecting enumerations of `E` that differ by one
adjacent transposition of an incomparable pair `(a,b)` at position `π` are
`ρ ++ [a,b] ++ τ` and `ρ ++ [b,a] ++ τ` with `ρ` the prefix and `τ` the shared
suffix. Convergence gives

    fold(ρ ++ [a,b] ++ τ) ≈ fold(ρ ++ [b,a] ++ τ) ,

a *`τ`-burdened* equality: `foldτ(do(do s a) b) ≈ foldτ(do(do s b) a)` with
`s = fold(ρ)`. This equals `EqSwap(a,b,s)` only when `τ` is empty, that is when
`(a,b)` is `loOnEq(E)`-maximal. `foldτ` is not left-cancellable in general (a
later operation can merge two distinct states), so at a non-maximal pair
convergence leaves the local swap free. The convergence engine, by contrast,
needs `EqSwap` at every adjacent transposition, including non-maximal ones (it
bubbles events past each other), so the swap oracle is a strictly stronger
sufficient condition than the convergence it produces. This is the exact
conditioned analog of the flat definition-note's reading of the rc arm and the
absorber as sufficient devices rather than invariant content, and of the flat
converse's finding that the commutation VC3 is shell (not forced).

**Antitonicity sharpens where the gap lives.** `EqSwap` is owed at
`loOnEq(E)`-incomparable pairs, and by antitonicity `loOnEq` has *fewer* edges on
the larger set `E` (growing the set only adds absorbers). So a pair can be
incomparable in `E` (an absorber in `E ∖ E'` has cancelled its rc-edge) while
comparable in a local weakly-closed `E' ⊆ E`. At such a pair the local
convergence at `E'` cannot even state the swap (one of the two orders is not
`E'`-respecting), and the global convergence at `E` only offers the `τ`-burdened
equality. The gap is precisely the absorber-and-antitone corner the task flagged.

**The witness (datatype RESET, PROVEN-BY-WITNESS).** State is a log of values in
append order; `write v` appends; `reset` erases the log to a sentinel `Z`;
`read(s)` is the last element; `eqObs` compares reads; `Inv = app = ⊤`. Events
`a = write A`, `b = write B` are concurrent; `c = reset` sees both (`a → c`,
`b → c`). `c` is the classic add-remove absorber: it does not `eqObs`-commute
with `a` or `b` (a write before a reset is erased, one after survives), so it is
a legitimate `loOnEq` absorber of the `a → b` rc-edge and carries the vis-arm
edges `a → c`, `b → c`. In `E = {a,b,c}` the pair `(a,b)` is therefore
incomparable and non-maximal (both order before `c`). The datatype is convergent
up to `eqObs` on every weakly-closed subset (in `{a,b,c}` both extensions
`[a,b,c]`, `[b,a,c]` reset to `Z`), so it is conditioned RA-linearizable. Yet
`EqSwap(a,b,init)` is owed (incomparable, both enabled at the empty prefix) and
FAILS: `read([a,b]) = B ≠ A = read([b,a])`. So RESET is RA-lin while its swap
oracle reddens at a reachable enabled reorder pair. **H-comm is refuted.**

The verdict is that vc:comm and vc:inv are not forced by conditioned RA-lin. What
conditioned RA-lin does force is their convergence *consequence* (folds agree up
to `eqObs`), which is the `converges` field of the hypothesis; the local swap
device is extra over it, and RESET separates them.

vc:inv carries a second reason it is not forced: its auxiliary invariant `J` on
(state, pending-event) is a datatype-*chosen* certificate, in the same category
as `Inv` below. Two `J` choices that agree on enabled reorder states but differ
off them give the same RA-lin verdict and different vc:inv verdicts.

## vc:disc: EXTRA (the two-Inv witness)

vc:disc has two parts. The *generation discipline* (distinct timestamps, Lamport
monotonicity, fresh applicable birth) is carried by the `ConditionedConfiguration`
structure (`Framework/ConditionedExecutionModel.lean`), which is the ambient
object conditioned RA-lin quantifies over. It is therefore *presupposed* by the
statement of the converse, not something to derive from it, exactly as
reachability is presupposed in the flat converse's domain. The *invariant
clauses* are `Inv(init)` and preservation `Inv(s) ∧ app(o,s) ⟹ Inv(do(s,o))`.

`Inv(init)` is forced trivially: the initial version folds `[]` to `init`, and
the RA-lin witness representative `σ ≈ init` satisfies `Inv`, so `init` sits in
the `Inv`-quotient. Preservation is the load-bearing clause, and it is **EXTRA**.

**The witness (datatype GSET, PROVEN-ON-PAPER, machine-anchored).** Take the
grow-only set with `eqObs = =`. Every pair of ops commutes at every state, so
`loOnEq` is empty and canonical RA-lin holds *independent of `Inv`*. Now compare
two invariants:

* `Inv1 = ⊤`: preservation holds vacuously, vc:disc GREEN.
* `Inv2(s) = poison ∉ s`: preservation FAILS at `o = add poison` (applicable, `Inv2`
  holds, `Inv2(s ∪ {poison})` false), vc:disc RED.

Same datatype, same RA-lin verdict under both invariants, different vc:disc
verdict. So vc:disc is a property of the datatype's *chosen* `Inv`, not a
consequence of RA-lin. The failure lives off the reachable-canonical domain
(`poison` never appears in any canonical fold of an honest configuration), which
is why RA-lin cannot see it. This is the direct conditioned analog of the flat
shell VC3/VC4 having RA-linearizable violators at unreachable states, and it
confirms the task's prior: vc:disc is extra, and the extra content is the
universal preservation quantifier over `Inv`-states that no reachable fold
visits.

## The driving instance: the rehoming RGA

The tombstone-free rehoming RGA (`MRDT_Instances/RGA_Rehoming/`, capstone
`rga_RA_linearizable_final` producing `IsRALinearizable3Eq`) is the fully
conditioned instance, and each VC's verdict shows on it.

* **vc:merge.** The RGA discharges its `eqObs`-Join through `RGA_EqJoin_NF` and
  the merge-canonicity chain. The converse says RGA RA-lin recovers it: at a
  reachable RGA merge the branch and LCA states are `renderIds`-canonical of their
  event sets, `rgaCongVC'` rewrites, and the Join follows. FORCED, on the same
  realizability caveat. This matches the flat delta-core-is-forced verdict.
* **vc:comm and vc:inv.** The RGA is the natural home of the RESET witness. Its
  delete path is the absorber (a delete removes an element, reconciling
  concurrent orders while not commuting), and the memory record
  (`rga-loOnEq-causal-collapse`, `loona-vs-looneq-applicable`) already shows the
  RGA's swap oracle is discharged by specific rehoming and born-applicability
  lemmas, not recovered from convergence. So RGA RA-lin forces only the
  convergence consequence, not the RGA-specific `EqSwap`. NOT forced (CONJECTURED,
  consistent with the RESET miniature, which is a faithful model of the delete
  absorber). vc:inv's `J = applicable ∧ noopFeasible` (born-applicability) is the
  device precondition, likewise not forced.
* **vc:disc.** The RGA's `Inv = WfOpA` (well-formedness, nonzero ids, id
  monotonicity), preserved on applicable ops, is load-bearing for the RGA's own
  proof but not forced by RA-lin: the two-Inv argument transfers (a reachable RGA
  is RA-lin under any `Inv` agreeing with `WfOpA` on reachable states, and the
  universal preservation clause is surplus). EXTRA.

## The lighter probe: the OR-set at the flat boundary

The OR-set feasible tier (`ORSetE`, `applicable = ⊤`, `Inv = ⊤`, `eqObs = =`)
sits at the flat/conditioned boundary. There vc:comm is unconditioned
commutation (flat VC3/VC4), vc:inv is `J = ⊤`, vc:merge is the ordinary Join, so
the OR-set converse *is* the flat converse: vc:merge forced (flat Join),
vc:comm/vc:inv not forced (flat commutation shell). The OR-set's own absorber
(the add-remove cycle of `absorber_dichotomy_check.py`) is the flat instance of
the RESET mechanism, where dropping the absorber makes `loOn` cyclic and destroys
*existence*. So the OR-set confirms the boundary is consistent: the conditioned
verdicts reduce to the flat verdicts at `Inv = app = ⊤`, `eqObs = =`, and the
RESET witness is the `eqObs`-lift of the OR-set absorber.

## What it means for #123 (the rc-free recast)

#123 asks whether vc:comm admits the abstract-arbitration and antitone recast of
`ra-lin-definition-note.md`: replace `rc`/`loOnEq` by an arbitration relation
`arb` required only to extend vis-on-non-commuting and to be acyclic (and here
antitone) on reachable `Inv`-sets, and re-derive adequacy against `arb`.

**Answer: YES, the recast admits the conditioned layer, BOUNDED.** Two
observations decide it.

1. vc:comm's content is not rc-specific. `EqSwap(a,b,s)` is pure commutation up to
   `eqObs`; `rc` enters only through `loOnEq`, which *selects* the incomparable
   pairs at which `EqSwap` is owed. So vc:comm is arbitration-relative
   commutation: over an abstract `arb`, it reads "arb-incomparable enabled pairs
   `eqObs`-commute." The convergence engine `thm:eqconv` (`eq_convergence`) is
   already stated order-agnostically over an arbitrary relation `ℓ`, with
   `loOnEq` only one instantiation, so the swap oracle over an abstract `arb`
   feeds the same engine unchanged. The forward direction (adequacy against
   `arb`) is therefore framework-wide, and the mechanization is already factored
   for it.
2. The converse forces exactly the invariant content the recast keeps. Of
   vc:comm, conditioned RA-lin forces the *acyclic* part (else existence fails,
   no witness) and the *convergent up to `eqObs`* part (the `converges` field),
   and antitonicity is a free structural property of any set-relative
   arbitration. It does not force the local-swap device (the RESET witness). So
   the recast keeps precisely what RA-lin forces (acyclic, antitone, convergent)
   and drops precisely what it does not (the rc form and the specific swap), which
   is the correct abstraction.

**The bound.** The recast is a sound reformulation of the *sufficient* swap-oracle
device, not a biconditional characterization of RA-lin. RA-lin does not force
`arb`-commutation back (RESET), so no `arb`-form of vc:comm can be claimed
equivalent to RA-lin; it can only be claimed sufficient for it. And the
abstraction must carry antitonicity of `arb` in the event set, because the gap
between owed swaps (global incomparability) and available convergence (local
incomparability) is an antitonicity gap; an `arb` that is not antitone would
mis-scope the swap oracle. Within those bounds the recast is framework-wide: it
is not RGA-specific, since the driving obstruction (the delete absorber) is the
RESET mechanism, which is generic.

## The finite conditioned probe

`whiteboard/litmus/conditioned_converse_check.py` (stdlib only, PASS+FAIL, exit 0,
hand-derived expectations) anchors the three verdicts on concrete finite
datatypes:

* **Probe C (vc:comm not forced).** Datatype RESET, config `{a,b,c}`. Verifies:
  `a,b` do not `eqObs`-commute (a swap is owed); in `{a,b,c}` the pair is
  `loOnEq`-incomparable and non-maximal (both order before `c`), while in `{a,b}`
  the edge `a → b` is present (the antitone contrast); the datatype is convergent
  up to `eqObs` on all five weakly-closed subsets (in `{a,b,c}` both extensions
  read `Z`); `EqSwap(a,b,init)` is owed and FAILS; the `τ`-burdened equality
  `fold([a,b]++[c]) ≈ fold([b,a]++[c])` does hold (the maximal-only reach); and a
  sweep over every vis-DAG on up to four events over `{write A, write B, reset}`
  (5418 configurations, 51072 weakly-closed sets) finds RESET globally convergent
  up to `eqObs`, so it satisfies the converse hypothesis everywhere and the swap
  failure is a global refutation. This is the machine-checked inhabitant of the
  gap.
* **Probe A (vc:disc extra).** Datatype GSET, two invariants. Verifies canonical
  RA-lin under both `Inv1 = ⊤` and `Inv2 = no-poison`, vc:disc GREEN under `Inv1`
  and RED under `Inv2`, and that the violating value never appears in a reachable
  canonical fold (the failure is off-domain).
* **Probe B (vc:merge forced).** Datatype GSET. Verifies the conditioned Join holds
  on every reachable pair for the union merge (positive) and that the checker
  detects a Join violation for a drop-branch merge (calibration negative).

The probe is a targeted oracle, not an exhaustive one: no finite sweep can carry
the general conditioned case (unbounded state, arbitrary `eqObs` and `Inv`). Its
value is that the two structural claims that could have gone either way (the gap
is inhabited; the two-Inv separation is real) are witnessed by concrete
datatypes with hand-derived verdicts, so the CONJECTURED labels rest on
demonstrated corners rather than on abstract reasoning alone.

## Phase-2 Lean shapes

The phase-2 mechanization is smaller than the flat converse's because only
vc:merge is a positive theorem; vc:comm and vc:disc are recorded as
*refutations* (RA-lin datatypes that redden the VC), which is the honest shape.

* `structure CanonicalRALin3Eq` with fields `join'` (derivable, see below) and
  `converges` (canonical class unique up to `eqObs` on reachable weakly-closed
  `Inv`-sets), mirroring `Converse.CanonicalRALin3`.
* `converse_vc_merge : CanonicalRALin3Eq D E W GenDisc → EqJoinLemma3C D E W GenDisc`
  on the reachable-realizable domain: the flat `converse_VC6`/`_VC8` Join step with
  `=` relaxed to `≈` via `CongVC`, the LCA lemma, and `converges`. The one new
  ingredient over the flat proof is the domain-realizability lemma
  (`GenDisc` fully-closed `Inv` pair is a reachable merge tuple), which should be
  stated as an explicit hypothesis, as the flat converse stated `converges`.
* `eqswap_not_forced : ∃ D E W C, IsRALinearizable3Eq … C ∧ ¬ EqSwapOracle D E W C`,
  the RESET datatype as a Lean instance. The refutation is the mechanized form of
  Probe C: convergence holds, `EqSwap` at a non-maximal enabled pair fails.
* `vc_disc_extra : ∃ D E1 E2, RALin D E1 ∧ RALin D E2 ∧ Discipline D E1 ∧ ¬ Discipline D E2`,
  the GSET two-Inv separation.
* `sig_peel_maximal_eq`: the `eqObs`-lift of the flat fold-peel, `σcan≈(U) ≈
  do(σcan≈(U ∖ e)) e` for `loOnEq(U)`-maximal `e`, proved from `converges` and
  antitonicity (`loOn_mono`) exactly as `Converse.sig_peel_maximal`. This is the
  positive residue of vc:comm: what convergence *does* force is the maximal swap,
  and the fold-peel is its packaging.
* The #123 experiment (`IsRALinearizable3ArbEq`): state vc:comm and vc:inv over an
  abstract acyclic antitone `arb`, show `loOnEq` is one such `arb` (transport in),
  and re-run the adequacy route (`eq_convergence` unchanged, since it is already
  order-agnostic). The recast fails only if the adequacy route consumes a property
  of `loOnEq` beyond acyclic-antitone-arbitration plus the `eqObs`-fold quotient;
  the converse of this note is evidence that it does not.

## What is proven and what is conjectural

PROVEN-ON-PAPER: vc:merge forced from existence plus convergence up to `eqObs` on
reachable merge tuples (the flat Join step lifted through `eqObs`-congruence and
the LCA lemma); the structural fact that convergence forces `EqSwap` only at
maximal pairs (the `τ`-burdened-equality argument); vc:disc's universal
preservation is extra (the GSET two-Inv separation, machine-anchored); the
core/shell lift map and its agreement with the flat converse at the boundary.

PROVEN-BY-WITNESS (finite, machine-checked, hand-derived): H-comm is refuted,
RESET being globally convergent up to `eqObs` (5418 configurations) hence
conditioned RA-linearizable everywhere, yet its swap oracle `EqSwap` fails at a
non-maximal enabled pair, so vc:comm and vc:inv are not forced; the vc:disc
two-Inv separation; the vc:merge Join detection and calibration.

CONJECTURED: the domain-realizability step closing vc:merge (every `GenDisc`
fully-closed `Inv` pair is a reachable merge tuple); the rehoming RGA reading of
vc:comm as the RESET absorber at scale (the RESET miniature models the delete
absorber, but the RGA's own global RA-lin-versus-swap separation is not
re-run here).

OPEN: whether a *stronger* conditioned RA-lin hypothesis (for example, RA-lin plus
a stated antitone-arbitration acyclicity) forces an `arb`-form of vc:comm, which
would upgrade H-recast from sufficient to biconditional; and the tight conditioned
biconditional at the reachable-core level (the conditioned analog of the flat
`#119` residue).
