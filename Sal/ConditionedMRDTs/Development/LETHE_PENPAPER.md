# Lethe: a core calculus of mergeable forgetting

**Status: pen-and-paper design note. Nothing in this file is mechanized; every
claim below is either (a) backed by an existing kernel-checked artifact (cited
inline), or (b) marked as an obligation or an open question.** This note is the
first deliverable of `oq:proglogic`: the kernel grammar, its typing rules and
proof obligations, the forgetting ladder, worked derivations of the exemplar
datatypes, and the statement of the soundness theorem the mechanization would
owe.

*Naming.* Lethe is the river of forgetting. The calculus has one non-trivial
operator, `Forget`; the LCA is the price of forgetting; and the soundness
theorem (§7) — the efficient term is observationally equivalent to its free,
remember-everything expansion — is an *un-forgetting* theorem, so it is named
**Aletheia** (ἀ-λήθη, truth as un-forgetting). The LCA-recovery law of level F2
(§5) is **Eunoë**, Lethe's paired river of restored memory.

---

## 0. Thesis

**Every efficient mergeable replicated data type is a forgetful image of a
free, remember-everything datatype.** Lethe makes the forgetting an operator.
Four consequences, each of which reorganizes an existing piece of the
framework rather than adding a new one:

1. **The LCA is the price of forgetting.** A datatype that remembers
   everything merges by union and never needs a common ancestor. Three-way
   merge exists because the normal form has discarded information that the
   join of two branches requires; the LCA is where it is recovered.
2. **Efficiency is the yield of forgetting.** "Efficient OR-set", "closed-form
   counter", "tombstone-free RGA" are all the same move: a retraction onto a
   normal form.
3. **The conditioned VC bundle is the proof obligation of `Forget`.** The
   causal-delta axiom `CDVC3` — machine-checked independent
   (`Refutations/CD_Not_Derivable_Ternary.lean`, see
   `CD_MINIMALITY_TERNARY.md`) — is the primitive law of level-F2 forgetting.
4. **≈ is the congruence of `Forget`.** The observational equivalence the
   framework reasons up to is not an artifact; it is the statement that
   forgetting is sound.

The assertion layer is separation logic over the *id-heap* (§3): datatype
state decomposes as a separating conjunction over keys/identities, operations
have footprints, `rc` is a per-atom overlap policy, and the honesty conditions
of the hardest datatype (the tombstone-free RGA's ancestor paths) are
list-segment assertions carried by operations as birth certificates. No global
rely appears in the judgment; interference is footprint-structured throughout.

---

## 1. Preliminaries (native definitions)

**Operations and events.** Fix a type `A` of application operations. An
*event* is `Op A := ℕ × ℕ × A` — a globally unique timestamp, a replica id,
and the payload. Timestamps are unique across the execution (`distinct_ops`).

**MRDT signature.** An MRDT is `D = ⟨State, init, do_, mergeL, rc⟩` where
`do_ : State → Op A → State`, `mergeL : State → State → State → State` is the
three-way merge (first argument the LCA), and `rc : Op A → Op A → RcRes`
(`Fst_then_snd | Snd_then_fst | Either`) arbitrates non-commuting concurrent
pairs. Binary merge, when it exists, is the slice `merge a b = mergeL init a b`.

**Version DAG.** Replicas evolve by local steps (1-parent commits, apply
`do_`) and merge steps (2-parent commits, apply `mergeL` at the DAG-LCA of the
parents). A *configuration* is coherent when every merge's LCA argument is the
fold of the shared causal prefix of its parents. **Caution (load-bearing):**
in a general DAG two branches may share events *beyond* their LCA (the same op
delivered to both sides via different merges), so no per-triple state equation
of the form `ν(A ⊔ B) = m(νL, νA, νB)` can be a definition of correctness —
this is exactly why the framework's contract is a DAG-inductive VC bundle and
why "no lattice contract can exist" (`mrdt-metatheory.pdf`, delta-contract
section). Lethe inherits this: F2's obligation (§5) is stated per *reachable
configuration*, not per triple.

**The judgment.** `D` is *RA-linearizable up to ≈* when at every version of
every reachable coherent configuration, the state is ≈-equal to the fold
(`do_` over `init`) of some linearization of the version's visible events that
respects causal order and `rc`. Here `≈` is an equivalence on `State`,
congruent for `do_` and `mergeL`, under which queries are invariant. For
datatypes whose operations are only meaningful on some states, the judgment is
conditioned on *honest delivery*: every op is `applicable` at each state it is
applied to, and *accurate at birth* (its payload correctly describes the
issuing state). Only level F3 and `Guard` consume honesty; F0–F2 derivations
are honesty-free.

**The metatheorem interface.** The framework provides: (i) the flat ternary
metatheorem — `CoreVCs3CD + FeasibleDeltaVCs3 + CDVC3 ⟹ JoinLemma3 ⟹ RA-lin`
(eight VCs, validated, minimal at `CDVC3`); (ii) the conditioned metatheorem
consuming honest delivery (the tombstone-free RGA's route,
`MRDT_Instances/RGA/RA_Lin.lean`); (iii) the product kit
(`Metatheory/Product*.lean`): convergence by concatenation witness, one-sided
safety, and the ≈-quotient lift. Lethe treats these as the semantic soundness
lemmas its typing rules will invoke; it adds no new metatheory in this note.

---

## 2. The free object: the log

```
Log(A):  State  := Finset (Op A)
         init   := ∅
         do_ s o := insert o s
         mergeL l a b := a ∪ b        -- l unused: remembering is free
         rc _ _ := Either
         ≈      := (=)
```

On coherent configurations `l ⊆ a ∩ b`, so union is the pushout of the two
branches over the LCA; every linearization folds to the same union, and
RA-linearizability is trivial. `Log(A)` is *free* in the operative sense:

> For any MRDT `D` over the same ops, RA-linearizability of `D` says exactly
> that every reachable state of `D` is (≈ to) the image of a reachable
> `Log`-state under `D`'s own fold. **Correct = a forgetful image of the log.**

The catalogue proves this datatype-by-datatype. Lethe's job is to build the
images *compositionally*: a term denotes a datatype together with the
retraction exhibiting it as an image, and the typing derivation assembles the
global retraction from per-constructor pieces.

---

## 3. The id-heap and the assertion layer

**Id-heap.** A Lethe state is presented as a separating conjunction of cells
indexed by keys (element identities, timestamps, replica ids, unit for
singleton cells):

```
σ  ⊨  ⊛_{k ∈ K} cell_k
```

**Assertions.**

```
P ::= emp | k ↦ v | P * P | lseg(k₀ … kₙ) | tok(n) | ⌜φ⌝
```

`k ↦ v` — key `k` holds cell value `v`; `*` — disjoint composition;
`lseg(k₀ … kₙ)` — a chain `k₀ ↦ (_, k₁) * … * kₙ₋₁ ↦ (_, kₙ)` in a
parent-pointer cell family (the RGA ancestor path); `tok(n)` — `n` escrow
tokens (the bounded-counter/budget discipline); `⌜φ⌝` — pure facts.

**Footprints and locality.** Each op has a footprint `fp(o) ⊆ K` — the keys
its `do_` reads or writes. The locality principle:

> `fp(o₁) ∩ fp(o₂) = ∅  ⟹  o₁, o₂ commute on all states, and rc(o₁,o₂) =
> Either` is forced.

Consequently `rc` is not a global relation but a **per-atom overlap policy
`ρ`**: a choice of arbitration for same-footprint concurrent pairs (add-wins,
remove-wins, larger-timestamp-wins, …). Composite `rc` is computed pointwise;
cross-component pairs are `Either` by frame. This is the separation-logic
reading of the repo's empirical fact that every production `rc` is `Either`
except on same-key pairs (`osRc`, the RGA's `Either`-everywhere, the queue's
*absence* of any valid `rc` being the flag that its ops share one footprint —
the whole sequence).

**Certificates.** An op may carry an assertion over the id-heap — its
*certificate* — required to hold at the issuing state (birth) and to be
re-establishable at delivery. F0–F2 ops carry `emp`. The tombstone-free RGA's
`Ins`/`Del` carry `lseg(prefix ++ [anchor])`: the recorded ancestor path *is*
a list-segment assertion, and honest delivery *is* certificate validity. This
is the design decision that replaces a global rely: what the environment may
do is bounded by what certificates it must preserve, checked per footprint.

---

## 4. The kernel

### Grammar

```
atoms        A ::= GSet τ            -- grow-only set of τ (the free cell)
                 | MaxCell (τ, <)    -- write-max register (⊥-initialized)
                 | Agree τ           -- write-once cell

terms        D ::= A^ρ                        (ATOM)
                 | D₁ ⊗ D₂                    (PROD)
                 | ⊛_{k : K} D                (MAP)
                 | Forget[μ]_{ν, ι, νop} D    (FORGET)
                 | Guard_{I, app} D           (GUARD)
```

`ρ` — overlap policy (the atom's `rc` on same-footprint pairs).
`ν : State_D → NF` — retraction; `ι : NF → State_D` — section, `ν ∘ ι = id`.
`νop` — action of the retraction on operations (identity except at F3, §5).
`μ ∈ {cc, flat, wit}` — the *join species*: which soundness route the owed
Join Lemma takes (conditioned-commutation, flat/unconditional, or direct
linearization witness). The species is a mode annotation, not a new judgment:
the framework already ships all three as proved routes (flat metatheorem;
conditioned metatheorem; the mergeable queue's direct witness
`queue_ra_linearizable3`).

In principle the atom basis is `GSet` alone — `MaxCell = Forget[flat](GSet)`
with `ν = max` (an F1 forgetting, §5) and `Agree` is its degenerate write-once
form. They are kept primitive as a *pre-discharged library*: their laws are
proved once and derivations cite them.

### The typing judgment

```
D  ⊢  ⟨ Σ ; ≈ ; O ⟩
```

`Σ` — the denoted MRDT signature; `≈` — the equivalence the judgment is up
to; `O` — the multiset of *owed obligations*: leaf-level proof debt that a
derivation leaves to the datatype author. **Aletheia (§7): if `D ⊢ ⟨Σ; ≈; O⟩`
and every obligation in `O` is discharged, then `Σ` is RA-linearizable up to
`≈` (under honest delivery iff an F3 `Forget` or a `Guard` occurs in `D`),
and `Σ ≈-refines its free expansion.**

### Rules

**(ATOM)** `A^ρ ⊢ ⟨A's signature with rc = ρ-on-overlap, Either off; (=) ;
{atom laws of A}⟩`. The atom laws (semilattice laws for `GSet`; totality of
`<` for `MaxCell`; single-writer for `Agree`) are library facts, discharged
once.

**(PROD)**
```
D₁ ⊢ ⟨Σ₁; ≈₁; O₁⟩    D₂ ⊢ ⟨Σ₂; ≈₂; O₂⟩    K(D₁) ∩ K(D₂) = ∅
----------------------------------------------------------------
D₁ ⊗ D₂ ⊢ ⟨Σ₁ × Σ₂ pointwise; ≈₁ × ≈₂; O₁ ∪ O₂⟩
```
**No new obligation.** This is the frame rule, and it is the one rule already
fully mechanized: convergence by concatenation witness, one-sided safety, and
the ≈-quotient lift (`Metatheory/Product*.lean`; first real consumer
PeritextTF, 1,064 lines for rich text). The side condition is syntactic:
disjoint key-spaces, hence cross `rc = Either` by locality (§3). The known
semantic caution — reachability does not project through ⊗ — is *why* the rule
owes a concatenation witness rather than a naive pairing; the witness is
proved once, in the kit, not per instance.

**(MAP)** `⊛_{k:K} D` — the keyed family, ops address one key, state is the
finitely-supported product. Semantically an iterated ⊗ with uniform
components; **no new obligation** beyond `D`'s, *provided* each op's footprint
is a single key (syntactic check). Owed to the mechanization: the pointwise
lift as a once-only theorem (it exists today only implicitly, inside each
set/map datatype's own discharge).

**(FORGET)** — the operator the calculus exists for.

```
D ⊢ ⟨Σ; ≈; O⟩     ν : Σ.State → NF,  ι : NF → Σ.State,  ν ∘ ι = id
--------------------------------------------------------------------
Forget[μ]_{ν,ι,νop} D ⊢ ⟨Σ_NF ; ≈_ν ; O ∪ O_F(level, μ)⟩

where  Σ_NF.init        := ν(Σ.init)
       Σ_NF.do_ s o     := ν(Σ.do_ (ι s) (νop o))
       Σ_NF.mergeL l a b := ν(Σ.mergeL (ι l) (ι a) (ι b))
       ≈_ν              := the ν-kernel quotient of ≈
```

The owed obligation `O_F` is stratified by *how much ν forgets* — the ladder,
§5. `νop = id` except at F3.

**(GUARD)** `Guard_{I,app} D` — the conditioning wrapper: invariant `I` on
states, applicability `app` on (state, op). Denotation unchanged; the judgment
gains a safety clause (`I` holds at every version) and the delivery assumption
strengthens to honest (`app` at each application). Owed: **stability** — `I`
is preserved by `do_` of applicable ops and by `mergeL` of `I`-states arising
in honest configurations — discharged by one of the two proved safety routes
(causal-witness or escrow; `conditioning` kit, both landed). The escrow
instance: `app` consumes `tok(n)` resources whose total is bounded by `I` —
the bounded counter is exactly this (`bc_version_inv`). **The rule must be
allowed to refuse**: see §8 for FWW-mutex and the ungated BudgetCart budget,
where refusal is the correct and already-established outcome.

---

## 5. The forgetting ladder

Stratify `Forget` by what the retraction destroys. Each level's obligations
strictly contain the previous level's (conjecture C1; the inclusions are
evident, strictness at each step is witnessed by the exemplar datatypes).

**F0 — no forgetting** (`ν = id`). Grow-only datatypes; merge is union;
obligations: atom laws only. *Exemplars:* G-set, G-map, tombstoned RGA,
Peritext (all components grow-only, pointwise union — the README's own
description).

**F1 — join-compatible forgetting.** The kernel of ν is a semilattice
congruence:
```
(F1-law)   ν(x ⊔ y) = ν(ι(ν x) ⊔ ι(ν y))    for all reachable x, y
```
The normal forms then carry an induced *binary* join; the datatype remains a
CRDT after forgetting, no LCA appears. *Exemplars:* LWW register (`ν` =
keep-max: max of a union is max of maxes), FWW register (min-cell, the
positive complement of the `lww_merge_needs_timestamps` kill-test), plausibly
MVR (`ν` = keep the undominated antichain — **tentative, to validate by
hand-derivation, RQ1**). Obligation: the F1-law, one commuting square per
atom.

**F2 — LCA-recoverable forgetting.** ν is *not* a join-congruence: the join
of images is not determined by the images. The lost information is recovered
from the LCA. The obligation is **Eunoë**, stated at the only level of
generality that survives the §1 caution (branches may share beyond the LCA):

> **(Eunoë, F2 obligation.)** There is a normal-form merge `m(l, a, b)` such
> that in every reachable coherent configuration, `m` at the version-DAG's
> LCA-images equals the ν-image of the log-level union — inductively over the
> DAG. Concretely: the shipped VC bundle `CoreVCs3CD + FeasibleDeltaVCs3 +
> CDVC3` for `Σ_NF`, under join species μ.

The shape of `m` is *inclusion–exclusion*: subtract from the branches what the
LCA shows to be shared history. Three instances of the same formula:

| datatype | normal form | m(l, a, b) |
|---|---|---|
| counter | event count | `a + b − l` |
| OR-set | live instances | `(l∩a∩b) ∪ (a∖l) ∪ (b∖l)` (= `osMergeL`) |
| monoid cell, general | fold of events | branch deltas re-applied to `l` |

`CDVC3` is the causal-delta law of this level, and its machine-checked
independence (`cdvc3_not_derivable_from_core_delta`) is now read as: **the
Eunoë law is a primitive axiom of the calculus, not derivable from the core
and delta laws — the rule basis is minimal at F2.** *Exemplars:* IO-counter,
PN-counter, OR-set, efficient OR-set (same free term, two retractions — the
"efficient" variant is a *further* ν; the calculus makes "efficient" a
relation between terms, not a new datatype), EW-flag (tentative), AWPQ
(tentative), the mergeable queue at species `wit` (no `rc` exists — the
enqueue clique shares the sequence footprint — so `cc` is structurally
unavailable and the Join Lemma is the direct witness, exactly
`queue_ra_linearizable3`).

**F3 — certificate-carrying forgetting.** ν destroys state that the *ops'
own semantics* reads: after forgetting, an op's meaning is no longer a
function of the normal form it is applied to. Two things become necessary,
and the calculus makes both explicit where the framework discovered them
semantically:

1. **`νop ≠ id`** — the retraction acts on operations: op payloads are
   extended with certificates (assertions, §3) recording the destroyed
   context at birth, and `do_` on normal forms consults the certificate.
2. **Honest delivery** — born-valid certificates, applicable at delivery —
   enters the judgment; it is consumed by nothing below F3.

Obligation: Eunoë *plus* honesty-threading (born accuracy + applicability
inductively over the DAG) *plus* correctness of `νop` (the rewritten op on
the normal form simulates the original op on the free state, up to ≈_ν).
*Exemplar (the only one):* the tombstone-free RGA. Free term: the tombstoned
RGA (an F0 term!). `ν`: drop dead nodes, rehome children along recorded
parent chains. Certificates: `lseg(prefix ++ [anchor])`. `≈_ν`: ghost
payloads — and the eq-variant result (`RGA_Tombstone_Free_Eq_MRDT.lean`:
on normal forms, ≈ *is* structural equality) is precisely the statement that
`≈_ν` is the ν-kernel quotient and nothing more. The impossibility of a
prefix-free variant (`RGA_PrefixFree_Impossible.lean`) becomes a calculus
theorem-shape: **F3 without certificates is underivable** (§8).

**Orthogonal axis — `Guard`.** Safety conditioning composes with any level:
BC = `Guard_escrow(F2 counter)`; BudgetCart = `Guard(⊛ OR-set with derived
spend)` with the budget theorem hypothesis-gated (OQ8 — the refusal is the
framework's, and the calculus must reproduce it, §8).

**The ladder retro-dicts the repo's difficulty gradient.** F0/F1 datatypes
discharged with `dsimp+grind` almost entirely; F2 needed the conditioned
metatheory; the single F3 datatype needed HonestDelivery and a bespoke
end-to-end proof. The calculus did not choose this ordering — the proofs did.

---

## 6. Worked derivations

Component-by-component, per the house format. Certificates are `emp` unless
stated.

### 6.1 LWW register — `Forget[flat]_{keep-max}( GSet (ℕ × ℕ × τ) )`  [F1]

| component | free term | after Forget |
|---|---|---|
| Type | `Finset (ts × rid × τ)` | `Option (ts × rid × τ)` |
| init | `∅` | `none` |
| do (`wr v` at `(t,r)`) | insert `(t,r,v)` | keep the `<`-larger of old and `(t,r,v)` |
| merge | union | `max l a b = max a b` (l drops out — F1) |
| rc | `Either` (overlap resolved by ts order) | same |
| Inv / app | ⊤ / ⊤ | ⊤ / ⊤ |
| ≈ | `=` | `=` (ν-kernel is trivial on NF) |
| honesty | none | none |

Obligation discharged: F1-law = `max(x ∪ y) = max(max x, max y)`. One line.
The LCA vanishing from the merge *is the observable content of F1*.

### 6.2 Counter — `Forget[flat]_{card}( GSet (ts × rid) )`  [F2]

| component | free term | after Forget |
|---|---|---|
| Type | `Finset (ts × rid)` (inc events) | `ℕ` |
| init | `∅` | `0` |
| do (`inc`) | insert | `+1` |
| merge | union | **`a + b − l`** |
| rc | `Either` | `Either` |
| ≈ | `=` | `=` |

Eunoë here is inclusion–exclusion on cardinality; `l` cannot be eliminated
(the join of two numbers does not determine the union's size) — the minimal
possible F2, and the right first mechanization target. PN-counter =
`(this) ⊗ (this)`.

### 6.3 Efficient OR-set — `Forget[cc]_{live}( ⊛_{inst} (GSet unit ⊗ GSet unit) )^{add-wins}`  [F2]

Free term: per instance `(ts, rid, payload)`, an add-flag `GSet` and a
remove-flag `GSet` (a keyed 2P pair). `ν` keeps instances with
`add ∧ ¬remove` — the live set. This lands verbatim on `ORSetCore.lean`:

| component | value (post-Forget) | repo artifact |
|---|---|---|
| Type | `Finset (ℕ × ℕ × β)` | `OSState β` |
| init | `∅` | `OSCore.init` |
| do | `add`: insert instance; `rem k`: filter key | `osUpdate` |
| merge | `(l∩a∩b) ∪ (a∖l) ∪ (b∖l)` | `osMergeL` |
| rc | add-wins on same key, else `Either` | `osRc` — `ρ` is exactly the same-key clause |
| ≈ | `=` | — |

Eunoë instance to check by hand: the live-set of a log-union against the
inclusion–exclusion formula, DAG-inductively (the per-triple identity fails
in general — §1 caution — which is *why* the obligation is the VC bundle).
The plain (tombstoned) OR-set is the *same free term with a weaker ν*; the
plain and efficient variants are two points on one Forget chain, and their
separate 24-VC discharges in the repo are the two Eunoë instances.

### 6.4 Tombstone-free RGA — `Forget[cc]_{drop-dead, rehome; νop}( tombstoned RGA )`  [F3]

| component | free term (F0, in repo as `RGA_MRDT`) | after Forget |
|---|---|---|
| Type | grow-only: nodes `(ts ↦ elem × anchor)` + tombstone set | live nodes only: `ts ↦ (elem, anchor)` |
| do | `Ins after x` adds node; `Del x` adds tombstone | `Ins pre x`: insert with certificate; `Del pre x`: **remove + rehome children to `resolve(pre)`** |
| merge | pointwise union | climb-LCA rehoming of survivors (`climb`) |
| rc | `Either` | `Either` (order is read-side) |
| certificate | `emp` | **`lseg(pre ++ [x])`** — the recorded ancestor path |
| ≈ | `=` | ghost-payload quotient; on normal forms `≈` = `=` (eq-variant) |
| honesty | none | born accuracy + applicable delivery (`HonestDelivery`) |

This is the derivation where the note's one flagged surprise lives: `νop` is
not optional — deletion on the normal form *edits surviving state* (children
re-anchor), which no state-only retraction produces. Whether `Forget` is one
operator with an op-action or two operators (state-quotient ∘ op-compiler) is
**OQ-L1**. Everything owed here is already discharged *as an instance*
(`RA_Lin.lean`, kernel-clean, one assumption = HonestDelivery); what Lethe
owes is the rule-generic form.

### 6.5 Guarded exemplars, briefly

- **Bounded counter** = `Guard_{v ≥ 0, escrow}(counter of §6.2 as PN)`;
  stability via tokens; `bc_version_inv` is the discharged obligation.
- **BudgetCart** = `Guard_{budget}( ⊛_{inst} OR-set ⊗ derived-spend )`;
  convergence flows through the OR-set route; the *ungated* budget obligation
  is provably false (enumeration-dependence of vis-only folds) — the GUARD
  rule must refuse, matching `bcart_version_inv_gated` and OQ8.

### 6.6 The catalogue as Lethe terms (proposed; validation = RQ1)

| datatype | proposed term | level | status of proposal |
|---|---|---|---|
| G-set / G-map | `⊛ GSet` / `⊛ₖ GSet` | F0 | clear |
| tombstoned RGA | `⊛_{ts} (Agree × GSet)` grow-only | F0 | clear |
| Peritext | tombstoned RGA `⊗` `GSet AnchorAttachment` | F0 | clear |
| LWW register | §6.1 | F1 | derived above |
| FWW register | `Forget[flat]_{keep-min}(GSet)` | F1 | clear; Guard-mutex refused (§8) |
| MVR | `Forget_{antichain}(GSet tagged-writes)` | F1/F2? | **hand-derive: does the antichain ν satisfy F1, or does dominance need the LCA?** |
| IO / PN counter | §6.2 (⊗ for PN) | F2 | derived above |
| OR-set / efficient | §6.3 (two ν's) | F2 | derived above |
| EW-flag | `Forget(OR-set-of-enables)`-like | F2? | hand-derive; the known-broken variant should *fail* a specific Eunoë instance — a calculus-level account of the Plausible counterexample |
| AWPQ | `⊛ (OR-set instance) + read-side max` | F2? | hand-derive |
| mergeable queue | `Forget[wit](Log)` — no ρ exists | F2 (μ=wit) | matches `queue_ra_linearizable3`; the *absence* of an rc is predicted by the shared footprint |
| tombstone-free RGA | §6.4 | F3 | derived above |
| PeritextTF | (§6.4) `⊗` markstore | F3 ⊗ F0 | matches `Peritext_Composed/`, the frame-rule consumer |
| BC / BudgetCart | §6.5 | Guard∘F2 | derived above |

---

## 7. Aletheia — the soundness theorem (statement owed, not proved)

> **Theorem (Aletheia).** If `D ⊢ ⟨Σ; ≈; O⟩` and every obligation in `O` is
> discharged, then:
> 1. *(convergence)* `Σ` is RA-linearizable up to `≈` at every version of
>    every reachable coherent configuration — under honest delivery iff `D`
>    contains an F3 `Forget` or a `Guard`, unconditionally otherwise;
> 2. *(un-forgetting)* the composite retraction `ν_D` assembled along the
>    derivation exhibits `⟦D⟧ ≈`-refining its free expansion — every
>    reachable `Σ`-state is `ν_D` of a reachable free state, and queries
>    factor through `ν_D`;
> 3. *(safety)* every `Guard_{I}` node's `I` holds at every version, given
>    the client honesty contract.
>
> **Proved by one induction on the typing derivation.**

Case-by-case, what exists versus what is owed:

| rule case | semantic lemma | status |
|---|---|---|
| ATOM | atom laws | exists piecemeal in instance discharges; owed: library form |
| PROD | concatenation witness + safety + ≈-lift | **exists** (`Product*.lean`) |
| MAP | pointwise lift | owed (implicit in per-datatype proofs today) |
| FORGET F1 | join-congruence ⟹ CRDT | easy; owed |
| FORGET F2 | Eunoë ⟹ VC bundle ⟹ JoinLemma3 ⟹ RA-lin | **exists** (flat + conditioned metatheorems); owed: the transport along ν as a lemma rather than per-instance |
| FORGET F3 | honesty-threading + νop simulation | exists as the RGA instance (`RA_Lin.lean`); owed: rule-generic form |
| GUARD | two safety routes | **exists** (causal-witness + escrow kits) |

The honest summary: **the semantic content of every case except MAP and the
rule-generic F3 already exists kernel-checked; what does not exist is the
grammar, the composite ν, and the single induction.** That is the
mechanization gap `oq:proglogic` names, now with a precise worklist.

---

## 8. What the calculus predicts and refuses

A logic earns its keep by refusing derivations, and each refusal below is
*already a kernel-checked or documented impossibility* — the calculus turns
them from post-hoc discoveries into syntactic non-derivability:

1. **No F3 without certificates.** A prefix-free tombstone-free RGA is not a
   Lethe term (νop has no certificate to consult), and the framework proved
   the corresponding datatype unverifiable (`RGA_PrefixFree_Impossible.lean`).
2. **No Guard-mutex from merges.** `Guard_{unset ⟹ exclusive}` over FWW fails
   stability ("unset" is not stable under concurrent honest extension) — the
   documented reason the FWW register is a reservation, never a mutex. The
   GUARD rule's stability side-condition refuses exactly this.
3. **No ungated BudgetCart budget.** The two-sided safety obligation is
   provably false (enumeration-dependence); GUARD derives only the gated form
   (`bcart_version_inv_gated`, OQ8).
4. **No rc for the queue.** Concurrent enqueues share the sequence footprint;
   locality (§3) makes `ρ` unavailable, forcing μ = `wit` — which is exactly
   the route the mechanized proof took.

And the constructive test (**the falsifiable success criterion**): build a
datatype *not in the catalogue* — a bounded OR-set (`Guard_escrow` over §6.3)
or an LWW-map with eviction (`⊛ₖ` over §6.1 with a `Forget` dropping evicted
keys) — where the only manual proof is the leaf Eunoë/F1 instance. If the
kernel cannot produce something new, it is a taxonomy; if it can, it is a
calculus.

---

## 9. Open questions

- **OQ-L1 (Forget: one operator or two?).** F3 forces an op-action `νop`.
  Is `Forget` a single operator with a (usually trivial) op-action, or a
  state-quotient composed with an *op-compiler*? The RGA hand-derivation
  (§6.4) suggests the compiler view: certificates are compiled-in
  preconditions. Decide on paper before mechanizing the FORGET rule.
- **OQ-L2 (exactness of Eunoë).** Is the F2 obligation *equivalent* to the
  shipped bundle `CoreVCs3CD + FeasibleDeltaVCs3 + CDVC3`, or merely
  sufficient? The CDVC3 countermodel gives the "not less" direction; the
  "not more" direction is open. If exact, the framework *is* the soundness
  theorem of one operator — the paper's headline.
- **OQ-L3 (SL sufficiency at F3).** Do footprint certificates + per-key
  invariants fully replace a global rely — i.e., can `HonestDelivery` be
  *derived* from per-op certificate validity, with the RGA lseg as the test?
  Expected yes for F0–F2 (vacuous), genuinely open at F3.
- **OQ-L4 (efficiency as a judgment).** `Forget` chains order variants of one
  datatype (plain vs efficient OR-set). Make "efficient" formal: normal-form
  size / merge cost versus the free term. Even semi-formal, it justifies the
  word in the thesis.
- **OQ-L5 (completeness).** Which RA-linearizable MRDTs are *not* Lethe
  terms? The queue needed a mode, not a new operator — evidence the mode
  lattice `{cc, flat, wit}` might suffice; MVR and AWPQ hand-derivations
  (§6.6) are the next stress tests.
- **OQ-L6 (ladder strictness — conjecture C1).** Each level's obligations
  strictly contain the previous. Strictness F1⊊F2 is witnessed by the counter
  (l does not drop out); F2⊊F3 by the prefix-free impossibility. F0⊊F1 needs
  a datatype whose ν = id fails F1 vacuously — trivial, but state it.

---

## 10. Relation to existing artifacts (crosswalk)

| Lethe piece | existing artifact |
|---|---|
| PROD rule | `Metatheory/Product*.lean` (concatenation witness, safety, ≈-lift) |
| F2 obligation | `Framework/VC_Set.lean` bundle; minimality: `Refutations/CD_Not_Derivable_Ternary.lean` |
| F3 instance | `MRDT_Instances/RGA/RA_Lin.lean`; ≈-collapse: `RGA_Tombstone_Free_Eq_MRDT.lean` |
| μ = wit | `MRDT_Instances/MergeableQueue/queue_ra_linearizable3` |
| GUARD routes | conditioning kits (causal-witness, escrow); `bc_version_inv`, `bcart_version_inv_gated` |
| refusals | `RGA_PrefixFree_Impossible.lean`; FWW reservation documentation; OQ8 |
| §6.3 verbatim | `MRDT_Instances/ORSetCore/ORSetCore.lean` (`osUpdate`, `osMergeL`, `osRc`) |

**Scope limit, stated once:** Aletheia certifies convergence to the
datatype's *own* fold up to ≈ — not intent (the `oq:linspec` limit; the
Peritext mark-leak is the canonical example). A spec layer per atom
(abstract state + per-op refinement) is future work and deliberately outside
this kernel.
