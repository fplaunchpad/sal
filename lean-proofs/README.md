# lean-proofs

The flat counter, restructured into the three-way split used by the
reference F* development, with every name taken from the paper.

Five implementations are restructured, covering four rows of Table 1:
Counter, Grow-only set (mathematical and enumerable carriers), Grow-only map,
and the LWW register.

The first four have `rc` empty, no issuance guard and no execution-scoped
bridge, so they fit the `Obligations` bundle and the unrestricted premise
`SpecSound`. The LWW register is the first that does not: its answer is the
greatest write key, which an arbitrary replay order does not explain, so it
uses the scoped premise `HistorySound` and selects a chronological witness.
That is the `E = Y` column of Table 1.

No datatype in the artifact is modified. The remaining rows need more than
this; see **Scope** below.

## Layout

```
LeanProofs/
  Interface/                     common to every implementation
    Implementation.lean          MRDTType and the tuple D_type = <Sigma, sigma0, do, merge, query, rc>
    Laws.lean                    Laws(D_type), the canonical join laws, Conformance
  Metatheory/                    proved once, for every implementation
    Adequacy.lean                obligations => join lemma => canonical correctness
  Soundness/                     proved once, for every implementation
    RALinearizability.lean       Definition 4 and the adequacy theorem
  Implementations/               one folder per implementation
    FlatCounter/
      Definition.lean            the counter's D_type, no proofs
      Laws.lean                  the obligations, each closed by omega
      Certificate.lean           Spec, issuance, the certificate
    GrowOnlySet/
      Definition.lean            the set's D_type, no proofs
      Laws.lean                  the obligations, each a set identity
      Certificate.lean           Spec, issuance, the certificate
    FiniteGrowOnlySet/
      Definition.lean            the enumerable (Finset) carrier
      Laws.lean                  the obligations, each a Finset identity
      Certificate.lean           Spec, issuance, the certificate
    FlatGrowOnlyMap/
      Definition.lean            the map's D_type, no proofs
      Laws.lean                  the obligations, each a Boolean identity
      Certificate.lean           Spec, issuance, the certificate
    LWWRegister/
      Definition.lean            the register's D_type, no proofs
      Laws.lean                  the obligations, each a max lemma
      Certificate.lean           Spec, issuance, the chronological witness
```

The split is enforced by content, not only by folder. `Interface/` and
`Metatheory/` name no datatype. `Implementations/FlatCounter/` never
mentions a configuration, an execution, `lo^C_E`, `can`, or the join lemma.

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
| `e1 --rc--> e2`    | `Impl.RcBefore`      |
| `rc_res`           | `OrderResult`        |

`Impl` carries two fields the paper leaves implicit, `decSigma` and
`decOType`, both marked as Lean bookkeeping in their docstrings.
`Impl.toMRDTSig` and `Impl.toRc` send the tuple to the shared framework's
representation; nothing else in this development mentions `MRDTSig`.

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
| the join lemma             | `Metatheory.joinLemma`                 |
| canonical correctness      | `Metatheory.canonicalCorrectness`      |

Section 4's Definition 4 and Section 5's adequacy theorem, in `Soundness/`:

| paper                             | here                            |
| --------------------------------- | ------------------------------- |
| Definition 4, at one configuration | `Soundness.RALinearizable`      |
| Definition 4, at every stored version | `Soundness.VersionsRALinearizable` |
| over every certified execution    | `Soundness.CertifiedRA`         |
| the sequential premise `ops(pi) . (q => b)` in `Spec` | `Soundness.SpecSound` |
| the adequacy theorem              | `Soundness.certifiedRA`         |

Lean reserves `do` and `Type`, so those two are spelled `do_` and
`MRDTType`. Everything else keeps the paper's spelling.

## Two deliberate departures from the paper, both local to this family

**The VCs are stated over arbitrary states.** The paper states VC2 to VC5
over canonical states, under `Admissible` and `Maximal` premises. This
development states the arbitrary-state strengthenings, which is what an
implementation in this family satisfies and what lets the counter close each
one with `omega`. VC1 is already over arbitrary states in the paper, so it is
reproduced verbatim. VC3 and VC5 have exactly the paper's equations with
`can(E)` replaced by an arbitrary state and `e(m)` by an arbitrary state `c`.

**VC4 is derived, not assumed.** For an implementation whose events all
commute, `Metatheory.vc4_causal_delta` proves CAUSAL-DELTA from an auxiliary
peel law plus `all_commute`. An implementation outside this family supplies
VC4 directly. `CanonicalJoinLaws.commuting_peel` is marked in its docstring
as auxiliary and not a paper VC.

`Interface/Laws.lean` states both departures in its header, so a reader who
opens only that file still sees them.

## Scope

`Obligations` is the bundle for implementations whose events all commute, so
`rc` is empty and `Laws(D_type)` is discharged by the metatheory. Of Table 1's
twenty-four rows, exactly these three fit it as it stands.

The others need the layout extended, in one of two ways.

**Nonempty `rc`** (optional register, both flags, both OR-sets, remove-wins
set, set-wins multimap: eight rows). These share `CanonicalJoinLaws` but must
supply `Laws(D_type)` themselves, and VC4 CAUSAL-DELTA becomes a real
obligation rather than something the metatheory derives, because
`causalDeltaLaw_of_all_comm` no longer applies. That means a second bundle
beside `Obligations`.

**An execution-scoped premise** (`E = Y`). `Soundness/` now carries this case
too: `HistorySound` and `certifiedRA_scoped`, added for the LWW register.
A datatype on this route supplies its own witness construction rather than
proving the unrestricted premise. `historySound_of_specSound` records that
the unrestricted premise implies the scoped one, so the first four rows
continue to use the simpler route.

The nonempty-`rc` change does not touch what is here; it adds alongside it.

## What each implementation supplies

| | Counter | Grow-only set | Grow-only map |
| --- | --- | --- | --- |
| `Sigma` | the integers | a mathematical set | a Boolean function |
| `sigma0` | `0` | the empty set | constantly false |
| `do` | `z + delta(o)` | `S union {o}` | `S(x) or (x = o)` |
| `merge` | `a + b - l` | `a union b`, base ignored | `l(x) or a(x) or b(x)` |
| `query` | return `z` | return `S` | return `S` |
| `rc` | empty | empty | empty |
| obligations closed by | `omega` | `Set.insert_comm`, `Set.union_comm`, `tauto` | case analysis on `Bool` |
| `Spec` state | an integer | a mathematical set | a **finite set** |

Each supplies a `Definition.lean` (the tuple, no proofs), a `Laws.lean`
(seven lemmas), and a `Certificate.lean` (`Spec`, issuance, `spec_non_comm`,
`conformance`, `certificate`). Everything else is inherited from `Interface/`
and `Metatheory/`.

The grow-only set and the map mark `type` (and the map also `Spec`)
`@[reducible]`, so that `(type A).OType` and `(Spec A).State` unfold during
instance search; without it the `Insert`, `Union` and `Membership` instances
are not found. Both use `Classical.propDecidable` for `decSigma`, since
equality of mathematical sets and of Boolean functions is not decidable.

The map is the only one whose specification uses a different carrier from the
implementation: `Spec` stores a finite set and answers with its characteristic
function, while the implementation stores the Boolean function directly. The
bridge is `fold_eq`, and it is the only real proof in that datatype's
`Certificate.lean`.

## Build

This is a self-contained Lake package. Build it from **this** directory:

```sh
cd lean-proofs
lake build LeanProofs
```

In an editor, open `lean-proofs` as its own workspace folder. The Lean
extension picks the project root from the workspace folder, so opening the
repository root instead gives these files the wrong search path and every
`import LeanProofs.*` fails with `unknown module prefix`.

The build reports that `joinLemma`, `certificate` and `raLinearizable` for
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
python3 - <<'EOF'
import hashlib, json
prov = json.load(open('artifact-provenance.json'))['sha256']
bad = [f for f, h in prov.items()
       if hashlib.sha256(open(f,'rb').read()).hexdigest() != h]
print('changed:', bad or 'none')
EOF
```

Vendoring keeps this package independent of any sibling directory, so it
builds on a fresh clone with no setup step.
