# Production MRDT packaging enquiry

## Claim

Every datatype presented as a production Sal MRDT must enter the production
registry as a dependent pair of its raw `MRDTSig` and a `VerifiedMRDT` for that
exact signature. Raw signatures used by SPOTs, countermodels, or refuted
experiments must remain available without entering that registry.

Status: public-certificate connections are machine-checked and release-gated;
semantic-contract review remains pending.

Formal oracle: `Sal.MRDTs.Metatheory.ProductionLedger` must build a registry
whose element type contains both the signature and its certificate. The
release gate must reject a production entry that supplies only `MRDTSig`,
`ReplayAdequateMRDT`, issuance, or convergence.

Falsifier: register the `rc` SPOT, queue, MVR, or FugueMax
`FMSig` without constructing a `VerifiedMRDT` for that exact signature.

Positive control: every current public package, including the completed LWW
register, OR-set, and Queue, constructs a production-registry entry.

Negative controls in `PublicCertificateGate` reject replay-only Queue evidence,
a certificate for another implementation, and substitutions of issuance,
`rc`, legality, or observations. These are type-boundary tests, not proofs that
Queue's intended contract is impossible. Queue's completed public certificate
is now accepted alongside rejection of its replay-only companion; MVR's refuted client specification remains in
`NegativeLedger`.

PBT gate: not applicable to the type-level registry claim. Datatype packages
retain their directed SPOTs and runtime randomized tests. The runtime evidence
manifest is a validation boundary, not a proof that handwritten JavaScript is
equivalent to Lean.

Trusted definitions: the registry determines what this repository calls a
production verified MRDT. The runtime manifest records correspondence status
but does not validate manual implementations by declaration.

Reality oracle: the release script checks the Lean production registry and the
JavaScript evidence manifest. Differential and conformance tests remain the
independent oracle for handwritten runtime implementations.

Residual: extraction is not implemented. A runtime may name a Lean package and
still have only tested, not proved, correspondence to it.

Result: `PackagedMRDT` is the only production entry type, and
`Production.registry` contains 22 signature/certificate pairs. The LWW
register uses one timestamp-directed `rc` policy and refines to a total
overwrite register. The OR-set has observed-remove issuance, convergence, and
an ordinary add-wins finite-set specification whose same-key conflicts are
resolved by `rc`. Queue has a complete public FIFO certificate permitting
concurrent duplicate targets, with timestamp-ordered surviving contents.
The enriched FugueMax implementation has a plain-list public certificate and
a same-witness maximal-non-interleaving theorem for ordinary and virtual
executions. Its coordinate-only `FMSig` companion remains internal. The compact
MVR stores only live tagged values. `MVRLive.verified` connects its
ancestor-relative merge to the unchanged live-value-set specification
and a same-execution theorem characterizing causally maximal writes; its old
single-register counterexample remains checked by `NegativeLedger`.
The runtime manifest distinguishes four released datatypes
from comparison-only representations, and the release script builds both
ledgers and runs the manifest test.

The tombstone tagged OR-set is no longer registered in Lean or JavaScript.
Its historical model and runtime module remain only as regression/comparison
fixtures. `efficient-or-set` is the sole released OR-set package; there is no
released JavaScript port of that implementation.

## Exact-contract release gate

`public-contracts.json` selects the implementation, issuance, semantic `rc`,
`SequentialSpec`, and state relation for every production entry. These are
explicit declarations, not projections inferred from whichever certificate
happens to be supplied. The manifest is a selection ledger, not a second
semantic specification.

`scripts/check-mrdt-refactor.sh`, also run by CI, invokes
`scripts/check-public-certificates.mjs`. It generates and checks Lean obligations
that:

- the supplied term is a `VerifiedMRDT` for the selected implementation;
- its issuance, `rc`, specification and relation equal the selected components;
- both replay adequacy and public sequential correctness use those components;
- its ordinary and virtual correctness theorems provide an exact event
  enumeration, respect for `loOn`, legality, state refinement and agreement
  with every specified query. These conjuncts are spelled out in the gate,
  so weakening `IsSpecLinearizable` itself does not silently weaken the check;
- the complete typed registry equals the selected list, so unlisted additions,
  omissions, and substituted packages fail;
- the certificates and both public theorems depend only on `propext`,
  `Classical.choice`, and `Quot.sound`.

Declared datatype-specific `obligations` are also elaborated against explicit
statements and axiom-audited. Queue requires its combined same-execution
concurrent FIFO contract (`queue_correct`) and ordinary sequential special
case (`client_linear_fifo`). MVR requires causal-maximality (`mvr_correct`)
and the ordinary-register query special case (`linear_register`). FugueMax
requires one witness for plain-list correctness and maximal non-interleaving
(`FugueMax.correct`). These select
existing Lean propositions; they do
not define another abstract machine.

Runtime evidence names a contract ID and matching certificate declaration.
Its instantiated Lean parameters are recorded in the contract ledger; the
mapping does not prove that handwritten JavaScript implements them.
Release checks include schema/mapping failures, axiom-report failures, actual
Lean rejection of an omitted registry entry and a changed `rc`, and the
negative type controls above. A Queue-specific negative control also rejects
evidence that supplies linearizability but drops the additional concurrent
FIFO obligations; another rejects MVR evidence omitting causal-maximality.
FugueMax controls reject replay/non-interleaving evidence without the
plain-list contract and list correctness without same-witness non-interleaving.
There is no datatype-name blacklist: Queue and MVR entered
with completed certificates and explicit contract entries; their replay-only
companions still cannot cross the boundary.

## What humans review

The sequential specification can be the human-reviewed artifact. Review its
state, initial state, transitions, legality and observations, together with the
selected issuance and `rc` that give the concurrent interpretation. No competing
specification layer is required. For example, RGA's public list specification
allows repeated deletion by identifier, while issuance requires a live target
at the origin. Requiring that target to remain live at every replay prefix
would instead exclude concurrent duplicate deletes.

The gate proves connection to the selected definitions, not that those
definitions capture the user's intent. Changing a selected definition's body
can change the contract without changing its name; such edits still require
semantic review and relevant positive/negative behavioral controls. The
manifest's `pending-semantic-audit` status deliberately records that the
all-datatype review has not been completed. Neither an existing `VerifiedMRDT`
nor a green CI run upgrades that status automatically. Additional promises
about operation responses or histories must appear in proved conclusions;
they cannot be inferred from per-version query agreement.
