# Production MRDT packaging enquiry

## Claim

Every datatype presented as a production Sal MRDT must enter the production
registry as a dependent pair of its raw `MRDTSig` and a `VerifiedMRDT` for that
exact signature. Raw signatures used by SPOTs, countermodels, or refuted
experiments must remain available without entering that registry.

Status: machine-checked and release-gated

Formal oracle: `Sal.MRDTs.Metatheory.ProductionLedger` must build a registry
whose element type contains both the signature and its certificate. The
release gate must reject a production entry that supplies only `MRDTSig`,
`ReplayVerifiedMRDT`, issuance, or convergence.

Falsifier: register the OR-set interaction SPOT, queue, MVR, or FugueMax
`FMSig` without constructing a `VerifiedMRDT` for that exact signature.

Positive control: every current public package, plus the completed OR-set,
constructs a production-registry entry.

Negative control: queue and MVR remain in a separate negative ledger with
their checked sequential counterexamples and cannot inhabit the production
entry type through their replay-only packages.

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
`Production.registry` contains 18 signature/certificate pairs. The OR-set now
has observed-remove issuance, convergence, a separate sequential tagged-set
machine, query refinement, and directed issuance/add-wins controls. Queue,
MVR, and the coordinate-level FugueMax `FMSig` are checked by
`NegativeLedger`. The runtime manifest distinguishes five released datatypes
from comparison-only representations, and the release script builds both
ledgers and runs the manifest test.
