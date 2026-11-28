import LeanProofs_no_spec_non_comm.Implementations.BoundedCounter.VCs
import LeanProofs_no_spec_non_comm.Implementations.BoundedCounter.Negative

/-!
# The bounded counter: the specification-visibility criterion

RA-linearizability **with specification visibility**, from the premise in
`VCs.lean` and from nothing else. SPEC-NON-COMM appears nowhere.

This row reaches the join lemma at the **full causal past**, through
`Metatheory.causalJoinLemma`, not at the paper's dependency set. The
soundness theorem takes the join as a hypothesis for exactly that reason, so
the specification route accepts it unchanged.

The folder is a standalone duplicate of the row, so `Definition.lean`,
`VCs.lean` and `Negative.lean` beside this file are the row's own, not the
main tree's.
-/

namespace LeanProofs.NoSpecNonComm.Implementations.BoundedCounter

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface

variable {n : Nat} {K : Int}

/-- **RA-linearizability with specification visibility.**

The one row that cannot use `certifiedSpecRA_scoped_on`: its join comes from
`Metatheory.causalJoinLemma` at the full causal past, not from `joinLemma`
at the paper's dependency set, so the five conditions arrive one at a time
and the join as a hypothesis. That is exactly what the join being a
hypothesis is for. -/
theorem specRaLinearizable :
    Soundness.SpecCertifiedRA (D n K) (historySpec K) (issuance n K) :=
  Soundness.certifiedSpecRA_scoped_strict laws
    (EqualOpCommutes.of_concurrent laws.no_rc_chain uniform_rc_non_comm.toConcurrent)
    uniform_cond_comm.toSameReplica
    (ExecutionOrder.ofUniform uniform_rc_non_comm)
    joinLemma (fun _ _ => trivial) specChosenOrderSound

/-- Definition 4 follows, as it does for every row on the specification
route. -/
theorem raLinearizable :
    Soundness.CertifiedRA (D n K) (historySpec K) (issuance n K) :=
  Soundness.certifiedRA_of_spec specRaLinearizable

#print axioms specRaLinearizable

end LeanProofs.NoSpecNonComm.Implementations.BoundedCounter
