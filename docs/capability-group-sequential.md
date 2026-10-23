# Capability groups: independent sequential contract and criterion boundary

The research question is whether dynamic grant/revoke authorisation, including
suppression of concurrent capability uses, admits an ordinary sequential
ACL interpretation under Sal's actual replication-aware criterion. A second
question asks what changes when a sequential explanation must preserve
independent specification conflicts along visibility edges.

The executable source model is a fixed-owner specialization of
[Jacob, Stuber, and Hartenstein, PaPoC 2026](https://arxiv.org/html/2604.23560),
Spec. 2. The paper distinguishes immutable precursive admission from mutable
discursive authorisation. Its verified cases in §4.2 separate grant-only and
revoke-only modes; §5 identifies their combination as a next step. This
artifact studies a restricted combination with a permanent owner, assign-only
grants, and no delegation. It does not extend the paper's Byzantine guarantees.

## Independent specification

`Sal/MRDTs/Paper1/CapabilityGroupSpec.lean` defines an ordinary deterministic
sequential machine. Its trusted state contains three finite tables:

| Table | Meaning |
| --- | --- |
| `Store.grants` | Granted `(grant ID, recipient)` permissions |
| `Store.revoked` | Revoked grant IDs |
| `Store.entries` | Live `(assignment ID, name)` entries |

An owner grant inserts its permission. An owner revocation of a known grant
records its ID. An assignment succeeds exactly when its actor holds the named
grant and that grant is not revoked. On success, it removes the entry IDs
explicitly listed in its `observed` input and inserts its own entry. Rejected
updates are no-ops. Revocation prevents subsequent assignments; it preserves
previously accepted names, as proved by `revoke_preserves_names`.

The specification never invokes source `authorized`, `visible`, or `names`,
and never stores or evaluates a source event DAG. The projection translates
source precursor IDs into explicit observed-overwrite IDs. This retains the
application intent of a multi-value register: concurrent assignments can both
remain visible. A scalar last-writer name specification would fail for that
representational reason even without revocation. `multivalue_control` verifies
that both this specification and the source return `{7,8}` for two concurrent
writes, and reject the accidental scalar result `{8}`.

## A checked boundary with concurrent owner revocations

`Sal/MRDTs/Paper1/CapabilityGroupBridge.lean` contains five events:

| Event | Invocation | Precursor IDs |
| --- | --- | --- |
| `grant` | Owner grants actor 1 permission, grant ID 1 | `{}` |
| `left` | Actor 1 assigns name 7 using grant 1 | `{1}` |
| `right` | Actor 1 assigns name 8 using grant 1 | `{1}` |
| `revokeLeft` | Owner revokes grant 1 | `{1,2}` |
| `revokeRight` | Owner revokes grant 1 | `{1,3}` |

Each revocation follows one write and is concurrent with the other. The source
suppresses both writes: `left` is disqualified by `revokeRight`, and `right` by
`revokeLeft`. The resulting name query is empty.

This is a well-formed, locally admissible source execution using multiple
devices for one authenticated owner. `source_wellFormed` proves timestamp
closure, ranking, and ID uniqueness. `source_fresh_issue_schedule` checks the
actual `CanIssue` contract at each local cut, including a timestamp equal to
all locally known IDs and a fresh ranked ID. `SourceReach` defines empty logs,
such issuance, and compatible union reconciliation. Its general preservation
theorem `SourceReach.valid` proves well-formedness and local admission.
`source_reachable` constructs both branches and their reconciliation;
`source_reachable_valid` proves that every final event remains precursively
admitted.
`owner_equivocates` proves that the owner events are not causally ordered.
Consequently this example does not refute the honest single-owner-replica case.

The independent specification conflicts on grant/write and same-grant
write/revoke pairs. The four conflict theorems prove this using accepted and
rejected concrete query histories. They force these visibility edges:

```
grant < left < revokeLeft
grant < right < revokeRight
```

Every sequential order preserving those edges accepts at least one write
before the first revocation. Subsequent revocations preserve its name.
`all_permutations_nonempty` checks all 120 permutations by kernel reduction.
`not_specificationRA` uses that result to refute every witness of the existing
`ProjectedSpecificationRALinearizable` predicate for the coherent Sal
configuration `config`.

The literal Sal criterion has a different outcome. Raw event insertion
commutes. With the empty operation policy, `paperOrder` therefore imposes no
visibility constraints. Its witness can order `grant`, both revocations, then
both writes. Both writes become sequential no-ops, matching the empty source
answer. `literal_operationRA` proves the repository's original
`RALinearizable` predicate; `criterion_boundary` pairs its success with failure
of the stronger criterion. Describing this result simply as “RA fails” would
be incorrect.

## Evidence and limits

The independent specification, source protocol reachability, configuration coherence,
120-order rejection proof, and literal witness are machine-checked without
new axioms, `sorry`, or native evaluation. `criterion_boundary` uses only the
standard Lean foundations `propext`, `Classical.choice`, and `Quot.sound`.

`config` is a coherent Sal configuration, not a proved `MintCertifiedReach`
endpoint. The `SourceReach` derivation supplies source-level reachability
evidence; it does not substitute for a Sal certified-network
trace. The wrapper deliberately separates authenticated actors from Sal
replica IDs. Claims requiring actor=replica would exclude its concurrent
owner events.

The honest owner-chain case remains a separate positive target. A candidate
construction places each assignment immediately before its earliest causally
succeeding owner event, or after all owner events when none succeeds it.
Owner events retain their chain order; assignments within each gap follow
causality. This places every concurrent revocation before its competing use
while preserving uses in the revocation's past. The general existence and
query-agreement bridge must be established separately; the concurrent-owner
counterexample provides no negative result about that target.

Run the focused checks with:

```
lake build Sal.MRDTs.Paper1.CapabilityGroupSpec Sal.MRDTs.Paper1.CapabilityGroupBridge
```
