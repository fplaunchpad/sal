# Capability-group enquiry

## Question and initial claims

Can a fixed-owner group combine dynamic grants and named revocations while preserving the precursive/discursive distinction of Jacob, Stuber, and Hartenstein, *Towards System-Oriented Formal Verification of Local-First Access Control* (PaPoC 2026), Spec. 2, and how does this semantics relate to Sal replay?

Candidate claim: union convergence and immutable causal admission coexist with nonmonotone discursive authorisation. A revoke suppresses concurrent and successor uses of its named grant, but preserves causal precursor assignments. A fresh grant identifier permits a later assignment. Unauthorized administrative events cannot affect names or capability queries.

Smallest falsifier: one owner grant, a concurrent user assignment and owner revoke, followed by a causal successor assignment or fresh grant. Erasing the concurrent assignment while also erasing a causal precursor assignment would expose a wrong global-tombstone interpretation. The Lean oracle is `CapabilityGroup.lean` with literal PASS+FAIL controls in `CapabilityGroupSPOT.lean`; the independent sequential/replay question is handled in the bridge files.

Reality oracle: the paper's Spec. 1 and Spec. 2, Section 3 authorisation/revocation/query safety, Section 4.2's three restricted algorithms, and Section 5's next step combining grants and revokes. Source: <https://arxiv.org/html/2604.23560>. The supplied PDF was read directly. The paper does not claim to verify a combined grant/revoke implementation.

## Model boundary

The model specializes administrative authority to an immutable owner. Event subjects are already authenticated: equality with the owner is an abstract precondition, not a cryptographic proof. Grant identifiers are unique grant-event identifiers. Events carry immutable sets of precursor IDs. Valid histories enforce unique event IDs, precursor availability, transitive downward closure, and an ID rank that rules out causal cycles. The rank is a modelling restriction; it is not a wall-clock rule or a proof about hash identifiers.

Creation/setup and its immutable owner grant/revoke authority are represented by the owner parameter. Dynamic grants only confer permission to assign a group name. Revocations name a grant precursor. Delegation, mutual administrators, membership/query permission, sparse replication, cryptography, Byzantine dissemination, garbage collection, and extraction are absent. Unlike the paper's recursive general authorisation relation, administrative authorisation cannot be revoked in this specialization.

Precursive admission consults only immutable precursors. Discursive query authorisation also consults concurrent events, but excludes causal successors. Group names retain all causally maximal discursively authorised assignments, matching Spec. 2's multi-value query. Union convergence is a separate claim from security and from refinement to a sequential specification.

## Evidence status

The results below are **machine-checked**. Trusted semantic correspondence is a manual specialization of the primary paper, not a mechanized equivalence proof. The [sequential analysis](capability-group-sequential.md) records the independent specification and checked concurrent-owner obstruction separately.

## Checked results

The following results are **machine-checked** by `lake build Sal.MRDTs.Instances.CapabilityGroupSPOT Sal.MRDTs.Instances.CapabilityGroupOwnerOrder`. Definitions use executable finite sets; concrete controls use kernel `decide`, with no `sorry`, added axiom, or `native_decide`.

| Claim | Lean evidence | Exact scope |
|---|---|---|
| Union converges | `merge_comm`, `merge_assoc`, `merge_idem`, `names_converge` | Raw event-set lattice; independent of authorisation |
| Only authorised new revocations can change old discursive authorisation | `authorization_safety` | Structurally valid extension with fresh event ID |
| Causal admission is immutable | `pre_extension`, `admission_stable` | Old event in a closed history, compatible extension with unique IDs |
| Dynamic administration has causal prerequisites | `assignment_requires_owner_grant`, `unauthorized_grant`, `unauthorized_revoke` | Fixed authenticated owner, named grant precursor |
| Concurrent/successor uses lose authorisation | `revoked_use_suppressed`, `revoked_grant_rejects_fresh_use` | Authorized named revoke; assignment is not its causal precursor; fresh IDs for backdated candidates |
| Causal precursor assignments survive revocation | `precursor_use_preserved` | A matching grant exists and every relevant authorised revoke follows the assignment |
| Query authorisation implies causal admission | `discursive_implies_admission` | All event histories, including malformed histories |
| Unauthorized administration has no query effect | `unauthorized_admin_auth_unchanged`, `unauthorized_admin_names_unchanged`, `unauthorized_admin_caps_unchanged` | Sender differs from owner; no newly inserted event is an old precursor |
| A malformed owner revoke is inert | `rejected_revoke_auth_unchanged`, `rejected_revoke_names_unchanged` | Revoke rejected at the resulting state, including missing-target-precursor cases |
| Valid extensions imply the no-new-precursor premise | `new_not_before_old` | Closed source state, unique-ID extension |
| Local issuance and delivery preserve structural validity | `wellFormed_step`, `wellFormed_union` | Full local observation and fresh rank for issuance; compatible IDs for union |
| Stored causal admission survives issue and delivery | `locallyAdmitted_step`, `locallyAdmitted_union` | A `CanIssue` certificate for local writes; closed compatible histories for delivery |
| A single owner issuer preserves an owner chain | `ownerOrdered_step` | Owner operations share full local history; merge of multiple owner devices need not preserve this |
| Owner-chain placement defines an initial segment | `OwnerOrder.cut_is_initial_segment` | `WellFormed` and `OwnerOrdered` |
| Source authorisation equals the ordinary ACL acceptance guard at the cut | `OwnerOrder.source_authorized_iff_cut_guard` | Causally admitted assignment in a valid history; cut ACL tables summarize grants/revokes |

The hand-derived PASS+FAIL scenarios cover owner grant and use, wrong-recipient borrowing, concurrent revoke versus admission, causal-before-revoke preservation, post-revoke denial, a fresh grant ID, delayed delivery, unauthorised grant/revoke, causal overwrite, concurrent multi-value names, valid histories, missing-precursor rejection, and local issuance. Owner-cut controls distinguish a concurrent revoke from a causal successor revoke. These directed controls are not a randomized test campaign or a complete differential validation against the paper's Rust implementation.

## Honest owner-chain bridge remains open

`OwnerOrder.cut_is_initial_segment` places each assignment after owner events that are not its causal successors, including concurrent administration, and before its owner successors. This proves the relevant administrative cut exists in an owner chain. `source_authorized_iff_cut_guard` relates authorisation at that cut to the independent ACL machine's acceptance guard. The cut's grant/revoke summaries are explicit finite tables, not a proof that a complete sequential run reaches those tables.

A theorem constructing a complete list of all events with these cuts, proving it meets Sal's visibility/order requirements, and proving equality of the final multi-value name projection with the independent sequential machine remains **open**. Do not report the local guard theorem as full sequential refinement. The separate bridge analysis records the actual Sal criterion and its finite contrast with stronger visibility obligations.
