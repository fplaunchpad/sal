# The stability VC: verified GC callbacks for conditioned MRDTs

*Design note for task #96. Pen and paper phase; Lean owed. Self contained.*

## 1. The problem

The runtime (task #94) learns which events have reached every replica
and calls back into the datatype so the concrete state can shed
redundant records. The motivating example: an OR-set holding two add
instances of the same element. Once both adds are known everywhere, the
instances share every future fate, so one record suffices. The
question is what the datatype must prove for such a `compact` to be
sound, and what exactly the runtime must promise it.

## 2. The interface: SettledAt, not the meet

The naive contract ("S is contained in every current head") is
UNSOUND, by the following near miss, which shapes everything after it.

**The discriminating remove.** Adds of element a at stamps t1 < t2,
both below every head. Replica A compacts, dropping the older instance
t1. But an in-flight remove, minted long ago by a replica that had
observed only t2 (the remove is concurrent with add t1), is still ≤
some head and arrives later. In the full execution the remove kills
only t2 and a survives through t1; in the compacted execution t1 is
gone and a is absent. Observable divergence: reads differ.

The repair is a version level condition. Say a cut S is **SettledAt**
version v when:

1. S ⊆ E(v), S causally downward closed;
2. every event concurrent with an event of S that exists anywhere is
   already in E(v).

Condition 2 is dischargeable by the runtime, not the datatype: an event
concurrent with s ∈ S was minted by some replica j before j saw s; the
evidence that j saw s is a commit c_j with s ∈ E(c_j); the concurrent
event precedes c_j at j. So if v has absorbed such a commit c_j **for
every replica j** (v has heard from everyone since S), then all
concurrency of S is inside E(v). This is causal stability in the sense
of Baquero, Almeida, and Shoker, transplanted from op-based delivery to
the commit DAG: there the argument rides on causal delivery order, here
on downward closure of event sets. The callback therefore fires
`compact(σ_v, S)` only at versions where the runtime can exhibit the
per replica evidence commits; the frontier data needed is the same
all-heads knowledge that the commit GC (gc_safety) and the in-flight
anchor argument (embed re-coding note) already require. One frontier,
three consumers.

## 3. Two species of compaction

**Drop species** (OR-set, MVR, rem-record GC): `compact` removes
records from the state. Under the live-set merge rule a removed record
propagates exactly like a deletion, so compaction spreads through
merges without any protocol.

**Remap species** (embed RGA re-coding, task #97): `compact` rewrites
coordinates by an order isomorphism below the cut; mixed states need
translation on ingest (the stable-prefix map). The congruence theorems
for this species are already mechanized (eRecode_applySeq and its
cluster); what #96 adds is the discharge of their standing hypothesis
(the cut) by the SettledAt contract.

One VC skeleton covers both, with the simulation relation R_S equal to
"differ only by S-redundant records" for the drop species and to the
graph of the coordinate isomorphism for the remap species.

## 4. The VC set

Fix a conditioned MRDT ⟨Σ, σ0, do, merge, rc, Inv, applicable, ≈⟩, a
cut S, and a compaction `compact : Σ → Σ` with a simulation relation
R_S ⊆ Σ × Σ (full on the left, compacted on the right).

- **(VC-S1) Entry.** SettledAt v S implies σ_v R_S compact(σ_v).
- **(VC-S2) Observation.** σ R_S τ implies query σ = query τ, for
  every query of the datatype's read interface.
- **(VC-S3) Step preservation.** σ R_S τ implies do o σ R_S do o τ,
  for every op o that is either (a) minted with S in its causal past
  (all future ops, by stability), or (b) an in-flight op ≤ some
  current head. Class (b) is where references to dropped records
  arrive (a kill set naming a dropped instance, an anchor naming a
  re-coded coordinate); R_S must absorb them. Note class (b) ops
  concurrent with S are, by SettledAt, already inside E(v), so at the
  compacting version itself only class (a) remains; class (b) matters
  at OTHER replicas that compact later or never.
- **(VC-S4) Merge congruence, argumentwise.** merge respects R_S in
  each argument independently: L R_S L' implies
  merge L A B R_S merge L' A B, and similarly in A and B. Argumentwise
  is forced because mixed executions are the normal case: a compacted
  head merging against a full LCA payload, or against a replica that
  never compacted.
- **(VC-S5) Contract preservation.** R_S preserves Inv, preserves the
  applicable set up to redundant references, and preserves the honesty
  contract the capstone consumes. This is the clause that composes
  compaction with the conditioned framework, and the one with no
  analogue in the unverified systems.
- **(VC-S6) Epoch coherence.** compact at S then at S' ⊇ S lands in
  the same R_{S'} class as compact at S' directly; so staggered and
  repeated compactions across replicas stay related.

## 5. The metatheorem

Lift R_S to configurations (versions pointwise related, DAG shape
shared). Given VC-S1 through VC-S6 and the runtime contract (head sync
plus SettledAt certification), every step of the execution model
preserves the lifted relation, with compaction itself a stuttering
step on the compacted side. Conclusion: every version of every
reachable configuration reads identically in the compacted and the
uncompacted execution, and the compacted system inherits
RA-linearizability up to ≈ observationally from the uncompacted
capstone. The proof architecture is the external invariant pattern
(the relation is threaded through the step relation without editing
any instance file), which is now three for three in this repo.

## 6. First instance: the OR-set

Redundant_S(σ): among the LIVE instances of an element, those adds in
S that are not the newest such instance. Under SettledAt every remove
that could discriminate between two S-instances is already applied in
σ (section 2), so the surviving S-instances live and die together from
here on; dropping all but the newest is sound. VC-S3 class (b) is the
interesting case: a remove minted elsewhere against a full state
carries a kill set that may name a dropped instance; on the compacted
side the kill is a partial no-op, and the states stay in R_S because
the dropped instance's fate is determined by the kept one. VC-S4 rides
on the live-set rule: absence propagates like deletion.

## 7. What the Lean owes, in order

1. The SettledAt definition at the framework level (Configuration +
   event sets; the evidence-commit form) and the runtime-facing lemma
   "heard from everyone since S implies concurrency containment".
2. The VC bundle as a structure (StabilityVC), the lifted relation,
   and the metatheorem (stability_simulation).
3. The OR-set instance: Redundant_S, compact, R_S, the six discharges.
4. The remap species bridge: eRecode's standing cut hypothesis
   discharged by SettledAt (connects #97; the held compactEliasDelta
   then slots in as the second instance).

## 8. Deferred

Open membership (the evidence quantifies over a known replica set);
compaction of historical (non-head) payloads interacts with the commit
GC keep set and is deferred to the #102 representation swap; the
FugueMax remap under tags is #89/#97 territory.

## 9. Errata and sharpenings from the validation pass

The harness (`litmus/stability_vc_check.py`: the countermodel fires
under the naive gate, SettledAt is clean, 500/500 and 2000/2000 twin
trials) forced four corrections, recorded here so this note stays the
source of truth.

1. **LCA resolution must be lineage aware once compaction exists.**
   Resolving the exact intersection LCA by event set alone is sound
   before compaction (payload is a function of the event set) and
   UNSOUND after: a same event set version from an unrelated lineage
   used as L resurrects a dropped instance through B minus L once a
   later rem killed its kept twin (found as a genuine randomized twin
   divergence, seed 2026 trial 218, not injected). The framework's
   structural IsLCA already resolves within shared ancestry, so the
   Lean model is right as it stands; but any representation swap that
   identifies versions by clocks or event sets (the task #102 route)
   must retain enough lineage, or restrict lookup to R_S compatible
   payloads. Compaction makes payload no longer a function of the
   event set; that is the whole content of this sharpening.

2. **VC-S4 needs a reachability side condition.** Unconditioned
   argumentwise congruence at the L argument is false for the OR-set
   R_S: with L_full related to L_compacted, an A past a rem that
   killed the kept twin, and a B still carrying the dropped instance
   live, the two merges read differ. The offending triple is
   unreachable (any state descending from the compacted L sheds the
   drop at its first absorption merge), so the metatheorem stands, but
   the Lean VC-S4 must be stated over reachable triples or with an
   indexed relation, not as a free congruence.

3. **Evidence is commit shaped, not event shaped.** A pull that brings
   no new events can still bring the evidence commit that opens
   SettledAt. A runtime that skips event subsumed pulls silently
   starves the callback; the no-op condition must be "the pulled head
   is already in the puller's ancestry".

4. In the directed countermodel, the delivery merge needs a shared
   full both-adds LCA, so the rem minter must pull the compactor's own
   pre-compaction merge version; pulling the add branch directly makes
   the delivery pair criss-cross and the naive compaction
   unobservable. A choreography note, not a soundness item.

## 10. Errata and sharpenings from the mechanization pass

Recorded from the Lean (Metatheory/Stability_VC.lean, ORSet_Stability,
EmbedRGA_Stability_Bridge); the note stays the source of truth.

1. VC-S3 class (b) is absorbed into VC-S4: in the state-based ternary
   model, in-flight effects arrive only through merge branch states, so
   the step VC covers class (a) only.
2. Redundant_S must be state dependent even under the settled gate: a
   static drop set is unsound when the kept twin has already died
   before compaction (SPOT static_drop_unsound); the sound callback is
   the twin-liveness-guarded drop. Newest-first is not needed for
   soundness; any live kept witness preserves reads.
3. The gate is SettledAt AND AllHeard: settledness alone is not stable
   under future mints by ignorant replicas; the all-heads frontier
   keeps it stable, and createReplica after a compaction is policy
   gated (the section 8 open-membership deferral made operational).
4. VC-S6 holds observationally, not as a same-R-class statement: a
   first-epoch-dropped tag whose second-epoch keeper has died is kept
   by the direct coarser compaction; reads still agree.
5. Query labels match only up to the observation; raw values may
   differ.
6. Mechanization convenience: compaction projects to a stuttering
   SELF-MERGE on the full side (IsLCA is reflexive, E union E = E), so
   the twin DAGs stay literally identical and no version-map
   bisimulation is needed. This is why stability_simulation needs only
   propext and Quot.sound.
