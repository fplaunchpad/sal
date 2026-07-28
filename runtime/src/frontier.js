// THE ONE FRONTIER: a single, pure computation read by the evidence-certificate
// producer here, the stability cut of src/compact.js, and the keep-set commit
// GC of src/gc.js.
//
// A replica's FRONTIER at a head version v is, per registered replica j, the
// LATEST commit authored by j that lies in v's reflexive ancestry. This is
// exactly the "evidence commit c_j" of AllHeardSince:
//
//   AllHeardSince C v S  :=  for every registered replica j, v's ancestry
//     contains a commit c_j (reaching v) with S subseteq E(c_j) and a
//     certification that every LATER j-event has all of S in its causal past.
//
// Here c_j = frontierOf(dag, v)[j], and "S subseteq E(c_j)" is CHECKED, not
// assumed. The certification comes for free from the commit shape: j's
// authored commits form a CHAIN by ancestry (each commit() extends j's own
// head; merges only splice branches below it), so every j-event not in
// E(c_j) is a descendant of c_j, hence causally after everything in E(c_j),
// in particular after all of S once S subseteq E(c_j). That is precisely the
// evidence commit's cert clause.
//
// COMMIT-SHAPED, NOT EVENT-SHAPED: the frontier is a function of ANCESTRY,
// never of "did this pull bring new events". A pull that adds no new events can
// still move c_j forward in the DAG (it is now an ancestor), which can be what
// opens SettledAt. Callers therefore recompute the frontier from the head id on
// every commit/sync, and never gate the update on event-subsumption.
// `frontierOf` reads the ancestry directly, so this is structural.

/** frontierOf(dag, headId) -> Map replicaName -> { id, seq }.
 *  The latest authored commit per replica in headId's reflexive ancestry.
 *  (Merge and root commits carry op === null and are not authored.) */
export function frontierOf(dag, headId) {
  const fr = new Map();
  for (const cid of dag.ancestorSet(headId)) {
    const { op } = dag.get(cid);
    if (op === null) continue;
    const cur = fr.get(op.replica);
    // authored commits of a replica chain by ancestry, so max seq = latest
    if (!cur || op.seq > cur.seq) fr.set(op.replica, { id: cid, seq: op.seq });
  }
  return fr;
}

/** The event set E(id) as a Map eventKey -> op over id's reflexive ancestry.
 *  eventKey = "replica:seq" uniquely names an authored op across the DAG (and
 *  across separate stores that agree on replica ids and seq counters). */
export function eventOps(dag, id) {
  const m = new Map();
  for (const cid of dag.ancestorSet(id)) {
    const { op } = dag.get(cid);
    if (op !== null) m.set(op.replica + ':' + op.seq, op);
  }
  return m;
}

/** THE CERTIFIED STABLE CUT at head `headId` for the compacting replica
 *  `self`, over the closed registered set `registeredNames`.
 *
 *  The cut is the MEET (intersection) of the event sets of the frontier
 *  commits of every OTHER registered replica -- the largest cut
 *  AllHeardSince certifies at `headId`. The compacting replica self-certifies
 *  via `headId` itself (all of self's events are in E(headId), and the meet
 *  is subseteq E(headId) since every frontier commit is an ancestor of
 *  headId), so self is excluded from the meet: including it would only shrink
 *  the cut to self's last local commit, never enlarge it.
 *
 *  THE NOT-HEARD-FROM BREAKER: a registered replica j != self with NO frontier
 *  commit in headId's ancestry has not been heard from, so it may hold an op
 *  concurrent with the cut that this replica has never absorbed. The
 *  certificate is then INCOMPLETE and no non-empty cut may be certified.
 *  Absence of evidence is refusal, never assumption. This is the runtime
 *  witness of the not-heard breaker.
 *
 *  Soundness of excluding a heard replica j: its frontier commit c_j has
 *  meet subseteq E(c_j), so any event e concurrent with a cut event s was
 *  minted by j (or another heard replica) BEFORE it heard s, hence e is at or
 *  below c_j and already in E(c_j) subseteq E(headId). Every op concurrent
 *  with the cut is therefore already delivered here -- SettledAt condition 2.
 *
 *  Returns { complete, meet: Map(eventKey -> op), missing: [names],
 *            frontier: Map }. When complete and there is no other registered
 *  replica, the whole of E(headId) is stable (single-writer). */
export function stableCut(dag, headId, registeredNames, self) {
  const fr = frontierOf(dag, headId);
  const sets = [];
  const missing = [];
  for (const name of registeredNames) {
    if (name === self) continue;
    const c = fr.get(name);
    if (c) sets.push(eventOps(dag, c.id));
    else missing.push(name); // registered, never absorbed here: not heard from
  }
  const complete = missing.length === 0;
  let meet;
  if (!complete) {
    meet = new Map(); // uncertifiable: refuse any non-empty cut
  } else if (sets.length === 0) {
    meet = eventOps(dag, headId); // self alone: the whole history is settled
  } else {
    sets.sort((a, b) => a.size - b.size); // intersect starting from the smallest
    meet = new Map();
    for (const [k, op] of sets[0]) if (sets.every((s) => s.has(k))) meet.set(k, op);
  }
  return { complete, meet, missing, frontier: fr };
}

/** The embed-RGA settled-id cut from a meet: the insert ids of the meet's
 *  ops -- exactly compact.js's cut.settledIds representation. A
 *  deleted-but-settled id stays listed via its insert op (its dead-ancestor
 *  chain persists); a delete op needs no separate listing (its record is
 *  already absent, and a future delete carries no coordinate). Under a
 *  certified cut this is sound with cut.inflight EMPTY. */
export function insertIds(meet) {
  const ids = new Set();
  for (const op of meet.values()) {
    // op.payload is a single op, or an op ARRAY for a group-op (batch) commit.
    const ps = Array.isArray(op.payload) ? op.payload : op.payload ? [op.payload] : [];
    for (const p of ps) if (p.type === 'ins') ids.add(p.id);
  }
  return ids;
}
