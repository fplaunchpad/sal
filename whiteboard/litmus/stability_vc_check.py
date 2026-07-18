#!/usr/bin/env python3
"""stability_vc_check.py -- task #96, validation of whiteboard/stability-vc-note.md.

Machine-checks the note's two central claims on the OR-set instance, before
mechanization:

  (A) The naive compaction contract ("the cut S is contained in every current
      head", i.e. meet-of-heads stability) is UNSOUND: the discriminating-remove
      countermodel of note section 2 makes reads diverge between the full and
      the compacted execution.
  (B) The SettledAt contract (note section 2: the compacting version has
      absorbed, for every replica j, an evidence commit by j containing S)
      repairs it: the same scenario stays read-identical everywhere forever,
      and randomized twin executions (control vs compact-at-every-SettledAt-
      opportunity) never diverge.

Model (matches the note's execution model):
  * Replicas over a version DAG.  Commit = local op extends the head.
    Sync = one replica pulls another: three-way merge at the
    exact-intersection LCA (the earliest version whose event set equals the
    intersection of the two heads' event sets); criss-cross pairs (no such
    version) are skipped.
  * OR-set: state = set of live instances (elem, stamp).  add mints an
    instance (stamp := its event id, a global total order).  rem kills
    exactly the instances of the element OBSERVED in the minter's state at
    mint time, carried as an explicit kill set, so in-flight rems replay
    correctly through merges.  merge = live-set rule
    (L cap A cap B) u (A \\ L) u (B \\ L), instance-wise.
  * Compaction (drop species, note section 3/6) rewrites the replica's LIVE
    state only; stored version payloads are immutable (compaction of
    historical payloads is deferred, note section 8).  Redundant_S = among
    the live instances of an element, the adds in S that are not the newest
    such instance.

Findings forced by the simulation (erratum candidates for the note):
  1. The exact-intersection LCA must be resolved WITHIN THE SHARED ANCESTRY
     of the two heads.  Under compaction, payload stops being a function of
     the event set, and a same-event-set version from an unrelated lineage
     used as L resurrects dropped instances via B \\ L (see World._lca).
  2. VC-S4 read as UNCONDITIONED argumentwise congruence is false at the
     L-argument: with L_full R_S L_compacted, A past a rem that killed the
     kept twin, and B still carrying the dropped instance live,
     merge(L_full,A,B) and merge(L_compacted,A,B) read-differ.  The triple
     is unreachable (any state descending from L_compacted has already shed
     the drop), so the metatheorem stands, but the Lean VC-S4 needs that
     reachability side condition.
  3. A pull that brings no new EVENTS can still bring the evidence COMMIT:
     sync must only skip pulls whose head commit is already in the puller's
     ancestry, else SettledAt is starved (see World.sync).
  4. Under the ancestry-resolved LCA, the countermodel needs the delivery
     merge to share a full {both-adds} LCA; the rem-minter must pull the
     compactor's own pre-compaction merge version (see build_countermodel).

Run:  python3 whiteboard/litmus/stability_vc_check.py [seed] [trials]
      (defaults: seed 96, trials 500).  Exit 0 iff every check passes.
"""

import random
import sys

ADD, REM = "add", "rem"


class World:
    """One execution: version DAG + per-replica heads and live states."""

    def __init__(self, n_replicas):
        self.n = n_replicas
        self.events = {}      # eid -> (kind, elem, data); data = stamp | kill set
        self.next_eid = 1
        self.versions = {}    # vid -> dict(rid, events, payload, anc)
        self.next_vid = 1
        self.by_events = {}   # frozenset(eids) -> EARLIEST vid with that event set
        self.versions[0] = dict(rid=None, events=frozenset(),
                                payload=frozenset(), anc=frozenset({0}))
        self.by_events[frozenset()] = [0]
        self.head = [0] * n_replicas
        # Live state; may be compacted strictly below the head's stored payload.
        self.state = [frozenset()] * n_replicas
        self.compactions = 0  # compact calls that dropped >= 1 instance
        self.dropped = 0      # total instances dropped

    # -- DAG plumbing ------------------------------------------------------

    def _new_version(self, rid, events, payload, parents):
        vid = self.next_vid
        self.next_vid += 1
        anc = frozenset({vid}).union(*(self.versions[p]["anc"] for p in parents))
        self.versions[vid] = dict(rid=rid, events=events, payload=payload, anc=anc)
        self.by_events.setdefault(events, []).append(vid)  # in creation order
        return vid

    def _lca(self, hi, hj):
        """Exact-intersection LCA: the earliest COMMON-ANCESTOR version whose
        event set equals E(hi) & E(hj); None = criss-cross.

        The ancestry constraint is load-bearing (found the hard way): under
        compaction, payload is no longer a function of the event set, and
        resolving L globally by event set can pick a same-event-set version
        from an unrelated lineage whose payload dropped an instance that i/j
        still carry live -- the live-set rule then resurrects it via B \\ L
        after a later rem killed its kept twin (twin divergence, seed 2026)."""
        inter = self.versions[hi]["events"] & self.versions[hj]["events"]
        shared = self.versions[hi]["anc"] & self.versions[hj]["anc"]
        for vid in self.by_events.get(inter, ()):
            if vid in shared:
                return vid
        return None

    def _commit(self, i, eid, new_state):
        h = self.head[i]
        ev = self.versions[h]["events"] | {eid}
        vid = self._new_version(i, ev, new_state, (h,))
        self.head[i] = vid
        self.state[i] = new_state
        return vid

    # -- OR-set operations -------------------------------------------------

    def do_add(self, i, elem):
        eid = self.next_eid
        self.next_eid += 1
        self.events[eid] = (ADD, elem, eid)          # stamp := event id
        return self._commit(i, eid, self.state[i] | {(elem, eid)})

    def do_rem(self, i, elem):
        # Kill exactly the instances observed at mint time (explicit kill set).
        kill = frozenset(inst for inst in self.state[i] if inst[0] == elem)
        eid = self.next_eid
        self.next_eid += 1
        self.events[eid] = (REM, elem, kill)
        return self._commit(i, eid, self.state[i] - kill)

    # -- Head sync ---------------------------------------------------------

    def sync(self, i, j):
        """Replica i pulls replica j.  Returns 'noop' | 'crisscross' | 'merged'.

        NOTE the skip condition: a pull is a no-op only when j's head COMMIT
        is already in i's ancestry.  Skipping merely event-subsumed pulls
        (Ej <= Ei) would be observationally harmless but starves SettledAt:
        evidence rides on absorbed commits, and a pull bringing no new events
        can still bring the evidence commit (found while validating (3))."""
        hi, hj = self.head[i], self.head[j]
        if hj in self.versions[hi]["anc"]:
            return "noop"
        lca = self._lca(hi, hj)
        if lca is None:
            return "crisscross"                      # no exact-intersection LCA
        Ei = self.versions[hi]["events"]
        Ej = self.versions[hj]["events"]
        L = self.versions[lca]["payload"]            # stored payload (immutable)
        A, B = self.state[i], self.state[j]
        m = (L & A & B) | (A - L) | (B - L)          # live-set rule, instance-wise
        vid = self._new_version(i, Ei | Ej, m, (hi, hj))
        self.head[i] = vid
        self.state[i] = m
        return "merged"

    # -- Queries -----------------------------------------------------------

    def read(self, i):
        """The OR-set read interface: the set of present elements."""
        return frozenset(e for (e, _t) in self.state[i])

    # -- Stability contracts -----------------------------------------------

    def naive_stable(self, S):
        """The NAIVE contract: S below every current head (meet-of-heads)."""
        return all(S <= self.versions[h]["events"] for h in self.head)

    def settled_at(self, vid, S):
        """SettledAt v S: for every replica j, v has absorbed an evidence
        commit by j whose event set contains S (note section 2)."""
        anc = self.versions[vid]["anc"]
        for j in range(self.n):
            if not any(self.versions[c]["rid"] == j
                       and S <= self.versions[c]["events"] for c in anc):
                return False
        return True

    def settled_cut(self, vid):
        """Largest settled cut at vid: intersect, over every replica j, the
        largest event set of a j-commit absorbed by vid.  (A replica's commits
        are nested, so 'largest' is well defined.)  None if some replica has
        no absorbed commit yet."""
        cut = None
        for j in range(self.n):
            best = None
            for c in self.versions[vid]["anc"]:
                v = self.versions[c]
                if v["rid"] == j and (best is None or len(v["events"]) > len(best)):
                    best = v["events"]
            if best is None:
                return None
            cut = best if cut is None else cut & best
        return cut

    # -- Compaction (drop species) -----------------------------------------

    def redundant(self, i, S):
        """Redundant_S: among the LIVE instances of an element, the adds in S
        that are not the newest such instance."""
        by_elem = {}
        for (e, t) in self.state[i]:
            if t in S:
                by_elem.setdefault(e, []).append(t)
        drop = set()
        for _e, ts in by_elem.items():
            if len(ts) > 1:
                keep = max(ts)
                drop.update((_e, t) for t in ts if t != keep)
        return frozenset(drop)

    def compact(self, i, S):
        """Drop Redundant_S from replica i's live state.  Stored payloads are
        untouched (historical compaction deferred, note section 8)."""
        d = self.redundant(i, S)
        if d:
            self.state[i] = self.state[i] - d
            self.compactions += 1
            self.dropped += len(d)
        return d


# ===========================================================================
# (2)+(3)  The discriminating-remove countermodel (note section 2)
# ===========================================================================
#
# Replicas R0, R1, R2.  Adds of element a at stamps t1 < t2 on different
# branches, fully synced so S = {e1, e2} is below every head (the naive
# contract holds at R2).  An in-flight remove, minted by R1 when it had
# observed ONLY t2 (concurrent with add t1), kills t2 and has not yet
# reached R0 or R2.  All expected values below are hand-derived.
#
# Choreography constraint (found while validating): with the LCA resolved in
# the SHARED ancestry, the delivery merge R2<-R1 needs a common {e1,e2}
# version.  So R2 builds V' = merge {t1,t2} first, and R1 (after minting the
# rem) pulls R2, putting V' below R1's head; V' is then the full LCA of the
# delivery merge.  (Pulling R0 instead makes the delivery pair criss-cross.)

def build_countermodel():
    """Returns (world, S).  Heads after build: R0 = {e1,e2}, R1 = {e1,e2,e3},
    R2 = {e1,e2} with state {t1,t2}; the rem e3 (kill {t2}) is in-flight
    w.r.t. R0 and R2."""
    w = World(3)
    w.do_add(0, "a")                    # v1: e1, instance t1 = (a,1)
    w.do_add(1, "a")                    # v2: e2, instance t2 = (a,2)
    assert w.sync(2, 0) == "merged"     # v3: R2 = {t1}, events {e1}
    assert w.sync(2, 1) == "merged"     # v4 = V': R2 = {t1,t2}, events {e1,e2}
    w.do_rem(1, "a")                    # v5: e3, kill = {t2} (R1 saw only t2)
    assert w.events[3] == (REM, "a", frozenset({("a", 2)})), \
        "the remove must have observed ONLY t2"
    assert w.sync(1, 2) == "merged"     # v6: R1 = {t1} (a survives through t1)
    assert w.sync(0, 2) == "merged"     # v7: R0 = {t1,t2}, events {e1,e2}
    S = frozenset({1, 2})               # the two adds
    assert w.naive_stable(S), "S must be below every head (naive gate open)"
    assert w.state[2] == frozenset({("a", 1), ("a", 2)})
    return w, S


def run_countermodel(gate):
    """Twin run of the countermodel under compaction gate 'naive' or
    'settled'.  Returns (control, treatment, log)."""
    ctl, S = build_countermodel()
    trt, _ = build_countermodel()
    log = []

    # Compaction attempt at R2's head.
    if gate == "naive":
        assert trt.naive_stable(S)
        fired = trt.compact(2, S)
        log.append("naive gate open at R2; compact dropped %s" % sorted(fired))
        assert fired == frozenset({("a", 1)}), "must drop the OLDER instance t1"
    else:
        ok = trt.settled_at(trt.head[2], S)
        log.append("SettledAt at R2's head: %s (no evidence commit from R0 or "
                   "R1 contains S)" % ok)
        assert not ok, "SettledAt must REFUSE compaction here"
        # Gate closed: no compaction happens.

    # The in-flight remove arrives at R2 (pull from R1).
    for wname, wrld in (("control", ctl), ("treatment", trt)):
        r = wrld.sync(2, 1)
        assert r == "merged", (wname, r)
    log.append("after rem arrives: control R2 reads %s, treatment R2 reads %s"
               % (sorted(ctl.read(2)), sorted(trt.read(2))))

    if gate == "settled":
        # Keep syncing; the gate must open only once R2 has heard from
        # everyone since the cut, at which point nothing is redundant.
        for wrld in (ctl, trt):
            assert wrld.sync(2, 0) == "merged"
        assert trt.settled_at(trt.head[2], S), \
            "SettledAt must hold once evidence from R0 and R1 is absorbed"
        fired = trt.compact(2, S)
        log.append("SettledAt now holds at R2; Redundant_S = %s" % sorted(fired))
        assert fired == frozenset(), \
            "rem already applied: only t1 lives, nothing redundant"
        # 'Forever': run a full sync closure and compare reads at every step.
        for _round in range(3):
            for i in range(3):
                for j in range(3):
                    if i == j:
                        continue
                    ctl.sync(i, j)
                    trt.sync(i, j)
                    for k in range(3):
                        assert ctl.read(k) == trt.read(k), \
                            ("post-closure divergence", i, j, k)
    return ctl, trt, log


def test_countermodel_naive():
    """(2) Directed: the naive contract MUST fail (reads diverge)."""
    ctl, trt, log = run_countermodel("naive")
    c, t = ctl.read(2), trt.read(2)
    assert c == frozenset({"a"}), "full execution: a survives through t1"
    assert t == frozenset(), "compacted execution: a is absent"
    assert c != t, "reads must DIVERGE under the naive contract"
    return log + ["VERDICT: countermodel FIRES (control %s vs treatment %s)"
                  % (sorted(c), sorted(t))]


def test_countermodel_settled():
    """(3) Directed: under SettledAt the same scenario stays identical."""
    ctl, trt, log = run_countermodel("settled")
    for k in range(3):
        assert ctl.read(k) == trt.read(k) == frozenset({"a"}), \
            ("reads must be identical everywhere", k)
    return log + ["VERDICT: SettledAt CLEAN (all replicas read {a} in both runs)"]


# ===========================================================================
# (5)  VC-S4 argumentwise spot-check: mixed merge, compacted head vs full
#      LCA payload and full sibling (note section 4, VC-S4)
# ===========================================================================

def _vc_s4_world(compacting):
    w = World(3)
    w.do_add(0, "a")                    # v1: e1, t1
    assert w.sync(1, 0) == "merged"     # v2
    w.do_add(1, "a")                    # v3: e2, t2; payload {t1,t2} (full LCA-to-be)
    assert w.sync(2, 1) == "merged"     # v4: R2 = {t1,t2}
    w.do_add(2, "b")                    # v5: e3, t3; evidence commit by R2
    assert w.sync(0, 1) == "merged"     # v6: evidence commit by R0
    assert w.sync(0, 2) == "merged"     # v7: R0 = {t1,t2,t3}
    S = frozenset({1, 2})
    assert w.settled_at(w.head[0], S), "S must be settled at R0"
    assert w.settled_cut(w.head[0]) == S, "largest settled cut must be S"
    if compacting:
        fired = w.compact(0, S)         # a legitimate SettledAt compaction
        assert fired == frozenset({("a", 1)}), "drops the older settled add"
    w.do_add(1, "c")                    # v8: e4, t4 -- the full sibling's news
    return w


def test_vc_s4_argumentwise():
    """Directed mixed merge: R0's COMPACTED head merges against the FULL
    stored LCA payload (v3 = {t1,t2}) and the FULL sibling R1; then R2 (full)
    merges against the compacted branch.  Reads must match the all-full
    control at every replica.  Expected values hand-derived."""
    ctl = _vc_s4_world(compacting=False)
    trt = _vc_s4_world(compacting=True)
    log = ["after SettledAt compaction at R0: state %s" % sorted(trt.state[0])]
    # A-argument compacted, L and B full.
    for w in (ctl, trt):
        assert w.sync(0, 1) == "merged"
    assert ctl.state[0] == frozenset({("a", 1), ("a", 2), ("b", 3), ("c", 4)})
    assert trt.state[0] == frozenset({("a", 2), ("b", 3), ("c", 4)})
    assert ctl.read(0) == trt.read(0) == frozenset({"a", "b", "c"}), \
        "A-position: compacted head vs full LCA payload and full sibling"
    log.append("A-position mixed merge at R0: both read %s" % sorted(ctl.read(0)))
    # B-argument compacted: full R2 pulls the compacted branch.
    for w in (ctl, trt):
        assert w.sync(2, 0) == "merged"
    assert ctl.read(2) == trt.read(2) == frozenset({"a", "b", "c"})
    assert ("a", 1) not in trt.state[2], \
        "the drop propagates like a deletion (drop species)"
    log.append("B-position mixed merge at R2: both read %s; dropped t1 "
               "propagated" % sorted(ctl.read(2)))
    return log + ["VERDICT: VC-S4 argumentwise spot-check PASSES"]


# ===========================================================================
# (4)  Randomized twin runs: the metatheorem's empirical form
# ===========================================================================

ELEMS = ["a", "b", "c"]


def random_schedule(rng, n, steps):
    sched = []
    for _ in range(steps):
        r = rng.random()
        if r < 0.40:
            sched.append(("add", rng.randrange(n), rng.choice(ELEMS)))
        elif r < 0.55:
            sched.append(("rem", rng.randrange(n), rng.choice(ELEMS)))
        else:
            i = rng.randrange(n)
            j = (i + 1 + rng.randrange(n - 1)) % n
            sched.append(("sync", i, j))
    return sched


def apply_step(w, step):
    if step[0] == "add":
        w.do_add(step[1], step[2])
    elif step[0] == "rem":
        w.do_rem(step[1], step[2])
    else:
        w.sync(step[1], step[2])


def run_twin_trial(sched, n):
    """Control (never compacts) vs treatment (compacts at every SettledAt
    opportunity, at every replica, after every step).  Per-step per-replica
    read equality, then final read equality."""
    ctl, trt = World(n), World(n)
    for idx, step in enumerate(sched):
        apply_step(ctl, step)
        apply_step(trt, step)
        for i in range(n):
            S = trt.settled_cut(trt.head[i])
            if S:
                assert trt.settled_at(trt.head[i], S)
                trt.compact(i, S)
        for i in range(n):
            if ctl.read(i) != trt.read(i):
                return dict(ok=False, step=idx, replica=i,
                            control=sorted(ctl.read(i)),
                            treatment=sorted(trt.read(i)),
                            ctl_state=sorted(ctl.state[i]),
                            trt_state=sorted(trt.state[i]))
    for i in range(n):                       # final reads (redundant but stated)
        if ctl.read(i) != trt.read(i):
            return dict(ok=False, step="final", replica=i,
                        control=sorted(ctl.read(i)),
                        treatment=sorted(trt.read(i)))
    return dict(ok=True, comp=trt.compactions, drop=trt.dropped)


def test_randomized(seed, trials):
    rng = random.Random(seed)
    passed = comp = drop = fired_trials = 0
    for t in range(trials):
        n = rng.randrange(3, 6)                       # 3..5 replicas
        sched = random_schedule(rng, n, rng.randrange(30, 61))
        res = run_twin_trial(sched, n)
        if not res["ok"]:
            print("FIRST-CLASS FINDING: twin divergence in trial %d" % t)
            print("  replicas=%d schedule=%r" % (n, sched))
            print("  at step %s replica %s: control reads %s, treatment %s"
                  % (res["step"], res["replica"], res["control"],
                     res["treatment"]))
            if "ctl_state" in res:
                print("  control state %s" % res["ctl_state"])
                print("  treatment state %s" % res["trt_state"])
            return None
        passed += 1
        comp += res["comp"]
        drop += res["drop"]
        fired_trials += 1 if res["comp"] else 0
    assert drop > 0 and comp > 0, "compaction never fired: the test is toothless"
    return dict(passed=passed, trials=trials, comp=comp, drop=drop,
                fired_trials=fired_trials)


def test_randomized_naive_bite(seed, trials):
    """FAIL companion at the randomized tier: the SAME twin harness, but the
    treatment compacts under the NAIVE gate (omniscient meet-of-heads cut).
    Divergences here show the harness can detect unsoundness; typical rate is
    a few per 500 trials.  A zero count on some seeds is possible, so the
    deterministic unsoundness witness remains the directed countermodel (2);
    this count is reported, not hard-asserted."""
    rng = random.Random(seed)
    diverged = 0
    for _t in range(trials):
        n = rng.randrange(3, 6)
        sched = random_schedule(rng, n, rng.randrange(30, 61))
        ctl, trt = World(n), World(n)
        bad = False
        for step in sched:
            apply_step(ctl, step)
            apply_step(trt, step)
            S = frozenset.intersection(
                *(trt.versions[trt.head[i]]["events"] for i in range(n)))
            if S:
                for i in range(n):
                    trt.compact(i, S)
            if any(ctl.read(i) != trt.read(i) for i in range(n)):
                bad = True
                break
        diverged += 1 if bad else 0
    return diverged


# ===========================================================================
# (6)  Verdict
# ===========================================================================

def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 96
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 500
    print("== stability_vc_check: #96 SettledAt validation (seed=%d) ==\n"
          % seed)
    for line in test_countermodel_naive():
        print("[countermodel/naive]  " + line)
    print()
    for line in test_countermodel_settled():
        print("[countermodel/settled] " + line)
    print()
    for line in test_vc_s4_argumentwise():
        print("[vc-s4]               " + line)
    print()
    r = test_randomized(seed, trials)
    if r is None:
        print("\n== VERDICT: RANDOMIZED TWIN RUNS DIVERGED (see finding) ==")
        return 1
    print("[randomized]          %d/%d twin trials read-identical at every "
          "step and replica" % (r["passed"], r["trials"]))
    print("[randomized]          compactions fired: %d (in %d/%d trials); "
          "instances dropped: %d" % (r["comp"], r["fired_trials"],
                                     r["trials"], r["drop"]))
    nb = test_randomized_naive_bite(seed, trials)
    print("[randomized/naive]    same harness, naive gate: diverged in %d/%d "
          "trials (harness bite indicator)" % (nb, trials))
    print("\n== VERDICT ==")
    print("naive meet-of-heads contract : UNSOUND (countermodel fires; "
          "reads ['a'] vs [])")
    print("SettledAt contract           : SOUND on all checks (directed fix "
          "clean, VC-S4 spot-check clean, twin trials %d/%d)"
          % (r["passed"], r["trials"]))
    print("compaction bite              : %d drops across %d firings"
          % (r["drop"], r["comp"]))
    return 0


if __name__ == "__main__":
    sys.exit(main())
