#!/usr/bin/env python3
"""
equiv_stress.py -- adversarial attack on the observational-equivalence
conjecture: DeltaTreeV3 == published tombstoned RGA (task #69).

The paired design (delta_tree.PairedV3RGA) runs both implementations in
lockstep on identical histories and asserts read-equality at EVERY apply,
merge, and read.  The baseline evidence (full battery + 120/300 DAG PBT) is
thin for a headline conjecture; this file adds three hostile regimes:

  1. GRID   -- pbt.run_execution cranked across a hostile parameter grid
               (p_del 0.4-0.6, up to 10 replicas / 20 rounds / 4 ops-per-turn,
               p_merge 0.4 and 0.7), thousands of executions, fixed seeds.
  2. CHURN  -- a small live string (cap 6-10 chars) hammered by 4-8 replicas
               over hundreds of rounds with high merge probability under the
               same version-DAG LCA discipline as pbt.py (pattern copied, not
               imported behaviourally: a merge is legal only when some
               recorded version's event set equals the two heads'
               intersection).  Over the cap a replica MUST delete; under it,
               it mostly inserts at random anchors including the front.  This
               drives deep dead-chain nesting, heavy rehoming through dead
               ancestors, and heavy ledger traffic -- where divergence hides.
  3. TARGETED -- hand-built litmus-style scenarios: fully-deleted nested
               chains merged against branches that inserted under the dead
               interior; concurrent same-anchor bursts then delete-the-anchor;
               interleaved delete/re-insert cycles across three branches
               merged in every topology; multi-epoch rehoming stacks;
               fast-forward (LCA = one head) re-render after deep local folds.

All ids honour the Lamport discipline the two designs share as a model
assumption: a newly inserted id exceeds every id in the causal past of its
origin (pbt uses a global counter; the targeted scenarios pick ids by hand
accordingly).  Violating that discipline attacks the model, not the design.

If a divergence appears, the CHURN harness records the execution as an
explicit replayable trace and delta-debugs it: remove events (with dependency
closure so the shrunk trace stays honest), keep the removal iff the
divergence persists, and finally re-validate honesty of the minimum.

Usage:
  python3 equiv_stress.py targeted
  python3 equiv_stress.py grid  [--pdel 0.4]      (shardable by p_del)
  python3 equiv_stress.py churn [--shard 0..2]
  python3 equiv_stress.py all
"""
import sys
from random import Random
import litmus as L
import pbt
from delta_tree import DeltaTreeV3, PairedV3RGA


# ---------------------------------------------------------------- the checker
class Pair(PairedV3RGA):
    """PairedV3RGA + divergence capture (survives pbt's exception swallowing:
    pbt.try_merge records only the exception TYPE, so we stash the detail)."""
    last = None          # detail of the most recent divergence
    checks = 0           # total lockstep read-equality checks performed

    def _chk(self, s, w):
        Pair.checks += 1
        ra, rb = self.A.read(s[0]), self.B.read(s[1])
        if ra != rb:
            Pair.last = f"DIVERGE at {w}: v3={ra} rga={rb}"
            raise AssertionError(Pair.last)
        return s


def classify(bad):
    """pbt violation strings -> ('DIVERGE'|'SHARED', detail).
    'ERR@merge: AssertionError' is the paired check tripping inside
    pbt.try_merge (the detail is in Pair.last); anything else (FLIP/CONV/
    LIVE/DUP) is an anomaly BOTH designs exhibit identically -- a finding
    about the designs, not about the equivalence."""
    for b in bad:
        if 'AssertionError' in b:
            return ('DIVERGE', Pair.last or b)
    return ('SHARED', bad[0])


# =====================================================================
# Regime 1: hostile grid over pbt.run_execution
# =====================================================================
#   (n_replicas, n_rounds, max_ops, executions)
GRID_SHAPES = [(4, 8, 2, 1500), (6, 12, 2, 800), (8, 16, 2, 500),
               (10, 20, 2, 300), (4, 8, 4, 1000), (6, 12, 4, 600)]
GRID_PDEL = [0.4, 0.5, 0.6]
GRID_PMERGE = [0.4, 0.7]


def run_grid(pdel_filter=None):
    D = Pair()
    total = div = shared = 0
    findings = []
    cell_id = 0
    for p_del in GRID_PDEL:
        for p_merge in GRID_PMERGE:
            for (nr, rounds, mo, execs) in GRID_SHAPES:
                cell_id += 1
                if pdel_filter is not None and abs(p_del - pdel_filter) > 1e-9:
                    continue
                seed0 = 7000 + cell_id          # disjoint from the baseline seed0=0
                nbad = 0
                for e in range(execs):
                    rng = Random(seed0 * 100003 + e)
                    Pair.last = None
                    try:
                        bad, _sk = pbt.run_execution(D, rng, nr, rounds, mo,
                                                     p_del, p_merge)
                    except AssertionError as ex:   # divergence inside do_ops
                        bad = [f"ERR@op: AssertionError: {ex}"]
                    total += 1
                    if bad:
                        kind, detail = classify(bad)
                        nbad += 1
                        if kind == 'DIVERGE':
                            div += 1
                        else:
                            shared += 1
                        findings.append((kind, p_del, p_merge, nr, rounds, mo,
                                         seed0, e, detail))
                tag = f"p_del={p_del} p_merge={p_merge} r={nr} rounds={rounds} ops<={mo}"
                print(f"  cell {tag:55} {execs:4d} execs  "
                      f"{'CLEAN' if not nbad else str(nbad)+' BAD'}", flush=True)
    return total, div, shared, findings


# =====================================================================
# Regime 2: small-string churn under the version-DAG LCA discipline
# =====================================================================
def churn_execution(D, rng, n_replicas, n_rounds, cap, p_merge, p_del_under,
                    trace=None):
    """One churn execution.  Returns (divergence-or-None, stats).
    Version-DAG bookkeeping mirrors pbt.run_execution: every post-op and
    post-merge state is a recorded version; a merge of heads i,j is legal
    only if the version with event set == intersection of the heads' event
    sets exists (common past <= LCA); forced convergence at the end.
    Cap discipline: read longer than `cap` forces a delete; otherwise insert
    at a uniformly random anchor (including the front, a=0), with a small
    residual delete probability to keep dead-chain churn high."""
    D.begin()
    init = D.init()
    versions = {frozenset(): init}
    heads = [(frozenset(), init)] * n_replicas
    next_id = [1]
    stats = {'ops': 0, 'merges': 0, 'skipped': 0, 'conv_mismatch': 0}

    def record(ev, st):
        if ev in versions:
            # CONV cross-check (a single-design property; both components
            # were separately convergent, but it is nearly free to watch)
            if D.read(versions[ev]) != D.read(st):
                stats['conv_mismatch'] += 1
        else:
            versions[ev] = st

    def do_op(r):
        ev, st = heads[r]
        st = D.copy(st)
        ev = set(ev)
        doc = D.read(st)                       # lockstep check fires here
        if doc and (len(doc) > cap or rng.random() < p_del_under):
            it = ('del', rng.choice(doc))
            ev.add(('d', it[1]))
        else:
            a = rng.choice([0] + doc) if doc else 0
            x = next_id[0]; next_id[0] += 1
            it = ('ins', x, a)
            ev.add(x)
        if trace is not None:
            trace.append(('op', r, it))
        st = D.apply(st, it)                   # lockstep check fires here
        stats['ops'] += 1
        heads[r] = (frozenset(ev), st)
        record(heads[r][0], st)

    def try_merge(i, j):
        (ei, si), (ej, sj) = heads[i], heads[j]
        if ei == ej:
            return False
        lca = versions.get(ei & ej)
        if lca is None:
            stats['skipped'] += 1
            return False
        if trace is not None:
            trace.append(('merge', i, j))
        m = D.merge(D.copy(lca), D.copy(si), D.copy(sj))   # lockstep check
        stats['merges'] += 1
        heads[i] = (ei | ej, m)
        record(heads[i][0], m)
        return True

    try:
        for _ in range(n_rounds):
            for r in range(n_replicas):
                if rng.random() < p_merge:
                    # scan partners in random order until a LEGAL merge fires
                    # (single random pick skips ~95% under the LCA
                    # discipline); then a reverse sync half the time -- its
                    # LCA is the partner's own recorded head, always legal.
                    js = [j for j in range(n_replicas) if j != r]
                    rng.shuffle(js)
                    for j in js:
                        if try_merge(r, j):
                            if rng.random() < 0.5:
                                try_merge(j, r)
                            break
                else:
                    for _ in range(rng.randint(1, 2)):
                        do_op(r)
        for _ in range(6 * n_replicas):        # forced convergence
            pairs = [(i, j) for i in range(n_replicas)
                     for j in range(n_replicas)
                     if i != j and heads[i][0] != heads[j][0]]
            if not pairs:
                break
            rng.shuffle(pairs)
            if not any(try_merge(i, j) for (i, j) in pairs):
                break
    except AssertionError as ex:
        return str(ex), stats

    # depth probe: how deep did rehoming through dead ancestors actually go?
    v3 = heads[0][1][0]                        # (r, led) of the v3 component
    if not (isinstance(v3, tuple) and len(v3) == 2):
        return None, stats                     # non-v3 component: skip probe
    r_, led = v3
    if r_:
        depths = []
        for x in r_:
            d = 0
            p = led[x]
            while p != 0:
                if p not in r_:
                    d += 1                     # dead ancestor on the birth path
                p = led[p]
            depths.append(d)
        stats['max_dead_depth'] = max(depths)
    stats['ledger'] = len(led)
    stats['live'] = len(r_)
    return None, stats


CHURN_CONFIGS = [
    #  n_replicas, n_rounds, cap, p_merge, p_del_under, seeds
    (4, 300, 6, 0.6, 0.15, 200),
    (6, 300, 8, 0.6, 0.15, 200),
    (8, 200, 10, 0.7, 0.20, 150),
    (6, 400, 6, 0.7, 0.10, 150),
    (8, 300, 6, 0.5, 0.15, 150),
    (5, 500, 8, 0.75, 0.10, 120),
]


def run_churn(shard=None, nshards=1):
    D = Pair()
    total = div = 0
    findings = []
    agg = {'max_dead_depth': 0, 'ledger': 0, 'live': 0,
           'merges': 0, 'ops': 0, 'conv_mismatch': 0}
    for ci, (nr, rounds, cap, pm, pd, seeds) in enumerate(CHURN_CONFIGS):
        if shard is not None and ci % nshards != shard:
            continue
        nbad = 0
        for e in range(seeds):
            seed = 900000 + ci * 10000 + e
            bad, stats = churn_execution(D, Random(seed), nr, rounds, cap,
                                         pm, pd)
            total += 1
            for k in ('merges', 'ops', 'conv_mismatch'):
                agg[k] += stats.get(k, 0)
            for k in ('max_dead_depth', 'ledger', 'live'):
                agg[k] = max(agg[k], stats.get(k, 0))
            if bad:
                div += 1
                nbad += 1
                findings.append((nr, rounds, cap, pm, pd, seed, bad))
        print(f"  churn r={nr} rounds={rounds} cap={cap} p_merge={pm} "
              f"p_del={pd}: {seeds} execs  "
              f"{'CLEAN' if not nbad else str(nbad)+' DIVERGENT'}", flush=True)
    print(f"  [probe] max dead-ancestor depth on a live birth path: "
          f"{agg['max_dead_depth']}, max ledger {agg['ledger']} vs max live "
          f"{agg['live']}; total ops {agg['ops']}, merges {agg['merges']}, "
          f"CONV mismatches {agg['conv_mismatch']}", flush=True)
    return total, div, findings


# ------------------------------------------------- trace replay + shrinking
def replay(D, events, n_replicas):
    """Deterministically replay an explicit trace.  Merges whose LCA is no
    longer recorded (because shrinking removed events) are skipped -- the
    result is still an honest execution.  Returns divergence-or-None."""
    D.begin()
    init = D.init()
    versions = {frozenset(): init}
    heads = [(frozenset(), init)] * n_replicas
    try:
        for e in events:
            if e[0] == 'op':
                _, r, it = e
                ev, st = heads[r]
                st = D.apply(D.copy(st), it)
                ev = set(ev)
                ev.add(it[1] if it[0] == 'ins' else ('d', it[1]))
                heads[r] = (frozenset(ev), st)
                versions.setdefault(heads[r][0], st)
            else:
                _, i, j = e
                (ei, si), (ej, sj) = heads[i], heads[j]
                if ei == ej:
                    continue
                lca = versions.get(ei & ej)
                if lca is None:
                    continue
                m = D.merge(D.copy(lca), D.copy(si), D.copy(sj))
                heads[i] = (ei | ej, m)
                versions.setdefault(heads[i][0], m)
    except AssertionError as ex:
        return str(ex)
    return None


def closure_remove(events, idx):
    """Remove events[idx] plus everything depending on it, so the shrunk
    trace stays honest: dropping ins x also drops del x and (recursively)
    every ins anchored at x."""
    dead = set()
    e = events[idx]
    if e[0] == 'op' and e[2][0] == 'ins':
        dead.add(e[2][1])
    out = []
    for i, ev in enumerate(events):
        if i == idx:
            continue
        if ev[0] == 'op':
            it = ev[2]
            if it[0] == 'ins' and it[2] in dead:
                dead.add(it[1])
                continue
            if it[0] == 'del' and it[1] in dead:
                continue
        out.append(ev)
    return out


def shrink(D, events, n_replicas):
    """Greedy delta-debug: keep removing events while the divergence
    persists.  Also tries dropping whole replicas."""
    assert replay(D, events, n_replicas) is not None
    changed = True
    while changed:
        changed = False
        # whole replicas first
        for r in range(n_replicas):
            cand = [e for e in events if not (e[0] == 'op' and e[1] == r)
                    and not (e[0] == 'merge' and r in (e[1], e[2]))]
            if len(cand) < len(events) and replay(D, cand, n_replicas):
                events = cand
                changed = True
        i = 0
        while i < len(events):
            cand = closure_remove(events, i)
            if replay(D, cand, n_replicas):
                events = cand
                changed = True
            else:
                i += 1
    return events


def validate_honest(D, events, n_replicas):
    """Check the (minimized) trace is honest: every del target is in the
    deleting replica's read; every ins anchor is 0 or in the read; ids obey
    the Lamport discipline (fresh id > every id in the origin's state)."""
    D.begin()
    init = D.init()
    versions = {frozenset(): init}
    heads = [(frozenset(), init)] * n_replicas
    seen_ids = [set() for _ in range(n_replicas)]
    ok = True
    for e in events:
        if e[0] == 'op':
            _, r, it = e
            ev, st = heads[r]
            try:
                doc = D.read(st)
            except AssertionError:
                return ok
            if it[0] == 'del' and it[1] not in doc:
                ok = False
            if it[0] == 'ins' and it[2] != 0 and it[2] not in doc:
                ok = False
            if it[0] == 'ins' and seen_ids[r] and it[1] <= max(seen_ids[r]):
                ok = False
            try:
                st = D.apply(D.copy(st), it)
            except AssertionError:
                return ok
            ev = set(ev)
            ev.add(it[1] if it[0] == 'ins' else ('d', it[1]))
            if it[0] == 'ins':
                seen_ids[r].add(it[1])
            heads[r] = (frozenset(ev), st)
            versions.setdefault(heads[r][0], st)
        else:
            _, i, j = e
            (ei, si), (ej, sj) = heads[i], heads[j]
            if ei == ej:
                continue
            lca = versions.get(ei & ej)
            if lca is None:
                continue
            try:
                m = D.merge(D.copy(lca), D.copy(si), D.copy(sj))
            except AssertionError:
                return ok
            heads[i] = (ei | ej, m)
            seen_ids[i] |= seen_ids[j]
            versions.setdefault(heads[i][0], m)
    return ok


def minimize_finding(config, seed):
    """Re-run a divergent churn execution with trace recording, then shrink."""
    nr, rounds, cap, pm, pd = config
    D = Pair()
    trace = []
    bad, _ = churn_execution(D, Random(seed), nr, rounds, cap, pm, pd,
                             trace=trace)
    if bad is None:
        return None
    small = shrink(D, trace, nr)
    return {'divergence': replay(D, small, nr), 'events': small,
            'honest': validate_honest(D, small, nr)}


# =====================================================================
# Regime 3: targeted adversarial scenarios
# =====================================================================
class Hist:
    """Named-version history over the paired design; every apply/merge/read
    goes through the lockstep checker."""
    def __init__(self, D):
        self.D = D
        D.begin()
        self.s = {'init': D.init()}

    def ops(self, name, base, script):
        st = self.D.copy(self.s[base])
        for it in script:
            st = self.D.apply(st, it)
        self.s[name] = st

    def merge(self, name, lca, a, b):
        D = self.D
        self.s[name] = D.merge(D.copy(self.s[lca]), D.copy(self.s[a]),
                               D.copy(self.s[b]))

    def read(self, name):
        return self.D.read(self.s[name])


I, DL = (lambda x, a: ('ins', x, a)), (lambda d: ('del', d))


def targeted():
    """Each scenario returns None (clean) or a divergence message.  Ids are
    Lamport-honest: every fresh id exceeds all ids in its origin's state."""
    out = []

    def run(name, fn):
        try:
            fn(Hist(Pair()))
            out.append((name, None))
        except AssertionError as ex:
            out.append((name, str(ex)))

    # T1 -- deep chain, ENTIRE interior+tip deleted on A, B inserts under the
    # dead interior at several depths; merge both orders; then keep editing.
    def t1(h):
        h.ops('lca', 'init', [I(1, 0), I(2, 1), I(3, 2), I(4, 3), I(5, 4)])
        h.ops('A', 'lca', [DL(2), DL(3), DL(4), DL(5)])
        h.ops('B', 'lca', [I(10, 5), I(11, 4), I(12, 3), I(13, 10)])
        h.merge('M', 'lca', 'A', 'B')
        h.merge('M2', 'lca', 'B', 'A')
        h.read('M'); h.read('M2')
        h.ops('P', 'M', [DL(1), I(20, 13), DL(11), I(21, 20)])
        h.read('P')
    run('T1 dead interior + deep inserts', t1)

    # T1b -- chain FULLY deleted (including the root child): every B insert
    # rehomes all the way to the document root through a 5-dead stack.
    def t1b(h):
        h.ops('lca', 'init', [I(1, 0), I(2, 1), I(3, 2), I(4, 3), I(5, 4)])
        h.ops('A', 'lca', [DL(5), DL(4), DL(3), DL(2), DL(1)])
        h.ops('B', 'lca', [I(10, 5), I(11, 10), I(12, 2)])
        h.merge('M', 'lca', 'A', 'B')
        h.merge('M2', 'lca', 'B', 'A')
        h.read('M'); h.read('M2')
        h.ops('P', 'M', [I(20, 0), I(21, 11), DL(10)])
        h.read('P')
    run('T1b chain fully deleted, root rehoming', t1b)

    # T2 -- concurrent same-anchor bursts with interleaved Lamport ids, then
    # one branch deletes the anchor; merge both orders; then delete survivors.
    def t2(h):
        h.ops('lca', 'init', [I(1, 0), I(2, 1)])
        h.ops('A', 'lca', [I(10, 2), I(12, 2), I(14, 2), DL(2)])
        h.ops('B', 'lca', [I(11, 2), I(13, 2), I(15, 2)])
        h.merge('M', 'lca', 'A', 'B')
        h.merge('M2', 'lca', 'B', 'A')
        h.read('M'); h.read('M2')
        h.ops('P', 'M', [DL(14), DL(15), I(20, 13)])
        h.read('P')
    run('T2 same-anchor burst + delete-the-anchor', t2)

    # T2b -- BOTH branches delete the anchor after bursting under it.
    def t2b(h):
        h.ops('lca', 'init', [I(1, 0), I(2, 1)])
        h.ops('A', 'lca', [I(10, 2), I(12, 10), DL(2)])
        h.ops('B', 'lca', [I(11, 2), I(13, 11), DL(2)])
        h.merge('M', 'lca', 'A', 'B')
        h.merge('M2', 'lca', 'B', 'A')
        h.read('M'); h.read('M2')
    run('T2b burst + double delete-the-anchor', t2b)

    # T3 -- interleaved delete/re-insert cycles at the same position across
    # THREE branches, merged in all three topologies (litmus L22 pattern).
    def t3(h):
        h.ops('lca', 'init', [I(1, 0), I(2, 1)])
        h.ops('B1', 'lca', [DL(2), I(10, 1), DL(10), I(13, 1)])
        h.ops('B2', 'lca', [DL(2), I(11, 1), DL(11), I(14, 1)])
        h.ops('B3', 'lca', [DL(2), I(12, 1), DL(12), I(15, 1)])
        for tag, (x, y, z) in (('a', ('B1', 'B2', 'B3')),
                               ('b', ('B1', 'B3', 'B2')),
                               ('c', ('B2', 'B3', 'B1'))):
            h.merge('M1' + tag, 'lca', x, y)
            h.merge('M2' + tag, 'lca', 'M1' + tag, z)
            h.read('M2' + tag)
    run('T3 del/re-ins cycles x3 branches, all topologies', t3)

    # T4 -- multi-epoch rehoming stack: epoch-1 merge rehomes 10 under 1
    # through dead 2,3; epoch-2 kills 1 and 10 while a fork extends under 10;
    # the epoch-2 merge folds through dead ids of BOTH epochs.
    def t4(h):
        h.ops('lca', 'init', [I(1, 0), I(2, 1), I(3, 2)])
        h.ops('A', 'lca', [I(10, 3)])
        h.ops('B', 'lca', [DL(2), DL(3)])
        h.merge('M1', 'lca', 'A', 'B')
        h.ops('C', 'M1', [I(20, 10), I(21, 20)])
        h.ops('E', 'M1', [DL(1), DL(10)])
        h.merge('M2', 'M1', 'C', 'E')
        h.merge('M2r', 'M1', 'E', 'C')
        h.read('M2'); h.read('M2r')
        h.ops('P', 'M2', [I(30, 21), DL(20)])
        h.read('P')
    run('T4 multi-epoch dead-ancestor stack', t4)

    # T5 -- L20-flavoured: concurrent heads, children typed under each, one
    # branch deletes the shared anchor; merge; then delete both heads so the
    # children's order must inherit the heads' verdict -- in lockstep.
    def t5(h):
        h.ops('lca', 'init', [I(1, 0)])
        h.ops('A', 'lca', [I(10, 1), I(40, 10), DL(1)])
        h.ops('B', 'lca', [I(20, 1), I(30, 20)])
        h.merge('M', 'lca', 'A', 'B')
        h.merge('M2', 'lca', 'B', 'A')
        h.read('M'); h.read('M2')
        h.ops('P', 'M', [DL(10), DL(20), I(50, 30)])
        h.read('P')
    run('T5 tie inheritance under a dead anchor', t5)

    # T6 -- cross-branch double kill of a nested chain: A kills the whole
    # chain and restarts; B extends the chain, kills part of it (its own
    # extension included), keeps typing.  Dead ids of mixed provenance.
    def t6(h):
        h.ops('lca', 'init', [I(1, 0), I(2, 1), I(3, 2), I(4, 3), I(5, 4),
                              I(6, 5)])
        h.ops('A', 'lca', [DL(2), DL(3), DL(4), DL(5), DL(6), I(30, 1)])
        h.ops('B', 'lca', [I(21, 6), DL(4), DL(5), I(22, 21), DL(6), I(23, 22)])
        h.merge('M', 'lca', 'A', 'B')
        h.merge('M2', 'lca', 'B', 'A')
        h.read('M'); h.read('M2')
        h.ops('P', 'M', [DL(21), DL(22), I(40, 23)])
        h.read('P')
    run('T6 cross-branch chain kill', t6)

    # T7 -- stale frame (L21 pattern) + deletes: C forks from A pre-merge,
    # edits under A's head and deletes; the second merge's LCA is the A state.
    def t7(h):
        h.ops('lca', 'init', [I(1, 0)])
        h.ops('A', 'lca', [I(25, 1), I(40, 25)])
        h.ops('B', 'lca', [I(20, 1), I(30, 20)])
        h.ops('C', 'A', [I(50, 25), DL(40)])
        h.merge('M1', 'lca', 'A', 'B')
        h.merge('M2', 'A', 'M1', 'C')
        h.merge('M2r', 'A', 'C', 'M1')
        h.read('M2'); h.read('M2r')
        h.ops('P', 'M2', [DL(25), I(60, 50)])
        h.read('P')
    run('T7 stale fork + delete (L21+)', t7)

    # T8 -- front-churn ping-pong: backward runs at the front with
    # interleaved ids, partial deletes, both merge orders (L19's shape but
    # with deletes; the pair must fail/pass IDENTICALLY).
    def t8(h):
        h.ops('lca', 'init', [I(1, 0)])
        h.ops('A', 'lca', [I(10, 0), I(12, 0), DL(10)])
        h.ops('B', 'lca', [I(11, 0), I(13, 0), DL(11)])
        h.merge('M', 'lca', 'A', 'B')
        h.merge('M2', 'lca', 'B', 'A')
        h.read('M'); h.read('M2')
        h.ops('P', 'M', [DL(12), DL(13), I(20, 0), DL(1)])
        h.read('P')
    run('T8 front churn ping-pong', t8)

    # T9 -- fast-forward re-render: build gnarly LOCAL fold geometry
    # (interleaved ins/del producing nested isometric folds), then merge with
    # LCA = an old self and with LCA = the CURRENT head (subset case): the
    # merge re-renders canonical geometry, and the read must be unchanged.
    def t9(h):
        h.ops('v0', 'init', [I(1, 0), I(2, 1), I(3, 2)])
        h.ops('v1', 'v0', [I(4, 2), DL(2), I(5, 4), DL(4), I(6, 3), DL(3),
                           I(7, 5), DL(5), I(8, 1), DL(1)])
        h.ops('other', 'v0', [I(20, 3)])
        h.merge('FF', 'v0', 'v1', 'other')       # deep-fold state vs tiny fork
        h.read('FF')
        h.ops('v2', 'v1', [I(30, 7)])
        h.merge('FF2', 'v1', 'v1', 'v2')         # LCA = one of the heads
        h.read('FF2')
    run('T9 fast-forward canonical re-render after deep folds', t9)

    # T10 -- idle-branch identity through the pair (merge with an untouched
    # branch must not disturb the read), on a fold-heavy state.
    def t10(h):
        h.ops('lca', 'init', [I(1, 0), I(2, 1), I(3, 2)])
        h.ops('A', 'lca', [I(10, 2), DL(2), DL(3), I(11, 10), DL(10)])
        h.merge('M', 'lca', 'A', 'lca')
        h.merge('Mr', 'lca', 'lca', 'A')
        h.read('M'); h.read('Mr')
    run('T10 idle-branch identity on fold-heavy state', t10)

    return out


# =====================================================================
def main():
    args = sys.argv[1:]
    mode = args[0] if args else 'all'
    opts = dict(zip(args[1::2], args[2::2]))
    grand_total = grand_div = 0

    if mode in ('targeted', 'all'):
        print("== targeted adversarial scenarios ==", flush=True)
        res = targeted()
        for name, bad in res:
            print(f"  {name:50} {'CLEAN' if bad is None else 'DIVERGE: ' + bad}",
                  flush=True)
        grand_total += len(res)
        grand_div += sum(1 for _, b in res if b)

    if mode in ('grid', 'all'):
        pd = float(opts['--pdel']) if '--pdel' in opts else None
        print("== hostile grid (pbt.run_execution) ==", flush=True)
        t, d, s, f = run_grid(pd)
        print(f"  grid total: {t} executions, {d} divergences, "
              f"{s} shared-anomalies", flush=True)
        for k in f[:5]:
            print(f"    {k}", flush=True)
        grand_total += t
        grand_div += d

    if mode in ('churn', 'all'):
        shard = int(opts['--shard']) if '--shard' in opts else None
        nsh = int(opts['--nshards']) if '--nshards' in opts else 3
        print("== small-string churn ==", flush=True)
        t, d, f = run_churn(shard, nsh)
        print(f"  churn total: {t} executions, {d} divergences", flush=True)
        for (nr, rounds, cap, pm, pdl, seed, bad) in f[:3]:
            print(f"    seed {seed}: {bad}", flush=True)
            mini = minimize_finding((nr, rounds, cap, pm, pdl), seed)
            if mini:
                print(f"    minimized ({len(mini['events'])} events, "
                      f"honest={mini['honest']}): {mini['divergence']}",
                      flush=True)
                for e in mini['events']:
                    print(f"      {e}", flush=True)
        grand_total += t
        grand_div += d

    print(f"== TOTAL: {grand_total} executions/scenarios, {grand_div} "
          f"divergences; {Pair.checks} lockstep read-equality checks ==",
          flush=True)


if __name__ == '__main__':
    main()
