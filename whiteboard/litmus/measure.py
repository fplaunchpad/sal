#!/usr/bin/env python3
"""
measure.py -- machine tests for delta-tree v3's ledger claims (#70, #71).

New file; modifies nothing else. All runs are fixed-seed.

A. LEDGER PRUNING SOUNDNESS (#70)
   A1 'naive'  : after EVERY apply and merge, drop led entries whose id is not
                 on any live node's birth chain (live-reachability closure).
                 Lockstep vs unpruned v3 -- r-dict equality + led-value
                 agreement asserted at every step -- under pbt's DAG harness
                 (three parameter regimes), under equiv_stress's churn harness
                 (A1b: opportunistic LCA merges, tens of thousands of legal
                 merges), and under the long custom runs.
   A2 'stab'   : global causal-stability oracle -- prune dead z only when
                 ('d',z) is in EVERY replica's current version.  Gate applied
                 alone ('stab') and conjoined with reachability ('sr').
   control     : a deliberately broken pruner ('drop every dead entry
                 immediately') to prove the lockstep harness actually bites.

B. STATE SIZE (#70): v3 + pruned variants vs the tombstoned RGA in lockstep on
   IDENTICAL histories; churn regime (live string pinned to ~6-10 while ops
   accumulate) and a growth regime; per-round size table.

C. DENOMINATOR GROWTH (#71): max/mean Fraction-denominator bit-length over all
   fractions in r, in (i) purely sequential, (ii) merge-heavy, (iii) churn
   regimes; pre/post-merge bits; bits vs ops-since-last-merge fit.

Run:  python3 measure.py [--quick]
"""
import os
import sys
from collections import defaultdict
from random import Random

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.setrecursionlimit(300000)

import litmus as L                    # noqa: E402
import pbt                            # noqa: E402
from delta_tree import DeltaTreeV3    # noqa: E402

V3 = DeltaTreeV3()
RGA = next(D for D in L.DESIGNS if D.name == 'tombstoned')


# ============================================================ pruning gates
def reachable_ids(r, led):
    """All ids on some live node's birth chain (live nodes included)."""
    keep = set()
    for x in r:
        while x != 0 and x not in keep:
            keep.add(x)
            x = led[x]            # KeyError here == chain closure broken
    return keep


def prune_naive(s):
    r, led = s
    keep = reachable_ids(r, led)
    return (r, {k: p for k, p in led.items() if k in keep})


def prune_all_dead(s):            # deliberately broken: sensitivity control
    r, led = s
    return (r, {k: p for k, p in led.items() if k in r})


class NaivePrunedV3(DeltaTreeV3):
    name = 'v3-naive-pruned'
    def apply(self, s, it):
        return prune_naive(super().apply(s, it))
    def merge(self, Ls, As, Bs):
        return prune_naive(super().merge(Ls, As, Bs))


class DropDeadV3(DeltaTreeV3):
    name = 'v3-drop-dead'
    def apply(self, s, it):
        return prune_all_dead(super().apply(s, it))
    def merge(self, Ls, As, Bs):
        return prune_all_dead(super().merge(Ls, As, Bs))


# ============================================ A1: lockstep pair for pbt DAG
class PairedVsV3(L.Design):
    """Run a pruned variant and unpruned v3 in lockstep; assert (1) identical
    r-dicts (implies identical reads: read depends only on r) and (2) every
    pruned led entry present in the unpruned led with the same value."""
    def __init__(self, P):
        self.P, self.U = P, DeltaTreeV3()
        self.name = P.name + '-vs-v3'
    def init(self): return (self.P.init(), self.U.init())
    def copy(self, s): return (self.P.copy(s[0]), self.U.copy(s[1]))
    def fp(self, s): return (self.P.fp(s[0]), self.U.fp(s[1]))
    def _chk(self, s, w):
        (rp, lp), (ru, lu) = s
        assert rp == ru, f"R-DIVERGE at {w}: pruned={rp} full={ru}"
        for k, v in lp.items():
            assert lu.get(k) == v, f"LED-DIVERGE at {w}: {k} -> {v} vs {lu.get(k)}"
        return s
    def apply(self, s, it):
        return self._chk((self.P.apply(s[0], it), self.U.apply(s[1], it)), it)
    def read(self, s):
        self._chk(s, "read")
        return self.P.read(s[0])
    def merge(self, Ls, As, Bs):
        return self._chk((self.P.merge(Ls[0], As[0], Bs[0]),
                          self.U.merge(Ls[1], As[1], Bs[1])), "merge")


def safe_sweep(D, executions, seed0=0, n_replicas=4, n_rounds=8, max_ops=2,
               p_del=0.3, p_merge=0.4):
    """pbt.sweep with per-execution exception capture (assertions in apply
    would otherwise kill the whole sweep)."""
    fails, first, skipped = 0, None, 0
    for e in range(executions):
        rng = Random(seed0 * 100003 + e)
        try:
            bad, sk = pbt.run_execution(D, rng, n_replicas, n_rounds, max_ops,
                                        p_del, p_merge)
            skipped += sk
            if bad:
                fails += 1
                if first is None: first = (e, bad[0])
        except Exception as ex:
            fails += 1
            if first is None: first = (e, f"{type(ex).__name__}: {ex}")
    return fails, first, skipped


# ============================== A1b: equiv_stress churn regime on the pair
def a1b_churn(quick):
    """Run the paired naive-pruned-vs-unpruned design through equiv_stress's
    churn harness (the ~332k-legal-merge regime from task #69: opportunistic
    partner-scan merges + reverse fast-forward syncs under the version-DAG LCA
    discipline, duplicate concurrent deletes allowed).  The pair's assertions
    fire inside churn_execution; non-assertion crashes (e.g. a KeyError from
    an over-pruned ledger) are caught here."""
    import equiv_stress as ES
    P = PairedVsV3(NaivePrunedV3())
    #        n_replicas, rounds, cap, p_merge, p_del_under, seeds
    cfgs = [(4, 300, 6, 0.6, 0.15, 30 if quick else 100),
            (6, 300, 8, 0.6, 0.15, 20 if quick else 70),
            (5, 500, 8, 0.75, 0.10, 10 if quick else 40)]
    tot = dict(execs=0, merges=0, ops=0, bad=0)
    first = None
    for ci, (nr, rounds, cap, pm, pd, seeds) in enumerate(cfgs):
        nbad = 0
        for e in range(seeds):
            seed = 3400000 + ci * 10000 + e
            try:
                bad, stats = ES.churn_execution(P, Random(seed), nr, rounds,
                                                cap, pm, pd)
            except Exception as ex:
                bad, stats = f"{type(ex).__name__}: {ex}", {}
            tot['execs'] += 1
            tot['merges'] += stats.get('merges', 0)
            tot['ops'] += stats.get('ops', 0)
            if bad:
                nbad += 1
                tot['bad'] += 1
                if first is None:
                    first = (seed, bad)
        print(f"    churn r={nr} rounds={rounds} cap={cap} p_merge={pm} "
              f"p_del={pd}: {seeds} execs  "
              f"{'CLEAN' if not nbad else str(nbad) + ' BAD'}", flush=True)
    return tot, first


# ============================== A2: multi-seed sweep over the oracle variants
def stability_seed_sweep(n_seeds, rounds):
    """run_lockstep across seeds; tally per-variant lockstep failures.
    Expected: 'naive' and 'sr' never fail; 'stab' (stability WITHOUT the
    reachability conjunct) fails whenever a stably-deleted id is still on a
    live node's birth chain at the next merge."""
    tallies = {'naive': 0, 'sr': 0, 'stab': 0, 'rga': 0}
    first = {}
    merges = 0
    for sd in range(n_seeds):
        res = run_lockstep(seed=1000 + sd, n_replicas=4, n_rounds=rounds,
                           policy=policy_churn(6, 10), p_merge=0.2,
                           variants=('naive', 'sr', 'stab'), with_rga=True,
                           sync_every=10)
        merges += res['merges']
        for (tag, n, msg) in res['failures']:
            tallies[n] += 1
            first.setdefault(n, (1000 + sd, tag, msg))
    return tallies, first, merges


# ================================= A2: hand countermodel, stability-only gate
def countermodel_stab_only():
    """Minimal script breaking the stability-ONLY gate.
       ins(1@root); ins(2@1); del(1); full sync (so ('d',1) is in every
       replica's version -> globally stable); GC drops led[1] from every
       stored state; one more op anywhere; merge."""
    D = DeltaTreeV3()
    s = D.init()
    for it in (('ins', 1, 0), ('ins', 2, 1), ('del', 1)):
        s = D.apply(s, it)
    # both replicas + version store now hold s; delete of 1 is globally stable
    s[1].pop(1)                              # stability-only GC: drop led[1]
    A, B = D.copy(s), D.copy(s)
    A = D.apply(A, ('ins', 3, 2))            # any post-GC activity
    try:
        D.merge(D.copy(s), A, B)             # LCA = the synced, GC'd state
        return None
    except KeyError as e:
        return f"KeyError({e}): survivor 2 is live but its birth chain passes through dead 1"


def countermodel_stab_only_control():
    """Same script with the reachability conjunct: led[1] retained (2's chain
    passes through 1) -> merge succeeds."""
    D = DeltaTreeV3()
    s = D.init()
    for it in (('ins', 1, 0), ('ins', 2, 1), ('del', 1)):
        s = D.apply(s, it)
    keep = reachable_ids(s[0], s[1])
    assert 1 in keep, "reachability gate should retain 1"
    A, B = D.copy(s), D.copy(s)
    A = D.apply(A, ('ins', 3, 2))
    m = D.merge(D.copy(s), A, B)
    return D.read(m)


# ===================================================== custom lockstep harness
def read_fast(rst):
    """Iterative, O(n log n) re-implementation of DeltaTreeV3.read (children
    by descending (loF, id)). Verified against V3.read at every sample."""
    kids = defaultdict(list)
    for x, (p, lo, _hi) in rst.items():
        kids[p].append((lo, x))
    for p in kids:
        kids[p].sort(reverse=True)
    out, stack = [], [x for (_l, x) in reversed(kids.get(0, []))]
    while stack:
        u = stack.pop()
        out.append(u)
        stack.extend(x for (_l, x) in reversed(kids.get(u, [])))
    return out


def v3bits(rst):
    bl = [f.denominator.bit_length() for (_p, lo, hi) in rst.values()
          for f in (lo, hi)]
    if not bl:
        return 0, 0.0
    return max(bl), sum(bl) / len(bl)


def policy_std(p_del):
    """dels = delete targets not yet deleted anywhere (globally-unique deletes
    keep hub-sync merges LCA-legal; duplicate concurrent deletes -- which make
    head intersections match no recorded version -- stay covered by the
    unrestricted pbt sweeps in section A1)."""
    def pol(doc, dels, rng, glive):
        if dels and rng.random() < p_del:
            return ('del', rng.choice(dels))
        return ('ins', rng.choice([0] + doc) if doc else 0)
    return pol


def policy_churn(lo=6, hi=10):
    """Keep the live string pinned to ~[lo,hi] while ops accumulate.
    Gauge = glive, the EVENTUAL global live count (total ins - total dels;
    exact because deletes are globally unique and always land).  A local gauge
    (len(doc) or len(dels)) cannot pin the merged string: with the doc gauge
    concurrent deletes collapse it (observed live=1 after 300 inserts), with
    the dels gauge concurrent inserts union it up (observed live~23 at band
    6-10).  A replica can still only delete what it SEES (dels), so the churn
    stays honest."""
    def pol(doc, dels, rng, glive):
        if dels and glive >= hi:
            return ('del', rng.choice(dels))
        if glive <= lo or not dels:
            return ('ins', rng.choice([0] + doc) if doc else 0)
        if rng.random() < 0.5:
            return ('del', rng.choice(dels))
        return ('ins', rng.choice([0] + doc))
    return pol


def run_lockstep(seed, n_replicas, n_rounds, policy, p_merge, max_ops=2,
                 variants=('naive', 'sr'), with_rga=True, sample_at=(),
                 oracle=True, sync_every=None):
    """pbt.run_execution's LCA discipline, generalized to a BUNDLE of designs
    run in lockstep on one schedule (ops drawn from the v3 read):
      'v3'    unpruned DeltaTreeV3        (reference)
      'naive' v3 + reachability pruning after every apply/merge
      'sr'    v3 + oracle pruning gated on stability AND reachability
      'stab'  v3 + oracle pruning gated on stability alone
      'rga'   tombstoned RGA (litmus baseline) for size comparison
    The stability oracle fires after every round on head states IN PLACE
    (which also GCs the aliased just-recorded version snapshot -- GC rewrites
    the store).  A variant that diverges or crashes is recorded and dropped;
    the rest continue."""
    rng = Random(seed)
    names = ['v3'] + list(variants) + (['rga'] if with_rga else [])
    def des(n): return RGA if n == 'rga' else V3
    alive = set(names)
    failures = []

    def kill(n, tag, msg):
        if n in alive:
            alive.discard(n)
            failures.append((tag, n, msg))

    b0 = {n: des(n).init() for n in names}
    versions = [(frozenset(), b0)]
    heads = [(frozenset(), b0)] * n_replicas
    next_id = [1]
    deleted_ever = set()
    ins_total = [0]; del_total = [0]
    osm = [0] * n_replicas               # local ops since this replica's last merge
    merge_bits = []                      # (pre_max_bits, post_max_bits, max_sibling_width) per merge
    law_viol = []                        # merges violating post_bits == width+2
    bit_points = []                      # (round, replica, osm, |events|, max_bits, mean_bits)
    samples = []

    def check_bundle(bd, tag):
        if 'v3' not in alive:
            return
        base_r, base_led = bd['v3']
        doc = read_fast(base_r)
        for n in [x for x in alive if x not in ('v3',)]:
            if n not in bd:
                continue
            if n == 'rga':
                try:
                    rd = RGA.read(bd['rga'])
                except Exception as ex:
                    kill(n, tag, f"read {type(ex).__name__}: {ex}"); continue
                if rd != doc:
                    kill(n, tag, f"read diverge: rga={rd} v3={doc}")
            else:
                rn, ln = bd[n]
                if rn != base_r:
                    kill(n, tag, f"r diverge: {rn} vs {base_r}"); continue
                for k, v in ln.items():
                    if base_led.get(k) != v:
                        kill(n, tag, f"led value diverge at {k}"); break

    def do_ops(rr, k, rnd):
        ev, bd = heads[rr]
        bd = {n: des(n).copy(bd[n]) for n in bd if n in alive}
        ev = set(ev)
        for _ in range(k):
            if 'v3' not in alive:
                return
            doc = read_fast(bd['v3'][0])
            dels = [x for x in doc if x not in deleted_ever]
            kind = policy(doc, dels, rng, ins_total[0] - del_total[0])
            if kind[0] == 'del':
                it = ('del', kind[1]); ev.add(('d', kind[1]))
                deleted_ever.add(kind[1]); del_total[0] += 1
            else:
                x = next_id[0]; next_id[0] += 1
                it = ('ins', x, kind[1]); ev.add(x); ins_total[0] += 1
            for n in list(alive):
                if n not in bd:
                    continue
                try:
                    s = des(n).apply(bd[n], it)
                    if n == 'naive':
                        s = prune_naive(s)
                    bd[n] = s
                except Exception as ex:
                    kill(n, f"op{it}@r{rr}rnd{rnd}", f"apply {type(ex).__name__}: {ex}")
            check_bundle(bd, f"op{it}@r{rr}rnd{rnd}")
            osm[rr] += 1
        heads[rr] = (frozenset(ev), bd)
        versions.append(heads[rr])

    def try_merge(i, j, rnd):
        if 'v3' not in alive:
            return False
        (ei, bi), (ej, bj) = heads[i], heads[j]
        if ei == ej:
            return False
        inter = ei & ej
        lca = next(((ev, bb) for (ev, bb) in versions if ev == inter), None)
        if lca is None:
            return False
        pre = max(v3bits(bi['v3'][0])[0], v3bits(bj['v3'][0])[0])
        out = {}
        for n in list(alive):
            if n not in bi or n not in bj or n not in lca[1]:
                continue
            try:
                m = des(n).merge(des(n).copy(lca[1][n]),
                                 des(n).copy(bi[n]), des(n).copy(bj[n]))
                if n == 'naive':
                    m = prune_naive(m)
                out[n] = m
            except Exception as ex:
                kill(n, f"merge@r{i}+r{j}rnd{rnd}", f"merge {type(ex).__name__}: {ex}")
        bd = {n: out[n] for n in out if n in alive}
        check_bundle(bd, f"merge@r{i}+r{j}rnd{rnd}")
        if 'v3' in bd:
            rm = bd['v3'][0]
            cnt = {}
            for (pp, _lo, _hi) in rm.values():
                cnt[pp] = cnt.get(pp, 0) + 1
            width = max(cnt.values(), default=0)
            post = v3bits(rm)[0]
            merge_bits.append((pre, post, width))
            # exact re-render law: post-merge max denominator bits ==
            # (max sibling-set size) + 2 (render carve: newest child's loF at
            # depth-in-run i has denominator 2^(i+2))
            if post != (width + 2 if width else 0):
                law_viol.append((f"r{i}+r{j}rnd{rnd}", width, post))
        heads[i] = (ei | ej, bd)
        versions.append(heads[i])
        osm[i] = 0
        return True

    def fire_oracle(rnd):
        stable = None
        for (ev, _bd) in heads:
            ds = {e[1] for e in ev if not isinstance(e, int)}
            stable = ds if stable is None else (stable & ds)
        if not stable:
            return
        done = set()
        for (_ev, bd) in heads:
            if id(bd) in done:
                continue
            done.add(id(bd))
            for n in ('sr', 'stab'):
                if n not in bd or n not in alive:
                    continue
                r, led = bd[n]
                if n == 'sr':
                    try:
                        keep = reachable_ids(r, led)
                    except KeyError as ex:
                        kill(n, f"oracle@rnd{rnd}", f"reach KeyError({ex})")
                        continue
                    for z in stable:
                        if z in led and z not in r and z not in keep:
                            del led[z]
                else:
                    for z in stable:
                        if z in led and z not in r:
                            del led[z]

    def snap(tag):
        k = max(range(n_replicas), key=lambda r: len(heads[r][0]))
        ev, bd = heads[k]
        if 'v3' not in bd:
            return dict(tag=tag)
        r, led = bd['v3']
        assert read_fast(r) == V3.read(bd['v3']), "read_fast fidelity"
        row = dict(tag=tag, events=len(ev), live=len(r), led=len(led))
        try:
            row['led_reach'] = len(reachable_ids(r, led))
        except KeyError:
            row['led_reach'] = -1
        for n, key in (('naive', 'led_naive'), ('sr', 'led_sr'), ('stab', 'led_stab')):
            if n in bd and n in alive:
                row[key] = len(bd[n][1])
        if 'rga' in bd and 'rga' in alive:
            row['rga_total'] = len(bd['rga'])
            row['rga_live'] = sum(1 for (_a, al) in bd['rga'].values() if al)
        mb, mnb = v3bits(r)
        row['bits_max'] = mb; row['bits_mean'] = round(mnb, 1)
        return row

    for rnd in range(1, n_rounds + 1):
        if 'v3' not in alive:
            break
        for rr in range(n_replicas):
            if rng.random() < p_merge:
                js = [j for j in range(n_replicas) if j != rr]
                rng.shuffle(js)
                for j in js:                 # retry partners: the strict LCA
                    if try_merge(rr, j, rnd):    # discipline rejects many pairs
                        break
            else:
                do_ops(rr, rng.randint(1, max_ops), rnd)
        if sync_every and rnd % sync_every == 0:
            # hub-sync epoch (always LCA-legal absent criss-cross): r0 absorbs
            # everyone, then everyone fast-forwards from r0 (LCA = own head).
            for j in range(1, n_replicas):
                try_merge(0, j, f"sync{rnd}")
            for j in range(1, n_replicas):
                try_merge(j, 0, f"sync{rnd}")
        if oracle:
            fire_oracle(rnd)
        for rr in range(n_replicas):
            bd = heads[rr][1]
            if 'v3' in bd:
                mb, mnb = v3bits(bd['v3'][0])
                bit_points.append((rnd, rr, osm[rr], len(heads[rr][0]), mb, mnb))
        if rnd in sample_at:
            samples.append(snap(rnd))

    # forced convergence, then a final oracle firing (full stability)
    for _ in range(6 * n_replicas):
        if 'v3' not in alive:
            break
        pairs = [(i, j) for i in range(n_replicas) for j in range(n_replicas)
                 if i != j and heads[i][0] != heads[j][0]]
        if not pairs:
            break
        rng.shuffle(pairs)
        if not any(try_merge(i, j, 'conv') for (i, j) in pairs):
            break
    if oracle:
        fire_oracle('final')
    samples.append(snap('final'))
    return dict(failures=failures, samples=samples, merge_bits=merge_bits,
                law_viol=law_viol, bit_points=bit_points, ins=ins_total[0],
                dels=del_total[0], merges=len(merge_bits), alive=sorted(alive))


# ============================================ C(0): denominator micro-mechanism
def micro_bits():
    """Targeted micro-benchmarks isolating WHERE denominator bits come from.
       hot   : N inserts at the same anchor (one carve run at one parent)
       chain : N inserts each under the previous (depth, no carve run)
       fold  : chain of N, then delete the N-1 interior nodes (isometric
               folds compound the leaf's fractions)
       each hot/fold state is also pushed through one merge
       (merge(init, s, init)) to see what the re-render does to it."""
    D = V3
    def bits(s):
        return v3bits(s[0])[0]
    rows = []
    for N in (8, 16, 32, 64):
        s = D.init()
        for i in range(1, N + 1):
            s = D.apply(s, ('ins', i, 0))
        hot = bits(s)
        hotm = bits(D.merge(D.init(), D.copy(s), D.init()))
        s = D.init()
        for i in range(1, N + 1):
            s = D.apply(s, ('ins', i, i - 1))
        chain = bits(s)
        for i in range(1, N):
            s = D.apply(s, ('del', i))
        fold = bits(s)
        foldm = bits(D.merge(D.init(), D.copy(s), D.init()))
        rows.append((N, hot, hotm, chain, fold, foldm))
    return rows


# ================================================================= reporting
def lsq(pts):
    n = len(pts)
    if n < 2:
        return 0.0, (pts[0][1] if pts else 0.0)
    sx = sum(p[0] for p in pts); sy = sum(p[1] for p in pts)
    sxx = sum(p[0] * p[0] for p in pts); sxy = sum(p[0] * p[1] for p in pts)
    d = n * sxx - sx * sx
    if d == 0:
        return 0.0, sy / n
    b = (n * sxy - sx * sy) / d
    return b, (sy - b * sx) / n


def osm_table(bit_points):
    buckets = [(0, 0), (1, 2), (3, 5), (6, 10), (11, 10**9)]
    rows = []
    for lo, hi in buckets:
        pts = [mb for (_r, _rr, o, _n, mb, _mn) in bit_points if lo <= o <= hi]
        if pts:
            rows.append((f"{lo}" if lo == hi else f"{lo}-{hi if hi < 10**9 else '+'}",
                         len(pts), round(sum(pts) / len(pts), 1), max(pts)))
    return rows


def print_size_table(res, label):
    cols = ['tag', 'events', 'live', 'led', 'led_reach', 'led_naive', 'led_sr',
            'led_stab', 'rga_total', 'bits_max', 'bits_mean']
    hdr = ['round', 'events', 'live', 'led_tot', 'led_reach', 'led_naive',
           'led_sr', 'led_stab', 'rga_tot', 'dbits_max', 'dbits_mean']
    print(f"  [{label}] per-round state size at the most-advanced replica "
          f"(ins={res['ins']} dels={res['dels']} merges={res['merges']})")
    print("    " + "  ".join(f"{h:>9}" for h in hdr))
    for row in res['samples']:
        print("    " + "  ".join(f"{str(row.get(c, '-')):>9}" for c in cols))


def main():
    quick = '--quick' in sys.argv
    W = 74
    print("=" * W)
    print("A1. NAIVE LIVE-REACHABLE PRUNING vs unpruned v3 (pbt DAG harness)")
    print("=" * W)
    cfgs = [
        ("default    4r  8rd del.30 mrg.40", dict(n_replicas=4, n_rounds=8,
         max_ops=2, p_del=0.30, p_merge=0.4), 120 if quick else 400, 0),
        ("harsh      6r 12rd del.55 mrg.50", dict(n_replicas=6, n_rounds=12,
         max_ops=2, p_del=0.55, p_merge=0.5), 60 if quick else 200, 7),
        ("mergeheavy 4r 10rd del.30 mrg.70", dict(n_replicas=4, n_rounds=10,
         max_ops=2, p_del=0.30, p_merge=0.7), 60 if quick else 200, 13),
    ]
    P = PairedVsV3(NaivePrunedV3())
    for label, kw, N, s0 in cfgs:
        fails, first, skipped = safe_sweep(P, N, seed0=s0, **kw)
        print(f"  {label}: {N:4d} executions -> "
              f"{'CLEAN' if not fails else f'{fails} FAILING, first: {first}'}"
              f"  [skipped illegal merges: {skipped}]")

    print("  sensitivity control (broken pruner: drop EVERY dead entry now):")
    fails, first, skipped = safe_sweep(PairedVsV3(DropDeadV3()),
                                       60 if quick else 200, seed0=0,
                                       n_replicas=4, n_rounds=8, max_ops=2,
                                       p_del=0.30, p_merge=0.4)
    print(f"    {fails} FAILING / {60 if quick else 200}"
          f"  first: {first}   (harness bites: expected FAIL)")

    print("  A1b. equiv_stress churn regime (opportunistic LCA merges, "
          "duplicate concurrent deletes):")
    tot, first = a1b_churn(quick)
    print(f"    total: {tot['execs']} execs, {tot['ops']} ops, "
          f"{tot['merges']} legal merges -> "
          f"{'CLEAN' if not tot['bad'] else str(tot['bad']) + ' BAD, first: ' + str(first)}")

    print()
    print("=" * W)
    print("A2. CAUSAL-STABILITY-GATED PRUNING (global oracle)")
    print("=" * W)
    print("  hand-minimized countermodel, stability-ONLY gate "
          "(6 steps: ins1@root, ins2@1, del1, sync+GC, ins3, merge):")
    print(f"    {countermodel_stab_only()}")
    print(f"  control (stability AND reachability on the same script): "
          f"merge OK, read={countermodel_stab_only_control()}")
    n_seeds = 12 if quick else 40
    tal, first, mgs = stability_seed_sweep(n_seeds, 60)
    print(f"  seed sweep ({n_seeds} executions, 4 replicas, 60 rounds, churn, "
          f"epochs/10 + p_merge=.2, {mgs} merges):")
    for n in ('naive', 'sr', 'stab', 'rga'):
        loc = f"   first: {first[n]}" if n in first else ""
        print(f"    {n:6}: {tal[n]} failing executions{loc}")

    print()
    print("=" * W)
    print("B. STATE SIZE + long-run lockstep soundness (custom DAG harness)")
    print("=" * W)
    churn_rounds = 100 if quick else 300
    # (a) epochs-only schedule: work offline, hub-sync every 10 rounds.  Every
    #     sync merge is LCA-legal, all replicas converge at each epoch, and the
    #     stability oracle gets full bite -- the compaction-claim table.
    res_churn = run_lockstep(seed=11, n_replicas=4, n_rounds=churn_rounds,
                             policy=policy_churn(6, 10), p_merge=0.0,
                             variants=('naive', 'sr', 'stab'), with_rga=True,
                             sample_at=(50, 100, 150, 200, 250, 300),
                             sync_every=10)
    print_size_table(res_churn, f"CHURN live~6-10, {churn_rounds} rounds, "
                                f"4 replicas, sync epoch/10 rounds, seed 11")
    print(f"    variant failures: {res_churn['failures'] if res_churn['failures'] else 'none'}")
    print(f"    variants alive at end: {res_churn['alive']}")

    # (b) random-DAG churn (pbt-style merges, no epochs): long-run lockstep
    #     soundness evidence for the naive gate under criss-cross topologies.
    res_dag = run_lockstep(seed=1, n_replicas=4, n_rounds=churn_rounds,
                           policy=policy_churn(6, 10), p_merge=0.4,
                           variants=('naive', 'sr', 'stab'), with_rga=True,
                           sample_at=(100, 200, 300))
    print_size_table(res_dag, f"CHURN random DAG merges, {churn_rounds} rounds, seed 1")
    print(f"    variant failures: {res_dag['failures'] if res_dag['failures'] else 'none'}")
    print(f"    variants alive at end: {res_dag['alive']}")

    growth_rounds = 60 if quick else 120
    res_growth = run_lockstep(seed=2, n_replicas=4, n_rounds=growth_rounds,
                              policy=policy_std(0.3), p_merge=0.0,
                              variants=('naive', 'sr'), with_rga=True,
                              sample_at=(25, 50, 75, 100, 120),
                              sync_every=10)
    print_size_table(res_growth, f"GROWTH del.30, {growth_rounds} rounds, "
                                 f"4 replicas, sync epoch/10 rounds, seed 2")
    print(f"    variant failures: {res_growth['failures'] if res_growth['failures'] else 'none'}")

    print()
    print("=" * W)
    print("C. DENOMINATOR GROWTH (#71)")
    print("=" * W)
    print("  (0) MICRO-MECHANISM (max denominator bits; merge = merge(init,s,init))")
    print("        N    hot  hot+mrg   chain    fold  fold+mrg")
    for N, hot, hotm, chain, fold, foldm in micro_bits():
        print(f"      {N:3d}  {hot:5d}  {hotm:7d}  {chain:6d}  {fold:6d}  {foldm:8d}")
    seq_rounds = 100 if quick else 300
    print(f"  (i) SEQUENTIAL (1 replica, no merges, {seq_rounds} rounds)")
    for lbl, pol, seed in (("del.30 mix ", policy_std(0.3), 3),
                           ("churn 6-10 ", policy_churn(6, 10), 4)):
        res = run_lockstep(seed=seed, n_replicas=1, n_rounds=seq_rounds,
                           policy=pol, p_merge=0.0, variants=('naive',),
                           with_rga=False, oracle=False)
        pts = [(nev, mb) for (_r, _rr, _o, nev, mb, _mn) in res['bit_points']]
        marks = []
        for tgt in (50, 100, 200, 300, 450):
            cand = [p for p in pts if p[0] >= tgt]
            if cand:
                marks.append(min(cand))
        b, a = lsq(pts)
        print(f"    {lbl} ops->max_bits at checkpoints: "
              + "  ".join(f"{n}op:{m}b" for n, m in marks))
        print(f"    {lbl} least-squares max_bits ~= {b:.3f}*ops + {a:.1f}"
              f"   (final: {pts[-1][0]} ops -> {pts[-1][1]} bits)"
              f"   failures: {res['failures'] if res['failures'] else 'none'}")

    print(f"  (ii) MERGE-HEAVY (4 replicas, p_merge=.60, del.30, "
          f"{100 if quick else 200} rounds, seed 5)")
    res = run_lockstep(seed=5, n_replicas=4, n_rounds=100 if quick else 200,
                       policy=policy_std(0.3), p_merge=0.6,
                       variants=('naive',), with_rga=False, oracle=False,
                       sync_every=10)
    mbs = res['merge_bits']
    pre = [p for p, _q, _w in mbs]; post = [q for _p, q, _w in mbs]
    wid = [w for _p, _q, w in mbs]
    allb = [mb for (_r, _rr, _o, _n, mb, _mn) in res['bit_points']]
    nev = max(n for (_r, _rr, _o, n, _mb, _mn) in res['bit_points'])
    print(f"    merges: {len(mbs)}   pre-merge bits mean/max: "
          f"{sum(pre)/len(pre):.1f}/{max(pre)}   post-merge (re-rendered) "
          f"mean/max: {sum(post)/len(post):.1f}/{max(post)}")
    print(f"    resets (post<pre): {sum(1 for p, q, _w in mbs if q < p)}/{len(mbs)}"
          f"   overall max bits across {nev} events: {max(allb)}"
          f"   failures: {res['failures'] if res['failures'] else 'none'}")
    print(f"    EXACT LAW post_bits == max_sibling_width + 2: "
          f"{len(mbs) - len(res['law_viol'])}/{len(mbs)} merges"
          f"   (width mean/max: {sum(wid)/len(wid):.1f}/{max(wid)})"
          f"{'' if not res['law_viol'] else '   VIOLATIONS: ' + str(res['law_viol'][:3])}")
    print("    max_bits grouped by ops-since-this-replica's-last-merge:")
    for rng_lbl, cnt, mean, mx in osm_table(res['bit_points']):
        print(f"      osm {rng_lbl:>5}: n={cnt:4d}  mean={mean:5.1f}  max={mx}")
    b, a = lsq([(o, mb) for (_r, _rr, o, _n, mb, _mn) in res['bit_points']])
    print(f"    least-squares max_bits ~= {b:.2f}*opsSinceMerge + {a:.1f}")

    print("  (iii) CHURN regime (run B(a), seed 11, sync epoch/10 rounds): "
          "max_bits grouped by ops-since-last-merge:")
    for rng_lbl, cnt, mean, mx in osm_table(res_churn['bit_points']):
        print(f"      osm {rng_lbl:>5}: n={cnt:4d}  mean={mean:5.1f}  max={mx}")
    allb = [mb for (_r, _rr, _o, _n, mb, _mn) in res_churn['bit_points']]
    print(f"    overall max bits across whole churn run: {max(allb)}"
          f"   (vs {res_churn['ins'] + res_churn['dels']} total ops)")
    lv = res_churn['law_viol']
    wid = [w for _p, _q, w in res_churn['merge_bits']]
    print(f"    EXACT LAW post_bits == max_sibling_width + 2: "
          f"{res_churn['merges'] - len(lv)}/{res_churn['merges']} merges"
          f"   (width mean/max: {sum(wid)/len(wid):.1f}/{max(wid)})"
          f"{'' if not lv else '   VIOLATIONS: ' + str(lv[:3])}")


if __name__ == '__main__':
    main()
