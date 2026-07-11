#!/usr/bin/env python3
"""
PBT for the sibling-linked tombstone-free RGA ("SL") against the OBSERVABLE spec.
Design record: /Users/kc/repos/sal/whiteboard/sibling-linked-rga-notes.md

Three-verdict scheme per merge: MATCH (== tombstoned oracle), LICENSED divergence
(differing pairs never displayed in tombstoned order by any state), VIOLATION
(strong-list breach: some pair displayed in both orders across the trial's states,
or a cycle in the union of displayed orders).
"""
import random, sys
from collections import defaultdict

ORIG = {}      # id -> insert anchor   (global side record, oracle only)
DELETED = set()

# ---------------- state ----------------
class St:
    __slots__ = ('V', 'par', 'sib')
    def __init__(s): s.V = set(); s.par = {}; s.sib = {}
    def clone(s):
        t = St(); t.V = set(s.V); t.par = dict(s.par); t.sib = dict(s.sib); return t
    def row(s, p):
        kids = [u for u in s.V if s.par[u] == p]
        if not kids: return []
        pointed = {s.sib[u] for u in kids if u in s.sib}
        heads = [u for u in kids if u not in pointed]
        assert len(heads) == 1, f"row {p}: heads {heads}"
        out = [heads[0]]
        seen = {heads[0]}
        while out[-1] in s.sib:
            nxt = s.sib[out[-1]]
            assert nxt not in seen, f"sib cycle in row {p}"
            out.append(nxt); seen.add(nxt)
        assert set(out) == set(kids)
        return out
    def read(s):
        out = []
        def vis(p):
            for c in s.row(p):
                out.append(c); vis(c)
        vis(0); return out

def insert(s, x, a):
    assert x not in ORIG, f'id collision {x}'
    ORIG[x] = a
    r = s.row(a)
    s.V.add(x); s.par[x] = a
    if r: s.sib[x] = r[0]

def delete(s, d):
    DELETED.add(d)
    p = s.par[d]
    kids = s.row(d)
    left = next((u for u in s.V if s.sib.get(u) == d), None)
    for c in kids: s.par[c] = p
    if kids:
        if left is not None: s.sib[left] = kids[0]
        if d in s.sib: s.sib[kids[-1]] = s.sib[d]
        elif kids[-1] in s.sib: del s.sib[kids[-1]]
    else:
        if left is not None:
            if d in s.sib: s.sib[left] = s.sib[d]
            else: del s.sib[left]
    s.V.discard(d); del s.par[d]; s.sib.pop(d, None)

# ---------------- tombstoned oracle ----------------
def oracle_read():
    ch = defaultdict(list)
    for n in ORIG: ch[ORIG[n]].append(n)
    for k in ch: ch[k].sort(reverse=True)
    out = []
    def vis(p):
        for c in ch.get(p, []):
            if c not in DELETED: out.append(c)
            vis(c)
    vis(0); return out

# ---------------- merge ----------------
def merge(L, A, B):
    liveM = (A.V & B.V) | (A.V - L.V) | (B.V - L.V)
    markers = L.V & (A.V ^ B.V)          # L-nodes live in exactly one branch
    W = liveM | markers
    ldoc = {n: i for i, n in enumerate(L.read())}

    def wpar(u):                          # deepest W-ancestor of an L-node, via L
        p = L.par[u]
        while p != 0 and p not in W:
            p = L.par[p]
        return p

    skelrow = {0: []}
    rowof = {}
    for u in sorted(W & L.V, key=lambda u: ldoc[u]):
        p = wpar(u)
        skelrow.setdefault(p, []).append(u)
        skelrow.setdefault(u, [])
        rowof[u] = p
    # branch-born wholesale rows (branch-born parents)
    bbrows = {}
    for X in (A, B):
        for q in X.V - L.V:
            r = X.row(q)
            if r: bbrows[q] = list(r)
    # runs of branch-born nodes in rows headed by L-nodes or root
    inserts = []                          # ('slot', row, k, run) | ('end', p, run)
    for X in (A, B):
        hosts = {X.par[u] for u in X.V - L.V if X.par[u] == 0 or X.par[u] in L.V}
        for p in sorted(hosts):
            r = X.row(p)
            i = 0
            pre = None                    # last L-node seen before the current run
            while i < len(r):
                if r[i] in L.V:
                    pre = r[i]; i += 1; continue
                j = i
                while j < len(r) and r[j] not in L.V: j += 1
                run = r[i:j]
                if pre is not None:
                    # ride immediately behind the predecessor, in its final row
                    tr = rowof[pre]
                    k = skelrow[tr].index(pre) + 1
                    inserts.append(('slot', tr, k, run))
                elif j < len(r):
                    s = r[j]              # successor; row head: may jump own-deleted markers
                    tr = rowof[s]
                    k = skelrow[tr].index(s)
                    while k > 0 and skelrow[tr][k-1] in markers and skelrow[tr][k-1] not in X.V:
                        k -= 1
                    inserts.append(('slot', tr, k, run))
                else:
                    inserts.append(('end', p, run))
                i = j
    # assemble
    out_rows = {}
    for p, skel in skelrow.items():
        slots = {}
        endr = []
        for ins_ in inserts:
            if ins_[0] == 'slot' and ins_[1] == p:
                slots.setdefault(ins_[2], []).append(ins_[3])
            elif ins_[0] == 'end' and ins_[1] == p:
                endr.append(ins_[2])
        row = []
        for k in range(len(skel) + 1):
            for run in sorted(slots.get(k, []), key=lambda r: -r[0]):
                row.extend(run)
            if k < len(skel): row.append(skel[k])
        for run in sorted(endr, key=lambda r: -r[0]):
            row.extend(run)
        out_rows[p] = row
    for q, r in bbrows.items():
        out_rows.setdefault(q, r)
    # splice markers (position-holders only)
    changed = True
    while changed:
        changed = False
        for p in list(out_rows):
            r = out_rows.get(p, [])
            if any(u in markers for u in r):
                nr = []
                for u in r:
                    if u in markers:
                        nr.extend(out_rows.pop(u, [])); changed = True
                    else: nr.append(u)
                out_rows[p] = nr
        for m in list(out_rows):
            if m in markers and not out_rows[m]:
                out_rows.pop(m)
    M = St(); M.V = set(liveM)
    for p, r in out_rows.items():
        if p in markers: continue
        for i, u in enumerate(r):
            M.par[u] = p
            if i + 1 < len(r): M.sib[u] = r[i + 1]
    for u in M.V: assert u in M.par, f"unplaced {u}"
    return M

# ---------------- observation log / checks ----------------
class Obs:
    def __init__(o): o.orders = {}   # (x,y) normalized -> set of dirs ('<' means x<y)
    def display(o, read):
        for i in range(len(read)):
            for j in range(i + 1, len(read)):
                x, y = read[i], read[j]
                k = (min(x, y), max(x, y))
                d = '<' if x == k[0] else '>'
                o.orders.setdefault(k, set()).add(d)
    def antisym_violations(o):
        return [k for k, ds in o.orders.items() if len(ds) > 1]
    def displayed(o, x, y):
        """directions displayed for pair"""
        k = (min(x, y), max(x, y))
        return o.orders.get(k, set())
    def acyclic(o):
        g = defaultdict(set); nodes = set()
        for (a, b), ds in o.orders.items():
            if len(ds) != 1: continue
            x, y = (a, b) if '<' in ds else (b, a)
            g[x].add(y); nodes.update((x, y))
        WHITE, GRAY, BLACK = 0, 1, 2
        color = dict.fromkeys(nodes, WHITE)
        def dfs(v):
            color[v] = GRAY
            for w in g[v]:
                if color[w] == GRAY: return False
                if color[w] == WHITE and not dfs(w): return False
            color[v] = BLACK; return True
        return all(color[v] != WHITE or dfs(v) for v in list(nodes))

def classify_merge(mread, obs):
    orc = oracle_read()
    assert set(orc) == set(mread), "survivor sets differ"
    if mread == orc: return 'match', []
    pos = {u: i for i, u in enumerate(mread)}
    bad = []
    div = []
    for i in range(len(orc)):
        for j in range(i + 1, len(orc)):
            x, y = orc[i], orc[j]          # tombstoned: x before y
            if pos[x] > pos[y]:
                div.append((x, y))
    # licensed iff tombstoned direction never displayed by any state
    for (x, y) in div:
        k = (min(x, y), max(x, y)); want = '<' if x == k[0] else '>'
        if want in obs.orders.get(k, set()):
            bad.append((x, y))
    return ('violation' if bad else 'licensed'), (bad or div)

# ---------------- generators ----------------
def gen_ops(s, rng, fresh, obs, nops):
    live_local = sorted(s.V)
    i = 0
    for _ in range(nops):
        live_local = sorted(s.V)
        if rng.random() < 0.30 and live_local:
            delete(s, rng.choice(live_local))
        else:
            if i >= len(fresh): break
            x = fresh[i]; i += 1
            insert(s, x, rng.choice([0] + live_local))
        obs.display(s.read())

def fresh_ids(mode, e, top, n=24):
    if mode == 'banded':
        return (list(range(top + 10000 * (e + 1), top + 10000 * (e + 1) + n)),
                list(range(top + 20000 * (e + 1), top + 20000 * (e + 1) + n)))
    return ([top + 2 * i for i in range(1, n)], [top + 2 * i + 1 for i in range(1, n)])

def trial_epochs(rng, E, mode):
    global ORIG, DELETED
    ORIG = {}; DELETED = set()
    import builtins
    globals()['ORIG'] = ORIG; globals()['DELETED'] = DELETED
    obs = Obs()
    cur = St()
    for k in range(rng.randint(2, 6)):
        insert(cur, k + 1, rng.choice([0] + sorted(cur.V)))
        obs.display(cur.read())
    verdicts = []
    for e in range(E):
        top = max(ORIG) if ORIG else 0
        fa, fb = fresh_ids(mode, e, top)
        A = cur.clone(); gen_ops(A, rng, fa, obs, rng.randint(1, 6))
        B = cur.clone(); gen_ops(B, rng, fb, obs, rng.randint(1, 6))
        M = merge(cur, A, B)
        M2 = merge(cur, B, A)
        assert M.read() == M2.read(), "merge not symmetric"
        obs.display(M.read())
        v, pairs = classify_merge(M.read(), obs)
        verdicts.append(v)
        cur = M
    anti = obs.antisym_violations()
    ok_acyclic = obs.acyclic()
    return verdicts, anti, ok_acyclic

def trial_stale(rng, mode):
    """R3 forks at epoch 0, idles/works, merges in at the end with the old fork as L."""
    global ORIG, DELETED
    ORIG = {}; DELETED = set()
    globals()['ORIG'] = ORIG; globals()['DELETED'] = DELETED
    obs = Obs()
    cur = St()
    for k in range(rng.randint(1, 5)):
        insert(cur, k + 1, rng.choice([0] + sorted(cur.V)))
        obs.display(cur.read())
    fork = cur.clone()
    R3 = cur.clone()
    r3_pending = rng.random() < 0.5
    verdicts = []
    for e in range(rng.randint(1, 3)):
        top = max(ORIG) if ORIG else 0
        fa, fb = fresh_ids(mode, e, top)
        A = cur.clone(); gen_ops(A, rng, fa, obs, rng.randint(1, 5))
        B = cur.clone(); gen_ops(B, rng, fb, obs, rng.randint(1, 5))
        cur = merge(cur, A, B); obs.display(cur.read())
        v, _ = classify_merge(cur.read(), obs); verdicts.append(v)
    if r3_pending:
        f3 = [900001 + 2 * i for i in range(6)] if mode != 'banded' else list(range(500000, 500006))
        gen_ops(R3, rng, f3, obs, rng.randint(0, 3))
    M = merge(fork, cur, R3)           # stale: L = old fork point
    assert M.read() == merge(fork, R3, cur).read()
    obs.display(M.read())
    v, _ = classify_merge(M.read(), obs); verdicts.append(v)
    anti = obs.antisym_violations()
    return verdicts, anti, obs.acyclic()

# ---------------- directed witnesses ----------------
def reset():
    global ORIG, DELETED
    ORIG = {}; DELETED = set()
    globals()['ORIG'] = ORIG; globals()['DELETED'] = DELETED

def witness_all():
    results = []
    def chk(name, got, want, verdict=None, wantv=None):
        ok = got == want and (verdict == wantv if wantv else True)
        results.append((name, got, want, verdict, ok))
    # 1. T2
    reset(); obs = Obs()
    L = St(); insert(L, 1, 0); insert(L, 2, 1); insert(L, 3, 1)
    A = L.clone(); insert(A, 10, 3); delete(A, 3)
    B = L.clone(); insert(B, 20, 2); delete(B, 2)
    for s in (L, A, B): obs.display(s.read())
    M = merge(L, A, B); obs.display(M.read())
    v, _ = classify_merge(M.read(), obs)
    chk('T2', M.read(), [1, 10, 20], v, 'match')
    # 2. CX-F
    reset(); obs = Obs()
    L = St(); insert(L, 1, 0); insert(L, 2, 1)
    A = L.clone(); insert(A, 3, 1); insert(A, 4, 3); delete(A, 3); delete(A, 1)
    B = L.clone()
    for s in (L, A, B): obs.display(s.read())
    M = merge(L, A, B); obs.display(M.read())
    v, _ = classify_merge(M.read(), obs)
    chk('CX-F', M.read(), [4, 2], v, 'match')
    # 3. stale-LCA on top of CX-F
    M2 = merge(L, M, L.clone()); obs.display(M2.read())
    v2, _ = classify_merge(M2.read(), obs)
    chk('staleLCA', M2.read(), [4, 2], v2, 'match')
    # 4. leapfrog
    reset(); obs = Obs()
    L = St(); insert(L, 1, 0); insert(L, 2, 1); insert(L, 3, 0)
    A = L.clone(); insert(A, 4, 1); insert(A, 5, 4); delete(A, 4); delete(A, 1)
    B = L.clone()
    for s in (L, A, B): obs.display(s.read())
    M = merge(L, A, B); obs.display(M.read())
    v, _ = classify_merge(M.read(), obs)
    chk('leapfrog', M.read(), [3, 5, 2], v, 'match')
    # 5. both delete x
    reset(); obs = Obs()
    L = St(); insert(L, 1, 0)
    A = L.clone(); insert(A, 10, 1); delete(A, 1)
    B = L.clone(); insert(B, 9, 1); delete(B, 1)
    for s in (L, A, B): obs.display(s.read())
    M = merge(L, A, B); obs.display(M.read())
    v, _ = classify_merge(M.read(), obs)
    chk('bothDel', M.read(), [10, 9], v, 'match')
    # 6. w-slot
    reset(); obs = Obs()
    L = St(); insert(L, 1, 0); insert(L, 3, 0); insert(L, 4, 3)   # z=1, w=3, c=4<-w
    A = L.clone(); insert(A, 5, 0)                                 # p=5
    B = L.clone(); insert(B, 6, 3); insert(B, 7, 6); delete(B, 6); delete(B, 3)
    for s in (L, A, B): obs.display(s.read())
    M = merge(L, A, B); obs.display(M.read())
    v, _ = classify_merge(M.read(), obs)
    chk('w-slot', M.read(), [5, 7, 4, 1], v, 'match')
    # 7. fooling worlds
    outs = []
    for gts in (2, 6):
        reset(); obs = Obs()
        L = St()
        A = L.clone(); insert(A, 5, 0)
        B = L.clone(); insert(B, gts, 0); insert(B, 10, gts); delete(B, gts)
        for s in (L, A, B): obs.display(s.read())
        M = merge(L, A, B); obs.display(M.read())
        v, _ = classify_merge(M.read(), obs)
        outs.append((M.read(), v))
    chk('fool-w1', outs[0][0], [10, 5], outs[0][1], 'licensed')
    chk('fool-w2', outs[1][0], [10, 5], outs[1][1], 'match')
    chk('fool-same-output', outs[0][0], outs[1][0])
    return results

# ---------------- main ----------------
if __name__ == '__main__':
    print("[directed witnesses]")
    allok = True
    for name, got, want, verdict, ok in witness_all():
        print(f"  {name:18s} got={got} want={want} verdict={verdict}  {'PASS' if ok else 'FAIL'}")
        allok &= ok
    if not allok: sys.exit(1)
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    for mode in ('banded', 'interleaved'):
        for E in (1, 2, 3, 4):
            rng = random.Random(20260711 + E * 7 + (0 if mode == 'banded' else 1))
            n = N if E <= 2 else N // 2
            cnt = defaultdict(int); viol = anti_v = cyc = err = 0; sample = None
            for t in range(n):
                try:
                    verdicts, anti, okc = trial_epochs(rng, E, mode)
                    for v in verdicts: cnt[v] += 1
                    if 'violation' in verdicts: viol += 1; sample = sample or t
                    if anti: anti_v += 1; sample = sample or t
                    if not okc: cyc += 1; sample = sample or t
                except AssertionError as ex:
                    err += 1; sample = sample or (t, str(ex))
            print(f"[epochs {mode:11s} E={E}] n={n} merges={sum(cnt.values())} "
                  f"match={cnt['match']} licensed={cnt['licensed']} "
                  f"FLIPS={anti_v} oracleflip={viol} slcycles(info)={cyc} asserts={err} sample={sample}")
        rng = random.Random(424242)
        n = N // 2
        cnt = defaultdict(int); viol = anti_v = cyc = err = 0; sample = None
        for t in range(n):
            try:
                verdicts, anti, okc = trial_stale(rng, mode)
                for v in verdicts: cnt[v] += 1
                if 'violation' in verdicts: viol += 1; sample = sample or t
                if anti: anti_v += 1; sample = sample or t
                if not okc: cyc += 1; sample = sample or t
            except AssertionError as ex:
                err += 1; sample = sample or (t, str(ex))
        print(f"[stale  {mode:11s}     ] n={n} merges={sum(cnt.values())} "
              f"match={cnt['match']} licensed={cnt['licensed']} "
              f"FLIPS={anti_v} oracleflip={viol} slcycles(info)={cyc} asserts={err} sample={sample}")
