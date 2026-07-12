#!/usr/bin/env python3
"""
anomaly_matrix.py — VERIFIED anomaly-comparison matrix for sequence RDTs (task #64).

Turns the DRAFT table of whiteboard/sibling-linked-proof.md §8 into a machine-verified
one. Six minimal implementations behind ONE interface (insert(x, anchor)/delete(x)/read/
ternary merge(L,A,B)); eight uniform column checks; every ✗ backed by a minimal concrete
witness run through the implementation, every ✓ by PBT counts.

Rows: TombRGA, FlatTF, Logoot, StoredPath, Shesha, Fugue.
Cols: (a) tombstone-free  (b) bounded per-node metadata  (c) sequential = naive list
      (d) pairwise display stability  (e) strong list (acyclic displays)
      (f) RGA-oracle fidelity  (g) non-interleaving forward  (h) non-interleaving backward

Harness architecture ported from whiteboard/sl_pbt.py (Obs display-log, epoch/stale
trial generators, three-verdict oracle classification).
"""
import random, sys
from collections import defaultdict

sys.setrecursionlimit(100000)

# ================================================================ implementations
# Common interface: new() clone(s) insert(s,x,a) delete(s,x) read(s) merge(L,A,B)
#                   mentions(s) -> set of node ids referenced anywhere in the repr
#                   meta_sizes(s) -> {id: per-node representation size (field count)}


class TombRGA:
    """Tombstoned RGA: nodes (id -> insert anchor) never removed + deleted set.
    read = DFS, siblings desc-id, dead emit nothing (but are traversed).
    merge = union of nodes, union of deleted (L unused: tombstones carry removal)."""
    name = 'TombRGA'
    def new(self): return ({}, set())
    def clone(self, s): return (dict(s[0]), set(s[1]))
    def insert(self, s, x, a): s[0][x] = a
    def delete(self, s, x): s[1].add(x)
    def read(self, s):
        nodes, dead = s
        ch = defaultdict(list)
        for n, a in nodes.items(): ch[a].append(n)
        for k in ch: ch[k].sort(reverse=True)
        out = []
        def vis(p):
            for c in ch.get(p, []):
                if c not in dead: out.append(c)
                vis(c)
        vis(0); return out
    def merge(self, L, A, B): return ({**A[0], **B[0]}, A[1] | B[1])
    def mentions(self, s):
        return set(s[0]) | {a for a in s[0].values() if a != 0} | set(s[1])
    def meta_sizes(self, s):  # per node: (anchor) + grave bit; constant
        return {x: 2 + (1 if x in s[1] else 0) for x in s[0]}


class FlatTF:
    """Flat tombstone-free RGA (the repo's refuted design, cf. Sal/MRDTs/RGA/ and
    AgentNotes.md): live (id -> anchor-as-nearest-live-ancestor) records.
    delete rehomes children to the deleted node's stored anchor; read ALWAYS re-sorts
    siblings desc-id; merge = live-set rule, anchors resolved to nearest merged-live
    ancestor by chasing the source branch's own records."""
    name = 'FlatTF'
    resolve_disagreements = 0   # instrumentation: A-chase vs B-chase ever differ?
    def new(self): return {}
    def clone(self, s): return dict(s)
    def insert(self, s, x, a): s[x] = a
    def delete(self, s, d):
        pa = s.pop(d)
        for x, a in list(s.items()):
            if a == d: s[x] = pa
    def read(self, s):
        ch = defaultdict(list)
        for n, a in s.items(): ch[a].append(n)
        for k in ch: ch[k].sort(reverse=True)
        out = []
        def vis(p):
            for c in ch.get(p, []): out.append(c); vis(c)
        vis(0); return out
    def merge(self, L, A, B):
        live = (A.keys() & B.keys()) | (A.keys() - L.keys()) | (B.keys() - L.keys())
        def resolve(a, X, Y):
            while a != 0 and a not in live:
                a = X[a] if a in X else Y[a]
            return a
        out = {}
        for x in live:
            if x in A and x in B:
                ra, rb = resolve(A[x], A, B), resolve(B[x], B, A)
                if ra != rb: FlatTF.resolve_disagreements += 1
                out[x] = max(ra, rb)
            elif x in A: out[x] = resolve(A[x], A, B)
            else:        out[x] = resolve(B[x], B, A)
        return out
    def mentions(self, s): return set(s) | {a for a in s.values() if a != 0}
    def meta_sizes(self, s): return {x: 2 for x in s}


BASE, MIDD = 16, 8

def logoot_alloc(l, r, ts):
    """Dense position strictly between l and r. Positions: tuples of (digit, ts) pairs,
    lexicographic; digits in [0,BASE); l may be () (bottom), r may be None (top).
    Invariant maintained: no returned position ends in digit 0 (guarantees the
    copy-descend loop below terminates before exhausting r)."""
    prefix = []
    i = 0
    r_active = r is not None
    while True:
        le = l[i] if i < len(l) else None
        re = r[i] if (r_active and i < len(r)) else None
        if le is not None and re is not None and le == re:
            prefix.append(le); i += 1; continue
        ld = le[0] if le is not None else -1
        rd = re[0] if re is not None else BASE
        if rd - ld > 1:                       # digit room at this level
            if le is not None: d = ld + 1     # boundary+ (after-left)
            elif re is not None: d = rd - 1   # boundary- (before-right)
            else: d = MIDD                    # free slot
            if d == 0:                        # avoid trailing zero
                prefix.extend([(0, ts), (MIDD, ts)])
            else:
                prefix.append((d, ts))
            return tuple(prefix)
        if le is not None:                    # le < re, digits equal/adjacent: descend left
            prefix.append(le); i += 1; r_active = False; continue
        # l exhausted and rd == 0: copy r's element and keep needing < r's residual
        prefix.append(re); i += 1


class Logoot:
    """Dense immutable positions (Logoot-style): position = list of (digit, ts) pairs;
    insert allocates strictly between anchor's position and its current successor;
    delete removes; read = sort by position; merge = live-set rule (positions immutable)."""
    name = 'Logoot'
    def new(self): return {}
    def clone(self, s): return dict(s)
    def insert(self, s, x, a):
        poss = sorted(s.values())
        if a == 0:
            l, r = (), (poss[0] if poss else None)
        else:
            l = s[a]
            after = [p for p in poss if p > l]
            r = after[0] if after else None
        s[x] = logoot_alloc(l, r, x)
    def delete(self, s, x): del s[x]
    def read(self, s): return [n for n, _ in sorted(s.items(), key=lambda kv: kv[1])]
    def merge(self, L, A, B):
        live = (A.keys() & B.keys()) | (A.keys() - L.keys()) | (B.keys() - L.keys())
        u = {**A, **B}
        return {x: u[x] for x in live}
    def mentions(self, s):
        ids = set(s)
        for p in s.values():
            for (_, t) in p: ids.add(t)
        return ids
    def meta_sizes(self, s): return {x: 2 * len(p) for x, p in s.items()}


class StoredPath:
    """Stored-path (phase 1, repo scratch): position = anchor's position ++ [-ts]
    (immutable); delete = filter; read = lex sort; merge = live-set rule."""
    name = 'StoredPath'
    def new(self): return {}
    def clone(self, s): return dict(s)
    def insert(self, s, x, a): s[x] = (s[a] if a != 0 else ()) + (-x,)
    def delete(self, s, x): del s[x]
    def read(self, s): return [n for n, _ in sorted(s.items(), key=lambda kv: kv[1])]
    def merge(self, L, A, B):
        live = (A.keys() & B.keys()) | (A.keys() - L.keys()) | (B.keys() - L.keys())
        u = {**A, **B}
        return {x: u[x] for x in live}
    def mentions(self, s): return set(s) | {-c for p in s.values() for c in p}
    def meta_sizes(self, s): return {x: len(p) for x, p in s.items()}


class SheshaSt:
    __slots__ = ('V', 'par', 'sib')
    def __init__(s): s.V = set(); s.par = {}; s.sib = {}
    def clone(s):
        t = SheshaSt(); t.V = set(s.V); t.par = dict(s.par); t.sib = dict(s.sib); return t
    def row(s, p):
        kids = [u for u in s.V if s.par[u] == p]
        if not kids: return []
        pointed = {s.sib[u] for u in kids if u in s.sib}
        heads = [u for u in kids if u not in pointed]
        assert len(heads) == 1, f"row {p}: heads {heads}"
        out = [heads[0]]; seen = {heads[0]}
        while out[-1] in s.sib:
            nxt = s.sib[out[-1]]
            assert nxt not in seen, f"sib cycle in row {p}"
            out.append(nxt); seen.add(nxt)
        assert set(out) == set(kids)
        return out
    def read(s):
        out = []
        def vis(p):
            for c in s.row(p): out.append(c); vis(c)
        vis(0); return out


class Shesha:
    """Sibling-linked list (whiteboard/sl_pbt.py, ported verbatim modulo the oracle
    globals ORIG/DELETED, which live in the runner here)."""
    name = 'Shesha'
    def new(self): return SheshaSt()
    def clone(self, s): return s.clone()
    def insert(self, s, x, a):
        r = s.row(a)
        s.V.add(x); s.par[x] = a
        if r: s.sib[x] = r[0]
    def delete(self, s, d):
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
    def read(self, s): return s.read()
    def merge(self, L, A, B):
        liveM = (A.V & B.V) | (A.V - L.V) | (B.V - L.V)
        markers = L.V & (A.V ^ B.V)
        W = liveM | markers
        ldoc = {n: i for i, n in enumerate(L.read())}
        def wpar(u):
            p = L.par[u]
            while p != 0 and p not in W: p = L.par[p]
            return p
        skelrow = {0: []}; rowof = {}
        for u in sorted(W & L.V, key=lambda u: ldoc[u]):
            p = wpar(u)
            skelrow.setdefault(p, []).append(u)
            skelrow.setdefault(u, [])
            rowof[u] = p
        bbrows = {}
        for X in (A, B):
            for q in X.V - L.V:
                r = X.row(q)
                if r: bbrows[q] = list(r)
        inserts = []
        for X in (A, B):
            hosts = {X.par[u] for u in X.V - L.V if X.par[u] == 0 or X.par[u] in L.V}
            for p in sorted(hosts):
                r = X.row(p)
                i = 0; pre = None
                while i < len(r):
                    if r[i] in L.V: pre = r[i]; i += 1; continue
                    j = i
                    while j < len(r) and r[j] not in L.V: j += 1
                    run = r[i:j]
                    if pre is not None:
                        tr = rowof[pre]; k = skelrow[tr].index(pre) + 1
                        inserts.append(('slot', tr, k, run))
                    elif j < len(r):
                        sX = r[j]; tr = rowof[sX]; k = skelrow[tr].index(sX)
                        while k > 0 and skelrow[tr][k-1] in markers and skelrow[tr][k-1] not in X.V:
                            k -= 1
                        inserts.append(('slot', tr, k, run))
                    else:
                        inserts.append(('end', p, run))
                    i = j
        out_rows = {}
        for p, skel in skelrow.items():
            slots = {}; endr = []
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
        M = SheshaSt(); M.V = set(liveM)
        for p, r in out_rows.items():
            if p in markers: continue
            for i, u in enumerate(r):
                M.par[u] = p
                if i + 1 < len(r): M.sib[u] = r[i + 1]
        for u in M.V: assert u in M.par, f"unplaced {u}"
        return M
    def mentions(self, s):
        return (set(s.V) | {p for p in s.par.values() if p != 0}
                | set(s.par) | set(s.sib) | set(s.sib.values()))
    def meta_sizes(self, s):  # row-local per-node representation: par entry + sib entry
        return {x: 1 + (1 if x in s.sib else 0) for x in s.V}


class Fugue:
    """Fugue (Weidner & Kleppmann 2023), minimal: tree with left/right child lists,
    tombstoned delete. insert after l: if l has no right children -> right child of l;
    else left child of l's visible successor (fallback: right child of l when no
    successor). Same-side siblings sorted by id ascending. merge = union + union."""
    name = 'Fugue'
    def new(self): return ({}, set())            # id -> (parent, side); dead
    def clone(self, s): return (dict(s[0]), set(s[1]))
    def _kids(self, nodes):
        L, R = defaultdict(list), defaultdict(list)
        for n, (p, sd) in nodes.items():
            (L if sd == 'L' else R)[p].append(n)
        for d in (L, R):
            for k in d: d[k].sort()
        return L, R
    def read(self, s):
        nodes, dead = s
        L, R = self._kids(nodes)
        out = []
        def vis(n):
            for c in L.get(n, []): vis(c)
            if n != 0 and n not in dead: out.append(n)
            for c in R.get(n, []): vis(c)
        vis(0); return out
    def insert(self, s, x, a):
        nodes, dead = s
        vis = self.read(s)
        succ = (vis[0] if vis else None) if a == 0 else \
               (vis[vis.index(a) + 1] if vis.index(a) + 1 < len(vis) else None)
        has_right = any(p == a and sd == 'R' for (p, sd) in nodes.values())
        if not has_right: nodes[x] = (a, 'R')
        elif succ is not None: nodes[x] = (succ, 'L')
        else: nodes[x] = (a, 'R')
    def delete(self, s, x): s[1].add(x)
    def merge(self, L, A, B): return ({**A[0], **B[0]}, A[1] | B[1])
    def mentions(self, s):
        return set(s[0]) | {p for (p, _) in s[0].values() if p != 0} | set(s[1])
    def meta_sizes(self, s):
        return {x: 3 + (1 if x in s[1] else 0) for x in s[0]}


IMPLS = [TombRGA(), FlatTF(), Logoot(), StoredPath(), Shesha(), Fugue()]

# ================================================================ oracle & naive list

def oracle_read(orig, dead):
    """Tombstoned-RGA replay over ALL ops delivered so far."""
    ch = defaultdict(list)
    for n, a in orig.items(): ch[a].append(n)
    for k in ch: ch[k].sort(reverse=True)
    out = []
    def vis(p):
        for c in ch.get(p, []):
            if c not in dead: out.append(c)
            vis(c)
    vis(0); return out

def naive_apply(ref, op):
    if op[0] == 'ins':
        _, x, a = op
        if a == 0: ref.insert(0, x)
        else: ref.insert(ref.index(a) + 1, x)
    else:
        ref.remove(op[1])

# ================================================================ Obs (from sl_pbt)

class Obs:
    def __init__(o): o.orders = {}
    def display(o, read):
        for i in range(len(read)):
            for j in range(i + 1, len(read)):
                x, y = read[i], read[j]
                k = (x, y) if x < y else (y, x)
                d = '<' if x == k[0] else '>'
                o.orders.setdefault(k, set()).add(d)
    def antisym_violations(o):
        return [k for k, ds in o.orders.items() if len(ds) > 1]
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
    def find_cycle(o):
        g = defaultdict(set)
        for (a, b), ds in o.orders.items():
            if len(ds) != 1: continue
            x, y = (a, b) if '<' in ds else (b, a)
            g[x].add(y)
        path, onpath, seen = [], set(), set()
        def dfs(v):
            path.append(v); onpath.add(v); seen.add(v)
            for w in g[v]:
                if w in onpath: return path[path.index(w):] + [w]
                if w not in seen:
                    c = dfs(w)
                    if c: return c
            path.pop(); onpath.discard(v); return None
        for v in list(g):
            if v not in seen:
                c = dfs(v)
                if c: return c
        return None

def classify_merge(mread, obs, orig, dead):
    orc = oracle_read(orig, dead)
    if set(orc) != set(mread): return 'liveset', []
    if mread == orc: return 'match', []
    pos = {u: i for i, u in enumerate(mread)}
    div = [(x, y) for i, x in enumerate(orc) for y in orc[i+1:] if pos[x] > pos[y]]
    bad = []
    for (x, y) in div:
        k = (x, y) if x < y else (y, x)
        want = '<' if x == k[0] else '>'
        if want in obs.orders.get(k, set()): bad.append((x, y))
    return ('violation' if bad else 'licensed'), (bad or div)

# ================================================================ trial scripts
# Scripts are implementation-independent: live sets follow set semantics, which every
# row agrees on under honest LCA (asserted at runtime via the survivor-set check).

def fresh_ids(mode, e, top, n=24):
    if mode == 'banded':
        return (list(range(top + 10000 * (e + 1), top + 10000 * (e + 1) + n)),
                list(range(top + 20000 * (e + 1), top + 20000 * (e + 1) + n)))
    return ([top + 2 * i for i in range(1, n)], [top + 2 * i + 1 for i in range(1, n)])

def gen_branch_ops(rng, live, fresh, nops, del_p=0.30):
    ops = []; i = 0
    for _ in range(nops):
        ll = sorted(live)
        if rng.random() < del_p and ll:
            x = rng.choice(ll); ops.append(('del', x)); live.discard(x)
        else:
            if i >= len(fresh): break
            x = fresh[i]; i += 1
            ops.append(('ins', x, rng.choice([0] + ll))); live.add(x)
    return ops

def live_merge(L, A, B): return (A & B) | (A - L) | (B - L)

def gen_epoch_trial(rng, E, mode, del_p=0.30):
    init = []; live = set()
    for k in range(rng.randint(2, 6)):
        init.append(('ins', k + 1, rng.choice([0] + sorted(live)))); live.add(k + 1)
    maxid = len(init)
    epochs = []
    for e in range(E):
        fa, fb = fresh_ids(mode, e, maxid)
        la, lb = set(live), set(live)
        opsA = gen_branch_ops(rng, la, fa, rng.randint(1, 6), del_p)
        opsB = gen_branch_ops(rng, lb, fb, rng.randint(1, 6), del_p)
        newlive = live_merge(live, la, lb)
        epochs.append((opsA, opsB, newlive))
        live = newlive
        used = [op[1] for op in opsA + opsB if op[0] == 'ins']
        if used: maxid = max(maxid, max(used))
    return {'init': init, 'epochs': epochs, 'stale': None}

def gen_stale_trial(rng, mode, del_p=0.30):
    init = []; live = set()
    for k in range(rng.randint(1, 5)):
        init.append(('ins', k + 1, rng.choice([0] + sorted(live)))); live.add(k + 1)
    maxid = len(init)
    fork_live = set(live)
    epochs = []
    for e in range(rng.randint(1, 3)):
        fa, fb = fresh_ids(mode, e, maxid)
        la, lb = set(live), set(live)
        opsA = gen_branch_ops(rng, la, fa, rng.randint(1, 5), del_p)
        opsB = gen_branch_ops(rng, lb, fb, rng.randint(1, 5), del_p)
        newlive = live_merge(live, la, lb)
        epochs.append((opsA, opsB, newlive))
        live = newlive
        used = [op[1] for op in opsA + opsB if op[0] == 'ins']
        if used: maxid = max(maxid, max(used))
    r3_live = set(fork_live)
    r3ops = []
    if rng.random() < 0.5:
        f3 = ([900001 + 2 * i for i in range(6)] if mode != 'banded'
              else list(range(500000, 500006)))
        r3ops = gen_branch_ops(rng, r3_live, f3, rng.randint(0, 3), del_p)
    final_live = live_merge(fork_live, live, r3_live)
    return {'init': init, 'epochs': epochs,
            'stale': (r3ops, final_live), 'fork_live': fork_live}

# ================================================================ trial runner

def run_trial(impl, trial):
    res = dict(merge_verdicts=[], antisym=[], acyclic=True, liveset_bad=0, sym_bad=0)
    orig, dead = {}, set()
    obs = Obs()
    def do(s, op):
        if op[0] == 'ins':
            orig[op[1]] = op[2]; impl.insert(s, op[1], op[2])
        else:
            dead.add(op[1]); impl.delete(s, op[1])
        obs.display(impl.read(s))
    cur = impl.new()
    for op in trial['init']: do(cur, op)
    fork = impl.clone(cur) if trial['stale'] is not None else None
    for (opsA, opsB, newlive) in trial['epochs']:
        A, B = impl.clone(cur), impl.clone(cur)
        for op in opsA: do(A, op)
        for op in opsB: do(B, op)
        M = impl.merge(cur, A, B)
        if impl.read(impl.merge(cur, B, A)) != impl.read(M): res['sym_bad'] += 1
        rM = impl.read(M)
        obs.display(rM)
        if set(rM) != newlive: res['liveset_bad'] += 1
        else: res['merge_verdicts'].append(classify_merge(rM, obs, orig, dead)[0])
        cur = M
    if trial['stale'] is not None:
        r3ops, final_live = trial['stale']
        R3 = impl.clone(fork)
        for op in r3ops: do(R3, op)
        M = impl.merge(fork, cur, R3)
        if impl.read(impl.merge(fork, R3, cur)) != impl.read(M): res['sym_bad'] += 1
        rM = impl.read(M)
        obs.display(rM)
        if set(rM) != final_live: res['liveset_bad'] += 1
        else: res['merge_verdicts'].append(classify_merge(rM, obs, orig, dead)[0])
        cur = M
    res['antisym'] = obs.antisym_violations()
    res['acyclic'] = obs.acyclic()
    res['cycle'] = None if res['acyclic'] else obs.find_cycle()
    res['final'] = cur; res['dead'] = dead; res['orig'] = orig; res['obs'] = obs
    return res

# ================================================================ column checks

def check_tombfree(impl, n_random=2000):
    """(a) chain probe + randomized delete-heavy trials; report retained deleted ids."""
    s = impl.new(); prev = 0
    for x in range(1, 13): impl.insert(s, x, prev); prev = x
    for x in range(1, 12): impl.delete(s, x)
    chain_ret = sorted(impl.mentions(s) & set(range(1, 12)))
    inc = 0; example = None
    for t in range(n_random):
        rng = random.Random(777000 + t)
        trial = gen_epoch_trial(rng, rng.randint(1, 3),
                                rng.choice(('banded', 'interleaved')), del_p=0.50)
        r = run_trial(impl, trial)
        ret = impl.mentions(r['final']) & r['dead']
        if ret:
            inc += 1
            if example is None: example = (t, sorted(ret)[:6])
    return dict(chain_retained=chain_ret, random_incidents=inc,
                n=n_random, example=example)

def check_bounded(impl, ns=(10, 20, 40)):
    """(b) nested insert-after chain and same-anchor (front) chain, then delete all but
    the last survivor; report max per-node representation size vs n."""
    rows = []
    for n in ns:
        s = impl.new(); prev = 0
        for x in range(1, n + 1): impl.insert(s, x, prev); prev = x
        for x in range(1, n): impl.delete(s, x)
        after = max(impl.meta_sizes(s).values())
        s = impl.new()
        for x in range(1, n + 1): impl.insert(s, x, 0)
        for x in range(1, n): impl.delete(s, x)
        front = max(impl.meta_sizes(s).values())
        rows.append((n, after, front))
    growing = rows[-1][1] > rows[0][1] or rows[-1][2] > rows[0][2]
    return dict(rows=rows, growing=growing)

def gen_linear_ops(rng, nops):
    live, ops, nxt = set(), [], 1
    for _ in range(nops):
        ll = sorted(live)
        if rng.random() < 0.35 and ll:
            x = rng.choice(ll); ops.append(('del', x)); live.discard(x)
        else:
            ops.append(('ins', nxt, rng.choice([0] + ll))); live.add(nxt); nxt += 1
    return ops

def minimal_seq_witness(impl, maxlen=5):
    """Exhaustive BFS over single-replica scripts by length -> genuinely minimal."""
    def run(ops):
        s = impl.new(); ref = []
        for op in ops:
            (impl.insert(s, op[1], op[2]) if op[0] == 'ins' else impl.delete(s, op[1]))
            naive_apply(ref, op)
            if impl.read(s) != ref: return (impl.read(s), list(ref))
        return None
    def extend(ops, live, nxt):
        outs = []
        for a in [0] + sorted(live):
            outs.append((ops + [('ins', nxt, a)], live | {nxt}, nxt + 1))
        for x in sorted(live):
            outs.append((ops + [('del', x)], live - {x}, nxt))
        return outs
    frontier = [([], frozenset(), 1)]
    for L in range(1, maxlen + 1):
        nxt_frontier = []
        for (ops, live, nxt) in frontier:
            for (o2, l2, n2) in extend(ops, set(live), nxt):
                bad = run(o2)
                if bad: return o2, bad
                nxt_frontier.append((o2, frozenset(l2), n2))
        frontier = nxt_frontier
    return None

def check_sequential(impl, n=10000):
    """(c) random single-replica op sequences vs the naive-list fold, checked after
    EVERY op."""
    fails = 0; first = None
    for t in range(n):
        rng = random.Random(31337 + t)
        ops = gen_linear_ops(rng, rng.randint(1, 14))
        s = impl.new(); ref = []
        for op in ops:
            (impl.insert(s, op[1], op[2]) if op[0] == 'ins' else impl.delete(s, op[1]))
            naive_apply(ref, op)
            if impl.read(s) != ref:
                fails += 1
                if first is None: first = (t, ops, impl.read(s), list(ref))
                break
    witness = minimal_seq_witness(impl) if fails else None
    return dict(fails=fails, n=n, first=first, witness=witness)

def build_trials(n_epoch_per_mode, n_stale_per_mode):
    trials = []
    for mi, mode in enumerate(('banded', 'interleaved')):
        for t in range(n_epoch_per_mode):
            rng = random.Random(9000001 + 2 * t + mi)
            trials.append((mode, gen_epoch_trial(rng, rng.randint(1, 3), mode)))
        for t in range(n_stale_per_mode):
            rng = random.Random(5000001 + 2 * t + mi)
            trials.append((mode, gen_stale_trial(rng, mode)))
    return trials

def check_multi(impl, trials):
    """(d)(e)(f) over the shared trial corpus."""
    st = dict(trials=len(trials), merges=0, match=0, licensed=0, violation=0,
              antisym_trials=0, cycle_trials=0, liveset=0, sym=0,
              first_anti=None, first_cycle=None, first_viol=None, first_lic=None)
    for idx, (mode, trial) in enumerate(trials):
        r = run_trial(impl, trial)
        st['merges'] += len(r['merge_verdicts'])
        for v in r['merge_verdicts']: st[v] = st.get(v, 0) + 1
        st['liveset'] += r['liveset_bad']; st['sym'] += r['sym_bad']
        if r['antisym']:
            st['antisym_trials'] += 1
            if st['first_anti'] is None:
                k = r['antisym'][0]
                st['first_anti'] = (idx, mode, k)
        if not r['acyclic']:
            st['cycle_trials'] += 1
            if st['first_cycle'] is None: st['first_cycle'] = (idx, mode, r['cycle'])
        if 'violation' in r['merge_verdicts'] and st['first_viol'] is None:
            st['first_viol'] = (idx, mode)
        if 'licensed' in r['merge_verdicts'] and st['first_lic'] is None:
            st['first_lic'] = (idx, mode)
    return st

def interleave_trial(impl, direction, mode, ctx, la=3, lb=3):
    """(g)(h) one directed trial; returns (ok_contig, ok_order, merged_read, runs)."""
    if ctx == 0: init, anchor = [('ins', 1, 0)], 1
    elif ctx == 1: init, anchor = [('ins', 1, 0), ('ins', 2, 0)], 2   # anchor has successor 1
    else: init, anchor = [('ins', 1, 0), ('ins', 2, 1)], 1            # anchor has child 2
    base = 10
    if mode == 'banded':
        runA = [base + i for i in range(la)]
        runB = [base + 10000 + i for i in range(lb)]
    else:
        runA = [base + 2 * i for i in range(la)]
        runB = [base + 2 * i + 1 for i in range(lb)]
    cur = impl.new()
    for op in init: impl.insert(cur, op[1], op[2])
    A, B = impl.clone(cur), impl.clone(cur)
    for (S, run) in ((A, runA), (B, runB)):
        prev = anchor
        for x in run:
            impl.insert(S, x, prev if direction == 'fwd' else anchor)
            prev = x
    M = impl.merge(cur, A, B)
    rM = impl.read(M)
    def contig(run):
        idx = sorted(rM.index(x) for x in run)
        return idx == list(range(idx[0], idx[0] + len(idx)))
    def order_ok(run):
        sub = [x for x in rM if x in set(run)]
        return sub == (list(run) if direction == 'fwd' else list(run)[::-1])
    return (contig(runA) and contig(runB), order_ok(runA) and order_ok(runB), rM,
            (runA, runB))

def check_interleaving(impl, direction, n_random=2000):
    directed = []
    for mode in ('banded', 'interleaved'):
        for ctx in (0, 1, 2):
            ok_c, ok_o, rM, runs = interleave_trial(impl, direction, mode, ctx)
            directed.append((mode, ctx, ok_c, ok_o, rM, runs))
    fails_rand = 0; first_rand = None
    for t in range(n_random):
        rng = random.Random(60000 + t)
        mode = rng.choice(('banded', 'interleaved'))
        ctx = rng.randint(0, 2)
        la, lb = rng.randint(2, 5), rng.randint(2, 5)
        ok_c, ok_o, rM, runs = interleave_trial(impl, direction, mode, ctx, la, lb)
        if not ok_c:
            fails_rand += 1
            if first_rand is None: first_rand = (t, mode, ctx, rM, runs)
    directed_fail = [d for d in directed if not d[2]]
    return dict(directed=directed, directed_fail=directed_fail,
                fails_rand=fails_rand, n_random=n_random, first_rand=first_rand)

# ================================================================ directed witnesses

def W(impl, script, lca_at=0):
    """Run a two-branch witness: script = (init_ops, opsA, opsB); returns dict with
    all reads + merged read + obs + classification."""
    orig, dead = {}, set()
    obs = Obs()
    def do(s, op):
        if op[0] == 'ins': orig[op[1]] = op[2]; impl.insert(s, op[1], op[2])
        else: dead.add(op[1]); impl.delete(s, op[1])
        obs.display(impl.read(s)); return impl.read(s)
    init_ops, opsA, opsB = script
    Lst = impl.new()
    for op in init_ops: do(Lst, op)
    A, B = impl.clone(Lst), impl.clone(Lst)
    readsA = [do(A, op) for op in opsA]
    readsB = [do(B, op) for op in opsB]
    M = impl.merge(Lst, A, B)
    rM = impl.read(M); obs.display(rM)
    v, pairs = classify_merge(rM, obs, orig, dead)
    return dict(L=impl.read(Lst) if not init_ops else None, readsA=readsA,
                readsB=readsB, merged=rM, oracle=oracle_read(orig, dead),
                verdict=v, pairs=pairs, antisym=obs.antisym_violations(),
                acyclic=obs.acyclic(), cycle=obs.find_cycle(), obs=obs)

def directed_witnesses():
    out = []
    # I2 world 1 through Shesha: strong-list cycle with pairwise antisymmetry intact
    sh = Shesha()
    w = W(sh, ([('ins', 1, 0), ('ins', 2, 0)],                      # L: m=1, g=2
               [('ins', 5, 0), ('del', 2), ('del', 1)],             # A: x=5<-root, del g, del m
               [('ins', 9, 2)]))                                    # B: y=9<-g
    out.append(('Shesha/I2-cycle', w))
    # I1 fooling world 1 through Shesha: licensed oracle divergence
    w = W(sh, ([], [('ins', 5, 0)],
               [('ins', 2, 0), ('ins', 10, 2), ('del', 2)]))
    out.append(('Shesha/I1-licensed', w))
    # FlatTF oracle violation (3 nodes): displayed 2<3 then merge flips
    w = W(FlatTF(), ([('ins', 1, 0), ('ins', 2, 0)],
                     [('ins', 3, 1), ('del', 1)], []))
    out.append(('FlatTF/del-reorder-merge', w))
    # Logoot & Fugue oracle divergence (2 nodes, licensed)
    w = W(Logoot(), ([], [('ins', 10, 0)], [('ins', 11, 0)]))
    out.append(('Logoot/oracle-div', w))
    w = W(Fugue(), ([], [('ins', 10, 0)], [('ins', 11, 0)]))
    out.append(('Fugue/oracle-div', w))
    # StoredPath on the I1 fooling pair (both worlds): does it match the oracle?
    for gts in (2, 6):
        w = W(StoredPath(), ([], [('ins', 5, 0)],
                             [('ins', gts, 0), ('ins', 10, gts), ('del', gts)]))
        out.append((f'StoredPath/I1-world-g{gts}', w))
    return out

# ================================================================ main

def main():
    quick = '--quick' in sys.argv
    N_EPOCH = 500 if quick else 5000
    N_STALE = 100 if quick else 1000
    N_SEQ = 1000 if quick else 10000
    N_RAND_TF = 200 if quick else 2000
    N_RAND_IL = 200 if quick else 2000

    print('=' * 78)
    print('DIRECTED WITNESSES')
    print('=' * 78)
    for name, w in directed_witnesses():
        print(f'\n[{name}]')
        print(f'  reads A: {w["readsA"]}')
        print(f'  reads B: {w["readsB"]}')
        print(f'  merged : {w["merged"]}   oracle: {w["oracle"]}   verdict: {w["verdict"]}')
        if w['pairs']: print(f'  divergent pairs: {w["pairs"]}')
        if w['antisym']: print(f'  PAIRWISE FLIPS: {w["antisym"]}')
        print(f'  acyclic: {w["acyclic"]}' + (f'   CYCLE: {w["cycle"]}' if w['cycle'] else ''))

    trials = build_trials(N_EPOCH, N_STALE)
    print(f'\nshared multi-replica corpus: {len(trials)} trials '
          f'({N_EPOCH} epoch + {N_STALE} stale per mode, modes banded/interleaved)')

    results = {}
    for impl in IMPLS:
        nm = impl.name
        print('\n' + '=' * 78)
        print(f'ROW: {nm}')
        print('=' * 78)
        r = {}
        r['tombfree'] = check_tombfree(impl, N_RAND_TF)
        print(f"[a tombstone-free] chain probe: deleted ids retained -> "
              f"{r['tombfree']['chain_retained'] or 'NONE'};  random delete-heavy: "
              f"{r['tombfree']['random_incidents']}/{r['tombfree']['n']} states retain "
              f"a deleted id (e.g. {r['tombfree']['example']})")
        r['bounded'] = check_bounded(impl)
        print(f"[b bounded meta ] (n, max-size after-chain, front-chain): "
              f"{r['bounded']['rows']}  -> {'GROWING' if r['bounded']['growing'] else 'flat'}")
        r['seq'] = check_sequential(impl, N_SEQ)
        print(f"[c seq = naive  ] fails {r['seq']['fails']}/{r['seq']['n']}")
        if r['seq']['witness']:
            ops, (got, want) = r['seq']['witness']
            print(f"    minimal witness (exhaustive-by-length): {ops}")
            print(f"    got {got}  want {want}")
        r['multi'] = check_multi(impl, trials)
        m = r['multi']
        print(f"[d/e/f multi    ] merges={m['merges']} match={m['match']} "
              f"licensed={m['licensed']} violation={m['violation']} "
              f"liveset_bad={m['liveset']} asym={m['sym']}")
        print(f"    pairwise-flip trials: {m['antisym_trials']}/{m['trials']} "
              f"(first: {m['first_anti']})")
        print(f"    cycle trials        : {m['cycle_trials']}/{m['trials']} "
              f"(first: {m['first_cycle']})")
        for d in ('fwd', 'bwd'):
            r[d] = check_interleaving(impl, d, N_RAND_IL)
            key = 'g fwd-noninter' if d == 'fwd' else 'h bwd-noninter'
            fails = r[d]['directed_fail']
            print(f"[{key}] directed fails: {len(fails)}/6, "
                  f"random fails: {r[d]['fails_rand']}/{r[d]['n_random']}")
            if fails:
                mode, ctx, _, _, rM, runs = fails[0]
                print(f"    witness ({mode}, ctx{ctx}): runA={runs[0]} runB={runs[1]} "
                      f"merged={rM}")
        results[nm] = r
    if FlatTF.resolve_disagreements:
        print(f"\nFlatTF resolve chase A-vs-B disagreements: {FlatTF.resolve_disagreements}")

    # ------------------------------------------------ verdict table
    print('\n' + '=' * 78)
    print('MATRIX (machine-derived verdicts)')
    print('=' * 78)
    hdr = ['design', 'a tomb-free', 'b bounded', 'c seq', 'd pairwise', 'e strong',
           'f oracle', 'g fwd', 'h bwd']
    print(' | '.join(f'{h:12s}' for h in hdr))
    for impl in IMPLS:
        r = results[impl.name]
        tf = 'yes' if (not r['tombfree']['chain_retained']
                       and r['tombfree']['random_incidents'] == 0) else 'NO'
        bd = 'NO' if r['bounded']['growing'] else 'yes'
        sq = 'yes' if r['seq']['fails'] == 0 else 'NO'
        pw = 'yes' if r['multi']['antisym_trials'] == 0 else 'NO'
        sl = 'yes' if r['multi']['cycle_trials'] == 0 else 'NO'
        orc = 'yes' if (r['multi']['licensed'] + r['multi']['violation']) == 0 else \
              ('NO/lic' if r['multi']['violation'] == 0 else 'NO/viol')
        fw = 'yes' if (not r['fwd']['directed_fail'] and r['fwd']['fails_rand'] == 0) else 'NO'
        bw = 'yes' if (not r['bwd']['directed_fail'] and r['bwd']['fails_rand'] == 0) else 'NO'
        print(' | '.join(f'{c:12s}' for c in
                         [impl.name, tf, bd, sq, pw, sl, orc, fw, bw]))

if __name__ == '__main__':
    main()
