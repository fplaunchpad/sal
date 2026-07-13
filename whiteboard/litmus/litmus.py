#!/usr/bin/env python3
"""
Consolidated litmus suite for tombstone-free sequence RDT designs.

Every anomaly that has driven a design decision or refutation in this project,
as ONE executable battery over a fixed adapter interface. Tests are defined
over HISTORIES (scripts of user intentions against a live local replica), not
state encodings, so any implementation exposing {init, apply, read, merge}
runs the entire suite unchanged.

Spec clauses checked (the observable ladder; see README.md):
  S1  sequential soundness      final read == naive-list fold of the script
  S2  step display stability    consecutive reads never flip a surviving pair
  S3  merge convergence         merge(L,A,B) == merge(L,B,A)   (read equality)
  S4  pairwise display stability  no pair displayed by LCA/branch reads flips in the merge
  S5  non-interleaving          given runs stay contiguous, in run order
  S6  list-linearizability      merge read == naive fold of SOME causal interleaving
  S7  strong-list closure       merge read respects the transitive closure of displays
  DUP no duplication            merge read has no repeated element
  IDL idle-branch identity      merge(L, A, L) == A

Deliberately EXCLUDED: RA-linearizability w.r.t. the datatype's OWN fold
(self-referential; it belongs to each design's verification, not to an
implementation-agnostic anomaly matrix — see the spec-limit note in README).

Intentions: ('ins', x, a) = insert fresh id x AFTER element a (a=0: at front),
            ('del', d)    = delete element d.
Ids are Lamport-plausible ints; the id doubles as the timestamp N.

Run:  python3 litmus.py            (matrix to stdout, markdown to litmus_matrix.md)
"""
import sys, os
from itertools import combinations
from fractions import Fraction
from collections import defaultdict

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import sl_pbt  # the rose-tree Shesha reference implementation (design record §4)

# ----------------------------------------------------------------- naive spec
def naive_fold(ops):
    """The sequential list spec (Shesha.lean SeqList totality choices:
    a=0 -> front; absent anchor -> the insert VANISHES; absent delete -> no-op)."""
    doc = []
    for op in ops:
        if op[0] == 'ins':
            _, x, a = op
            if a == 0:
                doc.insert(0, x)
            elif a in doc:
                doc.insert(doc.index(a) + 1, x)
            # else: vanishes
        else:
            _, d = op
            if d in doc:
                doc.remove(d)
    return doc

def pairs_of(doc):
    return {(doc[i], doc[j]) for i in range(len(doc)) for j in range(i + 1, len(doc))}

def step_stable(reads):
    """No consecutive pair of reads flips a common pair."""
    for r1, r2 in zip(reads, reads[1:]):
        p2 = pairs_of(r2)
        for (x, y) in pairs_of(r1):
            if (y, x) in p2:
                return False
    return True

def interleavings(a, b):
    """All order-preserving interleavings of two op lists."""
    n, m = len(a), len(b)
    for apos in combinations(range(n + m), n):
        out, ai, bi = [], 0, 0
        aset = set(apos)
        for k in range(n + m):
            if k in aset:
                out.append(a[ai]); ai += 1
            else:
                out.append(b[bi]); bi += 1
        yield out

def transitive_closure(pairs):
    succ = defaultdict(set)
    for (x, y) in pairs:
        succ[x].add(y)
    changed = True
    while changed:
        changed = False
        for x in list(succ):
            for y in list(succ[x]):
                new = succ[y] - succ[x]
                if new:
                    succ[x] |= new; changed = True
    return {(x, y) for x in succ for y in succ[x]}

# ================================================================== adapters
START, END = 0, -1

class Design:
    tombstone_free = True
    def begin(self): pass                    # per-scenario reset hook
    def fp(self, s): raise NotImplementedError

def successor_of(read_doc, a):
    """Display successor of anchor a (a=0: current first element), else END."""
    if a == 0:
        return read_doc[0] if read_doc else END
    i = read_doc.index(a)
    return read_doc[i + 1] if i + 1 < len(read_doc) else END

# ---- 0. the sequential spec itself (reference column; no merge) -------------
class Naive(Design):
    name = 'naive(spec)'
    def init(self): return []
    def copy(self, s): return list(s)
    def apply(self, s, it):
        return naive_fold([it]) if not s else self._ap(s, it)
    def _ap(self, s, it):
        if it[0] == 'ins':
            _, x, a = it
            if a == 0: s.insert(0, x)
            elif a in s: s.insert(s.index(a) + 1, x)
        else:
            if it[1] in s: s.remove(it[1])
        return s
    def read(self, s): return list(s)
    merge = None
    def fp(self, s): return tuple(s)

# ---- 1. tombstoned RGA (the oracle-faithful baseline) -----------------------
class Tombstoned(Design):
    name = 'tombstoned'
    tombstone_free = False
    def init(self): return {}
    def copy(self, s): return dict(s)
    def apply(self, s, it):
        if it[0] == 'ins':
            _, x, a = it
            s[x] = (a, True)
        else:
            d = it[1]
            if d in s: s[d] = (s[d][0], False)
        return s
    def read(self, s):
        kids = defaultdict(list)
        for x, (a, _) in s.items(): kids[a].append(x)
        for a in kids: kids[a].sort(reverse=True)
        out = []
        def dfs(u):
            for c in kids.get(u, []):
                if s[c][1]: out.append(c)
                dfs(c)
        dfs(0); return out
    def merge(self, L, A, B):
        out = {}
        for src in (L, A, B):
            for k, (a, al) in src.items():
                pa, pal = out.get(k, (a, True))
                out[k] = (a, pal and al)
        return out
    def fp(self, s): return frozenset(s.items())

# ---- 2. flat tombstone-free RGA (the proved RGA_Tombstone_Free shape) -------
class FlatRGA(Design):
    name = 'flat-RGA'
    def init(self): return {}
    def copy(self, s): return dict(s)
    def apply(self, s, it):
        if it[0] == 'ins':
            s[it[1]] = it[2]
        else:
            d = it[1]
            if d in s:
                p = s.pop(d)
                for y in list(s):
                    if s[y] == d: s[y] = p
        return s
    def read(self, s):
        kids = defaultdict(list)
        for x, a in s.items(): kids[a].append(x)
        for a in kids: kids[a].sort(reverse=True)
        out = []
        def dfs(u):
            for c in kids.get(u, []):
                out.append(c); dfs(c)
        dfs(0); return out
    def merge(self, L, A, B):
        surv = (set(L) & set(A) & set(B)) | (set(A) - set(L)) | (set(B) - set(L))
        def anchor(u):
            for S in (L, A, B):
                if u in S: return S[u]
            return 0
        def climb(v):
            while v != 0 and v not in surv: v = anchor(v)
            return v
        return {u: climb(anchor(u)) for u in surv}
    def fp(self, s): return frozenset(s.items())

# ---- 3. rose-tree Shesha (design record §4, via sl_pbt.py) ------------------
class RoseTree(Design):
    name = 'rose(Shesha)'
    def begin(self): sl_pbt.reset()
    def init(self): return sl_pbt.St()
    def copy(self, s): return s.clone()
    def apply(self, s, it):
        if it[0] == 'ins': sl_pbt.insert(s, it[1], it[2])
        else: sl_pbt.delete(s, it[1])
        return s
    def read(self, s): return s.read()
    def merge(self, L, A, B): return sl_pbt.merge(L, A, B)
    def fp(self, s):
        return (frozenset(s.V), frozenset(s.par.items()), frozenset(s.sib.items()))

# ---- 4. symmetric-splice two-tree (REFUTED variant; notes §9) ---------------
class Splice2(Design):
    name = 'splice2'
    def init(self): return {}
    def copy(self, s): return dict(s)
    def apply(self, s, it):
        if it[0] == 'ins':
            _, x, a = it
            doc = self.read(s)
            b = successor_of(doc, a)
            s[x] = (a if a != 0 else START, b)
        else:
            d = it[1]
            if d in s:
                da, db = s.pop(d)
                for y in list(s):
                    ay, by = s[y]
                    if ay == d: ay = da
                    if by == d: by = db
                    s[y] = (ay, by)
        return s
    def read(self, s):
        live = set(s)
        succ = defaultdict(set); indeg = defaultdict(int)
        def edge(u, v):
            if v not in succ[u]: succ[u].add(v); indeg[v] += 1
        for x, (a, b) in s.items():
            edge(a if (a in live or a == START) else START, x)
            edge(x, b if (b in live or b == END) else END)
        for x in live: edge(START, x); edge(x, END)
        order, ready = [], [START]; indeg.setdefault(START, 0)
        while ready:
            ready.sort(key=lambda n: (n == END, n))   # older-id-first ties
            n = ready.pop(0); order.append(n)
            for v in succ[n]:
                indeg[v] -= 1
                if indeg[v] == 0: ready.append(v)
        return [u for u in order if u in live]
    def merge(self, L, A, B):
        surv = (set(L) & set(A) & set(B)) | (set(A) - set(L)) | (set(B) - set(L))
        def field(u):
            for S in (L, A, B):
                if u in S: return S[u]
            return (START, END)
        def climb(v, side):
            while v not in (START, END) and v not in surv:
                v = field(v)[side]
            return v
        return {u: (climb(field(u)[0], 0), climb(field(u)[1], 1)) for u in surv}
    def fp(self, s): return frozenset(s.items())

# ---- 5. bare birth-records + ghost read (B2; today's exploration) -----------
class B2(Design):
    name = 'B2(bare)'
    def init(self): return {}
    def copy(self, s): return dict(s)
    def apply(self, s, it):
        if it[0] == 'ins':
            _, x, a = it
            doc = self.read(s)
            b = successor_of(doc, a)
            s[x] = (a if a != 0 else START, b)
        else:
            s.pop(it[1], None)
        return s
    def read(self, s):
        live = set(s)
        succ = defaultdict(set); indeg = defaultdict(int)
        nodes = set(live) | {v for p in s.values() for v in p if v not in (START, END)}
        def edge(u, v):
            if v not in succ[u]: succ[u].add(v); indeg[v] += 1
        for x, (a, b) in s.items():
            edge(a if a != END else START, x)
            edge(x, b if b != START else END)
        for n in nodes: edge(START, n); edge(n, END)
        order, ready = [], [START]; indeg.setdefault(START, 0)
        while ready:
            ready.sort(key=lambda n: (n == END, n))   # older-id-first ties
            n = ready.pop(0); order.append(n)
            for v in succ[n]:
                indeg[v] -= 1
                if indeg[v] == 0: ready.append(v)
        return [u for u in order if u in live]
    def merge(self, L, A, B):
        surv = (set(L) & set(A) & set(B)) | (set(A) - set(L)) | (set(B) - set(L))
        src = {}
        for S in (L, A, B):
            for k, v in S.items(): src.setdefault(k, v)
        return {u: src[u] for u in surv}
    def fp(self, s): return frozenset(s.items())

# ---- 6. ghost design with carried spines (VALIDATED 0/37k; sibling-origin) --
class Ghost(Design):
    name = 'ghost(spine)'
    def init(self): return {}
    def copy(self, s): return dict(s)
    def apply(self, s, it):
        if it[0] == 'ins':
            _, x, a = it
            doc = self.read(s)
            L = a if a != 0 else START
            R = successor_of(doc, a)
            pL = [L] + (s[L][2] if L in s else [])
            pR = [R] + (s[R][3] if R in s else [])
            s[x] = (L, R, pL, pR)
        else:
            s.pop(it[1], None)
        return s
    def read(self, s):
        succ = defaultdict(set); indeg = defaultdict(int); nodes = {START, END}
        def edge(u, v):
            if v not in succ[u]:
                succ[u].add(v); indeg[v] += 1
            nodes.add(u); nodes.add(v)
        for u, (L, R, pL, pR) in s.items():
            nodes.add(u)
            prev = u
            for g in pL: edge(g, prev); prev = g
            prev = u
            for h in pR: edge(prev, h); prev = h
        order, ready, seen = [], [n for n in nodes if indeg[n] == 0], set()
        while ready:
            if START in ready:
                n = START; ready.remove(START)
            else:
                ready.sort(key=lambda n: (n == END, -n))   # newest-id-first ties
                n = ready.pop(0)
            if n in seen: continue
            seen.add(n); order.append(n)
            for v in succ[n]:
                indeg[v] -= 1
                if indeg[v] == 0: ready.append(v)
        live = set(s)
        return [u for u in order if u in live]
    def merge(self, L, A, B):
        surv = (set(L) & set(A) & set(B)) | (set(A) - set(L)) | (set(B) - set(L))
        src = {}
        for S in (L, A, B):
            for k, v in S.items(): src.setdefault(k, v)
        return {u: src[u] for u in surv}
    def fp(self, s):
        return frozenset((k, v[0], v[1], tuple(v[2]), tuple(v[3])) for k, v in s.items())

# ---- dense position identifiers (Logoot-style) ------------------------------
# A position is a tuple of (digit, uid) pairs, ordered lexicographically.
# The uid sits INSIDE the order, so concurrent picks in one gap are distinct
# positions and the gap between any two positions is never empty (the flaw a
# naive midpoint-Fraction scheme has — caught by test M1).
BIG = 10 ** 18
POS_MIN = ((-BIG, -BIG),)
POS_MAX = ((BIG, BIG),)

def pos_between(a, b, uid):
    """A fresh position strictly between a and b (a < b lex), tagged uid."""
    out = []
    i = 0
    while True:
        da, ua = a[i] if i < len(a) else (-BIG, -BIG)
        db, _ub = b[i] if i < len(b) else (BIG, BIG)
        if db - da >= 2:
            out.append(((da + db) // 2, uid))
            return tuple(out)
        out.append((da, ua))      # follow the lower bound one level down
        i += 1

# ---- 7. Q-flat: immutable (N, Q, char) records, read = sort by Q ------------
class QFlat(Design):
    name = 'Q-flat'
    def init(self): return {}
    def copy(self, s): return dict(s)
    def apply(self, s, it):
        if it[0] == 'ins':
            _, x, a = it
            doc = self.read(s)
            lo = s[a] if a != 0 else POS_MIN
            b = successor_of(doc, a)
            hi = s[b] if b != END else POS_MAX
            s[x] = pos_between(lo, hi, x)
        else:
            s.pop(it[1], None)
        return s
    def read(self, s):
        return [x for x, _ in sorted(s.items(), key=lambda kv: kv[1])]
    def merge(self, L, A, B):
        surv = (set(L) & set(A) & set(B)) | (set(A) - set(L)) | (set(B) - set(L))
        src = {}
        for S in (L, A, B):
            for k, v in S.items(): src.setdefault(k, v)
        return {u: src[u] for u in surv}
    def fp(self, s): return frozenset(s.items())

# ---- 8. Q-tree: RGA tree + bounded sibling keys (instantiation (i)) ---------
class QTree(Design):
    name = 'Q-tree'
    def init(self): return {}
    def copy(self, s): return dict(s)
    def _kids(self, s, p):
        return sorted((x for x in s if s[x][0] == p),
                      key=lambda x: s[x][1], reverse=True)
    def _ub(self, s, a):
        """Position of the nearest newer-sibling boundary up a's ancestor chain."""
        node = a
        while node != 0:
            p = s[node][0]
            newer = [s[y][1] for y in s if s[y][0] == p and s[y][1] > s[node][1]]
            if newer: return min(newer)
            node = p
        return None
    def apply(self, s, it):
        if it[0] == 'ins':
            _, x, a = it
            kids = self._kids(s, a if a != 0 else 0)
            lo = s[a][1] if a != 0 else POS_MIN
            if kids: lo = max(lo, s[kids[0]][1])
            hi = self._ub(s, a) if a != 0 else None
            s[x] = (a if a != 0 else 0, pos_between(lo, hi or POS_MAX, x))
        else:
            d = it[1]
            if d in s:
                p = s.pop(d)[0]
                for y in list(s):
                    if s[y][0] == d: s[y] = (p, s[y][1])
        return s
    def read(self, s):
        out = []
        def dfs(u):
            for c in self._kids(s, u):
                out.append(c); dfs(c)
        dfs(0); return out
    def merge(self, L, A, B):
        surv = (set(L) & set(A) & set(B)) | (set(A) - set(L)) | (set(B) - set(L))
        def rec(u):
            for S in (L, A, B):
                if u in S: return S[u]
            return (0, POS_MIN)
        def climb(v):
            while v != 0 and v not in surv: v = rec(v)[0]
            return v
        return {u: (climb(rec(u)[0]), rec(u)[1]) for u in surv}
    def fp(self, s): return frozenset(s.items())

# ---- 6b. ghost with CHAIN-FOLLOWING tie rule (h-fix experiment) --------------
# Same state as Ghost; the read's Kahn tie prefers a ready node that the
# just-emitted node points to (its own chain continuation), falling back to
# newest-first. Backward runs are R-chains in the records; the plain
# newest-first tie walks across them (fails L19), this one follows them.
class GhostCF(Ghost):
    name = 'ghost-cf'
    def read(self, s):
        from collections import defaultdict as dd
        succ = dd(set); indeg = dd(int); nodes = {START, END}
        def edge(u, v):
            if v not in succ[u]:
                succ[u].add(v); indeg[v] += 1
            nodes.add(u); nodes.add(v)
        for u, (Lo, R, pL, pR) in s.items():
            nodes.add(u)
            prev = u
            for g in pL: edge(g, prev); prev = g
            prev = u
            for h in pR: edge(prev, h); prev = h
        order, ready, seen = [], [n for n in nodes if indeg[n] == 0], set()
        prev = None
        while ready:
            pick = None
            if prev is not None:
                chain = [n for n in ready if n in succ.get(prev, ())]
                if chain:
                    pick = max(chain)
            if pick is None:
                if START in ready: pick = START
                else:
                    ready.sort(key=lambda n: (n == END, -n))
                    pick = ready[0]
            ready.remove(pick)
            if pick in seen: continue
            seen.add(pick); order.append(pick); prev = pick
            for v in succ[pick]:
                indeg[v] -= 1
                if indeg[v] == 0: ready.append(v)
        live = set(s)
        return [u for u in order if u in live]

# ---- 9. path-key: key = ancestor path of (uid) per level, lex sort ----------
# KC's "carve a Q range per node" made concurrency-sound: a range is a PREFIX
# (fixed in the causal past of everything inside it), a key is a path, sort is
# lexicographic with parent-before-children and newest-uid-first per level.
# One-sided (after-paths only) — the StoredPath reference model's shape.
class PathKey(Design):
    name = 'path-key'
    def init(self): return {}
    def copy(self, s): return dict(s)
    def apply(self, s, it):
        if it[0] == 'ins':
            _, x, a = it
            s[x] = (s[a] if a != 0 else ()) + (x,)
        else:
            s.pop(it[1], None)
        return s
    def read(self, s):
        # sort key: (-uid per level); tuple order gives prefix-first + uid-desc
        return sorted(s, key=lambda x: tuple(-u for u in s[x]))
    def merge(self, L, A, B):
        surv = (set(L) & set(A) & set(B)) | (set(A) - set(L)) | (set(B) - set(L))
        src = {}
        for S in (L, A, B):
            for k, v in S.items(): src.setdefault(k, v)
        return {u: src[u] for u in surv}
    def fp(self, s): return frozenset(s.items())

DESIGNS = [Naive(), Tombstoned(), FlatRGA(), RoseTree(), Splice2(),
           B2(), Ghost(), GhostCF(), QFlat(), QTree(), PathKey()]

# ================================================================== driver
def run_replica(D, base, script):
    s = D.copy(base)
    reads = [D.read(s)]
    for it in script:
        s = D.apply(s, it)
        reads.append(D.read(s))
    return s, reads

def seq_verdict(D, script):
    try:
        D.begin()
        s, reads = run_replica(D, D.init(), script)
        s1 = (reads[-1] == naive_fold(script))
        s2 = step_stable(reads)
        return {'S1': s1, 'S2': s2, 'out': reads[-1]}
    except Exception as e:
        return {'ERR': type(e).__name__}

def merge_verdict(D, lca, a_ops, b_ops, runs=None):
    if D.merge is None: return None
    try:
        D.begin()
        Ls, lreads = run_replica(D, D.init(), lca)
        As, areads = run_replica(D, Ls, a_ops)
        Bs, breads = run_replica(D, Ls, b_ops)
        M = D.merge(Ls, As, Bs)
        M2 = D.merge(Ls, Bs, As)
        m = D.read(M)
        v = {'out': m}
        v['S3'] = (m == D.read(M2))
        v['DUP'] = (len(m) == len(set(m)))
        disp = set()
        for r in lreads + areads + breads: disp |= pairs_of(r)
        mp = pairs_of(m)
        v['S4'] = not any((y, x) in mp for (x, y) in disp)
        v['S6'] = any(naive_fold(lca + il) == m for il in interleavings(a_ops, b_ops))
        v['S7'] = not any((y, x) in mp for (x, y) in transitive_closure(disp))
        if runs:
            ok = True
            for run in runs:
                idx = [m.index(u) for u in run if u in m]
                ok &= (idx == sorted(idx) and
                       (not idx or idx == list(range(idx[0], idx[0] + len(idx)))))
            v['S5'] = ok
        # idle-branch identity on the same scenario shape
        D.begin()
        Ls, _ = run_replica(D, D.init(), lca)
        As, _ = run_replica(D, Ls, a_ops)
        v['IDL'] = (D.read(D.merge(Ls, As, D.copy(Ls))) == D.read(As))
        return v
    except Exception as e:
        return {'ERR': type(e).__name__}

def two_world_seq(D, w1, w2):
    r1 = seq_verdict(D, w1)
    r2 = seq_verdict(D, w2)
    ident = None
    try:
        D.begin(); s1, _ = run_replica(D, D.init(), w1)
        D.begin(); s2, _ = run_replica(D, D.init(), w2)
        ident = (D.fp(s1) == D.fp(s2))
    except Exception:
        pass
    return {'W1': r1, 'W2': r2, 'identical_states': ident}

def two_world_merge(D, lca, branch_fixed, worlds, required, fooled_state):
    """worlds: {'W1': varying_ops, 'W2': ...} for the varying branch.
    fooled_state: 'A' or 'B' — which branch's final state to fingerprint."""
    if D.merge is None: return None
    out = {}
    fps = {}
    try:
        for w, var_ops in worlds.items():
            D.begin()
            Ls, _ = run_replica(D, D.init(), lca)
            if fooled_state == 'B':
                As, _ = run_replica(D, Ls, branch_fixed)
                Bs, _ = run_replica(D, Ls, var_ops)
                fps[w] = D.fp(Bs)
            else:
                As, _ = run_replica(D, Ls, var_ops)
                Bs, _ = run_replica(D, Ls, branch_fixed)
                fps[w] = D.fp(As)
            out[w] = D.read(D.merge(Ls, As, Bs))
        return {'outs': out,
                'identical_inputs': fps['W1'] == fps['W2'],
                'meets': {w: (out[w] == required[w]) for w in worlds}}
    except Exception as e:
        return {'ERR': type(e).__name__}

def post_merge_verdict(D, lca, a_ops, b_ops, post):
    """Merge, then apply `post` ops on the merged replica; check that no pair
    the merged replica itself displayed ever flips (S2 over the post reads)."""
    if D.merge is None: return None
    try:
        D.begin()
        Ls, _ = run_replica(D, D.init(), lca)
        As, _ = run_replica(D, Ls, a_ops)
        Bs, _ = run_replica(D, Ls, b_ops)
        M = D.merge(Ls, As, Bs)
        reads = [D.read(M)]
        for it in post:
            M = D.apply(M, it)
            reads.append(D.read(M))
        return {'out': reads[-1], 'S2': step_stable(reads), 'merged': reads[0]}
    except Exception as e:
        return {'ERR': type(e).__name__}

def multi_epoch_verdict(D, lca, a1, b1, c2, d2):
    if D.merge is None: return None
    try:
        D.begin()
        Ls, lr = run_replica(D, D.init(), lca)
        As, ar = run_replica(D, Ls, a1)
        Bs, br = run_replica(D, Ls, b1)
        M1 = D.merge(Ls, As, Bs)
        conv1 = (D.read(M1) == D.read(D.merge(Ls, Bs, As)))
        Cs, cr = run_replica(D, M1, c2)
        Ds, dr = run_replica(D, M1, d2)
        M2 = D.merge(M1, Cs, Ds)
        m = D.read(M2)
        conv2 = (m == D.read(D.merge(M1, Ds, Cs)))
        disp = set()
        for r in lr + ar + br + [D.read(M1)] + cr + dr: disp |= pairs_of(r)
        mp = pairs_of(m)
        s4 = not any((y, x) in mp for (x, y) in disp)
        s6 = any(naive_fold(lca + il1 + il2) == m
                 for il1 in interleavings(a1, b1)
                 for il2 in interleavings(c2, d2))
        return {'out': m, 'S3': conv1 and conv2, 'S4': s4, 'S6': s6,
                'DUP': len(m) == len(set(m))}
    except Exception as e:
        return {'ERR': type(e).__name__}

# ================================================================== scenarios
I, DL = (lambda x, a: ('ins', x, a)), (lambda d: ('del', d))

SEQ_TESTS = [
    ('L1 delete-reorder', 'S1,S2', [I(1,0), I(2,0), I(3,1), DL(1)]),
    ('L3a chain(front) del-run', 'S1,S2',
     [I(1,0), I(2,0), I(3,0), I(4,0), I(5,0), DL(2), DL(3), DL(4)]),
    ('L3b chain(after) del-run', 'S1,S2',
     [I(1,0), I(2,1), I(3,2), I(4,3), I(5,4), DL(2), DL(3), DL(4)]),
    # L17: a deep chain is built under an OPEN ceiling (all heads), then a new
    # head arrives whose key floor sees only the old head, then the chain is
    # deleted: eagerly-assigned deep keys can exceed the new head's key and the
    # rehome re-sort flips a co-displayed pair. Found 2026-07-13 during the
    # pen-and-paper attempt at Q-tree's nesting invariant (not by the battery).
    ('L17 ceiling escape (seq)', 'S1,S2',
     [I(1,0), I(2,1), I(3,2), I(4,3), I(5,1), DL(2), DL(3)]),
]

L2 = ('L2 splice fooling pair',
      [I(1,0), I(2,0), I(3,1), DL(1)],       # W1: naive [2,3]
      [I(1,0), I(2,1), I(3,0), DL(1)])       # W2: naive [3,2]

MERGE_TESTS = [
    ('L4 criss-cross split', [I(1,0)], [I(2,1), I(4,0), DL(1)], [I(3,1)], None),
    ('L5 ins||del anchor',   [I(1,0)], [I(2,1)], [DL(1)], None),
    ('L7 concurrent runs',   [I(1,0)], [I(10,1), I(11,10)], [I(20,1), I(21,20)],
     [[10,11],[20,21]]),
    # L19: BACKWARD runs (matrix column h): each user repeatedly inserts at the
    # front (each element before the previous), interleaved Lamport ids.
    # A displays [50,30,10,1], B displays [61,41,21,1]; the runs must stay blocks.
    # Added 2026-07-13 — the battery previously had no h test (gap found while
    # assessing the path-key/range proposal).
    ('L19 backward runs (h)', [I(1,0)], [I(10,0), I(30,0), I(50,0)],
     [I(21,0), I(41,0), I(61,0)], [[50,30,10],[61,41,21]]),
    ('L8 T2 dual markers',   [I(2,0), I(3,0)], [I(10,3), DL(3)], [I(20,2), DL(2)], None),
    ('L9 w-slot',            [I(2,0), I(3,0)], [I(4,0)], [I(6,3), DL(3)], None),
    ('L10 attach-deep',      [I(1,0), I(2,1)], [I(10,2), DL(1)], [I(20,1)], None),
    ('L11 head jump-back',   [I(1,0), I(2,1)], [I(10,0), DL(1)], [I(20,2)], None),
    ('L12 leapfrog',         [I(1,0), I(2,1)], [DL(1)], [I(3,2)], None),
    ('L13 puncture',         [I(1,0), I(2,1), I(3,2)], [DL(2), I(4,1)], [I(5,2)], None),
    ('L16 concurrent del',   [I(1,0), I(2,1)], [DL(1)], [DL(1), I(10,2)], None),
]

L14 = ('L14 oracle fooling (4-node)',
       [],                       # lca
       [I(5,0)],                 # fixed branch A
       {'W1': [I(2,0), I(10,2), DL(2)],   # varying branch B, g=2
        'W2': [I(6,0), I(10,6), DL(6)]},  # g=6
       {'W1': [5,10], 'W2': [10,5]},      # tombstoned-oracle answers
       'B')

L15 = ('L15 strong-list (5-node)',
       [I(1,0), I(2,0)],         # lca: reads [2,1]
       [I(9,2)],                 # fixed branch B: y·9 after g·2
       {'W1': [I(5,0), DL(2), DL(1)],     # x·5 at front
        'W2': [I(5,1), DL(1), DL(2)]},    # x·5 after m·1
       {'W1': [5,9], 'W2': [9,5]},
       'A')

M1 = ('M1 two epochs', [I(1,0)], [I(2,1)], [I(3,1)], [DL(2)], [I(4,3)])

# L18: the CONCURRENT ceiling escape. Branch B extends a deep chain under an
# open ceiling while branch A concurrently inserts a new head whose key floor
# cannot see B's keys; after the merge the pair IS co-displayed, and deleting
# the chain re-sorts the escaped deep key above the head: a d-violation on the
# merged replica itself. No birth-time floor can prevent it (B cannot see A).
# Found on paper 2026-07-13; passes for lazy/relational orders (ghost, rose)
# and for flat keys (delete never re-sorts); fails for eager keys + splice.
L18 = ('L18 merge-then-delete collapse',
       [I(1,0), I(2,1), I(3,2), I(4,3)],      # lca: chain, all heads
       [I(5,1)],                              # A: new head after 1
       [I(6,4), I(7,6)],                      # B: deepen the chain
       [DL(2), DL(3), DL(4), DL(6)])          # applied ON THE MERGED replica

# ================================================================== report
def flag(v, keys):
    if 'ERR' in v: return 'ERR:' + v['ERR']
    marks = ''.join(('✓' if v[k] else '✗') for k in keys if k in v)
    return marks + ' ' + ''.join(map(str, v['out'])) if 'out' in v else marks

def main():
    md = ['# Litmus matrix (generated by litmus.py — do not edit)\n']
    def emit(line=''):
        print(line); md.append(line)

    emit('== SEQUENTIAL (S1 soundness, S2 step-stability) ==')
    emit('| test | ' + ' | '.join(D.name for D in DESIGNS) + ' |')
    emit('|---|' + '---|' * len(DESIGNS))
    for name, _, script in SEQ_TESTS:
        cells = []
        for D in DESIGNS:
            v = seq_verdict(D, script)
            cells.append(flag(v, ['S1', 'S2']))
        emit(f'| {name} | ' + ' | '.join(cells) + ' |')

    name, w1, w2 = L2
    emit()
    emit(f'== {name} (both worlds must be S1-sound; identical states ⇒ provably fooled) ==')
    emit('| design | W1 (want 23) | W2 (want 32) | states identical? |')
    emit('|---|---|---|---|')
    for D in DESIGNS:
        r = two_world_seq(D, w1, w2)
        c1 = flag(r['W1'], ['S1']); c2 = flag(r['W2'], ['S1'])
        emit(f'| {D.name} | {c1} | {c2} | {r["identical_states"]} |')

    emit()
    emit('== MERGE (S3 conv, S4 stability, S6 list-lin, S7 strong-list, DUP, IDL[, S5]) ==')
    for name, lca, a, b, runs in MERGE_TESTS:
        emit(f'-- {name} --')
        emit('| design | S3 | S4 | S6 | S7 | DUP | IDL | S5 | merge read |')
        emit('|---|---|---|---|---|---|---|---|---|')
        for D in DESIGNS:
            v = merge_verdict(D, lca, a, b, runs)
            if v is None: continue
            if 'ERR' in v:
                emit(f'| {D.name} | ERR:{v["ERR"]} ||||||||')
                continue
            def m(k): return ('✓' if v[k] else '✗') if k in v else '—'
            emit(f'| {D.name} | {m("S3")} | {m("S4")} | {m("S6")} | {m("S7")} | '
                 f'{m("DUP")} | {m("IDL")} | {m("S5")} | {v["out"]} |')

    for name, lca, fixed, worlds, req, side in (L14, L15):
        emit()
        emit(f'== {name} (impossibility probe; identical inputs ⇒ provably fooled) ==')
        emit(f'   required: W1 {req["W1"]}  W2 {req["W2"]}')
        emit('| design | inputs identical? | W1 out (meets?) | W2 out (meets?) |')
        emit('|---|---|---|---|')
        for D in DESIGNS:
            r = two_world_merge(D, lca, fixed, worlds, req, side)
            if r is None: continue
            if 'ERR' in r:
                emit(f'| {D.name} | ERR:{r["ERR"]} |||')
                continue
            emit(f'| {D.name} | {r["identical_inputs"]} | '
                 f'{r["outs"]["W1"]} ({"✓" if r["meets"]["W1"] else "✗"}) | '
                 f'{r["outs"]["W2"]} ({"✓" if r["meets"]["W2"] else "✗"}) |')

    emit()
    name, lca, a, b, post = L18
    emit(f'== {name} (S2 over the merged replica: co-displayed pairs must survive its own deletes) ==')
    emit('| design | S2(post) | merged read | after deletes |')
    emit('|---|---|---|---|')
    for D in DESIGNS:
        v = post_merge_verdict(D, lca, a, b, post)
        if v is None: continue
        if 'ERR' in v:
            emit(f'| {D.name} | ERR:{v["ERR"]} |||')
            continue
        emit(f'| {D.name} | {"✓" if v["S2"] else "✗"} | {v["merged"]} | {v["out"]} |')

    emit()
    name, lca, a1, b1, c2, d2 = M1
    emit(f'== {name} (S3, S4, S6 across chained merges) ==')
    emit('| design | S3 | S4 | S6 | DUP | out |')
    emit('|---|---|---|---|---|---|')
    for D in DESIGNS:
        v = multi_epoch_verdict(D, lca, a1, b1, c2, d2)
        if v is None: continue
        if 'ERR' in v:
            emit(f'| {D.name} | ERR:{v["ERR"]} |||||')
            continue
        def m(k): return '✓' if v[k] else '✗'
        emit(f'| {D.name} | {m("S3")} | {m("S4")} | {m("S6")} | {m("DUP")} | {v["out"]} |')

    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           'litmus_matrix.md'), 'w') as f:
        f.write('\n'.join(md) + '\n')

if __name__ == '__main__':
    main()
