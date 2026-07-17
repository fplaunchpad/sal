#!/usr/bin/env python3
"""
fuguemax_check.py -- the FugueMax variant of the sided embed, task #87 part (a).

Paper: Weidner & Kleppmann, "The Art of the Fugue" (arXiv:2305.00583v3),
Definition 6: FugueMax is identical to Fugue except that its tree traversal
visits right-side siblings in the REVERSE order of their right origins,
breaking ties by ascending ID. Left-side siblings stay in ascending ID
order (Fugue's rule). Theorem 9: FugueMax satisfies all three conditions
of Definition 4 (maximal non-interleaving).

Realization on the sided embed (design note section appended to
whiteboard/fugue-maximal-noninterleaving.md):

  * The same-anchor R-sibling order CANNOT be realized by re-banding the
    delta alphabet alone: it depends on the right origin, which is not a
    function of (side, delta). The 'mirror' control below (R band flipped
    to oldest-first, no right-origin tag = the paper's plain Fugue) fails
    condition (2) on the adverse-ID Figure-7 trace, machine-witnessed.
  * The FugueMax variant therefore enriches the R-band ENTRY: an R entry
    carries an immutable right-origin tag (the mint-time sort key of the
    tombstone-visible successor; the smallest tag for 'end'), and the
    R-sibling comparison is: smaller tag first (= reverse display order of
    the right origins, since display-later means smaller key), ties by
    ascending stamp. The L band is unchanged (already ascending-ID).

Expectations, stated up front:

  * FugueMax is NOT RGA-ordered: the all-R recency order is gone, so
    lockstep with the one-sided embed (the 'rga' policy's row) MUST fail;
    a concrete mismatch is printed. This is by design, not a bug.
  * The embed_sided gauntlet should otherwise pass (S1/S2 sequential rows:
    sequentially the tombstone-visible successor rule never creates
    same-side siblings, so FugueMax = Fugue = the naive buffer; S3/S4/S6/
    DUP/IDL/S5 are convergence/stability clauses that only need a
    deterministic total order on immutable coordinates).
  * The three W-K conditions (strict reading) and the run check: ALL CLEAN
    on every directed case and every randomized sweep. Any violation is a
    first-class result.

Run: python3 fuguemax_check.py [N]     (default N = 500 per sweep shape)
"""
import sys
from random import Random
import litmus as L
from embed_sided import SidedChain, gauntlet, mkD
from embed_tree import EmbedTreeCode
from fugue_noninterleave_check import check_wk, check_runs, FugueOrigins

R, LFT = 'R', 'L'
I = lambda x, a: ('ins', x, a)
DL = lambda d: ('del', d)


class Rev:
    """Order-reversing wrapper: Rev(a) < Rev(b) iff b < a. Used for the
    right-origin tag so that a display-later (smaller-key) right origin
    yields a display-earlier (larger-atom) sibling."""
    __slots__ = ('v',)

    def __init__(self, v):
        self.v = v

    def __eq__(self, o):
        return isinstance(o, Rev) and self.v == o.v

    def __lt__(self, o):
        return o.v < self.v

    def __hash__(self):
        return hash(('Rev', self.v))

    def __repr__(self):
        return f'Rev({self.v!r})'


END = ()          # the 'end' right origin: the lex-smallest tag


# ============================================================ the variant
class FugueMaxChain(SidedChain):
    """The sided embed with FugueMax coordinates: R entries carry the
    mint-time key of the right origin; R siblings sort by (reverse right
    origin, ascending stamp); L entries unchanged (ascending stamp).
    Entry shapes: ('R', t, roKey) and ('L', t)."""
    name = 'fuguemax-chain'
    policy = 'fuguemax'

    def __init__(self):
        self.origins = {}

    def begin(self):
        self.origins = {}

    @staticmethod
    def key(chain):
        k = []
        for e in chain:
            if e[0] == R:
                k.append((1, Rev(e[2]), -e[1]))
            else:
                k.append((3, -e[1]))
        k.append((2, 0))
        return tuple(k)

    def apply(self, s, it):
        live, chains, tree = s
        if it[0] == 'ins':
            _, x, a = it
            # the tombstone-visible successor of a (a = 0: start)
            order = sorted(chains.keys(), key=lambda y: self.key(chains[y]),
                           reverse=True)
            if a == 0:
                n = order[0] if order else None
            else:
                i = order.index(a)
                n = order[i + 1] if i + 1 < len(order) else None
            self.origins[x] = (a, n)
            has_r = any(sd == R and p == a for (sd, p) in tree.values())
            if not has_r or n is None:
                side, parent = R, a
                rokey = self.key(chains[n]) if n is not None else END
                entry = (R, x, rokey)
            else:
                side, parent = LFT, n
                entry = (LFT, x)
            chains[x] = chains.get(parent, ()) + (entry,)
            tree[x] = (side, parent)
            live.add(x)
        else:
            live.discard(it[1])
        return s


# ============================================================ the control
class MirrorOrigins(SidedChain):
    """The CONTROL: R band flipped to oldest-first (ascending ID), no
    right-origin tag -- this is the paper's PLAIN Fugue (same-side siblings
    in ascending ID order on both sides). Expected to fail condition (2)
    on the adverse-ID Figure-7 trace: re-banding alone is not FugueMax."""
    name = 'mirror-chain'
    policy = 'fugue'

    def __init__(self):
        self.origins = {}

    def begin(self):
        self.origins = {}

    @staticmethod
    def key(chain):
        k = [(1, -t) if side == R else (3, -t) for side, t in chain]
        k.append((2, 0))
        return tuple(k)

    def apply(self, s, it):
        if it[0] == 'ins':
            _, x, a = it
            live, chains, tree = s
            order = sorted(chains.keys(), key=lambda y: self.key(chains[y]),
                           reverse=True)
            if a == 0:
                n = order[0] if order else None
            else:
                i = order.index(a)
                n = order[i + 1] if i + 1 < len(order) else None
            self.origins[x] = (a, n)
        return super().apply(s, it)


# ============================================================ directed cases
def fig7(D, adverse=False):
    """The paper's Figure-7 execution, IDs chosen ascending (A=3 < B=4 <
    C=5) so the paper's desired order A X Y B C is the ascending-ID-
    compatible one. adverse=True mints Y before X (Y=6 < X=7): plain
    Fugue then orders Y first and violates condition (2); FugueMax must
    still order X first."""
    D.begin()
    e = D.init()
    sA, _ = L.run_replica(D, e, [I(3, 0)])
    sB, _ = L.run_replica(D, e, [I(4, 0)])
    sC, _ = L.run_replica(D, e, [I(5, 0)])
    r1 = D.merge(e, D.copy(sA), sC)                  # r1 knows {A=3, C=5}
    r2 = D.merge(e, D.copy(sB), D.copy(sA))          # r2 knows {A=3, B=4}
    if adverse:
        r2, _ = L.run_replica(D, r2, [I(6, 3)])      # Y=6 between A and B
        r1, _ = L.run_replica(D, r1, [I(7, 3)])      # X=7 between A and C
    else:
        r1, _ = L.run_replica(D, r1, [I(6, 3)])      # X=6 between A and C
        r2, _ = L.run_replica(D, r2, [I(7, 3)])      # Y=7 between A and B
    return D.merge(sA, r1, r2)                       # LCA of r1, r2 is {A}


def directed_cases():
    out = []

    def merge_case(name, lca, branches, runs, expect_doc):
        D = FugueMaxChain()
        D.begin()
        Ls, _ = L.run_replica(D, D.init(), lca)
        sts = [L.run_replica(D, Ls, b)[0] for b in branches]
        m = sts[0]
        for s2 in sts[1:]:
            m = D.merge(Ls, m, s2)
        vs = check_wk(D, m, strict=True)
        vl = check_wk(D, m, strict=False)
        vr = check_runs(D, m, runs) if runs else []
        out.append((name, vs, vl, vr, D.read(m), expect_doc))

    # 1. two concurrent front inserts: FugueMax ties ascending -> [1, 2]
    merge_case('two-front-inserts', [], [[I(1, 0)], [I(2, 0)]], None, [1, 2])

    # 2. L19 backward twin: L band unchanged, same display as Fugue
    merge_case('L19 backward', [I(1, 0)],
               [[I(10, 0), I(30, 0), I(50, 0)], [I(21, 0), I(41, 0), I(61, 0)]],
               [[50, 30, 10], [61, 41, 21]],
               [50, 30, 10, 61, 41, 21, 1])

    # 3. forward twin: run heads tie on ro=end -> ascending: 10's block first
    merge_case('forward twin', [I(1, 0)],
               [[I(10, 1), I(30, 10), I(50, 30)],
                [I(21, 1), I(41, 21), I(61, 41)]],
               [[10, 30, 50], [21, 41, 61]],
               [1, 10, 30, 50, 21, 41, 61])

    # 4. mixed: backward run (fixed anchor 1) vs forward run
    merge_case('mixed fwd/bwd', [I(1, 0)],
               [[I(10, 1), I(30, 1), I(50, 1)],
                [I(21, 1), I(41, 21), I(61, 41)]],
               [[50, 30, 10], [21, 41, 61]],
               [1, 50, 30, 10, 21, 41, 61])

    # 5. strict-vs-lenient C1 countermodel, adapted to ascending ties: the
    # DEAD sibling must be the OLDER one to sit first. Expected: strict
    # clean, lenient C1 fires on (1, 5).
    merge_case('lenient-C1 countermodel', [I(1, 0)],
               [[I(5, 1)], [I(2, 1), I(9, 2), DL(2)]],
               None, [1, 9, 5])

    # 6. Figure 7, natural mint order (X=6 before Y=7)
    D = FugueMaxChain()
    m = fig7(D, adverse=False)
    out.append(('figure 7 (W-K)', check_wk(D, m, True), check_wk(D, m, False),
                [], D.read(m), [3, 6, 7, 4, 5]))

    # 7. Figure 7, ADVERSE mint order (Y=6 before X=7): the case that kills
    # both plain re-bandings; FugueMax must still produce A X Y B C.
    D = FugueMaxChain()
    m = fig7(D, adverse=True)
    out.append(('figure 7 adverse', check_wk(D, m, True), check_wk(D, m, False),
                [], D.read(m), [3, 7, 6, 4, 5]))
    return out


# ============================================================ random cases
def random_run_scenario(rng, mkdesign, three=False, second_epoch=False):
    """Randomized concurrent-run scenario (port of
    fugue_noninterleave_check.random_run_scenario, parametric in the
    design class)."""
    D = mkdesign()
    D.begin()
    nid = [1]

    def fresh():
        x = nid[0]
        nid[0] += 1
        return x

    def rand_ops(st, k, p_del=0.25):
        ops = []
        s = D.copy(st)
        for _ in range(k):
            doc = D.read(s)
            if doc and rng.random() < p_del:
                op = DL(rng.choice(doc))
            else:
                a = rng.choice([0] + doc) if doc else 0
                op = I(fresh(), a)
            s = D.apply(s, op)
            ops.append(op)
        return s, ops

    def run_ops(st, n):
        doc = D.read(st)
        a = rng.choice([0] + doc) if doc else 0
        kind = rng.choice(['fwd', 'bwd'])
        ops, run = [], []
        prev = a
        for _ in range(n):
            x = fresh()
            ops.append(I(x, prev if kind == 'fwd' else a))
            run.append(x)
            prev = x
        s = D.copy(st)
        for op in ops:
            s = D.apply(s, op)
        text = run if kind == 'fwd' else list(reversed(run))
        return s, text

    Ls, _ = rand_ops(D.init(), rng.randint(0, 3))
    nb = 3 if three else 2
    branches, runs = [], []
    for _ in range(nb):
        s, text = run_ops(Ls, rng.randint(2, 4))
        branches.append(s)
        runs.append(text)
    if not second_epoch:
        m = branches[0]
        for s2 in branches[1:]:
            m = D.merge(Ls, m, s2)
        return D, m, runs, {}
    A, B, C = branches
    r1 = D.merge(Ls, D.copy(A), D.copy(C))
    r1, t1 = run_ops(r1, rng.randint(1, 3))
    r2 = D.merge(Ls, D.copy(B), D.copy(A))
    r2, t2 = run_ops(r2, rng.randint(1, 3))
    m = D.merge(A, r1, r2)
    return D, m, runs + [t1, t2], {3: {0, 2}, 4: {0, 1}}


def same_origin_same_branch(D, state):
    """The structural lemma behind condition (3)'s Lean proof: two minted
    elements with the SAME recorded (lo, ro) were minted in the SAME policy
    branch (same side, same tree parent). Returns violating pairs."""
    _, chains, tree = state
    bad = []
    xs = [x for x in chains if x in D.origins]
    for i, x in enumerate(xs):
        for y in xs[i + 1:]:
            if D.origins[x] == D.origins[y] and tree[x] != tree[y]:
                bad.append((x, y, tree[x], tree[y]))
    return bad


def sweep(n, seed0, mkdesign, **kw):
    stats = {'C1': 0, 'C2': 0, 'C3': 0, 'RUN': 0, 'C1len': 0, 'MIX': 0}
    first = {}
    for e in range(n):
        rng = Random(seed0 * 99991 + e)
        D, m, runs, seen = random_run_scenario(rng, mkdesign, **kw)
        for v in check_wk(D, m, strict=True):
            stats[v[0]] += 1
            first.setdefault(v[0], (e, v))
        for v in check_wk(D, m, strict=False):
            if v[0] == 'C1':
                stats['C1len'] += 1
                first.setdefault('C1len', (e, v))
        for v in check_runs(D, m, runs, seen):
            stats['RUN'] += 1
            first.setdefault('RUN', (e, v))
        for v in same_origin_same_branch(D, m):
            stats['MIX'] += 1
            first.setdefault('MIX', (e, v))
    return stats, first


if __name__ == '__main__':
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 500

    print('==== the gauntlet (embed_sided battery) ====')
    D = FugueMaxChain()
    bad = gauntlet(D, expect_l19_clean=True)
    print(f'  {D.name:22} gauntlet: {"CLEAN" if not bad else "FAIL"}')
    for b in bad:
        print(f'      {b}')

    print('==== NOT RGA-ordered (expected, by design) ====')
    # the forward twin: the one-sided embed (recency) puts the newer block
    # first; FugueMax puts the lower-ID block first.
    E = EmbedTreeCode()
    E.begin()
    lca, a_ops, b_ops = [I(1, 0)], [I(10, 1), I(30, 10), I(50, 30)], \
        [I(21, 1), I(41, 21), I(61, 41)]
    Ls, _ = L.run_replica(E, E.init(), lca)
    As, _ = L.run_replica(E, Ls, a_ops)
    Bs, _ = L.run_replica(E, Ls, b_ops)
    r_embed = E.read(E.merge(Ls, As, Bs))
    D = FugueMaxChain()
    D.begin()
    Ls, _ = L.run_replica(D, D.init(), lca)
    As, _ = L.run_replica(D, Ls, a_ops)
    Bs, _ = L.run_replica(D, Ls, b_ops)
    r_max = D.read(D.merge(Ls, As, Bs))
    print(f'  one-sided embed : {r_embed}')
    print(f'  fuguemax        : {r_max}')
    print(f'  lockstep with the RGA order: '
          f'{"HOLDS (unexpected!)" if r_embed == r_max else "FAILS, as expected"}')

    print('==== directed cases (hand-derived expectations) ====')
    for name, vs, vl, vr, doc, expect in directed_cases():
        okdoc = 'doc OK' if doc == expect else f'DOC MISMATCH exp={expect}'
        print(f'  {name:26} out={doc}  [{okdoc}]')
        print(f'      strict: {[v[:3] for v in vs] if vs else "CLEAN"}')
        if [v[:3] for v in vl] != [v[:3] for v in vs]:
            print(f'      lenient extra: {[v[:3] for v in vl]}')
        if vr:
            print(f'      RUN violations: {vr}')

    print('==== the control: plain re-banding is NOT FugueMax ====')
    D = MirrorOrigins()
    m = fig7(D, adverse=True)
    vs = check_wk(D, m, strict=True)
    print(f'  mirror (oldest-first R band = paper plain Fugue), '
          f'adverse fig-7: out={D.read(m)}')
    print(f'      strict: {[v[:3] for v in vs] if vs else "CLEAN (unexpected!)"}')

    print('==== randomized sweeps (FugueMax, strict reading) ====')
    for tag, seed0, kw in (('2-branch runs', 1, {}),
                           ('3-branch runs', 2, {'three': True}),
                           ('3-branch two-epoch (fig-7 shaped)', 3,
                            {'three': True, 'second_epoch': True})):
        stats, first = sweep(N, seed0, FugueMaxChain, **kw)
        print(f'  {tag:36} n={N}  '
              f"C1={stats['C1']} C2={stats['C2']} C3={stats['C3']} "
              f"RUN={stats['RUN']} MIX={stats['MIX']}  "
              f"[lenient C1={stats['C1len']}]")
        for k in ('C1', 'C2', 'C3', 'RUN', 'MIX', 'C1len'):
            if k in first:
                e, v = first[k]
                print(f'      first {k}: case {e}: {v}')

    print('==== DAG PBT (convergence) ====')
    import pbt
    f, _ = pbt.sweep(FugueMaxChain(), 120)
    print(f'  fuguemax-chain PBT 120: '
          f'{"CLEAN" if not f else str(len(f)) + " FAIL, first " + str(f[0])}')
