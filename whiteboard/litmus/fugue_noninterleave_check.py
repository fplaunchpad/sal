#!/usr/bin/env python3
"""
fugue_noninterleave_check.py -- the Weidner-Kleppmann (maximal)
non-interleaving statement as an executable predicate over the sided embed
under the Fugue side-selection policy.  Task #84 stage 2; the paper is
"The Art of the Fugue" (arXiv:2305.00583v3), Definitions 2 and 4, Lemma 5.
Companion design note: whiteboard/fugue-maximal-noninterleaving.md.

What is checked, per final (merged) state:

  C1  forward non-interleaving (Def 4, condition 1): if A is the left origin
      of B and B is earliest among elements with left origin A, then A and B
      are consecutive list elements.
  C2  backward non-interleaving with the Lemma-5 exception (condition 2):
      if B is the right origin of A and A is latest among elements with
      right origin B, then A and B are consecutive, unless (i) A and B have
      different left origins and (ii) some live C with A.leftOrigin < C < B
      is not a descendant of A.leftOrigin in the left-origin tree.
  C3  same-origin tiebreak (condition 3): same left origin and same right
      origin implies the lower id displays earlier.
  RUN candidate (a): every generated run's survivors form one contiguous
      display block, in run text order (the litmus S5 clause, re-checked
      here for the run scenarios).

Two readings of the Def-4 comparison quantifier are implemented:

  strict  : "any other element that has A as left origin" ranges over ALL
            inserted elements, tombstones included, compared in the
            underlying strong-list total order (the key order).  This is
            the reading the paper's Theorem-9 proof requires.
  lenient : the quantifier ranges over live elements only.  This reading is
            FALSIFIABLE for every Fugue-family algorithm (a dead newest
            sibling with a live descendant sits between A and the earliest
            live element with left origin A); the directed countermodel
            below witnesses it.

Left/right origins are recorded at generation time exactly as the policy
computes them: left origin = the intent anchor (0 = start), right origin =
the tombstone-visible successor of the anchor in the local order over all
minted nodes (None = end).

Run: python3 fugue_noninterleave_check.py
"""
import sys
from random import Random
import litmus as L
from embed_sided import SidedChain

R, LFT = 'R', 'L'
I = lambda x, a: ('ins', x, a)
DL = lambda d: ('del', d)


# ============================================================ origin capture
class FugueOrigins(SidedChain):
    """The sided chain model, Fugue policy, plus generation-time origin
    capture: origins[x] = (leftOrigin, rightOrigin) with 0 = start and
    None = end, computed exactly as `choose` computes its successor."""
    name = 'sided-chain[fugue]+origins'
    policy = 'fugue'

    def begin(self):
        self.origins = {}

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


# ============================================================ the predicate
def check_wk(D, state, strict=True):
    """The adapted Def-4 conditions on one state.  Returns a list of
    violation tuples ('C1'|'C2'|'C3', A, B, doc)."""
    live, chains, tree = state
    origins = D.origins
    minted = [x for x in chains if x in origins]
    key = {x: D.key(chains[x]) for x in minted}
    order_all = sorted(minted, key=lambda x: key[x], reverse=True)
    pos_all = {x: i for i, x in enumerate(order_all)}
    doc = D.read(state)
    pos_live = {x: i for i, x in enumerate(doc)}
    liveset = set(doc)
    lo = {x: origins[x][0] for x in minted}
    ro = {x: origins[x][1] for x in minted}

    def lt(x, y):
        """The strong-list total order, tombstones included; 0 = start is
        before everything, None = end after everything."""
        if x == 0:
            return y != 0
        if y == 0 or x is None:
            return False
        if y is None:
            return True
        return pos_all[x] < pos_all[y]

    def desc_lo(c, p):
        """c is a descendant of p in the left-origin tree (p may be 0)."""
        seen = set()
        while True:
            if c == p:
                return True
            if c == 0 or c in seen:
                return False
            seen.add(c)
            c = lo.get(c, 0)

    domain = minted if strict else doc
    bad = []
    # C1 forward
    for B in doc:
        A = lo[B]
        if A == 0 or A not in liveset:
            continue
        if all(lt(B, D2) for D2 in domain if D2 != B and lo[D2] == A):
            if pos_live[B] != pos_live[A] + 1:
                bad.append(('C1', A, B, doc))
    # C2 backward with the Lemma-5 exception
    for A in doc:
        B = ro[A]
        if B is None or B not in liveset:
            continue
        if all(lt(D2, A) for D2 in domain if D2 != A and ro[D2] == B):
            if pos_live[B] != pos_live[A] + 1:
                exc = False
                if lo[A] != lo[B]:
                    for C in doc:
                        if lt(lo[A], C) and lt(C, B) and not desc_lo(C, lo[A]):
                            exc = True
                            break
                if not exc:
                    bad.append(('C2', A, B, doc))
    # C3 same-origin tiebreak
    for i, A in enumerate(doc):
        for B in doc[i + 1:]:
            if lo[A] == lo[B] and ro[A] == ro[B] and A > B:
                bad.append(('C3', A, B, doc))
    return bad


def check_runs(D, state, runs, seen=None):
    """Candidate (a), concurrency-aware.  Each run's survivors must appear
    in run text order, and no element may sit strictly inside a run's block
    unless it was generated causally AFTER that run (an element inserted
    into the middle of a block one has already received is intent, not
    interleaving).  `seen[i]` = set of run indices run i's generator had
    absorbed; None means all runs are pairwise concurrent."""
    doc = D.read(state)
    runof = {u: i for i, run in enumerate(runs) for u in run}
    bad = []
    for i, run in enumerate(runs):
        idx = [doc.index(u) for u in run if u in doc]
        if idx != sorted(idx):
            bad.append(('RUN', run, doc))
            continue
        if not idx:
            continue
        for k in range(idx[0], idx[-1] + 1):
            f = doc[k]
            if f in run:
                continue
            j = runof.get(f)
            if j is not None and seen is not None and i in seen.get(j, set()):
                continue                    # f causally after run i: legitimate
            bad.append(('RUN', run, doc))
            break
    return bad


# ============================================================ directed cases
def directed_cases():
    """Hand-derived scenarios.  Each returns (name, violations_strict,
    violations_lenient, run_violations, doc, expected_doc)."""
    out = []

    def merge_case(name, lca, branches, runs, expect_doc):
        D = FugueOrigins()
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

    # 1. two concurrent front inserts: the minimal C3 countermodel
    merge_case('two-front-inserts', [], [[I(1, 0)], [I(2, 0)]], None, [2, 1])

    # 2. L19 backward twin (the validated trace): expected fully clean
    merge_case('L19 backward', [I(1, 0)],
               [[I(10, 0), I(30, 0), I(50, 0)], [I(21, 0), I(41, 0), I(61, 0)]],
               [[50, 30, 10], [61, 41, 21]],
               [50, 30, 10, 61, 41, 21, 1])

    # 3. forward twin: runs contiguous, C3 trips on the two heads (10, 21)
    merge_case('forward twin', [I(1, 0)],
               [[I(10, 1), I(30, 10), I(50, 30)],
                [I(21, 1), I(41, 21), I(61, 41)]],
               [[10, 30, 50], [21, 41, 61]],
               [1, 21, 41, 61, 10, 30, 50])

    # 4. mixed: one backward run, one forward run, same position (after 1)
    merge_case('mixed fwd/bwd', [I(1, 0)],
               [[I(10, 1), I(30, 1), I(50, 1)],
                [I(21, 1), I(41, 21), I(61, 41)]],
               [[50, 30, 10], [21, 41, 61]],
               [1, 21, 41, 61, 50, 30, 10])

    # 5. strict-vs-lenient C1 countermodel: dead newest sibling with a live
    # descendant. Expected: lenient C1 fires, strict stays clean.
    merge_case('lenient-C1 countermodel', [I(1, 0)],
               [[I(5, 1)], [I(8, 1), I(9, 8), DL(8)]],
               None, [1, 9, 5])

    # 6. W-K Figure 7: the Fugue/FugueMax gap (C2 violation).
    # Three concurrent front inserts A=5, B=4, C=3; r1 (sees 5,3) inserts
    # X=6 between 5 and 3; r2 (sees 5,4) inserts Y=7 between 5 and 4.
    D = FugueOrigins()
    D.begin()
    e = D.init()
    s5, _ = L.run_replica(D, e, [I(5, 0)])
    s4, _ = L.run_replica(D, e, [I(4, 0)])
    s3, _ = L.run_replica(D, e, [I(3, 0)])
    r1 = D.merge(e, D.copy(s5), s3)                 # r1 knows {5,3}
    r1, _ = L.run_replica(D, r1, [I(6, 5)])          # X=6 between 5 and 3
    r2 = D.merge(e, D.copy(s4), D.copy(s5))          # r2 knows {5,4}
    r2, _ = L.run_replica(D, r2, [I(7, 5)])          # Y=7 between 5 and 4
    m = D.merge(s5, r1, r2)                          # LCA of r1,r2 is {5}
    out.append(('figure 7 (W-K)', check_wk(D, m, True), check_wk(D, m, False),
                [], D.read(m), [5, 7, 6, 4, 3]))
    return out


# ============================================================ random cases
def random_run_scenario(rng, three=False, second_epoch=False):
    """Randomized concurrent-run scenario over a random LCA.  Returns
    (D, final_state, runs)."""
    D = FugueOrigins()
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
                d = rng.choice(doc)
                op = DL(d)
            else:
                a = rng.choice([0] + doc) if doc else 0
                op = I(fresh(), a)
            s = D.apply(s, op)
            ops.append(op)
        return s, ops

    def run_ops(st, n):
        """One run: forward or backward, at a random live position."""
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
    # two epochs, Figure-7 shaped: A,B,C branch (runs 0,1,2); r1 absorbs
    # A and C then runs (run 3); r2 absorbs B and A then runs (run 4);
    # final merge over LCA = (Ls + A).
    A, B, C = branches
    r1 = D.merge(Ls, D.copy(A), D.copy(C))
    r1, t1 = run_ops(r1, rng.randint(1, 3))
    r2 = D.merge(Ls, D.copy(B), D.copy(A))
    r2, t2 = run_ops(r2, rng.randint(1, 3))
    m = D.merge(A, r1, r2)
    return D, m, runs + [t1, t2], {3: {0, 2}, 4: {0, 1}}


def sweep(n, seed0, **kw):
    stats = {'C1': 0, 'C2': 0, 'C3': 0, 'RUN': 0, 'C1len': 0}
    first = {}
    for e in range(n):
        rng = Random(seed0 * 99991 + e)
        D, m, runs, seen = random_run_scenario(rng, **kw)
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
    return stats, first


if __name__ == '__main__':
    print('==== directed cases (hand-derived expectations) ====')
    for name, vs, vl, vr, doc, expect in directed_cases():
        okdoc = 'doc OK' if doc == expect else f'DOC MISMATCH exp={expect}'
        print(f'  {name:26} out={doc}  [{okdoc}]')
        print(f'      strict: {[v[:3] for v in vs] if vs else "CLEAN"}')
        if [v[:3] for v in vl] != [v[:3] for v in vs]:
            print(f'      lenient extra: {[v[:3] for v in vl]}')
        if vr:
            print(f'      RUN violations: {vr}')
    print()
    print('==== randomized sweeps (Fugue policy, strict reading) ====')
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    for tag, seed0, kw in (('2-branch runs', 1, {}),
                           ('3-branch runs', 2, {'three': True}),
                           ('3-branch two-epoch (fig-7 shaped)', 3,
                            {'three': True, 'second_epoch': True})):
        stats, first = sweep(N, seed0=seed0, **kw)
        print(f'  {tag:36} n={N}  '
              f"C1={stats['C1']} C2={stats['C2']} C3={stats['C3']} "
              f"RUN={stats['RUN']}  [lenient C1={stats['C1len']}]")
        for k in ('C1', 'C2', 'C3', 'RUN', 'C1len'):
            if k in first:
                e, v = first[k]
                print(f'      first {k}: case {e}: {v[:3] if k != "RUN" else v[:2]}')
