#!/usr/bin/env python3
"""
fuguemax_backward_check.py -- the FugueMax backward condition, task #92 item 1.

Statement under test (design note section 9.7): Weidner-Kleppmann
Definition 4 condition (2), backward non-interleaving with the Lemma-5
exception, on the FugueMax realization (fuguemax_check.FugueMaxChain).

Three checks per state:

  (a) the backward condition itself, in TWO readings of the exception
      witness C of Lemma 5(ii):
        'live'   -- C must be visible (the current Lean BackwardExceptionM);
        'minted' -- C ranges over all elements, tombstones included (the
                    paper's reading: its C lives in "the current list
                    state", which contains tombstoned elements).
      EXPECTED: 'minted' clean everywhere; 'live' REFUTED on directed
      delete traces (fig7 + del B, the beta0 ladder + del 8). The live
      refutation is a first-class result: the current Lean def must drop
      the mLive C conjunct.
  (b) the constructed exception witness (note 9.7.5): for every premise
      pair (A, B) that is not live-consecutive, A must be an R mint with
      lo(A) != lo(B), and for EVERY live in-between c the deterministic
      witness function must return a correct C (minted, lo(A) < C < B,
      not a left-origin-tree descendant of lo(A)).
  (c) the three mint-time invariant clauses (note 9.7.2): (RSA), (RSuccL),
      (RSuccR), plus the corner fact (R0) and the loShape re-check.

Run: python3 fuguemax_backward_check.py [N]   (default N = 400 per shape)

Modifies nothing existing; imports the generators from the sibling
harness modules.
"""
import sys
from random import Random

import litmus as L
from fuguemax_check import (FugueMaxChain, fig7,
                            random_run_scenario as fmax_scen)
from traversal_check import check_loshape

R, LFT = 'R', 'L'
I = lambda x, a: ('ins', x, a)
DL = lambda d: ('del', d)


class WitnessFail(Exception):
    pass


# ============================================================ order helpers
def order_ctx(D, state):
    """Positions, lo/ro maps, and the strong-list order lt (0 = start
    before everything, None = end after everything)."""
    live, chains, tree = state
    minted = [x for x in chains if x in D.origins]
    key = {x: D.key(chains[x]) for x in minted}
    order_all = sorted(minted, key=lambda x: key[x], reverse=True)
    pos_all = {x: i for i, x in enumerate(order_all)}
    doc = D.read(state)
    lo = {x: D.origins[x][0] for x in minted}
    ro = {x: D.origins[x][1] for x in minted}

    def lt(x, y):
        if x == 0:
            return y != 0
        if y == 0 or x is None:
            return False
        if y is None:
            return True
        return pos_all[x] < pos_all[y]

    def desc_lo(c, p):
        seen = set()
        while True:
            if c == p:
                return True
            if c == 0 or c in seen:
                return False
            seen.add(c)
            c = lo.get(c, 0)

    return minted, doc, lt, desc_lo, lo, ro


# ============================================================ (a) backward
def check_backward(D, state, witness_domain):
    """C2 violations under the given witness domain ('live'|'minted')."""
    minted, doc, lt, desc_lo, lo, ro = order_ctx(D, state)
    pos_live = {x: i for i, x in enumerate(doc)}
    liveset = set(doc)
    bad = []
    for A in doc:
        B = ro[A]
        if B is None or B not in liveset:
            continue
        if not all(lt(D2, A) for D2 in minted if D2 != A and ro[D2] == B):
            continue
        if pos_live[B] == pos_live[A] + 1:
            continue
        # not consecutive: the exception must fire
        if lo[A] == lo[B]:
            bad.append(('C2-lo-eq', A, B, doc))
            continue
        dom = doc if witness_domain == 'live' else minted
        if not any(lt(lo[A], C) and lt(C, B) and not desc_lo(C, lo[A])
                   for C in dom):
            bad.append(('C2', A, B, doc))
    return bad


# ============================================================ (b) witness
def witness(D, state, A, B, c):
    """The deterministic exception-witness construction (note 9.7.5).
    Premise shape: A an R mint, ro(A) = B, c a live element strictly
    between A and B. Returns (C, route)."""
    live, chains, tree = state
    a = D.origins[A][0]
    if a == 0:
        raise WitnessFail('a = 0: unreachable for an R mint with a '
                          'recorded successor')

    def is_prefix(p, ch):
        return ch[:len(p)] == p

    def node_at(ch):
        for y, cy in chains.items():
            if cy == ch:
                return y
        raise WitnessFail(f'ancestor closure: no node at {ch}')

    cha, chA, chc = chains[a], chains[A], chains[c]
    if not is_prefix(cha, chc):
        return c, 'alpha'
    e1 = chc[len(cha)]
    if e1[0] != R:
        raise WitnessFail('beta: entry above chain(a) not R')
    E = node_at(cha + (e1,))
    if E != A:
        C = D.origins[E][1]
        if C is None:
            raise WitnessFail('beta1: ro(E) = end')
        return C, 'beta1'
    # beta0: c sits in A's own R-subtree; descend once, then re-aim
    e2 = chc[len(chA)]
    if e2[0] != R:
        raise WitnessFail('beta0: entry above chain(A) not R')
    Dn = node_at(chA + (e2,))
    nD = D.origins[Dn][1]
    if nD is None:
        raise WitnessFail('beta0: ro(D) = end')
    chn = chains[nD]
    if not is_prefix(cha, chn):
        return nD, 'beta0-direct'
    e3 = chn[len(cha)]
    if e3[0] != R:
        raise WitnessFail('beta0: entry of chain(ro D) above chain(a) not R')
    E2 = node_at(cha + (e3,))
    if E2 == A:
        raise WitnessFail('beta0: ro(D) landed back in Subtree(A)')
    C = D.origins[E2][1]
    if C is None:
        raise WitnessFail('beta0: ro(E2) = end')
    return C, 'beta0-ladder'


def check_witness(D, state, stats=None):
    """For every premise pair not live-consecutive: A must be an R mint
    with lo(A) != lo(B) (the L case is consecutive outright), and the
    witness function must produce a correct C for EVERY live in-between."""
    live, chains, tree = state
    minted, doc, lt, desc_lo, lo, ro = order_ctx(D, state)
    pos_live = {x: i for i, x in enumerate(doc)}
    liveset = set(doc)
    bad = []
    for A in doc:
        B = ro[A]
        if B is None or B not in liveset:
            continue
        if not all(lt(D2, A) for D2 in minted if D2 != A and ro[D2] == B):
            continue
        if not lt(A, B):
            bad.append(('step0: not A < B', A, B))
            continue
        betweens = [c for c in doc if lt(A, c) and lt(c, B)]
        if not betweens:
            continue
        if tree[A][0] == LFT:
            bad.append(('L-case non-consecutive', A, B, doc))
            continue
        if lo[A] == lo[B]:
            bad.append(('cond-(i) fails: lo(A) = lo(B)', A, B))
            continue
        for c in betweens:
            try:
                C, route = witness(D, state, A, B, c)
            except WitnessFail as w:
                bad.append(('witness fail', A, B, c, str(w)))
                continue
            ok = (C in D.origins and lt(lo[A], C) and lt(C, B)
                  and not desc_lo(C, lo[A]))
            if not ok:
                bad.append(('witness wrong', A, B, c, C, route))
            elif stats is not None:
                stats[route] = stats.get(route, 0) + 1
                if C not in liveset:
                    stats['dead-witness'] = stats.get('dead-witness', 0) + 1
    return bad


# ============================================================ (c) clauses
def check_clauses(D, state):
    """(RSA), (RSuccL), (RSuccR), (R0) on every minted record."""
    live, chains, tree = state
    minted, doc, lt, desc_lo, lo, ro = order_ctx(D, state)
    bad = []
    for x in minted:
        lox, rox = lo[x], ro[x]
        side, parent = tree[x]
        if side == LFT:
            if rox != parent:
                bad.append(('L: ro != parent', x))
            if not lt(lox, rox):
                bad.append(('L: not lo < ro', x))
            continue
        if lox != parent:
            bad.append(('R: lo != parent', x))
        if lox == 0:
            if rox is not None:
                bad.append(('R0: root R mint with a successor', x))
            continue
        if rox is not None and not lt(lox, rox):
            bad.append(('RSA', x))
        asd, ap = tree[lox]
        if asd == LFT:                               # (RSuccL)
            if rox is None:
                bad.append(('RSuccL: ro = end', x))
            elif rox != ap:
                ok = any(tree.get(s) == (LFT, ap) and lt(lox, s)
                         and chains[rox][:len(chains[s])] == chains[s]
                         for s in minted)
                if not ok:
                    bad.append(('RSuccL', x, rox))
        else:                                        # (RSuccR)
            m = ro[lox]
            if m is not None:
                if rox is None:
                    bad.append(('RSuccR: ro = end', x))
                elif not (rox == m or lt(rox, m)):
                    bad.append(('RSuccR', x, rox, m))
    return bad


def check_all(D, state, stats=None):
    """(minted-reading backward, witness, clauses, loShape) failures, and
    separately the live-reading backward violations."""
    hard = (check_backward(D, state, 'minted') + check_witness(D, state, stats)
            + check_clauses(D, state) + check_loshape(D, state))
    livec2 = check_backward(D, state, 'live')
    return hard, livec2


# ============================================================ directed cases
def merged(lca, branches, post=()):
    """Merge pairwise from a common LCA, then apply post ops."""
    D = FugueMaxChain()
    D.begin()
    Ls, _ = L.run_replica(D, D.init(), lca)
    sts = [L.run_replica(D, Ls, b)[0] for b in branches]
    m = sts[0]
    for s2 in sts[1:]:
        m = D.merge(Ls, m, s2)
    for it in post:
        m = D.apply(m, it)
    return D, m


def beta0_case(ladder, kill):
    """The beta0 exercises (note 9.7.5): three concurrent root runs 1, 2,
    3; A = 4 an R child of a = 1 minted in view {1, 3} (so ro(A) = B = 3,
    tag key(3)); then a live in-between inside A's own R-subtree.

    ladder=False (beta0 direct): 5 = R child of 4 minted in view
    {1, 3, 4, 2} (succ(4) = 2, so ro(5) = 2, outside Subtree(1)).
    Display [1, 4, 5, 2, 3]; the pair (4, 3) has live in-betweens 5, 2;
    the witness for c = 5 is ro(5) = 2 by the beta0-direct route.

    ladder=True (beta0 ladder): 6 = R child of 1 minted in view {1, 2}
    (ro(6) = 2, tag key(2) > key(3)), then 7 = R child of 4 minted in
    view {1, 3, 4, 2, 6} (succ(4) = 6, so ro(7) = 6, INSIDE Subtree(1)).
    Display [1, 4, 7, 6, 2, 3]; the witness for c = 7 re-aims through
    E2 = 6 and returns ro(6) = 2 by the beta0-ladder route.

    kill=True deletes the witness 2: the minted reading keeps C = 2, the
    live reading is refuted (all live in-betweens are lo-descendants of
    1)."""
    D = FugueMaxChain()
    D.begin()
    e = D.init()
    r1, _ = L.run_replica(D, e, [I(1, 0)])
    r2, _ = L.run_replica(D, e, [I(2, 0)])
    r3, _ = L.run_replica(D, e, [I(3, 0)])
    rA = D.merge(e, D.copy(r1), r3)              # {1, 3}
    rA, _ = L.run_replica(D, rA, [I(4, 1)])      # 4 = R child of 1, ro 3
    if not ladder:
        m = D.merge(e, rA, r2)                   # {1, 3, 4, 2}
        m, _ = L.run_replica(D, m, [I(5, 4)])    # 5 = R child of 4, ro 2
    else:
        rD = D.merge(e, D.copy(r1), r2)          # {1, 2}
        rD, _ = L.run_replica(D, rD, [I(6, 1)])  # 6 = R child of 1, ro 2
        m = D.merge(e, rA, rD)                   # {1, 3, 4, 2, 6}
        m, _ = L.run_replica(D, m, [I(7, 4)])    # 7 = R child of 4, ro 6
    if kill:
        m = D.apply(m, DL(2))
    return D, m


def directed_states():
    out = []
    # the Figure-7 execution, both mint orders, live and with B = 4 deleted
    for adverse in (False, True):
        for kill in (False, True):
            D = FugueMaxChain()
            m = fig7(D, adverse=adverse)
            if kill:
                m = D.apply(m, DL(4))
            nm = f'fig7 adverse={int(adverse)}' + (' + del 4' if kill else '')
            out.append((nm, D, m, kill))
    # L19 backward and the forward twin
    out.append(('L19 backward',
                *merged([I(1, 0)], [[I(10, 0), I(30, 0), I(50, 0)],
                                    [I(21, 0), I(41, 0), I(61, 0)]]), False))
    out.append(('forward twin',
                *merged([I(1, 0)], [[I(10, 1), I(30, 10), I(50, 30)],
                                    [I(21, 1), I(41, 21), I(61, 41)]]), False))
    # dead-sibling variants (the strict-vs-lenient countermodel family)
    out.append(('dead-sibling',
                *merged([I(1, 0)], [[I(5, 1)],
                                    [I(2, 1), I(9, 2), DL(2)]]), False))
    out.append(('dead-sibling + del 9',
                *merged([I(1, 0)], [[I(5, 1)],
                                    [I(2, 1), I(9, 2), DL(2)]],
                        post=[DL(9)]), False))
    # the beta0 exercises, live and with the witness killed
    for ladder, nm in ((False, 'beta0 direct'), (True, 'beta0 ladder')):
        for kill in (False, True):
            out.append((nm + (' + del 2' if kill else ''),
                        *beta0_case(ladder, kill), kill))
    return out


# ============================================================ random cases
def random_del_scenario(rng, three=False, second_epoch=False):
    """Concurrent branches with MIXED inserts and deletes (the shape the
    older sweeps never exercised: deletes on concurrent branches)."""
    D = FugueMaxChain()
    D.begin()
    nid = [1]

    def fresh():
        x = nid[0]
        nid[0] += 1
        return x

    def rand_ops(st, k, p_del=0.35):
        s = D.copy(st)
        for _ in range(k):
            doc = D.read(s)
            if doc and rng.random() < p_del:
                s = D.apply(s, DL(rng.choice(doc)))
            else:
                a = rng.choice([0] + doc) if doc else 0
                s = D.apply(s, I(fresh(), a))
        return s

    Ls = rand_ops(D.init(), rng.randint(1, 4), p_del=0.15)
    nb = 3 if three else 2
    branches = [rand_ops(Ls, rng.randint(2, 5)) for _ in range(nb)]
    if not second_epoch:
        m = branches[0]
        for s2 in branches[1:]:
            m = D.merge(Ls, m, s2)
        return D, rand_ops(m, rng.randint(0, 2))
    A, B, C = branches
    r1 = rand_ops(D.merge(Ls, D.copy(A), D.copy(C)), rng.randint(1, 3))
    r2 = rand_ops(D.merge(Ls, D.copy(B), D.copy(A)), rng.randint(1, 3))
    return D, D.merge(A, r1, r2)


def sweep(n, seed0, scen, **kw):
    hard, livec2, first, stats = 0, 0, None, {}
    for e in range(n):
        rng = Random(seed0 * 99991 + e)
        if scen is fmax_scen:
            D, m = scen(rng, FugueMaxChain, **kw)[:2]
        else:
            D, m = scen(rng, **kw)
        hb, lc = check_all(D, m, stats)
        hard += len(hb)
        livec2 += (1 if lc else 0)
        if hb and first is None:
            first = (e, hb[0])
    return hard, livec2, first, stats


if __name__ == '__main__':
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 400
    fail, live_refuted = 0, 0
    totstats = {}

    print('==== directed cases ====')
    for name, D, m, expect_live_c2 in directed_states():
        hb, lc = check_all(D, m, totstats)
        fail += len(hb)
        lv = 'live-C2 ' + ('FIRES' if lc else 'clean')
        okl = 'ok' if bool(lc) == expect_live_c2 else 'UNEXPECTED'
        live_refuted += (1 if lc else 0)
        print(f'  {name:24} {"CLEAN" if not hb else "FAIL":6} '
              f'[{lv}, {okl}]  read={D.read(m)}')
        for b in hb:
            print(f'      {b}')
        if bool(lc) != expect_live_c2:
            fail += 1
            print(f'      live-C2 expectation violated: {lc}')

    print('==== randomized sweeps ====')
    shapes = (('del 2-branch', 11, random_del_scenario, {}),
              ('del 3-branch', 12, random_del_scenario, {'three': True}),
              ('del two-epoch', 13, random_del_scenario,
               {'three': True, 'second_epoch': True}),
              ('ins-only 2-branch', 1, fmax_scen, {}),
              ('ins-only 3-branch', 2, fmax_scen, {'three': True}),
              ('ins-only two-epoch', 3, fmax_scen,
               {'three': True, 'second_epoch': True}))
    for nm, seed0, scen, kw in shapes:
        n = N if scen is random_del_scenario else N // 2
        hb, lc, first, stats = sweep(n, seed0, scen, **kw)
        fail += hb
        live_refuted += lc
        for k, v in stats.items():
            totstats[k] = totstats.get(k, 0) + v
        print(f'  {nm:20} n={n}  hard={hb}  live-C2-states={lc}'
              + (f'  first: case {first[0]}: {first[1]}' if first else ''))

    print('==== witness route statistics ====')
    for k in sorted(totstats):
        print(f'  {k:16} {totstats[k]}')

    print('==== VERDICT ====')
    print(f'  corrected reading (minted witness) + construction + clauses: '
          f'{"CLEAN" if fail == 0 else str(fail) + " FAIL"}')
    print(f'  live-witness reading (current Lean def): '
          f'{"REFUTED, " + str(live_refuted) + " state(s)" if live_refuted else "no violation seen"}')
    sys.exit(1 if fail else 0)
