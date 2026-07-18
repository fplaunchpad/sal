#!/usr/bin/env python3
"""
traversal_check.py -- the executable traversal theorem, task #88 stage 2.

Claim under test (the design note's section 9.1): for a chain-generated
state, the display order (descending key over minted coordinates, dead
elements included) IS the depth-first in-order traversal of the origin
tree implicit in the chains: for each node, L-subtrees in the kernel's
L-sibling order, then the node, then R-subtrees in the kernel's R-sibling
order, recursively. Two kernels, two sibling orders:

  * plain sided (Fugue policy, FugueOrigins): L ascending stamp (older
    first), R descending stamp (newer first);
  * FugueMax (FugueMaxChain): L ascending stamp, R by reverse right
    origin (smaller recorded tag first), ties ascending stamp.

Also checked, per state: the loShape invariant (design note 9.2), the
chain form of the paper's Lemma 8(a): every minted x has
chain(x) = chain(lo(x)) + (one R entry) + (L entries only),
where lo is the generation-time recorded left origin (0 = start).

A mismatch is a first-class result. Run:
    python3 traversal_check.py [N]     (default N = 300 per sweep shape)

Modifies nothing existing; imports the generators from the sibling
harness modules.
"""
import sys
from random import Random

import litmus as L
from embed_sided import SidedChain
from fugue_noninterleave_check import (FugueOrigins,
                                       random_run_scenario as fugue_scen)
from fuguemax_check import (FugueMaxChain, fig7,
                            random_run_scenario as fmax_scen)

R, LFT = 'R', 'L'
I = lambda x, a: ('ins', x, a)
DL = lambda d: ('del', d)


# ============================================================ the traversal
def build_tree(chains):
    """children[parent chain] -> list of (entry, child chain). Every
    parent prefix of a minted chain is itself minted (ancestor closure),
    with the root ()."""
    children = {}
    for x, ch in chains.items():
        children.setdefault(ch[:-1], []).append((ch[-1], ch))
    return children


def traverse(D, chains):
    """The in-order traversal, kernel sibling orders read off D.key of a
    single-entry chain (so the sibling comparator is EXACTLY the kernel's
    entry order, not a re-implementation)."""
    children = build_tree(chains)
    byspine = {ch: x for x, ch in chains.items()}
    out = []

    def entry_key(e):
        # the kernel's entry order: key of the one-entry chain, descending
        return D.key((e,))

    def emit(ch):
        kids = children.get(ch, [])
        ls = [c for c in kids if c[0][0] == LFT]
        rs = [c for c in kids if c[0][0] == R]
        ls.sort(key=lambda c: entry_key(c[0]), reverse=True)
        rs.sort(key=lambda c: entry_key(c[0]), reverse=True)
        for _, cch in ls:
            emit(cch)
        if ch != ():
            out.append(byspine[ch])
        for _, cch in rs:
            emit(cch)

    emit(())
    return out


# ============================================================ the checks
def check_traversal(D, state):
    """traversal == display order over ALL minted (dead included), and the
    live read is its live filter. Returns a list of mismatch strings."""
    live, chains, _tree = state[:3]
    bad = []
    trav = traverse(D, chains)
    disp = sorted(chains.keys(), key=lambda x: D.key(chains[x]),
                  reverse=True)
    if trav != disp:
        bad.append(f'traversal != display: {trav} vs {disp}')
    doc = D.read(state)
    tlive = [x for x in trav if x in live]
    if tlive != doc:
        bad.append(f'live traversal != read: {tlive} vs {doc}')
    return bad


def check_loshape(D, state):
    """chain(x) = chain(lo(x)) + (R entry) + all-L, for every minted x
    with recorded origins."""
    _live, chains, _tree = state[:3]
    bad = []
    for x, (lo, _ro) in D.origins.items():
        if x not in chains:
            continue
        base = chains.get(lo, ()) if lo != 0 else ()
        ch = chains[x]
        if ch[:len(base)] != base or len(ch) <= len(base):
            bad.append(f'loShape {x}: chain(lo={lo}) not a proper prefix')
            continue
        ext = ch[len(base):]
        if ext[0][0] != R:
            bad.append(f'loShape {x}: extension head not R: {ext[0]}')
        if any(e[0] != LFT for e in ext[1:]):
            bad.append(f'loShape {x}: non-L entry in tail: {ext[1:]}')
    return bad


# ============================================================ directed cases
def directed_states():
    """(name, D, state) for the note's directed cases, both kernels."""
    out = []

    def merged(mk, name, lca, branches):
        D = mk()
        D.begin()
        Ls, _ = L.run_replica(D, D.init(), lca)
        sts = [L.run_replica(D, Ls, b)[0] for b in branches]
        m = sts[0]
        for s2 in sts[1:]:
            m = D.merge(Ls, m, s2)
        out.append((name, D, m))

    for mk, tag in ((FugueOrigins, 'fugue'), (FugueMaxChain, 'fuguemax')):
        merged(mk, f'{tag}: two-front', [], [[I(1, 0)], [I(2, 0)]])
        merged(mk, f'{tag}: L19 backward', [I(1, 0)],
               [[I(10, 0), I(30, 0), I(50, 0)],
                [I(21, 0), I(41, 0), I(61, 0)]])
        merged(mk, f'{tag}: forward twin', [I(1, 0)],
               [[I(10, 1), I(30, 10), I(50, 30)],
                [I(21, 1), I(41, 21), I(61, 41)]])
        merged(mk, f'{tag}: mixed', [I(1, 0)],
               [[I(10, 1), I(30, 1), I(50, 1)],
                [I(21, 1), I(41, 21), I(61, 41)]])
        merged(mk, f'{tag}: dead-sibling', [I(1, 0)],
               [[I(5, 1)], [I(2, 1), I(9, 2), DL(2)]])
    for adverse in (False, True):
        D = FugueMaxChain()
        m = fig7(D, adverse=adverse)
        out.append((f'fuguemax: fig7 adverse={adverse}', D, m))
    return out


def sweep(n, seed0, scen, **kw):
    trav_bad, shape_bad, first = 0, 0, None
    for e in range(n):
        rng = Random(seed0 * 99991 + e)
        got = scen(rng, **kw) if scen is fugue_scen else \
            scen(rng, FugueMaxChain, **kw)
        D, m = got[0], got[1]
        tb = check_traversal(D, m)
        sb = check_loshape(D, m)
        trav_bad += len(tb)
        shape_bad += len(sb)
        if (tb or sb) and first is None:
            first = (e, (tb + sb)[0])
    return trav_bad, shape_bad, first


if __name__ == '__main__':
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    fail = 0

    print('==== directed cases: traversal == display, loShape ====')
    for name, D, m in directed_states():
        tb = check_traversal(D, m)
        sb = check_loshape(D, m)
        verdict = 'CLEAN' if not (tb or sb) else 'FAIL'
        fail += len(tb) + len(sb)
        print(f'  {name:28} {verdict}   read={D.read(m)}')
        for b in tb + sb:
            print(f'      {b}')

    print('==== randomized sweeps ====')
    shapes = (('2-branch', 1, {}), ('3-branch', 2, {'three': True}),
              ('two-epoch', 3, {'three': True, 'second_epoch': True}))
    for scen, tag in ((fugue_scen, 'fugue   '), (fmax_scen, 'fuguemax')):
        for nm, seed0, kw in shapes:
            tb, sb, first = sweep(N, seed0, scen, **kw)
            fail += tb + sb
            print(f'  {tag} {nm:10} n={N}  traversal={tb}  loShape={sb}'
                  + (f'  first: case {first[0]}: {first[1]}' if first else ''))

    print(f'==== VERDICT: {"CLEAN" if fail == 0 else str(fail) + " FAIL"} ====')
