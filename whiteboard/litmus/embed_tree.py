#!/usr/bin/env python3
"""
embed_tree -- KC's challenge (2026-07-14, late): "we don't need metadata
for races ... the ranges fully capture it ... it may be the case you
don't see it or your merge may be wrong."  STATUS: EXPERIMENT.

The retention note's boxed claim (ties force a retained timestamp
verdict) has a hidden premise, made explicit here: MINTS ARE
TS-OBLIVIOUS. The quarter carve (b+w/4, b+w/2) is a deterministic
function of the seen state only, so concurrent same-slot mints produce
IDENTICAL ranges -- the tie -- and a merge repair must then decide by ts
and store the verdict somewhere. Every relsplit variant stores it in
mutable geometry, and mutation loses it (v2a dissolution, v2b topology
dependence).

The ts-faithful alternative (this file): embed the timestamp in the carve.

  I(t) = (1 - 2^-t,  1 - (3/4) * 2^-t)   relative to the anchor

Pen-and-paper properties:
  P1 injective/disjoint: s != t => I(s), I(t) disjoint (gap between).
     Concurrent same-slot mints can never collide: TIES DO NOT EXIST.
  P2 monotone: s < t => I(s) entirely below I(t); newest sits highest
     (the RGA convention) sequentially AND concurrently, with no
     head-tracking -- the mint ignores the current head entirely.
  P3 immutable geometry: no ties => no repairs => no slot rewrites,
     ever. The isometric fold preserves absolutes exactly, so a node's
     absolute range is a BIRTH CONSTANT. Merge = OR-set survival +
     refold to the nearest surviving ancestor: it re-derives coordinates
     but never re-decides an order. Convergence and pairwise stability
     should follow from "read = sort of birth constants, filtered by
     survival".
  P4 the credential persists: a dead founder's interval contains its
     folded heirs forever, so a later claimant is ordered against the
     heirs by comparing with the FOUNDER's interval -- ts(claimant) vs
     ts(founder), read off the geometry. "The ranges fully capture it."

HYPOTHESES (falsifiable; the machine decides):
  HE1 embed-tree passes the full battery (except one-sided L19) and the
      DAG PBT (FLIP/CONV/LIVE/DUP). Falsifier: any flip/divergence.
  HE2 the credential countermodel (below) separates the designs:
      relsplit-v2c (order-preserving repair over ts-OBLIVIOUS mints, the
      strongest "ranges capture the settled order" merge WITHOUT
      ts-faithful mints) diverges/flips on it; embed-tree converges.
      If v2c PASSES, my credential argument is wrong. If embed-tree
      FAILS, the ts-embedding claim is wrong.
  HE3 the toll is precision, not metadata: denominator bits grow with
      the ts values folded through (measured on chains) -- the same
      information a stamp would carry, paid in the coordinate encoding.

CREDENTIAL COUNTERMODEL (pre-registered): 6 and 10 race one slot; 22,16
typed under 6; a third party mints ts 8 into the same slot, concurrent
with everything. Topology X meets 8 while 6 is alive (8 can rank against
6 directly), THEN deletes 6; topology Y deletes 6 first, then meets 8
(8 must rank against 6's HEIRS). Equal final event sets. Prediction: a
rule ranking fresh claimants against survivors' OWN data (own ts, or
current settled order) gives X != Y -- ranking correctly needs the dead
founder's rank, which a ts-oblivious state no longer holds and
ts-faithful geometry does.
"""
from fractions import Fraction
import litmus as L
from relsplit_v2 import RelSplitV2a, l25_third_party
from contest_tree import ce_subordination_escape, ce_retroactive_subordination


# =========================================================================
# relsplit-v2c: KC's "the ranges capture the settled order" taken at its
# strongest WITHOUT changing the mint -- order-preserving repair. Settled
# members (present in the LCA, or in both branches) keep their current
# display order verbatim; only fresh claimants (born in exactly one
# branch) are ranked, by ts against the settled members' own ts.
# =========================================================================
class RelSplitV2c(RelSplitV2a):
    name = 'relsplit-v2c'

    def merge(self, Ls, As, Bs):
        surv = (set(Ls) & set(As) & set(Bs)) | (set(As) - set(Ls)) | (set(Bs) - set(Ls))
        fresh = (set(As) ^ set(Bs)) - set(Ls)
        inputs = (Ls, As, Bs)

        def resolved_rec(u):
            lrec = Ls.get(u)
            for S in (As, Bs):
                if u in S and S[u] != lrec:
                    return S[u]
            return As[u] if u in As else (Bs[u] if u in Bs else lrec)

        def fold_depth(rec):
            d, p, guard = 0, rec[0], 0
            while p != 0 and p not in surv:
                r = resolved_rec(p)
                if r is None: break
                d += 1; p = r[0]
                guard += 1
                if guard > 100000: raise RuntimeError('cycle')
            return d

        M = {}
        for u in surv:
            recs = [S[u] for S in inputs if u in S]
            base = max(recs, key=fold_depth)
            depth0 = fold_depth(base)
            peers = [r for r in recs if r[0] == base[0] and fold_depth(r) == depth0]
            lrec = Ls.get(u)
            resolved_peers = [r for r in peers if r != lrec]
            rec = resolved_peers[0] if resolved_peers else base
            p, lo, hi = rec
            guard = 0
            while p != 0 and p not in surv:
                pr = resolved_rec(p)
                if pr is None: break
                pw = pr[2] - pr[1]
                lo, hi = pr[1] + pw*lo, pr[1] + pw*hi
                p = pr[0]
                guard += 1
                if guard > 100000: raise RuntimeError('cycle')
            M[u] = (p, lo, hi)

        def repair(p):
            ks = sorted((x for x in M if M[x][0] == p), key=lambda x: M[x][1])
            comps, cur, cmax = [], [], None
            for k in ks:
                lo, hi = M[k][1], M[k][2]
                if cur and lo < cmax: cur.append(k); cmax = max(cmax, hi)
                else:
                    if cur: comps.append(cur)
                    cur, cmax = [k], hi
            if cur: comps.append(cur)
            for comp in comps:
                if len(comp) < 2: continue
                ulo = min(M[k][1] for k in comp); uhi = max(M[k][2] for k in comp)
                W = uhi - ulo
                settled = sorted((k for k in comp if k not in fresh),
                                 key=lambda x: -M[x][1])      # current order, top first
                order = list(settled)
                for f in sorted((k for k in comp if k in fresh), reverse=True):
                    pos = len(order)
                    for i, s in enumerate(order):
                        if s < f:                              # first settled with own ts < f
                            pos = i; break
                    order.insert(pos, f)
                n = len(order)
                for r, k in enumerate(order):
                    M[k] = (p, uhi - Fraction(r+1)*W/n, uhi - Fraction(r)*W/n)
            for k in (x for x in M if M[x][0] == p):
                repair(k)
        repair(0)
        return M


# =========================================================================
# embed-tree: ts-faithful mints, no repairs, immutable geometry.
# =========================================================================
class EmbedTree(L.Design):
    name = 'embed-tree'

    def init(self): return {}
    def copy(self, s): return dict(s)
    def fp(self, s): return frozenset(s.items())

    @staticmethod
    def I(t):
        w = Fraction(1, 2**t)
        return (1 - w, 1 - w*Fraction(3, 4))

    def apply(self, s, it):
        if it[0] == 'ins':
            _, x, a = it
            p = a if a != 0 else 0
            lo, hi = self.I(x)
            s[x] = (p, lo, hi)
        else:
            d = it[1]
            if d in s:
                dp, dl, dh = s.pop(d)
                dw = dh - dl
                for c in list(s):
                    if s[c][0] == d:                       # isometric fold
                        _, cl, ch = s[c]
                        s[c] = (dp, dl + dw*cl, dl + dw*ch)
        return s

    def read(self, s):
        out = []
        def dfs(u):
            for c in sorted((x for x in s if s[x][0] == u),
                            key=lambda x: (s[x][1], x), reverse=True):
                out.append(c); dfs(c)
        dfs(0); return out

    def merge(self, Ls, As, Bs):
        surv = (set(Ls) & set(As) & set(Bs)) | (set(As) - set(Ls)) | (set(Bs) - set(Ls))
        inputs = (As, Bs, Ls)

        def src_of(u):
            for S in inputs:
                if u in S: return S
            raise RuntimeError(f'no record for {u}')

        def absrange(u):
            # fold to root inside u's own source: a record's current
            # parent is always live in that source, so the chain stays in
            # one input. Absolutes are fold-invariant (P3), so the source
            # choice cannot matter -- asserted below.
            S = src_of(u)
            p, lo, hi = S[u]
            guard = 0
            while p != 0:
                pp, plo, phi = S[p]
                w = phi - plo
                lo, hi = plo + w*lo, plo + w*hi
                p = pp
                guard += 1
                if guard > 100000: raise RuntimeError('cycle')
            return (lo, hi)

        A2, par = {}, {}
        for u in surv:
            A2[u] = absrange(u)
            # cross-input invariance check: any other input holding u
            # must agree on the absolute (fires => the merge is wrong)
            for S in inputs:
                if u in S and S is not src_of(u):
                    p, lo, hi = S[u]
                    g = 0
                    while p != 0:
                        pp, plo, phi = S[p]
                        w = phi - plo
                        lo, hi = plo + w*lo, plo + w*hi
                        p = pp
                        g += 1
                        if g > 100000: raise RuntimeError('cycle')
                    assert (lo, hi) == A2[u], f'absolute divergence at {u}'
            S = src_of(u)
            p = S[u][0]
            while p != 0 and p not in surv:
                p = S[p][0]
            par[u] = p

        M = {}
        for u in surv:
            p = par[u]
            if p == 0:
                plo, w = Fraction(0), Fraction(1)
            else:
                plo, phi = A2[p]; w = phi - plo
            lo, hi = A2[u]
            M[u] = (p, (lo - plo)/w, (hi - plo)/w)
        return M


def credential_cm(D):
    """The pre-registered countermodel. Returns (ok, detail)."""
    z = D.init()
    R6  = D.apply(D.copy(z), ('ins', 6, 0))
    R10 = D.apply(D.copy(z), ('ins', 10, 0))
    M   = D.merge(D.copy(z), D.copy(R6), D.copy(R10))
    Mp  = D.apply(D.apply(D.copy(M), ('ins', 22, 6)), ('ins', 16, 6))
    pre = D.read(Mp)
    RT  = D.apply(D.copy(z), ('ins', 8, 0))
    # X: meet 8 while 6 alive, then delete 6
    X1 = D.merge(D.copy(z), D.copy(Mp), D.copy(RT)); x_mid = D.read(X1)
    xr = D.read(D.apply(D.copy(X1), ('del', 6)))
    # Y: delete 6 first, then meet 8
    Y1 = D.apply(D.copy(Mp), ('del', 6)); y_mid = D.read(Y1)
    yr = D.read(D.merge(D.copy(z), D.copy(Y1), D.copy(RT)))
    reads = [pre, x_mid, xr, y_mid, yr]
    seen, flips = set(), []
    for r in reads:
        for i in range(len(r)):
            for j in range(i+1, len(r)):
                if (r[j], r[i]) in seen: flips.append((r[j], r[i]))
                seen.add((r[i], r[j]))
    conv = (xr == yr)
    ok = conv and not flips
    return ok, f'pre={pre} X={xr} Y={yr} conv={conv} flips={sorted(set(flips))}'


if __name__ == '__main__':
    import pbt
    from random import Random

    print('== reference: the credential CM on the tombstoned RGA ==')
    RGA = {d.name: d for d in L.DESIGNS}['tombstoned']
    ok, detail = credential_cm(RGA)
    print(f'  {"PASS" if ok else "FAIL"}  {detail}')

    for D in (RelSplitV2c(), EmbedTree()):
        print(f'==== {D.name} ====')
        ok, detail = credential_cm(D)
        print(f'  credential CM: {"PASS" if ok else "FAIL"}  {detail}')
        ok, detail = l25_third_party(D)
        print(f'  L25-third-party: {"PASS" if ok else "FAIL  " + detail}')
        for nm, fn in (('CE-escape', ce_subordination_escape),
                       ('CE-retro', ce_retroactive_subordination)):
            ok, detail = fn(D)
            print(f'  {nm}: {"survives" if ok else "REFUTED  " + detail}')
        bad, _ = pbt.run_execution(D, Random(194), 2, 4, 2, 0.3, 0.4)
        print(f'  fold-frame CM (seed 194): {"CLEAN" if not bad else bad}')
        for nm, fn in (('L25', L.l25_verdict), ('L23', L.l23_verdict), ('L24', L.l24_verdict)):
            r = fn(D); print(f'  {nm}: {"PASS" if r["ok"] else "FAIL"}')
        v = L.three_branch_verdict(D, *L.L22[1:])
        print(f'  L22: {"PASS" if v["S3topo"] else "FAIL " + str(v["reads"])}')
        for name, lca, a, b, runs in L.MERGE_TESTS:
            vv = L.merge_verdict(D, lca, a, b, runs)
            badk = [k for k in ('S3','S4','S6','S7','DUP','IDL','S5') if k in vv and not vv[k]]
            if badk: print(f'  {name}: FAIL {badk}')
        for name, _, script in L.SEQ_TESTS:
            vv = L.seq_verdict(D, script)
            if not (vv.get('S1') and vv.get('S2')): print(f'  {name}: FAIL S1/S2')
        for name, lca, a, b, post in (L.L18, L.L20):
            vv = L.post_merge_verdict(D, lca, a, b, post)
            if not vv['S2']: print(f'  {name}: FAIL')
        v = L.stale_fork_verdict(D, *L.L21[1:])
        if not all(v[k] for k in ('S3','S4','S6','DUP')): print('  L21: FAIL')
        f, _ = pbt.sweep(D, 120)
        print(f'  DAG PBT 120: {"CLEAN" if not f else str(len(f))+" FAIL, first "+str(f[0])}')
        if not f:
            f2, _ = pbt.sweep(D, 300, seed0=7, n_replicas=6, n_rounds=12)
            print(f'  DAG PBT 300 (6 rep, 12 rounds): '
                  f'{"CLEAN" if not f2 else str(len(f2))+" FAIL, first "+str(f2[0])}')

    # HE3: the precision toll (embed vs quarter-carve), N=1000 chain
    print('== HE3: precision toll, 1000-chain then delete-all ==')
    for D in (EmbedTree(), RelSplitV2a()):
        s = D.init(); N = 1000
        s = D.apply(s, ('ins', 1, 0))
        for i in range(2, N+1): s = D.apply(s, ('ins', i, i-1))
        for i in range(1, N):   s = D.apply(s, ('del', i))
        (p, lo, hi), = s.values()
        bits = max(lo.denominator.bit_length(), hi.denominator.bit_length())
        print(f'  {D.name:14} live={len(s)}  survivor denominator ~2^{bits}')


# =========================================================================
# IEEE 754 analysis (KC's question): the same design with binary64 floats
# as the range carrier. Floats ARE dyadics -- sign * m * 2^e with m < 2^53
# -- so they are the right SHAPE for embed values (everything here is
# dyadic); the analysis measures what the fixed 53-bit window costs.
# Pre-registered failure modes:
#   F1 mint collapse: 1 - 2^-t rounds to 1.0 once 2^-t < ulp(1)/2, so
#      every mint with ts beyond ~2^6 collides at (1,1) -- ties return.
#   F2 depth underflow: absolute width 2^-(sum of ts+2) hits the
#      subnormal floor 2^-1074 after ~1000 bits of path.
#   F3 isometry loss: the fold multiplies dyadics; once a product needs
#      > 53 significand bits it rounds, absolutes stop being birth
#      constants, and different fold orders diverge -- mutable geometry
#      re-entering through the ulp (the merge's invariance assert fires).
# =========================================================================
class EmbedTreeFP(EmbedTree):
    name = 'embed-fp64'

    @staticmethod
    def I(t):
        w = 2.0**-t
        return (1.0 - w, 1.0 - 0.75*w)


def fp_report():
    import pbt
    print('== F1 mint collapse ==')
    t = 1
    while True:
        lo, hi = EmbedTreeFP.I(t)
        lo2, hi2 = EmbedTreeFP.I(t+1)
        if not (lo < hi and hi < lo2 and hi2 < 1.0):
            print(f'  first degenerate/non-disjoint mint at t={t}: '
                  f'I({t})=({lo!r},{hi!r})  I({t+1})=({lo2!r},{hi2!r})')
            break
        t += 1
    print('== F2 depth underflow (sequential chain, ts=1,2,3,...) ==')
    D = EmbedTreeFP()
    s = D.init(); s = D.apply(s, ('ins', 1, 0))
    n = None
    for i in range(2, 200):
        s = D.apply(s, ('ins', i, i-1))
        # absolute width of the deepest node
        w = 1.0
        u = i
        while u != 0:
            p, lo, hi = s[u]; w *= (hi - lo); u = p
        if w == 0.0:
            n = i
            print(f'  absolute width underflows to 0.0 at depth {i}')
            break
    if n is None: print('  no underflow through depth 200')
    print('== F3 isometry: fold exactness sentinel ==')
    D = EmbedTreeFP()
    s = D.init()
    for i, a in ((1,0),(2,1),(3,2),(4,3)):
        s = D.apply(s, ('ins', i, a))
    def absr(s, u):
        p, lo, hi = s[u]
        while p != 0:
            pp, plo, phi = s[p]
            w = phi - plo
            lo, hi = plo + w*lo, plo + w*hi
            p = pp
        return (lo, hi)
    before = absr(s, 4)
    s = D.apply(s, ('del', 2))
    after = absr(s, 4)
    print(f'  shallow chain (ts 1..4): fold exact? {before == after}')
    exact = EmbedTree()
    print('== DAG PBT under binary64 ==')
    from random import Random
    ok = flips = errs = 0
    first = None
    for i in range(120):
        try:
            bad, _ = pbt.run_execution(EmbedTreeFP(), Random(i), 4, 8, 2, 0.3, 0.4)
            if bad:
                flips += 1
                if first is None: first = (i, bad)
            else:
                ok += 1
        except AssertionError as e:
            errs += 1
            if first is None: first = (i, f'ISOMETRY ASSERT: {e}')
        except Exception as e:
            errs += 1
            if first is None: first = (i, f'{type(e).__name__}: {e}')
    print(f'  120 executions: {ok} clean, {flips} flip/conv, {errs} invariant-assert/error')
    print(f'  first failure: {first}')


if __name__ == '__main__' and __import__('sys').argv[1:] == ['fp']:
    fp_report()


# =========================================================================
# The efficient representation (KC: "is there one, if binary64 doesn't
# work?"). The unary-exponent mint I(t) = 1 - 2^-t spends t bits to
# encode log2(t) bits of information. Replace it with an ORDER-PRESERVING
# PREFIX-FREE CODE of the timestamp DELTA d = t - t_anchor (d >= 1 by
# causality: you insert after something you have seen):
#
#   C(d) = '1'^(L-1) ++ '0' ++ (binary of d minus its leading bit),
#   L = bitlength(d)                       [len = 2L-1 bits]
#
# Properties (same shape as Theorem 1, proofs one line each):
#   - prefix-free across length classes ('1'^(L-1)'0' headers differ)
#     => the dyadic cells [0.C(d), 0.C(d)+2^-len) are pairwise disjoint;
#   - monotone: d < d' => 0.C(d) < 0.C(d')  => newest highest, as before;
#   - mint takes the lower QUARTER of its cell => gaps + child headroom.
#
# Costs: sequential chain (d = 1 at every level) ~4 bits/level -- the
# quarter carve's constant, recovered; a race with timestamp gap g costs
# 2*log2(g) + O(1) bits. Total = Theta(sum over chain of log d_i): the
# entropy of the birth chain. The conservation law becomes sharp -- you
# pay for the MAGNITUDE OF ACTUAL CONCURRENCY, nothing else.
# Everything else (fold, merge, read, all theorems) is inherited verbatim.
# =========================================================================
class EmbedTreeCode(EmbedTree):
    name = 'embed-code'

    @staticmethod
    def C(d):
        b = bin(d)[2:]
        return '1'*(len(b)-1) + '0' + b[1:]

    def apply(self, s, it):
        if it[0] == 'ins':
            _, x, a = it
            p = a if a != 0 else 0
            bits = '1' + self.C(x - p)          # leading '1': keep lo > 0
            cell = Fraction(int(bits, 2), 2**len(bits))
            w = Fraction(1, 2**(len(bits)+2))
            s[x] = (p, cell + w, cell + 2*w)    # lower quarter of the cell
            return s
        return super().apply(s, it)


# =========================================================================
# embed-eliasd: the canonical mint — the flipped Elias-DELTA code (note I5,
# proved: Embed_Code_EliasDelta.lean, eliasDeltaCode, capstone inherited).
# The gamma-flip C above is applied to the LENGTH field, then the payload:
#   D(d) = C(bitlength d) ++ (d minus its leading bit)   [len = L + 2|L| - 2]
# = log2 d + O(log log d) per level. Same mint geometry; only C changes.
# Sequential (d=1) identical to C; wins from d >= 32, loses d in {2,3}+[8,15]
# (real editing tails are thin => wash on traces; the win is race-heavy
# shapes and the theorem — see entropy_measure.py + the design doc §2).
# =========================================================================
class EmbedTreeCodeD(EmbedTreeCode):
    name = 'embed-eliasd'

    @staticmethod
    def C(d):
        b = bin(d)[2:]
        h = bin(len(b))[2:]
        return '1'*(len(h)-1) + '0' + h[1:] + b[1:]


if __name__ == '__main__' and __import__('sys').argv[1:] == ['code']:
    import pbt
    D = EmbedTreeCode()
    print('==== embed-code: gauntlet ====')
    ok, detail = credential_cm(D)
    print(f'  credential CM: {"PASS" if ok else "FAIL  " + detail}')
    ok, detail = l25_third_party(D)
    print(f'  L25-third-party: {"PASS" if ok else "FAIL  " + detail}')
    for nm, fn in (('CE-escape', ce_subordination_escape),
                   ('CE-retro', ce_retroactive_subordination)):
        ok, detail = fn(D)
        print(f'  {nm}: {"survives" if ok else "REFUTED  " + detail}')
    for nm, fn in (('L25', L.l25_verdict), ('L23', L.l23_verdict), ('L24', L.l24_verdict)):
        r = fn(D); print(f'  {nm}: {"PASS" if r["ok"] else "FAIL"}')
    v = L.three_branch_verdict(D, *L.L22[1:])
    print(f'  L22: {"PASS" if v["S3topo"] else "FAIL " + str(v["reads"])}')
    for name, lca, a, b, runs in L.MERGE_TESTS:
        vv = L.merge_verdict(D, lca, a, b, runs)
        badk = [k for k in ('S3','S4','S6','S7','DUP','IDL','S5') if k in vv and not vv[k]]
        if badk: print(f'  {name}: FAIL {badk}')
    for name, _, script in L.SEQ_TESTS:
        vv = L.seq_verdict(D, script)
        if not (vv.get('S1') and vv.get('S2')): print(f'  {name}: FAIL S1/S2')
    for name, lca, a, b, post in (L.L18, L.L20):
        vv = L.post_merge_verdict(D, lca, a, b, post)
        if not vv['S2']: print(f'  {name}: FAIL')
    v = L.stale_fork_verdict(D, *L.L21[1:])
    if not all(v[k] for k in ('S3','S4','S6','DUP')): print('  L21: FAIL')
    f, _ = pbt.sweep(D, 120)
    print(f'  DAG PBT 120: {"CLEAN" if not f else str(len(f))+" FAIL, first "+str(f[0])}')
    if not f:
        f2, _ = pbt.sweep(D, 300, seed0=7, n_replicas=6, n_rounds=12)
        print(f'  DAG PBT 300 (6 rep, 12 rounds): '
              f'{"CLEAN" if not f2 else str(len(f2))+" FAIL, first "+str(f2[0])}')
    print('==== state-size measurements (survivor denominator bits) ====')
    for DD in (EmbedTreeCodeD(), EmbedTreeCode(), EmbedTree(), RelSplitV2a()):
        s = DD.init(); N = 1000
        s = DD.apply(s, ('ins', 1, 0))
        for i in range(2, N+1): s = DD.apply(s, ('ins', i, i-1))
        for i in range(1, N):   s = DD.apply(s, ('del', i))
        (p, lo, hi), = s.values()
        bits = max(lo.denominator.bit_length(), hi.denominator.bit_length())
        print(f'  {DD.name:14} 1000-chain (sequential, d=1): ~2^{bits}')
    # the race-cost case: 1000 root siblings (d = t, the worst gap growth)
    for DD in (EmbedTreeCodeD(), EmbedTreeCode(), EmbedTree()):
        s = DD.init()
        for i in range(1, 1001): s = DD.apply(s, ('ins', i, 0))
        bits = max(max(r[1].denominator.bit_length(), r[2].denominator.bit_length())
                   for r in s.values())
        tot = sum(r[1].denominator.bit_length() + r[2].denominator.bit_length()
                  for r in s.values())
        print(f'  {DD.name:14} 1000 root siblings (d=t): max ~2^{bits}, total {tot//8000} KB')
