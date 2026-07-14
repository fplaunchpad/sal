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
