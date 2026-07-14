#!/usr/bin/env python3
"""
relsplit_v2 — KC's keep-the-range design with merge-time canonical
refolding. STATUS: EXPERIMENT (2026-07-14, late session).

DESIGN (one structure, two views): parent-relative ranges are the durable
rendering of the per-level sibling list; nesting encodes the splice;
coordinates encode the order. Quarter carve (b+w/4, b+w/2) so ties occur
exactly at genuine races (same parent, same displaced head). Delete =
isometric fold (provisional, local frames). MERGE = the point of maximal
knowledge: survival (OR-set); CANONICAL REFOLDING — a survivor folded in
some input is re-folded from its least-folded record through the
MOST-RESOLVED record of each dead ancestor (the fold-frame-divergence
fix: local folds through stale frames are re-homed through resolved
ones); then overlap repair.

Two repair variants (pre-registered fork):
  v2a — naive family re-split: union of each overlapping component into
        equal slots, newest topmost. PREDICTION: fails the
        L25-third-party shape (a late full-slot claimant dissolves an
        integrated partition and its heirs re-litigate by own ts).
  v2b — containment-aware: members strictly containing others are
        CLAIMANTS; the contained, already-integrated partition is ONE
        FROZEN BLOCK (internal geometry preserved, rescaled as a group);
        units ordered newest-first by key (claimant: own ts; block: max
        member ts — an arbitrary but deterministic choice, pre-registered
        as such). Blocks never internally reordered => no pairwise flips
        inside; claimant-vs-block pairs are fresh (never co-displayed).

HYPOTHESES
  HV1 v2a fixes fold-frame divergence (the seed-194 countermodel runs
      clean) — the refolding rule is the fix, independent of the repair.
  HV2 v2a still fails L25-third-party (prediction above).
  HV3 v2b passes L25-third-party AND the full gauntlet (battery + PBT).
      Falsifier: any flip/divergence; minimize.
  HV4 retention: state is ranges only — zero stamps, zero tombstones;
      the 1M scenario carries one node.
  HV5 v2b need not equal RGA-dagger (block-key choices diverge on
      claimant-vs-dead-founder shapes); the lockstep run characterizes
      where. Divergence with a clean contract is acceptable.

KNOWN RISKS: topology-dependence of block structure (blocks are derived
from current geometry, which differs mid-flight across merge orders);
posthumous ties; tied orphans; both-branches-resolved-differently record
conflicts (A-first tiebreak, logged as a hole).
"""
from fractions import Fraction
import litmus as L


class RelSplitV2a(L.Design):
    name = 'relsplit-v2a'
    BLOCKS = False

    def init(self): return {}
    def copy(self, s): return dict(s)
    def fp(self, s): return frozenset(s.items())

    def _kids(self, s, p):
        return sorted((x for x in s if s[x][0] == p),
                      key=lambda x: (s[x][1], x), reverse=True)

    def apply(self, s, it):
        if it[0] == 'ins':
            _, x, a = it
            p = a if a != 0 else 0
            b = max((s[k][2] for k in s if s[k][0] == p), default=Fraction(0))
            w = Fraction(1) - b
            s[x] = (p, b + w/4, b + w/2)
        else:
            d = it[1]
            if d in s:
                dp, dl, dh = s.pop(d)
                dw = dh - dl
                for c in list(s):
                    if s[c][0] == d:
                        _, cl, ch = s[c]
                        s[c] = (dp, dl + dw*cl, dl + dw*ch)
        return s

    def read(self, s):
        out = []
        def dfs(u):
            for c in self._kids(s, u): out.append(c); dfs(c)
        dfs(0); return out

    # ---- merge ----
    def merge(self, Ls, As, Bs):
        surv = (set(Ls) & set(As) & set(Bs)) | (set(As) - set(Ls)) | (set(Bs) - set(Ls))
        inputs = (Ls, As, Bs)

        def all_recs(u):
            return [S[u] for S in inputs if u in S]

        def resolved_rec(u):
            """Most-resolved record: a branch record differing from the
            LCA's embodies a verdict; prefer it. A-first on conflicts."""
            lrec = Ls.get(u)
            for S in (As, Bs):
                if u in S and S[u] != lrec:
                    return S[u]
            return As[u] if u in As else (Bs[u] if u in Bs else lrec)

        def fold_depth(rec):
            """How many merge-dead ancestors this record still has to
            fold through (via resolved frames). Larger = less folded."""
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
            recs = all_recs(u)
            base = max(recs, key=fold_depth)          # least-folded frame path
            depth0 = fold_depth(base)
            # among records at the same fold depth AND same parent, prefer
            # the resolved slot value
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

        def kids_of(p): return [x for x in M if M[x][0] == p]

        def rescale_group(members, ulo, uhi, nlo, nhi):
            if ulo == nlo and uhi == nhi: return
            scale = (nhi - nlo) / (uhi - ulo)
            for k in members:
                pk, lo, hi = M[k]
                M[k] = (pk, nlo + (lo - ulo)*scale, nlo + (hi - ulo)*scale)

        def repair(p):
            ks = sorted(kids_of(p), key=lambda x: M[x][1])
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
                units = None
                if self.BLOCKS:
                    def contains(a, b):
                        return M[a][1] <= M[b][1] and M[b][2] <= M[a][2] and \
                               (M[a][1], M[a][2]) != (M[b][1], M[b][2])
                    maximal = [k for k in comp
                               if not any(contains(o, k) for o in comp if o != k)]
                    rest = [k for k in comp if k not in maximal]
                    if rest:
                        units = [('one', k, k) for k in maximal] + \
                                [('blk', max(rest), tuple(sorted(rest)))]
                if units is None:
                    units = [('one', k, k) for k in comp]
                units.sort(key=lambda t: -t[1])       # newest key topmost
                n = len(units)
                for r, (kind, _, payload) in enumerate(units):
                    nlo, nhi = uhi - Fraction(r+1)*W/n, uhi - Fraction(r)*W/n
                    if kind == 'one':
                        pk, olo, ohi = M[payload]
                        M[payload] = (pk, nlo, nhi)
                    else:
                        blo = min(M[k][1] for k in payload)
                        bhi = max(M[k][2] for k in payload)
                        rescale_group(payload, blo, bhi, nlo, nhi)
            for k in kids_of(p): repair(k)
        repair(0)
        return M


class RelSplitV2b(RelSplitV2a):
    name = 'relsplit-v2b'
    BLOCKS = True


def l25_third_party(D):
    """The pre-registered shape: a late full-slot claimant meets an
    integrated partition whose founder is dead. ok=False if any
    previously co-displayed pair flips."""
    R0 = D.apply(D.init(), ('ins', 6, 0))
    RM = D.apply(D.init(), ('ins', 10, 0))
    M1 = D.merge(D.init(), RM, D.copy(R0))
    M1p = D.apply(D.apply(D.copy(M1), ('ins', 16, 6)), ('ins', 22, 6))
    pre = D.read(M1p)
    RD = D.apply(D.copy(R0), ('del', 6))
    F = D.merge(D.copy(R0), M1p, RD)
    mid = D.read(F)
    RT = D.apply(D.init(), ('ins', 30, 0))
    F2 = D.read(D.merge(D.init(), F, RT))
    seen = set()
    for r in (pre, mid):
        for i in range(len(r)):
            for j in range(i+1, len(r)):
                seen.add((r[i], r[j]))
    flips = [(b, a) for (a, b) in seen
             if a in F2 and b in F2 and F2.index(b) < F2.index(a)]
    return (not flips), f"pre={pre} mid={mid} final={F2} flips={flips}"


if __name__ == '__main__':
    import pbt
    from random import Random
    from contest_tree import ce_subordination_escape, ce_retroactive_subordination
    RGA = {d.name: d for d in L.DESIGNS}['tombstoned']

    for D in (RelSplitV2a(), RelSplitV2b()):
        print(f"==== {D.name} ====")
        bad, _ = pbt.run_execution(D, Random(194), 2, 4, 2, 0.3, 0.4)
        print(f"  fold-frame CM (seed 194): {'CLEAN' if not bad else bad}")
        for nm, fn in (('CE-escape', ce_subordination_escape),
                       ('CE-retro', ce_retroactive_subordination)):
            ok, detail = fn(D)
            print(f"  {nm}: {'survives' if ok else 'REFUTED  ' + detail}")
        ok, detail = l25_third_party(D)
        print(f"  L25-third-party: {'PASS' if ok else 'FAIL  ' + detail}")
        for nm, fn in (('L25', L.l25_verdict), ('L23', L.l23_verdict), ('L24', L.l24_verdict)):
            r = fn(D); print(f"  {nm}: {'PASS' if r['ok'] else 'FAIL'}")
        v = L.three_branch_verdict(D, *L.L22[1:])
        print(f"  L22: {'PASS' if v['S3topo'] else 'FAIL ' + str(v['reads'])}")
        for name, lca, a, b, runs in L.MERGE_TESTS:
            vv = L.merge_verdict(D, lca, a, b, runs)
            badk = [k for k in ('S3','S4','S6','S7','DUP','IDL','S5') if k in vv and not vv[k]]
            if badk: print(f"  {name}: FAIL {badk}")
        for name, _, script in L.SEQ_TESTS:
            vv = L.seq_verdict(D, script)
            if not (vv.get('S1') and vv.get('S2')): print(f"  {name}: FAIL")
        f, _ = pbt.sweep(D, 120)
        print(f"  DAG PBT 120: {'CLEAN' if not f else str(len(f))+' FAIL, first '+str(f[0])}")
        if not f:
            f2, _ = pbt.sweep(D, 300, seed0=7, n_replicas=6, n_rounds=12)
            print(f"  DAG PBT 300 (6 rep, 12 rounds): "
                  f"{'CLEAN' if not f2 else str(len(f2))+' FAIL, first '+str(f2[0])}")
        # metadata: the million-character question, at 10k
        s = D.init(); N = 10_000
        s = D.apply(s, ('ins', 1, 0))
        for i in range(2, N+1): s = D.apply(s, ('ins', i, i-1))
        for i in range(1, N):   s = D.apply(s, ('del', i))
        print(f"  10k chain: live={len(s)} state entries={len(s)} (no stamps, no ledger)")
