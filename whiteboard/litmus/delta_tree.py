#!/usr/bin/env python3
"""
The delta-tree design (KC), faithful implementation.

State: id -> (parent, loF, hiF) with (loF, hiF) in [0,1] RELATIVE to the
parent's range (the delta). Absolute range = affine composition down the root
path. Strictly dead-free: delete removes the record and ISOMETRICALLY FOLDS
its children (compose the dead node's fractions into theirs, re-parent) --
every survivor's absolute position is arithmetically unchanged.

Merge (l = LCA):
  1. survival: OR-set on ids.
  2. values: shared nodes take the LCA's (parent, fractions) -- the canonical
     topology-free base frame, deliberately reverting branch-local repairs;
     branch-born nodes bring their branch's. Ratios are frame-free, so no
     normalization pass exists.
  3. dead-chain folding: survivors whose parent is merge-dead fold through
     the dead chain using the LCA's records (dead-in-merge => live-in-LCA).
  4. local repair (KC's overlap-split): per parent, in RELATIVE coordinates,
     connected components of overlapping child fractions have their union
     re-split into equal slots in timestamp order (newest topmost); only the
     members' own fractions are rewritten -- descendants are relative and
     follow automatically. Singletons untouched. Recurse.

Read: DFS, children by descending (loF, id) -- newest first.
"""
from fractions import Fraction
import litmus as L


class DeltaTree(L.Design):
    name = 'delta-tree'

    def init(self): return {}
    def copy(self, s): return dict(s)
    def fp(self, s): return frozenset(s.items())

    def _kids(self, s, p):
        return sorted((x for x in s if s[x][0] == p),
                      key=lambda x: (s[x][1], x), reverse=True)

    # ---- local operations (generation = application at the origin) ----
    def apply(self, s, it):
        if it[0] == 'ins':
            _, x, a = it
            p = a if a != 0 else 0
            base = max((s[k][2] for k in s if s[k][0] == p), default=Fraction(0))
            w = Fraction(1) - base
            s[x] = (p, base + w/4, base + w/2)
        else:
            d = it[1]
            if d in s:
                dp, dl, dh = s.pop(d)
                dw = dh - dl
                for c in list(s):
                    if s[c][0] == d:                      # isometric fold
                        _, cl, ch = s[c]
                        s[c] = (dp, dl + dw*cl, dl + dw*ch)
        return s

    def read(self, s):
        out = []
        def dfs(u):
            for c in self._kids(s, u):
                out.append(c); dfs(c)
        dfs(0); return out

    # ---- merge ----
    def merge(self, Lst, Ast, Bst):
        surv = (set(Lst) & set(Ast) & set(Bst)) | (set(Ast) - set(Lst)) | (set(Bst) - set(Lst))
        # 2. values: LCA-revert for shared nodes; branch values for branch-born
        M = {}
        for u in surv:
            if u in Lst:   M[u] = Lst[u]
            elif u in Ast: M[u] = Ast[u]
            else:          M[u] = Bst[u]
        # 3. fold dead chains via the LCA's records
        def lrec(u):
            if u in Lst: return Lst[u]
            if u in Ast: return Ast[u]                    # defensive; analysis says L suffices
            return Bst[u]
        for u in list(M):
            p, lo, hi = M[u]
            guard = 0
            while p != 0 and p not in surv:
                pp, plo, phi = lrec(p)
                w = phi - plo
                lo, hi = plo + w*lo, plo + w*hi
                p = pp
                guard += 1
                if guard > 10000: raise RuntimeError('fold cycle')
            M[u] = (p, lo, hi)
        # 4. local overlap-split repair, per level, in relative coordinates
        def repair(p):
            ks = sorted((x for x in M if M[x][0] == p), key=lambda x: M[x][1])
            comps, cur, cmax = [], [], None
            for k in ks:
                lo, hi = M[k][1], M[k][2]
                if cur and lo < cmax:
                    cur.append(k); cmax = max(cmax, hi)
                else:
                    if cur: comps.append(cur)
                    cur, cmax = [k], hi
            if cur: comps.append(cur)
            for comp in comps:
                if len(comp) >= 2:
                    ulo = min(M[k][1] for k in comp)
                    uhi = max(M[k][2] for k in comp)
                    W, n = uhi - ulo, len(comp)
                    for r, k in enumerate(sorted(comp, reverse=True)):   # ts desc, newest topmost
                        M[k] = (p, uhi - Fraction(r+1)*W/n, uhi - Fraction(r)*W/n)
            for k in (x for x in M if M[x][0] == p):
                repair(k)
        repair(0)
        return M


if __name__ == '__main__':
    D = DeltaTree()
    print("== battery ==")
    for name, lca, a, b, runs in L.MERGE_TESTS:
        v = L.merge_verdict(D, lca, a, b, runs)
        bad = [k for k in ('S3','S4','S6','S7','DUP','IDL','S5') if k in v and not v[k]]
        print(f"  {name:28} {'PASS' if not bad else 'FAIL '+str(bad):20} {v.get('out')}")
    for name, _, script in L.SEQ_TESTS:
        v = L.seq_verdict(D, script)
        ok = v.get('S1') and v.get('S2')
        print(f"  {name:28} {'PASS' if ok else 'FAIL':20} {v.get('out')}")
    for name, lca, a, b, post in (L.L18, L.L20):
        v = L.post_merge_verdict(D, lca, a, b, post)
        print(f"  {name:28} {'PASS' if v['S2'] else 'FAIL':20} {v['merged']} -> {v['out']}")
    v = L.stale_fork_verdict(D, *L.L21[1:])
    print(f"  {L.L21[0]:28} {'PASS' if all(v[k] for k in ('S3','S4','S6','DUP')) else 'FAIL'}")
    v = L.three_branch_verdict(D, *L.L22[1:])
    print(f"  {L.L22[0]:28} {'PASS' if v['S3topo'] else 'FAIL: '+str(v['reads'])}")
    v = L.l23_verdict(D)
    print(f"  L23 rescaled-children        {'PASS' if v['ok'] else 'FAIL: P '+str(v['P'])+' Q '+str(v['Q'])}")
    v = L.l24_verdict(D)
    print(f"  L24 frame mixing             {'PASS' if v['ok'] else 'FAIL: '+str(v['flips'])+' -> '+str(v['out'])}")

    import pbt
    print("\n== randomized DAG PBT ==")
    fails, skipped = pbt.sweep(D, 120)
    print(f"  default (4 replicas, 8 rounds): "
          f"{'CLEAN' if not fails else str(len(fails))+' FAILING, first: '+str(fails[0])}"
          f"   [skipped: {skipped}]")


# =============================================================================
# REPAIR CANDIDATE (also refuted): source-consistent folding — fold each node
# through the SAME input that provided its value. Fixes L25 (the fold then
# uses the branch's repaired frame, preserving its verdict) but STILL fails
# the DAG PBT (41/120): mechanism 2, REPAIR NON-LOCALITY — re-slotting a node
# within one overlap family changes its numeric relation to nodes OUTSIDE the
# family, so a pair whose tie was decided by ts at one merge arrives at a
# causally disjoint merge with diverged geometry and gets re-decided by
# position (machine-checked flip (10,4), pbt seed 1).
# =============================================================================
class DeltaTreeSF(DeltaTree):
    name = 'delta-tree-sf'
    def merge(self, Lst, Ast, Bst):
        from fractions import Fraction
        surv = (set(Lst)&set(Ast)&set(Bst)) | (set(Ast)-set(Lst)) | (set(Bst)-set(Lst))
        M = {}
        for u in surv:
            src = Lst if u in Lst else (Ast if u in Ast else Bst)
            p, lo, hi = src[u]
            g = 0
            while p != 0 and p not in surv:
                pp, plo, phi = src[p] if p in src else (Lst[p] if p in Lst else (Ast[p] if p in Ast else Bst[p]))
                w = phi - plo
                lo, hi = plo + w*lo, plo + w*hi
                p = pp; g += 1
                if g > 10000: raise RuntimeError('fold cycle')
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
                if len(comp) >= 2:
                    ulo = min(M[k][1] for k in comp); uhi = max(M[k][2] for k in comp)
                    W, n = uhi-ulo, len(comp)
                    for r, k in enumerate(sorted(comp, reverse=True)):
                        M[k] = (p, uhi - Fraction(r+1)*W/n, uhi - Fraction(r)*W/n)
            for k in (x for x in M if M[x][0] == p): repair(k)
        repair(0)
        return M


# =============================================================================
# v3 — THE CORRECTED DESIGN (KC: "almost right; the merge wasn't observing
# invariants"). Machine-checked CLEAN: full battery (except one-sided L19)
# + DAG PBT 120/120 and 300/300 (6 replicas, 12 rounds).
#
# State = KC's delta-tree rendering (parent + relative fractions; carve;
# isometric fold — local ops UNCHANGED) + a birth-parent LEDGER
# (id -> birth parent, retained incl. dead entries; live-reachable scope).
#
# The three invariants the earlier merges violated, now observed:
#  I1 ARBITRATION FROM IDENTITY ONLY: every order decision at a merge is
#     computed from the ledger (per-level birth chains, ts-desc per level,
#     prefix-first) — never from current geometry (which repairs perturb) and
#     never from frame-mixed folds. The v2 diagnosis (KC's "compare with
#     path-2 at the flip") showed the identity half of the state sufficed and
#     the geometric half was corrupted.
#  I2 GEOMETRY IS A RENDERING: the merge re-derives fractions realizing the
#     canonical order; reads stay geometric (never consult the ledger).
#  I3 RENDER/CARVE COMPATIBILITY: the render reproduces sequential-carve
#     geometry (oldest-lowest, quarter slices, HEADROOM above) so post-merge
#     states are indistinguishable from sequentially carved ones — v2's
#     residual PBT failures were zero-width slices minted after a render
#     that filled the parent's space to 1.
#
# The synthesis: the delta tree is the runtime (O(1)-ish geometric reads,
# isometric deletes); the birth chains are the arbitration substrate,
# consulted only at merges. Not strictly dead-free (the triangle held: dead
# ids persist in the ledger while live descendants reference them), but the
# retention is minimal — one parent id per node, no slot data, no
# materialized paths, nothing read-side.
# =============================================================================
class DeltaTreeV3(L.Design):
    name = 'delta-tree-v3'
    def init(self): return ({}, {})
    def copy(self, s): return (dict(s[0]), dict(s[1]))
    def fp(self, s): return (frozenset(s[0].items()), frozenset(s[1].items()))
    def _kids(self, r, p):
        return sorted((x for x in r if r[x][0] == p),
                      key=lambda x: (r[x][1], x), reverse=True)
    def apply(self, s, it):
        r, led = s
        if it[0] == 'ins':
            _, x, a = it
            p = a if a != 0 else 0
            base = max((r[k][2] for k in r if r[k][0] == p), default=Fraction(0))
            w = Fraction(1) - base
            r[x] = (p, base + w/4, base + w/2)
            led[x] = p
        else:
            d = it[1]
            if d in r:
                dp, dl, dh = r.pop(d); dw = dh - dl
                for c in list(r):
                    if r[c][0] == d:
                        _, cl, ch = r[c]
                        r[c] = (dp, dl + dw*cl, dl + dw*ch)
        return (r, led)
    def read(self, s):
        r, _ = s
        out = []
        def dfs(u):
            for c in self._kids(r, u):
                out.append(c); dfs(c)
        dfs(0); return out
    def _chain(self, led, x):
        ch = []
        while x != 0:
            ch.append(-x); x = led[x]
        ch.reverse(); return ch
    def merge(self, Ls, As, Bs):
        (lr, ll), (ar, al), (br, bl) = Ls, As, Bs
        led = dict(ll); led.update(al); led.update(bl)
        surv = (set(lr) & set(ar) & set(br)) | (set(ar) - set(lr)) | (set(br) - set(lr))
        def live_par(x):
            p = led[x]
            while p != 0 and p not in surv: p = led[p]
            return p
        par = {u: live_par(u) for u in surv}
        kids = {}
        for u in surv: kids.setdefault(par[u], []).append(u)
        chains = {u: self._chain(led, u) for u in surv}
        r = {}
        def render(p):
            ks = sorted(kids.get(p, []), key=lambda x: chains[x])
            base = Fraction(0)
            for k in reversed(ks):                     # oldest first: sequential-carve geometry
                w = Fraction(1) - base
                r[k] = (p, base + w/4, base + w/2)
                base = base + w/2
                render(k)
        render(0)
        return (r, led)
