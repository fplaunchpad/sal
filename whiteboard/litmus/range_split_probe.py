"""KC's LOCAL overlap-split strategy, machine-checked.

Merge = survival + par-climb + ranges verbatim, then a LOCAL repair pass:
for each node, find connected components of overlapping child ranges; a
component with >= 2 members has its UNION re-split into equal slots in
timestamp order (newest topmost = displayed first); each member's subtree is
rescaled affinely into its slot. Singletons untouched -- no global rebalance.
"""
from fractions import Fraction
import litmus as L

class RangeSplit(L.RangeTS):
    name = 'range-split'
    def merge(self, Lst, Ast, Bst):
        M = L.RangeTS.merge(self, Lst, Ast, Bst)
        M = {k: v for k, v in M.items()}
        def kids_of(p): return [x for x in M if M[x][0] == p]
        def rescale(root, olo, ohi, nlo, nhi):
            """Affinely map root's stored range and its whole subtree."""
            def mapv(v): return nlo + (v - olo) * (nhi - nlo) / (ohi - olo)
            stack = [root]
            while stack:
                u = stack.pop()
                p, lo, hi = M[u]
                M[u] = (p, mapv(lo), mapv(hi))
                stack.extend(kids_of(u))
        def repair(p):
            ks = sorted(kids_of(p), key=lambda x: M[x][1])
            # connected components of interval overlap (sweep)
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
                    W = uhi - ulo
                    n = len(comp)
                    for rank, k in enumerate(sorted(comp, reverse=True)):  # ts desc
                        nlo = uhi - Fraction(rank + 1) * W / n
                        nhi = uhi - Fraction(rank) * W / n
                        _, olo, ohi = M[k]
                        rescale(k, olo, ohi, nlo, nhi)
            for k in kids_of(p):
                repair(k)
        repair(0)
        return M

D = RangeSplit()

# ---------- the full battery ----------
print("== battery (merge tests + probes) ==")
for name, lca, a, b, runs in L.MERGE_TESTS:
    v = L.merge_verdict(D, lca, a, b, runs)
    bad = [k for k in ('S3','S4','S6','S7','DUP','IDL','S5') if k in v and not v[k]]
    print(f"  {name:26} {'PASS' if not bad else 'FAIL '+str(bad):18} {v.get('out')}")
for name, lca, a, b, post in (L.L18, L.L20):
    v = L.post_merge_verdict(D, lca, a, b, post)
    print(f"  {name:26} {'PASS' if v['S2'] else 'FAIL'}             {v['merged']} -> {v['out']}")
v = L.stale_fork_verdict(D, *L.L21[1:])
print(f"  {L.L21[0]:26} {'PASS' if all(v[k] for k in ('S3','S4','S6','DUP')) else 'FAIL'}             {v['out']}")
v = L.three_branch_verdict(D, *L.L22[1:])
print(f"  {L.L22[0]:26} {'PASS' if v['S3topo'] else 'FAIL: '+str(v['reads'])}")

# ---------- the DEEP probe: descendants of rescaled nodes meet across topologies
print("\n== deep probe: post-split children, merged via two different topologies ==")
def deep(Dz):
    Dz.begin()
    L0,_ = L.run_replica(Dz, Dz.init(), [('ins',1,0)])
    B1,_ = L.run_replica(Dz, L0, [('ins',10,1)])
    B2,_ = L.run_replica(Dz, L0, [('ins',20,1)])
    B3,_ = L.run_replica(Dz, L0, [('ins',30,1)])
    # path P: (B1+B2) -> type 60 under 20 ; (B1+B3) -> type 61 under 30 ; merge
    M12 = Dz.merge(L0, B1, B2)
    X1  = Dz.apply(Dz.copy(M12), ('ins',60,20))
    M13 = Dz.merge(L0, B1, B3)
    Y1  = Dz.apply(Dz.copy(M13), ('ins',61,30))
    FP  = Dz.merge(B1, X1, Y1)                  # LCA = {1,10}
    # path Q: X1 meets B3 alone first, then Y1
    Mq  = Dz.merge(L0, X1, B3)                  # LCA = {1}
    FQ  = Dz.merge(M13, Mq, Y1)                 # LCA = {1,10,30}
    return Dz.read(FP), Dz.read(FQ)

for Dz in (D, L.RangeTS(), L.Path2(), L.GhostCF()):
    rp, rq = deep(Dz)
    print(f"  {Dz.name:12} P: {rp}   Q: {rq}   {'CONVERGED' if rp == rq else '*** DIVERGED ***'}")


# ============================================================================
# DEPTH-3 FINDING (KC's question: "same node, different ranges at merge"):
# children carved in DIFFERENT FRAMES of the same parent are mutually
# incomparable raw; naive per-node value picking flips a co-displayed pair
# (machine-checked: (62,61) flip). INVARIANT (frame coherence): every input is
# internally consistent, so each input's frame of a subtree is an affine image
# of the canonical slot; a child's value pulled back through ITS OWN input's
# parent-frame is frame-independent. STRATEGY (normalize-then-repair): choose
# the canonical range per node = the LCA's value (well-defined: any node in
# both branches is in the LCA; branch-born nodes have no conflict), rewrite
# every input's values through the affine map (input-frame -> canonical frame)
# top-down, THEN run the canonical overlap repair. RangeSplitN below; fixes
# the depth-3 flip, passes the battery (except one-sided L19).
# ============================================================================
class RangeSplitN(RangeSplit):
    name = 'range-splitN'
    def merge(self, Lst, Ast, Bst):
        surv = (set(Lst)&set(Ast)&set(Bst)) | (set(Ast)-set(Lst)) | (set(Bst)-set(Lst))
        def normalized(I):
            out = {}
            def walk(p, plo, phi, ilo, ihi):
                for c in [x for x in I if I[x][0] == p]:
                    _, clo, chi = I[c]
                    nlo = plo + (clo-ilo)*(phi-plo)/(ihi-ilo)
                    nhi = plo + (chi-ilo)*(phi-plo)/(ihi-ilo)
                    cl, ch = (Lst[c][1], Lst[c][2]) if c in Lst else (nlo, nhi)
                    out[c] = (p, cl, ch)
                    walk(c, cl, ch, I[c][1], I[c][2])
            walk(0, Fraction(0), Fraction(1), Fraction(0), Fraction(1))
            return out
        src = {}
        for I in (Lst, Ast, Bst):
            for k, v in normalized(I).items():
                src.setdefault(k, v)
        M = {u: src[u] for u in surv}
        def anc(u):
            for S in (Lst, Ast, Bst):
                if u in S: return S[u][0]
            return 0
        M = {u: (self._climb_par(M[u][0], surv, anc), M[u][1], M[u][2]) for u in M}
        return self._repair_all(M)
    def _climb_par(self, p, surv, anc):
        while p != 0 and p not in surv: p = anc(p)
        return p
    def _repair_all(self, M):
        def kids_of(p): return [x for x in M if M[x][0] == p]
        def rescale(root, olo, ohi, nlo, nhi):
            def mapv(v): return nlo + (v-olo)*(nhi-nlo)/(ohi-olo)
            st = [root]
            while st:
                u = st.pop(); p, lo, hi = M[u]
                M[u] = (p, mapv(lo), mapv(hi)); st.extend(kids_of(u))
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
                if len(comp) >= 2:
                    ulo = min(M[k][1] for k in comp); uhi = max(M[k][2] for k in comp)
                    W, n = uhi-ulo, len(comp)
                    for r, k in enumerate(sorted(comp, reverse=True)):
                        _, olo, ohi = M[k]
                        rescale(k, olo, ohi, uhi-Fraction(r+1)*W/n, uhi-Fraction(r)*W/n)
            for k in kids_of(p): repair(k)
        repair(0)
        return M
