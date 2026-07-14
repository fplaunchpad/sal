#!/usr/bin/env python3
"""
sibling_tree — the SIBLING-LINKS representation (KC, 2026-07-14 evening).
STATUS: EXPERIMENT.

KC's conjecture (HS1): a version whose state stores, per node, its birth
parent and a SIBLING LINK (the node it displaced at insert time) — with
delete = pointer splice — is observationally equivalent to the rationals
version (contest-A, itself machine-equivalent to the tombstoned RGA).
Falsifier: any lockstep read divergence; minimize it.

Pre-registered candidate divergence shape (the machine decides if real):
concurrent same-level runs. Sibling links glue a newcomer to what it
displaced (insertion context); timestamp keys sort the level globally.
Branch A stacks 2 then 5 over 1; branch B stacks 4 over 1. Links read
[4,5,2,1] (5 stays glued above 2); rationals/RGA read [5,4,2,1].

HS2 (independent of HS1): does the sibling version itself meet the
contract (battery + DAG PBT: FLIP/CONV/LIVE/DUP)? If it diverges from
RGA but is contract-clean, it is a DIFFERENT datatype (possibly with
run-gluing at levels), not a bug.

STATE  id -> (par, sib, dig)
  par: current parent (rewritten by folds to nearest live ancestor)
  sib: current sibling link — the node this one sits directly above at
       its level; 0 = bottom. Rewritten only by splices when the target
       dies.
  dig: inherited dead-ancestor timestamps (ALWAYS-inherit rule — the
       fixed decision established by contest_tree's two refutations).

READ  per level (children of p): same-sib groups ordered newest-first by
  (dig ++ id); display = each node sits above its sib target, i.e.
  block(x) = blocks of x's displacers (newest first) ++ [x]; level =
  blocks of the bottom group. DFS into children after each node.

DELETE d
  - children of d: par := d.par; dig := d.dig+(d,) ++ own; those at the
    bottom of d's internal level (sib == 0) get sib := d.sib (the splice:
    the block takes d's place).
  - displacers of d (same level, sib == d): retarget sib := top child of
    d if any, else d.sib (they stay above whatever stands where d stood).
  - d's record removed.

MERGE  OR-set survival; per survivor take the most-folded record (longest
  dig); resolve par through merge-dead ancestors accumulating digs (as in
  contest-A); resolve sib by walking dead targets' records (sib := that
  record's sib). Simplification, noted: the merge's sib-walk skips the
  "top child" retarget of the local rule; if the resolved sib lands on a
  different level than the node, sib := 0. The controls below are the
  check on these choices.

CONTROLS
  C1 sequential agreement: on single-replica histories the sibling and
     rational versions must read identically (both are the insertion
     order); disagreement = implementation bug, not evidence.
  C2 the always-inherit rationals design (contest-A) is the lockstep
     reference; it is already machine-equivalent to the tombstoned RGA.
"""
from fractions import Fraction
import litmus as L
from contest_tree import ContestTreeA


def negkey(dig, uid):
    return tuple(-t for t in dig) + (-uid,)


class SiblingTree(L.Design):
    name = 'sibling-links'

    def init(self): return {}
    def copy(self, s): return dict(s)
    def fp(self, s): return frozenset(s.items())

    # ---- level order ----
    def _level_order(self, s, p):
        C = [x for x in s if s[x][0] == p]
        groups = {}
        for x in C:
            groups.setdefault(s[x][1], []).append(x)
        for g in groups.values():
            g.sort(key=lambda x: negkey(s[x][2], x))
        out = []
        def block(x):
            for y in groups.get(x, []):
                block(y)
            out.append(x)
        for r in groups.get(0, []):
            block(r)
        # top of the level displays first: reverse emission order
        return out[::-1] if False else self._reorder(out, groups)

    def _reorder(self, out, groups):
        # block() appends displacers (newest first) then the target, so a
        # stack [top..bottom] emits top-first already; bottom-group roots
        # were emitted newest-first with their stacks. Display = as emitted.
        return out

    def read(self, s):
        res = []
        def dfs(p):
            for x in self._level_order(s, p):
                res.append(x)
                dfs(x)
        dfs(0)
        return res

    # ---- local operations ----
    def apply(self, s, it):
        if it[0] == 'ins':
            _, x, a = it
            p = a if a != 0 else 0
            lvl = self._level_order(s, p)
            top = lvl[0] if lvl else 0
            s[x] = (p, top, ())
        else:
            d = it[1]
            if d not in s:
                return s
            dp, dsib, ddig = s.pop(d)
            contrib = ddig + (d,)
            kids = [c for c in s if s[c][0] == d]
            kid_lvl = self._level_order(dict(s), d) if kids else []
            top_kid = kid_lvl[0] if kid_lvl else 0
            for c in kids:
                _, csib, cdig = s[c]
                s[c] = (dp, dsib if csib == 0 else csib, contrib + cdig)
            for y in list(s):
                yp, ysib, ydig = s[y]
                if ysib == d:
                    s[y] = (yp, top_kid if top_kid else dsib, ydig)
        return s

    # ---- merge ----
    def merge(self, Ls, As, Bs):
        surv = (set(Ls) & set(As) & set(Bs)) | (set(As) - set(Ls)) | (set(Bs) - set(Ls))

        def rec(u):
            best = None
            for S in (Ls, As, Bs):
                if u in S:
                    r = S[u]
                    if best is None or len(r[2]) > len(best[2]):
                        best = r
            return best

        out = {}
        for u in surv:
            par, sib, dig = rec(u)
            # par walk (accumulate digs, always-inherit)
            acc, p, guard = [], par, 0
            while p != 0 and p not in surv:
                rp = rec(p)
                if rp is None: break
                acc.append(rp[2] + (p,))
                p = rp[0]
                guard += 1
                if guard > 100000: raise RuntimeError('cycle')
            pre = ()
            for c in reversed(acc): pre = pre + c
            # sib walk
            sb, guard = sib, 0
            while sb != 0 and sb not in surv:
                rs = rec(sb)
                if rs is None:
                    sb = 0; break
                sb = rs[1]
                guard += 1
                if guard > 100000: raise RuntimeError('cycle')
            out[u] = (p, sb, pre + dig)
        # a sib link must stay within its level; else drop to bottom group
        for u in list(out):
            p, sb, dig = out[u]
            if sb != 0 and (sb not in out or out[sb][0] != p):
                out[u] = (p, 0, dig)
        return out


if __name__ == '__main__':
    import pbt, random
    SIB, RAT = SiblingTree(), ContestTreeA()

    print("== C1 sequential agreement (single replica, random ops) ==")
    disagree = 0
    for seed in range(300):
        rng = random.Random(seed)
        s1, s2, nid, live = SIB.init(), RAT.init(), 1, []
        for _ in range(rng.randint(1, 25)):
            if live and rng.random() < 0.3:
                d = rng.choice(live); live.remove(d)
                it = ('del', d)
            else:
                a = rng.choice([0] + live)
                it = ('ins', nid, a); live.append(nid); nid += 1
            s1, s2 = SIB.apply(s1, it), RAT.apply(s2, it)
            if SIB.read(s1) != RAT.read(s2):
                disagree += 1
                if disagree == 1:
                    print(f"  FIRST DISAGREEMENT seed={seed} after {it}:")
                    print(f"    sibling: {SIB.read(s1)}")
                    print(f"    rational:{RAT.read(s2)}")
                break
    print(f"  {'AGREE on all 300 histories' if not disagree else str(disagree)+'/300 histories disagree'}")

    print("== pre-registered probe: concurrent same-level runs ==")
    for D, nm in ((SIB, 'sibling '), (RAT, 'rational')):
        base = D.apply(D.init(), ('ins', 1, 0))
        A = D.apply(D.apply(D.copy(base), ('ins', 2, 0)), ('ins', 5, 0))
        B = D.apply(D.copy(base), ('ins', 4, 0))
        print(f"  {nm}: merged {D.read(D.merge(D.copy(base), A, B))}")

    class Lockstep(L.Design):
        name = 'sib-vs-rational'
        def init(self): return (SIB.init(), RAT.init())
        def copy(self, s): return (SIB.copy(s[0]), RAT.copy(s[1]))
        def fp(self, s): return (SIB.fp(s[0]), RAT.fp(s[1]))
        def _chk(self, s, w):
            a, b = SIB.read(s[0]), RAT.read(s[1])
            assert a == b, f"DIVERGE at {w}: sib={a} rat={b}"
            return s
        def apply(self, s, it):
            return self._chk((SIB.apply(s[0], it), RAT.apply(s[1], it)), it)
        def read(self, s):
            self._chk(s, 'read'); return SIB.read(s[0])
        def merge(self, Ls, As, Bs):
            return self._chk((SIB.merge(Ls[0], As[0], Bs[0]),
                              RAT.merge(Ls[1], As[1], Bs[1])), 'merge')

    print("== HS1 lockstep: sibling vs rational (120 exec) ==")
    f, _ = pbt.sweep(Lockstep(), 120)
    print(f"  {'EQUIVALENT 120/120' if not f else 'diverges: ' + str(f[0])}")

    print("== HS2: the sibling design on its own contract ==")
    for name, lca, a, b, runs in L.MERGE_TESTS:
        v = L.merge_verdict(SIB, lca, a, b, runs)
        bad = [k for k in ('S3','S4','S6','S7','DUP','IDL','S5') if k in v and not v[k]]
        if bad: print(f"  {name:28} FAIL {bad}")
    for name, _, script in L.SEQ_TESTS:
        v = L.seq_verdict(SIB, script)
        if not (v.get('S1') and v.get('S2')): print(f"  {name:28} FAIL")
    for nm, fn in (('L23', L.l23_verdict), ('L24', L.l24_verdict), ('L25', L.l25_verdict)):
        if not fn(SIB)['ok']: print(f"  {nm} FAIL")
    v = L.three_branch_verdict(SIB, *L.L22[1:])
    if not v['S3topo']: print(f"  L22 FAIL: {v['reads']}")
    f, _ = pbt.sweep(SIB, 120)
    print(f"  battery: failures listed above (none listed = pass); DAG PBT: "
          f"{'CLEAN' if not f else str(len(f))+' FAIL, first '+str(f[0])}")
