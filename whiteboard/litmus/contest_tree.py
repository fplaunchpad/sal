#!/usr/bin/env python3
"""
contest_tree — the strictly-dead-free candidate from the order-merge design
session (KC, 2026-07-14 evening). STATUS: EXPERIMENT, not a result.

GOALS
  G1  Determine whether, in the MRDT/LCA model, a design retaining NO dead
      identifiers can satisfy the contract: S1 sequential soundness,
      pairwise display stability (FLIP-free, globally), topology
      convergence (CONV), forward non-interleaving (g). Dead-originated
      OPAQUE ORDER DATA (frozen digits: timestamps compared, never
      dereferenced) is permitted per KC's ruling; dead identifiers
      (dereferenceable names: ledger entries, tombstones) are not.
  G2  If G1 holds, establish the retention bound O(live + contested
      ancestry): purely sequential histories leave ZERO digits.
  NON-GOAL: matching RGA-dagger. Divergence on orphan shapes is expected
      and acceptable iff the contract holds. This design, if it survives,
      is a DIFFERENT sequence datatype, not a compaction of RGA.

HYPOTHESES (falsifiable; each falsifier is a runnable artifact here)
  H1  variant B (contest-only digit inheritance) passes the full battery
      (except one-sided L19) and the DAG PBT (FLIP/CONV/LIVE/DUP).
      Falsifier: any flip/divergence; minimize it and name the mechanism.
  H2  variant B's digits are empty on sequential histories (the 1M-chain
      scenario) and short under churn. Falsifier: digit growth without
      contests.
  H3  variant B diverges from RGA-dagger on orphan shapes (born-and-died
      arbiter, never contested). This is EXPECTED; the lockstep run
      characterizes the divergence set. A clean lockstep would instead
      suggest the digits are doing nothing (suspicious, investigate).
  H4  variant A (fold appends EVERY dead parent id — full anonymized
      chains) is observationally equivalent to the tombstoned RGA.
      This is the IMPLEMENTATION CONTROL: if A diverges from RGA-dagger,
      the merge here is buggy and no conclusion about B is licensed.

KNOWN RISKS, recorded before running (the machine decides):
  R1  cf-knowledge carrier loss: the contested flag of a node d may be
      known only to a branch in which d has since been folded away with no
      heirs; a later merge folding OTHER heirs via stale records drops
      d's contribution. Candidate flip mechanism.
  R2  cf flags may differ across merge topologies with equal event sets
      (read-CONV could hold while state-CONV fails, biting later).
  R3  contest marking is per-level (live parent at THAT merge); delete
      timing differences across topologies move levels.

STATE  id -> (par, lo, hi, dig, cf)
  (lo,hi) parent-relative fractions — rendering only, never compared
  across branches; dig — tuple of ids frozen onto the node by folds per
  the variant rule; cf — was this node ever party to a cross-branch
  same-level contest while alive (OR-monotone).

MERGE  OR-set survival; live parent + dig accumulation walking merge-dead
  ancestors via their surviving records (longest-dig record wins = latest
  fold knowledge); per-level canonical order = lex on (dig ++ [id]),
  newest first; contest marking of fresh-vs-fresh levels; carve-faithful
  render (invariants I2/I3 of the campaign).
"""
from fractions import Fraction
import litmus as L


class ContestTreeB(L.Design):
    name = 'contest-B'
    VA = False           # False: contest-only inheritance (hypothesis)

    def init(self): return {}
    def copy(self, s): return dict(s)
    def fp(self, s): return frozenset(s.items())

    def _kids(self, s, p):
        return sorted((x for x in s if s[x][0] == p),
                      key=lambda x: (s[x][1], x), reverse=True)

    # ---- local operations ----
    def apply(self, s, it):
        if it[0] == 'ins':
            _, x, a = it
            p = a if a != 0 else 0
            base = max((s[k][2] for k in s if s[k][0] == p), default=Fraction(0))
            w = Fraction(1) - base
            s[x] = (p, base + w/4, base + w/2, (), False)
        else:
            d = it[1]
            if d in s:
                dp, dl, dh, ddig, dcf = s.pop(d)
                dw = dh - dl
                contrib = ddig + ((d,) if (dcf or self.VA) else ())
                for c in list(s):
                    if s[c][0] == d:
                        _, cl, ch, cdig, ccf = s[c]
                        s[c] = (dp, dl + dw*cl, dl + dw*ch, contrib + cdig, ccf)
        return s

    def read(self, s):
        out = []
        def dfs(u):
            for c in self._kids(s, u):
                out.append(c); dfs(c)
        dfs(0); return out

    # ---- merge ----
    def merge(self, Ls, As, Bs):
        surv = (set(Ls) & set(As) & set(Bs)) | (set(As) - set(Ls)) | (set(Bs) - set(Ls))

        def rec(u):
            """Merged view of u: (par, dig) from the most-folded record
            (longest dig = latest knowledge); cf OR'd across records."""
            best, cf = None, False
            for S in (Ls, As, Bs):
                if u in S:
                    r = S[u]
                    if best is None or len(r[3]) > len(best[3]):
                        best = r
                    cf = cf or r[4]
            return (best[0], best[3], cf) if best else (None, (), False)

        out_par, out_dig, out_cf = {}, {}, {}
        for u in surv:
            par, dig, cf = rec(u)
            acc, p = [], par
            guard = 0
            while p != 0 and p not in surv:
                pp, pdig, pcf = rec(p)
                if pp is None: break          # locally-folded orphan: its
                acc.append(())                 # contribution is already in dig
                acc[-1] = pdig + ((p,) if (pcf or self.VA) else ())
                p = pp
                guard += 1
                if guard > 100000: raise RuntimeError('fold cycle')
            pre = ()
            for c in reversed(acc): pre = pre + c
            out_par[u], out_dig[u], out_cf[u] = p, pre + dig, cf

        freshA = {u for u in surv if u in As and u not in Ls}
        freshB = {u for u in surv if u in Bs and u not in Ls}
        bylevel = {}
        for u in surv: bylevel.setdefault(out_par[u], []).append(u)
        for p, ks in bylevel.items():
            fa = [u for u in ks if u in freshA]
            fb = [u for u in ks if u in freshB]
            if fa and fb:
                for u in fa + fb: out_cf[u] = True

        def negkey(u): return tuple(-t for t in out_dig[u]) + (-u,)
        r = {}
        def render(p):
            ks = sorted(bylevel.get(p, []), key=negkey)
            base = Fraction(0)
            for k in reversed(ks):
                w = Fraction(1) - base
                r[k] = (p, base + w/4, base + w/2, out_dig[k], out_cf[k])
                base = base + w/2
                render(k)
        render(0)
        return r


class ContestTreeA(ContestTreeB):
    name = 'contest-A'    # control: full anonymized chains
    VA = True


# =============================================================================
# V-C (also REFUTED): subordination-preserving inheritance — append d's ts on
# fold iff some live same-level node sorts above d. Kills V-B's countermodel
# class (the fatal config runs clean 200/200; PBT 32/120 -> 3/120) but falls
# to a 6-event countermodel of its own:
#
# RETROACTIVE SUBORDINATION (CE-C): sync {1}; A: del 1, ins 2@0; B: ins 3@1;
# merge -> [3,2] (1 dead, unsubordinated anywhere => 3 escapes with own key;
# verdict (3,2) minted). B': ins 4@0 lands ABOVE the still-live 1 in that
# branch => at the next merge sub_any(1) flips to True, the walk NOW appends
# 1's digit, and 3 demotes below 2: [4,2,3] — the co-displayed (3,2) FLIPS.
#
# MECHANISM: the inheritance CONDITION (is d subordinated?) is mutable,
# concurrently-accruing knowledge — it can differ between merges and between
# disjoint merge pairs processing the same death. A key minted under one
# answer is re-minted under the other. Together with V-B's SUBORDINATION
# ESCAPE this yields the session's sharpened negative claim:
#
#   THE INHERITANCE DECISION MUST BE A FUNCTION OF IMMUTABLE DATA.
#   Conditional-on-mutable-knowledge retention is non-convergent, however
#   the condition is chosen; always-inherit (V-A = full anonymized chains,
#   machine-checked == RGA-dagger) is the fixed decision, and retention
#   optimization must happen BELOW a fixed decision (e.g. stability-gated
#   digit compression), not inside it.
# =============================================================================
def negkey_of(dig, uid):
    return tuple(-t for t in dig) + (-uid,)


class ContestTreeC(ContestTreeB):
    name = 'contest-C'
    def _subordinated(self, S, d):
        dp, _, _, ddig, _ = S[d]
        kd = negkey_of(ddig, d)
        return any(negkey_of(S[y][3], y) < kd
                   for y in S if y != d and S[y][0] == dp)
    def apply(self, s, it):
        if it[0] == 'ins':
            return ContestTreeB.apply(self, s, it)
        d = it[1]
        if d in s:
            sub = self._subordinated(s, d)
            dp, dl, dh, ddig, dcf = s.pop(d)
            dw = dh - dl
            contrib = ddig + ((d,) if (sub or dcf) else ())
            for c in list(s):
                if s[c][0] == d:
                    _, cl, ch, cdig, ccf = s[c]
                    s[c] = (dp, dl + dw*cl, dl + dw*ch, contrib + cdig, ccf)
        return s
    def merge(self, Ls, As, Bs):
        surv = (set(Ls) & set(As) & set(Bs)) | (set(As) - set(Ls)) | (set(Bs) - set(Ls))
        def rec(u):
            best, cf = None, False
            for S in (Ls, As, Bs):
                if u in S:
                    r = S[u]
                    if best is None or len(r[3]) > len(best[3]): best = r
                    cf = cf or r[4]
            return (best[0], best[3], cf) if best else (None, (), False)
        def sub_any(u):
            return any(self._subordinated(S, u) for S in (Ls, As, Bs) if u in S)
        out_par, out_dig, out_cf = {}, {}, {}
        for u in surv:
            par, dig, cf = rec(u)
            acc, p, guard = [], par, 0
            while p != 0 and p not in surv:
                pp, pdig, pcf = rec(p)
                if pp is None: break
                acc.append(pdig + ((p,) if (pcf or sub_any(p)) else ()))
                p = pp; guard += 1
                if guard > 100000: raise RuntimeError('cycle')
            pre = ()
            for c in reversed(acc): pre = pre + c
            out_par[u], out_dig[u], out_cf[u] = p, pre + dig, cf
        freshA = {u for u in surv if u in As and u not in Ls}
        freshB = {u for u in surv if u in Bs and u not in Ls}
        bylevel = {}
        for u in surv: bylevel.setdefault(out_par[u], []).append(u)
        for p, ks in bylevel.items():
            if [u for u in ks if u in freshA] and [u for u in ks if u in freshB]:
                for u in ks:
                    if u in freshA or u in freshB: out_cf[u] = True
        r = {}
        def render(p):
            ks = sorted(bylevel.get(p, []),
                        key=lambda u: tuple(-t for t in out_dig[u]) + (-u,))
            base = Fraction(0)
            for k in reversed(ks):
                w = Fraction(1) - base
                r[k] = (p, base + w/4, base + w/2, out_dig[k], out_cf[k])
                base = base + w/2
                render(k)
        render(0)
        return r


def ce_subordination_escape(D):
    """V-B's 7-event countermodel. Returns (ok, detail): ok=True if the
    co-displayed pair (4,6) keeps its order through the merge."""
    s = D.init()
    for it in (('ins',1,0), ('ins',2,0), ('del',2), ('ins',3,1), ('ins',4,0)):
        s = D.apply(s, it)
    base = D.copy(s)
    A = D.apply(D.copy(base), ('ins', 6, 1))
    B = D.apply(D.apply(D.copy(base), ('ins', 5, 0)), ('del', 1))
    ra = D.read(A)
    m = D.read(D.merge(base, A, B))
    ok = not (ra.index(4) < ra.index(6) and m.index(6) < m.index(4))
    return ok, f"A={ra} merged={m}"


def ce_retroactive_subordination(D):
    """V-C's 6-event countermodel. ok=True if (3,2) keeps its order."""
    s0 = D.apply(D.init(), ('ins', 1, 0))
    A = D.apply(D.apply(D.copy(s0), ('del', 1)), ('ins', 2, 0))
    B = D.apply(D.copy(s0), ('ins', 3, 1))
    m1 = D.merge(D.copy(s0), A, B)
    r1 = D.read(m1)
    Bp = D.apply(D.copy(B), ('ins', 4, 0))
    m2 = D.read(D.merge(D.copy(B), Bp, m1))
    ok = not (r1.index(3) < r1.index(2) and m2.index(2) < m2.index(3))
    return ok, f"m1={r1} m2={m2}"


if __name__ == '__main__':
    import pbt
    print("==== minimized countermodels (regressions) ====")
    for D, ces in ((ContestTreeB(), ('escape',)), (ContestTreeC(), ('escape', 'retro'))):
        for ce in ces:
            fn = ce_subordination_escape if ce == 'escape' else ce_retroactive_subordination
            ok, detail = fn(D)
            print(f"  {D.name} vs CE-{ce}: {'survives' if ok else 'REFUTED'}  {detail}")
    RGA = {D.name: D for D in L.DESIGNS}['tombstoned']

    class Lockstep(L.Design):
        """Read-equality lockstep of a contest variant against RGA-dagger.
        Divergence raises with the reads; used for H3/H4."""
        def __init__(self, D, name):
            self.D, self.R, self.name = D, RGA, name
            self.divergences = []
        def init(self): return (self.D.init(), self.R.init())
        def copy(self, s): return (self.D.copy(s[0]), self.R.copy(s[1]))
        def fp(self, s): return (self.D.fp(s[0]), self.R.fp(s[1]))
        def _chk(self, s, w):
            a, b = self.D.read(s[0]), self.R.read(s[1])
            assert a == b, f"DIVERGE at {w}: {self.name}={a} rga={b}"
            return s
        def apply(self, s, it):
            return self._chk((self.D.apply(s[0], it), self.R.apply(s[1], it)), it)
        def read(self, s):
            self._chk(s, 'read'); return self.D.read(s[0])
        def merge(self, Ls, As, Bs):
            return self._chk((self.D.merge(Ls[0], As[0], Bs[0]),
                              self.R.merge(Ls[1], As[1], Bs[1])), 'merge')

    for D in (ContestTreeA(), ContestTreeB()):
        print(f"==== {D.name} ====")
        for name, lca, a, b, runs in L.MERGE_TESTS:
            v = L.merge_verdict(D, lca, a, b, runs)
            bad = [k for k in ('S3','S4','S6','S7','DUP','IDL','S5') if k in v and not v[k]]
            print(f"  {name:28} {'PASS' if not bad else 'FAIL '+str(bad)}")
        for name, _, script in L.SEQ_TESTS:
            v = L.seq_verdict(D, script)
            print(f"  {name:28} {'PASS' if v.get('S1') and v.get('S2') else 'FAIL'}")
        for name, lca, a, b, post in (L.L18, L.L20):
            v = L.post_merge_verdict(D, lca, a, b, post)
            print(f"  {name:28} {'PASS' if v['S2'] else 'FAIL'}")
        v = L.stale_fork_verdict(D, *L.L21[1:])
        print(f"  {L.L21[0]:28} {'PASS' if all(v[k] for k in ('S3','S4','S6','DUP')) else 'FAIL'}")
        v = L.three_branch_verdict(D, *L.L22[1:])
        print(f"  {L.L22[0]:28} {'PASS' if v['S3topo'] else 'FAIL: '+str(v['reads'])}")
        for nm, fn in (('L23', L.l23_verdict), ('L24', L.l24_verdict), ('L25', L.l25_verdict)):
            v = fn(D)
            print(f"  {nm:28} {'PASS' if v['ok'] else 'FAIL'}")
        fails, sk = pbt.sweep(D, 120)
        print(f"  DAG PBT 120: {'CLEAN' if not fails else str(len(fails))+' FAIL, first '+str(fails[0])}")

    print("==== H4 control: contest-A lockstep vs RGA-dagger ====")
    f, _ = pbt.sweep(Lockstep(ContestTreeA(), 'contest-A'), 120)
    print(f"  {'EQUIVALENT 120/120' if not f else 'DIVERGES: ' + str(f[0])}")
    print("==== H3: contest-B lockstep vs RGA-dagger (divergence EXPECTED) ====")
    f, _ = pbt.sweep(Lockstep(ContestTreeB(), 'contest-B'), 120)
    print(f"  {'no divergence in 120 (suspicious per H3)' if not f else 'diverges (expected): ' + str(f[0])}")

    print("==== H2 metadata: 10k chain, delete all but last ====")
    for D in (ContestTreeA(), ContestTreeB()):
        s = D.init(); N = 10_000
        s = D.apply(s, ('ins', 1, 0))
        for i in range(2, N+1): s = D.apply(s, ('ins', i, i-1))
        for i in range(1, N):   s = D.apply(s, ('del', i))
        x = next(iter(s))
        print(f"  {D.name}: live={len(s)} dig_len(survivor)={len(s[x][3])}")
