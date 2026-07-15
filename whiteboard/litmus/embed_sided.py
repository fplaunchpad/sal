#!/usr/bin/env python3
"""
embed_sided.py -- the SIDED embed (two-sidedness as a parameter), step 2 of
whiteboard/sided-embed-design-note.md. Task #82.

Two models of one datatype, lockstep-asserted (machine-checked
faithfulness, the EmbedTree/EmbedTreeCode pattern):

  * SidedChain -- the semantics: sided chains (tuples of (side, ts)),
    display = descending marker-lex with the sided alphabet
        (R, t) < marker < (L, t')   with L MIRRORED (newer adjacent).
  * SidedCode  -- the carrier: bit-string coordinates, one block per level:
        block = sideBit ++ (C(delta) if R else complement(C(delta)))
    parsed back to symbols for comparison. The complement of C is
    order-reversing prefix-free at identical lengths -- exactly the mirrored
    L order. Lockstep(SidedChain, SidedCode) = unique decodability +
    order-embedding of the sided carrier, machine-checked.

Side selection is a GENERATION POLICY, not a datatype choice:

  * policy 'rga'   -- always (R, anchor): the all-R fragment. Expected
    lockstep-EXACT with the current one-sided embed (EmbedTreeCode), L19
    dirty (the fan), everything else as today.
  * policy 'fugue' -- right child of the left neighbor when it has no right
    children (ever, tombstone-style over the grow-only policy tree), else
    left child of the successor. Expected: L19 FLIPS CLEAN (backward runs
    become L-chains), credential family stays clean, DAG PBT clean.

Run: python3 embed_sided.py
"""

import litmus as L
import pbt
from embed_tree import (EmbedTreeCode, credential_cm, l25_third_party,
                        ce_subordination_escape, ce_retroactive_subordination)

R, LFT = 'R', 'L'


def C(d):
    b = bin(d)[2:]
    return '1' * (len(b) - 1) + '0' + b[1:]


def comp(w):
    return ''.join('1' if c == '0' else '0' for c in w)


def decodeC(bits, i):
    """Decode one C codeword at offset i; return (delta, next offset)."""
    j = i
    while bits[j] == '1':
        j += 1
    header = j - i          # L-1 ones
    j += 1                  # the terminating 0
    Lw = header + 1
    payload = bits[j:j + header]
    j += header
    return (1 << (Lw - 1)) + (int(payload, 2) if payload else 0), j


# ============================================================ the semantics
class SidedChain(L.Design):
    name = 'sided-chain'
    policy = 'fugue'

    # state: (live set, chains: x -> tuple[(side, ts)], tree: x -> (side, parent))
    # chains/tree are grow-only order+policy metadata (the policy is
    # generation-time and may consult anything replica-local; Fugue's own
    # side rule consults tombstones the same way).
    def init(self):
        return (set(), {}, {})

    def copy(self, s):
        return (set(s[0]), dict(s[1]), dict(s[2]))

    def fp(self, s):
        live, chains, _ = s
        return frozenset((x, chains[x]) for x in live)

    # ---- ordering: descending marker-lex over the sided alphabet
    @staticmethod
    def key(chain):
        k = [(1, t) if side == R else (3, -t) for side, t in chain]
        k.append((2, 0))
        return tuple(k)

    def read(self, s):
        live, chains, _ = s
        return sorted(live, key=lambda x: self.key(chains[x]), reverse=True)

    # ---- generation policy: pick (side, parent) for "insert x after a"
    def choose(self, s, x, a):
        live, chains, tree = s
        if self.policy == 'rga':
            return (R, a)
        # Fugue: between a and its successor n (over the FULL policy tree,
        # dead included -- the tombstone-visible successor)
        order = sorted(chains.keys(), key=lambda y: self.key(chains[y]),
                       reverse=True)
        if a == 0:
            n = order[0] if order else None
        else:
            i = order.index(a)
            n = order[i + 1] if i + 1 < len(order) else None
        has_r = any(p == a and sd == R for (sd, p) in tree.values())
        if not has_r or n is None:
            return (R, a)
        return (LFT, n)

    def apply(self, s, it):
        live, chains, tree = s
        if it[0] == 'ins':
            _, x, a = it
            side, parent = self.choose(s, x, a)
            chains[x] = chains.get(parent, ()) + ((side, x),)
            tree[x] = (side, parent)
            live.add(x)
        else:
            live.discard(it[1])
        return s

    def merge(self, Ls, As, Bs):
        ll, lc, lt = Ls
        al, ac, at = As
        bl, bc, bt = Bs
        live = ({x for x in al if x in bl or x not in ll} |
                {x for x in bl if x not in ll and x not in al})
        chains = {**lc, **ac, **bc}
        tree = {**lt, **at, **bt}
        return (live, chains, tree)


# ============================================================ the carrier
class SidedCode(SidedChain):
    name = 'sided-code'

    # state gains coords: x -> bit string (grow-only alongside chains; the
    # datatype proper stores only live coords -- chains/tree here remain the
    # policy metadata as above, coords are the actual sort keys).
    def init(self):
        return (set(), {}, {}, {})

    def copy(self, s):
        return (set(s[0]), dict(s[1]), dict(s[2]), dict(s[3]))

    def fp(self, s):
        live, _, _, coords = s
        return frozenset((x, coords[x]) for x in live)

    @staticmethod
    def parse_key(bits):
        """Parse a sided coordinate into comparison symbols + marker."""
        k, i = [], 0
        while i < len(bits):
            side = bits[i]
            i += 1
            if side == '1':                      # R block: C(delta)
                d, i2 = decodeC(bits, i)
                k.append((1, d))
            else:                                # L block: complement(C(delta))
                # complement the remainder lazily: decode C on flipped bits
                d, i2 = decodeC(comp(bits[i:]), 0)
                i2 += i
                k.append((3, -d))
            i = i2
        k.append((2, 0))
        return tuple(k)

    def read(self, s):
        live, _, _, coords = s
        return sorted(live, key=lambda x: self.parse_key(coords[x]),
                      reverse=True)

    def apply(self, s, it):
        live, chains, tree, coords = s
        if it[0] == 'ins':
            _, x, a = it
            side, parent = self.choose((live, chains, tree), x, a)
            pts = chains[parent][-1][1] if parent != 0 and parent in chains \
                else 0
            delta = x - pts
            w = C(delta)
            block = ('1' + w) if side == R else ('0' + comp(w))
            coords[x] = coords.get(parent, '') + block
            chains[x] = chains.get(parent, ()) + ((side, x),)
            tree[x] = (side, parent)
            live.add(x)
        else:
            live.discard(it[1])
        return s

    def merge(self, Ls, As, Bs):
        ll, lc, lt, lco = Ls
        al, ac, at, aco = As
        bl, bc, bt, bco = Bs
        live = ({x for x in al if x in bl or x not in ll} |
                {x for x in bl if x not in ll and x not in al})
        return (live, {**lc, **ac, **bc}, {**lt, **at, **bt},
                {**lco, **aco, **bco})


def mkD(cls, policy):
    D = cls()
    D.policy = policy
    D.name = f'{cls.name}[{policy}]'
    return D


# ============================================================ the battery
def gauntlet(D, expect_l19_clean):
    bad = []
    ok, detail = credential_cm(D)
    if not ok:
        bad.append(f'credential CM: {detail}')
    ok, detail = l25_third_party(D)
    if not ok:
        bad.append(f'L25-third-party: {detail}')
    for nm, fn in (('CE-escape', ce_subordination_escape),
                   ('CE-retro', ce_retroactive_subordination)):
        ok, detail = fn(D)
        if not ok:
            bad.append(f'{nm}: {detail}')
    for nm, fn in (('L25', L.l25_verdict), ('L23', L.l23_verdict),
                   ('L24', L.l24_verdict)):
        r = fn(D)
        if not r['ok']:
            bad.append(nm)
    v = L.three_branch_verdict(D, *L.L22[1:])
    if not v['S3topo']:
        bad.append(f'L22: {v["reads"]}')
    for name, lca, a, b, runs in L.MERGE_TESTS:
        vv = L.merge_verdict(D, lca, a, b, runs)
        badk = [k for k in ('S3', 'S4', 'S6', 'DUP', 'IDL', 'S5')
                if k in vv and not vv[k]]
        if 'L19' in name and not expect_l19_clean:
            if 'S5' in badk:
                badk.remove('S5')      # known one-sided anomaly
        if badk:
            bad.append(f'{name}: {badk} out={vv.get("out")}')
    for name, _, script in L.SEQ_TESTS:
        vv = L.seq_verdict(D, script)
        if not (vv.get('S1') and vv.get('S2')):
            bad.append(f'{name}: S1/S2 out={vv.get("out")}')
    for name, lca, a, b, post in (L.L18, L.L20):
        vv = L.post_merge_verdict(D, lca, a, b, post)
        if not vv['S2']:
            bad.append(name)
    v = L.stale_fork_verdict(D, *L.L21[1:])
    if not all(v[k] for k in ('S3', 'S4', 'S6', 'DUP')):
        bad.append('L21')
    return bad


def lockstep_battery(D1, D2):
    """Reads of D1 and D2 must agree on every battery scenario."""
    mismatches = []
    for name, _, script in L.SEQ_TESTS:
        D1.begin(); _, r1 = L.run_replica(D1, D1.init(), script)
        D2.begin(); _, r2 = L.run_replica(D2, D2.init(), script)
        if r1 != r2:
            mismatches.append(f'seq {name}: {r1[-1]} vs {r2[-1]}')
    for name, lca, a, b, _ in L.MERGE_TESTS:
        outs = []
        for D in (D1, D2):
            D.begin()
            Ls, _ = L.run_replica(D, D.init(), lca)
            As, _ = L.run_replica(D, Ls, a)
            Bs, _ = L.run_replica(D, Ls, b)
            outs.append(D.read(D.merge(Ls, As, Bs)))
        if outs[0] != outs[1]:
            mismatches.append(f'merge {name}: {outs[0]} vs {outs[1]}')
    return mismatches


if __name__ == '__main__':
    print('==== sided embed: the battery is the judge ====')
    for policy, expect19 in (('fugue', True), ('rga', False)):
        for cls in (SidedChain, SidedCode):
            D = mkD(cls, policy)
            bad = gauntlet(D, expect_l19_clean=expect19)
            tag = 'CLEAN' if not bad else 'FAIL'
            extra = ' (L19 expected clean: two-sided)' if expect19 else \
                    ' (L19 exempted: known one-sided anomaly)'
            print(f'  {D.name:22} gauntlet: {tag}{extra}')
            for b in bad:
                print(f'      {b}')
    print('==== L19 verdicts explicitly ====')
    l19 = next(t for t in L.MERGE_TESTS if 'L19' in t[0])
    for policy in ('fugue', 'rga'):
        D = mkD(SidedChain, policy)
        vv = L.merge_verdict(D, l19[1], l19[2], l19[3], l19[4])
        print(f'  {D.name:22} S5={vv["S5"]}  out={vv["out"]}')
    print('==== faithfulness: chain vs code lockstep ====')
    for policy in ('fugue', 'rga'):
        mism = lockstep_battery(mkD(SidedChain, policy),
                                mkD(SidedCode, policy))
        print(f'  [{policy}] chain~code: '
              f'{"EXACT" if not mism else "MISMATCH"}')
        for m in mism[:5]:
            print(f'      {m}')
    print('==== all-R fragment vs the one-sided embed ====')
    mism = lockstep_battery(mkD(SidedChain, 'rga'), EmbedTreeCode())
    print(f'  sided[rga]~embed-code: {"EXACT" if not mism else "MISMATCH"}')
    for m in mism[:5]:
        print(f'      {m}')
    print('==== DAG PBT ====')
    for policy in ('fugue', 'rga'):
        for cls in (SidedChain, SidedCode):
            D = mkD(cls, policy)
            f, _ = pbt.sweep(D, 120)
            print(f'  {D.name:22} PBT 120: '
                  f'{"CLEAN" if not f else str(len(f)) + " FAIL, first " + str(f[0])}')
