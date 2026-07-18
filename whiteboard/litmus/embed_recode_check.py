#!/usr/bin/env python3
"""embed_recode_check -- the RE-CODING THEOREM's Python twin (#97).

Model: the flat-coordinate embed RGA exactly as EmbedRGA.lean (records
(id, elem, coord-bit-string), mint = anchor prefix ++ enc(delta), read =
descending key sort, delete = pure removal, merge = OR-set survival).
Codeword generator imported from the litmus embed artifact (EmbedTreeCode.C,
the flipped-gamma binary code); nothing existing is modified.

Checked here:
  A. a concrete live-tree compaction rho_hat (stable-prefix map: re-mint
     live records against nearest live ancestors, newest-first deltas
     k..1) leaves reads identical, at the cut and under continued ops,
     concurrency and merges included; the T1 state correspondence
     (recoded coord == rho_hat(original coord)) holds record for record;
  B. the negative control: an injective, extension-commuting but
     NON-order-preserving remap (deltas reversed) CHANGES reads;
  C. coordinate-size reduction measured on a delete-heavy chain.
"""
import random
import sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from embed_tree import EmbedTreeCode

enc_bin = EmbedTreeCode.C                      # C(1)='0', C(2)='100', ...
def enc_unary(d): return '1' * d + '0'

def key(c): return ''.join('2' if b == '1' else '1' for b in c) + '3'

# ---------------------------------------------------------------- datatype
def ins(s, t, elem, pi, a, enc):
    if t in s: return s
    s[t] = (elem, pi + enc(t - a)); return s

def dele(s, x): s.pop(x, None); return s

def read_ids(s):  # display order: descending key
    return sorted(s, key=lambda t: key(s[t][1]), reverse=True)

def read(s): return [(t, s[t][0]) for t in read_ids(s)]

def merge(l, a, b):
    surv = (set(a) & set(b)) | (set(a) - set(l)) | (set(b) - set(l))
    return {t: (a[t] if t in a else b[t]) for t in surv}

# --------------------------------------------------- stable-prefix re-map
def make_rho_hat(s_cut, enc, reverse=False):
    """Live-tree re-mint. reverse=True is the negative control (injective,
    ext-commuting, order-breaking)."""
    live = sorted(s_cut, key=lambda t: len(s_cut[t][1]))
    coord = {t: s_cut[t][1] for t in live}
    def parent(t):
        best = ''
        for u in live:
            cu = coord[u]
            if u != t and coord[t].startswith(cu) and len(cu) > len(best):
                best = cu
        return best                                  # '' = root
    kids = {}
    for t in live: kids.setdefault(parent(t), []).append(t)
    rho = {'': ''}
    def build(pc):
        ch = sorted(kids.get(pc, []), key=lambda t: key(coord[t]), reverse=True)
        n = len(ch)
        for i, t in enumerate(ch):                   # newest first
            d = (i + 1) if reverse else (n - i)      # reversed = control
            rho[coord[t]] = rho[pc] + enc(d)
            build(coord[t])
    build('')
    prefixes = sorted(rho, key=len, reverse=True)
    def rho_hat(c):
        for p in prefixes:
            if c.startswith(p): return rho[p] + c[len(p):]
        return c
    return rho_hat

def remap_state(s, rho_hat):
    return {t: (e, rho_hat(c)) for t, (e, c) in s.items()}

def coord_bits(s): return sum(len(c) for _, c in s.values())

# ------------------------------------------------------------ directed D1
def directed_worked_example():
    """The note's worked example, unary code, hand-derived pins."""
    s = {}
    ins(s, 1, 'a', '', 0, enc_unary); ins(s, 2, 'b', s[1][1], 1, enc_unary)
    ins(s, 3, 'c', s[2][1], 2, enc_unary); dele(s, 1); dele(s, 2)
    assert s == {3: ('c', '101010')}, s
    rho_hat = make_rho_hat(s, enc_unary)
    sr = remap_state(s, rho_hat)
    assert sr == {3: ('c', '10')}, sr
    # beyond the cut: d under c (t=6), e at root (t=7)
    ins(s, 6, 'd', s[3][1], 3, enc_unary); ins(s, 7, 'e', '', 0, enc_unary)
    ins(sr, 6, 'd', sr[3][1], 3, enc_unary); ins(sr, 7, 'e', '', 0, enc_unary)
    assert read(s) == read(sr) == [(7, 'e'), (3, 'c'), (6, 'd')], (read(s), read(sr))
    assert {t: rho_hat(c) for t, (_, c) in s.items()} == \
           {t: c for t, (_, c) in sr.items()}          # T1 correspondence
    return coord_bits(s), coord_bits(sr)               # 24, 16 by hand

def directed_negative_control():
    """>=2 live siblings; the reversed-delta remap must flip the read."""
    s = {}
    ins(s, 1, 'x', '', 0, enc_bin); ins(s, 2, 'y', '', 0, enc_bin)
    ins(s, 3, 'z', '', 0, enc_bin)
    good = remap_state(s, make_rho_hat(s, enc_bin))
    bad = remap_state(s, make_rho_hat(s, enc_bin, reverse=True))
    assert read(good) == read(s) == [(3, 'z'), (2, 'y'), (1, 'x')]
    assert read(bad) != read(s), (read(bad), read(s))
    return read(s), read(bad)

def directed_delete_heavy(n=200):
    s = {}
    ins(s, 1, 0, '', 0, enc_bin)
    for i in range(2, n + 1): ins(s, i, i, s[i - 1][1], i - 1, enc_bin)
    for i in range(1, n): dele(s, i)
    before = coord_bits(s)
    sr = remap_state(s, make_rho_hat(s, enc_bin))
    assert read(sr) == read(s)
    return before, coord_bits(sr)

# ------------------------------------------------------------- randomized
def random_trial(seed):
    rng = random.Random(seed)
    s, t = {}, 0
    n_pre = rng.randrange(10, 40)
    for _ in range(n_pre):
        t += 1
        if s and rng.random() < 0.35:
            dele(s, rng.choice(list(s)))
        else:
            a = rng.choice([0] + list(s))
            ins(s, t, t, s[a][1] if a else '', a, enc_bin)
    rho_hat = make_rho_hat(s, enc_bin)
    sr = remap_state(s, rho_hat)
    if read(sr) != read(s): return f'cut read diverges seed={seed}'
    # fork two replicas beyond the cut; A takes even stamps, B odd
    worlds = {'A': (dict(s), dict(sr)), 'B': (dict(s), dict(sr))}
    base = t + 1
    for rep, par in (('A', 0), ('B', 1)):
        orig, rec = worlds[rep]
        tt = base + par
        for _ in range(rng.randrange(4, 12)):
            if orig and rng.random() < 0.3:
                x = rng.choice(list(orig)); dele(orig, x); dele(rec, x)
            else:
                a = rng.choice([0] + list(orig))
                pi = orig[a][1] if a else ''
                pir = rec[a][1] if a else ''
                if pir != rho_hat(pi):                     # H3/factorization
                    return f'anchor translation mismatch seed={seed}'
                ins(orig, tt, tt, pi, a, enc_bin)
                ins(rec, tt, tt, pir, a, enc_bin)
            if read(rec) != read(orig):
                return f'{rep} read diverges seed={seed}'
            tt += 2
    mo = merge(s, worlds['A'][0], worlds['B'][0])
    mr = merge(sr, worlds['A'][1], worlds['B'][1])
    if read(mr) != read(mo): return f'merge read diverges seed={seed}'
    for x in mo:
        if mr[x][1] != rho_hat(mo[x][1]):
            return f'T1 correspondence fails at {x} seed={seed}'
    return None

def randomized(n=500):
    fails = [f for f in (random_trial(s) for s in range(n)) if f]
    return n, fails

# ----------------------------------------------------------------- driver
if __name__ == '__main__':
    print('==== embed re-coding check (#97) ====')
    b, a = directed_worked_example()
    print(f'  D1 worked example (unary): reads identical, T1 exact; '
          f'coord bits {b} -> {a}')
    orig, bad = directed_negative_control()
    print(f'  D2 negative control: good remap read-identical; reversed-delta '
          f'remap flips {[t for t, _ in orig]} -> {[t for t, _ in bad]}  '
          f'(order preservation is load-bearing)')
    b, a = directed_delete_heavy()
    print(f'  D3 delete-heavy 200-chain (binary code): coord bits {b} -> {a} '
          f'({b/a:.0f}x)')
    n, fails = randomized(500)
    print(f'  R  randomized states (pre-cut history + cut + concurrent '
          f'continuation + merge): {n - len(fails)}/{n} PASS')
    for f in fails[:5]: print('     FAIL:', f)
    print('==== VERDICT ====')
    ok = not fails
    print(f'  reads identical under re-coding : {"PASS" if ok else "FAIL"}')
    print( '  negative control flips reads    : PASS (asserted)')
    print( '  size reduction                  : measured above')
    sys.exit(0 if ok else 1)
