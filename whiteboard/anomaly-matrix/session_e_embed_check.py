#!/usr/bin/env python3
"""Step 4 companion (2026-07-12): machine-validation of Theorem O's construction
(sibling-linked-proof.md §5½ — chain/session strong list for Shesha).

The proof reduces session strong list to three ingredients; each is checked
here empirically, per replica line, so any gap in the proof surfaces as a
concrete counterexample:

  (NR) no relive — an element that leaves a line's display never returns, and
       an arriving element was never displayed on that line before
       (Corollary NR, from Lemma V causal-removal liveness + growing pasts);
  (SP) step preservation — consecutive reads of a line agree on the order of
       their common elements (Theorem P restricted to consecutive chain states);
  (GE) greedy embedding — the proof's explicit witness: process reads in chain
       order; splice each maximal block of arrivals immediately after its
       preceding survivor (else immediately before its following survivor,
       else append); the final total order T must contain every read of the
       line as a subsequence.

Corpora: the shared 12,000-trial matrix corpus (same seeds as
anomaly_matrix.py) and the 50,000-trial adversarial sweep (same seeds as
session_e_search.py stage 2).

Run: python3 session_e_embed_check.py [--quick]
"""
import sys
import random
from anomaly_matrix import Shesha, build_trials
from session_e_search import gen_adv_trial

IMPL = Shesha()


def run_trial_reads(impl, trial):
    """Same topology and observer-charging as session_e_check.run_trial_session,
    but records each line's full read sequence in chain order."""
    lines = {'A': [], 'B': [], 'R3': []}
    has_r3 = trial['stale'] is not None

    def do(s, op, observers):
        if op[0] == 'ins': impl.insert(s, op[1], op[2])
        else: impl.delete(s, op[1])
        show(impl.read(s), observers)

    def show(r, observers):
        for o in observers: lines[o].append(list(r))

    cur = impl.new()
    init_obs = ('A', 'B', 'R3') if has_r3 else ('A', 'B')
    for op in trial['init']: do(cur, op, init_obs)
    fork = impl.clone(cur) if has_r3 else None
    for (opsA, opsB, _newlive) in trial['epochs']:
        A, B = impl.clone(cur), impl.clone(cur)
        for op in opsA: do(A, op, ('A',))
        for op in opsB: do(B, op, ('B',))
        M = impl.merge(cur, A, B)
        show(impl.read(M), ('A', 'B'))
        cur = M
    if has_r3:
        r3ops, _final_live = trial['stale']
        R3 = impl.clone(fork)
        for op in r3ops: do(R3, op, ('R3',))
        M = impl.merge(fork, cur, R3)
        show(impl.read(M), ('A', 'B', 'R3'))
    return lines


def embed_line(reads):
    """Theorem O's greedy construction. Returns None on success, else a
    failure tag naming the proof step that broke."""
    if not reads: return None
    T = list(reads[0])
    displayed = set(reads[0])
    prev = reads[0]
    for k in range(1, len(reads)):
        r = reads[k]
        prevset = set(prev)
        S = [x for x in r if x in prevset]
        arrivals = [x for x in r if x not in prevset]
        for x in arrivals:                                     # (NR)
            if x in displayed: return ('NR-FAIL', k, x)
        if [x for x in prev if x in set(S)] != S:              # (SP)
            return ('SP-FAIL', k, prev, r)
        i = 0
        while i < len(r):                                      # (GE) splice blocks
            if r[i] in prevset:
                i += 1
                continue
            j = i
            while j < len(r) and r[j] not in prevset: j += 1
            block = r[i:j]
            if i > 0: pos = T.index(r[i - 1]) + 1              # after preceding survivor
            elif j < len(r): pos = T.index(r[j])               # before following survivor
            else: pos = len(T)                                 # no survivors: append
            T[pos:pos] = block
            i = j
        displayed |= set(r)
        prev = r
    for k, r in enumerate(reads):                              # the theorem's claim
        it = iter(T)
        if not all(x in it for x in r):
            return ('EMBED-FAIL', k, r, T)
    return None


def check_corpus(name, trials_iter, n):
    fails = []
    lines_checked = reads_checked = 0
    for idx, trial in enumerate(trials_iter):
        lines = run_trial_reads(IMPL, trial)
        for nm, reads in lines.items():
            if not reads: continue
            lines_checked += 1
            reads_checked += len(reads)
            bad = embed_line(reads)
            if bad:
                fails.append((idx, nm, bad))
                print(f'FAIL {name} trial {idx} line {nm}: {bad[:2]}', flush=True)
        if (idx + 1) % 10000 == 0:
            print(f'  ... {name} {idx + 1}/{n}, fails={len(fails)}', flush=True)
    print(f'{name}: {n} trials, {lines_checked} lines, {reads_checked} reads '
          f'embedded, failures={len(fails)}', flush=True)
    return fails


def main():
    quick = '--quick' in sys.argv
    n12 = 1200 if quick else 12000
    n50 = 2000 if quick else 50000

    corpus = build_trials(n12 // 12 * 5, n12 // 12)
    fails = check_corpus('matrix-corpus', (t for _m, t in corpus), len(corpus))

    adv = (gen_adv_trial(random.Random(4242000 + t)) for t in range(n50))
    fails += check_corpus('adversarial', adv, n50)

    print('\n' + '=' * 70)
    if fails:
        print(f'{len(fails)} FAILURE(S) — the corresponding Theorem O proof step '
              f'is broken; first: {fails[0]}')
    else:
        print('ALL CLEAN: no-relive, step preservation, and the greedy embedding '
              'hold on every replica line — Theorem O\'s construction is '
              'machine-validated end to end.')


if __name__ == '__main__':
    main()
