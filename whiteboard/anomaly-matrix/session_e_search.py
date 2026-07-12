#!/usr/bin/env python3
"""Step 3 (2026-07-12): adversarial search for a per-observer session-e cycle in Shesha.

Stage 1 — exhaustive-by-total-size directed search over small topologies:
  init ops (<=3), then 1 or 2 diverge/merge epochs (A/B, <=3 ops each in the
  1-epoch shape, <=2 otherwise), optionally a stale third replica R3 forked
  after init (<=2 ops) merged last with LCA = fork. For every op-structure,
  every anchor/delete choice over the locally-live set, and every LEGAL
  timestamp assignment = linear extension of the causal clock order:
    - program order within each location ascends;
    - init ids below everything;
    - epoch-2 ids above all epoch-1 ids (state sync carries the Lamport clock,
      including ids whose elements died — tombstone-freedom does not launder
      the clock);
    - R3 ids above init ONLY — they may interleave anywhere among epoch ids.
      (The random corpus never generates this region: its stale replica always
      draws the highest band.)
  A script is a HIT if any single replica line's own display log (per
  session_e_check partitioning) contains a cycle, or a per-observer pair flip
  (the latter would be a column-d violation; reported separately).

Stage 2 — biased randomized sweep past the corpus envelope: up to 4 epochs,
  delete-heavy (del_p in {0.3,0.5,0.7}), small anchor pools, optional stale R3
  whose id stream is LOW-interleaved among the epoch ids (channel residues
  mod 3 keep ids distinct while violating no clock constraint).

Run: python3 session_e_search.py [--max-total N] [--random N] [--stage 1|2]
"""
import sys
import time
import random
from anomaly_matrix import Obs, Shesha
from session_e_check import run_trial_session

IMPL = Shesha()


# ---------------------------------------------------------------- stage 1

def branch_seqs(live, base, n):
    """All op sequences of exactly n ops for one branch from live set `live`,
    allocating symbolic insert ids base, base+1, ... in program order."""
    if n == 0:
        yield []
        return
    ll = sorted(live)
    for a in [0] + ll:
        for rest in branch_seqs(live | {base}, base + 1, n - 1):
            yield [('ins', base, a)] + rest
    for x in ll:
        for rest in branch_seqs(live - {x}, base, n - 1):
            yield [('del', x)] + rest


def live_after(live, ops):
    l = set(live)
    for op in ops:
        if op[0] == 'ins': l.add(op[1])
        else: l.discard(op[1])
    return l


def live_merge(L, A, B):
    return (A & B) | (A - L) | (B - L)


def linear_extensions(preds):
    """All total orders of the symbols consistent with preds (sym -> set of
    symbols that must be placed earlier)."""
    syms = frozenset(preds)
    def rec(remaining, placed, acc):
        if not remaining:
            yield list(acc)
            return
        for s in sorted(remaining):
            if preds[s] <= placed:
                yield from rec(remaining - {s}, placed | {s}, acc + [s])
    yield from rec(syms, frozenset(), [])


def sub_ops(ops, ts):
    return [(('ins', ts[op[1]], (ts[op[2]] if op[2] != 0 else 0))
             if op[0] == 'ins' else ('del', ts[op[1]])) for op in ops]


def syms_of(ops):
    return [op[1] for op in ops if op[0] == 'ins']


BASES = {'INIT': 100, 'A1': 200, 'B1': 300, 'A2': 400, 'B2': 500, 'R3': 600}
TOPOLOGIES = {                     # loc list; per-loc op caps
    'E1':   ['A1', 'B1'],
    'E2':   ['A1', 'B1', 'A2', 'B2'],
    'E1R3': ['A1', 'B1', 'R3'],
    'E2R3': ['A1', 'B1', 'A2', 'B2', 'R3'],
}


def compositions(total, caps):
    if not caps:
        if total == 0: yield []
        return
    for k in range(min(total, caps[0]) + 1):
        for rest in compositions(total - k, caps[1:]):
            yield [k] + rest


def stage1(max_total):
    t0 = time.time()
    runs = 0
    hits = []

    def check(trial, tag):
        nonlocal runs
        runs += 1
        if runs % 200000 == 0:
            print(f'  ... {runs} runs, {time.time() - t0:.0f}s, hits={len(hits)}',
                  flush=True)
        _pooled, lines = run_trial_session(IMPL, trial)
        for nm, ob in lines.items():
            flips = ob.antisym_violations()
            if flips:
                hits.append(('PAIR-FLIP', tag, nm, flips, trial))
                print(f'PER-OBSERVER PAIR FLIP (d-violation!) line {nm} {tag}: '
                      f'{flips}\n  trial: {trial}', flush=True)
            if not ob.acyclic():
                hits.append(('CYCLE', tag, nm, ob.find_cycle(), trial))
                print(f'PER-OBSERVER CYCLE line {nm} {tag}: {ob.find_cycle()}'
                      f'\n  trial: {trial}', flush=True)

    for total in range(3, max_total + 1):
        runs_at = runs
        for topo, locs in TOPOLOGIES.items():
            caps = [3 if topo == 'E1' else 2] * len(locs)
            for n_init in range(0, min(3, total) + 1):
                n_post = total - n_init
                for init_ops in branch_seqs(frozenset(), BASES['INIT'], n_init):
                    live0 = live_after(set(), init_ops)
                    for comp in compositions(n_post, caps):
                        na1, nb1 = comp[0], comp[1]
                        has_e2 = 'A2' in locs
                        for opsA1 in branch_seqs(frozenset(live0), BASES['A1'], na1):
                            for opsB1 in branch_seqs(frozenset(live0), BASES['B1'], nb1):
                                live1 = live_merge(live0,
                                                   live_after(live0, opsA1),
                                                   live_after(live0, opsB1))
                                e2_choices = ([([], [])] if not has_e2 else
                                              [(oa, ob)
                                               for oa in branch_seqs(frozenset(live1), BASES['A2'], comp[2])
                                               for ob in branch_seqs(frozenset(live1), BASES['B2'], comp[3])])
                                nr3 = comp[-1] if 'R3' in locs else 0
                                r3_choices = ([None] if 'R3' not in locs else
                                              list(branch_seqs(frozenset(live0), BASES['R3'], nr3)))
                                for (opsA2, opsB2) in e2_choices:
                                    for opsR3 in r3_choices:
                                        groups = {'INIT': syms_of(init_ops),
                                                  'E1': syms_of(opsA1) + syms_of(opsB1),
                                                  'E2': syms_of(opsA2) + syms_of(opsB2),
                                                  'R3': syms_of(opsR3 or [])}
                                        preds = {}
                                        for loc, ops in (('INIT', init_ops), ('A1', opsA1),
                                                         ('B1', opsB1), ('A2', opsA2),
                                                         ('B2', opsB2), ('R3', opsR3 or [])):
                                            chain = syms_of(ops)
                                            for i, s in enumerate(chain):
                                                preds[s] = set(chain[:i])
                                        for s in groups['E1']:
                                            preds[s] |= set(groups['INIT'])
                                        for s in groups['E2']:
                                            preds[s] |= set(groups['INIT']) | set(groups['E1'])
                                        for s in groups['R3']:
                                            preds[s] |= set(groups['INIT'])
                                        for ext in linear_extensions(preds):
                                            ts = {s: i + 1 for i, s in enumerate(ext)}
                                            epochs = [(sub_ops(opsA1, ts), sub_ops(opsB1, ts), None)]
                                            if has_e2:
                                                epochs.append((sub_ops(opsA2, ts), sub_ops(opsB2, ts), None))
                                            trial = {'init': sub_ops(init_ops, ts),
                                                     'epochs': epochs,
                                                     'stale': ((sub_ops(opsR3, ts), None)
                                                               if opsR3 is not None else None)}
                                            check(trial, f'{topo}/total{total}')
        print(f'total={total} exhausted: {runs - runs_at} runs this size, '
              f'{runs} cumulative, {time.time() - t0:.0f}s, hits={len(hits)}',
              flush=True)
    return runs, hits


# ---------------------------------------------------------------- stage 2

def gen_adv_trial(rng):
    """Deeper/deleteful than the corpus; optional LOW-interleaved stale ids.
    Post-init ids are 100 + 3k + channel (A=0, B=1, R3=2): distinct by residue;
    epoch counters ascend across epochs (clock-valid), R3's counter starts back
    at 0 so its ids interleave among epoch-1/2 ids (clock-valid: R3 forked at
    init and only its own program order plus init bound its clock)."""
    del_p = rng.choice((0.3, 0.5, 0.7))
    init = []
    live = set()
    for k in range(rng.randint(1, 4)):
        init.append(('ins', k + 1, rng.choice([0] + sorted(live))))
        live.add(k + 1)

    def gen_ops(live, chan, k0, nops):
        ops = []
        k = k0
        l = set(live)
        for _ in range(nops):
            ll = sorted(l)
            if rng.random() < del_p and ll:
                x = rng.choice(ll)
                ops.append(('del', x))
                l.discard(x)
            else:
                x = 100 + 3 * k + chan
                k += 1
                ops.append(('ins', x, rng.choice([0] + ll)))
                l.add(x)
        return ops, l, k

    epochs = []
    k = 0
    fork_live = set(live)
    for _e in range(rng.randint(1, 4)):
        opsA, la, ka = gen_ops(live, 0, k, rng.randint(1, 5))
        opsB, lb, kb = gen_ops(live, 1, k, rng.randint(1, 5))
        k = max(ka, kb)
        live = live_merge(live, la, lb)
        epochs.append((opsA, opsB, None))
    stale = None
    if rng.random() < 0.5:
        opsR3, _l3, _k3 = gen_ops(fork_live, 2, 0, rng.randint(1, 3))
        stale = (opsR3, None)
    return {'init': init, 'epochs': epochs, 'stale': stale,
            'fork_live': fork_live}


def stage2(n_trials):
    t0 = time.time()
    pooled_cycles = 0
    hits = []
    for t in range(n_trials):
        rng = random.Random(4242000 + t)
        trial = gen_adv_trial(rng)
        pooled, lines = run_trial_session(IMPL, trial)
        if not pooled.acyclic(): pooled_cycles += 1
        for nm, ob in lines.items():
            if ob.antisym_violations():
                hits.append(('PAIR-FLIP', t, nm, ob.antisym_violations(), trial))
                print(f'PER-OBSERVER PAIR FLIP trial {t} line {nm}: '
                      f'{ob.antisym_violations()}\n  {trial}', flush=True)
            if not ob.acyclic():
                hits.append(('CYCLE', t, nm, ob.find_cycle(), trial))
                print(f'PER-OBSERVER CYCLE trial {t} line {nm}: '
                      f'{ob.find_cycle()}\n  {trial}', flush=True)
        if (t + 1) % 10000 == 0:
            print(f'  ... {t + 1}/{n_trials}, {time.time() - t0:.0f}s, '
                  f'pooled cycles={pooled_cycles}, hits={len(hits)}', flush=True)
    return pooled_cycles, hits


def main():
    argv = sys.argv[1:]
    max_total = int(argv[argv.index('--max-total') + 1]) if '--max-total' in argv else 6
    n_random = int(argv[argv.index('--random') + 1]) if '--random' in argv else 50000
    stage = argv[argv.index('--stage') + 1] if '--stage' in argv else 'both'

    all_hits = []
    if stage in ('1', 'both'):
        print(f'STAGE 1: exhaustive directed search, total ops 3..{max_total}')
        runs, hits = stage1(max_total)
        all_hits += hits
        print(f'stage 1 done: {runs} scripts run, hits={len(hits)}')
    if stage in ('2', 'both'):
        print(f'\nSTAGE 2: biased randomized sweep, {n_random} trials '
              f'(E<=4, del-heavy, low-interleaved stale ids)')
        pooled_cycles, hits = stage2(n_random)
        all_hits += hits
        print(f'stage 2 done: pooled (global-e) cycles={pooled_cycles}/{n_random}, '
              f'per-observer hits={len(hits)}')

    print('\n' + ('=' * 70))
    if all_hits:
        print(f'{len(all_hits)} PER-OBSERVER HIT(S) — session strong list REFUTED; '
              f'first: {all_hits[0]}')
    else:
        print('NO per-observer cycle and NO per-observer pair flip found: '
              'session strong list survives the directed search.')


if __name__ == '__main__':
    main()
