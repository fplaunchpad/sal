#!/usr/bin/env python3
"""Session strong list (per-observer timeline consistency) probe — 2026-07-12.

Reruns the exact shared multi-replica corpus of anomaly_matrix.py (same seeds,
same 12,000 trials), but partitions the display log per replica line instead of
pooling: line A = init reads + every epoch's opsA reads + every merged read;
line B = same with opsB; line R3 (stale trials) = init reads + r3ops reads +
the final stale-merge read. Ancestor (init) and merged reads are charged to
every line that holds them — the inclusive, adversarial choice: more edges per
observer, more chance of a cycle.

Question: Shesha fails global strong list (833/12,000 pooled-log cycle trials,
forced by §7 I2). Does the failure ever materialize inside a SINGLE observer's
own display history? Conjecture (from the I2 directed-witness hand-check): no —
the cycle needs displays pooled across observers.

The pooled log is recomputed alongside as a corpus-identity cross-check: its
cycle-trial count must reproduce the report's 833.

Run: python3 session_e_check.py [--quick]
"""
import sys
from anomaly_matrix import Obs, Shesha, build_trials


def run_trial_session(impl, trial):
    pooled = Obs()
    lines = {'A': Obs(), 'B': Obs(), 'R3': Obs()}
    has_r3 = trial['stale'] is not None

    def do(s, op, observers):
        if op[0] == 'ins': impl.insert(s, op[1], op[2])
        else: impl.delete(s, op[1])
        show(impl.read(s), observers)

    def show(r, observers):
        pooled.display(r)
        for o in observers: lines[o].display(r)

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
    return pooled, lines


def main():
    quick = '--quick' in sys.argv
    trials = build_trials(500 if quick else 5000, 100 if quick else 1000)
    impl = Shesha()
    pooled_cycles = {'epoch': 0, 'stale': 0}
    session_cycles = {'epoch': 0, 'stale': 0}
    per_line = {'A': 0, 'B': 0, 'R3': 0}
    pooled_only = 0          # trials with a pooled cycle but no per-line cycle
    witnesses = []
    for idx, (mode, trial) in enumerate(trials):
        kind = 'epoch' if trial['stale'] is None else 'stale'
        pooled, lines = run_trial_session(impl, trial)
        pc = not pooled.acyclic()
        bad = [nm for nm, ob in lines.items() if not ob.acyclic()]
        if pc: pooled_cycles[kind] += 1
        if bad:
            session_cycles[kind] += 1
            for nm in bad: per_line[nm] += 1
            if len(witnesses) < 5:
                witnesses.append((idx, mode, kind, bad,
                                  {nm: lines[nm].find_cycle() for nm in bad}))
        elif pc:
            pooled_only += 1
        if (idx + 1) % 2000 == 0:
            print(f'  ... {idx + 1}/{len(trials)}: pooled cycle trials='
                  f'{sum(pooled_cycles.values())}, per-observer cycle trials='
                  f'{sum(session_cycles.values())}', flush=True)

    n = len(trials)
    print(f'\ncorpus: {n} trials (identical seeds to anomaly_matrix.py)')
    print(f'pooled  (global e) : {sum(pooled_cycles.values())}/{n} cycle trials '
          f'(epoch {pooled_cycles["epoch"]}, stale {pooled_cycles["stale"]}) '
          f'— report expects 833/12000')
    print(f'session (per-line) : {sum(session_cycles.values())}/{n} cycle trials '
          f'(epoch {session_cycles["epoch"]}, stale {session_cycles["stale"]}) '
          f'by line: {per_line}')
    print(f'pooled-cycle trials with NO per-line cycle: {pooled_only}')
    for (idx, mode, kind, bad, cyc) in witnesses:
        print(f'\nPER-OBSERVER CYCLE WITNESS: trial {idx} ({mode}, {kind}) '
              f'lines {bad}: {cyc}')
    if not witnesses:
        print('\nno per-observer cycle in any trial: every replica\'s own display '
              'history admits a timeline; the global cycles live only in the '
              'cross-observer union.')


if __name__ == '__main__':
    main()
