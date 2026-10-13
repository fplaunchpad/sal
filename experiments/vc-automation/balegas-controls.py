#!/usr/bin/env python3
"""Deterministic bounded refutation gate; no claim of implementation equivalence.

Explore every trace up to the reported depth, including zero amounts, guard
rejections, and duplicate delivery; a directed control covers stale snapshots. Local operations use the current
single-writer replica state. Each snapshot carries its independently recorded
causal event set. Compare max-merged payload queries and every cell with sums
over that event set, and check local/global rights safety. The Lean SPOTs check
the actual Lean definitions; this executable model separately checks the
published algorithm against event accounting. No random sampling or discards.
"""
from dataclasses import dataclass
from itertools import product
import json


@dataclass(frozen=True)
class Payload:
    R: tuple
    U: tuple


def zero(n):
    return Payload((0,) * (n * n), (0,) * n)


def rights(s, r, n):
    return (s.R[r*n+r] + sum(s.R[j*n+r] for j in range(n) if j != r)
            - sum(s.R[r*n+j] for j in range(n) if j != r) - s.U[r])


def value(s, n):
    return sum(s.R[i*n+i] - s.U[i] for i in range(n))


def effect(s, r, kind, amount, target, n):
    R, U = list(s.R), list(s.U)
    if kind == 'inc':
        R[r*n+r] += amount
    elif kind == 'dec':
        U[r] += amount
    else:
        R[r*n+target] += amount
    return Payload(tuple(R), tuple(U))


def join(a, b):
    return Payload(tuple(map(max, a.R, b.R)), tuple(map(max, a.U, b.U)))


def account(events, n):
    """Independent event semantics: mint, burn, or move scalar credit."""
    balances = [0] * n
    scalar = 0
    R, U = [0] * (n*n), [0] * n
    for _, r, kind, amount, target in events:
        if kind == 'inc':
            scalar += amount
            balances[r] += amount
            R[r*n+r] += amount
        elif kind == 'dec':
            scalar -= amount
            balances[r] -= amount
            U[r] += amount
        else:
            balances[r] -= amount
            balances[target] += amount
            R[r*n+target] += amount
    return scalar, balances, Payload(tuple(R), tuple(U))


def known_broken_control():
    """Missing serialization: two donor forks reuse the same ten rights."""
    n = 3
    funded = effect(zero(n), 0, 'inc', 10, None, n)
    assert rights(funded, 0, n) >= 7
    a = effect(funded, 0, 'transfer', 7, 1, n)
    b = effect(funded, 0, 'transfer', 7, 2, n)
    fork = join(a, b)
    assert rights(fork, 0, n) == -4
    final = join(effect(fork, 1, 'dec', 7, None, n),
                 effect(fork, 2, 'dec', 7, None, n))
    assert value(final, n) == -4
    return {'same_issuer_fork_detected': True, 'value_minus_bound': -4}


def stale_snapshot_control():
    n = 2
    funded = effect(zero(n), 0, 'inc', 2, None, n)
    old = effect(funded, 0, 'transfer', 1, 1, n)
    latest = effect(old, 0, 'transfer', 1, 1, n)
    recipient = effect(latest, 1, 'dec', 2, None, n)
    assert join(recipient, old) == recipient
    assert join(join(recipient, old), old) == recipient
    assert rights(recipient, 1, n) == 0 and value(recipient, n) == 0
    return {'stale_duplicate_snapshot_control': True}


def exhaust(n, depth, amounts):
    counters = dict(nodes=0, accepted_issuances=0, rejected_issuances=0,
                    deliveries=0, snapshot_checks=0, global_checks=0)
    actions = [(kind, a, None) for kind, a in product(('inc', 'dec'), amounts)]
    actions += [('transfer', a, t) for a, t in product(amounts, range(n))]

    def check(states, histories):
        counters['nodes'] += 1
        for s, h in zip(states, histories):
            v, balances, expected = account(h, n)
            assert s == expected, (s, expected, h)
            assert value(s, n) == v
            assert [rights(s, r, n) for r in range(n)] == balances
            assert min(balances) >= 0 and v >= 0
            counters['snapshot_checks'] += 1
        global_events = frozenset().union(*histories)
        v, balances, expected = account(global_events, n)
        merged = zero(n)
        for s in states:
            merged = join(merged, s)
        assert merged == expected
        assert v == value(merged, n) == sum(balances)
        assert min(balances) >= 0 and v >= 0
        counters['global_checks'] += 1

    def explore(states, histories, remaining):
        check(states, histories)
        if not remaining:
            return
        step = depth - remaining
        for r in range(n):
            for kind, amount, target in actions:
                valid = kind != 'transfer' or target != r
                affordable = kind == 'inc' or amount <= rights(states[r], r, n)
                if not valid or not affordable:
                    counters['rejected_issuances'] += 1
                    continue
                counters['accepted_issuances'] += 1
                event = (step, r, kind, amount, target)
                ss, hs = list(states), list(histories)
                ss[r] = effect(states[r], r, kind, amount, target, n)
                hs[r] = histories[r] | {event}
                explore(tuple(ss), tuple(hs), remaining - 1)
        for source, target in product(range(n), repeat=2):
            if source == target:
                continue
            counters['deliveries'] += 1
            ss, hs = list(states), list(histories)
            ss[target] = join(states[target], states[source])
            hs[target] = histories[target] | histories[source]
            explore(tuple(ss), tuple(hs), remaining - 1)

    explore((zero(n),) * n, (frozenset(),) * n, depth)
    return dict(replicas=n, max_trace_length=depth, amounts=list(amounts),
                **counters, failures=0, discarded_cases=0)


if __name__ == '__main__':
    print(json.dumps(known_broken_control(), sort_keys=True))
    print(json.dumps(stale_snapshot_control(), sort_keys=True))
    for parameters in [(2, 4, (0, 1, 2)), (3, 3, (0, 1, 2))]:
        print(json.dumps(exhaust(*parameters), sort_keys=True))
