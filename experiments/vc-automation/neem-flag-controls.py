#!/usr/bin/env python3
"""Bounded deterministic source-model gate for Neem's two flag variants.

Map_extended.const has universal domain; model queried rows 0..n-1 plus
one untouched row. Preferred operations increment their issuer row; rival
operations clear all rows. Counts use integer ancestor inclusion/exclusion.
The public scalar interpretation is absent from App_mrdt.fst; this gate checks
row counts/bits against independently recorded causal events, not a client API.
Intersection histories provide canonical virtual bases. This is a Python
model refutation gate, not an equivalence proof against Lean or F*.
"""
import json
from itertools import product


def cell_merge(l, a, b):
    lc, _ = l
    ac, af = a
    bc, bf = b
    flag = af if af == bf else (ac > lc if af else bc > lc)
    return ac + bc - lc, flag


def oracle(events, pasts, rows, initially_true):
    resets = [e for e in events if e[2] == 'reset']
    cells = []
    for row in range(rows):
        preferred = [e for e in events if e[1] == row and e[2] == 'preferred']
        live = any(not any(e in pasts[d] for d in resets) for e in preferred)
        cells.append((len(preferred), live or (initially_true and not resets)))
    return tuple(cells)


def exhaust(n, depth, initially_true):
    rows = n + 1  # Untouched row pins the universal default-domain semantics.
    counters = dict(nodes=0, updates=0, merges=0, row_checks=0)
    scalar_failure = None

    def explore(states, histories, pasts, scalar_states, left, trace):
        nonlocal scalar_failure
        counters['nodes'] += 1
        for s, events in zip(states, histories):
            expected = oracle(events, pasts, rows, initially_true)
            assert s == expected, (s, expected, events)
            counters['row_checks'] += rows
        if not left:
            return
        step = depth - left
        for r, kind in product(range(n), ('preferred', 'reset')):
            counters['updates'] += 1
            e = (step, r, kind)
            ps = dict(pasts)
            ps[e] = histories[r]
            ss, hs, scalars = list(states), list(histories), list(scalar_states)
            if kind == 'preferred':
                cells = list(states[r])
                count, _ = cells[r]
                cells[r] = (count + 1, True)
                ss[r] = tuple(cells)
                scalars[r] = (scalars[r][0] + 1, True)
            else:
                ss[r] = tuple((count, False) for count, _ in states[r])
                scalars[r] = (scalars[r][0], False)
            hs[r] = histories[r] | {e}
            explore(tuple(ss), tuple(hs), ps, tuple(scalars), left - 1,
                    trace + [(kind, r)])
        for source, target in product(range(n), repeat=2):
            if source == target:
                continue
            counters['merges'] += 1
            common = histories[source] & histories[target]
            base = oracle(common, pasts, rows, initially_true)
            ss, hs, scalars = list(states), list(histories), list(scalar_states)
            ss[target] = tuple(cell_merge(l, a, b) for l, a, b in
                               zip(base, states[target], states[source]))
            hs[target] = histories[source] | histories[target]
            # The old scalar design forgets per-issuer identity; reconstruct
            # its base independently from this history's event semantics.
            scalar_base = (sum(c for c, _ in base), any(f for _, f in base))
            scalars[target] = cell_merge(scalar_base, scalars[target], scalars[source])
            expected = oracle(hs[target], pasts, rows, initially_true)
            if scalar_failure is None and scalars[target][1] != any(f for _, f in expected):
                scalar_failure = {'event_count': len(hs[target]),
                                  'trace': trace + [('merge', source, target)],
                                  'scalar_verdict': scalars[target][1],
                                  'per_issuer_verdict': any(f for _, f in expected)}
            explore(tuple(ss), tuple(hs), pasts, tuple(scalars), left - 1,
                    trace + [('merge', source, target)])

    init = ((0, initially_true),) * rows
    explore((init,) * n, (frozenset(),) * n, {},
            ((0, initially_true),) * n, depth, [])
    return dict(replicas=n, max_trace_length=depth, initially_true=initially_true,
                **counters, failures=0, discarded_cases=0,
                scalar_mutant_counterexample=scalar_failure)


if __name__ == '__main__':
    for init in (False, True):
        result = exhaust(2, 6, init)
        assert result['scalar_mutant_counterexample'] is not None
        print(json.dumps(result, sort_keys=True))
