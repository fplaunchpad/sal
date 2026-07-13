#!/usr/bin/env python3
"""
Randomized version-DAG PBT over the litmus adapter interface.

Generates executions parameterized by (#replicas, #rounds, ops/round, delete
ratio, merge probability, seed): honest clients issue inserts/deletes against
their own reads; replicas merge pairwise under the LCA discipline (a merge
happens only when some recorded version's event set equals the two heads'
intersection — the model invariant "common past ⊆ LCA"); at the end, forced
convergence rounds drive all replicas to the full event set along DIFFERENT
merge paths.

Checks (the scalable subset of the observable ladder):
  FLIP   pairwise display stability (column d): across EVERY read of EVERY
         replica in the whole execution, no pair is ever displayed in both
         orders.  Subsumes S2/S4 globally.
  CONV   replicas that reach the SAME event set via different merge
         topologies must read identically.
  LIVE   survival correctness: a replica's read is exactly (its inserts −
         its deletes), no duplicates.

NOT checked here (litmus territory): non-interleaving g/h, strong-list e,
oracle-fidelity f, list-linearizability S6 (brute force does not scale).

Run:  python3 pbt.py [executions-per-design]
"""
import sys
from random import Random
import litmus as L


def run_execution(D, rng, n_replicas, n_rounds, max_ops, p_del, p_merge):
    """One random DAG execution. Returns list of violation strings."""
    D.begin()
    bad = []
    init = D.init()
    versions = [(frozenset(), init)]              # (event set, state at that version)
    heads = [(frozenset(), init)] * n_replicas    # replica -> current version
    seen = {}                                     # (x,y) -> True  (x displayed before y)
    next_id = [1]
    skipped = 0

    def check(events, state, tag):
        doc = D.read(state)
        if len(doc) != len(set(doc)):
            bad.append(f"DUP@{tag}: {doc}")
        ins = {e for e in events if isinstance(e, int)}
        dels = {e[1] for e in events if not isinstance(e, int)}
        if set(doc) != ins - dels:
            bad.append(f"LIVE@{tag}: read={sorted(set(doc))} expect={sorted(ins - dels)}")
        for i in range(len(doc)):
            for j in range(i + 1, len(doc)):
                if (doc[j], doc[i]) in seen:
                    bad.append(f"FLIP@{tag}: {(doc[j], doc[i])} then {(doc[i], doc[j])}")
                seen[(doc[i], doc[j])] = True

    def do_ops(r, k):
        ev, st = heads[r]
        st = D.copy(st); ev = set(ev)
        for _ in range(k):
            doc = D.read(st)
            if doc and rng.random() < p_del:
                d = rng.choice(doc)
                st = D.apply(st, ('del', d)); ev.add(('d', d))
            else:
                a = rng.choice([0] + doc) if doc else 0
                x = next_id[0]; next_id[0] += 1
                st = D.apply(st, ('ins', x, a)); ev.add(x)
            check(frozenset(ev), st, f"op:r{r}")
        heads[r] = (frozenset(ev), st)
        versions.append(heads[r])

    def try_merge(i, j):
        nonlocal skipped
        (ei, si), (ej, sj) = heads[i], heads[j]
        if ei == ej:
            return False
        inter = ei & ej
        lca = next(((ev, st) for (ev, st) in versions if ev == inter), None)
        if lca is None:
            skipped += 1
            return False
        try:
            m = D.merge(D.copy(lca[1]), D.copy(si), D.copy(sj))
        except Exception as e:
            bad.append(f"ERR@merge: {type(e).__name__}")
            return True
        me = ei | ej
        # CONV: someone else already holds this exact event set via another path
        for (ev2, st2) in versions:
            if ev2 == me and D.read(st2) != D.read(m):
                bad.append(f"CONV: {D.read(st2)} vs {D.read(m)}")
                break
        check(me, m, f"merge:r{i}+r{j}")
        heads[i] = (me, m)
        versions.append(heads[i])
        return True

    for _ in range(n_rounds):
        for r in range(n_replicas):
            if bad: return bad, skipped
            if rng.random() < p_merge:
                j = rng.randrange(n_replicas)
                if j != r: try_merge(r, j)
            else:
                do_ops(r, rng.randint(1, max_ops))

    # forced convergence: merge until no legal merge changes anything
    for _ in range(6 * n_replicas):
        if bad: break
        pairs = [(i, j) for i in range(n_replicas) for j in range(n_replicas)
                 if i != j and heads[i][0] != heads[j][0]]
        if not pairs: break
        rng.shuffle(pairs)
        if not any(try_merge(i, j) for (i, j) in pairs):
            break
    return bad, skipped


def sweep(D, executions, seed0=0, n_replicas=4, n_rounds=8, max_ops=2,
          p_del=0.3, p_merge=0.4):
    fails, skipped_total = [], 0
    for e in range(executions):
        rng = Random(seed0 * 100003 + e)
        bad, skipped = run_execution(D, rng, n_replicas, n_rounds, max_ops,
                                     p_del, p_merge)
        skipped_total += skipped
        if bad:
            fails.append((e, bad[0]))
    return fails, skipped_total


if __name__ == '__main__':
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 150
    print(f"executions/design: {N}  (4 replicas, 8 rounds, ≤2 ops, 30% del, 40% merge)")
    for D in L.DESIGNS:
        if D.merge is None:
            continue
        fails, skipped = sweep(D, N)
        verdict = "CLEAN" if not fails else f"{len(fails)} FAILING (first: seed {fails[0][0]}: {fails[0][1]})"
        print(f"  {D.name:14} {verdict}   [skipped illegal merges: {skipped}]")
