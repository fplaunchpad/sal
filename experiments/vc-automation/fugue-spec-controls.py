#!/usr/bin/env python3
"""Refutation oracle for sequential FugueMax candidates; not a Lean equivalence proof.

Implement the published structural tree insertion rule and reverse-right-origin
sibling order independently. Compare its final visible list with ALL causally
legal sequential schedules of generated messages. Candidate states are ordinary
identified lists, optionally retaining deletion tombstones. They never use tree
chains, coordinates, or implementation sorting. IDs are globally fresh positive
integers, consistent with Sal's stricter timestamp discipline. Valid positional
requests only; deletion indices always refer to a visible element. Checks cover
single replicas and two branches from a common snapshot, not all executions.
"""
from dataclasses import dataclass
from itertools import permutations
import random
import json


@dataclass(frozen=True)
class Event:
    id: int
    rep: int
    kind: str
    parent: int = 0
    side: str = 'R'
    lo: int = 0
    ro: int | None = None
    target: int = 0
    past: frozenset = frozenset()


def structural(events):
    children = {0: {'L': [], 'R': []}}
    deleted = set()

    def traversal(root=0):
        out = []
        def visit(x):
            for c in children[x]['L']:
                visit(c)
            out.append(x)
            for c in children[x]['R']:
                visit(c)
        visit(root)
        return out

    born = {}
    for e in sorted(events, key=lambda e: e.id):
        if e.kind == 'delete':
            deleted.add(e.target)
            continue
        old_order = traversal()
        siblings = children[e.parent][e.side]
        if e.side == 'L':
            pos = next((i for i, x in enumerate(siblings) if e.id < x), len(siblings))
        else:
            origin_rank = len(old_order) if e.ro is None else old_order.index(e.ro)
            pos = len(siblings)
            for i, x in enumerate(siblings):
                other = born[x]
                other_rank = len(old_order) if other.ro is None else old_order.index(other.ro)
                if origin_rank > other_rank or (origin_rank == other_rank and e.id < x):
                    pos = i
                    break
        siblings.insert(pos, e.id)
        children[e.id] = {'L': [], 'R': []}
        born[e.id] = e
    full = traversal()
    return full, [x for x in full if x and x not in deleted], children


def issue(events, rep, id, kind, index):
    full, visible, children = structural(events)
    if kind == 'delete':
        return Event(id, rep, kind, target=visible[index], past=frozenset(e.id for e in events))
    lo = 0 if index == 0 else visible[index - 1]
    loc = full.index(lo)
    ro = full[loc + 1] if loc + 1 < len(full) else None
    if children[lo]['R'] and ro is not None:
        return Event(id, rep, kind, parent=ro, side='L', lo=lo, ro=ro,
                     past=frozenset(e.id for e in events))
    return Event(id, rep, kind, parent=lo, side='R', lo=lo, ro=ro,
                 past=frozenset(e.id for e in events))


def run_candidate(schedule, candidate, include_dead=False):
    full, dead = [0], set()
    for e in schedule:
        if e.kind == 'delete':
            if candidate.startswith('tombstone'):
                dead.add(e.target)
            else:
                full = [x for x in full if x != e.target]
            continue
        anchor = e.lo if candidate.endswith('left-origin') else e.parent
        before = not candidate.endswith('left-origin') and e.side == 'L'
        if anchor not in full:
            continue  # This is the existing absent-anchor no-op behavior.
        pos = full.index(anchor) + (not before)
        full.insert(pos, e.id)
    return [x for x in full if x and (include_dead or x not in dead)]


def spec_conflict(a, b):
    """Exact natural insert/delete conflict hypothesis; Lean proof is separate.

With tombstones, deletion does not remove an insertion anchor. Two distinct
fresh insertions commute except for shared anchors or anchor creation. An
insertion and deletion conflict only when deletion names the inserted ID.
"""
    if a.kind == b.kind == 'delete':
        return False
    if a.kind == b.kind == 'insert':
        return a.lo == b.lo or a.id == b.lo or b.id == a.lo
    insertion, deletion = (a, b) if a.kind == 'insert' else (b, a)
    return insertion.id == deletion.target

def verdict(events, candidate, include_dead=False, visibility='full-causal'):
    by_id = {e.id: e for e in events}
    expected = structural(events)[0][1:] if include_dead else structural(events)[1]
    ids = {e.id for e in events}
    tested, pruned = 0, 0

    def search(prefix, pending, seen):
        nonlocal tested, pruned
        if include_dead:
            partial = run_candidate(prefix, candidate, True)
            # Archive edits never reorder/delete old identities: a mismatch
            # cannot be repaired by extending this schedule. This is exact
            # semantic pruning, not a case/time budget or discarded execution.
            projection = [x for x in expected if x in partial]
            if partial != projection:
                pruned += 1
                return False
        if not pending:
            tested += 1
            return run_candidate(prefix, candidate, include_dead) == expected
        for e in pending:
            required = (e.past & ids) if visibility == 'full-causal' else {
                id for id in e.past & ids if spec_conflict(by_id[id], e)}
            if required <= seen:
                if search(prefix + (e,), tuple(x for x in pending if x != e), seen | {e.id}):
                    return True
        return False

    ok = search((), tuple(events), set())
    return ok, tested, expected


def programs(start, rep, first_id, length, trace=()):
    yield start, trace
    if not length:
        return
    visible = structural(start)[1]
    for i in range(len(visible) + 1):
        e = issue(start, rep, first_id, 'insert', i)
        yield from programs(start + (e,), rep, first_id + 1, length - 1,
                            trace + (('insert', i, e.id),))
    for i in range(len(visible)):
        e = issue(start, rep, first_id, 'delete', i)
        yield from programs(start + (e,), rep, first_id + 1, length - 1,
                            trace + (('delete', i, e.id),))


def dump(e):
    return dict(id=e.id, rep=e.rep, kind=e.kind, parent=e.parent, side=e.side,
                lo=e.lo, ro=e.ro, target=e.target, past=sorted(e.past))


def controls():
    candidates = ('visible-parent', 'visible-left-origin',
                  'tombstone-parent', 'tombstone-left-origin', 'tombstone-left-origin-full-archive')
    found = {}
    checked = dict.fromkeys(candidates, 0)
    schedule_checks = dict.fromkeys(candidates, 0)
    # Hand-derived PASS+FAIL: deleted structural parent is still an anchor.
    a = issue((), 0, 1, 'insert', 0)
    d = issue((a,), 0, 2, 'delete', 0)
    b = issue((a, d), 0, 3, 'insert', 0)
    assert b.parent == 1 and b.side == 'L' and b.lo == 0
    assert structural((a, d, b))[1] == [3]
    assert run_candidate((a, d, b), 'visible-parent') == []
    assert run_candidate((a, d, b), 'tombstone-parent') == [3]
    assert run_candidate((a, d, b), 'visible-left-origin') == [3]
    # Minimal source same-gap tie positive control.
    x, y = issue((), 0, 1, 'insert', 0), issue((), 1, 2, 'insert', 0)
    assert structural((x, y))[1] == [1, 2]
    assert structural((x, y))[1] != [2, 1]
    # Search in increasing total event count, rather than declaring the first
    # depth-first failure minimal. Common prefix is either empty or one insert.
    cases = []
    for common in ((), (a,)):
        left = list(programs(common, 0, len(common) + 1, 3))
        right = list(programs(common, 1, len(common) + 10, 3))
        for ls, lt in left:
            for rs, rt in right:
                events = common + ls[len(common):] + rs[len(common):]
                if len(events) <= 6:
                    cases.append((events, lt, rt, len(common)))
    cases.sort(key=lambda case: len(case[0]))
    for events, lt, rt, prefix in cases:
        for candidate in candidates:
            checked[candidate] += 1
            full_archive = candidate.endswith('full-archive')
            model = 'tombstone-left-origin' if full_archive else candidate
            ok, schedules, expected = verdict(events, model, full_archive)
            schedule_checks[candidate] += schedules
            if not ok and candidate not in found:
                found[candidate] = dict(events=len(events), common_prefix=prefix,
                    left_trace=lt, right_trace=rt, expected=expected,
                    causal_schedules_tested=schedules, messages=[dump(e) for e in events])
    return dict(bounds=dict(replicas=2, max_branch_requests=3, max_total_events=6,
                            common_prefix_inserts=[0, 1]),
                cases=checked, causal_schedule_checks=schedule_checks,
                counterexamples=found, directed_controls='pass',
                caveat='bounded Python refutation gate; no implementation equivalence or universal proof')


def structural_depth_control():
    a = issue((), 1, 1, 'insert', 0)
    b = issue((), 0, 2, 'insert', 0)
    c = issue((b,), 2, 3, 'insert', 0)
    events = (a, b, c)
    # Source has concurrent root children 1 and 2, and left child 3 of 2.
    # Existing depth-first construction orders both depth-1 births before3.
    assert structural(events)[1] == [1, 3, 2]
    assert run_candidate((b, a, c), 'tombstone-left-origin') == [3, 1, 2]
    assert run_candidate((a, b, c), 'tombstone-left-origin') == [3, 2, 1]
    assert run_candidate((b, c, a), 'tombstone-left-origin') == [1, 3, 2]
    return dict(status='structural-depth-construction-refuted', events=3,
        expected=[1, 3, 2], depth_order_outputs=[[3, 1, 2], [3, 2, 1]],
        working_non_depth_witness=[2, 3, 1], messages=[dump(e) for e in events])


def minimized_left_origin_control():
    # Hand-derived seven-insert fixture. Each local past is exactly its issuing
    # snapshot, and the structural fields follow the published insertion rule.
    events = (
        Event(1, 1, 'insert'),
        Event(2, 0, 'insert'),
        Event(3, 2, 'insert', parent=2, side='L', lo=0, ro=2, past=frozenset({2})),
        Event(4, 1, 'insert', parent=1, side='L', lo=0, ro=1, past=frozenset({1, 2, 3})),
        Event(6, 2, 'insert', parent=3, side='R', lo=3, ro=2, past=frozenset({2, 3})),
        Event(7, 2, 'insert', parent=3, side='L', lo=0, ro=3, past=frozenset({2, 3, 6})),
        Event(8, 1, 'insert', parent=3, side='R', lo=3, ro=2, past=frozenset({1, 2, 3, 4})),
    )
    expected = [4, 1, 7, 3, 6, 8, 2]
    assert structural(events)[1] == expected
    ok, schedules, actual = verdict(events, 'tombstone-left-origin', False)
    assert not ok and schedules == 22 and actual == expected
    # Dropping visibility admits a witness. This companion prevents treating
    # this result as a refutation of weaker, noncausal permutation existence.
    by_id = {e.id: e for e in events}
    noncausal = tuple(by_id[i] for i in (2, 3, 7, 1, 4, 8, 6))
    assert run_candidate(noncausal, 'tombstone-left-origin') == expected
    assert 6 in by_id[7].past and noncausal.index(by_id[7]) < noncausal.index(by_id[6])
    # Check each message can really be generated by the source positional API
    # from its own snapshot, rather than arbitrary malformed input metadata.
    for e in events:
        snapshot = tuple(by_id[i] for i in sorted(e.past))
        positions = range(len(structural(snapshot)[1]) + 1)
        assert any(issue(snapshot, e.rep, e.id, 'insert', i) == e for i in positions)
    return dict(status='causal-candidate-refuted', event_count=7,
        causal_schedules_tested=22, expected=expected,
        messages=[dump(e) for e in events],
        causal_order_cycle=[6, 7, 1, 4, 8, 6],
        noncausal_witness=[2, 3, 7, 1, 4, 8, 6],
        minimality='minimal causalclosed subset of sampled eight-event failure; not global minimality',
        kernel_status='not yet translated to Lean')


def randomized(visibility='full-causal'):
    seeds = (0, 1, 17, 42, 20261014)
    distributions = ('mixed', 'backward-heavy', 'delete-heavy')
    cases, prefix_checks, schedules = 0, 0, 0
    for seed in seeds:
        rng = random.Random(seed)
        for distribution in distributions:
            for trial in range(100):
                views = [(), (), ()]
                all_events = []
                trace = []
                for event_id in range(1, 9):
                    # Arbitrary peer-to-peer causal snapshot delivery, including
                    # repeated delivery and disconnected replicas.
                    for _ in range(rng.randrange(4)):
                        source, target = rng.sample(range(3), 2)
                        union = {e.id: e for e in views[target] + views[source]}
                        views[target] = tuple(sorted(union.values(), key=lambda e: e.id))
                        trace.append(('merge', source, target))
                    rep = rng.randrange(3)
                    visible = structural(views[rep])[1]
                    delete_chance = 0.55 if distribution == 'delete-heavy' else 0.2
                    if visible and rng.random() < delete_chance:
                        kind, index = 'delete', rng.randrange(len(visible))
                    else:
                        kind = 'insert'
                        if distribution == 'backward-heavy' and rng.random() < 0.8:
                            index = 0
                        else:
                            index = rng.randrange(len(visible) + 1)
                    e = issue(views[rep], rep, event_id, kind, index)
                    views[rep] += (e,)
                    all_events.append(e)
                    trace.append((kind, rep, index, event_id))
                    ok, tried, expected = verdict(all_events, 'tombstone-left-origin', True, visibility)
                    prefix_checks += 1
                    schedules += tried
                    if not ok:
                        return dict(status='refuted', visibility=visibility, seed=seed, distribution=distribution,
                            trial=trial, trace=trace, expected_archive=expected,
                            messages=[dump(e) for e in all_events], prefix_checks=prefix_checks)
                cases += 1
    return dict(status='survived-bounded-testing', visibility=visibility, seeds=list(seeds), replicas=3,
                event_count_per_execution=8, distributions=list(distributions),
                executions=cases, prefix_checks=prefix_checks,
                completed_causal_schedules_tested=schedules, discarded_executions=0,
                oracle='full archive order, stronger than final visible equality',
                caveat='sampling is a refutation oracle, not a universal proof')


if __name__ == '__main__':
    print(json.dumps(dict(deterministic=controls(), minimized=minimized_left_origin_control(), structural_depth=structural_depth_control(), randomized=randomized(), projected_spec_visibility=randomized('natural-spec-conflicts')), sort_keys=True))
