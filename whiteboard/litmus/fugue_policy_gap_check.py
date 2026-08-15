#!/usr/bin/env python3
"""Test an O(live)-entry mint-policy summary against the full Fugue tree.

The full oracle is ``embed_sided.SidedChain(policy='fugue')``.  ``GapState``
keeps the live chains plus, for start and every live anchor, only:

* ``has_r``: whether that anchor has ever minted an R child;
* ``succ``: its current tombstone-visible successor, if any.

An insert immediately after ``a`` replaces ``succ[a]`` with the new node and
gives the new node the old successor.  Deletion removes the anchor's own gap
entry but does not remove references to it as another gap's dead successor.
Merge takes the key-largest successor candidate supplied by either branch.

This is a refutation oracle, not a proof.  It includes ``LiveOnlyGap``, the
known-broken control that drops a deleted successor.
"""

from dataclasses import dataclass
from random import Random
from embed_sided import SidedChain, R, LFT


def skey(chain):
    return SidedChain.key(chain)


@dataclass(frozen=True)
class Gap:
    has_r: bool
    succ: int | None


@dataclass
class GapState:
    live: set
    chains: dict
    gaps: dict

    @classmethod
    def init(cls):
        return cls(set(), {}, {0: Gap(False, None)})

    def copy(self):
        return type(self)(set(self.live), dict(self.chains), dict(self.gaps))

    def read(self):
        return sorted(self.live, key=lambda x: skey(self.chains[x]), reverse=True)

    def choose(self, a):
        g = self.gaps[a]
        if g.succ is not None and g.has_r:
            return LFT, g.succ
        return R, a

    def insert(self, x, a):
        g = self.gaps[a]
        side, parent = self.choose(a)
        pchain = () if parent == 0 else self.chains[parent]
        self.chains[x] = pchain + ((side, x),)
        self.live.add(x)
        self.gaps[a] = Gap(g.has_r or (side == R and parent == a), x)
        self.gaps[x] = Gap(False, g.succ)

    def delete(self, x):
        self.live.discard(x)
        self.gaps.pop(x, None)
        self._prune()

    def _prune(self):
        keep = self.live | {g.succ for g in self.gaps.values() if g.succ is not None}
        self.chains = {x: ch for x, ch in self.chains.items() if x in keep}

    @staticmethod
    def merge(l, a, b):
        live = ((a.live & b.live) | (a.live - l.live) | (b.live - l.live))
        chains = {**l.chains, **a.chains, **b.chains}
        gaps = {}
        for x in {0} | live:
            gs = [s.gaps[x] for s in (a, b) if x in s.gaps]
            if not gs:
                raise AssertionError(f'missing gap for live anchor {x}')
            has_r = any(g.has_r for g in gs)
            candidates = {g.succ for g in gs if g.succ is not None}
            succ = max(candidates, key=lambda y: skey(chains[y])) if candidates else None
            gaps[x] = Gap(has_r, succ)
        out = type(a)(live, chains, gaps)
        out._prune()
        return out


class LiveOnlyGap(GapState):
    """Known-broken control: deleting x also drops references to x."""
    def delete(self, x):
        self.live.discard(x)
        self.gaps.pop(x, None)
        self.gaps = {a: Gap(g.has_r, None if g.succ == x else g.succ)
                     for a, g in self.gaps.items()}
        self._prune()


def full_init():
    d = SidedChain(); d.policy = 'fugue'
    return d, d.init()


def directed(state_cls=GapState):
    d, full = full_init(); gap = state_cls.init()
    for op in [('ins', 1, 0), ('ins', 2, 1), ('del', 2)]:
        d.apply(full, op)
        (gap.insert(op[1], op[2]) if op[0] == 'ins' else gap.delete(op[1]))
    fa, fb = d.copy(full), d.copy(full)
    ga, gb = gap.copy(), gap.copy()
    d.apply(fa, ('ins', 5, 1)); ga.insert(5, 1)
    d.apply(fb, ('ins', 4, 1)); gb.insert(4, 1)
    fm, gm = d.merge(full, fa, fb), state_cls.merge(gap, ga, gb)
    return d.read(fm), gm.read()


def random_fork_join(seed, rounds=60, max_branches=3):
    """Exercise valid MRDT diamonds, always merging against their true LCA."""
    rng = Random(seed); d, full = full_init(); gap = GapState.init()
    next_id = 1
    for step in range(rounds):
        base_f, base_g = d.copy(full), gap.copy()
        branches = []
        for _ in range(rng.randint(2, max_branches)):
            bf, bg = d.copy(base_f), base_g.copy()
            for _ in range(rng.randint(1, 3)):
                if bf[0] and rng.random() < .38:
                    x = rng.choice(tuple(bf[0]))
                    d.apply(bf, ('del', x)); bg.delete(x)
                else:
                    view = d.read(bf)
                    a = 0 if not view or rng.random() < .25 else rng.choice(view)
                    x = next_id; next_id += 1
                    d.apply(bf, ('ins', x, a)); bg.insert(x, a)
                if bg.read() != d.read(bf):
                    return step, 'local', d.read(bf), bg.read()
            branches.append((bf, bg))
        full, gap = branches[0]
        for bf, bg in branches[1:]:
            full = d.merge(base_f, full, bf)
            gap = GapState.merge(base_g, gap, bg)
            if gap.read() != d.read(full):
                return step, 'merge', d.read(full), gap.read()
    return None


if __name__ == '__main__':
    good = directed(GapState)
    bad = directed(LiveOnlyGap)
    print('directed gap summary :', good)
    print('negative live-only   :', bad)
    assert good[0] == good[1] == [1, 4, 5]
    assert bad[0] != bad[1]
    failures = [(seed, f) for seed in range(20)
                if (f := random_fork_join(seed)) is not None]
    print(f'random fork/join: {20 - len(failures)}/20 seeds clean')
    if failures:
        print('first failure:', failures[0])
        raise SystemExit(1)
