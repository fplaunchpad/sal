#!/usr/bin/env python3
"""
entropy_measure.py -- Task #76: measure H(delta | anchor context) on real
editing traces (order-coding-compression-notes.md, invariant I1).

Goal. Quantify the gap between what the embedded-chain RGA's current code
C(delta) = 2*floor(log2 delta) + 1 actually pays per chain level and the
conditional entropy H(delta | mint-time context) that a context-conditioned
order-preserving coder could approach (I1, semantics-preserving mode: the
code at a level may be any deterministic function of the ANCHOR's stored
record, since honesty + canonicity make that record shared and identical at
every replica, and comparison locality keeps every comparison inside one
anchor's context).

Hypotheses (pre-registered in the task):
  H1: on realistic traces delta is a mixture of a delta=1 continuation mass
      and a heavy cursor-jump tail, so H(delta | ctx) << E|C(delta)|.
  H2: the single biggest predictor is run continuation / same-author-as-
      anchor; conditioning on it captures most of the gap.
  H3: Elias-delta (the flipped-header variant, note I5) helps only the tail;
      sub-1-bit rates are unreachable for ANY per-level prefix-free code
      (>= 1 bit/symbol) -- that mass belongs to run coalescing (I2).

Replay model (the entropy law's regime, design doc "Timestamps in practice"):
  - dense logical time: one Lamport tick per event (insert AND delete);
    merge sets the clock to the max of the parents (no tick);
  - ids are (t, agent); delta = t_x - t_anchor on the t component;
  - the anchor of an insert at view position p is the live character at
    p-1 (the front sentinel, ts 0, for p = 0) -- all anchors live at mint,
    which is exactly the honesty contract;
  - concurrent traces replay over the shared birth tree with RGA sibling
    order (children newest-first); the traces guarantee no two users ever
    insert concurrently at the same location, so every CRDT (ours included)
    produces the same merged document, and endContent equality at the end
    of the replay is the correctness gate for the whole pipeline.

Data: josephg/editing-traces (fetch with the curl lines in traces/; see
README-sequential.md / README-concurrent.md there for the formats).

Usage: python3 entropy_measure.py [trace.json.gz ...]
       (no args: runs the standard four traces)
"""

import gzip
import json
import math
import sys
from bisect import insort
from collections import Counter, defaultdict

ROOT = 0  # sentinel id; ts 0, no author


# ---------------------------------------------------------------- codes

def bits_C(d: int) -> int:
    """Flipped Elias gamma (the design's delta code): 2 floor(log2 d) + 1."""
    return 2 * d.bit_length() - 1


def bits_D(d: int) -> int:
    """Flipped Elias delta (note I5): C on the length field, then payload.
    |D(d)| = |C(L)| + (L-1) = L + 2 floor(log2 L) - 1  with L = bitlen d."""
    L = d.bit_length()
    return (2 * L.bit_length() - 1) + (L - 1)


# ---------------------------------------------------------------- entropy

def entropy(counter: Counter) -> float:
    """Plug-in Shannon entropy (bits/symbol) of an empirical distribution."""
    n = sum(counter.values())
    if n == 0:
        return 0.0
    h = 0.0
    for c in counter.values():
        p = c / n
        h -= p * math.log2(p)
    return h


def cond_entropy(pairs: Counter) -> float:
    """H(Y | X) from a Counter over (x, y) pairs."""
    by_ctx = defaultdict(Counter)
    for (x, y), c in pairs.items():
        by_ctx[x][y] += c
    n = sum(pairs.values())
    return sum(sum(cnt.values()) / n * entropy(cnt) for cnt in by_ctx.values())


# ---------------------------------------------------------------- replay

class Replay:
    """Shared birth tree + per-branch (clock, view, ins, dels) states."""

    def __init__(self):
        # per id: timestamp, agent, anchor id, delta, char
        self.ts = {ROOT: 0}
        self.agent = {ROOT: -1}
        self.anchor = {}
        self.delta = {}
        self.char = {}
        # birth tree: anchor -> children as a list of (-ts, -agent, id)
        # kept sorted ascending == ts descending (RGA newest-first)
        self.children = defaultdict(list)
        # measurement stream: one record per insert event
        #   (delta, same_author_as_anchor|'R', anchor_delta_class)
        self.mints = []
        self._next_internal = 1

    # -- minting ---------------------------------------------------------
    def mint(self, t, agent, anchor, ch):
        x = self._next_internal
        self._next_internal += 1
        d = t - self.ts[anchor]
        assert d >= 1, "causality violated"
        self.ts[x] = t
        self.agent[x] = agent
        self.anchor[x] = anchor
        self.delta[x] = d
        self.char[x] = ch
        insort(self.children[anchor], (-t, -agent, x))
        if anchor == ROOT:
            sa, dc = "R", 0
        else:
            sa = agent == self.agent[anchor]
            dc = self.delta[anchor].bit_length()
        self.mints.append((d, sa, dc, agent))
        return x

    # -- merged view: DFS of the birth tree filtered by causal live set --
    def dfs_view(self, ins, dels):
        out = []
        stack = [(ROOT, 0)]  # (node, next child index)
        while stack:
            node, i = stack.pop()
            kids = self.children[node]
            if i < len(kids):
                stack.append((node, i + 1))
                child = kids[i][2]
                if child in ins:  # never emit or descend into unseen ids
                    if child not in dels:
                        out.append(child)
                    stack.append((child, 0))
        return out

    # -- one transaction --------------------------------------------------
    def apply_patches(self, state, agent, patches):
        clock, view, ins, dels = state
        for patch in patches:
            pos, ndel, content = patch[0], patch[1], patch[2]
            for _ in range(ndel):
                clock += 1  # deletes tick: dense logical time
                victim = view.pop(pos)
                dels.add(victim)
            for i, ch in enumerate(content):
                clock += 1
                anch = view[pos + i - 1] if pos + i > 0 else ROOT
                x = self.mint(clock, agent, anch, ch)
                ins.add(x)
                view.insert(pos + i, x)
        return clock, view, ins, dels


def replay_sequential(doc, replay):
    state = (0, [], set(), set())
    for txn in doc["txns"]:
        state = replay.apply_patches(state, 0, txn["patches"])
    return "".join(replay.char[x] for x in state[1])


def replay_concurrent(doc, replay):
    txns = doc["txns"]
    states = {}
    refcount = [t.get("numChildren", 0) for t in txns]
    final = None
    for idx, txn in enumerate(txns):
        parents = txn["parents"]
        if not parents:
            state = (0, [], set(), set())
        elif len(parents) == 1:
            p = parents[0]
            src = states[p]
            if refcount[p] > 1:
                state = (src[0], list(src[1]), set(src[2]), set(src[3]))
            else:
                state = src
                del states[p]
            refcount[p] -= 1
        else:  # k-way merge
            clock, ins, dels = 0, set(), set()
            for p in parents:
                src = states[p]
                clock = max(clock, src[0])
                ins |= src[2]
                dels |= src[3]
                refcount[p] -= 1
                if refcount[p] == 0:
                    del states[p]
            view = replay.dfs_view(ins, dels)
            state = (clock, view, ins, dels)
        state = replay.apply_patches(state, txn.get("agent", 0),
                                     txn["patches"])
        states[idx] = state
        final = state
    return "".join(replay.char[x] for x in final[1])


# ---------------------------------------------------------------- report

def analyze(name, replay, ok):
    mints = replay.mints
    n = len(mints)
    deltas = Counter(d for d, _, _, _ in mints)
    p1 = deltas[1] / n

    eC = sum(bits_C(d) * c for d, c in deltas.items()) / n
    eD = sum(bits_D(d) * c for d, c in deltas.items()) / n
    h = entropy(deltas)
    h_sa = cond_entropy(Counter((sa, d) for d, sa, _, _ in mints))
    h_dc = cond_entropy(Counter((dc, d) for d, _, dc, _ in mints))
    h_joint = cond_entropy(Counter(((sa, dc), d) for d, sa, dc, _ in mints))

    # I2 run statistics: maximal runs of consecutive delta=1 mints,
    # tracked per agent (concurrent traces interleave agents' streams).
    # delta=1 is intrinsic run-continuation: it means "anchored at my
    # immediately-preceding event, which was this insert's predecessor".
    run_lens = []
    cur = defaultdict(int)
    for d, _, _, ag in mints:
        if d == 1:
            cur[ag] += 1
        else:
            if cur[ag]:
                run_lens.append(cur[ag])
            cur[ag] = 0
    run_lens.extend(c for c in cur.values() if c)
    # order bits if delta>1 mints pay C(delta), each maximal delta=1 run
    # pays C(len) once, and run members pay nothing (Yjs-style item ranges)
    bits_plain = sum(bits_C(d) * c for d, c in deltas.items())
    bits_runs = sum(bits_C(d) * c for d, c in deltas.items() if d != 1) \
        + sum(bits_C(ln) for ln in run_lens)

    print(f"\n== {name}  [{'ENDCONTENT OK' if ok else 'ENDCONTENT MISMATCH -- REPLAY INVALID'}]")
    print(f"   inserts n={n}   distinct deltas={len(deltas)}   "
          f"P(delta=1)={p1:.3f}   max delta={max(deltas)}")
    print(f"   E|C(delta)|          = {eC:7.3f} bits/level   (current code)")
    print(f"   E|EliasDelta(delta)| = {eD:7.3f} bits/level   (note I5)")
    print(f"   H(delta)             = {h:7.3f} bits/level   (plug-in)")
    print(f"   H(delta | same-author-as-anchor) = {h_sa:7.3f}")
    print(f"   H(delta | anchor-delta class)    = {h_dc:7.3f}")
    print(f"   H(delta | joint ctx)             = {h_joint:7.3f}")
    print(f"   I2 runs: {len(run_lens)} maximal delta=1 runs, "
          f"mean len {sum(run_lens)/max(1,len(run_lens)):.1f}, "
          f"coalesced order-cost ~{bits_runs/n:.3f} bits/char "
          f"(vs {bits_plain/n:.3f} plain)")
    return dict(name=name, n=n, p1=p1, eC=eC, eD=eD, h=h, h_sa=h_sa,
                h_dc=h_dc, h_joint=h_joint)


def run(path):
    with gzip.open(path, "rt", encoding="utf-8") as f:
        doc = json.load(f)
    replay = Replay()
    if doc.get("kind") == "concurrent":
        end = replay_concurrent(doc, replay)
    else:
        end = replay_sequential(doc, replay)
    ok = end == doc["endContent"]
    name = path.split("/")[-1].replace(".json.gz", "")
    return analyze(name, replay, ok)


if __name__ == "__main__":
    args = sys.argv[1:] or [
        "traces/automerge-paper.json.gz",
        "traces/seph-blog1.json.gz",
        "traces/friendsforever.json.gz",
        "traces/clownschool.json.gz",
    ]
    for p in args:
        run(p)
