#!/usr/bin/env python3
"""
embed_compact_measure.py -- Task #97 (practical tail): REAL-TRACE
measurement of compactEliasDelta v1, the state-level GC of the embed RGA
(runtime/src/compact.js is the executable spec; the recoding theory is
whiteboard/embed-recoding-note.md, the settled-cut contract
whiteboard/stability-vc-note.md section 2).

Data: josephg/editing-traces (CC BY 4.0), the same local corpus
entropy_measure.py uses (traces/; fetch commands documented there).
Sequential traces (automerge-paper, seph-blog1, friendsforever_flat,
clownschool_flat) are single-author: every prefix of the history is
settled at the single replica, so periodic cuts are FREE and every
sibling group is renumberable (no in-flight, no unsettled members).
Concurrent traces (friendsforever, clownschool) get a single FINAL cut
(everything delivered = settled).

Measured, per trace:
  * per periodic cut: total coordinate bits over live records before and
    after the cut (the subject run carries its accumulated compactions
    into each next cut);
  * final bits/char, control (never compacted) vs subject;
  * the design's HISTORY-INDEPENDENCE prediction: post-compaction cost is
    a function of the live tree shape alone, so a final settled cut must
    land the control and the subject on EXACTLY the same bit count,
    despite their different compaction histories -- checked and reported;
  * for sequential traces, an end-to-end DISPLAY check: the compacted
    coordinates, sorted by the descending sentinel-key order of the JS/
    Lean model, must spell endContent. (Concurrent traces are skipped for
    this check: the dense-clock replay ties timestamps across branches,
    and coordinate injectivity there rides on the (t, agent) Lamport pair
    the litmus replay does not encode into coordinates; ties are counted
    and reported instead.)

This script tracks codeword LENGTHS (bits); order-preservation soundness
of the compaction itself is pinned by runtime/test/compact.test.js and
the Lean recoding cluster, not here.

Model reuse: Replay (shared birth tree + per-branch states) and bits_D
(flipped Elias-delta codeword length) are imported from entropy_measure.py
unchanged; the concurrent driver is transliterated from its
replay_concurrent (that file is read-only for this task).

Usage: python3 embed_compact_measure.py [trace.json.gz ...]
"""

import gzip
import json
import os
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from entropy_measure import Replay, bits_D, ROOT

HERE = os.path.dirname(os.path.abspath(__file__))


# ------------------------------------------------ the flipped Elias delta
def bin_enc(d):
    b = format(d, "b")
    return "1" * (len(b) - 1) + "0" + b[1:]


def d_enc(d):
    b = format(d, "b")
    return bin_enc(len(b)) + b[1:]


# ---------------------------------------------------------- accounting
class AccountingReplay(Replay):
    """Replay + per-node CURRENT codeword/prefix bit accounting.

    ordinal[x]  = x's current delta (its mint delta, until a cut
                  renumbers it to a rank ordinal);
    code_bits[x], prefix_bits[x] = |enc(ordinal)| and the full coordinate
                  bit length under the current epoch. A mint reads its
                  anchor's CURRENT prefix (the immutable-chain rule:
                  coord(x) = coord(anchor) ++ enc(t - ts(anchor)))."""

    def __init__(self):
        super().__init__()
        self.ordinal = {ROOT: 0}
        self.code_bits = {ROOT: 0}
        self.prefix_bits = {ROOT: 0}

    def mint(self, t, agent, anchor, ch):
        x = super().mint(t, agent, anchor, ch)
        d = self.delta[x]
        self.ordinal[x] = d
        self.code_bits[x] = bits_D(d)
        self.prefix_bits[x] = self.prefix_bits[anchor] + self.code_bits[x]
        return x


def live_bits(r, live):
    return sum(r.prefix_bits[x] for x in live)


def live_tree(r, live):
    """kept nodes (live chains' union) + children map, tie count."""
    kept = set()
    for x in live:
        while x != ROOT and x not in kept:
            kept.add(x)
            x = r.anchor[x]
    children = defaultdict(list)
    for x in kept:
        children[r.anchor[x]].append(x)
    ties = 0
    for n, kids in children.items():
        seen = set()
        for c in kids:
            if r.ts[c] in seen:
                ties += 1
            seen.add(r.ts[c])
    return kept, children, ties


def compact_cut(r, live):
    """compactEliasDelta over a fully SETTLED state: (1) dead ranges (all
    nodes off the live chains) leave the tree -- their deltas stop
    reserving room; (2) every sibling group rank-renumbers to ordinals
    1..k in (ts, agent) order, re-encoded with the Elias-delta code;
    (3) nothing is in flight, so no group is skipped. Returns ties."""
    live = set(live)
    kept, children, ties = live_tree(r, live)
    stack = [ROOT]
    while stack:
        n = stack.pop()
        kids = sorted(children.get(n, ()), key=lambda c: (r.ts[c], r.agent[c]))
        for i, c in enumerate(kids):
            r.ordinal[c] = i + 1
            r.code_bits[c] = bits_D(i + 1)
            r.prefix_bits[c] = r.prefix_bits[n] + r.code_bits[c]
            stack.append(c)
    return ties


def display_after_cut(r, live):
    """Rebuild the compacted coordinates as bit strings and read the
    document the JS/Lean way: descending lexicographic sentinel keys
    ('0'->'1', '1'->'2', terminator '3'; anchors above descendants,
    newest-first siblings)."""
    live = set(live)
    kept, children, _ = live_tree(r, live)
    coord = {ROOT: ""}
    stack = [ROOT]
    while stack:
        n = stack.pop()
        for c in children.get(n, ()):
            coord[c] = coord[n] + d_enc(r.ordinal[c])
            stack.append(c)
    key = {"0": "1", "1": "2"}
    order = sorted(
        live,
        key=lambda x: coord[x].translate(str.maketrans(key)) + "3",
        reverse=True,
    )
    return "".join(r.char[x] for x in order)


# ------------------------------------------------------------ drivers
def run_sequential(doc, cut_every):
    """Single-author replay; a cut fires each time the dense event clock
    crosses a multiple of cut_every (None = control, never compacts)."""
    r = AccountingReplay()
    state = (0, [], set(), set())
    rows = []
    next_cut = cut_every
    for txn in doc["txns"]:
        state = r.apply_patches(state, 0, txn["patches"])
        if next_cut is not None and state[0] >= next_cut:
            live = state[2] - state[3]
            before = live_bits(r, live)
            compact_cut(r, live)
            rows.append((state[0], len(live), before, live_bits(r, live)))
            while next_cut <= state[0]:
                next_cut += cut_every
    end = "".join(r.char[x] for x in state[1])
    return r, state, rows, end


def run_concurrent(doc):
    """Concurrent replay (transliterated from entropy_measure.py's
    replay_concurrent) on an AccountingReplay; no periodic cuts."""
    r = AccountingReplay()
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
        else:
            clock, ins, dels = 0, set(), set()
            for p in parents:
                src = states[p]
                clock = max(clock, src[0])
                ins |= src[2]
                dels |= src[3]
                refcount[p] -= 1
                if refcount[p] == 0:
                    del states[p]
            view = r.dfs_view(ins, dels)
            state = (clock, view, ins, dels)
        state = r.apply_patches(state, txn.get("agent", 0), txn["patches"])
        states[idx] = state
        final = state
    end = "".join(r.char[x] for x in final[1])
    return r, final, end


# ------------------------------------------------------------- report
def fmt(n):
    return f"{n:,}"


def measure(path):
    with gzip.open(path, "rt", encoding="utf-8") as f:
        doc = json.load(f)
    name = os.path.basename(path).replace(".json.gz", "")
    concurrent = doc.get("kind") == "concurrent"
    n_events = sum(p[1] + len(p[2]) for t in doc["txns"] for p in t["patches"])

    print(f"\n== {name}  [{'concurrent, final cut only' if concurrent else 'sequential single-author: fully settled, periodic cuts'}]")

    if concurrent:
        r, state, end = run_concurrent(doc)
        rows, r_ctl, live_ctl, cut_every = [], None, None, None
    else:
        cut_every = max(1000, n_events // 8)
        r_ctl, state_ctl, _, end_ctl = run_sequential(doc, None)  # control
        r, state, rows, end = run_sequential(doc, cut_every)      # subject
        assert end_ctl == end
        live_ctl = state_ctl[2] - state_ctl[3]
    live = state[2] - state[3]
    ok = end == doc["endContent"]
    n_chars = len(doc["endContent"])
    print(f"   events={fmt(n_events)}  inserts={fmt(len(r.ts) - 1)}  live chars={fmt(n_chars)}"
          f"  [{'ENDCONTENT OK' if ok else 'ENDCONTENT MISMATCH -- REPLAY INVALID'}]")

    if rows:
        print(f"   periodic cuts every {fmt(cut_every)} events:")
        print("      cut@event      live     bits before      bits after   saved")
        for ev, nl, b, a in rows:
            print(f"   {fmt(ev):>12}  {fmt(nl):>8}  {fmt(b):>14}  {fmt(a):>14}   {100*(b-a)/b:5.1f}%")

    # control = the never-compacted cost; subject = after its cut history
    before_ctl = live_bits(r_ctl, live_ctl) if r_ctl else live_bits(r, live)
    before_subj = live_bits(r, live)
    # the final settled cut, applied to BOTH histories
    ties = compact_cut(r, live)
    after_subj = live_bits(r, live)
    if r_ctl:
        compact_cut(r_ctl, live_ctl)
        after_ctl = live_bits(r_ctl, live_ctl)
        match = after_ctl == after_subj
    else:
        match = None  # one cut only: nothing to compare against

    print(f"   uncompacted (control) : {fmt(before_ctl):>14} bits   {before_ctl / n_chars:7.3f} bits/char")
    if r_ctl:
        print(f"   subject pre-final-cut : {fmt(before_subj):>14} bits   {before_subj / n_chars:7.3f} bits/char")
    print(f"   after final settled cut: {fmt(after_subj):>13} bits   {after_subj / n_chars:7.3f} bits/char"
          f"   ({before_ctl / max(1, after_subj):.1f}x smaller)")
    if match is not None:
        print("   history-independence (subject final == control final): "
              + ("MATCH" if match else "MISMATCH -- PREDICTION FALSIFIED"))
    else:
        print(f"   history-independence: n/a (single final cut)   [sibling ts ties: {ties}]")

    order_ok = None
    if not concurrent:
        order_ok = display_after_cut(r, live) == doc["endContent"]
        print(f"   display via compacted coordinates: {'ORDER OK' if order_ok else 'ORDER MISMATCH'}")
    return dict(name=name, chars=n_chars, before=before_ctl, after=after_subj,
                match=match, ok=ok, order_ok=order_ok,
                concurrent=concurrent)


if __name__ == "__main__":
    args = sys.argv[1:] or [
        os.path.join(HERE, "traces", t) for t in (
            "automerge-paper.json.gz",
            "seph-blog1.json.gz",
            "friendsforever_flat.json.gz",
            "clownschool_flat.json.gz",
            "friendsforever.json.gz",
            "clownschool.json.gz",
        )
    ]
    missing = [p for p in args if not os.path.exists(p)]
    if missing:
        print("MISSING TRACES (fetch per the curl lines documented in "
              "entropy_measure.py / traces/.gitignore):")
        for p in missing:
            print("  ", p)
    results = [measure(p) for p in args if os.path.exists(p)]
    if results:
        print("\n== SUMMARY (coordinate metadata over live records)")
        print(f"   {'trace':<22} {'chars':>8} {'before b/ch':>12} {'after b/ch':>11}"
              f" {'reduction':>10} {'shape-match':>12} {'order':>6}")
        for x in results:
            shape = "n/a" if x["match"] is None else ("MATCH" if x["match"] else "FAIL")
            order = "n/a" if x["order_ok"] is None else ("OK" if x["order_ok"] else "FAIL")
            print(f"   {x['name']:<22} {fmt(x['chars']):>8} {x['before']/x['chars']:>12.3f}"
                  f" {x['after']/x['chars']:>11.3f} {x['before']/max(1,x['after']):>9.1f}x"
                  f" {shape:>12} {order:>6}")
