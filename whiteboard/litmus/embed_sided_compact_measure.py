#!/usr/bin/env python3
"""
embed_sided_compact_measure.py -- REAL-TRACE measurement of the embed-GC
compaction (rank-renumbering + spine fusion) for the SIDED embed under the
FUGUE side-selection policy, next to the one-sided columns of
embed_compact_measure.py (whose algorithm is imported and rerun unchanged).
Question: is the relative improvement the same as one-sided, and what do
sides actually cost?

Model (embed_sided.py, SidedCode): a coordinate is one block per level,
    block = sideBit ++ (payload if R else complement(payload)),
banded alphabet (R, d) < marker < (L, d') with the L band mirrored (newer
adjacent to the marker). Deviation from the litmus toy, recorded: the
payload code here is the flipped ELIAS DELTA (entropy_measure.bits_D /
embed_compact_measure.d_enc), not the toy's gamma C, so the one-sided
columns and the sided columns share one code family; a level costs
1 (side) + |D(delta)| bits.

Fugue policy (embed_sided.choose): insert after live anchor a mints
(R, a) if a has no R child ever (tombstone-visible), else (L, n) with n
the tombstone-visible successor of a. Consequences used here, both
derivable from the banded order and checked by the endContent gates:
  * every node has at most ONE R child ever;
  * the minted node lands IMMEDIATELY AFTER a in the full (dead-included)
    order, so the order is maintainable as a linked list, O(1) per mint.

Band-aware compaction (the design under test; deviations are findings):
  (a) rank-renumbering WITHIN each (parent, band) sibling group, ordinals
      1..k in (ts, agent) order per band; cross-band order is automatic
      (disjoint symbol ranges);
  (b) spine fusion mirrors the one-sided map: a maximal dead unary spine
      (k >= 2, dead below-cut nodes, exactly one child branch counting
      both bands, no in-flight -- vacuous here, all cuts fully settled)
      collapses to one level carrying the SPINE HEAD's (band, group
      codeword); the fused children's own sides vanish with their levels;
  (c) marker/sentinel corner: dead spine nodes have no records, so no
      keys exist at fused-away levels; verified empirically by the
      bit-level display check (order == semantic walk, text == endContent).

Correctness gates: every replay gated on endContent via the sided display
order (the L-asc / node / R-desc tree walk = descending banded-key order);
reads identical before/after at EVERY cut (walk equality, both subjects);
final renumbered AND fused coordinates re-sorted at the BIT level (side
char + translated payload, L payload complemented) must reproduce the walk
order and spell endContent. History independence checked as in the
one-sided script (renumber two-way, fused three-way).

Concurrent traces (friendsforever, clownschool): single final cut, like
the one-sided script. The replay uses the global full order for the
policy's successor/has-R lookups (the traces guarantee no concurrent
same-location edits; locality misses are counted and reported). Dense
clocks tie across branches, so sibling order falls back to (ts, agent)
and the bit-level display check is skipped (ties counted), as one-sided.

Usage: python3 embed_sided_compact_measure.py [trace.json.gz ...]
"""

import gzip
import json
import math
import os
import sys
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from entropy_measure import bits_D, ROOT
import embed_compact_measure as OCM

R_, L_ = 'R', 'L'


def comp(w):
    return ''.join('1' if c == '0' else '0' for c in w)


# ------------------------------------------------------- the sided replay
class SidedReplay:
    """Fugue-policy sided replay over one shared grow-only structure.

    Per node: ts, agent, parent (the SIDED parent, not the intent anchor),
    side, delta = ts - ts(parent), char, label (delta until a cut
    renumbers it to a per-band rank ordinal), code_bits = 1 + |D(label)|,
    prefix_bits = full coordinate length under the current epoch (a mint
    reads its parent's CURRENT prefix). nxt/prv realize the full
    tombstone-visible display order (ROOT is the head sentinel)."""

    def __init__(self):
        self.ts = {ROOT: 0}
        self.agent = {ROOT: -1}
        self.parent = {}
        self.side = {}
        self.delta = {}
        self.char = {}
        self.label = {ROOT: 0}
        self.code_bits = {ROOT: 0}
        self.prefix_bits = {ROOT: 0}
        self.kidsR = defaultdict(list)   # policy tree, all minted
        self.kidsL = defaultdict(list)
        self.has_r = set()
        self.nxt = {ROOT: None}
        self.prv = {}
        self.n_R = self.n_L = 0
        self.vis_miss = self.hasr_miss = 0   # concurrent locality audit
        self._next = 1

    def _link_after(self, a, x):
        n = self.nxt[a]
        self.nxt[a] = x
        self.prv[x] = a
        self.nxt[x] = n
        if n is not None:
            self.prv[n] = x

    def mint(self, t, agent, anchor, ch, seen=None):
        """Insert after live intent anchor `anchor` (ROOT = front)."""
        n = self.nxt[anchor]
        if anchor not in self.has_r or n is None:
            side, parent = R_, anchor
        else:
            side, parent = L_, n
        if seen is not None:              # branch-local faithfulness audit
            loc_r = any(c in seen for c in self.kidsR[anchor])
            if loc_r != (anchor in self.has_r):
                self.hasr_miss += 1
            if side == L_ and n not in seen:
                self.vis_miss += 1
        x = self._next
        self._next += 1
        d = t - self.ts[parent]
        assert d >= 1, "causality violated"
        self.ts[x] = t
        self.agent[x] = agent
        self.parent[x] = parent
        self.side[x] = side
        self.delta[x] = d
        self.char[x] = ch
        self.label[x] = d
        self.code_bits[x] = 1 + bits_D(d)
        self.prefix_bits[x] = self.prefix_bits[parent] + self.code_bits[x]
        if side == R_:
            self.kidsR[parent].append(x)
            self.has_r.add(parent)
            self.n_R += 1
            self._link_after(anchor, x)          # right after the anchor
        else:
            self.kidsL[parent].append(x)
            self.n_L += 1
            self._link_after(self.prv[n], x)     # right before n
        return x

    def apply_patches(self, state, agent, patches, audit=False):
        clock, view, ins, dels = state
        for patch in patches:
            pos, ndel, content = patch[0], patch[1], patch[2]
            for _ in range(ndel):
                clock += 1                        # deletes tick: dense time
                dels.add(view.pop(pos))
            for i, ch in enumerate(content):
                clock += 1
                anch = view[pos + i - 1] if pos + i > 0 else ROOT
                x = self.mint(clock, agent, anch, ch, ins if audit else None)
                ins.add(x)
                view.insert(pos + i, x)
        return clock, view, ins, dels

    def list_view(self, ins, dels):
        """The branch's live sequence: the global full order filtered."""
        out, x = [], self.nxt[ROOT]
        while x is not None:
            if x in ins and x not in dels:
                out.append(x)
            x = self.nxt[x]
        return out


def live_bits(r, live):
    return sum(r.prefix_bits[x] for x in live)


def live_tree(r, live):
    """Kept nodes (union of live chains) + per-band children maps,
    (ts, agent) tie count per (parent, band) group."""
    kept = set()
    for x in live:
        while x != ROOT and x not in kept:
            kept.add(x)
            x = r.parent[x]
    kR, kL = defaultdict(list), defaultdict(list)
    for x in kept:
        (kR if r.side[x] == R_ else kL)[r.parent[x]].append(x)
    ties = 0
    for kids in list(kR.values()) + list(kL.values()):
        seen = set()
        for c in kids:
            k = (r.ts[c], r.agent[c])
            if k in seen:
                ties += 1
            seen.add(k)
    return kept, kR, kL, ties


def compact_cut(r, live, fuse=False):
    """Band-aware compaction over a fully settled state: (1) dead ranges
    off the live chains leave the tree; (2) each (parent, band) sibling
    group rank-renumbers to ordinals 1..k in (ts, agent) order, level
    cost 1 + |D(ordinal)|; (2b, fuse) a maximal dead unary spine (one
    child branch counting BOTH bands, k >= 2) collapses onto its head's
    (band, group codeword): members after the head contribute 0 bits,
    their sides vanish with their levels. Nothing is in flight, so no
    group is skipped. Sets r.fused. Returns (ties, spines, levels)."""
    live = set(live)
    kept, kR, kL, ties = live_tree(r, live)
    r.fused = set()
    spines = levels = 0

    def nkids(c):
        return len(kR.get(c, ())) + len(kL.get(c, ()))

    def only_child(c):
        return (kR.get(c) or kL.get(c))[0]

    stack = [ROOT]
    while stack:
        n = stack.pop()
        for band in (kR, kL):
            kids = sorted(band.get(n, ()), key=lambda c: (r.ts[c], r.agent[c]))
            for i, c in enumerate(kids):
                r.label[c] = i + 1
                r.code_bits[c] = 1 + bits_D(i + 1)
                r.prefix_bits[c] = r.prefix_bits[n] + r.code_bits[c]
                node = c
                if fuse and c not in live and nkids(c) == 1:
                    members = [c]
                    while True:
                        nx = only_child(members[-1])
                        if nx in live or nkids(nx) != 1:
                            break
                        members.append(nx)
                    if len(members) > 1:   # k = 1 is the identity
                        for m in members[1:]:
                            r.fused.add(m)
                            r.label[m] = r.label[c]
                            r.code_bits[m] = 0
                            r.prefix_bits[m] = r.prefix_bits[c]
                        spines += 1
                        levels += len(members) - 1
                        node = members[-1]     # resume below the tail
                stack.append(node)
    return ties, spines, levels


def walk_display(r, live, tree=None):
    """The sided display order, semantically: descending banded-key sort
    == the tree walk emitting, per node, L kids label-ASCENDING (each
    recursively), then the node (if live), then R kids label-DESCENDING.
    Labels are the CURRENT per-band labels (mint deltas / rank ordinals),
    so walk equality before/after a cut is the reads-identical gate on
    the actual coordinate content. (ts, agent) breaks concurrent ties."""
    live = set(live)
    kept, kR, kL, _ = tree or live_tree(r, live)
    key = lambda c: (r.label[c], r.ts[c], r.agent[c])
    out, stack = [], [(False, ROOT)]
    while stack:
        emit, n = stack.pop()
        if emit:
            out.append(n)
            continue
        items = [(False, c) for c in sorted(kL.get(n, ()), key=key)]
        if n in live:
            items.append((True, n))
        items += [(False, c) for c in sorted(kR.get(n, ()), key=key,
                                             reverse=True)]
        stack.extend(reversed(items))
    return out


def attribute_bits(r, live):
    """Account for every bit of every live post-fusion coordinate:
    payload bits on LIVE levels, payload bits on surviving DEAD levels,
    SIDE bits on live levels, SIDE bits on dead levels (fused-away
    members contribute 0), plus level and L-band level counts.
    Returns totals (lp, dp, sl, sd, llv, dlv, lL, dL) over live records;
    lp + dp + sl + sd == total fused bits, asserted per record."""
    live = set(live)
    kept, kR, kL, _ = live_tree(r, live)
    fused = getattr(r, "fused", set())
    acc = {ROOT: (0, 0, 0, 0, 0, 0, 0, 0)}
    tot = [0] * 8
    stack = [ROOT]
    while stack:
        n = stack.pop()
        base = acc[n]
        for c in list(kR.get(n, ())) + list(kL.get(n, ())):
            if c in fused:
                acc[c] = base
            else:
                lp, dp, sl, sd, llv, dlv, lL, dL = base
                pay, isl = r.code_bits[c] - 1, r.side[c] == L_
                if c in live:
                    acc[c] = (lp + pay, dp, sl + 1, sd, llv + 1, dlv,
                              lL + isl, dL)
                else:
                    acc[c] = (lp, dp + pay, sl, sd + 1, llv, dlv + 1,
                              lL, dL + isl)
            if c in live:
                t = acc[c]
                for k in range(8):
                    tot[k] += t[k]
                assert t[0] + t[1] + t[2] + t[3] == r.prefix_bits[c]
            stack.append(c)
    return tuple(tot)


def display_after_cut(r, live):
    """The BIT-LEVEL check: rebuild compacted coordinates as banded
    carrier strings -- per level a side char ('a' = R, 'c' = L, so that
    with terminator 'b' the descending sort realizes R < marker < L) then
    the D(label) payload translated '0'->'1','1'->'2', COMPLEMENTED first
    on the L band (the mirrored order). Fused members share their head's
    coordinate (no block of their own). Returns (order, text)."""
    live = set(live)
    kept, kR, kL, _ = live_tree(r, live)
    fused = getattr(r, "fused", set())
    tr = str.maketrans("01", "12")
    coord = {ROOT: ""}
    stack = [ROOT]
    while stack:
        n = stack.pop()
        for c in list(kR.get(n, ())) + list(kL.get(n, ())):
            if c in fused:
                coord[c] = coord[n]
            else:
                w = OCM.d_enc(r.label[c])
                coord[c] = coord[n] + (
                    "a" + w.translate(tr) if r.side[c] == R_
                    else "c" + comp(w).translate(tr))
            stack.append(c)
    order = sorted(live, key=lambda x: coord[x] + "b", reverse=True)
    return order, "".join(r.char[x] for x in order)


# ------------------------------------------------------------ drivers
def run_sequential(doc, cut_every, fuse=False):
    """Single-author sided replay; periodic cuts on the same schedule as
    the one-sided script, each gated by walk equality (reads identical
    before/after). Returns (r, state, rows, end, gates)."""
    r = SidedReplay()
    state = (0, [], set(), set())
    rows, gates = [], []
    next_cut = cut_every
    for txn in doc["txns"]:
        state = r.apply_patches(state, 0, txn["patches"])
        if next_cut is not None and state[0] >= next_cut:
            live = state[2] - state[3]
            before = live_bits(r, live)
            pre = walk_display(r, live)
            compact_cut(r, live, fuse)
            gates.append(pre == walk_display(r, live))
            rows.append((state[0], len(live), before, live_bits(r, live)))
            while next_cut <= state[0]:
                next_cut += cut_every
    end = "".join(r.char[x] for x in state[1])
    return r, state, rows, end, gates


def run_concurrent(doc):
    """Concurrent sided replay (driver transliterated from the one-sided
    script); merged views come from the global full order filtered by the
    branch's causal set; locality of the policy lookups is audited."""
    r = SidedReplay()
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
            state = (clock, r.list_view(ins, dels), ins, dels)
        state = r.apply_patches(state, txn.get("agent", 0), txn["patches"],
                                audit=True)
        states[idx] = state
        final = state
    end = "".join(r.char[x] for x in final[1])
    return r, final, end


def one_sided_columns(doc, concurrent, cut_every):
    """Rerun the imported one-sided algorithm; returns the headline
    (before, renumber, fused) exactly as embed_compact_measure computes
    them (control / subject-R final cut / subject-F final cut)."""
    if concurrent:
        r, state, _ = OCM.run_concurrent(doc)
        live = state[2] - state[3]
        before = OCM.live_bits(r, live)
        OCM.compact_cut(r, live)
        after = OCM.live_bits(r, live)
        OCM.compact_cut(r, live, fuse=True)
        return before, after, OCM.live_bits(r, live)
    rc, sc, _, _ = OCM.run_sequential(doc, None)
    rr, sr, _, _ = OCM.run_sequential(doc, cut_every)
    rf, sf, _, _ = OCM.run_sequential(doc, cut_every, True)
    before = OCM.live_bits(rc, sc[2] - sc[3])
    lr = sr[2] - sr[3]
    OCM.compact_cut(rr, lr)
    after = OCM.live_bits(rr, lr)
    lf = sf[2] - sf[3]
    OCM.compact_cut(rf, lf, fuse=True)
    return before, after, OCM.live_bits(rf, lf)


# ------------------------------------------------------------- report
def fmt(n):
    return f"{n:,}"


def h_bits(p):
    return 0.0 if p in (0.0, 1.0) else -p * math.log2(p) - (1 - p) * math.log2(1 - p)


def measure(path):
    with gzip.open(path, "rt", encoding="utf-8") as f:
        doc = json.load(f)
    name = os.path.basename(path).replace(".json.gz", "")
    concurrent = doc.get("kind") == "concurrent"
    n_events = sum(p[1] + len(p[2]) for t in doc["txns"] for p in t["patches"])
    n_chars = len(doc["endContent"])
    print(f"\n== {name}  [{'concurrent, final cut only' if concurrent else 'sequential: fully settled, periodic cuts'}]")

    if concurrent:
        r, state, end = run_concurrent(doc)
        rows = rows_f = []
        r_ctl = r_f = state_f = live_ctl = cut_every = None
        gates = []
    else:
        cut_every = max(1000, n_events // 8)
        r_ctl, state_ctl, _, end_ctl, _ = run_sequential(doc, None)  # control
        r, state, rows, end, g_r = run_sequential(doc, cut_every)    # subject R
        r_f, state_f, rows_f, end_f, g_f = run_sequential(doc, cut_every, True)
        assert end_ctl == end == end_f
        live_ctl = state_ctl[2] - state_ctl[3]
        gates = g_r + g_f
    live = state[2] - state[3]
    nm = r.n_R + r.n_L
    pL = r.n_L / nm
    # replay gate: the sided display order (semantic walk) spells endContent
    walk_r = r_ctl if r_ctl else r
    walk0 = walk_display(walk_r, live_ctl if r_ctl else live)
    ok = end == doc["endContent"]
    walk_ok = "".join(walk_r.char[x] for x in walk0) == doc["endContent"]
    print(f"   events={fmt(n_events)}  inserts={fmt(nm)}  live chars={fmt(n_chars)}"
          f"  L-mints={pL:.3f}  H(side)={h_bits(pL):.3f} b"
          f"  [view {'OK' if ok else 'MISMATCH'}, sided walk {'OK' if walk_ok else 'MISMATCH'}]")
    if concurrent and (r.vis_miss or r.hasr_miss):
        print(f"   LOCALITY MISSES: successor unseen {r.vis_miss}, has-R divergent {r.hasr_miss}")

    if rows:
        print(f"   periodic cuts every {fmt(cut_every)} events (R / F subjects, own histories):")
        print("      cut@event      live    R bits before    R bits after    F bits after")
        for (ev, nl, b, a), (_, _, _, af) in zip(rows, rows_f):
            print(f"   {fmt(ev):>12}  {fmt(nl):>8}  {fmt(b):>15}  {fmt(a):>14}  {fmt(af):>14}")

    before_ctl = live_bits(r_ctl, live_ctl) if r_ctl else live_bits(r, live)
    # COLUMN 2: renumber-only final settled cut (+ its reads gate)
    pre = walk_display(r, live)
    ties, _, _ = compact_cut(r, live)
    gates.append(pre == walk_display(r, live))
    after_subj = live_bits(r, live)
    order_ok = order_f_ok = None
    if not concurrent:
        o, txt = display_after_cut(r, live)
        order_ok = txt == doc["endContent"] and o == walk_display(r, live)
        compact_cut(r_ctl, live_ctl)
        match = OCM.live_bits(r_ctl, live_ctl) == after_subj  # live_bits alias
    else:
        match = None
    # COLUMN 3: renumber+fusion final settled cut, on every history
    pre = walk_display(r, live)
    _, sp_r, lv_r = compact_cut(r, live, fuse=True)
    gates.append(pre == walk_display(r, live))
    fused_from_r = live_bits(r, live)
    if not concurrent:
        live_f = state_f[2] - state_f[3]
        pre = walk_display(r_f, live_f)
        _, sp, lv = compact_cut(r_f, live_f, fuse=True)
        gates.append(pre == walk_display(r_f, live_f))
        fused = live_bits(r_f, live_f)
        o, txt = display_after_cut(r_f, live_f)
        order_f_ok = txt == doc["endContent"] and o == walk_display(r_f, live_f)
        compact_cut(r_ctl, live_ctl, fuse=True)
        fused_ctl = live_bits(r_ctl, live_ctl)
        match_f = fused_ctl == fused == fused_from_r
    else:
        fused, sp, lv, match_f = fused_from_r, sp_r, lv_r, None
    # attribution on the fused final tree (control history where available)
    diag_r, diag_live = (r_ctl, live_ctl) if r_ctl else (r, live)
    lp, dp, sl, sd, llv, dlv, lL, dL = attribute_bits(diag_r, diag_live)
    assert lp + dp + sl + sd == fused  # every bit accounted
    nl = max(1, len(diag_live))

    # the one-sided columns, same trace, the imported algorithm rerun
    os_b, os_r, os_f = one_sided_columns(doc, concurrent, cut_every)

    print(f"   SIDED  uncompacted     : {fmt(before_ctl):>14} bits  {before_ctl / n_chars:9.3f} b/ch"
          f"      one-sided: {os_b / n_chars:9.3f} b/ch")
    print(f"   SIDED  renumber final  : {fmt(after_subj):>14} bits  {after_subj / n_chars:9.3f} b/ch"
          f"      one-sided: {os_r / n_chars:9.3f} b/ch")
    print(f"   SIDED  renumber+fusion : {fmt(fused):>14} bits  {fused / n_chars:9.3f} b/ch"
          f"      one-sided: {os_f / n_chars:9.3f} b/ch"
          f"   [spines {fmt(sp)}, levels removed {fmt(lv)}]")
    print(f"   reduction sided {before_ctl / max(1, fused):5.2f}x   vs one-sided {os_b / max(1, os_f):5.2f}x")
    print(f"   fused bits: LIVE payload {lp / n_chars:8.3f} + DEAD payload {dp / n_chars:7.3f}"
          f" + SIDE bits {(sl + sd) / n_chars:8.3f} b/ch (live {sl / n_chars:.3f} / dead {sd / n_chars:.3f})")
    print(f"   levels/coord: live {llv / nl:.1f} (L-band {lL / max(1, llv):.3f}) "
          f"+ dead {dlv / nl:.1f} (L-band {dL / max(1, dlv):.3f});"
          f" side bit = 1.000 b/level flat")
    gate_n = sum(gates)
    print(f"   reads identical at cuts: {gate_n}/{len(gates)}"
          + ("" if gate_n == len(gates) else "  <-- GATE FAILED"))
    if match is not None:
        print("   history-independence: renumber "
              + ("MATCH" if match else "MISMATCH -- FALSIFIED")
              + ", fused three-way " + ("MATCH" if match_f else "MISMATCH -- FALSIFIED"))
    else:
        print(f"   history-independence: n/a (single final cut)  [sibling (ts,agent) ties: {ties}]")
    if not concurrent:
        print(f"   bit-level display: renumbered {'ORDER+TEXT OK' if order_ok else 'MISMATCH'},"
              f" fused {'ORDER+TEXT OK' if order_f_ok else 'MISMATCH'}")
    return dict(name=name, chars=n_chars, before=before_ctl, after=after_subj,
                fused=fused, os_b=os_b, os_r=os_r, os_f=os_f, pL=pL,
                side_pc=(sl + sd) / n_chars, sl_pc=sl / n_chars,
                sd_pc=sd / n_chars, gates=(gate_n, len(gates)),
                ok=ok and walk_ok, order_ok=order_ok, order_f_ok=order_f_ok,
                match=match, match_f=match_f, concurrent=concurrent)


if __name__ == "__main__":
    args = sys.argv[1:] or [
        os.path.join(HERE, "traces", t) for t in (
            "automerge-paper.json.gz", "seph-blog1.json.gz",
            "friendsforever_flat.json.gz", "clownschool_flat.json.gz",
            "friendsforever.json.gz", "clownschool.json.gz")
    ]
    missing = [p for p in args if not os.path.exists(p)]
    for p in missing:
        print("MISSING TRACE:", p)
    results = [measure(p) for p in args if os.path.exists(p)]
    if results:
        print("\n== SUMMARY (bits/char over live records; S=sided/Fugue, 1=one-sided)")
        print(f"   {'trace':<20} {'chars':>8} {'S-bef':>8} {'S-ren':>7} {'S-fus':>7} {'S-red':>6}"
              f" {'1-bef':>8} {'1-ren':>7} {'1-fus':>7} {'1-red':>6} {'L-mint':>6} {'H(s)':>5} {'side b/ch':>9}")
        for x in results:
            c = x["chars"]
            print(f"   {x['name']:<20} {fmt(c):>8} {x['before']/c:>8.1f} {x['after']/c:>7.1f}"
                  f" {x['fused']/c:>7.2f} {x['before']/max(1,x['fused']):>5.2f}x"
                  f" {x['os_b']/c:>8.1f} {x['os_r']/c:>7.1f} {x['os_f']/c:>7.2f}"
                  f" {x['os_b']/max(1,x['os_f']):>5.2f}x"
                  f" {x['pL']:>6.3f} {h_bits(x['pL']):>5.3f} {x['side_pc']:>9.2f}")
        bad = [x["name"] for x in results if not x["ok"]
               or x["gates"][0] != x["gates"][1]
               or x["order_ok"] is False or x["order_f_ok"] is False
               or x["match"] is False or x["match_f"] is False]
        print("   gates:", "ALL PASS" if not bad else f"FAILURES in {bad}")
