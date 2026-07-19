#!/usr/bin/env python3
"""
run_table_measure.py -- Task #73: the LOSSLESS RUN-TABLE REPRESENTATION of
the embed RGA's live chains, measured on the real editing traces next to the
chain representation and its compaction stack (embed_compact_measure.py,
embed_sided_compact_measure.py; design + measured context in
whiteboard/embed-recoding-note.md, the note for THIS design in
whiteboard/run-table-note.md).

THE REPRESENTATION. Work over the kept tree (live records plus their dead
ancestors; everything else is gone, tombstone-free). Call the edge from a
node p to its child c FUSIBLE when c is p's unique kept child, delta(c) = 1,
side(c) = R (one-sided: always), and live(c) = live(p). A RUN (table entry)
is a maximal fusible chain; live runs carry records, dead entries carry
structure only. A record's address is (run-id, offset). The table is pure
representation metadata over the immutable chain semantics: coordinates,
timestamps and the display order are all reconstructible from it (gated
below, exactly, per record), and it exists for EVERY state -- no stability
gate, no settled cut; the PBT builds it mid-flight on unmerged states.

TAIL-ATTACHMENT INVARIANT (checked on every build): in the canonical table
every entry attaches at its parent entry's LAST member, because an interior
member's unique kept child is its run successor by maximality. Hence the
comparator never materializes chains: within a run, display order = offset
order; across runs, compare the two entry chains, and at the first
difference compare branch headers (one-sided: newest first; sided: L band
ascending, node, R band descending) -- the divergence node is always a tail.

ACCOUNTING MODEL (every pointer and header bit counted; the same Elias
delta D and, for the chain columns, the same per-level cost as the landed
scripts):
  chain representation, per record: sum over its kept-chain levels of
    |D(delta_level)|, plus 1 side bit per level in the sided model
    (= prefix_bits of the landed scripts; "chain-fused" = after the
    renumber+fusion epoch, the current best).
  run-table representation:
    per record: run-id at W = ceil(log2(N_entries + 1)) bits (one id space
      for all entries plus the root sentinel) + offset as D(offset + 1);
    per entry header: 1 liveness flag + W parent ref + D(parent_offset + 1)
      + D(head delta) + D(length) + 1 side bit (sided model only).
  Not charged on either side: the (ts, agent) concurrency tie-break, which
  neither representation encodes in its bits (the landed scripts count ties
  and skip the bit-level display check on the concurrent traces; same here).

GATES: (a) display identity: table walk == chain display order, text ==
endContent (sequential; concurrent: order identity against the model's own
display, ties counted); (b) pairwise comparator sampled against display
positions; (c) losslessness: per-record coordinate bit length reconstructed
from the table alone == the chain accounting, every live record; (d) the
same after a renumber+fusion epoch with the table REBUILT (the composed
column); (e) randomized PBT with concurrent merges + directed cases
(mid-run concurrent insert, delete splitting liveness, foreign run into a
gap, coalesce after undo, materialization under a vanished anchor, sided
L-split), each with hand-derived expected text and a no-split rival pinned
wrong; incremental split/extend/coalesce rules checked == canonical rebuild
after every event.

Usage: python3 run_table_measure.py [trace.json.gz ...]   (no args: PBT +
directed cases, then the standard six traces)
"""

import gzip
import json
import math
import os
import random
import sys
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from entropy_measure import Replay, bits_D, ROOT
import embed_compact_measure as OCM
import embed_sided_compact_measure as SCM

R_, L_ = 'R', 'L'


# ------------------------------------------------------------ the table
class Entry:
    __slots__ = ("live", "parent", "side", "delta", "members")

    def __init__(self, live, parent, side, delta, members):
        self.live = live          # uniform over members
        self.parent = parent      # (eid, offset) or None (root-attached)
        self.side = side          # 'R' / 'L' (one-sided: 'R')
        self.delta = delta        # head's delta/label; members after: 1
        self.members = members    # node ids, chain order


class Table:
    __slots__ = ("entries", "att", "loc", "roots")

    def __init__(self):
        self.entries = []
        self.att = []             # eid -> [child eids], all at the tail
        self.loc = {}             # node -> (eid, offset)
        self.roots = []


def build_table(children, delta, side, live):
    """Canonical table over a kept tree given as children[node] -> kids
    (children[ROOT] = the top level). delta/side are per-node maps (side
    None = one-sided). Runs = maximal fusible chains, greedy from the top;
    unique partition since fusibility is a per-edge predicate."""
    t = Table()
    stack = [(c, None) for c in children.get(ROOT, ())]
    while stack:
        c, ploc = stack.pop()
        eid = len(t.entries)
        e = Entry(c in live, ploc, side[c] if side else R_, delta[c], [c])
        t.entries.append(e)
        t.att.append([])
        if ploc is None:
            t.roots.append(eid)
        else:
            t.att[ploc[0]].append(eid)
        t.loc[c] = (eid, 0)
        n = c
        while True:
            ks = children.get(n, ())
            if len(ks) == 1:
                k = ks[0]
                if delta[k] == 1 and (side is None or side[k] == R_) \
                        and ((k in live) == (n in live)):
                    e.members.append(k)
                    t.loc[k] = (eid, len(e.members) - 1)
                    n = k
                    continue
            break
        tail_loc = (eid, len(e.members) - 1)
        for k in children.get(n, ()):
            stack.append((k, tail_loc))
    # the tail-attachment invariant, at scale
    for e in t.entries:
        if e.parent is not None:
            pe, po = e.parent
            assert po == len(t.entries[pe].members) - 1, "interior attachment"
    return t


def reconstruct_bits(t, r, live, sided, check_ts=True):
    """Losslessness gate: recompute every live record's coordinate bit
    length FROM THE TABLE ALONE (head levels cost |D(delta)|, run levels
    |D(1)| = 1, +1 side bit per level in the sided model) and compare with
    the chain accounting r.prefix_bits. On the raw table also recompute
    head timestamps (parent ts + delta) against r.ts; after a renumbering
    epoch labels are rank ordinals, not time deltas, so the ts check is
    skipped there (the epoch deliberately forgets time, as the recoding
    note records). Returns (n_checked, n_level_sum)."""
    raw_ts_skip = not check_ts
    lvl1 = bits_D(1) + (1 if sided else 0)

    def head_cost(d):
        return bits_D(d) + (1 if sided else 0)

    cum = {}      # eid -> bits through the entry's tail
    lvls = {}     # eid -> levels through the entry's tail
    n_checked = n_levels = 0
    stack = list(t.roots)
    while stack:
        eid = stack.pop()
        e = t.entries[eid]
        if e.parent is None:
            base_b, base_l, pts = 0, 0, 0
        else:
            pe, po = e.parent
            base_b = cum[pe]
            base_l = lvls[pe]
            pts = r.ts[t.entries[pe].members[po]]
        if not raw_ts_skip:
            assert r.ts[e.members[0]] - pts == e.delta, \
                "ts not reconstructible"
        k = len(e.members)
        cum[eid] = base_b + head_cost(e.delta) + (k - 1) * lvl1
        lvls[eid] = base_l + k
        if e.live:
            for off, m in enumerate(e.members):
                got = base_b + head_cost(e.delta) + off * lvl1
                assert got == r.prefix_bits[m], \
                    f"coordinate bits not reconstructible at {m}"
                n_checked += 1
                n_levels += base_l + off + 1
        stack.extend(t.att[eid])
    assert n_checked == len(live)
    return n_checked, n_levels


def account(t, sided):
    """The explicit bit-accounting model. Returns a component dict; total
    = every pointer and header bit of the representation."""
    n_ent = len(t.entries)
    w = max(1, n_ent.bit_length())          # ceil(log2(n_ent + 1))
    n_rec = sum(len(e.members) for e in t.entries if e.live)
    rec_id = n_rec * w
    rec_off = sum(bits_D(j + 1) for e in t.entries if e.live
                  for j in range(len(e.members)))
    hdr_flag = n_ent
    hdr_parent = n_ent * w
    hdr_poff = sum(bits_D((e.parent[1] if e.parent else 0) + 1)
                   for e in t.entries)
    hdr_delta = sum(bits_D(e.delta) for e in t.entries)
    hdr_len = sum(bits_D(len(e.members)) for e in t.entries)
    hdr_side = n_ent if sided else 0
    n_L = sum(1 for e in t.entries if e.side == L_)
    total = rec_id + rec_off + hdr_flag + hdr_parent + hdr_poff \
        + hdr_delta + hdr_len + hdr_side
    return dict(total=total, rec_id=rec_id, rec_off=rec_off,
                hdr_flag=hdr_flag, hdr_parent=hdr_parent, hdr_poff=hdr_poff,
                hdr_delta=hdr_delta, hdr_len=hdr_len, hdr_side=hdr_side,
                n_ent=n_ent, n_rec=n_rec, w=w, n_L=n_L,
                n_live_runs=sum(1 for e in t.entries if e.live))


def depth_stats(t):
    """Contracted-tree depth: entries on the path per live record."""
    depth = {}
    stack = list(t.roots)
    for eid in stack:
        depth[eid] = 1
    while stack:
        eid = stack.pop()
        for c in t.att[eid]:
            depth[c] = depth[eid] + 1
            stack.append(c)
    tot = n = 0
    mx = 0
    for eid, e in enumerate(t.entries):
        if e.live:
            tot += depth[eid] * len(e.members)
            n += len(e.members)
            mx = max(mx, depth[eid])
    return (tot / max(1, n), mx)


def boundary_reasons(t):
    """Why does each entry exist (fail to fuse upward)?"""
    out = defaultdict(int)
    for e in t.entries:
        if e.parent is None:
            out['root'] += 1
        elif len(t.att[e.parent[0]]) > 1:
            out['branch'] += 1
        elif e.delta != 1:
            out['jump'] += 1
        elif e.side == L_:
            out['sideL'] += 1
        else:
            out['liveflip'] += 1
    return dict(out)


# ---------------------------------------------------- walk and comparator
def table_walk(t, r, sided):
    """Display order from the table alone (plus the (ts, agent) tie-break
    data, which the chain representation also keeps outside its coordinate
    bits). One-sided: entry = members in offset order, then attachments
    newest first. Sided: interior members, then the tail's L attachments
    (label ascending), the tail, the R attachments (label descending)."""
    E = t.entries

    def key(eid):
        h = E[eid].members[0]
        return (E[eid].delta, r.ts[h], r.agent[h])

    def expand(att_list, live, members):
        if not sided:
            items = [('N', m) for m in members] if live else []
            items += [('E', c) for c in
                      sorted(att_list, key=lambda i: (
                          r.ts[E[i].members[0]], r.agent[E[i].members[0]]),
                          reverse=True)]
            return items
        Lb = sorted((c for c in att_list if E[c].side == L_), key=key)
        Rb = sorted((c for c in att_list if E[c].side == R_), key=key,
                    reverse=True)
        items = [('N', m) for m in members[:-1]] if live else []
        items += [('E', c) for c in Lb]
        if live and members:
            items.append(('N', members[-1]))
        items += [('E', c) for c in Rb]
        return items

    out = []
    stack = list(reversed(expand(t.roots, False, [])))
    while stack:
        kind, v = stack.pop()
        if kind == 'N':
            out.append(v)
        else:
            e = E[v]
            stack.extend(reversed(expand(t.att[v], e.live, e.members)))
    return out


def make_cmp(t, r, sided):
    """The pairwise comparator: walk the two entry chains to the first
    difference; by the tail-attachment invariant the divergence node is a
    tail (or an offset within a shared entry), so only header fields are
    consulted, never materialized chains."""
    E = t.entries
    chains = {}

    def chain(eid):
        c = chains.get(eid)
        if c is not None:
            return c
        todo = []
        cur = eid
        while cur is not None and cur not in chains:
            todo.append(cur)
            p = E[cur].parent
            cur = p[0] if p else None
        base = chains[cur] if cur is not None else ()
        for x in reversed(todo):
            base = base + (x,)
            chains[x] = base
        return chains[eid]

    def cmp(x, y):
        if x == y:
            return 0
        (ex, ox), (ey, oy) = t.loc[x], t.loc[y]
        cx, cy = chain(ex), chain(ey)
        n = min(len(cx), len(cy))
        i = 0
        while i < n and cx[i] == cy[i]:
            i += 1
        if i == len(cx) and i == len(cy):        # same entry: offset order
            return -1 if ox < oy else 1
        if i == len(cx):                          # x's entry on y's path
            if not sided:
                return -1                         # ancestor side first
            if ox < len(E[ex].members) - 1:
                return -1                         # y under x's R subtree
            return 1 if E[cy[i]].side == L_ else -1
        if i == len(cy):                          # mirror
            if not sided:
                return 1
            if oy < len(E[ey].members) - 1:
                return 1
            return -1 if E[cx[i]].side == L_ else 1
        bx, by = E[cx[i]], E[cy[i]]               # branches at one tail
        hx, hy = bx.members[0], by.members[0]
        if not sided:
            kx, ky = (r.ts[hx], r.agent[hx]), (r.ts[hy], r.agent[hy])
            return -1 if kx > ky else 1           # newest first
        if bx.side != by.side:
            return -1 if bx.side == L_ else 1     # L band, node, R band
        kx = (bx.delta, r.ts[hx], r.agent[hx])
        ky = (by.delta, r.ts[hy], r.agent[hy])
        if bx.side == L_:
            return -1 if kx < ky else 1           # L ascending
        return -1 if kx > ky else 1               # R descending
    return cmp


def gate_comparator(t, r, sided, order, samples, rng):
    """Sampled pairwise comparator vs display positions (+ all adjacent
    pairs up to the sample budget). Returns (pass, total)."""
    cmp = make_cmp(t, r, sided)
    pos = {x: i for i, x in enumerate(order)}
    n = len(order)
    ok = tot = 0
    if n >= 2:
        for _ in range(samples):
            x, y = rng.sample(order, 2)
            tot += 1
            ok += (cmp(x, y) < 0) == (pos[x] < pos[y]) and cmp(x, y) == -cmp(y, x)
        step = max(1, n // samples)
        for i in range(0, n - 1, step):
            x, y = order[i], order[i + 1]
            tot += 1
            ok += cmp(x, y) < 0
    return ok, tot


# --------------------------------------------------------- trace drivers
def onesided_state(doc, concurrent):
    if concurrent:
        r, state, end = OCM.run_concurrent(doc)
    else:
        r, state, _, end = OCM.run_sequential(doc, None)
    live = state[2] - state[3]
    return r, state, live, end


def sided_state(doc, concurrent):
    if concurrent:
        r, state, end = SCM.run_concurrent(doc)
    else:
        r, state, _, end, _ = SCM.run_sequential(doc, None)
    live = state[2] - state[3]
    return r, state, live, end


def contracted_children(kept, fused, parent_map):
    ch = defaultdict(list)
    for x in kept:
        if x in fused:
            continue
        p = parent_map[x]
        while p in fused:
            p = parent_map[p]
        ch[p].append(x)
    return ch


def measure_family(doc, name, concurrent, sided, n_chars, rng):
    """One representation family (one-sided or sided/Fugue): chain before
    and fused columns, run table on raw chains, run table composed with the
    renumber+fusion epoch; all gates. Returns the row dict."""
    if sided:
        r, state, live, end = sided_state(doc, concurrent)
        kept, kR, kL, ties = SCM.live_tree(r, live)
        children = {n: list(kR.get(n, ())) + list(kL.get(n, ()))
                    for n in list(kR.keys()) + list(kL.keys())}
        order0 = SCM.walk_display(r, live)
        delta_map, side_map, parent_map = r.delta, r.side, r.parent
        label_map = r.label
    else:
        r, state, live, end = onesided_state(doc, concurrent)
        kept, children, ties = OCM.live_tree(r, live)
        order0 = [x for x in r.dfs_view(state[2], state[3])]
        delta_map, side_map, parent_map = r.delta, None, r.anchor
        label_map = r.ordinal
    text0 = "".join(r.char[x] for x in order0)
    chain_before = sum(r.prefix_bits[x] for x in live)

    # ---- run table on RAW chains (before any epoch)
    t_raw = build_table(children, delta_map, side_map, live)
    walk_raw = table_walk(t_raw, r, sided)
    g_order_raw = walk_raw == order0
    g_text_raw = text0 == doc["endContent"]
    n_rec, n_levels = reconstruct_bits(t_raw, r, live, sided)
    acc_raw = account(t_raw, sided)
    dep_raw = depth_stats(t_raw)
    bnd_raw = boundary_reasons(t_raw)
    cmp_raw = gate_comparator(t_raw, r, sided, order0, 4000, rng)

    # ---- the composed column: renumber+fusion epoch, table REBUILT
    if sided:
        SCM.compact_cut(r, live, fuse=True)
    else:
        OCM.compact_cut(r, live, fuse=True)
    chain_fused = sum(r.prefix_bits[x] for x in live)
    ch2 = contracted_children(kept, r.fused, parent_map)
    t_cmp = build_table(ch2, label_map, side_map, live)
    walk_cmp = table_walk(t_cmp, r, sided)
    g_order_cmp = walk_cmp == order0
    _, n_levels_f = reconstruct_bits(t_cmp, r, live, sided, check_ts=False)
    acc_cmp = account(t_cmp, sided)
    dep_cmp = depth_stats(t_cmp)
    bnd_cmp = boundary_reasons(t_cmp)
    cmp_cmp = gate_comparator(t_cmp, r, sided, order0, 4000, rng)

    return dict(
        chain_before=chain_before, chain_fused=chain_fused,
        raw=acc_raw, cmpd=acc_cmp, dep_raw=dep_raw, dep_cmp=dep_cmp,
        bnd_raw=bnd_raw, bnd_cmp=bnd_cmp,
        g_order=(g_order_raw, g_order_cmp), g_text=g_text_raw,
        cmp_gates=(cmp_raw, cmp_cmp), ties=ties,
        n_levels=n_levels, n_levels_f=n_levels_f, n_rec=n_rec,
        end_ok=end == doc["endContent"])


def fmt(n):
    return f"{n:,}"


def report_family(tag, m, n_chars):
    print(f"   [{tag}] chain: before {m['chain_before'] / n_chars:9.2f}"
          f"  fused {m['chain_fused'] / n_chars:9.3f} b/ch"
          f"  (levels/coord raw {m['n_levels'] / m['n_rec']:.1f},"
          f" fused {m['n_levels_f'] / m['n_rec']:.1f})")
    for lbl, acc, dep, bnd in (("raw     ", m['raw'], m['dep_raw'], m['bnd_raw']),
                               ("composed", m['cmpd'], m['dep_cmp'], m['bnd_cmp'])):
        a = acc
        mean_len = a['n_rec'] / max(1, a['n_live_runs'])
        print(f"   [{tag}] run-table {lbl}: {a['total'] / n_chars:8.3f} b/ch"
              f"  = rec(id {a['rec_id'] / n_chars:.2f} + off {a['rec_off'] / n_chars:.2f})"
              f" + hdr(parent {a['hdr_parent'] / n_chars:.2f}"
              f" + delta {a['hdr_delta'] / n_chars:.2f}"
              f" + len {a['hdr_len'] / n_chars:.2f}"
              f" + poff {a['hdr_poff'] / n_chars:.2f}"
              f" + flag {a['hdr_flag'] / n_chars:.2f}"
              + (f" + side {a['hdr_side'] / n_chars:.2f}" if a['hdr_side'] else "")
              + ")")
        print(f"   [{tag}]   entries {fmt(a['n_ent'])} (live runs"
              f" {fmt(a['n_live_runs'])}, mean len {mean_len:.1f},"
              f" dead {fmt(a['n_ent'] - a['n_live_runs'])},"
              f" L {fmt(a['n_L']) if a['hdr_side'] else 'n/a'});"
              f" id width {a['w']} b;"
              f" contracted depth mean {dep[0]:.2f} max {dep[1]};"
              f" boundaries {bnd}")
    (okr, totr), (okc, totc) = m['cmp_gates']
    print(f"   [{tag}] gates: order raw {'OK' if m['g_order'][0] else 'FAIL'}"
          f" / composed {'OK' if m['g_order'][1] else 'FAIL'};"
          f" text {'OK' if m['g_text'] else 'MISMATCH (ties: %d)' % m['ties']};"
          f" comparator raw {okr}/{totr}, composed {okc}/{totc};"
          f" reconstruction {fmt(m['n_rec'])} records exact")


def measure(path, rng):
    with gzip.open(path, "rt", encoding="utf-8") as f:
        doc = json.load(f)
    name = os.path.basename(path).replace(".json.gz", "")
    concurrent = doc.get("kind") == "concurrent"
    n_chars = len(doc["endContent"])
    print(f"\n== {name}  [{'concurrent, final-state table' if concurrent else 'sequential'}]  chars={fmt(n_chars)}")
    rows = {}
    for sided, tag in ((False, "1-sided"), (True, "sided/F")):
        m = measure_family(doc, name, concurrent, sided, n_chars, rng)
        report_family(tag, m, n_chars)
        rows[tag] = m
    return dict(name=name, chars=n_chars, concurrent=concurrent, rows=rows)


def summarize(results):
    print("\n== SUMMARY (bits per live char; cf = chain fused, the landed best;"
          " rt = run table raw; rtc = run table composed with renumber+fusion)")
    print(f"   {'trace':<20} {'fam':<7} {'ch-bef':>8} {'cf':>8} {'rt':>8}"
          f" {'rtc':>7} {'cf/rtc':>6} {'depth':>11} {'side b/ch':>16}")
    all_ok = True
    for x in results:
        c = x['chars']
        for tag in ("1-sided", "sided/F"):
            m = x['rows'][tag]
            side_chain = m['n_levels_f'] / c if tag == "sided/F" else 0
            side_rt = m['cmpd']['hdr_side'] / c
            dep = f"{m['dep_cmp'][0]:.1f}/{m['dep_cmp'][1]}"
            sc = (f"{side_chain:8.2f}->{side_rt:6.3f}" if tag == "sided/F"
                  else f"{'':>16}")
            print(f"   {x['name']:<20} {tag:<7}"
                  f" {m['chain_before'] / c:>8.1f}"
                  f" {m['chain_fused'] / c:>8.2f}"
                  f" {m['raw']['total'] / c:>8.2f}"
                  f" {m['cmpd']['total'] / c:>7.2f}"
                  f" {m['chain_fused'] / max(1, m['cmpd']['total']):>5.1f}x"
                  f" {dep:>11} {sc}")
            (okr, totr), (okc, totc) = m['cmp_gates']
            if not (m['g_order'][0] and m['g_order'][1] and okr == totr
                    and okc == totc and m['end_ok']):
                all_ok = False
                print(f"      ^^ GATE FAILURE on {x['name']} {tag}")
    print("   trace gates:", "ALL PASS" if all_ok else "FAILURES (see above)")


# ------------------------------------------- incremental rules (one-sided)
class Inc:
    """The run table maintained incrementally under the note's mutation
    rules: insert = (split if the anchor is interior) + attach a singleton
    + coalesce; delete = split-to-tail, then carve a dead entry (if kept)
    or vanish (if not), with coalesce and dead-tail trimming; delivery of
    an op whose anchor chain has vanished locally re-materializes dead
    entries from the op's carried chain data (here: the shared birth
    tree, standing for the coordinate the embed op carries). Checked
    against the canonical rebuild after every event in the PBT."""

    def __init__(self, r):
        self.r = r
        self.entries = {}
        self.att = defaultdict(list)
        self.loc = {}
        self.roots = []
        self._next = 0
        self.stats = defaultdict(int)

    def _new(self, live, parent, delta, members):
        eid = self._next
        self._next += 1
        self.entries[eid] = Entry(live, parent, R_, delta, members)
        for j, m in enumerate(members):
            self.loc[m] = (eid, j)
        if parent is None:
            self.roots.append(eid)
        else:
            self.att[parent[0]].append(eid)
        return eid

    def _split(self, eid, j):
        """Make member j its entry's tail (the mid-run split)."""
        e = self.entries[eid]
        if j == len(e.members) - 1:
            return
        self.stats['splits'] += 1
        tail = e.members[j + 1:]
        e.members = e.members[:j + 1]
        nid = self._next
        self._next += 1
        self.entries[nid] = Entry(e.live, (eid, j), R_, 1, tail)
        for k, m in enumerate(tail):
            self.loc[m] = (nid, k)
        self.att[nid] = self.att[eid]          # old-tail attachments move
        for c in self.att[nid]:
            self.entries[c].parent = (nid, len(tail) - 1)
        self.att[eid] = [nid]

    def _coalesce(self, eid):
        """Fuse the entry with its unique attachment while fusible."""
        while eid in self.entries:
            e = self.entries[eid]
            if len(self.att[eid]) != 1:
                return
            cid = self.att[eid][0]
            c = self.entries[cid]
            if c.live != e.live or c.delta != 1 or c.side != R_:
                return
            self.stats['coalesces'] += 1
            base = len(e.members)
            e.members += c.members
            for k, m in enumerate(c.members):
                self.loc[m] = (eid, base + k)
            moved = self.att.pop(cid, [])
            self.att[eid] = moved
            for g in moved:
                self.entries[g].parent = (eid, len(e.members) - 1)
            del self.entries[cid]

    def _remove(self, eid):
        e = self.entries.pop(eid)
        self.att.pop(eid, None)
        if e.parent is None:
            self.roots.remove(eid)
            return
        pe = e.parent[0]
        self.att[pe].remove(eid)
        self._trim(pe)

    def _trim(self, eid):
        """Dead tail members with no children are not kept: drop them,
        cascading; then see whether the parent can re-coalesce."""
        e = self.entries.get(eid)
        if e is None:
            return
        while (not e.live) and not self.att[eid] and e.members:
            del self.loc[e.members.pop()]
            self.stats['unkept'] += 1
        if not e.members:
            self._remove(eid)
        else:
            self._coalesce(eid)

    def _place(self, node, anchor, live):
        if anchor == ROOT:
            return self._new(live, None, self.r.delta[node], [node])
        eid, j = self.loc[anchor]
        self._split(eid, j)
        nid = self._new(live, (eid, j), self.r.delta[node], [node])
        self._coalesce(eid)
        return nid

    def ensure(self, node):
        """Materialize a vanished (locally deleted, childless) anchor
        chain as dead entries."""
        if node == ROOT or node in self.loc:
            return
        self.ensure(self.r.anchor[node])
        self.stats['materialized'] += 1
        self._place(node, self.r.anchor[node], live=False)

    def insert(self, node, anchor):
        self.ensure(anchor)
        self._place(node, anchor, live=True)

    def delete(self, node):
        if node not in self.loc:
            return                              # vanished: already dead
        eid, j = self.loc[node]
        e = self.entries[eid]
        if not e.live:
            return                              # duplicate delivery
        self._split(eid, j)                     # node becomes the tail
        if self.att[eid]:                       # kept: liveness split
            self.stats['liveness_splits'] += 1
            if len(e.members) == 1:
                e.live = False
                self._coalesce(eid)
                if e.parent is not None:
                    self._coalesce(e.parent[0])
            else:
                e.members.pop()
                nid = self._next
                self._next += 1
                self.entries[nid] = Entry(False, (eid, len(e.members) - 1),
                                          R_, 1, [node])
                self.loc[node] = (nid, 0)
                self.att[nid] = self.att[eid]
                for c in self.att[nid]:
                    self.entries[c].parent = (nid, 0)
                self.att[eid] = [nid]
                self._coalesce(nid)
        else:                                    # not kept: vanishes
            del self.loc[node]
            e.members.pop()
            self.stats['unkept'] += 1
            if not e.members:
                self._remove(eid)


def canon_of_table(t):
    return {(ROOT if e.parent is None
             else t.entries[e.parent[0]].members[e.parent[1]],
             e.live, e.side, e.delta, tuple(e.members))
            for e in t.entries}


def canon_of_inc(inc):
    return {(ROOT if e.parent is None
             else inc.entries[e.parent[0]].members[e.parent[1]],
             e.live, e.side, e.delta, tuple(e.members))
            for e in inc.entries.values()}


def rebuild_from(r, ins, dels):
    live = ins - dels
    kept, children, _ = OCM.live_tree(r, live)
    return build_table(children, r.delta, None, live), live


# ----------------------------------------------------------- directed
def directed():
    print("== directed cases (expected texts hand-derived, never eval'd)")
    oks = []

    def case(name, ok, detail=""):
        oks.append(ok)
        print(f"   {name:<62} {'PASS' if ok else 'FAIL'} {detail}")

    def typing(r, s, agent=0, t0=0, anchor=ROOT):
        ns, prev = [], anchor
        for i, ch in enumerate(s):
            prev = r.mint(t0 + i + 1, agent, prev, ch)
            ns.append(prev)
        return ns

    # D1: a concurrent insert into the middle of a typing run
    r = OCM.AccountingReplay()
    ns = typing(r, "abcdef")
    X = r.mint(7, 1, ns[2], 'X')                 # concurrent, after 'c'
    t, live = rebuild_from(r, set(ns) | {X}, set())
    txt = "".join(r.char[x] for x in table_walk(t, r, False))
    case("D1 mid-run concurrent insert: text abcXdef", txt == "abcXdef", txt)
    case("D1 the run split into three entries", len(t.entries) == 3,
         f"entries={len(t.entries)}")
    rival = Table()                              # the no-split rival table
    rival.entries = [Entry(True, None, R_, 1, list(ns)),
                     Entry(True, (0, 2), R_, 4, [X])]
    rival.att, rival.roots = [[1], []], [0]
    for j, m in enumerate(ns):
        rival.loc[m] = (0, j)
    rival.loc[X] = (1, 0)
    rtxt = "".join(r.char[x] for x in table_walk(rival, r, False))
    case("D1 rival without the split misplaces X", rtxt != "abcXdef",
         f"rival text {rtxt!r}")

    # D2: a delete splitting liveness
    r = OCM.AccountingReplay()
    ns = typing(r, "abcdef")
    t, live = rebuild_from(r, set(ns), {ns[2]})
    txt = "".join(r.char[x] for x in table_walk(t, r, False))
    dead = [e for e in t.entries if not e.live]
    case("D2 delete mid-run: text abdef", txt == "abdef", txt)
    case("D2 three entries, dead 'c' kept as structure",
         len(t.entries) == 3 and len(dead) == 1 and dead[0].members == [ns[2]],
         f"entries={len(t.entries)} dead={len(dead)}")

    # D3: a merge bringing a foreign run into a gap (delivered eventwise)
    r = OCM.AccountingReplay()
    ns = typing(r, "abcdef")
    inc = Inc(r)
    for x in ns:
        inc.insert(x, r.anchor[x])
    fs = typing(r, "XYZ", agent=1, t0=6, anchor=ns[2])
    for x in fs:
        inc.insert(x, r.anchor[x])               # delivery, one op at a time
    t, live = rebuild_from(r, set(ns) | set(fs), set())
    txt = "".join(r.char[x] for x in table_walk(t, r, False))
    foreign = [e for e in t.entries if e.members == fs]
    case("D3 foreign run lands in the gap: text abcXYZdef",
         txt == "abcXYZdef", txt)
    case("D3 foreign run re-coalesced to ONE entry on delivery",
         len(foreign) == 1 and len(t.entries) == 3,
         f"entries={len(t.entries)}")
    case("D3 incremental == canonical", canon_of_inc(inc) == canon_of_table(t))

    # D4: deleting the foreign run: entries re-coalesce to one
    for x in fs:
        inc.delete(x)
    t, live = rebuild_from(r, set(ns) | set(fs), set(fs))
    txt = "".join(r.char[x] for x in table_walk(t, r, False))
    case("D4 undo: text abcdef, table back to ONE entry",
         txt == "abcdef" and len(t.entries) == 1
         and t.entries[0].members == ns)
    case("D4 incremental coalesce == canonical",
         canon_of_inc(inc) == canon_of_table(t))

    # D5: delivery under a vanished anchor re-materializes dead structure
    r = OCM.AccountingReplay()
    ns = typing(r, "abc")
    inc = Inc(r)
    for x in ns:
        inc.insert(x, r.anchor[x])
    inc.delete(ns[2])                            # 'c' vanishes (childless)
    X = r.mint(4, 1, ns[2], 'X')                 # concurrent insert after c
    inc.insert(X, ns[2])                         # delivery materializes c
    t, live = rebuild_from(r, set(ns) | {X}, {ns[2]})
    txt = "".join(r.char[x] for x in table_walk(t, r, False))
    case("D5 materialized dead anchor: text abX", txt == "abX", txt)
    case("D5 incremental == canonical, one materialization",
         canon_of_inc(inc) == canon_of_table(t)
         and inc.stats['materialized'] == 1)

    # D6: sided/Fugue L split (insert after a node with an R child)
    rs = SCM.SidedReplay()
    prev = ROOT
    sn = []
    for i, ch in enumerate("abcdef"):
        prev = rs.mint(i + 1, 0, prev, ch)
        sn.append(prev)
    Xs = rs.mint(7, 1, sn[2], 'X')               # Fugue: (L, successor d)
    live = set(sn) | {Xs}
    kept, kR, kL, _ = SCM.live_tree(rs, live)
    children = {n: list(kR.get(n, ())) + list(kL.get(n, ()))
                for n in set(kR) | set(kL)}
    ts = build_table(children, rs.delta, rs.side, live)
    txt = "".join(rs.char[x] for x in table_walk(ts, rs, True))
    case("D6 sided L-split: text abcXdef", txt == "abcXdef", txt)
    # hand-derivation, corrected once: the L child X lands on d, so it is
    # the edge d->e that breaks, not c->d; the run [a,b,c,d] stays intact
    # with X an L attachment at its tail d (three entries, not four).
    dloc = ts.loc[sn[3]]
    case("D6 sided table: three entries, X = L attachment at tail 'd'",
         len(ts.entries) == 3 and rs.side[Xs] == L_
         and ts.loc[Xs][0] != dloc[0]
         and ts.entries[ts.loc[Xs][0]].parent == dloc
         and dloc[1] == len(ts.entries[dloc[0]].members) - 1,
         f"entries={len(ts.entries)}")
    print(f"   directed: {sum(oks)}/{len(oks)} PASS")
    return all(oks)


# ---------------------------------------------------------------- PBT
def pbt(trials=150, seed=7):
    rng = random.Random(seed)
    n_events = n_states = n_pairs = 0
    stats = defaultdict(int)
    for _ in range(trials):
        r = OCM.AccountingReplay()
        NA = 3
        clock = [0] * NA
        views = [[] for _ in range(NA)]
        inss = [set() for _ in range(NA)]
        delss = [set() for _ in range(NA)]
        inc = Inc(r)                             # mirrors agent 0

        def check(a):
            nonlocal n_states, n_pairs
            t, live = rebuild_from(r, inss[a], delss[a])
            order = r.dfs_view(inss[a], delss[a])
            assert table_walk(t, r, False) == order, "PBT walk mismatch"
            if len(order) <= 45:
                cmp = make_cmp(t, r, False)
                for i in range(len(order)):
                    for j in range(i + 1, len(order)):
                        assert cmp(order[i], order[j]) < 0 \
                            and cmp(order[j], order[i]) > 0, "PBT cmp"
                        n_pairs += 1
            if a == 0:
                assert canon_of_inc(inc) == canon_of_table(t), \
                    "incremental drifted from canonical"
            n_states += 1

        for _ in range(rng.randint(20, 45)):
            a = rng.randrange(NA)
            if rng.random() < 0.18:
                b = rng.choice([x for x in range(NA) if x != a])
                new_ins = sorted(inss[b] - inss[a],
                                 key=lambda x: (r.ts[x], r.agent[x], x))
                new_dels = delss[b] - delss[a]
                if a == 0:
                    for x in new_ins:
                        inc.insert(x, r.anchor[x])
                    for x in new_dels:
                        inc.delete(x)
                stats['merges'] += 1
                inss[a] |= inss[b]
                delss[a] |= delss[b]
                clock[a] = max(clock[a], clock[b])
                views[a] = r.dfs_view(inss[a], delss[a])
            else:
                for _ in range(rng.randint(1, 3)):
                    clock[a] += 1
                    if views[a] and rng.random() < 0.3:
                        victim = views[a].pop(rng.randrange(len(views[a])))
                        delss[a].add(victim)
                        if a == 0:
                            inc.delete(victim)
                    else:
                        pos = rng.randint(0, len(views[a]))
                        anch = views[a][pos - 1] if pos > 0 else ROOT
                        x = r.mint(clock[a], a, anch,
                                   chr(97 + rng.randrange(26)))
                        inss[a].add(x)
                        views[a].insert(pos, x)
                        if a == 0:
                            inc.insert(x, anch)
                    n_events += 1
            check(a)
        for k, v in inc.stats.items():
            stats[k] += v
    print(f"\n== PBT: {trials} trials, {fmt(n_events)} events,"
          f" {fmt(n_states)} states gated (walk identity + incremental =="
          f" canonical), {fmt(n_pairs)} comparator pairs -- ALL PASS")
    print(f"   exercised: merges {stats['merges']},"
          f" mid-run splits {stats['splits']},"
          f" liveness splits {stats['liveness_splits']},"
          f" coalesces {stats['coalesces']},"
          f" materializations {stats['materialized']},"
          f" unkept vanishings {stats['unkept']}")
    return True


if __name__ == "__main__":
    ok = directed()
    pbt()
    args = sys.argv[1:] or [
        os.path.join(HERE, "traces", t) for t in (
            "friendsforever_flat.json.gz", "clownschool_flat.json.gz",
            "seph-blog1.json.gz", "automerge-paper.json.gz",
            "friendsforever.json.gz", "clownschool.json.gz")
    ]
    rng = random.Random(2026)
    results = []
    for p in args:
        if not os.path.exists(p):
            print("MISSING TRACE:", p)
            continue
        results.append(measure(p, rng))
    if results:
        summarize(results)
