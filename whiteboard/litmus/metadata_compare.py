#!/usr/bin/env python3
"""
metadata_compare.py -- final-state metadata overhead on real editing traces:
tombstoned RGA vs the embedded-chain RGA (flat, Steiner-shared, and
run-coalesced forms), with an order-of-magnitude estimate for Eg-walker's
durable event graph.

Replay model is entropy_measure.py's (dense Lamport time, anchors from the
live view, RGA sibling order; endContent equality is the correctness gate).

What is counted, per design, as METADATA of the final state (live character
bytes excluded everywhere, since data costs are identical across designs):

  RGA (tombstoned)   one record per insert EVER: own id + anchor id + flag.
                     Widths: practical (2x32+1 bits) and tight (2 ceil(log2 T)
                     + 1 bits, T = final Lamport clock). Dead chars dropped.

  embed (flat)       one record per SURVIVOR: own id + par id (nearest live
                     ancestor) + stored string s = own block plus the blocks
                     of the dead birth ancestors up to the nearest live
                     ancestor. Block = |C(delta)| + 3 framing bits.

  embed (shared)     same, but each distinct dead node's block is stored once
                     (cord / Steiner sharing) rather than once per heir.

  embed (runs)       item-range coalescing (note I2): maximal chains of
                     survivors linked by (birth parent live, delta = 1)
                     become one record: head's ids + head's string + C(len).

  Eg-walker          durable state = the full event graph, RLE'd by runs;
                     estimated as bytes_per_patch * #patches + bytes_per_txn
                     * #txns (position varints, lengths, parent edges). The
                     DOCUMENT state is metadata-free; the graph is retained
                     while concurrent ops may arrive. Estimate, not their
                     file format.
"""

import sys
from collections import defaultdict

sys.path.insert(0, "/Users/kc/repos/sal/whiteboard/litmus")
import entropy_measure as em

KB = 8 * 1024.0


def block_bits(d):
    return em.bits_C(d) + 3


def analyze(path):
    import gzip
    import json
    with gzip.open(path, "rt", encoding="utf-8") as f:
        doc = json.load(f)
    replay = em.Replay()
    if doc.get("kind") == "concurrent":
        end = em.replay_concurrent(doc, replay)
    else:
        end = em.replay_sequential(doc, replay)
    assert end == doc["endContent"], f"replay invalid for {path}"

    # final branch state: reconstruct from the last computed view
    # (replay_* return only text; recompute live set from chars of view)
    # -- easiest: rerun to keep state. Patch: emulate by re-deriving from
    # replay structures: survivors are exactly the ids in the final view.
    # Re-run the replay to capture the final state directly.
    replay = em.Replay()
    if doc.get("kind") == "concurrent":
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
                view = replay.dfs_view(ins, dels)
                state = (clock, view, ins, dels)
            state = replay.apply_patches(state, txn.get("agent", 0),
                                         txn["patches"])
            states[idx] = state
            final = state
    else:
        final = (0, [], set(), set())
        for txn in doc["txns"]:
            final = replay.apply_patches(final, 0, txn["patches"])

    clock, view, ins, dels = final
    survivors = list(view)
    n_ins, n_del = len(ins), len(dels)
    n_live = len(survivors)
    T = clock
    id_tight = max(1, (T).bit_length())

    live = set(survivors)

    # nearest-live-ancestor walk with memoised dead-path (bits, node set)
    # memo[u] = (dead_bits_above_u, tuple unused); collect distinct dead nodes
    dead_bits_above = {}
    dead_nodes_on_paths = set()

    def dead_path_bits(u):
        # bits of dead-ancestor blocks strictly above u, up to nearest live
        chain = []
        v = replay.anchor[u]
        while v != em.ROOT and v not in live and v not in dead_bits_above:
            chain.append(v)
            v = replay.anchor[v]
        base = 0.0
        if v != em.ROOT and v not in live:
            base = dead_bits_above[v] + block_bits(replay.delta[v])
            dead_nodes_on_paths.add(v)
        for v2 in reversed(chain):
            dead_bits_above[v2] = base
            dead_nodes_on_paths.add(v2)
            base = base + block_bits(replay.delta[v2])
        return base

    embed_string_bits = 0.0
    for u in survivors:
        embed_string_bits += dead_path_bits(u) + block_bits(replay.delta[u])

    # shared (Steiner/cord) form: every distinct dead node's block once
    shared_dead_bits = sum(block_bits(replay.delta[v])
                           for v in dead_nodes_on_paths)
    own_blocks_bits = sum(block_bits(replay.delta[u]) for u in survivors)

    # run coalescing over the final live tree
    run_child = {}
    for u in survivors:
        p = replay.anchor[u]
        if replay.delta[u] == 1 and (p in live):
            run_child[u] = p
    heads = [u for u in survivors if u not in run_child
             or run_child[u] not in live]
    # chains: follow from each survivor up; count chains = survivors that are
    # not a delta=1 child of a live parent
    chain_of = {}
    n_chains = 0
    chain_len = defaultdict(int)
    for u in survivors:
        # find head by walking up delta=1 live links
        walk = []
        v = u
        while v in run_child and run_child[v] in live and v not in chain_of:
            walk.append(v)
            v = run_child[v]
        head = chain_of.get(v, v)
        for w in walk:
            chain_of[w] = head
        chain_of.setdefault(u, head)
    for u in survivors:
        chain_len[chain_of[u]] += 1
    n_chains = len(chain_len)
    runs_bits = 0.0
    for h, ln in chain_len.items():
        runs_bits += dead_path_bits(h) + block_bits(replay.delta[h]) \
            + em.bits_C(ln)

    # totals (metadata only; live char bytes excluded everywhere)
    rga_practical = n_ins * (2 * 32 + 1)
    rga_tight = n_ins * (2 * id_tight + 1)
    embed_flat = n_live * (2 * id_tight) + embed_string_bits
    embed_shared = n_live * (2 * id_tight) + own_blocks_bits \
        + shared_dead_bits
    embed_runs = n_chains * (2 * id_tight) + runs_bits

    # full-history insert runs (I2 runs over ALL inserts, live and dead):
    # per agent, maximal chains of delta=1 mints in mint order. Also the
    # Yjs-style ranged tombstoned RGA: those runs further fragmented where
    # final liveness flips inside a run (a range carries one deleted flag).
    all_ids = sorted(replay.delta.keys())
    last_of_agent = {}
    insert_runs = 0
    yjs_records = 0
    run_live = {}
    for x in all_ids:
        ag = replay.agent[x]
        isl = x in live
        if replay.delta[x] == 1 and ag in last_of_agent:
            if last_of_agent[ag] != isl:
                yjs_records += 1
                last_of_agent[ag] = isl
        else:
            insert_runs += 1
            yjs_records += 1
            last_of_agent[ag] = isl
    yjs_bits = yjs_records * (2 * id_tight + 1 + 8)  # ids+flag+len varint

    # Eg-walker estimate: durable graph = full history, RLE'd into runs
    # (insert runs as above; delete runs ~ patches with ndel>0; parent
    # edges only at branch/merge points). 8--16 B per run record.
    n_txns = len(doc["txns"])
    n_patches = sum(len(t["patches"]) for t in doc["txns"])
    # delete runs coalesced across patches: a run continues while the next
    # delete lands at the same or adjacent position (fwd-delete/backspace)
    del_runs = 0
    prev = None
    for t in doc["txns"]:
        ag = t.get("agent", 0)
        for p in t["patches"]:
            if p[1] > 0:
                if prev is None or prev[0] != ag \
                        or abs(prev[1] - p[0]) > 1:
                    del_runs += 1
                prev = (ag, p[0])
            if p[2]:
                prev = None
    branchy = sum(1 for t in doc["txns"]
                  if len(t.get("parents", [1])) != 1
                  or t.get("numChildren", 1) > 1)
    eg_records = insert_runs + del_runs + branchy
    eg_lo = eg_records * 8 * 8
    eg_hi = eg_records * 16 * 8

    name = path.split("/")[-1].replace(".json.gz", "")
    print(f"\n== {name}")
    print(f"   events: {n_ins} ins + {n_del} del = {n_ins+n_del}   "
          f"final chars: {n_live}   T={T} (id {id_tight} bits)")
    print(f"   dead nodes remembered by embed: {len(dead_nodes_on_paths)}"
          f" / {n_del} deleted "
          f"({100*len(dead_nodes_on_paths)/max(1,n_del):.1f}%)")
    print(f"   live text baseline:            {n_live/1024:10.1f} KB")
    print(f"   RGA tombstoned (2x32b ids):    {rga_practical/KB:10.1f} KB")
    print(f"   RGA tombstoned (tight ids):    {rga_tight/KB:10.1f} KB")
    print(f"   RGA ranged, Yjs-style:         {yjs_bits/KB:10.1f} KB"
          f"   ({yjs_records} range records)")
    print(f"   embed flat:                    {embed_flat/KB:10.1f} KB"
          f"   (strings {embed_string_bits/KB:.1f})")
    print(f"   embed shared dead prefixes:    {embed_shared/KB:10.1f} KB")
    print(f"   embed run-coalesced:           {embed_runs/KB:10.1f} KB"
          f"   ({n_chains} chains, mean len "
          f"{n_live/max(1,n_chains):.1f})")
    print(f"   Eg-walker event graph (est.):  {eg_lo/KB:10.1f}--"
          f"{eg_hi/KB:.1f} KB   ({eg_records} run records from"
          f" {insert_runs} ins-runs + {del_runs} del-runs + {branchy}"
          f" branch points; doc state itself metadata-free)")


if __name__ == "__main__":
    args = sys.argv[1:] or [
        "traces/automerge-paper.json.gz",
        "traces/seph-blog1.json.gz",
        "traces/friendsforever.json.gz",
        "traces/clownschool.json.gz",
    ]
    for p in args:
        analyze(p)
