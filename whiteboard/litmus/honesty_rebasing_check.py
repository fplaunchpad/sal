#!/usr/bin/env python3
"""
honesty_rebasing_check.py -- VALIDATION of the (*) honesty-rebasing lemma
(whiteboard/honesty-rebasing-note.md, section 5 risks R1/R2/R3) BEFORE any
Lean.  Pen-and-paper + Python only.  Imports the validated embed compaction
models; modifies nothing existing.

The claim under test (note S2, load-bearing): the coded anchored forest
invariant I(C) over a config's LIVE embed-RGA coordinates is PRESERVED by a
StablePrefixMap F (rank-renumber, spine fusion, or their composition):
I(C) implies I(F.C), with anc' the image of anc.

I(C): there is a nearest-live-ancestor function anc such that
  (1) every live coord c = anc(c) ++ w, w a nonempty DECODABLE code-word
      tail (a sequence of >=1 whole code words under the datatype's
      OrderedPrefixCode);
  (2) anc is well founded (iterating reaches the sentinel "");
  (3) distinct live coords are distinct AND the forest is a tree (each node
      has a unique nearest-live-ancestor; no two live nodes collide).

We reconstruct anc PURELY from the live coordinate SET (longest proper
live-coord prefix) -- the executable form of eAnchored_exists -- and
cross-check it against the ground-truth birth tree (r.anchor).

F = embed_compact_measure.compact_cut: fuse=False is rank-renumber, fuse=True
is renumber+spine-fusion (runtime/compact.js step 2 + 2b).  compact_cut is
history-independent (it recomputes ordinals from the tree + original ts each
call), so a second call over an evolved live set IS the multi-epoch F2.

Usage: python3 honesty_rebasing_check.py [trace.json.gz ...]
"""
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from embed_compact_measure import (  # noqa: E402  (validated model, read-only)
    AccountingReplay, compact_cut, live_tree, live_bits, d_enc, bits_D,
)
from entropy_measure import ROOT  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))


# ------------------------------------------------ decoders (the "re-split")
def decode_delta_seq(bits):
    """Decode a bit string as a SEQUENCE of flipped-Elias-delta code words
    (the inverse of embed_compact_measure.d_enc).  Returns the list of
    decoded positive integers, or None if the string is not a clean
    concatenation of whole code words (leftover / truncated).  This is the
    R1 'anchor walk can re-split the concatenation' test."""
    out, i, n = [], 0, len(bits)
    while i < n:
        # gamma-decode the length field L
        k = 0
        while i < n and bits[i] == '1':
            k += 1
            i += 1
        if i >= n or bits[i] != '0':
            return None
        i += 1
        if i + k > n:
            return None
        L = int('1' + bits[i:i + k], 2)
        i += k
        # read L-1 payload bits, value = '1' ++ payload
        if i + (L - 1) > n:
            return None
        val = int('1' + bits[i:i + L - 1], 2) if L > 1 else 1
        i += (L - 1)
        out.append(val)
    return out if out else None


def decode_unary_seq(bits):
    """Sequence of unary code words '1'*d ++ '0' (d >= 1); value = run len."""
    out, run = [], 0
    for ch in bits:
        if ch == '1':
            run += 1
        elif ch == '0':
            if run < 1:
                return None  # d >= 1: a bare '0' is not a code word
            out.append(run)
            run = 0
        else:
            return None
    if run != 0:
        return None
    return out if out else None


# ------------------------------------------------ coordinate reconstruction
def build_coords(r, live):
    """Coordinate bit-string of every KEPT node from the current
    r.ordinal / r.fused (identical logic to display_after_cut, but returns
    the dict).  Native config (no cut): r.ordinal = birth deltas, r.fused
    empty, so coords are the birth-chain telescopes."""
    kept, children, _ = live_tree(r, live)
    fused = getattr(r, "fused", set())
    coord = {ROOT: ""}
    stack = [ROOT]
    while stack:
        n = stack.pop()
        for c in children.get(n, ()):
            coord[c] = coord[n] if c in fused else coord[n] + d_enc(r.ordinal[c])
            stack.append(c)
    return coord


def nla_tree(r, live, x):
    """Ground-truth nearest-LIVE-ancestor NODE via the birth tree."""
    p = r.anchor[x]
    while p != ROOT and p not in live:
        p = r.anchor[p]
    return p


def nla_all(clive):
    """Nearest-live-ancestor for EVERY node, from the live coord SET alone:
    the live node whose coord is the LONGEST PROPER prefix (ROOT/sentinel if
    none).  Sorted-order stack walk: O(N log N), O(N) memory (a bit-trie
    would blow memory on the O(N^2)-total-bits paste traces).  Same
    semantics as the naive longest-proper-live-prefix search."""
    items = sorted(clive.items(), key=lambda kv: kv[1])
    res, stack = {}, []  # stack = the current ancestor chain (coord, node)
    for x, c in items:
        while stack and not (len(stack[-1][0]) < len(c) and c.startswith(stack[-1][0])):
            stack.pop()
        res[x] = stack[-1][1] if stack else ROOT
        stack.append((c, x))
    return res


def nla_coords(clive, x):
    """Single-node nla (small incidental callers); naive longest proper
    live-coord prefix.  Same semantics as nla_all (asserted equal on the
    randomized suite)."""
    cx = clive[x]
    best_node, best_len = ROOT, -1
    for u, cu in clive.items():
        if u != x and len(cu) < len(cx) and cx.startswith(cu) and len(cu) > best_len:
            best_node, best_len = u, len(cu)
    return best_node


# ------------------------------------------------------- the I(C) predicate
def check_I(clive, decode=decode_delta_seq):
    """Check I(C) on a live coord dict {node: coordstring}.  Returns a list
    of problems (empty = holds).  Reconstructs anc purely from the set."""
    problems = []
    anc = nla_all(clive)
    # (3) collision / injectivity of live coordinates
    if len(set(clive.values())) != len(clive):
        problems.append("R2 COLLISION: two live coords are equal")
    for x, cx in clive.items():
        p = anc[x]
        pc = "" if p == ROOT else clive[p]
        # (1) factorization c = anc(c) ++ w, w nonempty decodable seq
        if not (cx.startswith(pc) and len(pc) < len(cx)):
            problems.append(f"cond1 anc-not-proper-prefix node={x}")
            continue
        tail = cx[len(pc):]
        vals = decode(tail)
        if not vals:
            problems.append(f"R1 tail-not-codeword-seq node={x} tail={tail!r}")
    # (2) well-foundedness of anc (strictly shorter prefixes => terminates)
    for x in clive:
        seen, cur, steps = set(), x, 0
        while cur != ROOT:
            if cur in seen or steps > len(clive) + 1:
                problems.append(f"cond2 anc-not-wellfounded node={x}")
                break
            seen.add(cur)
            cur = anc[cur]
            steps += 1
    return problems


def forest_matches_tree(r, live, clive):
    """S1 / R2 structural: the coord-reconstructed forest equals the true
    birth forest (reconstructed nla == nla_tree for every live node)."""
    anc = nla_all(clive)
    return [x for x in live if anc[x] != nla_tree(r, live, x)]


def live_coords(r, live):
    coord = build_coords(r, live)
    return {x: coord[x] for x in live}


# ---------------------------------------------------------------- directed
def directed():
    """Small hand-built configs with hand-derived expectations."""
    results = []

    def rec(name, ok, detail=""):
        results.append((name, ok, detail))

    # D1: dead-spine fusion.  L(live) -> h(dead) -> m(dead) -> x(live).
    # After renumber+fusion the tail of x must be TWO code words (cw(h)++cw(x)),
    # decodable, and nla(x)=L preserved.
    r = AccountingReplay()
    L = r.mint(1, 0, ROOT, 'L')
    h = r.mint(2, 0, L, 'h')
    m = r.mint(3, 0, h, 'm')
    x = r.mint(4, 0, m, 'x')
    live = {L, x}
    cl0 = live_coords(r, live)
    p0 = check_I(cl0)
    f0 = forest_matches_tree(r, live, cl0)
    nla_before = nla_coords(cl0, x)
    compact_cut(r, live, fuse=True)          # F = renumber + fusion
    cl1 = live_coords(r, live)
    p1 = check_I(cl1)
    f1 = forest_matches_tree(r, live, cl1)
    tail = cl1[x][len(cl1[L]):]
    ncw = len(decode_delta_seq(tail) or [])
    nla_after = nla_coords(cl1, x)
    rec("D1 native honest satisfies I", not p0 and not f0, str(p0 + f0))
    rec("D1 fusion preserves I", not p1 and not f1, str(p1 + f1))
    rec("D1 R1 fused tail is multi-codeword & decodes", ncw >= 2,
        f"tail={tail!r} -> {ncw} code words")
    rec("D1 R2 anc'(x)=anc(x) forest preserved (both L)",
        nla_before == L and nla_after == L, f"{nla_before}->{nla_after}")

    # D2: injectivity with >=3 live siblings under root; renumber must not
    # collide (R2) and must keep the descending-key display order.
    r = AccountingReplay()
    a = r.mint(1, 0, ROOT, 'a')
    b = r.mint(2, 0, ROOT, 'b')
    c = r.mint(3, 0, ROOT, 'c')
    live = {a, b, c}
    compact_cut(r, live, fuse=True)
    cl = live_coords(r, live)
    rec("D2 R2 siblings injective after renumber",
        len(set(cl.values())) == 3, str(cl))
    rec("D2 I holds for sibling group", not check_I(cl), "")

    # D3: unary-code parametricity, dead-spine fusion (note: parametric code).
    # Build native unary coords by hand, fuse, check I under unary decoder.
    # Native: L=1 -> h=2 -> x=3 (h dead).  We drive the SAME tree but decode
    # with unary by re-encoding ordinals in unary via a shadow coord map.
    def unary_coord(r, live):
        kept, children, _ = live_tree(r, live)
        fused = getattr(r, "fused", set())
        coord = {ROOT: ""}
        st = [ROOT]
        while st:
            n = st.pop()
            for cc in children.get(n, ()):
                coord[cc] = coord[n] if cc in fused else \
                    coord[n] + ('1' * r.ordinal[cc] + '0')
                st.append(cc)
        return {q: coord[q] for q in live}
    r = AccountingReplay()
    L = r.mint(1, 0, ROOT, 'L')
    h = r.mint(2, 0, L, 'h')
    x = r.mint(3, 0, h, 'x')
    live = {L, x}
    compact_cut(r, live, fuse=True)
    clu = unary_coord(r, live)
    pu = check_I(clu, decode=decode_unary_seq)
    fu = forest_matches_tree(r, live, clu)
    rec("D3 unary-code parametric: fusion preserves I", not pu and not fu,
        str(pu + fu))
    return results


# --------------------------------------------- random honest op replay
def random_honest(rng, n_ops):
    """Real op replay: single-author (agent 0, no ts ties) random inserts /
    deletes via the validated apply_patches.  Returns (r, state, live)."""
    r = AccountingReplay()
    state = (0, [], set(), set())
    for _ in range(n_ops):
        view = state[1]
        if view and rng.random() < 0.30:
            patch = [rng.randrange(len(view)), 1, ""]
        else:
            pos = rng.randrange(len(view) + 1)
            content = "".join(rng.choice("abcde") for _ in range(rng.randint(1, 3)))
            patch = [pos, 0, content]
        state = r.apply_patches(state, 0, [patch])
    return r, state, state[2] - state[3]


def _snap(r):
    return (dict(r.ordinal), dict(r.code_bits), dict(r.prefix_bits),
            getattr(r, "fused", set()).copy())


def _restore(r, s):
    r.ordinal, r.code_bits, r.prefix_bits, r.fused = s


def apply_F(r, live, cl0, fuse):
    """Apply F (compact_cut) on a snapshot, return the I / forest / R2 /
    forest-preservation verdicts, then restore r."""
    snap = _snap(r)
    ties, spines, levels = compact_cut(r, live, fuse=fuse)
    cl1 = live_coords(r, live)
    anc0, anc1 = nla_all(cl0), nla_all(cl1)      # forest before / after F
    out = dict(
        probs=check_I(cl1),
        forest=forest_matches_tree(r, live, cl1),          # reconstructed==tree
        inj=(len(set(cl1.values())) == len(cl1)),          # R2 no collision
        pres=[x for x in live if anc0[x] != anc1[x]],      # anc' = image of anc
        spines=spines, ties=ties,
    )
    _restore(r, snap)
    return out


def compact_cut_by_ordinal(r, live):
    """R3 STRESS: a renumber+fusion cut that sorts each sibling group by its
    STORED LABEL (r.ordinal: rank for pre-cut nodes, birth-delta for
    post-cut nodes) rather than by original ts.  This is the 'deltas are
    ordinals not original stamps' epoch-2 concern made concrete.  Returns
    the resulting live coord dict; compared against the ts-based coords."""
    kept, children, _ = live_tree(r, live)
    r.fused = set()
    stack = [ROOT]
    while stack:
        n = stack.pop()
        kids = sorted(children.get(n, ()), key=lambda c: (r.ordinal[c], r.ts[c], r.agent[c]))
        for i, c in enumerate(kids):
            r.ordinal[c] = i + 1
            r.code_bits[c] = bits_D(i + 1)
            r.prefix_bits[c] = r.prefix_bits[n] + r.code_bits[c]
            node = c
            if c not in live and len(children.get(c, ())) == 1:
                members = [c]
                while True:
                    nxt = children[members[-1]][0]
                    if nxt in live or len(children.get(nxt, ())) != 1:
                        break
                    members.append(nxt)
                if len(members) > 1:
                    for m in members[1:]:
                        r.fused.add(m)
                        r.ordinal[m] = r.ordinal[c]
                        r.code_bits[m] = 0
                        r.prefix_bits[m] = r.prefix_bits[c]
                    node = members[-1]
            stack.append(node)
    return {x: build_coords(r, live)[x] for x in live}


def randomized(n=600):
    """S1 (native honest satisfies I) + S2 (renumber / fusion preserve I,
    with R2 injectivity and forest-preservation) over random honest states."""
    rng = random.Random(20260720)
    cnt = dict(trials=0, s1=0, renum=0, fuse=0, fused_fired=0)
    fails = []
    for s in range(n):
        r, state, live = random_honest(rng, rng.randint(30, 90))
        if len(live) < 2:
            continue
        cnt["trials"] += 1
        cl0 = live_coords(r, live)
        if not check_I(cl0) and not forest_matches_tree(r, live, cl0):
            cnt["s1"] += 1
        else:
            fails.append(f"S1 native fails seed-order {s}")
            continue
        for fuse, key in ((False, "renum"), (True, "fuse")):
            v = apply_F(r, live, cl0, fuse)
            good = not v["probs"] and not v["forest"] and v["inj"] and not v["pres"]
            if good:
                cnt[key] += 1
            else:
                fails.append(f"S2 {key} fails {s}: I={v['probs']} "
                             f"forest={v['forest']} inj={v['inj']} pres={v['pres']}")
            if fuse and v["spines"] > 0:
                cnt["fused_fired"] += 1
    return cnt, fails


def two_epoch(n=500):
    """R3 heart: honest ops -> cut1 (renumber+fuse) -> MORE honest ops beyond
    the cut -> cut2 (renumber+fuse) over already-renumbered-and-fused coords.
    Checks I survives each epoch, the tree/forest is recovered, fusion fires,
    and the by-stored-ordinal cut agrees with the by-ts cut (the 'ordinals
    not stamps' equivalence)."""
    rng = random.Random(770077)
    cnt = dict(trials=0, e1=0, e2=0, fired1=0, fired2=0, ord_eq=0, multi=0)
    fails = []
    for s in range(n):
        r, state, live = random_honest(rng, rng.randint(25, 60))
        if len(live) < 2:
            continue
        _, sp1, _ = compact_cut(r, live, fuse=True)
        cl1 = live_coords(r, live)
        ok1 = not check_I(cl1) and not forest_matches_tree(r, live, cl1)
        # continue honest ops BEYOND the cut (new mints anchor on live nodes)
        for _ in range(rng.randint(15, 40)):
            view = state[1]
            if view and rng.random() < 0.30:
                patch = [rng.randrange(len(view)), 1, ""]
            else:
                pos = rng.randrange(len(view) + 1)
                patch = [pos, 0, "".join(rng.choice("xyz") for _ in range(rng.randint(1, 2)))]
            state = r.apply_patches(state, 0, [patch])
        live2 = state[2] - state[3]
        if len(live2) < 2:
            continue
        cnt["trials"] += 1
        cnt["e1"] += ok1
        if not ok1:
            fails.append(f"epoch1 I fails {s}")
        # by-stored-ordinal cut vs by-ts cut (the R3 representation concern)
        snap = _snap(r)
        cl_ord = compact_cut_by_ordinal(r, live2)
        _restore(r, snap)
        _, sp2, _ = compact_cut(r, live2, fuse=True)
        cl2 = live_coords(r, live2)
        ok2 = not check_I(cl2) and not forest_matches_tree(r, live2, cl2)
        cnt["e2"] += ok2
        if not ok2:
            fails.append(f"epoch2 I fails {s}: {check_I(cl2)} {forest_matches_tree(r, live2, cl2)}")
        cnt["fired1"] += (sp1 > 0)
        cnt["fired2"] += (sp2 > 0)
        cnt["ord_eq"] += (cl_ord == cl2)
        if cl_ord != cl2:
            fails.append(f"by-ordinal != by-ts at epoch2 {s}")
        # did any epoch-2 live coord get a genuinely multi-code-word tail?
        for x in live2:
            p = nla_coords(cl2, x)
            pc = "" if p == ROOT else cl2[p]
            if len(decode_delta_seq(cl2[x][len(pc):]) or []) >= 2:
                cnt["multi"] += 1
                break
    return cnt, fails


def negative_controls():
    """The checker must have TEETH: known-bad configs MUST fail I / forest /
    injectivity (else the passes above are a self-fulfilling oracle)."""
    res = []

    def rec(n, ok, d=""):
        res.append((n, ok, d))

    # NC1: two distinct live nodes forced to the SAME coord -> R2 collision.
    probs = check_I({1: "0", 2: "1000", 3: "1000"})
    rec("NC1 collision is detected", any("COLLISION" in p for p in probs), str(probs))
    # NC2: a tail that is NOT a whole code-word sequence ('1' is a truncated
    # Elias-delta word) -> R1 must flag it.
    probs = check_I({1: "0", 2: "01"})
    rec("NC2 non-codeword tail is detected", any("R1" in p for p in probs), str(probs))
    # NC3: coord-longest-prefix disagrees with the true birth tree (a forged
    # spurious nesting) -> forest_matches_tree must flag it.
    r = AccountingReplay()
    a = r.mint(1, 0, ROOT, 'a')
    b = r.mint(2, 0, ROOT, 'b')          # a and b are both ROOT children
    forged = {a: "0", b: "0" + d_enc(1)}  # makes a a spurious ancestor of b
    rec("NC3 forest/anchor mismatch is detected",
        b in forest_matches_tree(r, {a, b}, forged), "")
    # NC4 foil: the CORRECT sibling coords for the same tree pass forest.
    good = {a: d_enc(2), b: d_enc(1)}
    rec("NC4 correct sibling coords pass (foil)",
        not forest_matches_tree(r, {a, b}, good), "")
    return res


def traces(paths):
    """S1 + S2 on REAL editing traces at the final settled cut."""
    import gzip
    import json
    from embed_compact_measure import run_sequential, run_concurrent
    rows = []
    for path in paths:
        if not os.path.exists(path):
            continue
        with gzip.open(path, "rt", encoding="utf-8") as f:
            doc = json.load(f)
        name = os.path.basename(path).replace(".json.gz", "")
        conc = doc.get("kind") == "concurrent"
        if conc:
            r, state, end = run_concurrent(doc)
        else:
            r, state, _, end = run_sequential(doc, None)   # control: never compacted
        live = state[2] - state[3]
        cl0 = live_coords(r, live)
        s1 = not check_I(cl0) and not forest_matches_tree(r, live, cl0)
        vr = apply_F(r, live, cl0, False)
        vf = apply_F(r, live, cl0, True)
        renum = not vr["probs"] and not vr["forest"] and vr["inj"] and not vr["pres"]
        fuse = not vf["probs"] and not vf["forest"] and vf["inj"] and not vf["pres"]
        rows.append((name, len(live), s1, renum, fuse, vf["spines"], vf["ties"],
                     conc, vr["inj"] and vf["inj"]))
    return rows


if __name__ == "__main__":
    print("==== honesty-rebasing (*) validation: I(C) preservation ====\n")
    print("-- DIRECTED --")
    dfails = 0
    for name, ok, detail in directed():
        dfails += not ok
        print(f"  [{'PASS' if ok else 'FAIL'}] {name}"
              + (f"   ({detail})" if detail else ""))

    print("\n-- NEGATIVE CONTROLS (the checker must reject known-bad configs) --")
    ncfails = 0
    for name, ok, detail in negative_controls():
        ncfails += not ok
        print(f"  [{'PASS' if ok else 'FAIL'}] {name}"
              + (f"   ({detail})" if detail and not ok else ""))

    print("\n-- RANDOMIZED honest states (S1 + S2 renumber/fusion) --")
    rc, rf = randomized(600)
    print(f"  trials={rc['trials']}  S1 native satisfies I: {rc['s1']}/{rc['trials']}")
    print(f"  S2 rank-renumber preserves I (+R2 inj +forest): {rc['renum']}/{rc['trials']}")
    print(f"  S2 renumber+fusion preserves I (+R2 inj +forest): {rc['fuse']}/{rc['trials']}"
          f"   [fusion actually fired in {rc['fused_fired']} trials]")
    for f in rf[:6]:
        print("     FAIL:", f)

    print("\n-- TWO-EPOCH (R3: renumber+fuse over already renumbered+fused) --")
    tc, tf = two_epoch(500)
    print(f"  trials={tc['trials']}  epoch1 I holds: {tc['e1']}/{tc['trials']}"
          f"   epoch2 I holds: {tc['e2']}/{tc['trials']}")
    print(f"  fusion fired: epoch1 {tc['fired1']}, epoch2 {tc['fired2']};"
          f"  epoch2 multi-code-word tails present in {tc['multi']} trials")
    print(f"  by-stored-ordinal cut == by-ts cut (ordinals-not-stamps): "
          f"{tc['ord_eq']}/{tc['trials']}")
    for f in tf[:6]:
        print("     FAIL:", f)

    print("\n-- REAL TRACES (S1 + S2 at the final settled cut) --")
    args = sys.argv[1:] or [
        os.path.join(HERE, "traces", t) for t in (
            "automerge-paper.json.gz", "seph-blog1.json.gz",
            "friendsforever_flat.json.gz", "clownschool_flat.json.gz",
            "friendsforever.json.gz", "clownschool.json.gz",
        )
    ]
    trows = traces(args)
    if not trows:
        print("  (no traces present; fetch per entropy_measure.py curl lines)")
    for name, nl, s1, rn, fz, sp, ties, conc, inj in trows:
        tag = "concurrent" if conc else "sequential"
        print(f"  {name:<22} live={nl:>7}  [{tag}]  S1 {'OK' if s1 else 'FAIL'}"
              f"  renumber {'OK' if rn else 'FAIL'}  fusion {'OK' if fz else 'FAIL'}"
              f"  [spines={sp}, ts-ties={ties}]")

    print("\n==== VERDICT ====")
    s1_ok = rc['s1'] == rc['trials'] and all(x[2] for x in trows)
    renum_ok = rc['renum'] == rc['trials'] and all(x[3] for x in trows)
    fuse_ok = rc['fuse'] == rc['trials'] and all(x[4] for x in trows)
    r3_ok = (tc['e1'] == tc['trials'] and tc['e2'] == tc['trials']
             and tc['ord_eq'] == tc['trials'])
    allok = (not dfails and not ncfails and not rf and not tf
             and s1_ok and renum_ok and fuse_ok and r3_ok)
    print(f"  negative controls have teeth ....... {'PASS' if not ncfails else 'FAIL'}")
    print(f"  S1  EHonest => I ................... {'PASS' if s1_ok else 'FAIL'}")
    print(f"  S2  rank-renumber preserves I ...... {'PASS' if renum_ok else 'FAIL'}")
    print(f"  S2  fusion preserves I (R1+R2) ..... {'PASS' if fuse_ok else 'FAIL'}")
    print(f"  R3  two-epoch preserves I .......... {'PASS' if r3_ok else 'FAIL'}")
    print(f"  OVERALL: {'ALL PASS -- Lean-ready (see note sec 7)' if allok else 'SEE FAILURES ABOVE'}")
    sys.exit(0 if allok else 1)
