#!/usr/bin/env python3
"""epoch_diamond_check -- the EPOCH PROTOCOL question, Python phase (#112).

Can replicas that compacted at INCOMPARABLE settled cuts merge without
coordination?  The cuts are CERTIFIED (AllHeardSince evidence): S1 and S2
are downward-closed event sets that every replica already possesses, so
there is no informational obstacle; the question is algebraic.

Hypotheses (falsifiable; this file's job is to try to kill each):

  H-D  (diamond/confluence). For incomparable settled cuts S1, S2 over one
       honest history: compact at S1 then relative-compact at the S1-union-S2
       remainder (composing the two StablePrefixMaps with the
       composite-surviving-domain fix) equals compacting once at S1 u S2,
       and equals the symmetric S2-first path.  Tested at three strengths,
       reported separately:
         s1  bit-identical states + identical composed translation maps on
             the surviving domain;
         s2  order-isomorphic: identical live-chain key order and identical
             reads, with a common refinement map between the results;
         s3  reads-identical only.
  H-M  (barrier-free merge). R1 compacts at S1, R2 at S2, both keep editing
       (declared stragglers included), then merge by translating BOTH into
       the join epoch (the S1 u S2 compaction): reads equal the
       never-compacted twin's merge, for all continuations, multi-epoch
       included (diamonds of diamonds).
  H-A3 (map drop). Once every replica has advanced past epoch e AND every
       op minted before its minter's advance has been heard everywhere, no
       old-space record can arrive, so dropping e's translation map changes
       nothing.  The harness models the certificate and asserts no
       straggler below a superseded epoch is ever generated; a directed
       case shows the ack-only certificate (everyone advanced, without the
       all-heard-of-pre-ack-mints half) is INSUFFICIENT.
  ContOK shape-check: every generated continuation satisfies the four
       ContOK clauses (fresh ids exceed all state ids; nodup insert ids;
       mint-key freshness vs state and pairwise).  Counted, not papered
       over.

PASS+FAIL convention: expected values in directed cases are hand-derived
in comments, never #eval'd from the code under test.  Directed FAIL
companions: naive full-domain composition must collide (c1, two-sided);
a cross-epoch merge WITHOUT translation must flip a read (c4).

Model (transliterated from marks_gc_check.py's compact_map interface and
embed_recode_check.py; stdlib only, nothing existing is modified):
coordinates are delta chains (tuples of positive ints), coord of insert i
after anchor a is coord(a) + (i - a,); key(c) = tuple(-d for d in c);
display = ascending key sort (ancestor before subtree, larger delta =
newer sibling first: recency order).  Delete is logical (deleted set);
physical drop happens at compaction.  Ops travel id-addressed and each
state re-derives the coordinate from its own anchor record, which is
exactly the stable-prefix map's extension law H3; the op-level
translated-wire form was validated in embed_recode_check.py (#97) and is
not re-modeled here.  Cuts are EVENT sets (inserts and deletes), so
drop-finality (the settled set lists deleted ids below the cut) is
by construction.  After epoch one the harness addresses cut members by id
into an id->coord table, which is the coordinate-addressed cut of
embed-recoding-note.md Addendum 4 (ids here are stable dictionary keys,
never decoded from coordinates, so id_addressing_breaks does not apply).
"""
import random
import sys

# ---------------------------------------------------------------- model

def key(c):
    return tuple(-d for d in c)


class Ev:
    __slots__ = ('id', 'kind', 'minter', 'anchor', 'target', 'elem', 'deps')

    def __init__(self, id, kind, minter, anchor=None, target=None, elem=None,
                 deps=frozenset()):
        self.id, self.kind, self.minter = id, kind, minter
        self.anchor, self.target, self.elem = anchor, target, elem
        self.deps = deps


class St:
    __slots__ = ('shadow', 'anchor', 'elem', 'deleted')

    def __init__(self):
        self.shadow = {}          # insert id -> coord tuple
        self.anchor = {}          # insert id -> anchor id (0 = root)
        self.elem = {}
        self.deleted = set()      # logical

    def copy(self):
        s = St()
        s.shadow = dict(self.shadow)
        s.anchor = dict(self.anchor)
        s.elem = dict(self.elem)
        s.deleted = set(self.deleted)
        return s

    def ins(self, i, elem, a):
        assert i > a, 'Lamport violation'
        base = () if a == 0 else self.shadow[a]
        self.shadow[i] = base + (i - a,)
        self.anchor[i] = a
        self.elem[i] = elem

    def dele(self, x):
        if x in self.shadow:
            self.deleted.add(x)

    def live_ids(self):
        return sorted((i for i in self.shadow if i not in self.deleted),
                      key=lambda i: key(self.shadow[i]))

    def read(self):
        return [(i, self.elem[i]) for i in self.live_ids()]


def fold(events, ids):
    """Fold the events with the given ids, in id (Lamport) order: the
    canonical epoch-0 state of that event set (the never-compacted twin)."""
    st = St()
    for i in sorted(ids):
        e = events[i]
        if e.kind == 'ins':
            st.ins(e.id, e.elem, e.anchor)
        else:
            st.dele(e.target)
    return st


def down_close(S, events):
    S = set(S)
    frontier = list(S)
    while frontier:
        i = frontier.pop()
        for d in events[i].deps:
            if d not in S:
                S.add(d)
                frontier.append(d)
    return S


def up_close(S, events, universe):
    """All events in universe depending (transitively) on something in S."""
    out = set(S)
    changed = True
    while changed:
        changed = False
        for i in universe:
            if i not in out and any(d in out for d in events[i].deps):
                out.add(i)
                changed = True
    return out

# ------------------------------------------------------------- compactor
#
# make_spm builds the certificate-determined StablePrefixMap for one cut:
#   rank pass  = marks_gc_check.compact_map (dense renumber per sibling
#                group, frozen groups keep deltas verbatim: the in-flight
#                guard);
#   fusion pass= embed-recoding-note Addendum 2 + errata: a maximal chain
#                of phantom-unary nodes (no kept or declared record at the
#                node, exactly one child branch counting every known
#                coordinate INCLUDING declared in-flight ones) of length
#                k >= 2 keeps the head's (already ranked) codeword and
#                drops the interior levels.  The anchored-at-a-spine-node
#                guard is subsumed by branch counting: a declared coord
#                through or at a node contributes a child branch.
# The map is a function of the CERTIFICATE data only (settled coords, the
# settled-dead subset, the declared in-flight set), never of a replica's
# private unsettled records: that is what makes two replicas compute the
# SAME join map without coordination.
#
# Inline machine checks (H2/H1 on the coordinates at hand) raise
# AssertionError with details; randomized drivers catch and count them as
# verdict failures, not harness noise.

def _factor(c, table):
    for j in range(len(c), -1, -1):
        p = c[:j]
        if p in table:
            return table[p] + c[j:]
    raise AssertionError('unfactorable coordinate %r' % (c,))


class SPM:
    __slots__ = ('pfx', 'dom', 'dropped', 'kept_ids')

    def __init__(self, pfx, dom, dropped, kept_ids):
        self.pfx = pfx            # old prefix -> new prefix (stable part)
        self.dom = dom            # frozenset of old full coords kept
        self.dropped = dropped    # ids physically dropped
        self.kept_ids = kept_ids

    def rho(self, c):
        return _factor(c, self.pfx)


def make_spm(settled, dead, declared, freeze=True, fuse=True, check=True):
    """settled: {insert id: coord} (current-epoch coords of settled
    records, dead included).  dead: ids in settled whose delete is also
    settled.  declared: {op id: (anchor id, coord)} for known in-flight
    inserts (minted before the declaration, not settled)."""
    retained = {a for (a, _c) in declared.values() if a in settled and a in dead}
    kept_ids = {i for i in settled if i not in dead} | retained
    kept = {i: settled[i] for i in kept_ids}
    frozen = set()
    if freeze:
        for (a, _c) in declared.values():
            if a == 0:
                frozen.add(())
            elif a in settled:
                frozen.add(settled[a])
    # rank pass (dense renumber, frozen groups verbatim)
    children = {}
    for c in kept.values():
        for k in range(len(c)):
            children.setdefault(c[:k], set()).add(c[k])
    newpfx = {(): ()}
    for p in sorted(children, key=lambda q: (len(q), q)):
        ds = sorted(children[p])
        renumber = p not in frozen
        for idx, d in enumerate(ds):
            nd = (idx + 1) if renumber else d
            newpfx[p + (d,)] = newpfx[p] + (nd,)
    # fusion pass on the RANKED tree (erratum 1: fusion runs after ranking)
    fpfx = {(): ()}
    if fuse:
        ranked_full = {newpfx[c] for c in kept.values()}
        ranked_full |= {_factor(c, newpfx) for (_a, c) in declared.values()}
        kids2 = {}
        for c in ranked_full:
            for k in range(len(c)):
                kids2.setdefault(c[:k], set()).add(c[k])
        def unary_phantom(p):
            return (p != () and p not in ranked_full
                    and len(kids2.get(p, ())) == 1)
        skip = set()
        for p in kids2:
            for d in kids2[p]:
                q = p + (d,)
                if unary_phantom(q) and unary_phantom(p):
                    skip.add(q)               # interior spine node: k>=2 met
        for q in sorted(set().union(*[{c[:k + 1] for k in range(len(c))}
                                      for c in ranked_full] or [set()]),
                        key=len):
            fpfx[q] = fpfx[q[:-1]] if q in skip else fpfx[q[:-1]] + (q[-1],)
    else:
        for q in sorted(newpfx.values(), key=len):
            fpfx[q] = q
    pfx = {p: _factor(newpfx[p], fpfx) for p in newpfx}
    spm = SPM(pfx, frozenset(kept.values()), dead - kept_ids,
              frozenset(kept_ids))
    if check:
        at_hand = list(kept.values()) + [c for (_a, c) in declared.values()]
        imgs = [spm.rho(c) for c in at_hand]
        assert len(set(imgs)) == len(set(at_hand)), \
            'H1 violation: rho not injective on the coordinates at hand'
        pairs = [(a, b) for x, a in enumerate(at_hand) for b in at_hand[x + 1:]]
        if len(pairs) > 1500:
            rng = random.Random(0xD1A)
            pairs = [tuple(rng.sample(at_hand, 2)) for _ in range(1500)]
        for a, b in pairs:
            assert (key(a) < key(b)) == (key(spm.rho(a)) < key(spm.rho(b))), \
                'H2 violation: order of %r,%r not preserved' % (a, b)
    return spm


def apply_spm(st, spm):
    out = St()
    for i, c in st.shadow.items():
        if i in spm.dropped:
            continue
        out.shadow[i] = spm.rho(c)
        out.anchor[i] = st.anchor[i]
        out.elem[i] = st.elem[i]
    out.deleted = st.deleted - spm.dropped
    return out


def compose(F, G, universe=None, naive=False):
    """Composite of F (epoch a->b) then G (b->c).  naive=True composes on
    F's FULL first-epoch domain (the Addendum-4 landmine, expected to
    collide under rank reclaim).  A caller-supplied universe is the
    CARRIED surviving domain (id-derived: the epoch-0 coords of the final
    cut's kept ids) and is taken as-is: it cannot be recomputed here,
    because (a) membership pullback through F is unsound (a coord dropped
    by F falls through verbatim and can alias a kept epoch-b coordinate)
    and (b) intersecting with G.dom wrongly evicts records settled only
    at a LATER constituent cut (their intermediate image is unsettled,
    yet still correctly translated by prefix factoring).  Without a
    universe, dom is the nested-cut default: F.dom filtered by survival
    into G.dom."""
    if naive:
        dom = frozenset(F.dom if universe is None else universe)
    elif universe is not None:
        dom = frozenset(universe)
    else:
        dom = frozenset(c for c in F.dom if F.rho(c) in G.dom)
    keys = {()}
    for c in dom:
        for k in range(len(c)):
            keys.add(c[:k + 1])
    pfx = {p: G.rho(F.rho(p)) for p in keys}
    return SPM(pfx, dom, F.dropped | G.dropped,
               frozenset(F.kept_ids & G.kept_ids))


def injective_on(spm, coords):
    imgs = [spm.rho(c) for c in coords]
    return len(set(imgs)) == len(set(coords))

# ------------------------------------------- history + certificate layer
#
# Replicated history generator: n replicas mint (Lamport-fresh global ids,
# anchors chosen among LOCALLY LIVE records only: a minter that has heard
# a delete never anchors under it, which is why no future op can anchor at
# a settled-dead node) and deliver causally.  A cut is any downward-closed
# subset of the all-heard intersection: that intersection IS the
# AllHeardSince certificate (every replica possesses every member).
# declared(S) = inserts existing at declaration time and not in S (the
# all-heads-visibility half of the certificate makes them all known).

def gen_history(rng, n_rep, n_ev, chainy=False):
    """chainy=True biases toward typing runs (insert anchored at the
    minter's previous insert) and deep-node deletes: this is what
    manufactures dead unary spines, so the fusion pass actually fires in
    the randomized diamonds (the plain generator rarely builds one)."""
    events = {}
    heard = [set() for _ in range(n_rep)]
    prev = [None] * n_rep
    last_ins = [0] * n_rep
    clock = 0
    while len(events) < n_ev:
        r = rng.randrange(n_rep)
        act = rng.random()
        undeliv = [i for i in events if i not in heard[r]]
        if act < 0.45 and undeliv:                       # causal delivery
            ready = [i for i in undeliv
                     if events[i].deps <= heard[r]]
            if ready:
                heard[r].add(rng.choice(ready))
                continue
        clock += 1
        st_r = fold(events, heard[r])
        live = st_r.live_ids()
        deps = {prev[r]} - {None}
        p_del = 0.35 if chainy else 0.3
        if live and rng.random() < p_del:
            if chainy:
                deep = sorted(live, key=lambda i: -len(st_r.shadow[i]))
                tgt = rng.choice(deep[:3])
            else:
                tgt = rng.choice(live)
            events[clock] = Ev(clock, 'del', r, target=tgt,
                               deps=frozenset(deps | {tgt}))
        else:
            if chainy and last_ins[r] in st_r.shadow and rng.random() < 0.7:
                a = last_ins[r]                          # typing run
            else:
                a = rng.choice([0] + live)
            if a:
                deps.add(a)
            events[clock] = Ev(clock, 'ins', r, anchor=a, elem=clock,
                               deps=frozenset(deps))
            last_ins[r] = clock
        heard[r].add(clock)
        prev[r] = clock
    return events, heard


def sample_cut(rng, settled, events):
    """A random downward-closed nonempty proper-ish subset of settled."""
    S = set(settled)
    for _ in range(rng.randrange(1, 4)):
        if not S:
            break
        e = rng.choice(sorted(S))
        S -= up_close({e}, events, S)
    return frozenset(S)


def incomparable_pair(rng, settled, events, tries=60):
    for _ in range(tries):
        S1 = sample_cut(rng, settled, events)
        S2 = sample_cut(rng, settled, events)
        if S1 and S2 and not (S1 <= S2) and not (S2 <= S1):
            return S1, S2
    return None


def cut_data(state, events, S, declared_ids, delof):
    """Certificate-shaped inputs for make_spm, addressed in state's epoch:
    settled record coords, settled-dead subset, declared coords."""
    ins_ids = {i for i in S if events[i].kind == 'ins' and i in state.shadow}
    settled = {i: state.shadow[i] for i in ins_ids}
    dead = {i for i in ins_ids if delof.get(i, frozenset()) & S}
    decl = {}
    for d in declared_ids:
        if events[d].kind == 'ins' and d in state.shadow:
            decl[d] = (events[d].anchor, state.shadow[d])
    return settled, dead, decl


def delof_index(events):
    delof = {}
    for e in events.values():
        if e.kind == 'del':
            delof.setdefault(e.target, set()).add(e.id)
    return {t: frozenset(v) for t, v in delof.items()}

# ----------------------------------------------------- ContOK shape-check

CONTOK = {'checked': 0, 'violations': []}

def contok_check(cont_ops, base_states):
    """The four ContOK clauses against every base state the continuation
    is applied to: (1) fresh ids exceed all state ids; (2) nodup insert
    ids; (3) mint keys fresh vs state; (4) mint keys pairwise distinct."""
    ins_ids = [o[0] for o in cont_ops if o[1] == 'ins']
    ok = len(ins_ids) == len(set(ins_ids))                          # (2)
    for st0 in base_states:
        st = st0.copy()
        seen_keys = set()
        for o in cont_ops:
            if o[1] == 'ins':
                i, _k, a, el = o
                ok &= all(i > j for j in st.shadow)                 # (1)
                st.ins(i, el, a)
                k = key(st.shadow[i])
                ok &= all(k != key(c) for j, c in st.shadow.items()
                          if j != i)                                # (3)
                ok &= k not in seen_keys                            # (4)
                seen_keys.add(k)
            else:
                st.dele(o[2])
        CONTOK['checked'] += 1
        if not ok:
            CONTOK['violations'].append(cont_ops)
            break
    return ok

# --------------------------------------------------------- diamond runner

def compact_step(state, events, S, declared_ids, delof, **kw):
    settled, dead, decl = cut_data(state, events, S, declared_ids, delof)
    spm = make_spm(settled, dead, decl, **kw)
    return apply_spm(state, spm), spm


def run_diamond(events, cuts, declared, cont_ops, delof):
    """cuts: list of >= 2 incomparable settled cuts.  Returns dict with
    per-strength booleans and a detail string on failure.  Paths compared:
      A: cuts[0], then union            (relative)
      B: cuts[-1], then union           (relative, symmetric)
      C: union in one shot.
    For triples, A becomes cuts[0]; cuts[0] u cuts[1]; union (a diamond of
    diamonds)."""
    W = frozenset().union(*cuts)
    declW = frozenset().union(*[declared[S] for S in cuts]) - W
    st = fold(events, events.keys())
    twin = st.copy()

    def path2(seq):
        cur = st
        spms = []
        for S, dec in seq:
            cur, spm = compact_step(cur, events, S, dec, delof)
            spms.append(spm)
        # The composite's surviving domain is CARRIED, id-addressed: the
        # epoch-0 coords of the records kept at the final cut.  It cannot
        # be computed by coordinate-membership pullback: a coord dropped
        # by the first map falls through verbatim and can alias a kept
        # epoch-1 coordinate (found by this harness, directed_c3 leg B),
        # and on incomparable cuts the first map's domain misses the
        # other cut's records entirely.  This is Addendum 4's "carry the
        # composite's own surviving domain", sharpened.
        u0 = frozenset(st.shadow[i] for i in spms[-1].kept_ids)
        comp = spms[0]
        for nxt in spms[1:]:
            comp = compose(comp, nxt, universe=u0)
        return cur, comp, spms

    seqA = [(cuts[0], declared[cuts[0]])]
    for k in range(1, len(cuts)):
        Wk = frozenset().union(*cuts[:k + 1])
        decWk = frozenset().union(
            *[declared[S] for S in cuts[:k + 1]]) - Wk
        seqA.append((Wk, decWk))
    seqB = [(cuts[-1], declared[cuts[-1]])]
    seqB.append((W, declW))
    stA, GA, spmsA = path2(seqA)
    stB, GB, spmsB = path2(seqB)
    stC, FC, _ = path2([(W, declW)])

    res = {'s1': True, 's2': True, 's3': True, 'detail': ''}
    # s1: bit-identical states + identical composite maps on surviving dom
    if not (stA.shadow == stB.shadow == stC.shadow
            and stA.deleted == stB.deleted == stC.deleted):
        res['s1'] = False
        res['detail'] += 'state-mismatch '
    if not (GA.dom == GB.dom == FC.dom):
        res['s1'] = False
        res['detail'] += 'dom-mismatch(%d,%d,%d) ' % (
            len(GA.dom), len(GB.dom), len(FC.dom))
    else:
        for c in FC.dom:
            if not (GA.rho(c) == GB.rho(c) == FC.rho(c)):
                res['s1'] = False
                res['detail'] += 'map-mismatch@%r ' % (c,)
                break
    # s2: identical live-chain key order + identical reads + refinement map
    if not (stA.live_ids() == stB.live_ids() == stC.live_ids()
            == twin.live_ids()):
        res['s2'] = False
        res['detail'] += 'order-mismatch '
    else:
        ids = stA.live_ids()
        h = {stA.shadow[i]: stB.shadow[i] for i in ids}   # refinement map
        srt = sorted(h, key=key)
        if [h[c] for c in srt] != sorted(h.values(), key=key):
            res['s2'] = False
            res['detail'] += 'refinement-not-order-iso '
    # s3: reads identical
    if not (stA.read() == stB.read() == stC.read() == twin.read()):
        res['s3'] = False
        res['detail'] += 'read-mismatch '
    # continuation: same ops on all four states, reads compared stepwise
    if cont_ops:
        contok_check(cont_ops, [twin, stA, stB, stC])
        for o in cont_ops:
            for s in (twin, stA, stB, stC):
                if o[1] == 'ins':
                    assert o[2] == 0 or o[2] in s.shadow, \
                        'continuation anchor %r missing (model finding)' % (o,)
                    s.ins(o[0], o[3], o[2])
                else:
                    s.dele(o[2])
            if not (stA.read() == stB.read() == stC.read() == twin.read()):
                res['s3'] = False
                res['s2'] = False
                res['detail'] += 'cont-read-mismatch@%r ' % (o,)
                break
    return res

# -------------------------------------------------------------- selfchecks

def selfchecks():
    out = []
    # SC1: single-cut compaction is reads-identical (#97 T2, model form).
    # Hand-derived: inserts a(1),b(2),c(3) at root, delete b (id 4); cut =
    # everything: b dropped, group {1,3} renumbers to {1,2}; read stays
    # [c, a] (descending delta: c newest first).
    events = {
        1: Ev(1, 'ins', 0, anchor=0, elem='a', deps=frozenset()),
        2: Ev(2, 'ins', 0, anchor=0, elem='b', deps=frozenset({1})),
        3: Ev(3, 'ins', 0, anchor=0, elem='c', deps=frozenset({2})),
        4: Ev(4, 'del', 0, target=2, deps=frozenset({3, 2})),
    }
    delof = delof_index(events)
    st = fold(events, events.keys())
    assert st.read() == [(3, 'c'), (1, 'a')]
    st1, spm = compact_step(st, events, frozenset(events), frozenset(), delof)
    assert st1.read() == [(3, 'c'), (1, 'a')], st1.read()
    assert st1.shadow == {1: (1,), 3: (2,)}, st1.shadow   # hand: 1->1, 3->2
    out.append('SC1 single-cut reads-identical + hand renumber: PASS')
    # SC2: sequential (nested) composition, three strengths.  Hand: chain
    # r1(1)->r2(2)->x(3), del r1 (4) settles in cut1, del r2 (5) settles in
    # cut2.  Cut1 {1,2,3,4}: drop r1; x=(1,1,1)->(1,1) after rank (r1 level
    # phantom-unary but chain length 1: no fusion, level kept).  Wait: at
    # cut1 kept = r2 (1,1)->(1,1)? r1 dropped so tree from kept coords
    # {(1,1),(1,1,1)}: node (1) phantom-unary, node (1,1)=r2 record.
    # Chain length 1 => no fusion; rank keeps unary deltas: r2=(1,1),
    # x=(1,1,1).  Cut2 (union, rel): drop r2; phantoms (1),(1,1): k=2
    # spine, head (1) kept, interior dropped: x -> (1,1).  One-shot at
    # union: drop r1,r2; phantoms (1),(1,1): x=(1,1,1) -> (1,1).  Same.
    events = {
        1: Ev(1, 'ins', 0, anchor=0, elem='r1', deps=frozenset()),
        2: Ev(2, 'ins', 0, anchor=1, elem='r2', deps=frozenset({1})),
        3: Ev(3, 'ins', 0, anchor=2, elem='x', deps=frozenset({2})),
        4: Ev(4, 'del', 0, target=1, deps=frozenset({3, 1})),
        5: Ev(5, 'del', 0, target=2, deps=frozenset({4, 2})),
    }
    delof = delof_index(events)
    st = fold(events, events.keys())
    S1, W = frozenset({1, 2, 3, 4}), frozenset(events)
    stA1, F1 = compact_step(st, events, S1, frozenset(), delof)
    assert stA1.shadow[3] == (1, 1, 1) and stA1.shadow[2] == (1, 1), stA1.shadow
    stA2, F2 = compact_step(stA1, events, W, frozenset(), delof)
    stC, FC = compact_step(st, events, W, frozenset(), delof)
    assert stA2.shadow == stC.shadow == {3: (1, 1)}, (stA2.shadow, stC.shadow)
    G = compose(F1, F2)
    assert G.dom == FC.dom and all(G.rho(c) == FC.rho(c) for c in G.dom)
    out.append('SC2 nested two-epoch composition bit-identical (s1): PASS')
    # SC3: the Addendum-4 landmine, minimal linear form.  Hand: a=(1),
    # b=(2) at root; cut1 = both live (identity map, dom {(1),(2)});
    # b's delete settles by cut2: drop (2)?? -- no: a=(1) dies between
    # epochs.  Take: del a (id 3) settles only in cut2.  Cut2 rel: drop
    # a=(1); b=(2)->(1): rank 1 RECLAIMED.  Naive composite on full dom:
    # (1) -> verbatim (1) [dropped coord falls through], (2) -> (1):
    # COLLIDES.  Surviving-domain composite: dom {(2)} only: injective.
    events = {
        1: Ev(1, 'ins', 0, anchor=0, elem='a', deps=frozenset()),
        2: Ev(2, 'ins', 0, anchor=0, elem='b', deps=frozenset({1})),
        3: Ev(3, 'del', 0, target=1, deps=frozenset({2, 1})),
    }
    delof = delof_index(events)
    st = fold(events, events.keys())
    S1, W = frozenset({1, 2}), frozenset(events)
    st1, F1 = compact_step(st, events, S1, frozenset(), delof)
    assert F1.dom == frozenset({(1,), (2,)})
    st2, F2 = compact_step(st1, events, W, frozenset(), delof)
    assert st2.shadow == {2: (1,)}, st2.shadow
    naive = compose(F1, F2, naive=True)
    assert not injective_on(naive, list(naive.dom)), \
        'landmine NOT reproduced: naive composition should collide'
    surv = compose(F1, F2)
    assert surv.dom == frozenset({(2,)}) and injective_on(surv, list(surv.dom))
    out.append('SC3 naive composition collides, surviving-domain fix passes '
               '(the Addendum-4 landmine reproduced): PASS')
    return out

# ---------------------------------------------------- directed cases c1-c4

def directed_c1():
    """Rank reclaim across the diamond, two-sided.  Hand derivation:
    root inserts x1(id1)=(1) x2(id2)=(2) x3(id3)=(3) x4(id4)=(4);
    del x1 (id5) settles only in S2; del x3 (id6) settles only in S1.
      S1 = {1,2,3,4,6}:  drop x3; kept (1),(2),(4) -> rank 1,2,3.
        rel W: drop x1 (now (1)); kept (2),(3) -> 1,2.
        NAIVE composite on full dom {(1),(2),(4)}:
          (1) -> dropped at ep2, falls through verbatim = (1)
          (2) -> (1)          COLLISION (two-sided leg A).
        surviving dom {(2),(4)}: (2)->(1), (4)->(2): injective.
      S2 = {1,2,3,4,5}:  drop x1; kept (2),(3),(4) -> rank 1,2,3.
        rel W: drop x3 (now (2)); kept (1),(3) -> 1,2.
        NAIVE on full dom {(2),(3),(4)}:
          (3) -> dropped, falls through verbatim = (2)
          (4) -> (2)          COLLISION (two-sided leg B).
        surviving dom {(2),(4)}: (2)->(1), (4)->(2): injective.
      One-shot W: dead {x1,x3}; kept (2),(4) -> (1),(2).
    All three surviving composites agree: x2 -> (1), x4 -> (2): s1 holds.
    Post-S1 straggler s (id 9, root, coord (9), minted after both
    declarations, NOT declared): rides through every path verbatim at the
    root factor; fresh delta 9 dominates ordinals (rED_fresh_dominates);
    final read everywhere = [s, x4, x2] = the twin's."""
    events = {
        1: Ev(1, 'ins', 0, anchor=0, elem='x1', deps=frozenset()),
        2: Ev(2, 'ins', 0, anchor=0, elem='x2', deps=frozenset({1})),
        3: Ev(3, 'ins', 0, anchor=0, elem='x3', deps=frozenset({2})),
        4: Ev(4, 'ins', 0, anchor=0, elem='x4', deps=frozenset({3})),
        5: Ev(5, 'del', 1, target=1, deps=frozenset({1})),
        6: Ev(6, 'del', 2, target=3, deps=frozenset({3})),
    }
    delof = delof_index(events)
    S1 = frozenset({1, 2, 3, 4, 6})
    S2 = frozenset({1, 2, 3, 4, 5})
    W = S1 | S2
    st = fold(events, events.keys())
    # leg A
    stA1, F1 = compact_step(st, events, S1, frozenset(), delof)
    assert stA1.shadow[1] == (1,) and stA1.shadow[2] == (2,) \
        and stA1.shadow[4] == (3,), stA1.shadow
    stA2, F2A = compact_step(stA1, events, W, frozenset(), delof)
    naiveA = compose(F1, F2A, naive=True)
    assert not injective_on(naiveA, list(naiveA.dom)), \
        'c1 FAIL companion missing: naive leg A should collide'
    # leg B
    stB1, F1b = compact_step(st, events, S2, frozenset(), delof)
    assert stB1.shadow[2] == (1,) and stB1.shadow[3] == (2,) \
        and stB1.shadow[4] == (3,), stB1.shadow
    stB2, F2B = compact_step(stB1, events, W, frozenset(), delof)
    naiveB = compose(F1b, F2B, naive=True)
    assert not injective_on(naiveB, list(naiveB.dom)), \
        'c1 FAIL companion missing: naive leg B should collide'
    # one-shot + s1 agreement, hand values (composites on the CARRIED
    # surviving domain: the epoch-0 coords of the join cut's kept ids)
    stC, FC = compact_step(st, events, W, frozenset(), delof)
    u0 = frozenset(st.shadow[i] for i in FC.kept_ids)
    survA = compose(F1, F2A, universe=u0)
    survB = compose(F1b, F2B, universe=u0)
    assert injective_on(survA, list(survA.dom))
    assert injective_on(survB, list(survB.dom))
    assert stA2.shadow == stB2.shadow == stC.shadow == \
        {2: (1,), 4: (2,)}, (stA2.shadow, stB2.shadow, stC.shadow)
    assert survA.dom == survB.dom == frozenset({(2,), (4,)})
    for c in survA.dom:
        assert survA.rho(c) == survB.rho(c) == FC.rho(c)
    # post-cut straggler, fresh delta dominates
    for s in (stA2, stB2, stC, st):
        s.ins(9, 's', 0)
    assert stA2.read() == stB2.read() == stC.read() == st.read() \
        == [(9, 's'), (4, 'x4'), (2, 'x2')]
    return ('c1 rank reclaim: naive composition COLLIDES on both legs '
            '(FAIL companion), surviving-domain composite injective and '
            'path-equal (s1), straggler read = twin: PASS')


def directed_c2():
    """Fusion asymmetry.  Unary spine r1..r4 with live leaf x below;
    dels of r1,r2 settle in S1 only, dels of r3,r4 settle in S2 only.
    Hand derivation (all deltas 1):
      leg A: S1 drops r1,r2: phantoms (1),(1,1) unary, k=2 spine: head (1)
        kept, interior (1,1) dropped: r3 (1,1,1)->(1,1), r4 ->(1,1,1),
        x ->(1,1,1,1).  rel W: drop r3,r4: phantoms (1),(1,1),(1,1,1),
        k=3 spine: head (1): x -> (1,1).
      leg B: S2 keeps r1,r2 (their dels unsettled there: records stay,
        logically deleted), drops r3,r4: phantoms (1,1,1),(1,1,1,1), k=2:
        head (1,1,1) kept: x (1,1,1,1,1) -> (1,1,1,1).  rel W: drop r1,r2:
        phantoms (1),(1,1),(1,1,1) k=3: head (1): x -> (1,1).
      one-shot: drop all four: phantoms (1)..(1,1,1,1) k=4: head (1):
        x (1,1,1,1,1) -> (1,1).
    Path A fuses a prefix then the rest, path B a suffix then the rest,
    C fuses once: all land on x = (1,1) because fusion always keeps the
    OUTERMOST head.  Expect s1."""
    events = {
        1: Ev(1, 'ins', 0, anchor=0, elem='r1', deps=frozenset()),
        2: Ev(2, 'ins', 0, anchor=1, elem='r2', deps=frozenset({1})),
        3: Ev(3, 'ins', 0, anchor=2, elem='r3', deps=frozenset({2})),
        4: Ev(4, 'ins', 0, anchor=3, elem='r4', deps=frozenset({3})),
        5: Ev(5, 'ins', 0, anchor=4, elem='x', deps=frozenset({4})),
        6: Ev(6, 'del', 1, target=1, deps=frozenset({1})),
        7: Ev(7, 'del', 1, target=2, deps=frozenset({2})),
        8: Ev(8, 'del', 2, target=3, deps=frozenset({3})),
        9: Ev(9, 'del', 2, target=4, deps=frozenset({4})),
    }
    delof = delof_index(events)
    S1 = frozenset({1, 2, 3, 4, 5, 6, 7})
    S2 = frozenset({1, 2, 3, 4, 5, 8, 9})
    W = S1 | S2
    st = fold(events, events.keys())
    stA1, F1 = compact_step(st, events, S1, frozenset(), delof)
    assert stA1.shadow[5] == (1, 1, 1, 1), stA1.shadow    # hand: prefix fused
    stA2, F2A = compact_step(stA1, events, W, frozenset(), delof)
    stB1, F1b = compact_step(st, events, S2, frozenset(), delof)
    assert stB1.shadow[5] == (1, 1, 1, 1), stB1.shadow    # hand: suffix fused
    stB2, F2B = compact_step(stB1, events, W, frozenset(), delof)
    stC, FC = compact_step(st, events, W, frozenset(), delof)
    # s1: hand value x = (1,1) on all three paths
    assert stA2.shadow == stB2.shadow == stC.shadow == {5: (1, 1)}, \
        (stA2.shadow, stB2.shadow, stC.shadow)
    GA, GB = compose(F1, F2A), compose(F1b, F2B)
    assert GA.dom == GB.dom == FC.dom == frozenset({(1, 1, 1, 1, 1)})
    assert GA.rho((1, 1, 1, 1, 1)) == GB.rho((1, 1, 1, 1, 1)) \
        == FC.rho((1, 1, 1, 1, 1)) == (1, 1)
    # s2/s3 follow; check reads vs twin
    assert stA2.read() == stB2.read() == stC.read() == st.read() \
        == [(5, 'x')]
    return ('c2 fusion asymmetry: prefix-then-rest, suffix-then-rest and '
            'one-shot all fuse to x=(1,1); s1, s2, s3 all hold: PASS')


def directed_c3():
    """In-flight guard across the diamond.  Root group a(1) b(2) c(3);
    del b (id4) settled everywhere; f (id5, root) declared in flight at
    S1's declaration but settled under S2; d (id6, root) minted after
    S2's declaration, settled under S1 only.
      S1 = {1,2,3,4,6}, declared(S1) = {5}: root group FROZEN: kept
        a(1) c(3) d(6) verbatim; f delivered later rides at (5).
        rel W (f now settled, nothing declared): renumber {1,3,5,6} ->
        a(1) c(2) f(3) d(4): a renumbering OF the frozen (skipped) group.
      S2 = {1,2,3,4,5}, declared(S2) = {} (d not yet minted): renumber
        {1,3,5} -> a(1) c(2) f(3); d arrives post-cut at (6).
        rel W: renumber {1,2,3,6} -> a(1) c(2) f(3) d(4).
      one-shot W, declared = ({5} u {}) minus W = {}: renumber {1,3,5,6}
        -> a(1) c(2) f(3) d(4).
    Codeword-level hand expectation: all three paths end with exactly
    a=(1) c=(2) f=(3) d=(4); read = [d,f,c,a] = twin's."""
    events = {
        1: Ev(1, 'ins', 0, anchor=0, elem='a', deps=frozenset()),
        2: Ev(2, 'ins', 0, anchor=0, elem='b', deps=frozenset({1})),
        3: Ev(3, 'ins', 0, anchor=0, elem='c', deps=frozenset({2})),
        4: Ev(4, 'del', 0, target=2, deps=frozenset({2})),
        5: Ev(5, 'ins', 1, anchor=0, elem='f', deps=frozenset()),
        6: Ev(6, 'ins', 2, anchor=0, elem='d', deps=frozenset()),
    }
    delof = delof_index(events)
    S1, S2 = frozenset({1, 2, 3, 4, 6}), frozenset({1, 2, 3, 4, 5})
    W = S1 | S2
    st = fold(events, events.keys())
    stA1, F1 = compact_step(st, events, S1, frozenset({5}), delof)
    # hand: frozen group => deltas verbatim
    assert stA1.shadow[1] == (1,) and stA1.shadow[3] == (3,) \
        and stA1.shadow[6] == (6,) and stA1.shadow[5] == (5,), stA1.shadow
    stA2, F2A = compact_step(stA1, events, W, frozenset(), delof)
    stB1, F1b = compact_step(st, events, S2, frozenset(), delof)
    # hand: unfrozen renumber {1,3,5} -> 1,2,3; d rides at (6)
    assert stB1.shadow[1] == (1,) and stB1.shadow[3] == (2,) \
        and stB1.shadow[5] == (3,) and stB1.shadow[6] == (6,), stB1.shadow
    stB2, F2B = compact_step(stB1, events, W, frozenset(), delof)
    stC, FC = compact_step(st, events, W, frozenset(), delof)
    want = {1: (1,), 3: (2,), 5: (3,), 6: (4,)}
    assert stA2.shadow == stB2.shadow == stC.shadow == want, \
        (stA2.shadow, stB2.shadow, stC.shadow)
    assert stA2.read() == stB2.read() == stC.read() == st.read() \
        == [(6, 'd'), (5, 'f'), (3, 'c'), (1, 'a')]
    u0 = frozenset(st.shadow[i] for i in FC.kept_ids)   # carried domain
    GA = compose(F1, F2A, universe=u0)
    GB = compose(F1b, F2B, universe=u0)
    for c in FC.dom:
        assert GA.rho(c) == GB.rho(c) == FC.rho(c), c
    return ('c3 in-flight guard: freeze-then-renumber equals '
            'renumber-once at the codeword level (s1): PASS')


def directed_c4():
    """No-translation control (the required FAIL): a cross-epoch merge
    without translation must flip a read, justifying the runtime's throw.
    Hand derivation: x1(1) x2(2) at root, del x1 (3), all settled.  R1
    compacts: x1 dropped, x2 (2)->(1).  R2 (epoch 0) mints y (id 9)
    anchored at x2: coord (2,7).  Raw union of shadows WITHOUT
    translation: {x2:(1), y:(2,7)}.  Keys: x2 -> (-1,), y -> (-2,-7):
    y sorts BEFORE x2 (not under it): read [y, x2].  Truth (twin, epoch-0
    coords x2=(2), y=(2,7)): y is x2's child: read [x2, y].  FLIPPED.
    With translation (y's stable prefix (2) -> (1), tail verbatim:
    y=(1,7)) the read is [x2, y] = twin's: the fix the runtime owes."""
    events = {
        1: Ev(1, 'ins', 0, anchor=0, elem='x1', deps=frozenset()),
        2: Ev(2, 'ins', 0, anchor=0, elem='x2', deps=frozenset({1})),
        3: Ev(3, 'del', 0, target=1, deps=frozenset({1})),
    }
    delof = delof_index(events)
    st = fold(events, events.keys())
    W = frozenset(events)
    st1, spm = compact_step(st, events, W, frozenset(), delof)
    assert st1.shadow == {2: (1,)}, st1.shadow
    twin = st.copy()
    twin.ins(9, 'y', 2)
    assert twin.shadow[9] == (2, 7) and twin.read() == [(2, 'x2'), (9, 'y')]
    # raw no-translation merge: R2's y record unioned verbatim
    raw = st1.copy()
    raw.shadow[9], raw.anchor[9], raw.elem[9] = (2, 7), 2, 'y'
    assert raw.read() == [(9, 'y'), (2, 'x2')], raw.read()   # FLIPPED
    assert [i for i, _e in raw.read()] != [i for i, _e in twin.read()]
    # translated merge: rho(y) = rho((2)) + (7,) = (1,7)
    fixed = st1.copy()
    fixed.shadow[9], fixed.anchor[9], fixed.elem[9] = spm.rho((2, 7)), 2, 'y'
    assert fixed.shadow[9] == (1, 7)
    assert fixed.read() == [(2, 'x2'), (9, 'y')]
    return ('c4 no-translation control: raw cross-epoch union flips the '
            'read [x2,y] -> [y,x2] (FAIL, justifying the runtime throw); '
            'translated merge restores it: PASS')

# ------------------------------------------- H-M: barrier-free merge engine
#
# Replicas carry (state, heard, cutset).  A replica's epoch IS its cutset
# (a certified downward-closed all-heard event set); the coordinate space
# is compact-at-cutset.  advance() relative-compacts to a superset cut;
# join() advances both sides to the UNION cutset and unions states with a
# coord-agreement assert on shared ids: that assert is H-D's s1 tested in
# vivo (two replicas reached the join epoch along different paths and
# must agree on every shared coordinate).  decl() is the certificate
# registry: decl(U u V) = (decl(U) | decl(V)) - (U | V).

class Rep:
    __slots__ = ('rid', 'state', 'heard', 'cutset')

    def __init__(self, rid, state, heard):
        self.rid, self.state, self.heard = rid, state, heard
        self.cutset = frozenset()


class Sim:
    def __init__(self, events, heard_sets):
        self.events = dict(events)
        self.reps = [Rep(r, fold(events, h), set(h))
                     for r, h in enumerate(heard_sets)]
        self.decl = {frozenset(): frozenset()}
        self.mint_cut = {i: frozenset() for i in events}
        self.clock = max(events) if events else 0
        self.delof = None
        self._reindex()

    def _reindex(self):
        self.delof = delof_index(self.events)

    def declare(self, S):
        """Certificate for cut S: declared = existing inserts not in S."""
        S = frozenset(S)
        if S not in self.decl:
            self.decl[S] = frozenset(
                i for i, e in self.events.items()
                if e.kind == 'ins' and i not in S)
        return S

    def join_cut(self, U, V):
        W = U | V
        if W not in self.decl:
            self.decl[W] = (self.decl[U] | self.decl[V]) - W
        return W

    def mint(self, r, rng):
        self.clock += 1
        i = self.clock
        live = r.state.live_ids()
        if live and rng.random() < 0.3:
            tgt = rng.choice(live)
            self.events[i] = Ev(i, 'del', r.rid, target=tgt,
                                deps=frozenset({tgt}))
            r.state.dele(tgt)
        else:
            a = rng.choice([0] + live)
            deps = frozenset() if a == 0 else frozenset({a})
            self.events[i] = Ev(i, 'ins', r.rid, anchor=a, elem=i, deps=deps)
            # ContOK at mint time (clauses 1 and 3 vs the minter's state)
            assert all(i > j for j in r.state.shadow), 'ContOK(1) violated'
            r.state.ins(i, i, a)
            k = key(r.state.shadow[i])
            assert all(k != key(c) for j, c in r.state.shadow.items()
                       if j != i), 'ContOK(3) violated'
            CONTOK['checked'] += 1
        r.heard.add(i)
        self.mint_cut[i] = r.cutset
        self._reindex()
        return i

    def deliver_ready(self, r, rng):
        ready = [i for i in self.events
                 if i not in r.heard and self.events[i].deps <= r.heard]
        if not ready:
            return None
        i = rng.choice(ready)
        e = self.events[i]
        if e.kind == 'ins':
            # id-addressed ingest: coord re-derived from the local anchor
            # record (H3).  The anchor must be present: settled-dead
            # anchors of pre-declaration mints are RETAINED, and
            # post-declaration minters never anchor at settled-dead
            # records (they heard the delete).  A failure here is a
            # protocol finding, not harness noise.
            assert e.anchor == 0 or e.anchor in r.state.shadow, \
                'delivery anchor %d missing at replica %d' % (e.anchor, r.rid)
            r.state.ins(i, e.elem, e.anchor)
        else:
            r.state.dele(e.target)
        r.heard.add(i)
        return i

    def advance(self, r, W):
        assert r.cutset <= W and W in self.decl
        ins_in_W = {i for i in W if self.events[i].kind == 'ins'}
        assert ins_in_W <= r.heard, 'cut not certified for this replica'
        settled = {i: r.state.shadow[i] for i in ins_in_W
                   if i in r.state.shadow}
        dead = {i for i in settled if self.delof.get(i, frozenset()) & W}
        decl = {}
        for d in self.decl[W]:
            e = self.events[d]
            if d in r.state.shadow:
                decl[d] = (e.anchor, r.state.shadow[d])
            elif e.anchor == 0:
                decl[d] = (0, (d,))
            elif e.anchor in r.state.shadow:
                decl[d] = (e.anchor, r.state.shadow[e.anchor] + (d - e.anchor,))
        spm = make_spm(settled, dead, decl)
        r.state = apply_spm(r.state, spm)
        r.cutset = W

    def join(self, a, b):
        W = self.join_cut(a.cutset, b.cutset)
        self.advance(a, W)
        self.advance(b, W)
        merged = a.state.copy()
        for i, c in b.state.shadow.items():
            if i in merged.shadow:
                assert merged.shadow[i] == c, \
                    ('JOIN COORD DIVERGENCE at %d: %r vs %r '
                     '(H-D s1 refuted in vivo)' % (i, merged.shadow[i], c))
            else:
                merged.shadow[i] = c
                merged.anchor[i] = b.state.anchor[i]
                merged.elem[i] = b.state.elem[i]
        merged.deleted |= b.state.deleted
        heard = a.heard | b.heard
        a.state, b.state = merged, merged.copy()
        a.heard, b.heard = set(heard), set(heard)
        return W

    def twin_read(self, r):
        return fold(self.events, r.heard).read()


A3 = {'checked': 0, 'violations': 0}

def run_hm_trial(seed):
    """One randomized barrier-free-merge trial.  Returns None or a fail
    string.  Shape: pre-history -> two incomparable certified cuts ->
    R0/R1 compact, everyone keeps editing + delivering (stragglers
    included) -> pairwise joins (in-vivo s1 asserts) -> full exchange ->
    round 2 with fresh incomparable cuts on top (multi-epoch, diamonds of
    diamonds) -> final join of all -> reads vs the never-compacted twin."""
    rng = random.Random(seed)
    n_rep = rng.randrange(2, 5)
    events, heard = gen_history(rng, n_rep, rng.randrange(18, 34))
    sim = Sim(events, heard)
    settled = frozenset(set.intersection(*[r.heard for r in sim.reps]))
    if len(settled) < 5:
        return 'skip'
    pair = incomparable_pair(rng, settled, sim.events)
    if pair is None:
        return 'skip'
    S1, S2 = sim.declare(pair[0]), sim.declare(pair[1])
    try:
        sim.advance(sim.reps[0], S1)
        sim.advance(sim.reps[1], S2)
        for r in sim.reps[:2]:
            if r.state.read() != sim.twin_read(r):
                return 'seed=%d advance read != twin' % seed
        # continuations: mints + straggler deliveries on every replica
        for _ in range(rng.randrange(6, 16)):
            r = rng.choice(sim.reps)
            if rng.random() < 0.5:
                sim.mint(r, rng)
            else:
                sim.deliver_ready(r, rng)
            if r.state.read() != sim.twin_read(r):
                return 'seed=%d cont read != twin at replica %d' % (
                    seed, r.rid)
        # round-1 joins: R0 x R1 is the incomparable-epochs merge
        sim.join(sim.reps[0], sim.reps[1])
        for r in sim.reps[:2]:
            if r.state.read() != sim.twin_read(r):
                return 'seed=%d join read != twin' % seed
        # full exchange (delivers all stragglers; A3 moment)
        for r in sim.reps:
            while sim.deliver_ready(r, rng) is not None:
                pass
        W1 = sim.reps[0].cutset
        for r in sim.reps[2:]:
            sim.join(sim.reps[0], r)
        moment = sim.clock          # all-advanced + all-heard: A3 moment
        assert all(r.cutset >= W1 for r in sim.reps)
        # round 2: fresh incomparable cuts ON TOP (multi-epoch)
        settled2 = frozenset(set.intersection(*[r.heard for r in sim.reps]))
        base = sim.reps[0].cutset
        pair2 = None
        for _ in range(40):
            c1 = frozenset(base | sample_cut(rng, settled2 - base, sim.events)) \
                if settled2 - base else None
            c2 = frozenset(base | sample_cut(rng, settled2 - base, sim.events)) \
                if settled2 - base else None
            if c1 and c2 and not (c1 <= c2) and not (c2 <= c1):
                pair2 = (c1, c2)
                break
        if pair2:
            T1, T2 = sim.declare(pair2[0]), sim.declare(pair2[1])
            sim.advance(sim.reps[0], T1)
            sim.advance(sim.reps[1], T2)
            for _ in range(rng.randrange(3, 9)):
                r = rng.choice(sim.reps)
                if rng.random() < 0.6:
                    i = sim.mint(r, rng)
                    # H-A3 bookkeeping: after the all-advanced moment no
                    # mint may sit below the superseded epoch
                    A3['checked'] += 1
                    if i > moment and not sim.mint_cut[i] >= W1:
                        A3['violations'] += 1
                else:
                    sim.deliver_ready(r, rng)
                if r.state.read() != sim.twin_read(r):
                    return 'seed=%d round2 read != twin' % seed
            sim.join(sim.reps[0], sim.reps[1])
        # final: join everyone
        for r in sim.reps[1:]:
            sim.join(sim.reps[0], r)
        r0 = sim.reps[0]
        if r0.state.read() != sim.twin_read(r0):
            return 'seed=%d FINAL merged read != twin' % seed
        return None
    except AssertionError as ex:
        return 'seed=%d ASSERT %s' % (seed, ex)


def directed_a3():
    """H-A3, the certificate question.  Scenario, hand-derived: three
    replicas; R2 mints x (epoch 0), undelivered to R0.  Cut S (not
    containing x, x declared) is certified; ALL THREE advance (ack).
    Ack-only certificate now claims epoch-0 is superseded; yet x, an
    epoch-0-minted op (mint_cut = {}), is STILL IN FLIGHT and arrives at
    R0 afterwards: the ack-only drop is UNSOUND.  The sufficient
    certificate is ack + AllHeardSince(each minter's advance): every op
    minted before its minter's advance is heard everywhere.  In the
    scenario that moment occurs only after x lands, and every op minted
    after it has mint_cut >= S by construction (cutsets only grow), so no
    old-space arrival can follow it: dropping epoch 0's map is then
    justified."""
    rng = random.Random(0xA3)
    events = {
        1: Ev(1, 'ins', 0, anchor=0, elem='a', deps=frozenset()),
        2: Ev(2, 'ins', 1, anchor=0, elem='b', deps=frozenset()),
    }
    heard = [{1, 2}, {1, 2}, {1, 2}]
    sim = Sim(events, heard)
    x = sim.mint(sim.reps[2], random.Random(1))     # R2 mints x, epoch 0
    while sim.events[x].kind != 'ins':              # ensure it is an insert
        x = sim.mint(sim.reps[2], random.Random(2))
    S = sim.declare(frozenset({1, 2}))
    assert x in sim.decl[S]                          # x is declared in flight
    for r in sim.reps:
        sim.advance(r, S)                            # everyone acks epoch 1
    # ack-only moment: all advanced, yet x undelivered to R0
    assert x not in sim.reps[0].heard
    assert sim.mint_cut[x] == frozenset()            # minted in epoch 0
    got = sim.deliver_ready(sim.reps[0], rng)        # old-space arrival!
    arrivals = {got}
    while got is not None and x not in arrivals:
        got = sim.deliver_ready(sim.reps[0], rng)
        arrivals.add(got)
    assert x in arrivals, 'x should arrive after the ack-only moment'
    # strong certificate: now every pre-advance mint is heard everywhere
    for r in sim.reps:
        while sim.deliver_ready(r, rng) is not None:
            pass
    pre_advance = {i for i in sim.events if not (sim.mint_cut[i] >= S)}
    assert all(i in r.heard for i in pre_advance for r in sim.reps)
    # from this moment every future mint has mint_cut >= S:
    for r in sim.reps:
        i = sim.mint(r, rng)
        assert sim.mint_cut[i] >= S
    return ('A3 directed: ack-only certificate UNSOUND (declared epoch-0 '
            'straggler x arrives after all replicas advanced: the map is '
            'still needed); ack + AllHeardSince(pre-advance mints) closes '
            'it (every later mint is minted at cutset >= S): PASS')

# ------------------------------------------------- randomized H-D driver

def gen_cont(rng, events, kmax):
    """Continuation ops beyond both cuts: minted against the evolving twin
    so anchors are live; ids Lamport-fresh."""
    twin = fold(events, events.keys())
    clock = max(events)
    ops = []
    for _ in range(rng.randrange(0, kmax)):
        clock += 1
        live = twin.live_ids()
        if live and rng.random() < 0.3:
            t = rng.choice(live)
            ops.append((clock, 'del', t))
            twin.dele(t)
        else:
            a = rng.choice([0] + live)
            ops.append((clock, 'ins', a, clock))
            twin.ins(clock, clock, a)
    return ops


def randomized_hd(n_pairs, n_triples, seed0=0, chainy=False):
    stats = {'pairs': 0, 'triples': 0,
             's1': 0, 's2': 0, 's3': 0, 'details': []}
    seed = seed0
    want = [('pairs', n_pairs, 2), ('triples', n_triples, 3)]
    for name, n_want, n_cuts in want:
        while stats[name] < n_want:
            seed += 1
            if seed > seed0 + 40 * (n_pairs + n_triples + 1):
                break                                    # safety valve
            rng = random.Random(seed)
            events, heard = gen_history(rng, rng.randrange(2, 5),
                                        rng.randrange(16, 40),
                                        chainy=chainy)
            settled = frozenset(set.intersection(*map(set, heard)))
            if len(settled) < 5:
                continue
            pair = incomparable_pair(rng, settled, events)
            if pair is None:
                continue
            cuts = [pair[0], pair[1]]
            if n_cuts == 3:
                third = None
                for _ in range(40):
                    S3 = sample_cut(rng, settled, events)
                    if S3 and not any(S3 <= c or c <= S3 for c in cuts):
                        third = S3
                        break
                if third is None:
                    continue
                cuts.append(third)
            existing_ins = frozenset(i for i, e in events.items()
                                     if e.kind == 'ins')
            declared = {S: existing_ins - S for S in cuts}
            cont = gen_cont(rng, events, 9)
            delof = delof_index(events)
            stats[name] += 1
            try:
                res = run_diamond(events, cuts, declared, cont, delof)
            except AssertionError as ex:
                res = {'s1': False, 's2': False, 's3': False,
                       'detail': 'ASSERT %s' % ex}
            for s in ('s1', 's2', 's3'):
                if res[s]:
                    stats[s] += 1
            if res['detail'] and len(stats['details']) < 6:
                stats['details'].append('seed=%d cuts=%d %s'
                                        % (seed, n_cuts, res['detail']))
    return stats


def randomized_hm(n_trials, seed0=10 ** 6):
    done = skipped = 0
    fails = []
    seed = seed0
    while done < n_trials and seed < seed0 + 40 * n_trials:
        seed += 1
        r = run_hm_trial(seed)
        if r == 'skip':
            skipped += 1
            continue
        done += 1
        if r is not None and len(fails) < 6:
            fails.append(r)
        elif r is not None:
            fails.append('...')
            break
    return done, skipped, fails

# ------------------------------------------------------------------ main

if __name__ == '__main__':
    print('==== epoch diamond check (#112 phase 1) ====')
    print('-- selfchecks --')
    for line in selfchecks():
        print('  ' + line)
    print('-- directed cases (hand-derived expectations) --')
    for fn in (directed_c1, directed_c2, directed_c3, directed_c4,
               directed_a3):
        print('  ' + fn())
    print('-- randomized H-D (diamond at three strengths) --')
    hd = randomized_hd(1400, 600)
    hdc = randomized_hd(300, 100, seed0=5 * 10 ** 5, chainy=True)
    for k in ('pairs', 'triples', 's1', 's2', 's3'):
        hd[k] += hdc[k]
    hd['details'] += hdc['details']
    n_hd = hd['pairs'] + hd['triples']
    print('  trials: %d (%d incomparable pairs, %d triples: diamonds of '
          'diamonds; %d spine-heavy chainy trials included)'
          % (n_hd, hd['pairs'], hd['triples'],
             hdc['pairs'] + hdc['triples']))
    for s, label in (('s1', 'bit-identical + composed maps equal'),
                     ('s2', 'order-isomorphic, common refinement'),
                     ('s3', 'reads identical')):
        print('  %s %-38s: %d/%d %s'
              % (s, label, hd[s], n_hd,
                 'PASS' if hd[s] == n_hd else 'FAIL'))
    for d in hd['details']:
        print('    detail:', d)
    print('-- randomized H-M (barrier-free merge vs never-compacted twin) --')
    done, skipped, fails = randomized_hm(400)
    print('  trials: %d completed (%d skipped: no incomparable certified '
          'cuts)' % (done, skipped))
    print('  merge reads == twin, all continuations + multi-epoch: %d/%d %s'
          % (done - len([f for f in fails if f != '...']), done,
             'PASS' if not fails else 'FAIL'))
    for f in fails:
        print('    FAIL:', f)
    print('-- bookkeeping --')
    print('  ContOK continuation checks : %d, violations: %d'
          % (CONTOK['checked'], len(CONTOK['violations'])))
    print('  A3 post-advance mint checks: %d, old-space violations: %d'
          % (A3['checked'], A3['violations']))
    print('==== VERDICT ====')
    ok = (hd['s1'] == n_hd and hd['s2'] == n_hd and hd['s3'] == n_hd
          and not fails and not CONTOK['violations']
          and A3['violations'] == 0)
    print('  H-D  diamond confluence      : %s'
          % ('VALIDATED at s1 (hence s2, s3)' if hd['s1'] == n_hd else
             'VALIDATED at s2' if hd['s2'] == n_hd else
             'VALIDATED at s3 only' if hd['s3'] == n_hd else 'REFUTED'))
    print('  H-M  barrier-free merge      : %s'
          % ('VALIDATED' if not fails else 'REFUTED'))
    print('  H-A3 map-drop certificate    : ack-only UNSOUND (directed); '
          'ack+all-heard sound, %d checks clean' % A3['checked'])
    print('  ContOK                       : %d checks, %d violations'
          % (CONTOK['checked'], len(CONTOK['violations'])))
    sys.exit(0 if ok else 1)
