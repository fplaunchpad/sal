#!/usr/bin/env python3
"""rga_byzantine_check -- self-certifying embed RGA, adversary phase (#116).

RESEARCH QUESTION.  Does a decidable per-op ADMISSION predicate A(op,
declared_past) turn the honest-delivery RELY into a runtime-checked
CONTRACT that no Byzantine participant can violate for convergence /
RA-linearizability, while STRUCTURAL INTENT (non-interleaving of chained
runs) holds by merge geometry?  A is a function of the op plus the
DECLARED past only (a set of content-addressed commit ids), never of a
verifier's private view: any verifier possessing those commits recomputes
the same verdict.  This harness's JOB is to REFUTE the claim by
constructing a Byzantine trace that PASSES A yet BREAKS RA-lin or
interleaves a chained run.  A hit is the finding; a clean sweep pins the
metatheorem for phase-2 Lean.

MODEL (transliterated from epoch_diamond_check.py / embed_recode_check.py;
stdlib only, nothing existing modified).  Coordinates are delta chains
(tuples of positive ints); coord of insert i anchored at a is
coord(a) + (i - a,), root anchor (a = 0) is (i,).  key(c) = tuple(-d for
d in c); display = ascending key sort (ancestor before its subtree, larger
delta = newer sibling first: the RGA recency order).  Delete = record
removal; merge = OR-set survival, coords carried UNCHANGED (birth
constants, Theorem chain(ii)).  A verified read is a function of the event
set alone (fold canonicity e_fold_canon / Theorem chain(i)).

ADMISSION A(op, declared_past) -- decidable, over the DECLARED past:
  reconstruct pre = canonical fold of the down-closed declared event set
  (canonicity: the fold is a function of the set).
  ins(id, el, anchor):
    (a) anchor is root (0) OR present in pre        (phantom-anchor reject)
    (b) coord is DERIVED, coord == base(anchor)+(id-anchor), never the
        shipped coord   (forged-coord reject; FAIL companion trusts ship)
    (c) freshness: id > every insert id in the declared past (Lamport
        monotone) and id not already present (pairwise fresh)
    (d) applicability (eApplicable shape): the anchor is a LIVE record
        carrying exactly its coordinate -- in the tombstone-free embed
        fold, present == live, so (d) coincides with (a); the DERIVED
        coord then makes the newcomer land immediately after its anchor
        (adjacency lemma chainBefore_snoc_iff), so there is no separate
        positional check.
  del(id): id present and live in pre.
  Equivocation is OUT OF SCOPE via the substrate: each replica's ops form
  a signed single-writer chain with monotone ids; NO intra-author fork is
  asserted as an IMPORTED assumption (not defended here).

HYPOTHESES (falsifiable).
  H-C   any set of ops each passing A merges to an RA-linearizable state
        (a loOn-fold witness exists); no A-passing Byzantine trace makes
        two honest verifiers diverge or yields a non-linearizable state.
  H-I   a chained run (each op anchoring the previous) displays
        contiguously in the merge REGARDLESS of authorship (subtree
        convexity); a Byzantine author cannot interleave its chained run
        into an honest run.  subtree_convex is stated over an ARBITRARY
        state (no honesty, no reachability), so H-I is UNCONDITIONAL; the
        harness verifies convexity even on states carrying a REJECTED op.
  H-M-boundary  a Byzantine author CAN insert single chars at any legally
        anchored position and CAN delete any live id; these pass A and are
        NOT breaches (authoring / moderation), demonstrated positively.

PASS+FAIL convention: directed expectations are hand-derived in comments,
never computed from the code under test.  FAIL companions (trust-shipped-
coord, skip-freshness, accept-phantom) demonstrably flip a read or RA-lin.
"""
import hashlib
import json
import random
import sys


# ------------------------------------------------------------------ model

def key(c):
    return tuple(-d for d in c)


class St:
    __slots__ = ('shadow', 'anchor', 'elem')

    def __init__(self):
        self.shadow = {}      # id -> coord tuple (live records only)
        self.anchor = {}      # id -> anchor id (0 = root)
        self.elem = {}        # id -> element

    def copy(self):
        s = St()
        s.shadow = dict(self.shadow)
        s.anchor = dict(self.anchor)
        s.elem = dict(self.elem)
        return s

    def derive(self, i, a):
        """The DERIVED coord of insert i anchored at a in this state."""
        base = () if a == 0 else self.shadow[a]
        return base + (i - a,)

    def ins(self, i, el, a, coord=None):
        """coord=None derives (the honest mint); a passed coord is the
        shipped one (FAIL companion trust-shipped-coord uses it)."""
        self.shadow[i] = self.derive(i, a) if coord is None else coord
        self.anchor[i] = a
        self.elem[i] = el

    def dele(self, x):
        self.shadow.pop(x, None)
        self.anchor.pop(x, None)
        self.elem.pop(x, None)

    def live_ids(self):
        return sorted(self.shadow, key=lambda i: key(self.shadow[i]))

    def read(self):
        return [(i, self.elem[i]) for i in self.live_ids()]

    def read_ids(self):
        return [i for i in self.live_ids()]


def fold(ops, order=None):
    """Canonical fold of an op list.  Every insert stores its CARRIED
    coord (op['coord']) -- the mint written at generation time, a birth
    constant (def:embed do_: the insert writes its carried prefix, never
    reading the state).  So the fold does not consult a live anchor and is
    order-INDEPENDENT: any enumeration of a set folds to the same state
    (fold canonicity / e_fold_canon).  An op WITHOUT a carried coord (an
    unblessed directed fixture) derives from the anchor live so far.
    order=None folds in id (Lamport) order; a supplied order is any
    enumeration, used to witness convergence and the loOn linearization."""
    by_id = {}
    for o in ops:
        by_id[o['id']] = o             # list-order dedup (last wins)
    seq = sorted(by_id) if order is None else order
    st = St()
    for i in seq:
        o = by_id[i]
        if o['type'] == 'ins':
            st.ins(o['id'], o['el'], o['anchor'], coord=o.get('coord'))
        else:
            st.dele(o['target'])       # a delete carries its own fresh id,
    return st                          # removing the record named `target`


def bless(op, past_ops, checks=('phantom', 'derive', 'fresh', 'live')):
    """Admit op against its declared past; on success return a COPY of the
    op carrying the DERIVED coord (the honest mint / carried prefix that
    the merge will treat as a birth constant), so a forged shipped coord
    can never enter a state.  Returns (ok, reason, blessed_op)."""
    ok, reason = admit(op, past_ops, checks=checks)
    if not ok:
        return False, reason, None
    b = dict(op)
    if op['type'] == 'ins':
        pre = fold(past_ops)
        b['coord'] = pre.derive(op['id'], op['anchor'])
    return True, reason, b


# ------------------------------------------- content-address / certificate
#
# Each commit is content-addressed: cid = H(author, seq, op, sorted
# parents).  A commit references its parents by cid, so a phantom past
# (a cid nobody produced) is unresolvable, and a forged payload changes
# the cid.  declared_past = a frontier set of cids; the declared event set
# is its down-closure over parent links.  Single-writer chains: an
# author's commits carry strictly increasing seq and each includes the
# author's previous commit among its parents; no_fork asserts no two
# distinct commits of one author share a seq (equivocation imported as
# out of scope, not defended).

def _op_canon(op):
    if op is None:
        return ['root']
    if op['type'] == 'ins':
        return ['ins', op['id'], op['el'], op['anchor'], op.get('coord')]
    return ['del', op['id']]


class Store:
    def __init__(self):
        self.commits = {}          # cid -> {author, seq, op, parents}
        self.by_author = {}        # author -> {seq -> cid}

    def add(self, author, seq, op, parents):
        parents = sorted(parents)
        cid = hashlib.sha256(
            json.dumps([author, seq, _op_canon(op), parents],
                       sort_keys=True).encode()).hexdigest()[:16]
        # no-fork substrate assumption (asserted, not defended)
        prev = self.by_author.setdefault(author, {})
        assert seq not in prev or prev[seq] == cid, \
            'intra-author fork at %r/%d (equivocation is out of scope)' % (
                author, seq)
        prev[seq] = cid
        self.commits[cid] = {'author': author, 'seq': seq, 'op': op,
                             'parents': parents}
        return cid

    def down_close(self, frontier):
        seen = set()
        stack = list(frontier)
        while stack:
            cid = stack.pop()
            if cid in seen or cid not in self.commits:
                continue
            seen.add(cid)
            stack.extend(self.commits[cid]['parents'])
        return seen

    def resolvable(self, frontier):
        """Every cid in the down-closure is a commit we actually hold."""
        stack = list(frontier)
        seen = set()
        while stack:
            cid = stack.pop()
            if cid in seen:
                continue
            seen.add(cid)
            if cid not in self.commits:
                return False
            stack.extend(self.commits[cid]['parents'])
        return True

    def ops_of(self, cids):
        return [self.commits[c]['op'] for c in cids
                if self.commits[c]['op'] is not None]


# ------------------------------------------------------ admission predicate

def admit(op, past_ops, checks=('phantom', 'derive', 'fresh', 'live')):
    """A(op, declared_past).  past_ops: the ops of the down-closed declared
    event set.  Returns (ok, reason).  `checks` selects which clauses are
    enforced; dropping a clause is a FAIL companion:
      'phantom' off -> accept a phantom anchor
      'derive'  off -> trust the shipped coord
      'fresh'   off -> skip Lamport freshness
      'live'    off -> skip delete-target liveness
    The pre-state is the canonical fold of the declared past (a function of
    the SET, so any possessor recomputes it)."""
    pre = fold(past_ops)                       # canonical reconstruction
    ins_ids = [o['id'] for o in past_ops if o['type'] == 'ins']
    if op['type'] == 'ins':
        i, a = op['id'], op['anchor']
        # (c) freshness: Lamport monotone (exceeds every past insert) +
        # pairwise fresh (not already present)
        if 'fresh' in checks:
            if any(i <= j for j in ins_ids):
                return False, 'stamp_rewind'
            if i in pre.shadow:
                return False, 'dup_id'
        # (a)/(d) phantom-anchor + applicability (present == live here)
        if 'phantom' in checks and a != 0 and a not in pre.shadow:
            return False, 'phantom_anchor'
        # eApplicable's a < t (an anchor stamp below its inserter's)
        if 'fresh' in checks and a != 0 and i <= a:
            return False, 'stamp_rewind'
        # (b) derived coordinate, never the shipped one
        if 'derive' in checks:
            derived = pre.derive(i, a) if (a == 0 or a in pre.shadow) else None
            if derived is None:
                return False, 'phantom_anchor'
            if 'coord' in op and op['coord'] is not None \
                    and tuple(op['coord']) != derived:
                return False, 'forged_coord'
        return True, 'admitted'
    else:  # del: the op carries a fresh id and names a `target` to remove
        if 'live' in checks and op['target'] not in pre.shadow:
            return False, 'del_absent'
        return True, 'admitted'


# ------------------------------------ RA-lin witness / convexity / converge

def common_prefix(a, b):
    n = 0
    for x, y in zip(a, b):
        if x != y:
            break
        n += 1
    return tuple(a[:n])


def causal_order(ops, rng=None):
    """A random loOn linearization: a topological order of the causal DAG
    (insert's anchor before it; delete's target insert before it).  rc =
    Either, so any linear extension is a valid loOn order."""
    by_id = {o['id']: o for o in ops}
    preds = {i: set() for i in by_id}
    ins_ids = {i for i, o in by_id.items() if o['type'] == 'ins'}
    for i, o in by_id.items():
        if o['type'] == 'ins' and o['anchor'] != 0 and o['anchor'] in ins_ids:
            preds[i].add(o['anchor'])          # anchor visible before insert
        if o['type'] == 'del' and o['target'] in ins_ids:
            preds[i].add(o['target'])          # target insert before its delete
    # Kahn with random tie-breaking
    rng = rng or random
    avail = [i for i in by_id if not preds[i]]
    done, out = set(), []
    indeg = {i: set(p) for i, p in preds.items()}
    while avail:
        rng.shuffle(avail)
        i = avail.pop()
        out.append(i)
        done.add(i)
        for j in by_id:
            if j not in done and i in indeg[j]:
                indeg[j].discard(i)
                if not indeg[j] and j not in out and j not in avail:
                    avail.append(j)
    if len(out) != len(by_id):          # a cycle: not linearizable
        return None
    return out


def ra_linearizable(ops, rng=None):
    """(ok, reason).  A loOn-fold witness exists iff: (i) every insert's
    non-root anchor is present as an insert in the set (no dangling coord
    prefix); (ii) two distinct causal linearizations fold to the SAME read
    (convergence); (iii) live coords are pairwise distinct (a total display
    order, no ties).  Under admission all three hold."""
    by_id = {o['id']: o for o in ops}
    ins_ids = {i for i, o in by_id.items() if o['type'] == 'ins'}
    for i, o in by_id.items():
        if o['type'] == 'ins' and o['anchor'] != 0 and o['anchor'] not in ins_ids:
            return False, 'dangling_anchor(%d->%d)' % (i, o['anchor'])
    lin = causal_order(ops, rng)
    if lin is None:
        return False, 'causal_cycle'
    st_id = fold(ops)                    # canonical (id order)
    st_lin = fold(ops, order=lin)        # a witness linearization
    if st_id.read() != st_lin.read():
        return False, 'fold_order_divergence'
    keys = [key(st_id.shadow[i]) for i in st_id.shadow]
    if len(set(keys)) != len(keys):
        return False, 'key_tie(non_total_order)'
    return True, 'ra_lin'


def subtree_convex_holds(st):
    """subtree_convex (thm:subtreeconvex), the UNCONDITIONAL non-interleave
    guarantee, checked directly: for display-order t1 before t3 and every
    t2 strictly between them, the longest common prefix of pos(t1),pos(t3)
    also prefixes pos(t2).  (Any coord c prefixing both endpoints is a
    prefix of that LCP, so checking the LCP suffices.)  Returns
    (ok, witness_or_None)."""
    disp = st.live_ids()                  # ascending key = display order
    pos = st.shadow
    for x in range(len(disp)):
        for z in range(x + 2, len(disp)):
            t1, t3 = disp[x], disp[z]
            lcp = common_prefix(pos[t1], pos[t3])
            if not lcp:
                continue
            for y in range(x + 1, z):
                t2 = disp[y]
                if pos[t2][:len(lcp)] != lcp:
                    return False, (t1, t2, t3, lcp)
    return True, None


def converges(ops, k=4, rng=None):
    """k random causal linearizations all fold to one read (two honest
    verifiers cannot diverge on one admitted event set)."""
    rng = rng or random
    base = fold(ops).read()
    for _ in range(k):
        lin = causal_order(ops, rng)
        if lin is None or fold(ops, order=lin).read() != base:
            return False
    return True


def run_ids(anchor_id, ops):
    """The ids of the chained run rooted at anchor_id: the maximal set
    reachable by anchor links downward (a spine plus its subtree)."""
    by_id = {o['id']: o for o in ops if o['type'] == 'ins'}
    kids = {}
    for i, o in by_id.items():
        kids.setdefault(o['anchor'], []).append(i)
    out, stack = set(), [anchor_id]
    while stack:
        i = stack.pop()
        for c in kids.get(i, []):
            if c not in out:
                out.add(c)
                stack.append(c)
    return out


# ---------------------------------------------------------------- selfchecks

def selfchecks():
    out = []
    # SC1: honest typing run p a b c (each anchors the previous).  Hand:
    # p id1 root (1,); a id2 anchor1 (1,1); b id4 anchor2 (1,1,2);
    # c id6 anchor4 (1,1,2,2).  Each step passes A; derived == carried;
    # read = [p,a,b,c].
    ops, past = [], []
    steps = [(1, 'p', 0), (2, 'a', 1), (4, 'b', 2), (6, 'c', 4)]
    for i, el, a in steps:
        op = {'type': 'ins', 'id': i, 'el': el, 'anchor': a}
        ok, why, b = bless(op, past)
        assert ok, (i, why)
        ops.append(b)
        past.append(b)
    coords = {o['id']: o['coord'] for o in ops}
    assert coords == {1: (1,), 2: (1, 1), 4: (1, 1, 2), 6: (1, 1, 2, 2)}, coords
    st = fold(ops)
    assert st.read() == [(1, 'p'), (2, 'a'), (4, 'b'), (6, 'c')], st.read()
    # derived-coord recomputation matches the honest mint (b == the ship)
    for o in ops:
        pre = fold([x for x in ops if x['id'] < o['id']])
        assert o['coord'] == pre.derive(o['id'], o['anchor'])
    ok, why = ra_linearizable(ops)
    assert ok, why
    cv, _ = subtree_convex_holds(st)
    assert cv
    out.append('SC1 honest typing run: A admits every step, derived==carried, '
               'RA-lin + subtree-convex: PASS')
    # SC2: honest concurrent branching -- two runs off a root char p.
    # author1 run A2 B4 C6 under p; author2 run X3 Y5 Z7 under p.
    # p(1,); A(1,1) X(1,2) [delta 2 newer -> X before A]; runs contiguous.
    # Hand read: [p, X, Y, Z, A, B, C].
    ops2, past2 = [], []
    tree = [(1, 'p', 0), (2, 'A', 1), (3, 'X', 1), (4, 'B', 2), (5, 'Y', 3),
            (6, 'C', 4), (7, 'Z', 5)]
    for i, el, a in tree:
        op = {'type': 'ins', 'id': i, 'el': el, 'anchor': a}
        ok, why, b = bless(op, past2)
        assert ok, (i, why)
        ops2.append(b)
        past2.append(b)
    st2 = fold(ops2)
    assert [e for _, e in st2.read()] == ['p', 'X', 'Y', 'Z', 'A', 'B', 'C'], \
        st2.read()
    ok, why = ra_linearizable(ops2)
    assert ok, why
    cv, wit = subtree_convex_holds(st2)
    assert cv, wit
    out.append('SC2 concurrent branching (two runs off p): read [p,X,Y,Z,A,B,C],'
               ' both runs contiguous, RA-lin + convex: PASS')
    return out


# --------------------------------------------- directed attacks a1..a6
#
# Base document, honest, hand-derived once and reused: a typing run
#   p id1 root  (1,)      a id2 anchor1 (1,1)
#   b id4 anchor2 (1,1,2) c id6 anchor4 (1,1,2,2)   read = [p,a,b,c].

def base_doc():
    ops, past = [], []
    for i, el, a in [(1, 'p', 0), (2, 'a', 1), (4, 'b', 2), (6, 'c', 4)]:
        ok, _why, b = bless({'type': 'ins', 'id': i, 'el': el, 'anchor': a}, past)
        assert ok
        ops.append(b)
        past.append(b)
    assert [e for _, e in fold(ops).read()] == ['p', 'a', 'b', 'c']
    return ops, past


def directed_a1_forged_coord():
    """Ship ins(9,'!',anchor=1) with a coord forged to sort '!' at the END.
    Hand: honest derived from anchor p(1,) delta 9-1=8 is (1,8); key
    (-1,-8) lands '!' right after p -> [p,!,a,b,c].  Forged coord
    (1,1,2,2,1) = child of c, key (-1,-1,-2,-2,-1), lands '!' last ->
    [p,a,b,c,!].  A recomputes (1,8) != (1,1,2,2,1): REJECT forged_coord.
    FAIL companion (trust shipped coord): read flips to [p,a,b,c,!]."""
    ops, past = base_doc()
    forged = {'type': 'ins', 'id': 9, 'el': '!', 'anchor': 1,
              'coord': (1, 1, 2, 2, 1)}
    ok, why = admit(forged, past)
    assert (not ok) and why == 'forged_coord', (ok, why)
    # honest derived position (what A would have blessed)
    _, _, honest = bless({'type': 'ins', 'id': 9, 'el': '!', 'anchor': 1}, past)
    assert honest['coord'] == (1, 8)
    good = [e for _, e in fold(ops + [honest]).read()]
    assert good == ['p', '!', 'a', 'b', 'c'], good
    # FAIL companion: trust the shipped coord (drop 'derive')
    okf, whyf = admit(forged, past, checks=('phantom', 'fresh', 'live'))
    assert okf
    flipped = [e for _, e in fold(ops + [forged]).read()]
    assert flipped == ['p', 'a', 'b', 'c', '!'] and flipped != good, flipped
    return ('a1 forged coordinate: A REJECTS (forged_coord); trust-shipped '
            'FAIL flips read [p,!,a,b,c] -> [p,a,b,c,!]')


def directed_a2_phantom_anchor():
    """ins(9,'!',anchor=99) where 99 was never created.  A: 99 not in the
    reconstructed pre-state -> REJECT phantom_anchor.  FAIL companion
    (drop 'phantom' and 'derive', ship a root-ish coord): the record is
    admitted but its anchor 99 is absent -> the assembled set is NOT
    RA-linearizable (dangling coord prefix)."""
    ops, past = base_doc()
    # anchor 5 was never created (base ids are 1,2,4,6) and 5 < 9, so the
    # phantom clause -- not the a<t clause -- is what fires.
    ph = {'type': 'ins', 'id': 9, 'el': '!', 'anchor': 5, 'coord': (5,)}
    ok, why = admit(ph, past)
    assert (not ok) and why == 'phantom_anchor', (ok, why)
    # FAIL companion: accept the phantom, assemble, RA-lin must break
    okf, _ = admit(ph, past, checks=('fresh', 'live'))
    assert okf
    ra_ok, ra_why = ra_linearizable(ops + [ph])
    assert (not ra_ok) and ra_why.startswith('dangling_anchor'), ra_why
    return ('a2 phantom anchor: A REJECTS (phantom_anchor); accept-phantom '
            'FAIL yields a non-RA-linearizable state (%s)' % ra_why)


def directed_a3_stale_past():
    """Author Z declares a REAL but PARTIAL past {p,a} (down-closed, legal)
    and inserts ins(9,'!',anchor=a) having really seen more.  A checks the
    DECLARED past only: a is live there, derived (1,1,9-2)=(1,1,7).  A
    ACCEPTS.  Assembled with the full {p,a,b,c}: '!' key (-1,-1,-7) lands
    between a and b -> [p,a,!,b,c].  This EQUALS an honest slow replica
    that saw only {p,a}, inserted '!', then merged: legal CONCURRENCY, not
    a breach.  RA-lin holds; the two constructions agree."""
    ops, _full = base_doc()
    stale_past = [o for o in ops if o['id'] in (1, 2)]   # declared {p,a}
    op = {'type': 'ins', 'id': 9, 'el': '!', 'anchor': 2}
    ok, why, blessed = bless(op, stale_past)
    assert ok and blessed['coord'] == (1, 1, 7), (why, blessed)
    merged = ops + [blessed]
    read = [e for _, e in fold(merged).read()]
    assert read == ['p', 'a', '!', 'b', 'c'], read
    ra_ok, _ = ra_linearizable(merged)
    assert ra_ok and converges(merged)
    # the honest slow-replica twin: same '!' minted on {p,a}, then union
    twin = [o for o in ops if o['id'] in (1, 2)] + [blessed] + \
           [o for o in ops if o['id'] in (4, 6)]
    assert fold(twin).read() == fold(merged).read()
    return ('a3 stale-past anchor: A ACCEPTS -- legal concurrent insert '
            '[p,a,!,b,c], RA-lin, equals a slow-replica trace (it is just '
            'concurrency, NOT a breach)')


def directed_a4_run_interleave():
    """Honest run ABC after root p (p1, A2 anchor1, B3 anchor2, C4 anchor3;
    read [p,A,B,C]).  Adversary (fresh ids 5,6,7) tries the interleaved
    read [A,X,B,Y,C,Z] where X,Y,Z is its own chained run."""
    p = []
    for i, el, a in [(1, 'p', 0), (2, 'A', 1), (3, 'B', 2), (4, 'C', 3)]:
        ok, _w, b = bless({'type': 'ins', 'id': i, 'el': el, 'anchor': a}, p)
        assert ok
        p.append(b)
    honest = list(p)
    assert [e for _, e in fold(honest).read()] == ['p', 'A', 'B', 'C']
    # (i) CHAINED run anchored into A's subtree: X id5 anchor2(A), Y id6
    # anchor5(X), Z id7 anchor6(Y).  Hand coords X(1,1,3) Y(1,1,3,1)
    # Z(1,1,3,1,1); X delta3 beats B delta1, so read = [p,A,X,Y,Z,B,C]:
    # XYZ a CONTIGUOUS block inside A's subtree, NEVER woven through B,C.
    chain, past = list(honest), list(honest)
    for i, el, a in [(5, 'X', 2), (6, 'Y', 5), (7, 'Z', 6)]:
        ok, _w, b = bless({'type': 'ins', 'id': i, 'el': el, 'anchor': a}, past)
        assert ok
        chain.append(b)
        past.append(b)
    st = fold(chain)
    read = [e for _, e in st.read()]
    assert read == ['p', 'A', 'X', 'Y', 'Z', 'B', 'C'], read
    ids = st.read_ids()
    xyz_pos = sorted(ids.index(t) for t in (5, 6, 7))
    assert xyz_pos == [2, 3, 4], xyz_pos            # contiguous block
    cv, wit = subtree_convex_holds(st)
    assert cv, wit
    # (ii) SCATTER: X anchor A(2), Y anchor B(3), Z anchor C(4) -- three
    # SEPARATE single chars, NOT chained.  Each admissible (H-M boundary);
    # none is a run.  Convexity still holds.
    scatter, past = list(honest), list(honest)
    for i, el, a in [(5, 'X', 2), (6, 'Y', 3), (7, 'Z', 4)]:
        ok, _w, b = bless({'type': 'ins', 'id': i, 'el': el, 'anchor': a}, past)
        assert ok
        scatter.append(b)
        past.append(b)
    sst = fold(scatter)
    anchors = {o['id']: o['anchor'] for o in scatter if o['id'] in (5, 6, 7)}
    assert anchors == {5: 2, 6: 3, 7: 4}
    assert not ({5, 6, 7} & {anchors[5], anchors[6], anchors[7]})  # no chaining
    cv2, wit2 = subtree_convex_holds(sst)
    assert cv2, wit2
    # (iii) IMPOSSIBILITY: the interleaved read [.,A,X,B,Y,C,Z] requires X,Y,Z
    # (a chain) to be non-contiguous; convexity forbids it.  Verified: in
    # (i) the chain is contiguous; and subtree_convex holds on BOTH states,
    # so no chained run can be woven between A,B,C.
    return ('a4 run-interleave: chained XYZ -> CONTIGUOUS block [p,A,X,Y,Z,B,C] '
            '(positions 2-4), never AXBYCZ; scatter = three separate admissible '
            'chars (H-M boundary), not a run; subtree_convex holds both ways')


def directed_a5_stamp_rewind():
    """id below the declared max is rejected (Lamport).  Base max insert id
    = 6.  ins(3,...) : 3 <= 4 in the past -> REJECT stamp_rewind.  FAIL
    companion (drop 'fresh'): admit a DUPLICATE id=2 with element 'Z'; two
    verifiers that saw the two id-2 versions in opposite order DIVERGE
    (last-writer-wins on a reused id): [p,a,b,c] vs [p,Z,b,c]."""
    ops, past = base_doc()
    rewind = {'type': 'ins', 'id': 3, 'el': '!', 'anchor': 2}
    ok, why = admit(rewind, past)
    assert (not ok) and why == 'stamp_rewind', (ok, why)
    # FAIL companion: duplicate id 2 admitted with 'fresh' off
    dup = {'type': 'ins', 'id': 2, 'el': 'Z', 'anchor': 1, 'coord': (1, 1)}
    okf, _ = admit(dup, past, checks=('phantom', 'derive', 'live'))
    assert okf
    vA = ops + [dup]                 # verifier A saw the dup last
    vB = [dup] + ops                 # verifier B saw the honest 'a' last
    rA = [e for _, e in fold(vA).read()]
    rB = [e for _, e in fold(vB).read()]
    assert rA == ['p', 'Z', 'b', 'c'] and rB == ['p', 'a', 'b', 'c'], (rA, rB)
    assert rA != rB                  # divergence: convergence broken
    return ('a5 stamp rewind: A REJECTS (stamp_rewind); skip-freshness FAIL '
            'admits a duplicate id -> verifiers DIVERGE [p,Z,b,c] vs [p,a,b,c]')


def directed_a6_delete_resurrect():
    """Delete is monotone removal; no admissible op resurrects a dead id's
    ORDER slot.  Delete b (id4) via del op id7.  State [p,a,c]; c keeps
    coord (1,1,2,2), still prefixed by dead b's chain (1,1,2): the retained
    dead timestamp (the conservation law).  Attempts: re-insert id=4 ->
    REJECT stamp_rewind; fresh id=9 anchored at a gives (1,1,7) != b's slot
    (1,1,2), so the dead slot is UNREPRODUCIBLE; c's order is unchanged."""
    ops, past = base_doc()
    delop = {'type': 'del', 'id': 7, 'target': 4}
    ok, why, bd = bless(delop, past)
    assert ok, why
    after = ops + [bd]
    assert [e for _, e in fold(after).read()] == ['p', 'a', 'c']
    cpos = fold(after).shadow[6]
    assert cpos == (1, 1, 2, 2) and cpos[:3] == (1, 1, 2)   # dead b's prefix kept
    # attempt 1: re-mint id=4 -> rejected (not fresh; 4 <= 6)
    ok1, why1 = admit({'type': 'ins', 'id': 4, 'el': 'b2', 'anchor': 2},
                      after)
    assert (not ok1) and why1 == 'stamp_rewind', why1
    # attempt 2: fresh id 9 anchored at a cannot reproduce b's slot (1,1,2)
    _, _, fresh = bless({'type': 'ins', 'id': 9, 'el': 'q', 'anchor': 2}, after)
    assert fresh['coord'] == (1, 1, 7) != (1, 1, 2)
    # survivor order among the ORIGINAL survivors is preserved (sublist)
    after2 = after + [fresh]
    surv_order = [i for i in fold(after2).read_ids() if i in (1, 2, 6)]
    assert surv_order == [1, 2, 6]              # p,a,c order untouched
    return ('a6 delete resurrection: delete is monotone; re-mint id REJECTED, '
            "dead slot (1,1,2) UNREPRODUCIBLE by fresh ids, c still ranks by "
            'dead b (conservation law), survivor order preserved')


# --------------------------------------------- H-M boundary (positive demo)

def cert_selfcheck():
    """The content-address / certificate layer, exercised: a declared past
    is a set of commit cids; the pre-state is the fold of its down-closure;
    a phantom cid is unresolvable; content addressing dedups; the no-fork
    substrate assumption fires on an equivocation attempt."""
    S = Store()
    root = S.add('sys', 0, None, [])
    c1 = S.add('h', 0, {'type': 'ins', 'id': 1, 'el': 'a', 'anchor': 0}, [root])
    c2 = S.add('h', 1, {'type': 'ins', 'id': 2, 'el': 'b', 'anchor': 1}, [c1])
    # declared past {c2} down-closes to {root,c1,c2}; its ops fold to [a,b]
    dc = S.down_close({c2})
    pre = fold(S.ops_of(dc))
    assert [e for _, e in pre.read()] == ['a', 'b'], pre.read()
    # content addressing dedups: the SAME commit re-added yields the same cid
    assert S.add('h', 1, {'type': 'ins', 'id': 2, 'el': 'b', 'anchor': 1},
                 [c1]) == c2
    # a phantom past (a cid nobody produced) is unresolvable
    assert S.resolvable({c2}) and not S.resolvable({'deadbeefdeadbeef'})
    # no-fork: two DIFFERENT ops at the same (author, seq) is rejected
    forked = False
    try:
        S.add('h', 1, {'type': 'ins', 'id': 99, 'el': 'X', 'anchor': 1}, [c1])
    except AssertionError:
        forked = True
    assert forked, 'no-fork substrate assumption did not fire'
    return ('cert layer: declared past = cid set, pre = fold of down-closure '
            '[a,b]; phantom cid unresolvable; content-address dedups; no-fork '
            'assumption fires on equivocation')


def hm_boundary_demo():
    """The HONEST NON-CLAIM, shown positively: a Byzantine author CAN
    (1) insert a single char at any legally anchored position, and
    (2) delete any live id.  Both pass A and are NOT breaches -- they are
    authoring / moderation.  Base [p,a,b,c]; adversary inserts a char after
    b and deletes a; the results are admissible, RA-lin, convex."""
    ops, past = base_doc()
    # (1) a legal single-char insert after b (id4), by the adversary
    _, _, ins = bless({'type': 'ins', 'id': 9, 'el': '*', 'anchor': 4}, past)
    s1 = ops + [ins]
    assert ra_linearizable(s1)[0] and subtree_convex_holds(fold(s1))[0]
    r1 = [e for _, e in fold(s1).read()]
    assert '*' in r1 and r1.index('*') == r1.index('b') + 1        # after b
    # (2) a legal delete of a live id (a, id2), by the adversary
    _, _, dl = bless({'type': 'del', 'id': 11, 'target': 2}, past)
    s2 = ops + [dl]
    assert ra_linearizable(s2)[0] and subtree_convex_holds(fold(s2))[0]
    assert [e for _, e in fold(s2).read()] == ['p', 'b', 'c']
    return ('H-M boundary: adversary CAN insert one legal char (after b) and '
            'delete any live id (a) -- both admitted, RA-lin, convex; these '
            'are authoring/moderation, NOT breaches')


# ----------------------------------------------------- adversary search
#
# ids are author-tagged and globally unique BY THE SUBSTRATE (id = clock*10
# + author, clock a global monotone counter, author < 10): a signed
# single-writer chain cannot forge another author's id nor fork its own.
# That is the IMPORTED no-equivocation assumption, not defended here.
# Admission still enforces intra-author Lamport monotonicity (a stamp below
# the declared past's max is rejected).  One replica is Byzantine and fires
# the a1..a6 attack menu; every op is put through A against a DECLARED past
# (for the stale-past attack, a strict down-closed subset of what it heard).

CLASSES = ('honest_ins', 'honest_del', 'stale_past', 'chain', 'scatter',
           'boundary', 'forged_coord', 'phantom', 'stamp_rewind',
           'del_resurrect')


def _down_closed_subset(heard, rng):
    """A random down-closed strict subset of heard (by deps): drop a random
    op and everything depending on it."""
    ids = [o['id'] for o in heard]
    if len(ids) < 2:
        return list(heard)
    drop = {rng.choice(ids)}
    changed = True
    while changed:
        changed = False
        for o in heard:
            if o['id'] not in drop and (o['deps'] & drop):
                drop.add(o['id'])
                changed = True
    sub = [o for o in heard if o['id'] not in drop]
    return sub


def adversary_trial(seed, counts, countermodels):
    rng = random.Random(seed)
    n_rep = rng.randrange(2, 5)
    byz = rng.randrange(n_rep)
    clock = [0]
    heard = [[] for _ in range(n_rep)]      # per-author possessed ops
    pool = []
    pool_ids = set()

    def new_id(author):
        clock[0] += 1
        return clock[0] * 10 + author

    def add(op):
        if op['id'] not in pool_ids:
            pool.append(op)
            pool_ids.add(op['id'])

    def deps_of(past_ops):
        return frozenset(o['id'] for o in past_ops)

    def deliver(r):
        cand = [o for o in pool
                if o['id'] not in {x['id'] for x in heard[r]}
                and o['deps'] <= {x['id'] for x in heard[r]}]
        if cand:
            heard[r].append(rng.choice(cand))

    def honest_mint(r):
        st = fold(heard[r])
        live = st.read_ids()
        if live and rng.random() < 0.3:
            op = {'type': 'del', 'id': new_id(r), 'target': rng.choice(live)}
        else:
            # chain-bias: sometimes anchor at this author's last live insert
            mine = [i for i in live
                    if any(o['id'] == i and o['type'] == 'ins'
                           and o.get('author') == r for o in heard[r])]
            if mine and rng.random() < 0.5:
                a = mine[-1]
            else:
                a = rng.choice([0] + live)
            op = {'type': 'ins', 'id': new_id(r), 'el': 'h%d' % clock[0],
                  'anchor': a}
        ok, why, b = bless(op, heard[r])
        if not ok:
            return  # honest ops must be admissible; a miss is silently skipped
        b['author'] = r
        b['deps'] = deps_of(heard[r])
        heard[r].append(b)
        add(b)
        cls = 'honest_del' if op['type'] == 'del' else 'honest_ins'
        counts[cls]['admit'] += 1

    def byz_attack(r):
        st = fold(heard[r])
        live = st.read_ids()
        if not live:
            return
        attack = rng.choice(['stale_past', 'chain', 'scatter', 'boundary',
                             'forged_coord', 'phantom', 'stamp_rewind',
                             'del_resurrect'])
        if attack == 'stale_past':
            sub = _down_closed_subset(heard[r], rng)
            sst = fold(sub)
            slive = sst.read_ids()
            if not slive:
                return
            a = rng.choice(slive)
            op = {'type': 'ins', 'id': new_id(r), 'el': 'z%d' % clock[0],
                  'anchor': a}
            _record(op, sub, r, 'stale_past', counts, countermodels, pool,
                    pool_ids, heard, deps_of)
        elif attack == 'chain':
            a = rng.choice(live)
            prev = a
            for _ in range(rng.randrange(2, 4)):
                op = {'type': 'ins', 'id': new_id(r), 'el': 'c%d' % clock[0],
                      'anchor': prev}
                prev2 = _record(op, heard[r], r, 'chain', counts,
                                countermodels, pool, pool_ids, heard, deps_of)
                if prev2 is None:
                    break
                prev = op['id']
        elif attack == 'scatter':
            for a in rng.sample(live, min(len(live), rng.randrange(1, 4))):
                op = {'type': 'ins', 'id': new_id(r), 'el': 's%d' % clock[0],
                      'anchor': a}
                _record(op, heard[r], r, 'scatter', counts, countermodels,
                        pool, pool_ids, heard, deps_of)
        elif attack == 'boundary':
            if rng.random() < 0.5:
                op = {'type': 'ins', 'id': new_id(r), 'el': 'b%d' % clock[0],
                      'anchor': rng.choice([0] + live)}
            else:
                op = {'type': 'del', 'id': new_id(r), 'target': rng.choice(live)}
            _record(op, heard[r], r, 'boundary', counts, countermodels, pool,
                    pool_ids, heard, deps_of)
        elif attack == 'forged_coord':
            a = rng.choice(live)
            nid = new_id(r)
            derived = st.derive(nid, a)
            forged = derived[:-1] + (derived[-1] + 500,)   # wrong last delta
            op = {'type': 'ins', 'id': nid, 'el': 'f', 'anchor': a,
                  'coord': forged}
            _record(op, heard[r], r, 'forged_coord', counts, countermodels,
                    pool, pool_ids, heard, deps_of, expect_reject=True)
        elif attack == 'phantom':
            ghost = max([o['id'] for o in heard[r]] + [0]) + 1  # unheard id
            op = {'type': 'ins', 'id': new_id(r), 'el': 'p', 'anchor': ghost}
            _record(op, heard[r], r, 'phantom', counts, countermodels, pool,
                    pool_ids, heard, deps_of, expect_reject=True)
        elif attack == 'stamp_rewind':
            mx = max(o['id'] for o in heard[r] if o['type'] == 'ins') \
                if any(o['type'] == 'ins' for o in heard[r]) else 0
            low = max(1, mx - rng.randrange(1, 5))          # a stamp <= max
            a = rng.choice(live)
            op = {'type': 'ins', 'id': low, 'el': 'r', 'anchor': a}
            _record(op, heard[r], r, 'stamp_rewind', counts, countermodels,
                    pool, pool_ids, heard, deps_of, expect_reject=True)
        elif attack == 'del_resurrect':
            # delete a live id, then try to re-mint at the dead slot (forged)
            tgt = rng.choice(live)
            dead_c = st.shadow[tgt]
            dop = {'type': 'del', 'id': new_id(r), 'target': tgt}
            _record(dop, heard[r], r, 'boundary', counts, countermodels, pool,
                    pool_ids, heard, deps_of)
            a = st.anchor.get(tgt, 0)
            op = {'type': 'ins', 'id': new_id(r), 'el': 'R', 'anchor': a,
                  'coord': dead_c}
            _record(op, heard[r], r, 'del_resurrect', counts, countermodels,
                    pool, pool_ids, heard, deps_of, expect_reject=True)

    # main loop
    for _ in range(rng.randrange(30, 70)):
        r = rng.randrange(n_rep)
        if rng.random() < 0.35:
            deliver(r)
        elif r == byz:
            byz_attack(r)
        else:
            honest_mint(r)

    # final invariant checks on the assembled admitted pool
    if not pool:
        return
    st = fold(pool)
    if not converges(pool, rng=rng):
        countermodels.append(('divergence', seed, len(pool)))
    ok, why = ra_linearizable(pool, rng=rng)
    if not ok:
        countermodels.append(('non_ra_lin:%s' % why, seed, len(pool)))
    cv, wit = subtree_convex_holds(st)
    if not cv:
        countermodels.append(('interleave:%r' % (wit,), seed, len(pool)))


def _record(op, past, r, cls, counts, countermodels, pool, pool_ids, heard,
            deps_of, expect_reject=False):
    """Put one attack op through A against its DECLARED `past`.  On admit:
    bless (coord forced to derived), tag author+deps, add to the pool and
    the author's heard.  Counts admit/reject by class.  An expect_reject
    attack that is ADMITTED is flagged (a soundness gap in A) -- though the
    blessed op carries the DERIVED coord, so it is still harmless."""
    ok, why, b = bless(op, past)
    if ok:
        b['author'] = r
        b['deps'] = deps_of(past)
        if b['id'] not in pool_ids:
            pool.append(b)
            pool_ids.add(b['id'])
        heard[r].append(b)
        counts[cls]['admit'] += 1
        if expect_reject:
            countermodels.append(('unexpected_admit:%s' % cls, why))
        return b['id']
    counts[cls]['reject'] += 1
    counts[cls].setdefault('why', {})
    counts[cls]['why'][why] = counts[cls]['why'].get(why, 0) + 1
    return None


def unconditional_convexity_probe(seed):
    """H-I unconditionality: subtree_convex holds on a state carrying a
    REJECTED (non-admitted) op forcibly applied -- so convexity is a
    property of the coordinate GEOMETRY, not of admission.  Build an honest
    doc, force in a forged-coord record (A would reject it), and check
    convexity still holds."""
    rng = random.Random(seed)
    ops, past = base_doc()
    st = fold(ops)
    live = st.read_ids()
    a = rng.choice(live)
    # a coordinate that is a legal child of a but was NEVER admitted
    forced = {'type': 'ins', 'id': 999, 'el': '?', 'anchor': a,
              'coord': st.shadow[a] + (rng.randrange(1, 9),)}
    st2 = fold(ops + [forced])
    cv, _ = subtree_convex_holds(st2)
    return cv


def run_search(n_trials, seed0=0):
    counts = {c: {'admit': 0, 'reject': 0} for c in CLASSES}
    countermodels = []
    for s in range(seed0, seed0 + n_trials):
        adversary_trial(s, counts, countermodels)
    # unconditional convexity on rejected-op states
    uncond = all(unconditional_convexity_probe(s) for s in range(200))
    return counts, countermodels, uncond


# ------------------------------------------------------------------ main

if __name__ == '__main__':
    print('==== self-certifying embed RGA: Byzantine admission check (#116) ====')
    print('-- selfchecks --')
    for line in selfchecks():
        print('  ' + line)
    print('  ' + cert_selfcheck())
    print('  ' + hm_boundary_demo())
    print('-- directed attacks a1..a6 (hand-derived expectations) --')
    for fn in (directed_a1_forged_coord, directed_a2_phantom_anchor,
               directed_a3_stale_past, directed_a4_run_interleave,
               directed_a5_stamp_rewind, directed_a6_delete_resurrect):
        print('  ' + fn())
    print('-- adversary search (2-4 replicas, one Byzantine) --')
    N = 3500
    counts, countermodels, uncond = run_search(N)
    tot_admit = sum(c['admit'] for c in counts.values())
    tot_reject = sum(c['reject'] for c in counts.values())
    print('  trials: %d; admitted ops: %d; rejected ops: %d' %
          (N, tot_admit, tot_reject))
    print('  by class                 admitted   rejected  (reject reasons)')
    for c in CLASSES:
        why = counts[c].get('why', {})
        wtxt = ', '.join('%s=%d' % (k, v) for k, v in sorted(why.items()))
        print('    %-16s %8d %10d   %s' %
              (c, counts[c]['admit'], counts[c]['reject'], wtxt))
    print('  admitted-yet-broken countermodels: %d' % len(countermodels))
    for cm in countermodels[:8]:
        print('    COUNTERMODEL:', cm)
    print('  subtree_convex on rejected-op states (unconditionality): %s' %
          ('PASS' if uncond else 'FAIL'))
    print('==== VERDICT ====')
    hc = not any(cm[0].startswith(('divergence', 'non_ra_lin', 'unexpected'))
                 for cm in countermodels)
    hi = not any(cm[0].startswith('interleave') for cm in countermodels) \
        and uncond
    print('  H-C convergence / RA-lin under admission : %s' %
          ('VALIDATED (no admitted trace diverges or breaks RA-lin)'
           if hc else 'REFUTED'))
    print('  H-I structural intent (subtree convex)   : %s' %
          ('VALIDATED, UNCONDITIONAL (holds even on rejected-op states)'
           if hi else 'REFUTED'))
    print('  H-M boundary (authoring / moderation)    : demonstrated positive')
    print('  admission soundness (a1,a2,a5,a6 reject) : forged/phantom/rewind/'
          'resurrect all REJECTED by A')
    ok = hc and hi and not countermodels
    sys.exit(0 if ok else 1)
