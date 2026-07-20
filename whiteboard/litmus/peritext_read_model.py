#!/usr/bin/env python3
"""
peritext_read_model -- task #55 DESIGN+VALIDATION (Python + pen-and-paper).

A DOCUMENT-ORDER Peritext mark-positioning read model, built on top of the
embed-RGA document order (embed_tree.EmbedTree, reused unchanged), plus the
WRONG frozen-path/tree-ancestry resolver as a labelled control so the
retracted "formatting does not leak" claim is exhibitable as a concrete leak.

Background (the retraction this file makes concrete).
  Sal/ConditionedMRDTs/MRDT_Instances/Peritext_Composed/MarkIntent.lean once
  carried a `mark_*_no_leak` theorem asserting the frozen-path read never
  leaks formatting.  It is FALSE: frozen-path resolution climbs the recorded
  TREE ancestry, and a tree ancestor sits EARLIER in reading order than its
  descendants (a parent precedes its children in the DFS).  So when a boundary
  anchor is deleted the boundary migrates BACKWARD in the document, formatting
  text that was never in the span.  The honest replacement is a containment
  bound (mark_*_within_recorded_ancestry).  This file builds the paper-faithful
  DOCUMENT-ORDER read (boundary -> nearest surviving neighbour in READING
  order, gravity-aware via startSide/endSide) and shows the leak side by side.

The two resolvers (both take the SAME immutable mark record):
  * DocumentOrderResolver  -- paper-faithful.  A dead boundary anchor rehomes
    to the nearest SURVIVING neighbour in reading order, on the side dictated
    by the anchor's gravity.  startSide/endSide additionally give the
    expand/no-expand behaviour for text typed AT a boundary.
  * TreeAncestryResolver   -- the retracted frozen-path control.  A dead
    boundary anchor climbs its recorded RGA ancestor path to the nearest live
    ancestor (tree ancestry), which drags the boundary backward.

Run:   python3 peritext_read_model.py            # examples + gravity + PBT
       python3 peritext_read_model.py -v          # verbose traces
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Optional
import embed_tree as ET


# =========================================================================
# The document layer: reading-order characters over the embed-RGA order.
#
# The embed model's key property (P3, embed_tree.py): a live read after
# deletes EQUALS the immutable birth order filtered to survivors.  So we keep
# ONE no-delete "shadow" embed state as the immutable birth order + birth
# parents, and a separate `deleted` set.  live_order() = birth order minus
# deleted -- verified against the real embed delete+refold in _selfcheck().
# =========================================================================
class Doc:
    def __init__(self):
        self.E = ET.EmbedTree()
        self.shadow = self.E.init()      # all inserts, never deleted (birth order)
        self.deleted: set[int] = set()
        self.codept: dict[int, str] = {}

    def copy(self) -> "Doc":
        d = Doc()
        d.shadow = self.E.copy(self.shadow)
        d.deleted = set(self.deleted)
        d.codept = dict(self.codept)
        return d

    def ins(self, cid: int, cp: str, anchor: int):
        """Insert character `cid` (codepoint `cp`) after live char `anchor`
        (0 = document start)."""
        self.shadow = self.E.apply(self.shadow, ('ins', cid, anchor))
        self.codept[cid] = cp

    def delete(self, cid: int):
        self.deleted.add(cid)

    def birth_order(self) -> list[int]:
        return self.E.read(self.shadow)

    def live_order(self) -> list[int]:
        return [c for c in self.birth_order() if c not in self.deleted]

    def live(self, cid: int) -> bool:
        return cid in self.shadow and cid not in self.deleted

    def birth_parent(self, cid: int) -> int:
        return self.shadow[cid][0] if cid in self.shadow else 0

    def birth_path(self, cid: int) -> list[int]:
        """The recorded frozen path: anchor, its birth parent, ... , root 0.
        This is what the retracted frozen-path design stores at mark issue."""
        path, cur, guard = [], cid, 0
        while cur != 0:
            path.append(cur)
            cur = self.birth_parent(cur)
            guard += 1
            if guard > 100000:
                raise RuntimeError('cycle in birth path')
        path.append(0)
        return path


# =========================================================================
# The mark record (immutable data carried by the mark op).
# =========================================================================
@dataclass(frozen=True)
class Mark:
    mid: int                 # mark instance id (also its creation opId / timestamp)
    mtype: str               # 'bold', 'italic', 'link', 'comment', ...
    value: Optional[str]     # e.g. a link target or a comment body; None for bold
    op: str = 'add'          # 'add' | 'remove' (removeMark); LWW by mid per (char,mtype)
    start_id: int = 0        # start boundary anchor character id
    end_id: int = 0          # end   boundary anchor character id
    startSide: str = 'before'  # 'before' (inner, expands left) | 'after' (outer)
    endSide: str = 'after'     # 'after'  (inner, expands right) | 'before' (outer)
    start_path: tuple = ()   # frozen recorded ancestry of start_id (control only)
    end_path: tuple = ()     # frozen recorded ancestry of end_id   (control only)


def make_mark(doc: Doc, mid, mtype, value, start_id, end_id,
              startSide='before', endSide='after', op='add') -> Mark:
    """Build a mark, snapshotting the frozen ancestry paths (for the control)."""
    return Mark(mid, mtype, value, op, start_id, end_id, startSide, endSide,
                tuple(doc.birth_path(start_id)), tuple(doc.birth_path(end_id)))


# =========================================================================
# Resolver 1: DOCUMENT-ORDER (paper-faithful).
#
# A boundary resolves to a position in the CURRENT live reading order.  If the
# anchor is dead, it rehomes to the nearest SURVIVING neighbour in reading
# order on the gravity side.  startSide/endSide additionally give the
# expand/no-expand behaviour for text typed AT a live boundary:
#
#   start 'before' (inner, first span char): boundary at anchor's left edge;
#                  expands LEFT over newer-than-mark chars (bold grows left).
#   start 'after'  (outer, char before span): boundary at anchor's right edge;
#                  does NOT expand (link/no-grow start).
#   end   'after'  (inner, last span char):  boundary at anchor's right edge;
#                  expands RIGHT over newer-than-mark chars (bold grows right).
#   end   'before' (outer, char after span): boundary at anchor's left edge;
#                  does NOT expand (link/no-grow end).
#
# "newer than mark" = char id > mark.mid (ids are Lamport timestamps); this is
# the RGA opId tiebreak, so concurrent inserts resolve deterministically.
# =========================================================================
class DocumentOrderResolver:
    name = 'document-order'

    @staticmethod
    def _scan(birth, deleted, start_bidx, step):
        """Nearest live char scanning from birth index start_bidx by +/-step."""
        j = start_bidx + step
        while 0 <= j < len(birth):
            if birth[j] not in deleted:
                return birth[j]
            j += step
        return None

    def _start_index(self, doc, mark, live, pos, birth, bpos, n):
        a, side = mark.start_id, mark.startSide
        if not doc.live(a):
            # rehome: inner-before scans RIGHT (into span); outer-after scans LEFT
            a = self._scan(birth, doc.deleted, bpos[a], +1 if side == 'before' else -1)
            if a is None:
                return None if side == 'before' else 0   # collapse-right | doc start
        i = pos[a]
        if side == 'before':
            # inner start: stable, includes exactly from the anchor char.  A
            # 'before' start does NOT grow left (text typed before the first
            # styled char is not retroactively formatted -- paper-faithful, and
            # avoids grabbing unrelated newer siblings that merely read to the
            # left).  Growth is an END-side (endSide=after) phenomenon.
            first = i
        else:  # 'after' (outer, char before span): skip the newer run typed
            # right after the anchor -- a non-growing (link) start.
            first = i + 1
            while first < n and live[first] > mark.mid:
                first += 1
        return first

    def _end_index(self, doc, mark, live, pos, birth, bpos, n):
        a, side = mark.end_id, mark.endSide
        if not doc.live(a):
            # rehome: inner-after scans LEFT (into span); outer-before scans RIGHT
            a = self._scan(birth, doc.deleted, bpos[a], -1 if side == 'after' else +1)
            if a is None:
                return None if side == 'after' else n - 1  # collapse-left | doc end
        i = pos[a]
        if side == 'after':
            last = i
            while last + 1 < n and live[last + 1] > mark.mid:
                last += 1
        else:  # 'before' (outer)
            last = i - 1
            while last >= 0 and live[last] > mark.mid:
                last -= 1
        return last

    def covered(self, doc, mark):
        live = doc.live_order()
        birth = doc.birth_order()
        pos = {c: i for i, c in enumerate(live)}
        bpos = {c: i for i, c in enumerate(birth)}
        n = len(live)
        first = self._start_index(doc, mark, live, pos, birth, bpos, n)
        last = self._end_index(doc, mark, live, pos, birth, bpos, n)
        if first is None or last is None or first > last:
            return []
        return live[first:last + 1]


# =========================================================================
# Resolver 2: TREE-ANCESTRY / FROZEN-PATH (the retracted control).
#
# Each boundary carries a FROZEN recorded RGA ancestor path (anchor, parent,
# ..., root).  Resolution climbs that path to the nearest live ancestor.  A
# tree ancestor sits EARLIER in reading order (a parent precedes its children
# in the DFS), so a dead anchor drags the boundary BACKWARD -- the leak.  Side
# bits are ignored (the retracted design had no positional gravity); coverage
# is the plain inclusive interval between the two resolved anchors.
# =========================================================================
class TreeAncestryResolver:
    name = 'tree-ancestry (frozen-path, RETRACTED)'

    @staticmethod
    def _resolve(doc, path):
        for c in path:
            if c == 0:
                return 0
            if doc.live(c):
                return c
        return 0

    def covered(self, doc, mark):
        live = doc.live_order()
        pos = {c: i for i, c in enumerate(live)}
        n = len(live)
        rs = self._resolve(doc, mark.start_path)
        re = self._resolve(doc, mark.end_path)
        first = 0 if rs == 0 else pos[rs]
        last = n - 1 if re == 0 else pos[re]
        if n == 0 or first > last:
            return []
        return live[first:last + 1]


# =========================================================================
# Render: per live char -> active mark set, and a single-type boolean view.
# =========================================================================
def render(doc, marks, resolver):
    """Per live char -> set of active (mtype, value).  For each (char, mtype),
    the covering mark with the highest mid wins (LWW, paper §4.4); an 'add'
    formats, a 'remove' does not."""
    live = doc.live_order()
    best = {c: {} for c in live}   # c -> mtype -> (mid, op, value)
    for m in marks:
        for c in resolver.covered(doc, m):
            cur = best[c].get(m.mtype)
            if cur is None or m.mid > cur[0]:
                best[c][m.mtype] = (m.mid, m.op, m.value)
    out = []
    for c in live:
        active = {(mt, val) for mt, (_mid, op, val) in best[c].items() if op == 'add'}
        out.append((c, doc.codept[c], active))
    return out


def render_flags(doc, marks, resolver, mtype):
    """[(codepoint, is-of-type)] in reading order -- the paper's rendered view."""
    return [(cp, any(t == mtype for (t, _v) in s)) for (_c, cp, s) in render(doc, marks, resolver)]


# =========================================================================
# Validation harness: the Litt et al. examples, gravity, the leak, the
# trilemma.  Every PASS carries a hand-derived expected value; leak examples
# carry a FAIL companion pinning the retracted claim's error concretely.
# =========================================================================
DR = DocumentOrderResolver()
TR = TreeAncestryResolver()


def build(recs):
    d = Doc()
    for (i, cp, a) in recs:
        d.ins(i, cp, a)
    return d


def bview(d, marks, res, mt):
    return render_flags(d, marks, res, mt)


def _selfcheck():
    """P3: the shadow (birth order minus deleted) equals the real embed
    delete+refold read.  If this fails the document layer is unfaithful."""
    E = ET.EmbedTree()
    cases = [
        ([(1, 0), (2, 1), (3, 2), (4, 3)], [2]),
        ([(1, 0), (2, 1), (3, 1), (4, 2), (5, 0)], [2, 4]),
        ([(1, 0), (2, 0), (3, 0), (4, 2), (5, 4)], [2]),
    ]
    for recs, dels in cases:
        d = Doc()
        s = E.init()
        for (i, a) in recs:
            d.ins(i, chr(64 + i), a)
            s = E.apply(s, ('ins', i, a))
        for x in dels:
            d.delete(x)
            s = E.apply(s, ('del', x))
        if d.live_order() != E.read(s):
            return False, f'P3 MISMATCH recs={recs} dels={dels}: {d.live_order()} vs {E.read(s)}'
    return True, 'P3 holds on 3 delete+refold cases'


# ---- Litt et al. examples (subset tracked in docs/peritext-vs-paper.md) ----

def ex1_insert_within_span():
    """Ex 1 (§3.1): insertion WITHIN a bold span is formatted.  a,c bold;
    insert b between them -> b bold.  Both resolvers agree (no deletion)."""
    d = build([(1, 'a', 0), (2, 'c', 1)])
    m = make_mark(d, 3, 'bold', None, 1, 2, 'before', 'after')
    d.ins(4, 'b', 1)                       # b typed after a, inside [a,c]
    got = bview(d, [m], DR, 'bold')
    exp = [('a', True), ('b', True), ('c', True)]
    neg = got != [('a', True), ('b', False), ('c', True)]   # b NOT left plain
    return 'Ex1 insert-within-span', got == exp and neg, f'{got}'


def ex2_overlapping_bold_italic():
    """Ex 2 (§3.2): overlapping marks of different type coexist; the overlap
    carries both.  bold[a,c], italic[b,d]."""
    d = build([(1, 'a', 0), (2, 'b', 1), (3, 'c', 2), (4, 'd', 3)])
    bd = make_mark(d, 10, 'bold', None, 1, 3, 'before', 'after')
    it = make_mark(d, 11, 'italic', None, 2, 4, 'before', 'after')
    r = render(d, [bd, it], DR)
    got = [(cp, sorted(t for t, _ in s)) for (_c, cp, s) in r]
    exp = [('a', ['bold']), ('b', ['bold', 'italic']),
           ('c', ['bold', 'italic']), ('d', ['italic'])]
    return 'Ex2 overlapping bold+italic', got == exp, f'{got}'


def ex3_delete_span_then_reinsert():
    """Ex 3 (task): mark a span, delete the WHOLE span, reinsert text.  The
    reinserted text must NOT be formatted.  DOC-ORDER: clean (span collapses).
    TREE-ANCESTRY: LEAKS -- both boundaries climb to the dead root, so the
    span becomes the whole document and formats the brand-new text."""
    d = build([(1, 'a', 0), (2, 'b', 1), (3, 'c', 2)])
    m = make_mark(d, 10, 'bold', None, 1, 3, 'before', 'after')
    for x in (1, 2, 3):
        d.delete(x)
    d.ins(4, 'd', 0)                       # reinsert fresh text
    doc = bview(d, [m], DR, 'bold')
    tree = bview(d, [m], TR, 'bold')
    ok = doc == [('d', False)]             # doc-order: fresh text plain
    leaks = tree == [('d', True)]          # control: leaks bold onto fresh text
    return 'Ex3 delete-span-then-reinsert', ok and leaks, \
        f'doc={doc} (PASS) tree={tree} (LEAK={leaks})'


def ex5_concurrent_add_vs_remove():
    """Ex 5 (§3.2.1): concurrent bold add vs removeMark, resolved LWW by mid.
    Higher mid wins per (char, type)."""
    d = build([(1, 'a', 0), (2, 'b', 1)])
    add_lo = make_mark(d, 10, 'bold', None, 1, 2, 'before', 'after', op='add')
    rem_hi = make_mark(d, 20, 'bold', None, 1, 2, 'before', 'after', op='remove')
    add_hi = make_mark(d, 20, 'bold', None, 1, 2, 'before', 'after', op='add')
    rem_lo = make_mark(d, 10, 'bold', None, 1, 2, 'before', 'after', op='remove')
    remove_wins = bview(d, [add_lo, rem_hi], DR, 'bold')   # -> plain
    add_wins = bview(d, [add_hi, rem_lo], DR, 'bold')      # -> bold
    ok = (remove_wins == [('a', False), ('b', False)] and
          add_wins == [('a', True), ('b', True)])
    return 'Ex5 concurrent add-vs-remove (LWW)', ok, \
        f'remove-wins={remove_wins} add-wins={add_wins}'


def ex7_bold_boundary_expands():
    """Ex 7 (§3.3): typing at the end of a bold span extends it (endSide=after).
    Also: a concurrent insert OLDER than the mark is NOT grabbed (mark wins)."""
    d = build([(1, 'a', 0), (2, 'b', 1)])
    m = make_mark(d, 3, 'bold', None, 1, 2, 'before', 'after')
    d.ins(4, 'x', 2)                       # typed after b, newer than mark
    expand = bview(d, [m], DR, 'bold')
    # older-than-mark concurrent insert at the same boundary: not grabbed
    d2 = build([(1, 'a', 0), (2, 'b', 1)])
    m2 = make_mark(d2, 9, 'bold', None, 1, 2, 'before', 'after')  # mark newer
    d2.ins(4, 'x', 2)                      # x id 4 < mark 9 -> concurrent-loser
    noexp = bview(d2, [m2], DR, 'bold')
    ok = (expand == [('a', True), ('b', True), ('x', True)] and
          noexp == [('a', True), ('b', True), ('x', False)])
    return 'Ex7 bold boundary expands', ok, f'expand={expand} older-insert={noexp}'


def ex8_link_boundary_no_expand():
    """Ex 8 (§3.3): typing after a link does NOT extend it (endSide=before,
    anchored to the char after the link).  Bold on the SAME insertion DOES
    extend -- the directed gravity contrast."""
    d = build([(1, 'a', 0), (2, 'b', 1), (3, 'z', 2)])
    ln = make_mark(d, 4, 'link', 'http://x', 1, 3, 'before', 'before')
    bd = make_mark(d, 4, 'bold', None, 1, 2, 'before', 'after')
    d.ins(5, 'x', 2)                       # typed after b (last styled char)
    link = bview(d, [ln], DR, 'link')
    bold = bview(d, [bd], DR, 'bold')
    ok = (link == [('a', True), ('b', True), ('x', False), ('z', False)] and
          bold == [('a', True), ('b', True), ('x', True), ('z', False)])
    return 'Ex8 link no-expand vs bold expand', ok, f'link={link} bold={bold}'


# ---- The retracted-claim leak, made concrete (deletion of a boundary anchor) ----

def leak_delete_start_anchor():
    """PRIMARY LEAK.  Chain W,A,B,C; bold spans [A,B]; delete the start anchor
    A.  DOC-ORDER rehomes the start to the nearest surviving neighbour (B) ->
    bold={B}, W stays plain.  TREE-ANCESTRY climbs A's path to its parent W
    (earlier in reading order) -> bold={W,B}: W is formatted though it was never
    in the span.  This is the retracted mark_*_no_leak error, concretely."""
    d = build([(1, 'W', 0), (2, 'A', 1), (3, 'B', 2), (4, 'C', 3)])
    m = make_mark(d, 100, 'bold', None, 2, 3, 'before', 'after')  # mid high: no expand
    d.delete(2)
    doc = bview(d, [m], DR, 'bold')
    tree = bview(d, [m], TR, 'bold')
    ok = doc == [('W', False), ('B', True), ('C', False)]
    leaks = tree == [('W', True), ('B', True), ('C', False)]
    return 'LEAK delete-start-anchor', ok and leaks, \
        f'doc={doc} (no leak) tree={tree} (LEAK backward onto W={leaks})'


def leak_skip_surviving_sibling():
    """LEAK, skip-sibling variant.  W has children Q (plain sibling) and A;
    A has child B; bold spans [A,B].  Reading order W,Q,A,B.  Delete A.
    TREE-ANCESTRY climbs A->W, so the span becomes [W..B] and formats BOTH W
    and the surviving sibling Q -- the climb skips Q entirely.  DOC-ORDER
    rehomes to B (nearest survivor), leaving W and Q plain."""
    d = Doc()
    d.ins(1, 'W', 0)
    d.ins(2, 'A', 1)
    d.ins(3, 'B', 2)
    d.ins(4, 'Q', 1)                      # sibling of A under W, newer -> reads before A
    m = make_mark(d, 100, 'bold', None, 2, 3, 'before', 'after')
    d.delete(2)
    doc = bview(d, [m], DR, 'bold')
    tree = bview(d, [m], TR, 'bold')
    ok = doc == [('W', False), ('Q', False), ('B', True)]
    leaks = tree == [('W', True), ('Q', True), ('B', True)]
    return 'LEAK skip-surviving-sibling', ok and leaks, \
        f'doc={doc} tree={tree} (W,Q leaked={leaks})'


def trilemma_atomicity_respan():
    """THE TRILEMMA COST (observable, single replica).  bold spans [A,B]; C
    (older than the mark) sits after B and BLOCKS expansion; D (newer, child of
    C) is plain.  Delete the plain C: D becomes contiguous with B and the
    endSide=after expansion GRABS it -- D is re-formatted though the delete
    touched neither D nor any boundary.  This is the tombstone-free price of a
    live document-order read (cf. fused_delete_moves_char_into_span); a
    tombstone would keep C between B and D and break the run (the paper keeps D
    plain).  Not a leak of the retracted kind (no backward migration): a
    membership re-span from losing the deleted char's separating position."""
    d = build([(1, 'A', 0), (2, 'B', 1), (3, 'C', 2)])
    m = make_mark(d, 4, 'bold', None, 1, 2, 'before', 'after')   # mid 4 > C(3), < D(5)
    d.ins(5, 'D', 3)
    before = bview(d, [m], DR, 'bold')
    d.delete(3)
    after = bview(d, [m], DR, 'bold')
    naive_expected = [('A', True), ('B', True), ('D', False)]     # paper (tombstone) keeps D plain
    respanned = after == [('A', True), ('B', True), ('D', True)]
    diverges = after != naive_expected
    return 'TRILEMMA atomicity re-span', respanned and diverges, \
        f'before={before} after-del-C={after} (D re-spanned={respanned}, != paper-atomic={diverges})'


def gravity_start_side():
    """startSide contrast.  A 'before' (inner) start is STABLE: text typed
    right before the first styled char is NOT retroactively formatted (growth
    is an END-side phenomenon; and this avoids grabbing an unrelated newer
    sibling that merely reads to the left).  An 'after' (outer) start likewise
    skips the newer run typed right after its anchor.  Insert y between W and
    the first styled char A."""
    d = build([(1, 'W', 0), (2, 'A', 1), (3, 'B', 2)])
    bd = make_mark(d, 3, 'bold', None, 2, 3, 'before', 'after')   # inner start at A
    ln = make_mark(d, 3, 'link', 'u', 1, 3, 'after', 'before')    # outer start at W, outer end at B
    d.ins(4, 'y', 1)                      # y typed between W and A, newer than marks
    bold = bview(d, [bd], DR, 'bold')
    link = bview(d, [ln], DR, 'link')
    # bold start=(A,before) stable: y NOT grabbed -> bold covers A,B only
    ok_bold = bold == [('W', False), ('y', False), ('A', True), ('B', True)]
    # link start=(W,after) skips y; end=(B,before) excludes B -> link covers only A
    ok_link = link == [('W', False), ('y', False), ('A', True), ('B', False)]
    return 'GRAVITY start-side (stable start, no over-grab)', ok_bold and ok_link, \
        f'bold={bold} link={link}'


# =========================================================================
# Randomized PBT.  Compare the DOCUMENT-ORDER render to a naive centralized
# oracle: a plain marked-text buffer that STAMPS marks eagerly onto characters
# at addMark time and inherits-from-left on insert (the "atomic" semantics).
# Expanding marks only (bold/italic add/remove) so the crude oracle is sane.
#
# Claim under test: absent deletion the two AGREE exactly (the read is the
# naive semantics); every divergence is delete-induced -- the trilemma
# atomicity caveat.  Also: the doc-order read is a pure function of (live set,
# marks), so permuting mark/delete order leaves it unchanged (convergence).
# =========================================================================
def random_run(rng, nsteps):
    d = Doc()
    marks = []           # list of Mark (document-order model)
    ofmt = {}            # oracle: char id -> {mtype: (mid, op)}
    nextid = [1]
    # seed with two chars
    for cp in ('p', 'q'):
        i = nextid[0]; nextid[0] += 1
        d.ins(i, cp, d.live_order()[-1] if d.live_order() else 0)
        ofmt[i] = {}
    had_delete = False
    for _ in range(nsteps):
        live = d.live_order()
        r = rng.random()
        if r < 0.40 or not live:                       # insert
            i = nextid[0]; nextid[0] += 1
            anchor = rng.choice([0] + live)
            d.ins(i, chr(97 + i % 26), anchor)
            nl = d.live_order(); k = nl.index(i)
            ofmt[i] = dict(ofmt[nl[k - 1]]) if k > 0 else {}   # inherit-left
        elif r < 0.62 and live:                        # delete
            x = rng.choice(live); d.delete(x); ofmt.pop(x, None); had_delete = True
        else:                                          # add / remove mark
            mt = rng.choice(['bold', 'italic'])
            op = 'add' if rng.random() < 0.7 else 'remove'
            i = rng.randrange(len(live)); j = rng.randrange(i, len(live))
            mid = nextid[0]; nextid[0] += 1
            marks.append(make_mark(d, mid, mt, None, live[i], live[j],
                                   'before', 'after', op=op))
            for c in live[i:j + 1]:
                cur = ofmt[c].get(mt)
                if cur is None or mid > cur[0]:
                    ofmt[c][mt] = (mid, op)
    # renders (mtype sets in reading order)
    doc_r = [(cp, {t for t, _ in s}) for (_c, cp, s) in render(d, marks, DR)]
    orc_r = []
    for c in d.live_order():
        orc_r.append((d.codept[c], {mt for mt, (_m, op) in ofmt[c].items() if op == 'add'}))
    # convergence: permuting mark order must not change the doc render
    perm = list(marks); rng.shuffle(perm)
    conv = [(cp, {t for t, _ in s}) for (_c, cp, s) in render(d, perm, DR)]
    return doc_r, orc_r, conv, had_delete


def pbt(n=400, seed0=0):
    from random import Random
    nodel_total = nodel_agree = del_total = del_agree = conv_fail = 0
    over = under = mixed = 0        # divergence classification (with-delete)
    first_nodel_div = None
    for e in range(n):
        rng = Random(seed0 * 100003 + e)
        doc_r, orc_r, conv, had_del = random_run(rng, rng.randint(6, 20))
        if conv != doc_r:
            conv_fail += 1
        if had_del:
            del_total += 1
            if doc_r == orc_r:
                del_agree += 1
            else:
                doc_extra = any(sd - so for (_c, sd), (_o, so) in zip(doc_r, orc_r))
                orc_extra = any(so - sd for (_c, sd), (_o, so) in zip(doc_r, orc_r))
                if doc_extra and not orc_extra:
                    over += 1        # trilemma atomicity re-span (doc over-formats)
                elif orc_extra and not doc_extra:
                    under += 1       # doc-order drops the oracle's STALE stamp (a win)
                else:
                    mixed += 1
        else:
            nodel_total += 1
            if doc_r == orc_r:
                nodel_agree += 1
            elif first_nodel_div is None:
                first_nodel_div = (e, doc_r, orc_r)
    return {'nodel': (nodel_agree, nodel_total), 'del': (del_agree, del_total),
            'conv_fail': conv_fail, 'first_nodel_div': first_nodel_div,
            'over': over, 'under': under, 'mixed': mixed}


# =========================================================================
def main():
    import sys
    verbose = '-v' in sys.argv[1:]
    print('=' * 70)
    print('Peritext DOCUMENT-ORDER read model vs TREE-ANCESTRY control (task #55)')
    print('=' * 70)
    ok, detail = _selfcheck()
    print(f'[document layer]  {"OK" if ok else "FAIL"}  {detail}\n')

    print('-- Litt et al. examples (document-order = paper; tree-ancestry control) --')
    examples = [ex1_insert_within_span, ex2_overlapping_bold_italic,
                ex3_delete_span_then_reinsert, ex5_concurrent_add_vs_remove,
                ex7_bold_boundary_expands, ex8_link_boundary_no_expand]
    allok = ok
    for fn in examples:
        name, good, detail = fn()
        allok &= good
        print(f'  [{"PASS" if good else "FAIL"}] {name}')
        if verbose or not good:
            print(f'         {detail}')

    print('\n-- The retracted no-leak claim, made concrete (deletion of anchor) --')
    for fn in (leak_delete_start_anchor, leak_skip_surviving_sibling):
        name, good, detail = fn()
        allok &= good
        print(f'  [{"PASS" if good else "FAIL"}] {name}')
        print(f'         {detail}')

    print('\n-- startSide/endSide gravity + the trilemma atomicity cost --')
    for fn in (gravity_start_side, trilemma_atomicity_respan):
        name, good, detail = fn()
        allok &= good
        print(f'  [{"PASS" if good else "FAIL"}] {name}')
        print(f'         {detail}')

    print('\n-- Randomized PBT (doc-order vs naive eager oracle; convergence) --')
    res = pbt(400)
    na, nt = res['nodel']; da, dt = res['del']
    print(f'  delete-free runs : {na}/{nt} agree with naive oracle '
          f'(expect ALL: read == naive semantics absent deletion)')
    print(f'  with-delete runs : {da}/{dt} agree; {res["over"]} diverge by the '
          f'trilemma atomicity re-span (doc over-formats), {res["under"]} by '
          f'doc-order dropping the oracle\'s STALE stamp (a win), '
          f'{res["mixed"]} mixed')
    print(f'  convergence      : {res["conv_fail"]} / 400 mark-permutation failures '
          f'(expect 0: read is a pure function of live set + marks)')
    if res['first_nodel_div']:
        print(f'  !! delete-free divergence (unexpected): {res["first_nodel_div"]}')
    pbt_ok = (na == nt) and res['conv_fail'] == 0
    allok &= pbt_ok

    print('\n' + '=' * 70)
    print(f'OVERALL: {"ALL CHECKS PASS" if allok else "FAILURES PRESENT"}')
    print('=' * 70)
    return 0 if allok else 1


if __name__ == '__main__':
    raise SystemExit(main())
