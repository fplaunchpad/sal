/**
 * Hand-derived minimal schedules with their expected outcomes, for
 * Automerge text with marks under both mark semantics of the instance's
 * specification: `anchor` (Peritext's anchors) and `marker` (boundaries as
 * list elements). Each case states, per semantics, the admitted final views
 * (derived by hand in the comment above it) and whether a witness exists, the
 * view Automerge is expected to display, a view it must not display, and the
 * expected verdict of each check. Failing cases name their mechanism class
 * and are paired with a control that changes one ingredient.
 *
 * Notation in comments: ids are counter@actor, replica r has actor 0r, the
 * genesis change is 1@00. <B and B> are a bold begin and end boundary, + marks
 * a boundary whose expand flag is set; siblings with one reference are
 * ordered by descending id, and among marks of one name covering a character
 * the greatest id wins. Policies: bold expands after, italic before,
 * link none. `x*` is bold x, `x/` italic, `x~` linked.
 *
 * Run with `node regressions.mjs` or `node run.mjs --mode regressions`.
 */
import assert from 'node:assert/strict';
import { fileURLToPath } from 'node:url';
import { runRegressions as runAll } from '../../ra-pbt/src/index.js';
import { Execution, execute, eventsAt, instanceFor, viewKey, viewsEqual } from '../../ra-pbt/instances/automerge/index.js';
import { findWitness, allFinalViews } from '../../ra-pbt/src/witness.js';
import { classifyAt } from '../../ra-pbt/instances/automerge/classify.js';

const B = { bold: true };
const I = { italic: true };
const L = (u) => ({ link: u });
const v = (...pairs) => pairs.map(([ch, attrs]) => ({ ch, attrs: attrs ?? {} }));
const plain = (s) => v(...[...s].map((ch) => [ch]));
const ins = (replica, index, text, attrs = {}) => ({ type: 'edit', replica, kind: 'insert', index, text, attrs });
const del = (replica, index, len) => ({ type: 'edit', replica, kind: 'delete', index, len });
const fmt = (replica, index, len, attrs) => ({ type: 'edit', replica, kind: 'format', index, len, attrs });
const deliver = (from, to) => ({ type: 'deliver', from, to });
const send = (from, to, op) => ({ type: 'send', from, to, op });
const both = [deliver(1, 2), deliver(2, 1)];

const sameViewSet = (xs, ys) => JSON.stringify(xs.map(viewKey).sort()) === JSON.stringify(ys.map(viewKey).sort());
const SEMANTICS = ['anchor', 'marker'];

/** Runs a schedule without checks or final sync under a semantics. */
function run(schedule, semantics) {
  const ex = new Execution(schedule.replicas, { checks: [], semantics });
  for (const s of schedule.steps) ex.apply(s);
  return ex;
}

/**
 * A declared case. `expect[semantics]` is { witness, admitted? } and
 * `checks[semantics]` maps check names to the expected pass verdict (checks
 * not listed must pass). `replicas` are checked for `observed`; `cls` is
 * { semantics, replica, class } for the classifier. `extra(ex)` runs further
 * assertions on the anchor execution.
 */
function declared({ name, schedule, replicas, observed, notObserved, expect, checks = {}, cls, extra }) {
  return {
    name,
    schedule,
    run(results) {
      for (const sem of SEMANTICS) {
        const ex = run(schedule, sem);
        for (const r of replicas) {
          const rep = ex.replica(r);
          const shown = rep.visible();
          assert.ok(viewsEqual(shown, observed), `${sem} replica ${r}: displayed ${JSON.stringify(shown)}`);
          assert.ok(!viewsEqual(shown, notObserved), `${sem} replica ${r}: displayed the excluded view`);
          const { events } = eventsAt(ex, r);
          const spec = instanceFor(sem, 'chars').spec;
          const w = findWitness(spec, events, rep.visibleWithIds()).found;
          assert.equal(w, expect[sem].witness, `${sem} replica ${r}: witness ${w ? 'found' : 'not found'}`);
          if (expect[sem].admitted) {
            const adm = allFinalViews(spec, events);
            assert.ok(!adm.truncated, `${sem} replica ${r}: admitted views truncated`);
            assert.ok(sameViewSet(adm, expect[sem].admitted), `${sem} replica ${r}: admitted ${JSON.stringify(adm)}`);
            assert.equal(adm.some((a) => viewsEqual(a, observed)), expect[sem].witness, `${sem} replica ${r}: admitted set and witness disagree`);
          }
        }
        const trace = execute(schedule, { semantics: sem });
        for (const [c, res] of Object.entries(trace.checks)) {
          const want = checks[sem]?.[c] ?? true;
          assert.equal(res.pass, want, `${sem}: ${c} ${res.pass ? 'passed' : 'failed'}, expected ${want ? 'pass' : 'fail'}`);
        }
        assert.equal(trace.anomalies.length, 0, `${sem}: execution anomalies ${JSON.stringify(trace.anomalies)}`);
        if (sem === 'anchor' && extra) extra(ex);
      }
      if (cls) assert.equal(classifyAt(schedule, cls.replica, cls.semantics).class, cls.class, 'classified otherwise');
      results.observed = observed;
      results.admitted = expect.anchor.admitted;
    },
  };
}

/*
 * Plain text. r1 inserts "ab" (a 2@01, b 3@01); sync. Concurrently r1
 * inserts x at 1 (4@01, reference a) and r2 inserts y at 1 (4@02, reference
 * a), then deletes a (5@02); sync. Children of a by descending id: y, x, so
 * the list is a(x) y x b, shown "yxb". Specification: x and y each land in
 * the gap (a, b), in either order; a deleted. Admitted { yxb, xyb } under
 * both semantics (no marks).
 */
const plainCase = declared({
  name: 'plain text: concurrent inserts in one gap and a delete',
  schedule: { replicas: 2, steps: [ins(1, 0, 'ab'), deliver(1, 2), ins(1, 1, 'x'), ins(2, 1, 'y'), del(2, 0, 1), ...both] },
  replicas: [1, 2],
  observed: plain('yxb'),
  notObserved: plain('xyb'),
  expect: { anchor: { witness: true, admitted: [plain('yxb'), plain('xyb')] }, marker: { witness: true, admitted: [plain('yxb'), plain('xyb')] } },
});

/*
 * Convergence control. r1 inserts "ab"; sync to r2 and r3. Concurrently:
 *   X r1 inserts x at 1 (4@01, reference a);
 *   F r2 bolds [0,2): <B 4@02 (reference head), B>+ 5@02 (reference b); the
 *     range reaches the end of the text, so the end anchor is the end;
 *   D r3 deletes b.
 * Deliveries 1->2, 2->3, 3->1 leave r2 without D; then 1->3, 2->1, 3->2.
 * List at the end: <B a x b(x) B>, shown a* x*. Before the last round r2
 * shows a* x* b*, which differs from r1's a* x*.
 * Specification: X before F: F covers a to the end: a* x*. X after F: x
 * lands between a and b, inside F under both readings: a* x*. D commutes.
 * Admitted { a* x* } under both semantics.
 */
const convergenceRound = [deliver(1, 2), deliver(2, 3), deliver(3, 1)];
const convergenceHead = [ins(1, 0, 'ab'), deliver(1, 2), deliver(1, 3), ins(1, 1, 'x'), fmt(2, 0, 2, B), del(3, 1, 1), ...convergenceRound];
const convergenceCase = declared({
  name: 'convergence control: concurrent insert, format and delete received in different orders by three replicas',
  schedule: { replicas: 3, steps: [...convergenceHead, deliver(1, 3), deliver(2, 1), deliver(3, 2)] },
  replicas: [1, 2, 3],
  observed: v(['a', B], ['x', B]),
  notObserved: v(['a', B], ['x']),
  expect: { anchor: { witness: true, admitted: [v(['a', B], ['x', B])] }, marker: { witness: true, admitted: [v(['a', B], ['x', B])] } },
  extra() {
    const head = run({ replicas: 3, steps: convergenceHead }, 'anchor');
    assert.ok(viewsEqual(head.replica(1).visible(), v(['a', B], ['x', B])), 'replica 1 before the last round');
    assert.ok(viewsEqual(head.replica(2).visible(), v(['a', B], ['x', B], ['b', B])), 'replica 2 before the last round');
    assert.ok(!viewsEqual(head.replica(1).visible(), head.replica(2).visible()), 'replicas 1 and 2 agree before the last round');
  },
});

/*
 * Opened replica. r1 inserts "abc" and bolds [1,2); r2 opens the saved
 * document, deletes b and inserts x at 1. The determinism check forks r2 as a
 * created and an opened replica before each edit; both must agree. x sits
 * between a and c; bold expands after and a is plain, so x is plain: a x c.
 * Specification: one linear extension, a x c, under both semantics (x lands
 * immediately after a, before the begin boundary, whose anchor is before b).
 */
const openedCase = declared({
  name: 'opened replica: delete and insert agree with a created replica',
  schedule: { replicas: 2, steps: [ins(1, 0, 'abc'), fmt(1, 1, 1, B), { type: 'open', replica: 2, from: 1 }, del(2, 1, 1), ins(2, 1, 'x'), deliver(2, 1)] },
  replicas: [1, 2],
  observed: plain('axc'),
  notObserved: v(['a'], ['x', B], ['c']),
  expect: { anchor: { witness: true, admitted: [plain('axc')] }, marker: { witness: true, admitted: [plain('axc')] } },
});

/*
 * Y-001 shape. r1 inserts "abc" (2..4@01) and bolds b (5, 6@01); sync.
 * Concurrently r1 bolds [0,2) (7, 8@01) and r2 unbolds [1,3) (7, 8@02).
 * b is covered by 5@01, 7@01 and 7@02; 7@02 is greatest: b plain. a has
 * 7@01: bold. c has 7@02: plain. Shown a* b c.
 * Specification: on b the greater identity 7@02 (the unbold) wins in either
 * order, a is covered by the bold only, c by the unbold only. Admitted
 * { a* b c } under both semantics; the order-dependent reading's second view
 * a* b* c is excluded, and c is bold in no reading.
 */
const y001 = declared({
  name: 'Y-001 shape: concurrent overlapping bold and unbold (expected pass)',
  schedule: { replicas: 2, steps: [ins(1, 0, 'abc'), fmt(1, 1, 1, B), deliver(1, 2), fmt(1, 0, 2, B), fmt(2, 1, 2, { bold: null }), ...both] },
  replicas: [1, 2],
  observed: v(['a', B], ['b'], ['c']),
  notObserved: v(['a', B], ['b', B], ['c', B]),
  expect: { anchor: { witness: true, admitted: [v(['a', B], ['b'], ['c'])] }, marker: { witness: true, admitted: [v(['a', B], ['b'], ['c'])] } },
});

/*
 * Y-002 shape. r1 inserts q (2@01); sync. Concurrently r1 bolds [0,1)
 * (<B 3@01 at the head, B>+ 4@01 after q) and r2 inserts z bold at 0 (z 3@02,
 * <B 4@02 at the head, B>+ 5@02 after z). Head children by descending id:
 * 4@02, 3@02, 3@01: <B z B> <B q B>, shown z* q*.
 * Specification: z carries its own bold, q is bolded; either order gives
 * z* q*, and z's position against r1's begin boundary does not change it.
 * Admitted { z* q* } under both semantics.
 */
const y002 = declared({
  name: 'Y-002 shape: bold insert at the head beside a concurrent bold (expected pass)',
  schedule: { replicas: 2, steps: [ins(1, 0, 'q'), deliver(1, 2), fmt(1, 0, 1, B), ins(2, 0, 'z', B), ...both] },
  replicas: [1, 2],
  observed: v(['z', B], ['q', B]),
  notObserved: v(['z', B], ['q']),
  expect: { anchor: { witness: true, admitted: [v(['z', B], ['q', B])] }, marker: { witness: true, admitted: [v(['z', B], ['q', B])] } },
});

/*
 * Y-003 shape. r1 inserts "wv", then b bold at 2; sync. Concurrently r1
 * deletes b and r2 inserts z bold at 3 (after b, with its own boundaries).
 * Shown w v z*. Specification: z carries its own bold whatever b's fate.
 * Admitted { w v z* } under both semantics.
 */
const y003 = declared({
  name: 'Y-003 shape: deleting a bold character beside a concurrent bold insert (expected pass)',
  schedule: { replicas: 2, steps: [ins(1, 0, 'wv'), ins(1, 2, 'b', B), deliver(1, 2), del(1, 2, 1), ins(2, 3, 'z', B), ...both] },
  replicas: [1, 2],
  observed: v(['w'], ['v'], ['z', B]),
  notObserved: v(['w'], ['v'], ['z']),
  expect: { anchor: { witness: true, admitted: [v(['w'], ['v'], ['z', B])] }, marker: { witness: true, admitted: [v(['w'], ['v'], ['z', B])] } },
});

/*
 * Y-004 shape, passing. r1 inserts a (2@01); sync. Concurrently r1 bolds
 * [0,1) (<B 3@01 at the head, B>+ 4@01) and r2 inserts h at 0 (3@02, at the
 * head). Head children: h (3@02) before <B (3@01): h <B a B>, shown h a*.
 * Anchor: bold does not expand before, so its start is anchored before a and
 * h, which stands before a in every order, is plain: admitted { h a* }.
 * Marker: h and <B both land in the gap at the head, in either order:
 * admitted { h a*, h* a* }.
 */
const y004 = declared({
  name: 'Y-004 shape: plain insert at the start of a concurrent bold, insert ordered first (expected pass)',
  schedule: { replicas: 2, steps: [ins(1, 0, 'a'), deliver(1, 2), fmt(1, 0, 1, B), ins(2, 0, 'h'), ...both] },
  replicas: [1, 2],
  observed: v(['h'], ['a', B]),
  notObserved: v(['h', B], ['a', B]),
  expect: { anchor: { witness: true, admitted: [v(['h'], ['a', B])] }, marker: { witness: true, admitted: [v(['h'], ['a', B]), v(['h', B], ['a', B])] } },
});

/*
 * A-001, the same shape with the boundary ordered first. r1 inserts "ax"
 * (2, 3@01); sync. r1 deletes x (4@01), so its next ids are higher, and
 * bolds [0,1) (<B 5@01 at the head, B>+ 6@01); concurrently r2 inserts h at 0
 * (4@02). Head children: <B (5@01) before h (4@02): <B h a B> x(x), shown
 * h* a*. Bold does not expand before, yet the concurrent h is bold.
 * Anchor: admitted { h a* } (as in the control): no witness.
 * Marker: admitted { h a*, h* a* }: a witness.
 */
const a001Start = declared({
  name: 'A-001 boundary placed by operation order: a non-expanding start captures a concurrent insert',
  schedule: { replicas: 2, steps: [ins(1, 0, 'ax'), deliver(1, 2), del(1, 1, 1), fmt(1, 0, 1, B), ins(2, 0, 'h'), ...both] },
  replicas: [1, 2],
  observed: v(['h', B], ['a', B]),
  notObserved: v(['h'], ['a', B]),
  expect: { anchor: { witness: false, admitted: [v(['h'], ['a', B])] }, marker: { witness: true, admitted: [v(['h'], ['a', B]), v(['h', B], ['a', B])] } },
  checks: { anchor: { raLinearizability: false } },
  cls: { semantics: 'anchor', replica: 1, class: 'A-001' },
});

/*
 * A-001 at the end of a link. r1 inserts "ab" (2, 3@01); sync. r2 inserts z
 * at 0 (4@02). r1 links [0,2) (<L 4@01, L> 5@01, the end not expanding, so
 * anchored after b); concurrently r2 inserts x at 3, after b (5@02). Children
 * of b: x (5@02) before L> (5@01): z <L a b x L>, shown z a~ b~ x~.
 * Anchor: x stands after b in every order: admitted { z a~ b~ x }.
 * Marker: x and L> both land in the gap after b, and z, concurrent with the
 * link too, lands at the head on either side of <L: admitted { z a~ b~ x,
 * z a~ b~ x~, z~ a~ b~ x, z~ a~ b~ x~ }.
 * Control: without z, x gets 4@02, ordered after L> (5@01): z is absent and
 * x stays outside: a~ b~ x, admitted under both.
 */
const u1 = L('u1');
const a001Link = declared({
  name: 'A-001 boundary placed by operation order: a link grows to a concurrent insert after its end',
  schedule: { replicas: 2, steps: [ins(1, 0, 'ab'), deliver(1, 2), ins(2, 0, 'z'), fmt(1, 0, 2, u1), ins(2, 3, 'x'), ...both] },
  replicas: [1, 2],
  observed: v(['z'], ['a', u1], ['b', u1], ['x', u1]),
  notObserved: v(['z'], ['a', u1], ['b', u1], ['x']),
  expect: {
    anchor: { witness: false, admitted: [v(['z'], ['a', u1], ['b', u1], ['x'])] },
    marker: {
      witness: true,
      admitted: [v(['z'], ['a', u1], ['b', u1], ['x']), v(['z'], ['a', u1], ['b', u1], ['x', u1]), v(['z', u1], ['a', u1], ['b', u1], ['x']), v(['z', u1], ['a', u1], ['b', u1], ['x', u1])],
    },
  },
  checks: { anchor: { raLinearizability: false } },
  cls: { semantics: 'anchor', replica: 1, class: 'A-001' },
});
const a001LinkControl = declared({
  name: 'control for the link case: the concurrent insert is ordered after the end boundary',
  schedule: { replicas: 2, steps: [ins(1, 0, 'ab'), deliver(1, 2), fmt(1, 0, 2, u1), ins(2, 2, 'x'), ...both] },
  replicas: [1, 2],
  observed: v(['a', u1], ['b', u1], ['x']),
  notObserved: v(['a', u1], ['b', u1], ['x', u1]),
  expect: {
    anchor: { witness: true, admitted: [v(['a', u1], ['b', u1], ['x'])] },
    marker: { witness: true, admitted: [v(['a', u1], ['b', u1], ['x']), v(['a', u1], ['b', u1], ['x', u1])] },
  },
});

/*
 * A-001 at the end of the text. r1 inserts t (2@01); concurrently r2 inserts
 * f bold at 0 (f 2@02, <B 3@02 at the head, B>+ 4@02 after f). The bold
 * expands after and reaches the end of r2's text, so its end anchor is the
 * end of the text. Head children: <B (3@02), f (2@02), t (2@01): <B f B> t,
 * shown f* t.
 * Anchor: t before f: t f*; t after f: f* t*. Admitted { t f*, f* t* }: no
 * witness for f* t.
 * Marker: t lands anywhere at the head: before <B (t f*), between <B and f
 * (t* f*), between f and B> (f* t*) or after B> (f* t): admitted all four.
 */
const a001End = declared({
  name: 'A-001 boundary placed by operation order: an expanding end at the end of the text misses a concurrent insert',
  schedule: { replicas: 2, steps: [ins(1, 0, 't'), ins(2, 0, 'f', B), ...both] },
  replicas: [1, 2],
  observed: v(['f', B], ['t']),
  notObserved: v(['f', B], ['t', B]),
  expect: { anchor: { witness: false, admitted: [v(['t'], ['f', B]), v(['f', B], ['t', B])] }, marker: { witness: true, admitted: [v(['t'], ['f', B]), v(['t', B], ['f', B]), v(['f', B], ['t']), v(['f', B], ['t', B])] } },
  checks: { anchor: { raLinearizability: false } },
  cls: { semantics: 'anchor', replica: 1, class: 'A-001' },
});

/*
 * Y-005 shape. r1 inserts "abc"; sync. Concurrently r1 bolds [0,2) and r2
 * bolds [1,3). Shown a* b* c*. Admitted { a* b* c* } under both semantics.
 */
const y005 = declared({
  name: 'Y-005 shape: overlapping concurrent bolds (expected pass)',
  schedule: { replicas: 2, steps: [ins(1, 0, 'abc'), deliver(1, 2), fmt(1, 0, 2, B), fmt(2, 1, 2, B), ...both] },
  replicas: [1, 2],
  observed: v(['a', B], ['b', B], ['c', B]),
  notObserved: v(['a', B], ['b', B], ['c']),
  expect: { anchor: { witness: true, admitted: [v(['a', B], ['b', B], ['c', B])] }, marker: { witness: true, admitted: [v(['a', B], ['b', B], ['c', B])] } },
});

/*
 * Y-007 shape (partial delivery). r1 inserts a bold (r1#0), inserts b at 1
 * (r1#1; bold expands after, so b is bold), unbolds [0,2) (r1#2, depending
 * on r1#1). r2 receives r1#0 and then r1#2: Automerge queues r1#2, whose
 * dependency is missing, so r2 has integrated r1#0 only, holds a queued
 * change, and shows a*. Admitted for { r1#0 }: { a* }.
 * Control: r1#0, r1#1, r1#2 in order: a b. Admitted { a b }.
 */
const y007Steps = (order) => [ins(1, 0, 'a', B), ins(1, 1, 'b'), fmt(1, 0, 2, { bold: null }), ...order.map((k) => send(1, 2, k))];
const y007 = declared({
  name: 'Y-007 shape: an unbold sent ahead of the insert it depends on is queued (expected pass)',
  schedule: { replicas: 2, steps: y007Steps([0, 2]) },
  replicas: [2],
  observed: v(['a', B]),
  notObserved: plain('a'),
  expect: { anchor: { witness: true, admitted: [v(['a', B])] }, marker: { witness: true, admitted: [v(['a', B])] } },
  extra(ex) {
    assert.equal(ex.replica(2).hasPending(), true, 'no change queued');
    assert.deepEqual([...ex.integrated[2]].sort(), ['r1#0'], 'integrated records differ');
  },
});
const y007Control = declared({
  name: 'control for the Y-007 shape: the three changes sent in issue order',
  schedule: { replicas: 2, steps: y007Steps([0, 1, 2]) },
  replicas: [1, 2],
  observed: plain('ab'),
  notObserved: v(['a', B], ['b', B]),
  expect: { anchor: { witness: true, admitted: [plain('ab')] }, marker: { witness: true, admitted: [plain('ab')] } },
  extra(ex) {
    assert.equal(ex.replica(2).hasPending(), false, 'a change is queued');
  },
});

/*
 * A-002 shared insertion point, one replica. r1 inserts q bold (q 2@01, <B
 * 3@01, B>+ 4@01), links it (<L 5@01 at the head, L> 6@01 after q; the link
 * does not expand, so L> is sticky), deletes q and inserts i at 0. List
 * before the insert: <L <B q(x) L> B>+. The scan from the head passes the
 * non-sticky <L and <B, the tombstone, and stops after the sticky L>: i
 * lands between L> and B>, inside the bold. Shown i*; the displayed
 * document was empty, so the index-level edit gives a plain i.
 * Specification: i is inserted after q's tombstone, inside the bold's
 * anchors (before q, the end of the text) and its boundaries: admitted
 * { i* } under both semantics. localMeaning fails, RA-linearizability holds.
 * Control: without the link, nothing sticky follows the head: i lands before
 * <B and is plain; admitted { i } under both.
 */
const a002Steps = (withLink) => [ins(1, 0, 'q', B), ...(withLink ? [fmt(1, 0, 1, L('u1'))] : []), del(1, 0, 1), ins(1, 0, 'i')];
const a002 = declared({
  name: 'A-002 shared insertion point: a link boundary carries a new character into a deleted bold span',
  schedule: { replicas: 1, steps: a002Steps(true) },
  replicas: [1],
  observed: v(['i', B]),
  notObserved: plain('i'),
  expect: { anchor: { witness: true, admitted: [v(['i', B])] }, marker: { witness: true, admitted: [v(['i', B])] } },
  checks: { anchor: { localMeaning: false }, marker: { localMeaning: false } },
  cls: { semantics: 'marker', replica: 1, class: 'A-002' },
});
const a002Control = declared({
  name: 'control for A-002: the same edits without the link',
  schedule: { replicas: 1, steps: a002Steps(false) },
  replicas: [1],
  observed: plain('i'),
  notObserved: v(['i', B]),
  expect: { anchor: { witness: true, admitted: [plain('i')] }, marker: { witness: true, admitted: [plain('i')] } },
});

/*
 * A-003 emptied mark, one replica. r1 inserts a (2@01), italicises [0,1)
 * (italic expands before; the range starts at 0, so the start anchor is the
 * start of the text; <I+ 3@01 at the head, I> 4@01 after a, anchored after
 * a), deletes a and inserts u at 0. The scan from the head records the sticky
 * <I+, passes a's tombstone, and drops it at the matching I>: u lands at the
 * head, before <I+, and is plain. The index-level edit agrees: an empty view
 * gives a plain u.
 * Anchor: u is recorded before a's tombstone, and the anchors (start of
 * text, after a) enclose it: admitted { u/ }: no witness.
 * Marker: u lands before <I: admitted { u }.
 * Control: a is not deleted; the scan stops at a, so u lands after <I+ and
 * is italic: u/ a/, admitted under both.
 */
const a003Steps = (deleted) => [ins(1, 0, 'a'), fmt(1, 0, 1, I), ...(deleted ? [del(1, 0, 1)] : []), ins(1, 0, 'u')];
const a003 = declared({
  name: 'A-003 emptied mark: the anchors of a mark whose text is deleted still enclose a new character',
  schedule: { replicas: 1, steps: a003Steps(true) },
  replicas: [1],
  observed: plain('u'),
  notObserved: v(['u', I]),
  expect: { anchor: { witness: false, admitted: [v(['u', I])] }, marker: { witness: true, admitted: [plain('u')] } },
  checks: { anchor: { raLinearizability: false } },
  cls: { semantics: 'anchor', replica: 1, class: 'A-003' },
});
const a003Control = declared({
  name: 'control for A-003: the italic text is kept',
  schedule: { replicas: 1, steps: a003Steps(false) },
  replicas: [1],
  observed: v(['u', I], ['a', I]),
  notObserved: v(['u'], ['a', I]),
  expect: { anchor: { witness: true, admitted: [v(['u', I], ['a', I])] }, marker: { witness: true, admitted: [v(['u', I], ['a', I])] } },
});

export const REGRESSIONS = [plainCase, convergenceCase, openedCase, y001, y002, y003, y004, a001Start, y005, y007, y007Control, a001Link, a001LinkControl, a001End, a002, a002Control, a003, a003Control];

/** Runs every regression; returns [{ name, pass, error?, results }]. */
export function runRegressions() {
  return runAll(REGRESSIONS);
}

if (process.argv[1] && fileURLToPath(import.meta.url) === process.argv[1]) {
  const out = runRegressions();
  for (const r of out) console.log(`${r.pass ? 'ok  ' : 'FAIL'} ${r.name}${r.pass ? '' : ': ' + r.error}`);
  if (out.some((r) => !r.pass)) process.exitCode = 1;
}
