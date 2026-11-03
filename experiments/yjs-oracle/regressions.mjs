/**
 * Hand-derived minimal schedules with their expected outcomes. Each case
 * states the specification's admitted final views (derived by hand in the
 * comment above it), the observed Yjs view it is expected to produce, and
 * whether a witness exists. Every failing case is paired with a passing
 * control that changes one ingredient, and every assertion of equality has a
 * companion assertion of inequality against the tempting wrong answer.
 *
 * Failing cases carry the mechanism class of the instance's classifier (Y-001 to Y-005)
 * and assert that the classifier assigns it. Notation in comments: B and N
 * are a bold:true and a bold:null marker, I and In the italic ones, x marks
 * a deleted item; clients 1 and 2 order concurrent siblings with equal
 * origins (lower client first).
 *
 * Run with `node regressions.mjs` or `node run.mjs --mode regressions`.
 */
import assert from 'node:assert/strict';
import { fileURLToPath } from 'node:url';
import { runRegressions as runAll } from '../../ra-pbt/src/index.js';
import { execute, Execution, viewKey, viewsEqual, initial, apply, view, interpret, findWitness, allFinalViews, eventsAt } from '../../ra-pbt/instances/yjs/index.js';
import { classifyAt } from '../../ra-pbt/instances/yjs/classify.js';

const v = (...pairs) => pairs.map(([ch, attrs]) => ({ ch, attrs: attrs ?? {} }));
const B = { bold: true };
const I = { italic: true };
const ins = (replica, index, text, attrs = {}) => ({ type: 'edit', replica, kind: 'insert', index, text, attrs });
const del = (replica, index, len) => ({ type: 'edit', replica, kind: 'delete', index, len });
const fmt = (replica, index, len, attrs) => ({ type: 'edit', replica, kind: 'format', index, len, attrs });
const deliver = (from, to) => ({ type: 'deliver', from, to });
/** Two replicas: `prefix` at replica 1, sync, the concurrent pair, sync both ways. */
const concurrentPair = (prefix, op1, op2) => ({ replicas: 2, steps: [...prefix, deliver(1, 2), op1, op2, deliver(1, 2), deliver(2, 1)] });

const sameViewSet = (xs, ys) =>
  JSON.stringify(xs.map(viewKey).sort()) === JSON.stringify(ys.map(viewKey).sort());

/** Runs a schedule (no final sync) and returns the views and witness results per replica. */
function observe(schedule) {
  const ex = new Execution(schedule.replicas, { checks: [] });
  for (const s of schedule.steps) ex.apply(s);
  const out = {};
  for (let r = 1; r <= schedule.replicas; r++) {
    const { events } = eventsAt(ex, r);
    const visible = ex.replica(r).visible();
    out[r] = { visible, witness: findWitness(events, visible), admitted: allFinalViews(events) };
  }
  return out;
}

/*
 * Y-001 marker ownership: concurrent overlapping bold / unbold.
 *
 * Replica 1 inserts "abc" (ids 1:0 1:1 1:2) and bolds b, then replica 2
 * receives both. Concurrently:
 *   F1 (replica 1): format [a..b] {bold:true}
 *   F2 (replica 2): format [b..c] {bold:null}
 * Starting state: a, b(bold), c. The two linear extensions:
 *   F1 then F2: a(bold) b(bold) c  ->  a(bold) b c
 *   F2 then F1: a b c              ->  a(bold) b(bold) c
 * So the admitted final views are exactly { a(bold) b c, a(bold) b(bold) c }.
 * c is bold in neither, since F2 unbolds it and F1 never touches it.
 */
const overlapSchedule = {
  replicas: 2,
  steps: [
    { type: 'edit', replica: 1, kind: 'insert', index: 0, text: 'abc', attrs: {} },
    { type: 'edit', replica: 1, kind: 'format', index: 1, len: 1, attrs: { bold: true } },
    { type: 'deliver', from: 1, to: 2 },
    { type: 'edit', replica: 1, kind: 'format', index: 0, len: 2, attrs: { bold: true } },
    { type: 'edit', replica: 2, kind: 'format', index: 1, len: 2, attrs: { bold: null } },
    { type: 'deliver', from: 1, to: 2 },
    { type: 'deliver', from: 2, to: 1 },
  ],
};
const overlapAdmitted = [v(['a', B], ['b'], ['c']), v(['a', B], ['b', B], ['c'])];
const overlapBelieved = v(['a', B], ['b', B], ['c', B]);

/*
 * Control: the same two formats issued sequentially on replica 1.
 * a, b(bold), c  -> format [0,2) bold -> a(bold) b(bold) c
 *                -> format [1,3) null -> a(bold) b c
 * Exactly one linear extension, so the single admitted view is a(bold) b c.
 */
const controlSchedule = {
  replicas: 2,
  steps: [
    { type: 'edit', replica: 1, kind: 'insert', index: 0, text: 'abc', attrs: {} },
    { type: 'edit', replica: 1, kind: 'format', index: 1, len: 1, attrs: { bold: true } },
    { type: 'edit', replica: 1, kind: 'format', index: 0, len: 2, attrs: { bold: true } },
    { type: 'edit', replica: 1, kind: 'format', index: 1, len: 2, attrs: { bold: null } },
    { type: 'deliver', from: 1, to: 2 },
  ],
};
const controlExpected = v(['a', B], ['b'], ['c']);

/**
 * A failing case and its control as two regressions. `failing` and `control`
 * are { schedule, observed, admitted } with hand-derived views; the failing
 * case also names its class. Asserted at both replicas: the observed view,
 * the admitted set, (non-)membership of the observed view in it, the witness
 * result, and the classifier's verdict; and that the control's view differs
 * from the failing case's observed view.
 */
function pairOf(id, title, failing, control, controlTitle) {
  return [
    {
      name: `${id} ${title}`,
      schedule: failing.schedule,
      run(results) {
        const o = observe(failing.schedule);
        for (const r of [1, 2]) {
          assert.ok(viewsEqual(o[r].visible, failing.observed), `replica ${r}: view is not the expected wrong outcome`);
          assert.ok(sameViewSet(o[r].admitted, failing.admitted), `replica ${r}: admitted views differ from the hand derivation`);
          for (const a of failing.admitted) assert.ok(!viewsEqual(o[r].visible, a), `replica ${r}: observed view is admitted`);
          assert.equal(o[r].witness.found, false, `replica ${r}: witness unexpectedly found`);
          assert.equal(classifyAt(failing.schedule, r).class, id, `replica ${r}: classified otherwise`);
        }
        results.observed = o[1].visible;
        results.admitted = failing.admitted;
        const trace = execute(failing.schedule);
        assert.equal(trace.checks.raLinearizability.pass, false, 'raLinearizability check passed');
        assert.equal(trace.checks.convergence.pass, true, 'convergence check failed');
      },
    },
    {
      name: `control for ${id}: ${controlTitle}`,
      schedule: control.schedule,
      run(results) {
        const o = observe(control.schedule);
        for (const r of [1, 2]) {
          assert.ok(viewsEqual(o[r].visible, control.observed), `replica ${r}: view differs from the hand derivation`);
          assert.ok(!viewsEqual(o[r].visible, failing.observed), `replica ${r}: view is the failing case's outcome`);
          assert.ok(sameViewSet(o[r].admitted, control.admitted), `replica ${r}: admitted views differ from the hand derivation`);
          assert.equal(o[r].witness.found, true, `replica ${r}: no witness`);
          assert.equal(classifyAt(control.schedule, r).class, null, `replica ${r}: a difference was classified`);
        }
        results.observed = o[1].visible;
        results.admitted = control.admitted;
        const trace = execute(control.schedule);
        for (const c of ['convergence', 'raLinearizability', 'localMeaning', 'conservation'])
          assert.equal(trace.checks[c].pass, true, `${c} check failed on the control`);
      },
    },
  ];
}

/*
 * Y-001 marker ownership, insert variant.
 *
 * Replica 1 inserts "et" with bold: items B(1:0) e(1:1) t(1:2) N(1:3); sync.
 * Concurrently:
 *   P (replica 1): insert "d" {bold} at 2. The attributes in effect after t
 *     are already bold, so no marker is created: d(1:4) sits between t and N
 *     and is bold only through B, which P does not own.
 *   U (replica 2): format [0,2) {bold:null}. formatText deletes B (value true
 *     differs from null), covers e and t, then deletes N (it equals the
 *     requested null); it creates no marker.
 * Merged: Bx e t d Nx, so d is plain: observed e t d.
 * Specification: d is inserted after t with bold; U unbolds exactly e..t.
 *   P then U: e t d(bold); U then P: e t d(bold). Admitted: { e t d(bold) }.
 *
 * Control: U formats [0,1) instead. formatText deletes B, covers e, and
 * re-opens bold with a new marker B' before t (the negated value): Bx e B' t
 * d N, so e t(bold) d(bold). Both specification orders give the same view.
 */
const y001Insert = {
  schedule: concurrentPair([ins(1, 0, 'et', B)], ins(1, 2, 'd', B), fmt(2, 0, 2, { bold: null })),
  observed: v(['e'], ['t'], ['d']),
  admitted: [v(['e'], ['t'], ['d', B])],
};
const y001InsertControl = {
  schedule: concurrentPair([ins(1, 0, 'et', B)], ins(1, 2, 'd', B), fmt(2, 0, 1, { bold: null })),
  observed: v(['e'], ['t', B], ['d', B]),
  admitted: [v(['e'], ['t', B], ['d', B])],
};

/*
 * Y-002 opening marker judged redundant, two formats.
 *
 * Replica 1 inserts "au" (1:0 1:1); sync. Concurrently:
 *   F1 (replica 1): format [0,2) bold: B1(1:2) a u N1(1:3)
 *   F2 (replica 2): format [0,1) bold: B2(2:0) a N2(2:1) u
 * B1 and B2 both have origin null and right origin a, so B1 precedes B2:
 * B1 B2 a N2 u N1. The cleanup that follows each delivery walks the gap
 * before a, finds two bold markers, keeps the last (B2) and deletes B1 as
 * overwritten. N1 stays live where bold is already null and changes
 * nothing; u is governed by N2: observed a(bold) u.
 * Specification: both formats set bold; in either order a and u are bold.
 * Admitted: { a(bold) u(bold) }.
 *
 * Control: F2 formats [0,2) as well. B1 is still deleted, but F2's own
 * closer now follows u: a(bold) u(bold), the single admitted view.
 */
const y002Formats = {
  schedule: concurrentPair([ins(1, 0, 'au')], fmt(1, 0, 2, B), fmt(2, 0, 1, B)),
  observed: v(['a', B], ['u']),
  admitted: [v(['a', B], ['u', B])],
};
const y002FormatsControl = {
  schedule: concurrentPair([ins(1, 0, 'au')], fmt(1, 0, 2, B), fmt(2, 0, 2, B)),
  observed: v(['a', B], ['u', B]),
  admitted: [v(['a', B], ['u', B])],
};

/*
 * Y-002 opening marker judged redundant, insert and format.
 *
 * Replica 1 inserts "q" (1:0); sync. Concurrently:
 *   F (replica 1): format [0,1) bold: B1(1:1) q N1(1:2)
 *   P (replica 2): insert "z" {bold} at 0: B2(2:0) z(2:1) N2(2:2) q
 * B1 and B2 share origin null and right origin q; B1 precedes B2:
 * B1 B2 z N2 q N1. The cleanup deletes B1 as overwritten by B2; N1 stays
 * live and changes nothing; q is governed by N2: observed z(bold) q.
 * Specification: z is inserted at the head with bold, q is formatted bold.
 * Either order: z(bold) q(bold). Admitted: { z(bold) q(bold) }.
 *
 * Control: P inserts z at 1 (after q). B2 now has origin q, and N1 (origin
 * q, right origin null) precedes it: B1 q N1 B2 z N2, so q(bold) z(bold).
 */
const y002Insert = {
  schedule: concurrentPair([ins(1, 0, 'q')], fmt(1, 0, 1, B), ins(2, 0, 'z', B)),
  observed: v(['z', B], ['q']),
  admitted: [v(['z', B], ['q', B])],
};
const y002InsertControl = {
  schedule: concurrentPair([ins(1, 0, 'q')], fmt(1, 0, 1, B), ins(2, 1, 'z', B)),
  observed: v(['q', B], ['z', B]),
  admitted: [v(['q', B], ['z', B])],
};

/*
 * Y-003 delete removes neighbour formatting.
 *
 * Replica 1 inserts "wv" (1:0 1:1) and then "b" {bold} at 2: B(1:2) b(1:3)
 * N(1:4); sync. Concurrently:
 *   D (replica 1): delete [2,3), which removes b. deleteText runs
 *     cleanupFormattingGap over B bx N: with nothing left between them, B is
 *     overwritten by N and N is redundant; both are deleted.
 *   P (replica 2): insert "z" {bold} at 3 (after b). Bold is already in
 *     effect, so z(2:0) is placed between b and N with no marker of its own.
 * Merged: w v Bx bx z Nx, so z is plain: observed w v z.
 * Specification: z after b with bold; b deleted. Either order: w v z(bold).
 * Admitted: { w v z(bold) }.
 *
 * Control: D deletes [1,2) (v) instead. The gap cleanup runs over vx B and
 * keeps B, which is the last bold marker before b and changes the value:
 * w B b z N, so w b(bold) z(bold).
 */
const y003 = {
  schedule: concurrentPair([ins(1, 0, 'wv'), ins(1, 2, 'b', B)], del(1, 2, 1), ins(2, 3, 'z', B)),
  observed: v(['w'], ['v'], ['z']),
  admitted: [v(['w'], ['v'], ['z', B])],
};
const y003Control = {
  schedule: concurrentPair([ins(1, 0, 'wv'), ins(1, 2, 'b', B)], del(1, 1, 1), ins(2, 3, 'z', B)),
  observed: v(['w'], ['b', B], ['z', B]),
  admitted: [v(['w'], ['b', B], ['z', B])],
};

/*
 * Y-004 boundary spread.
 *
 * Replica 1 inserts "a" (1:0); sync. Concurrently:
 *   F (replica 1): format [0,1) italic: I(1:1) a In(1:2)
 *   P (replica 2): insert "h" (no attributes) at 0: h(2:0), origin null,
 *     right origin a.
 * I and h share origin null and right origin a; I precedes h: I h a In, so
 * h is italic: observed h(italic) a(italic).
 * Specification: h at the head with no attributes; F covers exactly a.
 * Either order: h a(italic). Admitted: { h a(italic) }.
 *
 * Control: P inserts h at 1 (after a). h and In share origin a and right
 * origin null; In precedes h: I a In h, so a(italic) h. (With the client
 * numbers swapped the spread would occur at the right boundary instead.)
 */
const y004 = {
  schedule: concurrentPair([ins(1, 0, 'a')], fmt(1, 0, 1, I), ins(2, 0, 'h')),
  observed: v(['h', I], ['a', I]),
  admitted: [v(['h'], ['a', I])],
};
const y004Control = {
  schedule: concurrentPair([ins(1, 0, 'a')], fmt(1, 0, 1, I), ins(2, 1, 'h')),
  observed: v(['a', I], ['h']),
  admitted: [v(['a', I], ['h'])],
};

/*
 * Y-005 overlapping same attribute.
 *
 * Replica 1 inserts "abc" (1:0 1:1 1:2); sync. Concurrently:
 *   F1 (replica 1): format [0,2) bold: B1 a b N1 c, N1 with origin b and
 *     right origin c.
 *   F2 (replica 2): format [1,3) bold: a B2 b c N2.
 * Merged: B1 a B2 b N1 c N2. N1 restores the value F1 saw after b (null)
 * inside F2's span, so c is plain. B2 (inside bold) and N2 (after c, where
 * bold is already null) stay live and change nothing. Observed
 * a(bold) b(bold) c.
 * Specification: both formats set bold; in either order a, b and c are
 * bold. Admitted: { a(bold) b(bold) c(bold) }.
 *
 * Control: F1 formats [0,3) instead. N1 now follows c (origin c, right
 * origin null) as does N2: B1 a B2 b c N1 N2, so all three are bold.
 */
const y005 = {
  schedule: concurrentPair([ins(1, 0, 'abc')], fmt(1, 0, 2, B), fmt(2, 1, 2, B)),
  observed: v(['a', B], ['b', B], ['c']),
  admitted: [v(['a', B], ['b', B], ['c', B])],
};
const y005Control = {
  schedule: concurrentPair([ins(1, 0, 'abc')], fmt(1, 0, 3, B), fmt(2, 1, 2, B)),
  observed: v(['a', B], ['b', B], ['c', B]),
  admitted: [v(['a', B], ['b', B], ['c', B])],
};

/** Folds the events at replica r in the given key order under `rule`; returns the view, or null on a failed precondition. */
function foldInOrder(schedule, r, order, rule) {
  const ex = new Execution(schedule.replicas, { checks: [] });
  for (const s of schedule.steps) ex.apply(s);
  const { events } = eventsAt(ex, r);
  const byKey = new Map(events.map((e) => [e.key, e]));
  assert.equal(order.length, events.length, 'the order does not name every event');
  const pos = new Map(order.map((k, i) => [k, i]));
  for (const e of events) for (const d of e.deps) assert.ok(pos.get(d) < pos.get(e.key), `${d} must precede ${e.key}`);
  let st = initial();
  for (const k of order) for (const op of byKey.get(k).specOps) {
    st = apply(st, op, rule);
    if (st === null) return null;
  }
  return view(st);
}

/** Witness results at every replica under the one-sided, two-sided and (default) gap rules. */
function observeRules(schedule) {
  const ex = new Execution(schedule.replicas, { checks: [] });
  for (const s of schedule.steps) ex.apply(s);
  const out = {};
  for (let r = 1; r <= schedule.replicas; r++) {
    const { events } = eventsAt(ex, r);
    const visible = ex.replica(r).visible();
    out[r] = {
      visible,
      left: { witness: findWitness(events, visible, { rule: 'left' }), admitted: allFinalViews(events, { rule: 'left' }) },
      both: { witness: findWitness(events, visible, { rule: 'both' }), admitted: allFinalViews(events, { rule: 'both' }) },
      gap: { witness: findWitness(events, visible), admitted: allFinalViews(events) },
    };
  }
  return out;
}

/*
 * The placement pair, first history: a specification result in plain text (not
 * a Yjs anomaly). The one-sided insertion rule admits no witness for a Yjs
 * history that the two-sided rule linearises.
 *
 * Ids: q 1:0, e 2:0, i 1:1, l 2:1, w 2:2, u 3:0. Recorded neighbours
 * (origin, right origin): q (none, none); e (none, none); i (q, none), q
 * being a tombstone at r1; l (e, none); w (none, e), since r2 inserts at the
 * head of "e l"; u (e, none), r3 having deleted q and e. Replica 3 receives
 * q and e before its delete. Yjs's list after sync: q i w e l u, so every
 * replica shows i w l u.
 *
 * One-sided rule (after the origin; a later sibling lands nearer it):
 *   - q, w and e are siblings at the head, displayed q (with its child i),
 *     then w, then e; a later head insert lands first, so w is applied before
 *     q (and e before w).
 *   - l and u are children of e, displayed l then u; so u is applied before l.
 *   - r2's program order gives l before w; r3 deletes q (so follows it) and
 *     then inserts u.
 *   u < l < w < q < r3's delete < u: a cycle, so no witness.
 * Two-sided rule (before the right origin when present, else after the
 * origin): the order e, q, r3's delete, u, l, w, r1's delete, i folds as
 *   [e] [q e] (q, e deleted) [q e u] [q e l u] [q w e l u] [q i w e l u],
 * showing i w l u.
 *
 * Control: r2 inserts w at index 1 instead (between e and l), so w records
 * (e, l). Yjs's list: q i e w l u, showing i w l u. One-sided: e, q, r3's
 * delete, u, l, w, r1's delete, i folds as [e] [q e] [q e u] [q e l u]
 * [q e w l u] [q i e w l u]; two-sided: the same order, w landing before l.
 * Expected view i w l u under both rules.
 *
 * The witness default is the gap rule (an insertion lands anywhere strictly
 * after its origin and strictly before its right origin); it admits both
 * the failing view and the control's, since every two-sided fold is also a
 * gap fold.
 */
const placementPairSteps = (wIndex) => [
  ins(1, 0, 'q'),
  ins(2, 0, 'e'),
  deliver(1, 3),
  deliver(2, 3),
  del(1, 0, 1),
  ins(1, 0, 'i'),
  ins(2, 1, 'l'),
  ins(2, wIndex, 'w'),
  del(3, 0, 2),
  ins(3, 0, 'u'),
  deliver(1, 3),
  deliver(2, 3),
  deliver(3, 1),
  deliver(3, 2),
];
const placementPair = { replicas: 3, steps: placementPairSteps(0) };
const placementPairControl = { replicas: 3, steps: placementPairSteps(1) };
const placementPairObserved = v(['i'], ['w'], ['l'], ['u']);
const placementPairOrder = ['r2#0', 'r1#0', 'r3#0', 'r3#1', 'r2#1', 'r2#2', 'r1#1', 'r1#2'];

/*
 * The admitted unbold: a format interval and a concurrent attributed insert.
 * A specification result: a failure under the one-sided rule only.
 *
 * r1 inserts c (1:0) and deletes it; r2 inserts d (2:0); r2's state reaches
 * r1. Then r1 inserts n {bold} at 0, recorded (c, d), and unbolds [0,2),
 * the interval n..d; concurrently r2 inserts q {bold} at 0, recorded
 * (none, d). Yjs: r1 has c(x) B n N d, and the unbold deletes B and N and
 * creates nothing. r2 has B2 q N2 d. B2 (origin none) follows c and c's
 * children, so the list is c(x) Bx n Nx B2 q N2 d: n q(bold) d.
 * One-sided rule: n is c's child. For q (a head insert) to stand after n, c
 * must be applied after q (c lands at the head); c precedes r1's unbold, so
 * q precedes the unbold, which covers q (q lies between n and d): n q d.
 * With q after c, q is at the head: q(bold) n d. Admitted { n q d,
 * q(bold) n d }: no witness for n q(bold) d.
 * Two-sided rule: n and q both land immediately before d, so n q d needs q
 * after n; the order d, c, delete c, n, unbold, q folds as [d] [c d] [c n d]
 * [c n d] (n unbolded) [c n q(bold) d]: n q(bold) d. Admitted { n q(bold) d,
 * n q d, q(bold) n d }.
 *
 * Control: q inserted with no attributes. Yjs: n q d. One-sided: the order
 * d, q, c, delete c, n, unbold folds to n q d; the two-sided order above
 * gives n q d as well.
 *
 * The witness default is the gap rule; every two-sided fold is a gap fold,
 * so it admits both n q(bold) d and the control's n q d.
 */
const admittedUnboldSteps = (qAttrs) => [
  ins(1, 0, 'c'),
  del(1, 0, 1),
  ins(2, 0, 'd'),
  deliver(2, 1),
  ins(1, 0, 'n', B),
  ins(2, 0, 'q', qAttrs),
  fmt(1, 0, 2, { bold: null }),
  deliver(1, 2),
  deliver(2, 1),
];
const admittedUnbold = { replicas: 2, steps: admittedUnboldSteps(B) };
const admittedUnboldControl = { replicas: 2, steps: admittedUnboldSteps({}) };
const admittedUnboldObserved = v(['n'], ['q', B], ['d']);
const admittedUnboldLeftAdmitted = [v(['n'], ['q'], ['d']), v(['q', B], ['n'], ['d'])];
const admittedUnboldBothAdmitted = [v(['n'], ['q', B], ['d']), v(['n'], ['q'], ['d']), v(['q', B], ['n'], ['d'])];

/*
 * The admitted unbold, the shape with the bold already in place. r1 inserts
 * "ab" (1:0 1:1); sync; r1 bolds [0,2): B(1:2) a b N(1:3); sync. Concurrently
 * r1 unbolds [0,2) and r2 inserts x {bold} at 1, recorded (a, b). At r2 bold is
 * in effect between a and b, so x creates no marker and sits inside B..N;
 * the unbold deletes B and N and creates nothing. Yjs: a x b, all plain.
 * Specification (either rule; x lands between a and b in every order):
 * insert first, then unbold: a x b; unbold first: a x(bold) b. Admitted
 * { a x b, a x(bold) b }; Yjs's view is admitted.
 */
const admittedUnboldInside = {
  replicas: 2,
  steps: [ins(1, 0, 'ab'), deliver(1, 2), fmt(1, 0, 2, B), deliver(1, 2), fmt(1, 0, 2, { bold: null }), ins(2, 1, 'x', B), deliver(1, 2), deliver(2, 1)],
};
const admittedUnboldInsideAdmitted = [v(['a'], ['x'], ['b']), v(['a'], ['x', B], ['b'])];

/*
 * The placement pair, second history: a specification result refuting the
 * two-sided rule.
 *
 * Ids: p 1:0, d 2:0, j 3:0, t 3:1; p, d and j are concurrent head inserts
 * with no recorded neighbours. Replica 3 receives p alone, sees p j (Yjs
 * orders concurrent head siblings by client) and inserts t at 1, recording
 * origin p and right origin j. Yjs, integrating d (origin none) at a replica
 * holding p t j: d passes p (lower client) and p's child t, and stops before
 * j (higher client): p t d j at every replica after sync.
 *
 * Two-sided rule: p, d, j land at the head, so their displayed order is the
 * reverse of their application order; t lands immediately before j, with the
 * precondition that its origin p does not stand after j. Admitted: the three
 * orders of p, d, j with p before j, t inserted immediately before j:
 *   p d t j, p t j d, d p t j.
 * d never stands between t and j, so p t d j has no witness.
 * One-sided rule: t lands immediately after p. Admitted: the six orders with
 * t immediately after p:
 *   p t d j, p t j d, d p t j, d j p t, j p t d, j d p t.
 * The order j, d, p, t folds [j] [d j] [p d j] [p t d j].
 * Gap rule (default): p, d, j have no recorded neighbours and may land
 * anywhere; t lands strictly between p and j, so p precedes j when t is
 * applied, and d may be anywhere. Admitted: d p t j, p d t j, p t d j,
 * p t j d. The same order j, d, p, t, placing t right after p, gives p t d j.
 *
 * Control: replica 3 inserts t at 2 instead (after j), recording origin j and
 * no right origin. Yjs: d stops before j as before, t follows j: p d j t.
 * One-sided and two-sided: t lands immediately after j; the order j, d, p, t
 * folds [j] [d j] [p d j] [p d j t]. Gap: t lands strictly after j; the same
 * order with t at the end gives p d j t. All three rules admit it.
 */
const placementPairBSteps = (tIndex) => [
  ins(1, 0, 'p'),
  ins(2, 0, 'd'),
  ins(3, 0, 'j'),
  { type: 'send', from: 1, to: 3, op: 0 },
  ins(3, tIndex, 't'),
  deliver(1, 2),
  deliver(1, 3),
  deliver(2, 1),
  deliver(2, 3),
  deliver(3, 1),
  deliver(3, 2),
];
const placementPairB = { replicas: 3, steps: placementPairBSteps(1) };
const placementPairBControl = { replicas: 3, steps: placementPairBSteps(2) };
const plainView = (s) => v(...[...s].map((ch) => [ch]));
const placementPairBObserved = plainView('ptdj');
const placementPairBBoth = ['pdtj', 'ptjd', 'dptj'].map(plainView);
const placementPairBLeft = ['ptdj', 'ptjd', 'dptj', 'djpt', 'jptd', 'jdpt'].map(plainView);
const placementPairBGap = ['dptj', 'pdtj', 'ptdj', 'ptjd'].map(plainView);
const placementPairBOrder = ['r3#0', 'r2#0', 'r1#0', 'r3#1'];

/** Runs a schedule (no final sync) and returns the execution. */
function run(schedule) {
  const ex = new Execution(schedule.replicas, { checks: [] });
  for (const s of schedule.steps) ex.apply(s);
  return ex;
}

/*
 * Marker-anchored insert, a specification result: the character an insert's
 * marker origin resolves to may be separated from the marker by a concurrent
 * insert, and the resolved gap still admits Yjs's order.
 *
 * r1 inserts a (1:0); sync. Concurrently:
 *   P (replica 2): insert "b" {bold} at 1. Bold is not in effect after a, so
 *     Yjs writes B(2:0) b(2:1) N(2:2), B with origin a and b with origin B:
 *     b's recorded origin is the marker B, resolved to a; no right origin.
 *   Z (replica 1): insert "z" at 1: z(1:1), origin a, no right origin.
 * B and z are siblings with origin a; z (client 1) precedes B (client 2), and
 * b and N follow B: a z B b N. Every replica shows a z b(bold). z lies
 * between b's resolved origin a and b's recorded origin B.
 * Specification (gap rule): b and z both land anywhere after a. P then Z:
 * a b(bold), then z after a: a z b(bold) or a b(bold) z. Z then P: a z, then
 * b after a: a b(bold) z or a z b(bold). Admitted { a z b(bold),
 * a b(bold) z }; Yjs's view is admitted. Resolving a marker origin to the
 * nearest character beyond it moves the bound past the marker, away from the
 * new character, so the resolved gap contains the marker-bounded one.
 *
 * Control: P inserts b with no attributes, so b's recorded origin is a
 * itself. Yjs: b (client 2) and z (client 1) are siblings with origin a, z
 * first: a z b. Admitted { a z b, a b z }, by the same two orders.
 */
const markerOriginSteps = (bAttrs) => [ins(1, 0, 'a'), deliver(1, 2), ins(2, 1, 'b', bAttrs), ins(1, 1, 'z'), deliver(1, 2), deliver(2, 1)];
const markerOrigin = { replicas: 2, steps: markerOriginSteps(B) };
const markerOriginControl = { replicas: 2, steps: markerOriginSteps({}) };

/*
 * Convergence control (claim 1): concurrent insert, format and delete
 * received in different orders by three replicas.
 *
 * r1 inserts "ab" (1:0 1:1); sync to r2 and r3. Concurrently:
 *   X (replica 1): insert "x" at 1: x(1:2), origin a, right origin b.
 *   F (replica 2): format [0,2) {bold}: B(2:0) with right origin a, a, b,
 *     N(2:1) with origin b.
 *   D (replica 3): delete [1,2), which deletes b.
 * Deliveries 1->2, 2->3, 3->1: r2 holds X and F, r3 and r1 hold all three.
 * Then 1->3, 2->1, 3->2 bring r2 the delete.
 * Yjs, at every replica after the last delivery: x lands between a and b
 * (its recorded neighbours), F's markers bound the identity interval a..b, so
 * x lies inside it, and b is deleted: B a x bx N, showing a(bold) x(bold).
 * Before the last round r2 lacks D: B a x b N, showing a(bold) x(bold)
 * b(bold), which differs from r1's a(bold) x(bold).
 * Specification: X before F: F covers a..b, which contains x: a(bold)
 * x(bold); X after F: x carries exactly its own attributes: a(bold) x. D
 * commutes with both. Admitted { a(bold) x(bold), a(bold) x }.
 */
const convergenceRound = [deliver(1, 2), deliver(2, 3), deliver(3, 1)];
const convergenceHead = [ins(1, 0, 'ab'), deliver(1, 2), deliver(1, 3), ins(1, 1, 'x'), fmt(2, 0, 2, B), del(3, 1, 1), ...convergenceRound];
const convergence = { replicas: 3, steps: [...convergenceHead, deliver(1, 3), deliver(2, 1), deliver(3, 2)] };
const convergenceObserved = v(['a', B], ['x', B]);
const convergenceAdmitted = [v(['a', B], ['x', B]), v(['a', B], ['x'])];

/*
 * Y-007 causal gap through a delete set (partial delivery). Yjs holds back a
 * struct until its clock predecessor and its origins are present, and applies
 * a delete set as soon as the items it names exist. Neither waits for a
 * causal predecessor whose update carries only a delete set, which is the
 * update of a delete and of a format that only removes markers. In plain text
 * the witness search accepts such a gap, since a delete needs only the
 * characters it names and a deleted character still anchors insertions;
 * with formatting it does not, because deleting a marker changes
 * attributes.
 *
 * Shape A, a marker-removing format ahead of the insert of its endpoint.
 * r1 inserts "a" {bold}: B(1:0) a(1:1) N(1:2). r1 inserts "b" at 1 with no
 * attributes: b(1:3) after N, no marker. r1 unbolds [a..b]: the opener B and
 * the closer N are deleted and no marker is written, so the update is the
 * delete set {1:0, 1:2} alone. r2 receives r1#0 (a(bold)) and then r1#2:
 * 1:0 and 1:2 exist, so both are deleted and nothing is pending; r2 shows a.
 * r2 has integrated {r1#0, r1#2}, and r1#2 depends on r1#1, which r2 has not
 * received.
 * Specification: r1#2 is format [a..b] {bold:null}; with b absent its
 * precondition fails in every order of {r1#0, r1#2}, so the admitted set is
 * empty. The causally closed versions containing r1#0 show a(bold) ({r1#0}),
 * a(bold) b ({r1#0, r1#1}) and a b (all three); a is none of them.
 * Control: r1#0, r1#1, r1#2 sent in issue order. One linear extension:
 * a(bold), then a(bold) b, then a b. Admitted { a b }, shown a b.
 *
 * Shape B, an insert ahead of the marker-removing format it was issued
 * after. r1 inserts "ab" {bold}: B(1:0) a(1:1) b(1:2) N(1:3); sync to r2.
 * r2 unbolds [a..b]: the update is the delete set {1:0, 1:3}. r2 inserts q
 * at 1 with no attributes: q(2:0), origin a, right origin b, and no marker,
 * since bold is not in effect at r2. r1 receives r2#1 only: q's clock is
 * client 2's first and its origins exist, so it is integrated between a and
 * b inside the live span B..N, and r1 shows a(bold) q(bold) b(bold).
 * r1 has integrated {r1#0, r2#1}, and r2#1 depends on r2#0.
 * Specification over {r1#0, r2#1}: q lands between a and b carrying exactly
 * {}: admitted { a(bold) q b(bold) }. The causally closed versions show
 * a(bold) b(bold) ({r1#0}), a b ({r1#0, r2#0}) and a q b (all three); the
 * observed view is none of them.
 * Control: r2#0 then r2#1 sent to r1. B and N are deleted, then q lands
 * between a and b: a q b. Admitted { a q b }.
 *
 * Both shapes converge after a full sync: both replicas then show a b in
 * shape A and a q b in shape B.
 */
const send = (from, to, op) => ({ type: 'send', from, to, op });
const y007ASteps = (order) => [ins(1, 0, 'a', B), ins(1, 1, 'b'), fmt(1, 0, 2, { bold: null }), ...order.map((k) => send(1, 2, k))];
const y007A = { replicas: 2, steps: y007ASteps([0, 2]) };
const y007AControl = { replicas: 2, steps: y007ASteps([0, 1, 2]) };
const y007BSteps = (order) => [ins(1, 0, 'ab', B), deliver(1, 2), fmt(2, 0, 2, { bold: null }), ins(2, 1, 'q'), ...order.map((k) => send(2, 1, k))];
const y007B = { replicas: 2, steps: y007BSteps([1]) };
const y007BControl = { replicas: 2, steps: y007BSteps([0, 1]) };

/** Admitted views of the causally closed version `keys` of an execution, with every dependency kept. */
function closedVersionViews(ex, keys) {
  const set = new Set(keys);
  const events = ex.ops.filter((o) => set.has(o.key)).map((o) => {
    for (const d of o.deps) assert.ok(set.has(d), `${o.key} depends on ${d}, outside the version`);
    return { key: o.key, deps: o.deps, specOps: o.kind === 'cleanup' ? [] : interpret(o) };
  });
  return allFinalViews(events);
}

/**
 * Y-007 assertions at the receiving replica `r`: Yjs holds nothing pending,
 * the tracked integrated set is `integrated` with exactly one causal gap,
 * the view is `observed` and not `before`, the admitted set is `admitted`,
 * no witness exists, the observed view is the view of none of the closed
 * versions `closed` ([keys, views]), and the classifier names no class.
 */
function y007Failing(schedule, r, { integrated, observed, before, admitted, closed }) {
  const ex = run(schedule);
  const rep = ex.replica(r);
  assert.equal(rep.doc.store.pendingStructs, null, 'Yjs holds structs pending');
  assert.equal(rep.doc.store.pendingDs, null, 'Yjs holds a delete set pending');
  assert.deepEqual([...ex.integrated[r]].sort(), integrated, 'integrated ops differ from the hand derivation');
  assert.deepEqual(ex.partial[r], [], 'an op is partly integrated');
  const { events, gaps } = eventsAt(ex, r);
  assert.equal(gaps, 1, 'not exactly one causal gap');
  const visible = rep.visible();
  assert.ok(viewsEqual(visible, observed), 'view is not the expected wrong outcome');
  assert.ok(!viewsEqual(visible, before), 'the gap op had no visible effect');
  const target = rep.visibleWithIds();
  assert.ok(sameViewSet(allFinalViews(events), admitted), 'admitted views differ from the hand derivation');
  assert.ok(sameViewSet(allFinalViews(events, { target }), admitted.filter((a) => a.length === target.length)), 'placement-directed admitted views differ');
  for (const a of admitted) assert.ok(!viewsEqual(visible, a), 'observed view is admitted');
  assert.equal(findWitness(events, target).found, false, 'witness unexpectedly found');
  for (const [keys, views] of closed) {
    const got = closedVersionViews(ex, keys);
    assert.ok(sameViewSet(got, views), `closed version ${keys}: views differ from the hand derivation`);
    for (const w of got) assert.ok(!viewsEqual(visible, w), `observed view is the view of closed version ${keys}`);
  }
  assert.equal(classifyAt(schedule, r).class, 'other', 'a mechanism class was assigned');
  const trace = execute(schedule);
  assert.equal(trace.checks.raLinearizability.pass, false, 'raLinearizability check passed');
  for (const c of ['convergence', 'conservation']) assert.equal(trace.checks[c].pass, true, `${c} check failed`);
  return visible;
}

/** Y-007 control assertions at replica `r`: no gap, `observed`, not `wrong`, admitted exactly `admitted`, a witness. */
function y007Control(schedule, r, { integrated, observed, wrong, admitted }) {
  const ex = run(schedule);
  assert.deepEqual([...ex.integrated[r]].sort(), integrated, 'integrated ops differ from the hand derivation');
  const { events, gaps } = eventsAt(ex, r);
  assert.equal(gaps, 0, 'a causal gap');
  const visible = ex.replica(r).visible();
  assert.ok(viewsEqual(visible, observed), 'view differs from the hand derivation');
  assert.ok(!viewsEqual(visible, wrong), "view is the failing case's outcome");
  assert.ok(sameViewSet(allFinalViews(events), admitted), 'admitted views differ from the hand derivation');
  assert.equal(findWitness(events, ex.replica(r).visibleWithIds()).found, true, 'no witness');
  const trace = execute(schedule);
  for (const c of ['convergence', 'raLinearizability', 'conservation']) assert.equal(trace.checks[c].pass, true, `${c} check failed on the control`);
  return visible;
}

export const REGRESSIONS = [
  {
    name: 'placement pair, second history (specification result, plain text): no witness under the two-sided rule, witnesses under the one-sided and gap rules',
    schedule: placementPairB,
    run(results) {
      const o = observeRules(placementPairB);
      for (const r of [1, 2, 3]) {
        assert.ok(viewsEqual(o[r].visible, placementPairBObserved), `replica ${r}: view is not p t d j`);
        assert.ok(!viewsEqual(o[r].visible, plainView('pdtj')), `replica ${r}: view is p d t j`);
        assert.ok(sameViewSet(o[r].both.admitted, placementPairBBoth), `replica ${r}: two-sided admitted views differ from the hand derivation`);
        for (const a of o[r].both.admitted) {
          const k = a.findIndex((e) => e.ch === 't');
          assert.equal(a[k + 1]?.ch, 'j', `replica ${r}: a two-sided view has t not immediately before j`);
        }
        assert.equal(o[r].both.witness.found, false, `replica ${r}: two-sided witness found`);
        assert.ok(sameViewSet(o[r].left.admitted, placementPairBLeft), `replica ${r}: one-sided admitted views differ from the hand derivation`);
        assert.equal(o[r].left.witness.found, true, `replica ${r}: no one-sided witness`);
        assert.ok(sameViewSet(o[r].gap.admitted, placementPairBGap), `replica ${r}: gap admitted views differ from the hand derivation`);
        assert.equal(o[r].gap.witness.found, true, `replica ${r}: no gap witness`);
      }
      assert.ok(viewsEqual(foldInOrder(placementPairB, 3, placementPairBOrder, 'left'), placementPairBObserved), 'the hand order does not fold to p t d j under the one-sided rule');
      assert.ok(!viewsEqual(foldInOrder(placementPairB, 3, placementPairBOrder, 'both') ?? [], placementPairBObserved), 'the hand order folds to p t d j under the two-sided rule');
      results.observed = o[1].visible;
      results.admitted = placementPairBBoth;
    },
  },
  {
    name: 'control for the second placement history: t recorded after j, all three rules admit the view',
    schedule: placementPairBControl,
    run(results) {
      const o = observeRules(placementPairBControl);
      for (const r of [1, 2, 3]) {
        assert.ok(viewsEqual(o[r].visible, plainView('pdjt')), `replica ${r}: view is not p d j t`);
        assert.ok(!viewsEqual(o[r].visible, placementPairBObserved), `replica ${r}: view is p t d j`);
        for (const rule of ['left', 'both', 'gap']) assert.equal(o[r][rule].witness.found, true, `replica ${r}: no ${rule} witness`);
      }
      for (const rule of ['left', 'both'])
        assert.ok(viewsEqual(foldInOrder(placementPairBControl, 3, placementPairBOrder, rule), plainView('pdjt')), `the hand order does not fold to p d j t under ${rule}`);
      results.observed = o[1].visible;
      const trace = execute(placementPairBControl);
      for (const c of ['convergence', 'raLinearizability', 'localMeaning', 'conservation'])
        assert.equal(trace.checks[c].pass, true, `${c} check failed on the control`);
    },
  },
  {
    name: 'placement pair, first history (specification result, plain text), sibling order: no witness under the one-sided rule, a witness under the two-sided rule',
    schedule: placementPair,
    run(results) {
      const o = observeRules(placementPair);
      for (const r of [1, 2, 3]) {
        assert.ok(viewsEqual(o[r].visible, placementPairObserved), `replica ${r}: view is not i w l u`);
        assert.ok(!viewsEqual(o[r].visible, v(['i'], ['l'], ['w'], ['u'])), `replica ${r}: view is i l w u`);
        assert.equal(o[r].left.witness.found, false, `replica ${r}: one-sided witness found`);
        for (const a of o[r].left.admitted) assert.ok(!viewsEqual(a, placementPairObserved), `replica ${r}: one-sided rule admits the view`);
        assert.equal(o[r].both.witness.found, true, `replica ${r}: no two-sided witness`);
      }
      assert.ok(viewsEqual(foldInOrder(placementPair, 3, placementPairOrder, 'both'), placementPairObserved), 'the hand order does not fold to i w l u under the two-sided rule');
      assert.ok(!viewsEqual(foldInOrder(placementPair, 3, placementPairOrder, 'left') ?? [], placementPairObserved), 'the hand order folds to i w l u under the one-sided rule');
      results.observed = o[1].visible;
      const trace = execute(placementPair);
      assert.equal(trace.checks.convergence.pass, true, 'convergence check failed');
      assert.equal(trace.checks.raLinearizability.pass, true, 'raLinearizability check failed under the default rule');
    },
  },
  {
    name: 'control for the first placement history: w recorded after e, both rules admit the view',
    schedule: placementPairControl,
    run(results) {
      const o = observeRules(placementPairControl);
      for (const r of [1, 2, 3]) {
        assert.ok(viewsEqual(o[r].visible, placementPairObserved), `replica ${r}: view is not i w l u`);
        assert.ok(!viewsEqual(o[r].visible, v(['i'], ['l'], ['w'], ['u'])), `replica ${r}: view is i l w u`);
        assert.equal(o[r].left.witness.found, true, `replica ${r}: no one-sided witness`);
        assert.equal(o[r].both.witness.found, true, `replica ${r}: no two-sided witness`);
      }
      for (const rule of ['left', 'both'])
        assert.ok(viewsEqual(foldInOrder(placementPairControl, 3, placementPairOrder, rule), placementPairObserved), `the hand order does not fold to i w l u under ${rule}`);
      results.observed = o[1].visible;
      const trace = execute(placementPairControl);
      for (const c of ['convergence', 'raLinearizability', 'localMeaning', 'conservation'])
        assert.equal(trace.checks[c].pass, true, `${c} check failed on the control`);
    },
  },
  {
    name: 'admitted unbold (specification result): an unbold interval and a concurrent bold insert: no witness under the one-sided rule only',
    schedule: admittedUnbold,
    run(results) {
      const o = observeRules(admittedUnbold);
      for (const r of [1, 2]) {
        assert.ok(viewsEqual(o[r].visible, admittedUnboldObserved), `replica ${r}: view is not n q(bold) d`);
        assert.ok(!viewsEqual(o[r].visible, v(['n'], ['q'], ['d'])), `replica ${r}: view is n q d`);
        assert.ok(sameViewSet(o[r].left.admitted, admittedUnboldLeftAdmitted), `replica ${r}: one-sided admitted views differ from the hand derivation`);
        assert.equal(o[r].left.witness.found, false, `replica ${r}: one-sided witness found`);
        assert.ok(sameViewSet(o[r].both.admitted, admittedUnboldBothAdmitted), `replica ${r}: two-sided admitted views differ from the hand derivation`);
        assert.equal(o[r].both.witness.found, true, `replica ${r}: no two-sided witness`);
      }
      assert.ok(viewsEqual(foldInOrder(admittedUnbold, 1, ['r2#0', 'r1#0', 'r1#1', 'r1#2', 'r1#3', 'r2#1'], 'both'), admittedUnboldObserved), 'the hand order does not fold to n q(bold) d');
      results.observed = o[1].visible;
      results.admitted = admittedUnboldLeftAdmitted;
    },
  },
  {
    name: 'control for the admitted unbold: the concurrent insert carries no attributes',
    schedule: admittedUnboldControl,
    run(results) {
      const o = observeRules(admittedUnboldControl);
      for (const r of [1, 2]) {
        assert.ok(viewsEqual(o[r].visible, v(['n'], ['q'], ['d'])), `replica ${r}: view is not n q d`);
        assert.ok(!viewsEqual(o[r].visible, admittedUnboldObserved), `replica ${r}: view is n q(bold) d`);
        assert.equal(o[r].left.witness.found, true, `replica ${r}: no one-sided witness`);
        assert.equal(o[r].both.witness.found, true, `replica ${r}: no two-sided witness`);
      }
      assert.ok(viewsEqual(foldInOrder(admittedUnboldControl, 1, ['r2#0', 'r2#1', 'r1#0', 'r1#1', 'r1#2', 'r1#3'], 'left'), v(['n'], ['q'], ['d'])), 'the one-sided hand order does not fold to n q d');
      results.observed = o[1].visible;
      const trace = execute(admittedUnboldControl);
      for (const c of ['convergence', 'raLinearizability', 'localMeaning', 'conservation'])
        assert.equal(trace.checks[c].pass, true, `${c} check failed on the control`);
    },
  },
  {
    name: 'admitted unbold with the bold in place: the concurrent insert reuses the opener and Yjs shows an admitted view',
    schedule: admittedUnboldInside,
    run(results) {
      const o = observeRules(admittedUnboldInside);
      for (const r of [1, 2]) {
        assert.ok(viewsEqual(o[r].visible, v(['a'], ['x'], ['b'])), `replica ${r}: view is not a x b`);
        assert.ok(!viewsEqual(o[r].visible, v(['a'], ['x', B], ['b'])), `replica ${r}: view is a x(bold) b`);
        for (const rule of ['left', 'both']) {
          assert.ok(sameViewSet(o[r][rule].admitted, admittedUnboldInsideAdmitted), `replica ${r}: ${rule} admitted views differ from the hand derivation`);
          assert.equal(o[r][rule].witness.found, true, `replica ${r}: no ${rule} witness`);
        }
      }
      results.observed = o[1].visible;
      results.admitted = admittedUnboldInsideAdmitted;
    },
  },
  {
    name: 'Y-001 concurrent overlapping bold and unbold: Yjs view outside the admitted set',
    schedule: overlapSchedule,
    run(results) {
      const o = observe(overlapSchedule);
      for (const r of [1, 2]) {
        assert.ok(sameViewSet(o[r].admitted, overlapAdmitted), `replica ${r}: admitted views differ from the hand derivation`);
        assert.ok(!sameViewSet(o[r].admitted, [overlapBelieved]), `replica ${r}: admitted set must not be the all-bold view`);
        for (const a of overlapAdmitted) assert.ok(!viewsEqual(o[r].visible, a), `replica ${r}: observed view is admitted`);
        assert.equal(o[r].witness.found, false, `replica ${r}: witness unexpectedly found`);
        assert.equal(classifyAt(overlapSchedule, r).class, 'Y-001', `replica ${r}: classified otherwise`);
      }
      results.observed = o[1].visible;
      results.observedMatchesBelief = viewsEqual(o[1].visible, overlapBelieved);
      results.admitted = overlapAdmitted;
      const trace = execute(overlapSchedule);
      assert.equal(trace.checks.raLinearizability.pass, false, 'raLinearizability check passed');
      assert.equal(trace.checks.convergence.pass, true, 'convergence check failed');
    },
  },
  {
    name: 'control: the same formats issued sequentially on one replica',
    schedule: controlSchedule,
    run(results) {
      const o = observe(controlSchedule);
      for (const r of [1, 2]) {
        assert.ok(viewsEqual(o[r].visible, controlExpected), `replica ${r}: view differs from a(bold) b c`);
        assert.ok(!viewsEqual(o[r].visible, overlapBelieved), `replica ${r}: view is all bold`);
        assert.ok(!viewsEqual(o[r].visible, v(['a', B], ['b', B], ['c'])), `replica ${r}: view is a(bold) b(bold) c`);
        assert.equal(o[r].witness.found, true, `replica ${r}: no witness`);
        assert.ok(sameViewSet(o[r].admitted, [controlExpected]), `replica ${r}: admitted set is not exactly a(bold) b c`);
      }
      results.observed = o[1].visible;
      const trace = execute(controlSchedule);
      for (const c of ['convergence', 'raLinearizability', 'localMeaning', 'conservation'])
        assert.equal(trace.checks[c].pass, true, `${c} check failed on the control`);
    },
  },
  {
    name: 'marker-anchored insert (specification result): a concurrent insert between the resolved character and the marker is admitted',
    schedule: markerOrigin,
    run(results) {
      const ex = run(markerOrigin);
      const b = ex.ops.find((o) => o.key === 'r2#0').chars[0];
      assert.deepEqual(b.yOrigin, [2, 0], 'b is not recorded after the marker 2:0');
      assert.deepEqual(b.origin, [1, 0], 'the marker origin does not resolve to a');
      assert.notDeepEqual(b.origin, b.yOrigin, 'the recorded and resolved origins coincide');
      const walk = ex.replica(1).items().map((it) => `${it.id[0]}:${it.id[1]}`);
      assert.deepEqual(walk, ['1:0', '2:0', '2:1', '2:2'], 'item list is not az B b N');
      assert.equal(ex.replica(1).items()[0].str, 'az', 'z is not merged into a\'s item before the marker');
      const admitted = [v(['a'], ['z'], ['b', B]), v(['a'], ['b', B], ['z'])];
      const o = observe(markerOrigin);
      for (const r of [1, 2]) {
        assert.ok(viewsEqual(o[r].visible, admitted[0]), `replica ${r}: view is not a z b(bold)`);
        assert.ok(!viewsEqual(o[r].visible, admitted[1]), `replica ${r}: view is a b(bold) z`);
        assert.ok(sameViewSet(o[r].admitted, admitted), `replica ${r}: admitted views differ from the hand derivation`);
        assert.equal(o[r].witness.found, true, `replica ${r}: no witness`);
      }
      results.observed = o[1].visible;
      results.admitted = admitted;
      const trace = execute(markerOrigin);
      for (const c of ['convergence', 'raLinearizability', 'localMeaning', 'conservation'])
        assert.equal(trace.checks[c].pass, true, `${c} check failed`);
    },
  },
  {
    name: 'control for the marker-anchored insert: the insert carries no attributes and is recorded after a',
    schedule: markerOriginControl,
    run(results) {
      const ex = run(markerOriginControl);
      const b = ex.ops.find((o) => o.key === 'r2#0').chars[0];
      assert.deepEqual(b.yOrigin, [1, 0], 'b is not recorded after a');
      assert.deepEqual(b.origin, b.yOrigin, 'the recorded and resolved origins differ');
      assert.equal(ex.replica(1).items().some((it) => it.kind === 'format'), false, 'a marker was written');
      const admitted = [v(['a'], ['z'], ['b']), v(['a'], ['b'], ['z'])];
      const o = observe(markerOriginControl);
      for (const r of [1, 2]) {
        assert.ok(viewsEqual(o[r].visible, admitted[0]), `replica ${r}: view is not a z b`);
        assert.ok(!viewsEqual(o[r].visible, admitted[1]), `replica ${r}: view is a b z`);
        assert.ok(sameViewSet(o[r].admitted, admitted), `replica ${r}: admitted views differ from the hand derivation`);
        assert.equal(o[r].witness.found, true, `replica ${r}: no witness`);
      }
      results.observed = o[1].visible;
      results.admitted = admitted;
    },
  },
  {
    name: 'convergence control (claim 1): concurrent insert, format and delete received in different orders by three replicas',
    schedule: convergence,
    run(results) {
      const head = run({ replicas: 3, steps: convergenceHead });
      const before = [1, 2, 3].map((r) => head.replica(r).visible());
      assert.ok(viewsEqual(before[0], convergenceObserved), 'replica 1 before the last round is not a(bold) x(bold)');
      assert.ok(viewsEqual(before[1], v(['a', B], ['x', B], ['b', B])), 'replica 2 before the last round is not a(bold) x(bold) b(bold)');
      assert.ok(!viewsEqual(before[0], before[1]), 'replicas 1 and 2 agree before the last round');
      const o = observe(convergence);
      for (const r of [1, 2, 3]) {
        assert.ok(viewsEqual(o[r].visible, convergenceObserved), `replica ${r}: view is not a(bold) x(bold)`);
        assert.ok(!viewsEqual(o[r].visible, v(['a', B], ['x'])), `replica ${r}: view is a(bold) x`);
        assert.ok(viewsEqual(o[r].visible, o[1].visible), `replica ${r} differs from replica 1`);
        assert.ok(sameViewSet(o[r].admitted, convergenceAdmitted), `replica ${r}: admitted views differ from the hand derivation`);
        assert.equal(o[r].witness.found, true, `replica ${r}: no witness`);
      }
      results.observed = o[1].visible;
      results.admitted = convergenceAdmitted;
      const trace = execute(convergence);
      for (const [c, res] of Object.entries(trace.checks)) assert.equal(res.pass, true, `${c} check failed`);
      assert.deepEqual(Object.keys(trace.checks).sort(), ['conservation', 'convergence', 'determinism', 'localMeaning', 'raLinearizability'], 'a check did not run');
    },
  },
  ...pairOf('Y-001', 'insert relying on an opener a concurrent unbold deletes', y001Insert, y001InsertControl, 'the unbold stops before the last character'),
  ...pairOf('Y-002', 'concurrent nested bolds: the outer opener is judged overwritten', y002Formats, y002FormatsControl, 'both bolds cover the same range'),
  ...pairOf('Y-002', 'bold insert at the head beside a concurrent bold format', y002Insert, y002InsertControl, 'the insert goes after the formatted character'),
  ...pairOf('Y-003', 'deleting a bold character strips a concurrent bold insert after it', y003, y003Control, 'the delete removes a character before the markers'),
  ...pairOf('Y-004', 'plain insert at the left boundary of a concurrent italic', y004, y004Control, 'the insert is at the right boundary'),
  ...pairOf('Y-005', 'overlapping concurrent bolds leave the last character plain', y005, y005Control, 'the first bold covers the second'),
  {
    name: 'Y-007 (partial delivery) a marker-removing format applied before the insert of its endpoint',
    schedule: y007A,
    run(results) {
      const ex = run(y007A);
      const f = ex.ops.find((o) => o.key === 'r1#2');
      assert.deepEqual(f.effect.structs, [], 'the format writes a marker');
      assert.deepEqual(f.effect.deletes, [{ client: 1, clock: 0, len: 1 }, { client: 1, clock: 2, len: 1 }], 'the format does not delete exactly B and N');
      results.observed = y007Failing(y007A, 2, {
        integrated: ['r1#0', 'r1#2'],
        observed: v(['a']),
        before: v(['a', B]),
        admitted: [],
        closed: [[['r1#0'], [v(['a', B])]], [['r1#0', 'r1#1'], [v(['a', B], ['b'])]], [['r1#0', 'r1#1', 'r1#2'], [v(['a'], ['b'])]]],
      });
      results.admitted = [];
    },
  },
  {
    name: 'control for Y-007 shape A: the three ops sent in issue order',
    schedule: y007AControl,
    run(results) {
      results.observed = y007Control(y007AControl, 2, { integrated: ['r1#0', 'r1#1', 'r1#2'], observed: v(['a'], ['b']), wrong: v(['a']), admitted: [v(['a'], ['b'])] });
      results.admitted = [v(['a'], ['b'])];
    },
  },
  {
    name: 'Y-007 (partial delivery) an insert applied before the marker-removing format it was issued after',
    schedule: y007B,
    run(results) {
      const ex = run(y007B);
      const f = ex.ops.find((o) => o.key === 'r2#0');
      assert.deepEqual(f.effect.structs, [], 'the format writes a marker');
      assert.deepEqual(ex.ops.find((o) => o.key === 'r2#1').deps, ['r1#0', 'r2#0'], 'q is not issued after the format');
      const admitted = [v(['a', B], ['q'], ['b', B])];
      results.observed = y007Failing(y007B, 1, {
        integrated: ['r1#0', 'r2#1'],
        observed: v(['a', B], ['q', B], ['b', B]),
        before: v(['a', B], ['b', B]),
        admitted,
        closed: [[['r1#0'], [v(['a', B], ['b', B])]], [['r1#0', 'r2#0'], [v(['a'], ['b'])]], [['r1#0', 'r2#0', 'r2#1'], [v(['a'], ['q'], ['b'])]]],
      });
      results.admitted = admitted;
    },
  },
  {
    name: 'control for Y-007 shape B: the format sent before the insert',
    schedule: y007BControl,
    run(results) {
      results.observed = y007Control(y007BControl, 1, { integrated: ['r1#0', 'r2#0', 'r2#1'], observed: v(['a'], ['q'], ['b']), wrong: v(['a', B], ['q', B], ['b', B]), admitted: [v(['a'], ['q'], ['b'])] });
      results.admitted = [v(['a'], ['q'], ['b'])];
    },
  },
];

/** Runs every regression; returns [{ name, pass, error?, results }]. */
export function runRegressions() {
  return runAll(REGRESSIONS);
}

if (process.argv[1] && fileURLToPath(import.meta.url) === process.argv[1]) {
  const out = runRegressions();
  for (const r of out) console.log(`${r.pass ? 'ok  ' : 'FAIL'} ${r.name}${r.pass ? '' : ': ' + r.error}`);
  if (out.some((r) => !r.pass)) process.exitCode = 1;
}
