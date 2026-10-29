/**
 * Hand-derived minimal schedules with predicted outcomes on the production
 * Notion text instance. Each case states the specification's admitted final
 * views (derived in the comment above it), the view the shipped code is
 * predicted to display, whether a witness exists, and the tempting wrong view
 * that must not be shown (the Yjs outcome, the rival reading's verdict).
 * Every failing case carries a passing control that changes one ingredient.
 *
 * Mechanism used in the derivations (modules 458789, 508649, 519193, 499116,
 * 300957): ids are [session, counter], the counter a Lamport clock, compared
 * counter first and then session; an insertion goes after its origin (its
 * visible left neighbour, 'start' at index 0), past every following item
 * with a greater id (RGA); a bold (addition or removal) of [i, j) is anchored
 * 'before' character i and 'before' the item following character j - 1 (a
 * tombstone or the end); a character's bold is decided by the annotation
 * operations in force at the last anchor before it, applied in id order, so
 * the greatest id wins. Sessions are s1, s2, s3 for replicas 1, 2, 3, and s1 <
 * s2 < s3. Bold requests are toggles.
 *
 * Notation: x* is a bold x. Run: node run.mjs --mode regressions.
 */
import assert from 'node:assert/strict';
import { cpSync, mkdtempSync, rmSync, writeFileSync, readFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { runRegression, Execution, prepareInstance, execute as executeWith } from '../../ra-pbt/src/index.js';
import { instanceFor, execute, parseView, renderView, viewKey, normaliseView, verifySources, items } from '../../ra-pbt/instances/notion-production-text/index.js';
import { classifyTrace } from '../../ra-pbt/instances/notion-production-text/classify.js';
import { libraryPath } from '../../ra-pbt/instances/notion-production-text/library.js';
import { yieldToTimers } from './search.mjs';
import { unbuffered } from './out-of-order.mjs';

const ins = (replica, index, text) => ({ type: 'edit', replica, kind: 'insert', index, text });
const del = (replica, start, end) => ({ type: 'edit', replica, kind: 'delete', start, end });
const bold = (replica, start, end) => ({ type: 'edit', replica, kind: 'bold', start, end });
const deliver = (from, to) => ({ type: 'deliver', from, to });
const send = (from, to, op) => ({ type: 'send', from, to, op });
const open = (replica, from) => ({ type: 'open', replica, from });
/** Two replicas: `prefix` at replica 1, sync, the concurrent pair, sync both ways. */
const pair = (prefix, op1, op2) => ({ replicas: 2, steps: [...prefix, deliver(1, 2), op1, op2, deliver(1, 2), deliver(2, 1)] });
const views = (...ss) => ss.map(parseView);

const ANCHORED = {};
const INHERIT = { local: 'inherit' };
const INTERVAL = { reading: 'interval', local: 'inherit' };

/**
 * A declared case under a specification configuration: checked by ra-pbt's
 * checkDeclared (observed view at every replica, admitted set, witness
 * verdict, excluded views, controls), plus, when `checks` is given, the
 * outcome of each named check on the full execution, and, when `classes` is
 * given, the classes the classifier assigns to its failures.
 */
function declared(name, config, c) {
  const inst = instanceFor(config);
  return {
    name,
    run(results) {
      const decl = { ...c, observed: parseView(c.observed), admitted: c.admitted.map(parseView), notObserved: (c.notObserved ?? []).map(parseView) };
      const r = runRegression(inst, decl);
      if (!r.pass) throw new Error(r.error);
      if (c.checks) {
        const trace = execute(c.schedule, {}, config);
        for (const [check, pass] of Object.entries(c.checks)) assert.equal(trace.checks[check].pass, pass, `${check} ${pass ? 'failed' : 'passed'}`);
        if (c.classes) assert.deepEqual([...new Set(classifyTrace(inst, c.schedule, trace.checks).map((x) => x.class))].sort(), c.classes, 'classes differ');
      }
      results.observed = c.observed;
      results.admitted = c.admitted;
    },
  };
}

const cases = [];

/*
 * Y-001 re-expressed: concurrent overlapping bold and unbold.
 * r1 inserts "abc" (s1:1..3) and toggles [1,3): b, c plain, so an addition
 * s1:4 from before b to before end; sync. Concurrently r1 toggles [0,2) (a
 * plain, so an addition F1 = s1:5 from before a to before c) and r2 toggles
 * [1,3) (b, c bold, so a removal F2 = s2:5 from before b to before end).
 * Specification (anchored): F1 then F2: a* b c; F2 then F1: a* b* c.
 * Admitted { a* b c, a* b* c }; c is bold in neither. Shipped code: F2 and F1
 * both have counter 5, s2 > s1, so F2 is applied last on b: a* b c.
 * Yjs showed a* b* c* (marker ownership).
 * Control: F2 issued by r1 after F1 (sequential): F1 a* b* c*, then the
 * toggle of [1,3) removes: a* b c, the single admitted view.
 */
cases.push(declared('Y-001 re-expressed: concurrent bold [0,2) and unbold [1,3) from a b* c*', ANCHORED, {
  schedule: pair([ins(1, 0, 'abc'), bold(1, 1, 3)], bold(1, 0, 2), bold(2, 1, 3)),
  observed: 'a*bc',
  admitted: ['a*bc', 'a*b*c'],
  witness: true,
  notObserved: ['a*b*c*'],
  checks: { raLinearizability: true, convergence: true, localMeaning: true, determinism: true, conservation: true },
  controls: [{ name: 'sequential', schedule: { replicas: 2, steps: [ins(1, 0, 'abc'), bold(1, 1, 3), bold(1, 0, 2), bold(1, 1, 3), deliver(1, 2)] }, observed: parseView('a*bc'), admitted: [parseView('a*bc')], notObserved: [parseView('a*b*c')], witness: true }],
}));

/*
 * Y-002 re-expressed, two formats. r1 inserts "au"; sync. Concurrently r1
 * bolds [0,2) (s1:3, before a to before end) and r2 bolds [0,1) (s2:3,
 * before a to before u). Both are additions: a and u are bold in every
 * order. Admitted { a* u* }. Shipped: a is covered by both, u by the first:
 * a* u*. Yjs showed a* u (opening marker judged redundant).
 */
cases.push(declared('Y-002 re-expressed: concurrent bold [0,2) and bold [0,1) of au', ANCHORED, {
  schedule: pair([ins(1, 0, 'au')], bold(1, 0, 2), bold(2, 0, 1)),
  observed: 'a*u*',
  admitted: ['a*u*'],
  witness: true,
  notObserved: ['a*u'],
  checks: { raLinearizability: true, convergence: true },
}));

/*
 * Y-002 re-expressed, insert and format. An insertion carries no formatting
 * request, so the bold insert becomes an insertion followed by a bold. r1
 * inserts "q" (s1:1); sync. Concurrently r1 bolds [0,1) (s1:2, before q to
 * before end) and r2 inserts "z" at 0 (s2:2, origin start) and bolds [0,1)
 * (s2:3, before z to before q). Shipped: z and q are siblings after start,
 * z has the greater id: z q; each is covered by its own bold: z* q*.
 * Admitted { z* q* }. Yjs showed z* q.
 */
cases.push(declared('Y-002 re-expressed: bold q concurrent with a bold z inserted at 0', ANCHORED, {
  schedule: { replicas: 2, steps: [ins(1, 0, 'q'), deliver(1, 2), bold(1, 0, 1), ins(2, 0, 'z'), bold(2, 0, 1), deliver(1, 2), deliver(2, 1)] },
  observed: 'z*q*',
  admitted: ['z*q*'],
  witness: true,
  notObserved: ['z*q'],
  checks: { raLinearizability: true, convergence: true },
}));

/*
 * Y-003 re-expressed: a delete next to a bold span. r1 inserts "wvb"
 * (s1:1..3) and bolds [2,3) (s1:4, before b to before end); sync.
 * Concurrently r1 deletes b and r2 inserts "z" at 3 (s2:5, origin b), which
 * inherits b's bold on r2. Shipped: z goes after b, inside the range, and the
 * range survives the deletion of b (anchors stay on tombstones): w v z*.
 * Admitted { w v z* } (z lies in [before b, before end) in every order).
 * Yjs showed w v z.
 */
cases.push(declared('Y-003 re-expressed: delete a bold b concurrent with an insert after it', ANCHORED, {
  schedule: pair([ins(1, 0, 'wvb'), bold(1, 2, 3)], del(1, 2, 3), ins(2, 3, 'z')),
  observed: 'wvz*',
  admitted: ['wvz*'],
  witness: true,
  notObserved: ['wvz'],
  checks: { raLinearizability: true, convergence: true, conservation: true },
}));

/*
 * Y-004 re-expressed at the left boundary. r1 inserts "a"; sync.
 * Concurrently r1 bolds [0,1) (s1:2, before a to before end) and r2 inserts
 * "h" at 0 (s2:2, origin start). Shipped: h and a are siblings after start,
 * h has the greater id, so h precedes a and its before anchor: h a*.
 * Admitted { h a* }. Yjs showed h* a* (boundary spread).
 */
cases.push(declared('Y-004 re-expressed: plain insert at the left boundary of a concurrent bold', ANCHORED, {
  schedule: pair([ins(1, 0, 'a')], bold(1, 0, 1), ins(2, 0, 'h')),
  observed: 'ha*',
  admitted: ['ha*'],
  witness: true,
  notObserved: ['h*a*'],
  checks: { raLinearizability: true, convergence: true },
}));

/*
 * Y-005 re-expressed: overlapping same attribute. r1 inserts "abc"; sync.
 * Concurrently r1 bolds [0,2) (s1:4, before a to before c) and r2 bolds
 * [1,3) (s2:4, before b to before end). Both additions: a* b* c* in every
 * order, and shipped. Yjs showed a* b* c (issue #382).
 */
cases.push(declared('Y-005 re-expressed: concurrent bold [0,2) and bold [1,3) of abc', ANCHORED, {
  schedule: pair([ins(1, 0, 'abc')], bold(1, 0, 2), bold(2, 1, 3)),
  observed: 'a*b*c*',
  admitted: ['a*b*c*'],
  witness: true,
  notObserved: ['a*b*c'],
  checks: { raLinearizability: true, convergence: true },
}));

/*
 * NT-3, the right boundary (the mirror of Y-004). r1 inserts "a"; sync.
 * Concurrently r1 bolds [0,1) (s1:2, before a to before end) and r2 inserts
 * "h" at 1 (s2:2, origin a), plain on r2. Shipped: h goes after a, before the
 * end item, so inside the range: a* h*.
 * Anchored: h lies in [before a, before end) whenever the view is read:
 * admitted { a* h* }. Interval: the bold covers a..a; h carries plain:
 * admitted { a* h }, so no witness for a* h*.
 * Session order does not enter: the same outcome with the roles swapped
 * (r1 inserts, r2 bolds) is the control, and both have a witness under the
 * anchored reading.
 */
const rightBoundary = pair([ins(1, 0, 'a')], bold(1, 0, 1), ins(2, 1, 'h'));
const rightBoundarySwapped = pair([ins(1, 0, 'a')], ins(1, 1, 'h'), bold(2, 0, 1));
cases.push(declared('NT-3: plain insert at the right boundary of a concurrent bold, anchored reading', ANCHORED, {
  schedule: rightBoundary,
  observed: 'a*h*',
  admitted: ['a*h*'],
  witness: true,
  notObserved: ['a*h'],
  checks: { raLinearizability: true, convergence: true },
  controls: [{ name: 'roles swapped', schedule: rightBoundarySwapped, observed: parseView('a*h*'), admitted: [parseView('a*h*')], witness: true }],
}));
cases.push(declared('NT-3: the same history under the interval reading has no witness', INTERVAL, {
  schedule: rightBoundary,
  observed: 'a*h*',
  admitted: ['a*h'],
  witness: false,
  checks: { raLinearizability: false, convergence: true, localMeaning: true },
  classes: ['NT-3'],
  controls: [{ name: 'insert at the left boundary instead', schedule: pair([ins(1, 0, 'a')], bold(1, 0, 1), ins(2, 0, 'h')), observed: parseView('ha*'), admitted: [parseView('ha*')], witness: true }],
}));

/*
 * NT-3, a gap filled by a concurrent head insert: r1 inserts "l" (s1:1) and toggles it twice, an addition Fb
 * (s1:2) and a removal Fu (s1:3), both from before l to before end; r3
 * inserts "ja" (s3:1..2) and bolds [1,2), F3 (s3:3) from before a to
 * before end. Shipped after sync: the head siblings are ordered j (s3:1)
 * before l (s1:1), so j a l; l lies before end, inside F3's range, and
 * s3:3 > s1:3, so F3 decides l: j a* l*.
 * Anchored: l, j and a may land in the orders l j a, j l a, j a l (a after
 * j). Fb and Fu cover everything from l on, F3 everything from a on; a
 * character takes the last-applied covering annotation, Fu always after Fb,
 * F3 before or after Fu:
 *   l j a: l, j plain (Fu); a* or a      -> l j a*, l j a
 *   j l a: j, l plain; a* or a           -> j l a*, j l a
 *   j a l: j plain; a* (F3 only); l* or l -> j a* l*, j a* l
 * Interval: Fb and Fu set and clear l alone, F3 sets a alone, inserted
 * characters carry plain: l j a*, j l a*, j a* l; no witness for j a* l*.
 */
const headGap = { replicas: 3, steps: [ins(1, 0, 'l'), bold(1, 0, 1), bold(1, 0, 1), ins(3, 0, 'ja'), bold(3, 1, 2), deliver(1, 3), deliver(3, 1)] };
cases.push(declared('NT-3: a concurrent head insert ordered into a bold end gap, interval reading', INTERVAL, {
  schedule: headGap,
  replicas: [1, 3],
  observed: 'ja*l*',
  admitted: ['lja*', 'jla*', 'ja*l'],
  witness: false,
  notObserved: ['ja*l'],
}));
cases.push(declared('NT-3 control: the head insert under the anchored reading', INHERIT, {
  schedule: headGap,
  replicas: [1, 3],
  observed: 'ja*l*',
  admitted: ['lja*', 'lja', 'jla*', 'jla', 'ja*l*', 'ja*l'],
  witness: true,
}));

/*
 * NT-3 in three requests: two typists on an empty block.
 * r1 types "w" (s1:1); r2 types "u" (s2:1) and bolds it (s2:2, before u to
 * before end). Shipped: the head siblings are ordered u (s2) before w (s1):
 * u w, and w lies before end: u* w*.
 * Anchored: u w gives u* w* (w inside [before u, before end)), w u gives
 * w u*: admitted { u* w*, w u* }. Interval: the bold sets u alone and w
 * carries plain: admitted { u* w, w u* }; no witness for u* w*.
 */
const twoTypists = { replicas: 2, steps: [ins(1, 0, 'w'), ins(2, 0, 'u'), bold(2, 0, 1), deliver(1, 2), deliver(2, 1)] };
cases.push(declared('NT-3: concurrent typing into an empty block, one bolds, interval reading', INTERVAL, {
  schedule: twoTypists,
  observed: 'u*w*',
  admitted: ['u*w', 'wu*'],
  witness: false,
  notObserved: ['u*w'],
}));
cases.push(declared('NT-3 control: the two typists under the anchored reading', INHERIT, {
  schedule: twoTypists,
  observed: 'u*w*',
  admitted: ['u*w*', 'wu*'],
  witness: true,
}));

/*
 * NT-1: inheritance. r1 inserts "d", bolds it (d*), inserts "e" at 1: the
 * origin is d, e goes immediately after it, before the end item that
 * bounds the bold, so e is bold: d* e*. positional-spec.mjs inserts plain
 * text: expected d* e. The inherit local meaning expects d* e*.
 * Control: "e" at 0 (origin start, before d's before anchor): e d*, which
 * both local meanings expect.
 */
const inherit = { replicas: 1, steps: [ins(1, 0, 'd'), bold(1, 0, 1), ins(1, 1, 'e')] };
cases.push(declared('NT-1: an insertion right of a bold character, positional local meaning', ANCHORED, {
  schedule: inherit,
  observed: 'd*e*',
  admitted: ['d*e*'],
  witness: true,
  notObserved: ['d*e'],
  checks: { localMeaning: false, raLinearizability: true },
  classes: ['NT-1'],
}));
cases.push(declared('NT-1 control: the inherit local meaning', INHERIT, {
  schedule: inherit,
  observed: 'd*e*',
  admitted: ['d*e*'],
  witness: true,
  checks: { localMeaning: true },
  controls: [{ name: 'insert at 0', schedule: { replicas: 1, steps: [ins(1, 0, 'd'), bold(1, 0, 1), ins(1, 0, 'e')] }, observed: parseView('ed*'), admitted: [parseView('ed*')], notObserved: [parseView('e*d*')], witness: true }],
}));

/*
 * NT-2: the two-sided rule. r1 inserts "c" at 0 (s1:1) and "f" at 0 (s1:2,
 * right neighbour c); r2 inserts "x" at 0 (s2:1) on an empty display. All
 * three have origin start; RGA orders the siblings by decreasing id:
 * f (2) x (1, s2) c (1, s1). Shipped: f x c.
 * left (after the origin, so the head): the orders with c before f fold to
 * c f x -> x f c, c x f -> f x c, x c f -> f c x: admitted { xfc, fxc, fcx }.
 * both: f lands immediately before c, c and x at the head: c f x -> x f c,
 * c x f -> x f c, x c f -> f c x: admitted { xfc, fcx }; no witness for fxc.
 * gap: f anywhere before c, c and x anywhere: { fcx, fxc, xfc }.
 * Control: r2 receives c before inserting x at 0 (s2:2, right neighbour c).
 * Shipped: siblings x (2, s2) f (2, s1) c: x f c. both: f and x each land
 * immediately before c, after it: c f x -> f x c, c x f -> x f c; admitted
 * { fxc, xfc }.
 */
const twoSided = { replicas: 2, steps: [ins(1, 0, 'c'), ins(1, 0, 'f'), ins(2, 0, 'x'), deliver(1, 2), deliver(2, 1)] };
const twoSidedControl = { replicas: 2, steps: [ins(1, 0, 'c'), send(1, 2, 0), ins(1, 0, 'f'), ins(2, 0, 'x'), deliver(1, 2), deliver(2, 1)] };
cases.push(declared('NT-2: two-sided rule, concurrent head inserts', { rule: 'both' }, {
  schedule: twoSided,
  observed: 'fxc',
  admitted: ['xfc', 'fcx'],
  witness: false,
  checks: { raLinearizability: false, convergence: true },
  classes: ['NT-2'],
  controls: [{ name: 'x issued after receiving c', schedule: twoSidedControl, observed: parseView('xfc'), admitted: views('fxc', 'xfc'), witness: true }],
}));
cases.push(declared('NT-2: the same history under the one-sided rule', { rule: 'left' }, {
  schedule: twoSided,
  observed: 'fxc',
  admitted: ['xfc', 'fxc', 'fcx'],
  witness: true,
  checks: { raLinearizability: true },
}));
cases.push(declared('NT-2: the same history under the gap rule', ANCHORED, {
  schedule: twoSided,
  observed: 'fxc',
  admitted: ['fcx', 'fxc', 'xfc'],
  witness: true,
}));

/*
 * T5 convergence control: insert, bold and delete concurrently at three
 * replicas, received in different orders. r1 inserts "ab" (s1:1..2); sync
 * to r2, r3. Concurrently X: r1 inserts "x" at 1 (s1:3, origin a);
 * F: r2 bolds [0,2) (s2:3, before a to before end); D: r3 deletes b.
 * Rounds 1->2, 2->3, 3->1, then 1->3, 2->1, 3->2. Shipped at every replica:
 * a x b(deleted), all covered by F: a* x*.
 * Anchored: x lies in F's range in every order: admitted { a* x* }.
 */
cases.push(declared('T5 control: insert, bold and delete at three replicas in rotated orders', ANCHORED, {
  schedule: { replicas: 3, steps: [ins(1, 0, 'ab'), deliver(1, 2), deliver(1, 3), ins(1, 1, 'x'), bold(2, 0, 2), del(3, 1, 2), deliver(1, 2), deliver(2, 3), deliver(3, 1), deliver(1, 3), deliver(2, 1), deliver(3, 2)] },
  observed: 'a*x*',
  admitted: ['a*x*'],
  witness: true,
  notObserved: ['a*x'],
  checks: { convergence: true, raLinearizability: true, conservation: true, determinism: true },
}));

/*
 * T4 determinism control: an opened replica issues the requests a created
 * one does. r1 inserts "ab" and bolds [0,1); r2 is opened from r1; r2
 * inserts "z" at 1 (origin a, inheriting bold) and toggles [1,3) (z* and b:
 * not all bold, so an addition). Expected on r2: a* z* b*. The determinism
 * check forks each request onto a created and an opened replica.
 */
cases.push(declared('T4 control: requests on an opened replica', INHERIT, {
  schedule: { replicas: 2, steps: [ins(1, 0, 'ab'), bold(1, 0, 1), open(2, 1), ins(2, 1, 'z'), bold(2, 1, 3), deliver(2, 1)] },
  observed: 'a*z*b*',
  admitted: ['a*z*b*'],
  witness: true,
  notObserved: ['a*zb*', 'a*z*b'],
  checks: { determinism: true, localMeaning: true, raLinearizability: true, convergence: true },
}));

/*
 * Causal buffering in the adapter: r1 inserts "a" (s1:1) and deletes it; r2
 * is sent only the delete. The client would apply a delete of an absent
 * character as a no-op; the adapter holds it until the insert arrives, so r2
 * shows nothing in between and nothing after.
 */
cases.push({
  name: 'transport: a delete sent ahead of its insert is held, then applied',
  run(results) {
    const inst = prepareInstance(instanceFor(ANCHORED));
    const ex = new Execution(inst, 2, { checks: [] });
    for (const s of [ins(1, 0, 'a'), del(1, 0, 1), send(1, 2, 1)]) ex.apply(s);
    assert.equal(inst.adapter.hasPending(ex.replica(2)), true, 'the delete is not held');
    assert.equal(ex.integrated[2].size, 0);
    ex.apply(send(1, 2, 0));
    assert.equal(inst.adapter.hasPending(ex.replica(2)), false);
    assert.equal(renderView(inst.adapter.displayed(ex.replica(2))), '(empty)');
    assert.notEqual(renderView(inst.adapter.displayed(ex.replica(2))), 'a');
    results.observed = '(empty)';
  },
});

/*
 * Probe classes under the unbuffered transport of out-of-order.mjs, each
 * against the instance's causal transport as control.
 * P-1: r1 types "l" (s1:1) and deletes it; r2 is sent the deletion first.
 * Unbuffered, r2 applies it as a no-op and shows l after the final sync,
 * while r1 shows nothing: conservation and convergence fail. Buffered: both
 * empty.
 * P-4: r2 types "hw" (s2:1..2), "j" at 1 and "x" at 1; r1 is sent the
 * insertion of x first, backfilling h alone (the item h | w was split by j);
 * the insertion of "hw" then arrives in the final sync and is dropped as
 * likely already applied. Unbuffered: r1 shows h x j, r2 h x j w.
 * Buffered: h x j w on both.
 */
function probeCase(name, schedule, expected) {
  return {
    name,
    run(results) {
      const checks = ['convergence', 'conservation'];
      const loose = executeWith(unbuffered, schedule, { checks });
      const held = executeWith(instanceFor(INHERIT), schedule, { checks });
      assert.equal(loose.checks.conservation.pass, false, 'unbuffered conservation passed');
      assert.equal(loose.checks.convergence.pass, false, 'unbuffered convergence passed');
      const shown = loose.snapshots.slice(-schedule.replicas * (schedule.replicas - 1)).map((x) => [x.replica, x.text]);
      const final = Object.fromEntries(shown);
      assert.deepEqual(final, expected.loose);
      assert.equal(held.checks.conservation.pass, true, 'buffered conservation failed');
      assert.equal(held.checks.convergence.pass, true, 'buffered convergence failed');
      const heldFinal = Object.fromEntries(held.snapshots.slice(-schedule.replicas * (schedule.replicas - 1)).map((x) => [x.replica, x.text]));
      assert.deepEqual(heldFinal, expected.held);
      assert.notDeepEqual(final, heldFinal);
      results.observed = JSON.stringify(final);
    },
  };
}
cases.push(probeCase('P-1 (probe): a deletion sent ahead of its insertion, unbuffered', { replicas: 2, steps: [ins(1, 0, 'l'), del(1, 0, 1), send(1, 2, 1)] }, { loose: { 1: '', 2: 'l' }, held: { 1: '', 2: '' } }));
cases.push(probeCase('P-4 (probe): an insertion backfilled from a split item, unbuffered', { replicas: 2, steps: [ins(2, 0, 'hw'), ins(2, 1, 'j'), ins(2, 1, 'x'), send(2, 1, 2)] }, { loose: { 1: 'hxj', 2: 'hxjw' }, held: { 1: 'hxjw', 2: 'hxjw' } }));

/* Identities: the k-th character of an insertion has [session, counter + k], and counters are Lamport. */
cases.push({
  name: 'identities: run ids, recorded origin and Lamport counters',
  run(results) {
    const inst = prepareInstance(instanceFor(ANCHORED));
    const ex = new Execution(inst, 2, { checks: [] });
    const r1 = ex.apply(ins(1, 0, 'abc'));
    assert.deepEqual(r1.chars.map((c) => c.id), [['s1', 1], ['s1', 2], ['s1', 3]]);
    assert.deepEqual(r1.chars.map((c) => c.origin), [null, ['s1', 1], ['s1', 2]]);
    ex.apply(deliver(1, 2));
    const r2 = ex.apply(ins(2, 1, 'x'));
    assert.deepEqual(r2.chars[0].id, ['s2', 4]);
    assert.notDeepEqual(r2.chars[0].id, ['s2', 1]);
    assert.deepEqual(r2.chars[0].origin, ['s1', 1]);
    assert.deepEqual(r2.chars[0].rightOrigin, ['s1', 2]);
    const b = ex.apply(bold(2, 0, 2));
    assert.deepEqual(b.annotation.start, { id: ['s1', 1], anchor: 'before' });
    assert.deepEqual(b.annotation.end, { id: ['s1', 2], anchor: 'before' });
    assert.notDeepEqual(b.annotation.end, { id: ['s2', 4], anchor: 'after' });
    const d = ex.apply(del(2, 1, 2));
    assert.deepEqual(d.deletedIds, [['s2', 4]]);
    const list = items(ex.replica(2).client).map((it) => `${it.kind}${it.deleted ? '-' : ''}`);
    assert.deepEqual(list, ['StartItem', 'TextItem', 'TextItem-', 'TextItem', 'EndItem']);
    results.observed = renderView(inst.adapter.displayed(ex.replica(2)));
    assert.equal(results.observed, 'a*bc');
  },
});

/* Source verification rejects a modified export (a temporary copy). */
cases.push({
  name: 'source verification rejects a same-length modification of the export',
  run(results) {
    const original = process.env.NOTION_PRODUCTION_LIBRARY;
    const copy = mkdtempSync(join(tmpdir(), 'notion-export-'));
    try {
      cpSync(libraryPath(), copy, { recursive: true });
      const path = join(copy, 'sources.json');
      const text = readFileSync(path, 'utf8');
      writeFileSync(path, text.replace('2026-10-29', '2026-10-28'));
      process.env.NOTION_PRODUCTION_LIBRARY = copy;
      assert.throws(() => verifySources(), /sha256 sources\.json/);
      writeFileSync(path, text);
      assert.doesNotThrow(() => verifySources());
    } finally {
      if (original === undefined) delete process.env.NOTION_PRODUCTION_LIBRARY;
      else process.env.NOTION_PRODUCTION_LIBRARY = original;
      rmSync(copy, { recursive: true, force: true });
    }
    results.observed = 'modified copy rejected, restored copy accepted';
  },
});

export async function runAll() {
  const out = [];
  for (const c of cases) {
    const results = {};
    try {
      c.run(results);
      out.push({ name: c.name, pass: true, results });
    } catch (e) {
      out.push({ name: c.name, pass: false, error: e.message, results });
    }
    await yieldToTimers();
  }
  return out;
}
