/**
 * Hand-derived minimal schedules over Loro text with their expected
 * outcomes. Each case states, in the comment above it, the specification's
 * admitted views (derived by hand), the view Loro is expected to show, and
 * whether a witness exists, under the insertion rule and attribute reading
 * it names. Every failing case is paired with a control that changes one
 * ingredient, and every equality has a companion inequality against the
 * tempting wrong answer.
 *
 * Replica r is Loro peer r. Concurrent list elements with the same recorded
 * neighbours are ordered by ascending peer; a style anchor is such an
 * element, so its order against a concurrent insertion is decided by peers.
 * Notation: x* bold, x^ sup, x~ link, x= hl; r+ a deleted r. The Yjs cases
 * (Y-000 to Y-007) are the schedules of `experiments/yjs-oracle/regressions.mjs`
 * with formats as marks; an insert Yjs issued with attributes is an insert
 * followed by a mark.
 *
 * Run with `node run.mjs --mode regressions`.
 */
import assert from 'node:assert/strict';
import { checkDeclared } from '../../ra-pbt/src/index.js';
import { Execution, execute, eventsAt, findWitness, allFinalViews, loroText, apply, initial, view, viewKey, viewsEqual } from '../../ra-pbt/instances/loro/index.js';
import { classifyTrial } from '../../ra-pbt/instances/loro/classify.js';

const B = { bold: true };
const S = { sup: true };
const L = { link: true };
const H = { hl: true };
const HS = { hl: true, sup: true };
const v = (...pairs) => pairs.map(([ch, attrs]) => ({ ch, attrs: attrs ?? {} }));
const plainView = (s) => v(...[...s].map((ch) => [ch]));
const ins = (replica, index, text) => ({ type: 'edit', replica, kind: 'insert', index, text });
const del = (replica, index, len) => ({ type: 'edit', replica, kind: 'delete', index, len });
const mark = (replica, index, len, key) => ({ type: 'edit', replica, kind: 'mark', index, len, key, value: true });
const unmark = (replica, index, len, key) => ({ type: 'edit', replica, kind: 'unmark', index, len, key });
const deliver = (from, to) => ({ type: 'deliver', from, to });
const send = (from, to, op) => ({ type: 'send', from, to, op });
/** Two replicas: `prefix` at replica 1, sync, the concurrent ops, sync both ways. */
const concurrent = (prefix, ops1, ops2) => ({ replicas: 2, steps: [...prefix, deliver(1, 2), ...ops1, ...ops2, deliver(1, 2), deliver(2, 1)] });

const sameViewSet = (xs, ys) => JSON.stringify(xs.map(viewKey).sort()) === JSON.stringify(ys.map(viewKey).sort());

function run(schedule, opts = {}) {
  const ex = new Execution(schedule.replicas, { checks: [], ...opts });
  for (const s of schedule.steps) ex.apply(s);
  return ex;
}

/** A declared regression (see ra-pbt/src/regressions.js) checked under an insertion rule and attribute reading. */
function under(rule, attrs, c) {
  return { name: c.name, schedule: c.schedule, run: (results) => checkDeclared(loroText(rule, attrs), c, results) };
}

/** A declared failing case under (rule, attrs) that also requires the raLinearizability check to fail and convergence to hold. */
function failing(rule, attrs, c) {
  return {
    name: c.name,
    schedule: c.schedule,
    run(results) {
      checkDeclared(loroText(rule, attrs), c, results);
      const trace = execute(c.schedule, { rule, attrs });
      assert.equal(trace.checks.raLinearizability.pass, false, 'raLinearizability check passed');
      assert.equal(trace.checks.convergence.pass, true, 'convergence check failed');
    },
  };
}

/** Folds the events at replica r in the given key order; returns the view, or null on a failed precondition. */
function foldInOrder(ex, r, order, rule, attrs = 'carry') {
  const { events } = eventsAt(ex, r);
  const byKey = new Map(events.map((e) => [e.key, e]));
  assert.equal(order.length, events.length, 'the order does not name every event');
  const pos = new Map(order.map((k, i) => [k, i]));
  for (const e of events) for (const d of e.deps) assert.ok(pos.get(d) < pos.get(e.key), `${d} must precede ${e.key}`);
  let st = initial();
  for (const k of order)
    for (const op of byKey.get(k).specOps) {
      st = apply(st, op, rule, { attrsMode: attrs });
      if (st === null) return null;
    }
  return view(st);
}

/** Witness results at replica r under each insertion rule. */
function witnesses(ex, r, attrs = 'carry') {
  const { events } = eventsAt(ex, r);
  const target = ex.adapter.view(ex.replica(r));
  return Object.fromEntries(['gap', 'left', 'both'].map((rule) => [rule, findWitness(events, target, { rule, attrs }).found]));
}

/*
 * Convergence control (L0): concurrent insert, mark and delete received in
 * different orders by three replicas.
 *
 * r1 inserts "ab" (1:0 1:1); sync to r2 and r3. Concurrently:
 *   X (r1): insert x at 1, recorded (a, b), carrying {} (a and b are plain).
 *   M (r2): mark [0,2) bold: anchors before a and after b.
 *   D (r3): delete [1,2), which deletes b.
 * x lies between a and b, so between M's anchors, at every replica.
 * Deliveries 1->2, 2->3, 3->1, then 1->3, 2->1, 3->2: every replica ends with
 * all four records and shows a* x*.
 * Specification (gap, carry): X before M: M covers a..b, which contains x:
 * a* x*; X after M: x keeps its own {}: a* x. D commutes with both.
 * Admitted { a* x*, a* x }.
 */
const convergenceRound = [deliver(1, 2), deliver(2, 3), deliver(3, 1)];
const convergence = {
  replicas: 3,
  steps: [ins(1, 0, 'ab'), deliver(1, 2), deliver(1, 3), ins(1, 1, 'x'), mark(2, 0, 2, 'bold'), del(3, 1, 1), ...convergenceRound, deliver(1, 3), deliver(2, 1), deliver(3, 2)],
};

/*
 * L1, the one-sided rule refuted on plain text.
 *
 * Ids: q 1:0, n 2:0, i 2:1, u 3:0, f 2:2. r3 receives n and q (Loro orders
 * the concurrent head inserts by peer: q n). r2 inserts i after n, recorded
 * (n, none); r3 inserts u after n, recorded (n, none); r2 then inserts f at
 * the head of "n i", recorded (none, n). Loro's origin for f is none and its
 * right origin n, so Fugue makes f a left child of n: f lands immediately
 * before n, after q, which r2 never saw. i and u are concurrent children of
 * n with equal origins, ordered by peer: i u. Every replica shows q f n i u.
 *
 * One-sided rule (immediately after the recorded left neighbour; a later
 * sibling lands nearer it): q, n and f are head inserts, displayed q f n, so
 * they were applied n, f, q; i and u are children of n, displayed i u, so u
 * was applied before i. Causally q precedes u (r3 saw q) and i precedes f
 * (r2's program order). Then q < u < i < f < q: a cycle, no witness.
 * Two-sided and gap rules: the order n, q, u, i, f folds as [n] [q n]
 * [q n u] [q n i u] [q f n i u] (f immediately before n), showing the view.
 *
 * Control: f inserted at 1 instead, between n and i, recorded (n, i): q n f i
 * u. One-sided rule: n, q, u, i, f folds [n] [q n] [q n u] [q n i u]
 * [q n f i u].
 */
const leftSteps = (fIndex) => [ins(1, 0, 'q'), ins(2, 0, 'n'), deliver(2, 3), deliver(1, 3), ins(2, 1, 'i'), ins(3, 2, 'u'), ins(2, fIndex, 'f'), deliver(1, 2), deliver(2, 1), deliver(3, 1), deliver(3, 2), deliver(1, 3), deliver(2, 3)];
const leftOrder = ['r2#0', 'r1#0', 'r3#0', 'r2#1', 'r2#2'];

/*
 * L1, the two-sided rule refuted on plain text, with the visible right
 * neighbour as the recorded right origin.
 *
 * r1 inserts r (1:0); sync. r1 inserts m at the head, recorded (none, r);
 * concurrently r2 deletes r and inserts c into its empty display, recorded
 * (none, none). Loro records for c the right origin r, a tombstone the API
 * does not expose, so m and c are both left children of r, ordered by peer:
 * m c r+, shown m c.
 * Two-sided rule: c has no recorded right neighbour, so it lands at the
 * head; m lands immediately before r. Orders: r m del c: [r] [m r] [m r+]
 * [c m r+]; r del c m: [r] [r+] [c r+] [c m r+]; r del m c: [r] [r+] [m r+]
 * [c m r+]. Admitted { c m }: no witness.
 * One-sided rule: m and c are head inserts; r del c m folds [r] [r+] [c r+]
 * [m c r+]: a witness. Admitted { m c, c m }. Gap rule: the same order.
 *
 * Control: r2 inserts c without deleting r, so c is recorded (none, r). Loro:
 * m c r. Two-sided: r m c folds [r] [m r] [m c r]; r c m folds [r] [c r]
 * [c m r]. Admitted { m c r, c m r }.
 */
const bothSteps = (withDelete) => [ins(1, 0, 'r'), deliver(1, 2), ins(1, 0, 'm'), ...(withDelete ? [del(2, 0, 1)] : []), ins(2, 0, 'c'), deliver(1, 2), deliver(2, 1)];

/*
 * Y-000 (the Yjs one-sided refutation) on Loro.
 *
 * q 1:0, e 2:0; r3 receives both (q e). r1 deletes q and inserts i into its
 * empty display: Loro origins (none, q). r2 inserts l after e (e, none) and w
 * at its head (none, e). r3 deletes q and e and inserts u into its empty
 * display: origins (none, q). i and u are left children of q, ordered by
 * peer; w is a left child of e and passes q, which r2 never saw: i u q w e l,
 * shown i u w l at every replica. Yjs showed i w l u.
 * One-sided rule: i, u and w are head inserts displayed i u w, so applied
 * w, u, i. q e l w (r3 delete) u (r1 delete) i folds [q] [e q] [e l q]
 * [w e l q] [u w e l q] [i u w e l q]: a witness. Two-sided rule: the same
 * order, w landing immediately before e.
 */
const y000 = {
  replicas: 3,
  steps: [ins(1, 0, 'q'), ins(2, 0, 'e'), deliver(1, 3), deliver(2, 3), del(1, 0, 1), ins(1, 0, 'i'), ins(2, 1, 'l'), ins(2, 0, 'w'), del(3, 0, 2), ins(3, 0, 'u'), deliver(1, 3), deliver(2, 3), deliver(3, 1), deliver(3, 2)],
};
const y000Order = ['r1#0', 'r2#0', 'r2#1', 'r2#2', 'r3#0', 'r3#1', 'r1#1', 'r1#2'];

/*
 * Y-000 companion (the Yjs two-sided refutation) on Loro.
 *
 * p 1:0, d 2:0, j 3:0 are concurrent head inserts. r3 receives p, shows p j
 * and inserts t at 1, recorded (p, j). d, integrating where p t j are
 * present, passes p (lower peer) and p's child t and stops before j: p t d j,
 * as in Yjs. Admitted, by the derivation in the Yjs regressions (it depends
 * only on the recorded neighbours, which are the same):
 *   two-sided { p d t j, p t j d, d p t j }   (no witness)
 *   one-sided { p t d j, p t j d, d p t j, d j p t, j p t d, j d p t }
 *   gap       { d p t j, p d t j, p t d j, p t j d }
 */
const y000b = {
  replicas: 3,
  steps: [ins(1, 0, 'p'), ins(2, 0, 'd'), ins(3, 0, 'j'), send(1, 3, 0), ins(3, 1, 't'), deliver(1, 2), deliver(1, 3), deliver(2, 1), deliver(2, 3), deliver(3, 1), deliver(3, 2)],
};

/*
 * Y-001 overlapping bold and unbold.
 *
 * r1 inserts "abc" and bolds b; sync. Concurrently r1 bolds [0,2) (a..b) and
 * r2 unbolds [1,3) (b..c). Both concurrent marks have Lamport timestamp 5;
 * Loro resolves a key by the greatest (Lamport, peer), so r2's unbold wins on
 * b. a carries r1's bold only; c carries r2's unbold only: a* b c.
 * Specification: bold then unbold: a* b c; unbold then bold: a* b* c.
 * Admitted { a* b c, a* b* c }: a witness. Yjs showed a* b* c*.
 */
const y001 = concurrent([ins(1, 0, 'abc'), mark(1, 1, 1, 'bold')], [mark(1, 0, 2, 'bold')], [unmark(2, 1, 2, 'bold')]);

/*
 * Y-001 insert variant, a boundary case.
 *
 * r1 inserts "et" and bolds it: anchors B before e, B' after t; sync.
 * Concurrently r1 inserts d at 2: bold expands after, so d is placed before
 * B' and carries bold; d is recorded (t, none). r2 unbolds [0,2) (e..t): its
 * end anchor U' follows t. d and U' are concurrent elements after t, ordered
 * by peer: d before U', so d lies inside the unbold, whose Lamport timestamp
 * exceeds the bold's: e t d, all plain.
 * Specification (carry): d carries bold and lies outside e..t in every order:
 * admitted { e t d* }: no witness. Inherit: d after the unbold lands after a
 * plain t, with no right neighbour: e t d; d before it inherits bold from t:
 * e t d*. Admitted { e t d, e t d* }: a witness.
 *
 * Control: r2 unbolds [0,1) (e only), so U' sits before t: d lies inside B..B'
 * and outside the unbold: e t* d*, the single admitted view (carry).
 */
const y001Insert = (len) => concurrent([ins(1, 0, 'et'), mark(1, 0, 2, 'bold')], [ins(1, 2, 'd')], [unmark(2, 0, len, 'bold')]);

/*
 * Y-002 nested bolds: from "au", r1 bolds [0,2) and r2 bolds [0,1)
 * concurrently. Both cover a; r1's covers u: a* u*, the single admitted view.
 * Yjs showed a* u.
 */
const y002 = concurrent([ins(1, 0, 'au')], [mark(1, 0, 2, 'bold')], [mark(2, 0, 1, 'bold')]);

/*
 * Y-002 insert and format: from "q", r1 bolds q; concurrently r2 inserts z at
 * the head and bolds it. z carries {} (bold does not expand before); r2's
 * bold covers z, r1's covers q: z* q* in every order. Yjs showed z* q.
 */
const y002Insert = concurrent([ins(1, 0, 'q')], [mark(1, 0, 1, 'bold')], [ins(2, 0, 'z'), mark(2, 0, 1, 'bold')]);

/*
 * Y-003 delete beside a bold insert: r1 inserts "wv", then "b" at 2, and
 * bolds b; sync. Concurrently r1 deletes b and r2 inserts z at 3 (bold
 * expands after: z carries bold, placed before the closing anchor). A delete
 * removes no anchor, so z stays bold: w v z*, the single admitted view.
 * Yjs showed w v z.
 */
const y003 = concurrent([ins(1, 0, 'wv'), ins(1, 2, 'b'), mark(1, 2, 1, 'bold')], [del(1, 2, 1)], [ins(2, 3, 'z')]);

/*
 * Y-004 boundary spread at the start of a mark.
 *
 * r1 inserts "a"; sync. Concurrently r1 marks [0,1) with `key` and r2 inserts
 * h at the head, recorded (none, a), carrying {}. r1's opening anchor and h
 * have the same neighbours and r1 has the lower peer, so the anchor precedes
 * h and h lies inside the mark: h(key) a(key).
 * Specification: h never lies in a..a; it carries {} (carry), or (inherit)
 * takes the mark only if key expands before. For bold (after) and link
 * (none): admitted { h a(key) } under both readings: no witness.
 *
 * Control: h inserted at 1, after a. r1's closing anchor precedes h: a(key) h.
 * Admitted (carry) { a(key) h }.
 */
const y004 = (key, hIndex) => concurrent([ins(1, 0, 'a')], [mark(1, 0, 1, key)], [ins(2, hIndex, 'h')]);

/*
 * Boundary spread at the end of a mark.
 *
 * As Y-004 with the roles swapped: r2 marks [0,1) and r1 inserts h at 1,
 * recorded (a, none), carrying {}. h has the lower peer, so it precedes r2's
 * closing anchor and lies inside the mark: a(key) h(key).
 * Bold, carry: h carries {} and lies outside a..a: admitted { a* h }: no
 * witness. Bold, inherit: mark then h: h lands after a*, bold expands after:
 * a* h*; h then mark: a* h. Admitted { a* h*, a* h }: a witness.
 * Link (expand none): admitted { a~ h } under both readings: no witness.
 * Control (link): h issued after the mark arrived: a~ h, admitted { a~ h }.
 */
const endBoundary = (key) => concurrent([ins(1, 0, 'a')], [ins(1, 1, 'h')], [mark(2, 0, 1, key)]);

/*
 * The expand reading (a mark also covers the gap on each side its expand
 * type extends to; an unmark by the reversed type) on the boundary cases.
 *   bold end boundary (endBoundary('bold')): mark then h: a* h; h then mark:
 *     the mark reaches h, which lies in the gap after a: a* h*. Admitted
 *     { a* h*, a* h }: a witness.
 *   Y-001 insert variant: the unbold of e..t extends after (after reversed
 *     is after) to the end; d before the unbold: e t d; after it: d carries
 *     bold: e t d*. Admitted { e t d, e t d* }: a witness.
 *   Y-004 with bold: bold does not extend before: admitted { h a* }: no
 *     witness. With link: link extends nowhere: { h a~ } and { a~ h }: no
 *     witness at either boundary.
 *   sup (expand before), r1 marking a and r2 inserting h at the head
 *     (supStart): the opening anchor (peer 1) precedes h: h^ a^. Carry:
 *     admitted { h a^ }: no witness. Expand: h then mark reaches h: h^ a^;
 *     mark then h: h a^. Admitted { h^ a^, h a^ }: a witness.
 *   sup at the end (endBoundary('sup')): h (peer 1) precedes r2's closing
 *     anchor: a^ h^. sup does not extend after: admitted { a^ h } under
 *     both readings: no witness.
 */
const supStart = concurrent([ins(1, 0, 'a')], [mark(1, 0, 1, 'sup')], [ins(2, 0, 'h')]);

/*
 * Two replicas each mark their own concurrent head insert: r1 inserts q and
 * marks it hl (H), r2 inserts s and marks it sup (P); sync. Loro: q before s
 * (peer order), each mark's anchors around its own character: q= s^. q and s
 * have no recorded neighbours, so the gap rule admits both list orders.
 * Carry: each mark covers its own character only: { q= s^, s^ q= }.
 * Expand: H extends both ways to the ends, P before to the head. With q
 * before s: q has sup iff P follows q's insert, s has hl iff H follows s's;
 * Loro's view needs P before q's insert and H before s's, while q's insert
 * precedes H and s's precedes P: a cycle. The other three combinations have
 * orders. With s before q: P never reaches q; s has hl iff H follows s's
 * insert. Admitted { q=^ s=^, q=^ s^, q= s=^, s=^ q=, s^ q= }: no witness.
 * Anchors: each mark may extend over any adjoining part of its gaps, or none:
 * every combination in both orders, eight views, q= s^ among them.
 */
/*
 * Crossed boundaries (L-001, the residue of the anchors reading).
 *
 * r1 inserts e; r2 and r3 open the document in turn. Concurrently r1 marks e
 * sup (S) and then inserts u after e (U, carrying {}: sup does not extend
 * after), and r3 marks e bold (B) and then inserts y at the head (Y, carrying
 * {}: bold does not extend before). Loro: S's opening anchor precedes y by
 * peer and B's closing anchor follows u by peer: y^ e*^ u*.
 * Carry: S and B cover e only: admitted { y e*^ u }: no witness.
 * Anchors: S reaches y only if Y precedes S, and Y follows B; B reaches u
 * only if U precedes B, and U follows S: both would close a cycle, so
 * admitted { y e*^ u, y^ e*^ u, y e*^ u* }: no witness.
 * Persistent: Y knows B and lands outside it, and may land inside S, whose
 * opening anchor it did not know; U likewise inside B and outside S. With
 * items S< Y B< e S> U B>: y^ e*^ u*: a witness.
 */
const crossed = {
  replicas: 3,
  steps: [ins(1, 0, 'e'), { type: 'open', replica: 2, from: 1 }, { type: 'open', replica: 3, from: 2 }, mark(1, 0, 1, 'sup'), ins(1, 1, 'u'), mark(3, 0, 1, 'bold'), ins(3, 0, 'y'), ...[[1, 2], [1, 3], [3, 1], [3, 2], [2, 1], [2, 3]].map(([a, b]) => deliver(a, b))],
};
const BS = { bold: true, sup: true };

const ownMarks = { replicas: 2, steps: [ins(1, 0, 'q'), mark(1, 0, 1, 'hl'), ins(2, 0, 's'), mark(2, 0, 1, 'sup'), deliver(1, 2), deliver(2, 1)] };

/*
 * Y-005 overlapping bolds: from "abc", r1 bolds [0,2) and r2 bolds [1,3)
 * concurrently: a* b* c*, the single admitted view. Yjs showed a* b* c.
 */
const y005 = concurrent([ins(1, 0, 'abc')], [mark(1, 0, 2, 'bold')], [mark(2, 1, 2, 'bold')]);

/*
 * Y-007 shape A: r1 inserts a, bolds it, inserts b at 1 (b bold by expand),
 * unbolds [0,2). r2 is sent r1#0 and then r1#3, the unbold. Loro holds r1#3
 * pending, since it depends on r1#1 and r1#2: r2 shows a, pending, and has
 * integrated r1#0 alone. Admitted { a }: a witness, and no causal gap. Yjs
 * applied the unbold's delete set and showed a version no causally closed
 * history has. Control: all four sent in order: a b.
 *
 * Y-007 shape B: r1 inserts "ab" and bolds it; sync. r2 unbolds [0,2) and
 * inserts q at 1 (plain). r1 is sent r2#1, the insert, alone: pending, since
 * it depends on r2#0; r1 shows a* b*. Admitted { a* b* }. Control: r2#0 then
 * r2#1: a q b.
 */
const y007A = (order) => ({ replicas: 2, steps: [ins(1, 0, 'a'), mark(1, 0, 1, 'bold'), ins(1, 1, 'b'), unmark(1, 0, 2, 'bold'), ...order.map((k) => send(1, 2, k))] });
const y007B = (order) => ({ replicas: 2, steps: [ins(1, 0, 'ab'), mark(1, 0, 2, 'bold'), deliver(1, 2), unmark(2, 0, 2, 'bold'), ins(2, 1, 'q'), ...order.map((k) => send(2, 1, k))] });

/*
 * Local meaning on a single replica (no concurrency). The request's expected
 * value is the list edit with expandAttrs; the observed value is Loro's.
 *
 * L-002 a style no displayed character carries.
 *   (a) "ab", mark [0,2) hl, unmark [0,2) hl: shown a b. Insert X at 0:
 *       expected X a b; Loro shows X= a b. Control: the same with bold:
 *       X a b.
 *   (b) "abc", mark [1,2) hl (b), delete b: shown a c. Insert X at 1:
 *       expected a X c; Loro shows a X= c. Control: link instead: a X c.
 * L-003 the left boundary of an unmarked hole.
 *       "abc", mark [0,3) link, unmark [1,2) link: shown a~ b c~. Insert X
 *       at 1: link expands nowhere, so expected a~ X b c~; Loro shows
 *       a~ X~ b c~. Control: bold (after): expected and shown a* X* b c*.
 * L-004 adjacent spans of one value.
 *       "ab", mark [0,1) link, mark [1,2) link: shown a~ b~. Insert X at 1:
 *       both neighbours carry link, so expected a~ X~ b~; Loro shows
 *       a~ X b~ (X between the first span's closing anchor and the second's
 *       opening one). Control: one mark [0,2) link: a~ X~ b~.
 */
const single = (steps) => ({ replicas: 1, steps });
const l002a = (key) => single([ins(1, 0, 'ab'), mark(1, 0, 2, key), unmark(1, 0, 2, key), ins(1, 0, 'X')]);
const l002b = (key) => single([ins(1, 0, 'abc'), mark(1, 1, 1, key), del(1, 1, 1), ins(1, 1, 'X')]);
const l003 = (key) => single([ins(1, 0, 'abc'), mark(1, 0, 3, key), unmark(1, 1, 1, key), ins(1, 1, 'X')]);
const l004 = (split) => single([ins(1, 0, 'ab'), ...(split ? [mark(1, 0, 1, 'link'), mark(1, 1, 1, 'link')] : [mark(1, 0, 2, 'link')]), ins(1, 1, 'X')]);

/*
 * L-005 concurrent marks of two keys at one boundary.
 *
 * r1 inserts y; sync. Concurrently r1 marks y with `k1` and r2 marks y with
 * `k2`; r2's mark reaches r1, which shows y with both and inserts X at 0.
 * Expected: X takes sup (it expands before) and not bold: X^ y*^.
 * With k1 = bold, k2 = sup: the opening anchors share their neighbours and
 * are ordered by peer, bold's first. An insertion stops before an opening
 * anchor whose style does not expand before, so X lands before both: X y*^.
 * Control, k1 = sup, k2 = bold: sup's anchor first; X passes it and stops
 * before bold's: X^ y*^, as expected.
 */
const l005 = (k1, k2) => ({ replicas: 2, steps: [ins(1, 0, 'y'), deliver(1, 2), mark(1, 0, 1, k1), mark(2, 0, 1, k2), deliver(2, 1), ins(1, 0, 'X')] });

/** A local-meaning failure at the last step and its control, which passes every check. */
function localMeaningPair(name, schedule, { before, expected, observed }, controlName, control) {
  return [
    {
      name,
      schedule,
      run(results) {
        const trace = execute(schedule);
        const lm = trace.checks.localMeaning;
        assert.equal(lm.pass, false, 'localMeaning passed');
        const f = lm.details.failures.at(-1);
        assert.equal(f.step, schedule.steps.length - 1, 'the failure is not at the last step');
        if (before) assert.ok(viewsEqual(f.before, before), 'the view before the request differs from the hand derivation');
        assert.ok(viewsEqual(f.expected, expected), 'the list edit differs from the hand derivation');
        assert.ok(viewsEqual(f.actual, observed), 'Loro shows something else');
        assert.ok(!viewsEqual(f.actual, expected), 'Loro shows the expected view');
        for (const c of ['convergence', 'raLinearizability', 'determinism', 'conservation']) assert.equal(trace.checks[c].pass, true, `${c} failed`);
        results.observed = f.actual;
        results.admitted = [expected];
      },
    },
    {
      name: controlName,
      schedule: control.schedule,
      run(results) {
        const trace = execute(control.schedule);
        for (const c of ['convergence', 'raLinearizability', 'localMeaning', 'determinism', 'conservation']) assert.equal(trace.checks[c].pass, true, `${c} failed on the control`);
        const shown = run(control.schedule).replica(1).visible();
        assert.ok(viewsEqual(shown, control.observed), 'the control shows something else');
        assert.ok(!viewsEqual(shown, observed), "the control shows the failing case's view");
        results.observed = shown;
      },
    },
  ];
}

export const REGRESSIONS = [
  under('gap', 'carry', {
    name: 'L0 convergence control: concurrent insert, mark and delete received in different orders by three replicas',
    schedule: convergence,
    observed: v(['a', B], ['x', B]),
    notObserved: [v(['a', B], ['x'])],
    admitted: [v(['a', B], ['x', B]), v(['a', B], ['x'])],
    witness: true,
  }),
  {
    name: 'L1 one-sided rule refuted on plain text: f is a left child of its right origin n, which no one-sided order produces',
    schedule: { replicas: 3, steps: leftSteps(0) },
    run(results) {
      const ex = run({ replicas: 3, steps: leftSteps(0) });
      for (const r of [1, 2, 3]) {
        const shown = ex.replica(r).visible();
        assert.ok(viewsEqual(shown, plainView('qfniu')), `replica ${r}: view differs from the hand derivation`);
        assert.ok(!viewsEqual(shown, plainView('fqniu')), `replica ${r}: f at the head`);
        assert.deepEqual(witnesses(ex, r), { gap: true, left: false, both: true }, `replica ${r}: witnesses differ`);
        assert.ok(viewsEqual(foldInOrder(ex, r, leftOrder, 'both'), plainView('qfniu')), 'the two-sided order does not fold to the view');
        assert.ok(!viewsEqual(foldInOrder(ex, r, leftOrder, 'left'), plainView('qfniu')), 'the one-sided rule folds the same order to the view');
        assert.ok(!allFinalViews(eventsAt(ex, r).events, { rule: 'left' }).some((w) => viewsEqual(w, shown)), 'the one-sided rule admits the view');
      }
      results.observed = ex.replica(1).visible();
    },
  },
  {
    name: 'control for L1 one-sided: f recorded between n and i, every rule admits the view',
    schedule: { replicas: 3, steps: leftSteps(1) },
    run(results) {
      const ex = run({ replicas: 3, steps: leftSteps(1) });
      for (const r of [1, 2, 3]) {
        const shown = ex.replica(r).visible();
        assert.ok(viewsEqual(shown, plainView('qnfiu')), `replica ${r}: view differs from the hand derivation`);
        assert.ok(!viewsEqual(shown, plainView('qfniu')), `replica ${r}: the failing case's view`);
        assert.deepEqual(witnesses(ex, r), { gap: true, left: true, both: true }, `replica ${r}: witnesses differ`);
        assert.ok(viewsEqual(foldInOrder(ex, r, leftOrder, 'left'), plainView('qnfiu')), 'the one-sided order does not fold to the view');
      }
      results.observed = ex.replica(1).visible();
    },
  },
  failing('both', 'carry', {
    name: 'L1 two-sided rule refuted on plain text: c recorded with no visible right neighbour lands after m (both are left children of the tombstone r)',
    schedule: { replicas: 2, steps: bothSteps(true) },
    observed: plainView('mc'),
    notObserved: [plainView('cm')],
    admitted: [plainView('cm')],
    witness: false,
    controls: [under('left', 'carry', { name: 'the one-sided rule admits it', schedule: { replicas: 2, steps: bothSteps(true) }, observed: plainView('mc'), admitted: [plainView('mc'), plainView('cm')], witness: true })],
  }),
  under('both', 'carry', {
    name: 'control for L1 two-sided: r not deleted, c recorded before r',
    schedule: { replicas: 2, steps: bothSteps(false) },
    observed: plainView('mcr'),
    notObserved: [plainView('cmr')],
    admitted: [plainView('mcr'), plainView('cmr')],
    witness: true,
  }),
  {
    name: 'Y-000 on Loro: the Yjs one-sided refutation has witnesses under every rule (Loro shows i u w l, Yjs i w l u)',
    schedule: y000,
    run(results) {
      const ex = run(y000);
      for (const r of [1, 2, 3]) {
        const shown = ex.replica(r).visible();
        assert.ok(viewsEqual(shown, plainView('iuwl')), `replica ${r}: view differs from the hand derivation`);
        assert.ok(!viewsEqual(shown, plainView('iwlu')), `replica ${r}: the Yjs view`);
        assert.deepEqual(witnesses(ex, r), { gap: true, left: true, both: true }, `replica ${r}: witnesses differ`);
        for (const rule of ['left', 'both']) assert.ok(viewsEqual(foldInOrder(ex, r, y000Order, rule), plainView('iuwl')), `the ${rule} order does not fold to the view`);
      }
      results.observed = ex.replica(1).visible();
    },
  },
  {
    name: 'Y-000 companion on Loro: p t d j as in Yjs, no witness under the two-sided rule only',
    schedule: y000b,
    run(results) {
      const ex = run(y000b);
      const want = { both: ['pdtj', 'ptjd', 'dptj'], left: ['ptdj', 'ptjd', 'dptj', 'djpt', 'jptd', 'jdpt'], gap: ['dptj', 'pdtj', 'ptdj', 'ptjd'] };
      for (const r of [1, 2, 3]) {
        const shown = ex.replica(r).visible();
        assert.ok(viewsEqual(shown, plainView('ptdj')), `replica ${r}: view differs`);
        assert.ok(!viewsEqual(shown, plainView('pdtj')), `replica ${r}: d before t`);
        assert.deepEqual(witnesses(ex, r), { gap: true, left: true, both: false }, `replica ${r}: witnesses differ`);
        for (const [rule, views] of Object.entries(want)) assert.ok(sameViewSet(allFinalViews(eventsAt(ex, r).events, { rule }), views.map(plainView)), `replica ${r}: ${rule} admitted views differ`);
      }
      results.observed = ex.replica(1).visible();
    },
  },
  under('gap', 'carry', {
    name: 'Y-001 on Loro: overlapping bold and unbold, the unbold wins on b by (Lamport, peer): an admitted view',
    schedule: y001,
    observed: v(['a', B], ['b'], ['c']),
    notObserved: [v(['a', B], ['b', B], ['c', B])],
    admitted: [v(['a', B], ['b'], ['c']), v(['a', B], ['b', B], ['c'])],
    witness: true,
  }),
  failing('gap', 'carry', {
    name: 'L-001 (Y-001 insert variant) a bold insert after t lands inside a concurrent unbold of e..t: no witness under carry',
    schedule: y001Insert(2),
    observed: plainView('etd'),
    notObserved: [v(['e'], ['t'], ['d', B])],
    admitted: [v(['e'], ['t'], ['d', B])],
    witness: false,
    controls: [under('gap', 'inherit', { name: 'the inherit reading admits it', schedule: y001Insert(2), observed: plainView('etd'), admitted: [plainView('etd'), v(['e'], ['t'], ['d', B])], witness: true })],
  }),
  under('gap', 'carry', {
    name: 'control for L-001 (Y-001 insert variant): the unbold covers e only',
    schedule: y001Insert(1),
    observed: v(['e'], ['t', B], ['d', B]),
    notObserved: [plainView('etd')],
    admitted: [v(['e'], ['t', B], ['d', B])],
    witness: true,
  }),
  under('gap', 'carry', { name: 'Y-002 on Loro: nested concurrent bolds', schedule: y002, observed: v(['a', B], ['u', B]), notObserved: [v(['a', B], ['u'])], admitted: [v(['a', B], ['u', B])], witness: true }),
  under('gap', 'carry', { name: 'Y-002 insert variant on Loro: a bold insert at the head beside a concurrent bold', schedule: y002Insert, observed: v(['z', B], ['q', B]), notObserved: [v(['z', B], ['q'])], admitted: [v(['z', B], ['q', B])], witness: true }),
  under('gap', 'carry', { name: 'Y-003 on Loro: deleting a bold character keeps a concurrent bold insert after it bold', schedule: y003, observed: v(['w'], ['v'], ['z', B]), notObserved: [plainView('wvz')], admitted: [v(['w'], ['v'], ['z', B])], witness: true }),
  failing('gap', 'carry', {
    name: 'L-001 (Y-004) a plain insert at the head lands inside a concurrent bold: no witness',
    schedule: y004('bold', 0),
    observed: v(['h', B], ['a', B]),
    notObserved: [v(['h'], ['a', B])],
    admitted: [v(['h'], ['a', B])],
    witness: false,
    controls: [under('gap', 'inherit', { name: 'nor under the inherit reading', schedule: y004('bold', 0), observed: v(['h', B], ['a', B]), admitted: [v(['h'], ['a', B])], witness: false })],
  }),
  under('gap', 'carry', { name: 'control for L-001 (Y-004): the insert after a, outside the closing anchor', schedule: y004('bold', 1), observed: v(['a', B], ['h']), notObserved: [v(['a', B], ['h', B])], admitted: [v(['a', B], ['h'])], witness: true }),
  failing('gap', 'inherit', {
    name: 'L-001 (Y-004 with link, expand none) a plain insert at the head takes a concurrent link: no witness under either reading',
    schedule: y004('link', 0),
    observed: v(['h', L], ['a', L]),
    notObserved: [v(['h'], ['a', L])],
    admitted: [v(['h'], ['a', L])],
    witness: false,
    controls: [under('gap', 'carry', { name: 'carry', schedule: y004('link', 0), observed: v(['h', L], ['a', L]), admitted: [v(['h'], ['a', L])], witness: false })],
  }),
  under('gap', 'carry', { name: 'control for L-001 with link: the insert after a', schedule: y004('link', 1), observed: v(['a', L], ['h']), notObserved: [v(['a', L], ['h', L])], admitted: [v(['a', L], ['h'])], witness: true }),
  failing('gap', 'carry', {
    name: 'L-001 end boundary, bold: an insert after a precedes a concurrent closing anchor: no witness under carry',
    schedule: endBoundary('bold'),
    observed: v(['a', B], ['h', B]),
    notObserved: [v(['a', B], ['h'])],
    admitted: [v(['a', B], ['h'])],
    witness: false,
  }),
  under('gap', 'inherit', { name: 'the inherit reading admits the bold end boundary (a specification artefact of carry)', schedule: endBoundary('bold'), observed: v(['a', B], ['h', B]), notObserved: [v(['a', B], ['h'])], admitted: [v(['a', B], ['h', B]), v(['a', B], ['h'])], witness: true }),
  failing('gap', 'inherit', {
    name: 'L-001 end boundary, link: the same schedule with expand none has no witness under either reading',
    schedule: endBoundary('link'),
    observed: v(['a', L], ['h', L]),
    notObserved: [v(['a', L], ['h'])],
    admitted: [v(['a', L], ['h'])],
    witness: false,
  }),
  under('gap', 'inherit', {
    name: 'control for the link end boundary: the insert issued after the mark arrived',
    schedule: { replicas: 2, steps: [ins(1, 0, 'a'), deliver(1, 2), mark(2, 0, 1, 'link'), deliver(2, 1), ins(1, 1, 'h'), deliver(1, 2)] },
    observed: v(['a', L], ['h']),
    notObserved: [v(['a', L], ['h', L])],
    admitted: [v(['a', L], ['h'])],
    witness: true,
  }),
  under('gap', 'expand', { name: 'expand reading: the bold end boundary is admitted', schedule: endBoundary('bold'), observed: v(['a', B], ['h', B]), notObserved: [v(['a', B], ['h'])], admitted: [v(['a', B], ['h', B]), v(['a', B], ['h'])], witness: true }),
  under('gap', 'expand', { name: 'expand reading: the Y-001 insert variant is admitted (the unbold extends after)', schedule: y001Insert(2), observed: plainView('etd'), notObserved: [v(['e'], ['t'], ['d', B])], admitted: [plainView('etd'), v(['e'], ['t'], ['d', B])], witness: true }),
  failing('gap', 'expand', { name: 'expand reading: bold reaching an insert before its start has no witness', schedule: y004('bold', 0), observed: v(['h', B], ['a', B]), notObserved: [v(['h'], ['a', B])], admitted: [v(['h'], ['a', B])], witness: false }),
  failing('gap', 'expand', { name: 'expand reading: link reaching an insert before its start has no witness', schedule: y004('link', 0), observed: v(['h', L], ['a', L]), notObserved: [v(['h'], ['a', L])], admitted: [v(['h'], ['a', L])], witness: false }),
  failing('gap', 'expand', { name: 'expand reading: link reaching an insert after its end has no witness', schedule: endBoundary('link'), observed: v(['a', L], ['h', L]), notObserved: [v(['a', L], ['h'])], admitted: [v(['a', L], ['h'])], witness: false }),
  failing('gap', 'carry', {
    name: 'L-001 start boundary, sup (expand before): no witness under carry',
    schedule: supStart,
    observed: v(['h', S], ['a', S]),
    notObserved: [v(['h'], ['a', S])],
    admitted: [v(['h'], ['a', S])],
    witness: false,
    controls: [under('gap', 'expand', { name: 'the expand reading admits it', schedule: supStart, observed: v(['h', S], ['a', S]), admitted: [v(['h', S], ['a', S]), v(['h'], ['a', S])], witness: true })],
  }),
  failing('gap', 'expand', { name: 'L-001 end boundary, sup: sup reaching an insert after its end has no witness under either reading', schedule: endBoundary('sup'), observed: v(['a', S], ['h', S]), notObserved: [v(['a', S], ['h'])], admitted: [v(['a', S], ['h'])], witness: false }),
  under('gap', 'carry', { name: 'marks on two concurrent head inserts: each stays on its own character (carry admits it)', schedule: ownMarks, observed: v(['q', H], ['s', S]), notObserved: [v(['q', { ...H, ...S }], ['s', { ...H, ...S }])], admitted: [v(['q', H], ['s', S]), v(['s', S], ['q', H])], witness: true }),
  failing('gap', 'expand', { name: 'the expand reading refuted: marks on two concurrent head inserts close a cycle', schedule: ownMarks, observed: v(['q', H], ['s', S]), admitted: [v(['q', { ...H, ...S }], ['s', { ...H, ...S }]), v(['q', { ...H, ...S }], ['s', S]), v(['q', H], ['s', { ...H, ...S }]), v(['s', { ...H, ...S }], ['q', H]), v(['s', S], ['q', H])], witness: false }),
  ...[
    ['Y-004 bold', y004('bold', 0), v(['h', B], ['a', B]), [v(['h', B], ['a', B]), v(['h'], ['a', B])]],
    ['Y-004 link', y004('link', 0), v(['h', L], ['a', L]), [v(['h', L], ['a', L]), v(['h'], ['a', L])]],
    ['end boundary bold', endBoundary('bold'), v(['a', B], ['h', B]), [v(['a', B], ['h', B]), v(['a', B], ['h'])]],
    ['end boundary link', endBoundary('link'), v(['a', L], ['h', L]), [v(['a', L], ['h', L]), v(['a', L], ['h'])]],
    ['end boundary sup', endBoundary('sup'), v(['a', S], ['h', S]), [v(['a', S], ['h', S]), v(['a', S], ['h'])]],
    ['start boundary sup', supStart, v(['h', S], ['a', S]), [v(['h', S], ['a', S]), v(['h'], ['a', S])]],
    ['Y-001 insert variant', y001Insert(2), plainView('etd'), [plainView('etd'), v(['e'], ['t'], ['d', B])]],
    ['two own marks', ownMarks, v(['q', H], ['s', S]), [HS, H].flatMap((qa) => [HS, S].flatMap((sa) => [v(['q', qa], ['s', sa]), v(['s', sa], ['q', qa])]))],
  ].map(([name, schedule, observed, admitted]) => under('gap', 'anchors', { name: `anchors reading admits the boundary case: ${name}`, schedule, observed, admitted, witness: true })),
  failing('gap', 'carry', { name: 'L-001 crossed boundaries: each concurrent mark reaches the other replica\'s later insert (carry)', schedule: crossed, observed: v(['y', S], ['e', BS], ['u', B]), notObserved: [v(['y'], ['e', BS], ['u'])], admitted: [v(['y'], ['e', BS], ['u'])], witness: false }),
  failing('gap', 'anchors', { name: 'L-001 crossed boundaries: no witness under the anchors reading either', schedule: crossed, observed: v(['y', S], ['e', BS], ['u', B]), admitted: [v(['y'], ['e', BS], ['u']), v(['y', S], ['e', BS], ['u']), v(['y'], ['e', BS], ['u', B])], witness: false }),
  {
    name: 'persistent reading admits every boundary case, the crossed one included',
    run(results) {
      for (const [name, schedule, observed] of [
        ['crossed', crossed, v(['y', S], ['e', BS], ['u', B])],
        ['Y-004 bold', y004('bold', 0), v(['h', B], ['a', B])],
        ['Y-004 link', y004('link', 0), v(['h', L], ['a', L])],
        ['end boundary bold', endBoundary('bold'), v(['a', B], ['h', B])],
        ['end boundary link', endBoundary('link'), v(['a', L], ['h', L])],
        ['end boundary sup', endBoundary('sup'), v(['a', S], ['h', S])],
        ['start boundary sup', supStart, v(['h', S], ['a', S])],
        ['Y-001 insert variant', y001Insert(2), plainView('etd')],
        ['two own marks', ownMarks, v(['q', H], ['s', S])],
      ]) {
        const ex = run(schedule);
        for (let r = 1; r <= schedule.replicas; r++) {
          const shown = ex.replica(r).visible();
          assert.ok(viewsEqual(shown, observed), `${name}, replica ${r}: view differs`);
          const { events } = eventsAt(ex, r);
          assert.equal(findWitness(events, ex.adapter.view(ex.replica(r)), { attrs: 'persistent' }).found, true, `${name}, replica ${r}: no witness under persistent`);
        }
        const trace = execute(schedule, { attrs: 'persistent' });
        assert.equal(trace.checks.raLinearizability.pass, true, `${name}: raLinearizability failed under persistent`);
      }
      // negative companion: the persistent reading still rejects a view no placement gives.
      const ex = run(y004('link', 0));
      const { events } = eventsAt(ex, 1);
      const wrong = ex.adapter.view(ex.replica(1)).map((e) => ({ ...e, attrs: {} }));
      assert.equal(findWitness(events, wrong, { attrs: 'persistent' }).found, false, 'persistent admits h a with no link at all');
    },
  },
  under('gap', 'carry', { name: 'Y-005 on Loro: overlapping concurrent bolds', schedule: y005, observed: v(['a', B], ['b', B], ['c', B]), notObserved: [v(['a', B], ['b', B], ['c'])], admitted: [v(['a', B], ['b', B], ['c', B])], witness: true }),
  {
    name: 'Y-007 shape A on Loro: the unbold sent ahead of its predecessors is held pending',
    schedule: y007A([0, 3]),
    run(results) {
      const ex = run(y007A([0, 3]));
      const rep = ex.replica(2);
      assert.equal(rep.hasPending(), true, 'nothing pending');
      assert.deepEqual([...ex.integrated[2]].sort(), ['r1#0'], 'integrated records differ');
      const { events, gaps } = eventsAt(ex, 2);
      assert.equal(gaps, 0, 'a causal gap');
      assert.ok(viewsEqual(rep.visible(), plainView('a')), 'view differs');
      assert.ok(!viewsEqual(rep.visible(), v(['a', B])), 'the bold reached r2');
      assert.ok(sameViewSet(allFinalViews(events), [plainView('a')]), 'admitted views differ');
      assert.equal(findWitness(events, ex.adapter.view(rep)).found, true, 'no witness');
      results.observed = rep.visible();
      const ctl = run(y007A([0, 1, 2, 3]));
      assert.equal(ctl.replica(2).hasPending(), false, 'control: pending');
      assert.ok(viewsEqual(ctl.replica(2).visible(), plainView('ab')), 'control: view differs');
      assert.ok(!viewsEqual(ctl.replica(2).visible(), v(['a', B], ['b', B])), 'control: unbold not applied');
    },
  },
  {
    name: 'Y-007 shape B on Loro: the insert sent ahead of the unbold it follows is held pending',
    schedule: y007B([1]),
    run(results) {
      const ex = run(y007B([1]));
      const rep = ex.replica(1);
      assert.equal(rep.hasPending(), true, 'nothing pending');
      assert.deepEqual([...ex.integrated[1]].sort(), ['r1#0', 'r1#1'], 'integrated records differ');
      assert.equal(eventsAt(ex, 1).gaps, 0, 'a causal gap');
      assert.ok(viewsEqual(rep.visible(), v(['a', B], ['b', B])), 'view differs');
      assert.ok(!viewsEqual(rep.visible(), v(['a', B], ['q', B], ['b', B])), 'q integrated ahead of the unbold');
      assert.equal(findWitness(eventsAt(ex, 1).events, ex.adapter.view(rep)).found, true, 'no witness');
      results.observed = rep.visible();
      const ctl = run(y007B([0, 1]));
      assert.ok(viewsEqual(ctl.replica(1).visible(), plainView('aqb')), 'control: view differs');
      assert.ok(!viewsEqual(ctl.replica(1).visible(), v(['a', B], ['q'], ['b', B])), 'control: unbold not applied');
    },
  },
  ...localMeaningPair(
    'L-002 (a) unmarking a whole hl span: an insert at its start takes hl back',
    l002a('hl'),
    { before: plainView('ab'), expected: plainView('Xab'), observed: v(['X', H], ['a'], ['b']) },
    'control for L-002 (a): the same with bold',
    { schedule: l002a('bold'), observed: plainView('Xab') },
  ),
  ...localMeaningPair(
    'L-002 (b) deleting the only hl character: an insert into its gap takes hl',
    l002b('hl'),
    { before: plainView('ac'), expected: plainView('aXc'), observed: v(['a'], ['X', H], ['c']) },
    'control for L-002 (b): the same with link',
    { schedule: l002b('link'), observed: plainView('aXc') },
  ),
  ...localMeaningPair(
    'L-003 an insert at the left boundary of an unlinked hole takes link, which expands nowhere',
    l003('link'),
    { before: v(['a', L], ['b'], ['c', L]), expected: v(['a', L], ['X'], ['b'], ['c', L]), observed: v(['a', L], ['X', L], ['b'], ['c', L]) },
    'control for L-003: the same with bold, which expands after',
    { schedule: l003('bold'), observed: v(['a', B], ['X', B], ['b'], ['c', B]) },
  ),
  ...localMeaningPair(
    'L-004 between two adjacent link spans of one value an insert takes no link',
    l004(true),
    { before: v(['a', L], ['b', L]), expected: v(['a', L], ['X', L], ['b', L]), observed: v(['a', L], ['X'], ['b', L]) },
    'control for L-004: one link span',
    { schedule: l004(false), observed: v(['a', L], ['X', L], ['b', L]) },
  ),
  {
    name: 'L-005 concurrent bold and sup on y: an insert at the head stops before the bold anchor and loses sup',
    schedule: l005('bold', 'sup'),
    run(results) {
      const trace = execute(l005('bold', 'sup'));
      const lm = trace.checks.localMeaning;
      assert.equal(lm.pass, false, 'localMeaning passed');
      const f = lm.details.failures.at(-1);
      assert.ok(viewsEqual(f.expected, v(['X', S], ['y', { ...B, ...S }])), 'the list edit differs from the hand derivation');
      assert.ok(viewsEqual(f.actual, v(['X'], ['y', { ...B, ...S }])), 'Loro shows something else');
      assert.ok(!viewsEqual(f.actual, f.expected), 'Loro shows the expected view');
      results.observed = f.actual;
      const ctl = execute(l005('sup', 'bold'));
      assert.equal(ctl.checks.localMeaning.pass, true, 'control: localMeaning failed');
      const shown = run(l005('sup', 'bold')).replica(1).visible();
      assert.ok(viewsEqual(shown, v(['X', S], ['y', { ...B, ...S }])), 'control: view differs');
      assert.ok(!viewsEqual(shown, f.actual), "control: the failing case's view");
    },
  },
];

/*
 * The classifier on the cases above: each failing schedule's classes under
 * the reading it fails in, and no class on the controls. The boundary cases
 * also state the side and whether the key's expand type extends the mark to
 * that side.
 */
const CLASSIFIED = [
  ['L-001 (Y-001 insert variant)', y001Insert(2), 'gap', 'carry', ['L-001'], { side: 'end', expandConsistent: true }],
  ['L-001 start boundary, sup', supStart, 'gap', 'carry', ['L-001'], { side: 'start', expandConsistent: true }],
  ['L-001 end boundary, sup', endBoundary('sup'), 'gap', 'carry', ['L-001'], { side: 'end', expandConsistent: false }],
  ['the bold end boundary under expand', endBoundary('bold'), 'gap', 'expand', []],
  ['Y-004 bold under expand', y004('bold', 0), 'gap', 'expand', ['L-001'], { side: 'start', expandConsistent: false }],
  ['L-001 (Y-004) bold', y004('bold', 0), 'gap', 'carry', ['L-001'], { side: 'start', expandConsistent: false }],
  ['L-001 (Y-004) link', y004('link', 0), 'gap', 'carry', ['L-001'], { side: 'start', expandConsistent: false }],
  ['L-001 end boundary, bold', endBoundary('bold'), 'gap', 'carry', ['L-001'], { side: 'end', expandConsistent: true }],
  ['L-001 end boundary, link', endBoundary('link'), 'gap', 'carry', ['L-001'], { side: 'end', expandConsistent: false }],
  ['L1 two-sided refutation', { replicas: 2, steps: bothSteps(true) }, 'both', 'carry', ['plain-order']],
  ['L-002 (a)', l002a('hl'), 'gap', 'carry', ['L-002']],
  ['L-002 (b)', l002b('hl'), 'gap', 'carry', ['L-002']],
  ['L-003', l003('link'), 'gap', 'carry', ['L-003']],
  ['L-004', l004(true), 'gap', 'carry', ['L-004']],
  ['L-005', l005('bold', 'sup'), 'gap', 'carry', ['L-005']],
  ['control Y-004', y004('bold', 1), 'gap', 'carry', []],
  ['control L-002 (a)', l002a('bold'), 'gap', 'carry', []],
  ['control L-004', l004(false), 'gap', 'carry', []],
  ['control L-005', l005('sup', 'bold'), 'gap', 'carry', []],
  ['the bold end boundary under inherit', endBoundary('bold'), 'gap', 'inherit', []],
  ['crossed boundaries under carry', crossed, 'gap', 'carry', ['L-001'], { side: 'start', expandConsistent: true }],
  ['crossed boundaries under persistent', crossed, 'gap', 'persistent', []],
];
REGRESSIONS.push({
  name: 'classifier: each failing case takes its class, each control none',
  run(results) {
    for (const [name, schedule, rule, attrs, classes, boundary] of CLASSIFIED) {
      const trace = execute(schedule, { rule, attrs });
      const c = classifyTrial(trace.checks, trace.ops);
      assert.deepEqual(c.classes, classes, `${name}: classes ${JSON.stringify(c.classes)}`);
      assert.notDeepEqual(c.classes, ['other'], `${name}: unexplained`);
      if (boundary) {
        const d = c.records[0].differences[0];
        assert.equal(d.side, boundary.side, `${name}: side ${d.side}`);
        assert.equal(d.expandConsistent, boundary.expandConsistent, `${name}: expandConsistent ${d.expandConsistent}`);
      }
    }
    results.observed = undefined;
  },
});

export function runRegressions() {
  return REGRESSIONS.map((c) => {
    const results = {};
    try {
      c.run(results);
      return { name: c.name, pass: true, results };
    } catch (e) {
      return { name: c.name, pass: false, error: e.message, results };
    }
  });
}
