/**
 * One declared case per catalogued Notion defect (N-001 to N-005), on the
 * pinned demo and on the corrected block merge (anchor-absorb), with nearby
 * controls. Every expected value below is derived by hand, from the
 * positional contract (positional-spec.mjs) or by folding the identity
 * specification over the causal linearizations of the decoded commands, as
 * the comment above each case shows; none is read off the model under test.
 * Every equality has a companion inequality against the tempting wrong
 * answer.
 *
 * Notation: `a | b` is two displayed blocks, `empty` an empty block,
 * `[a]` a bold character. Replica r has session A, B, ... unless stated.
 *
 *   node regressions.mjs        (or node run.mjs --mode regressions)
 *
 * Writes results/regressions.json. Exit 0 when every case holds.
 */
import assert from 'node:assert/strict';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';
import { execute, Execution, eventsAt, allFinalViews, findWitness, checkDeclared, runRegressions, writeJson, CHECKS, makeConfiguration, evaluator } from '../../ra-pbt/src/index.js';
import { loadModel, notionInstance, lawsFor, classifyFailure, renderBlocks, textsOf, blocksOf } from '../../ra-pbt/instances/notion/index.js';

const here = dirname(fileURLToPath(import.meta.url));

// ------------------------------------------------------------ notation

const e = (replica, kind, block, x = {}) => ({ type: 'edit', replica, kind, block, ...x });
const split = (r, block, index) => e(r, 'split', block, { index });
const merge = (r, block) => e(r, 'merge', block);
const insert = (r, block, index, text) => e(r, 'insert', block, { index, text });
const bold = (r, block, start, end) => e(r, 'bold', block, { start, end });
const send = (from, to, op) => ({ type: 'send', from, to, op });
const deliver = (from, to) => ({ type: 'deliver', from, to });
/** A view literal from block strings; `[c]` marks a bold character. */
const V = (...blocks) =>
  blocks.map((s) => {
    const out = [];
    for (let i = 0; i < s.length; i++) {
      if (s[i] === '[') {
        out.push({ text: s[i + 1], bold: true });
        i += 2;
      } else out.push({ text: s[i], bold: false });
    }
    return out;
  });
const sameKey = (inst, a, b) => inst.spec.viewKey(a) === inst.spec.viewKey(b);

/** Executes with every check; returns the trace and the set of failing checks. */
function run(inst, schedule, { finalSync = true } = {}) {
  const trace = execute(inst, schedule, { finalSync });
  const failing = CHECKS.filter((c) => !trace.checks[c].pass);
  return { trace, failing };
}

/** The displayed value at replica r after the given number of steps (no final sync). */
function shownAfter(inst, schedule, steps, r) {
  const ex = new Execution(inst, schedule.replicas, { checks: [] });
  for (const s of schedule.steps.slice(0, steps)) ex.apply(s);
  return blocksOf(ex.adapter.displayed(ex.replica(r)));
}

/** The admitted views and witness at replica r after the whole schedule (no final sync). */
function admittedAt(inst, schedule, r) {
  const ex = new Execution(inst, schedule.replicas, { checks: [] });
  for (const s of schedule.steps) ex.apply(s);
  const { events } = eventsAt(ex, r);
  return { admitted: allFinalViews(inst.spec, events), witness: findWitness(inst.spec, events, ex.adapter.view(ex.replica(r))).found };
}

/** A case asserting the exact set of failing checks and, for failures, the catalogue class. */
function verdictCase({ name, defect, model, inst, schedule, failing, finalSync = true, classOf, extra }) {
  return {
    name,
    defect,
    model,
    expected: failing.length ? `fail: ${failing.join(', ')}` : 'pass',
    run(results) {
      const r = run(inst, schedule, { finalSync });
      results.failing = r.failing;
      assert.deepEqual(r.failing, failing, `failing checks ${JSON.stringify(r.failing)}, expected ${JSON.stringify(failing)}`);
      for (const [check, cls] of Object.entries(classOf ?? {})) {
        const f = r.trace.checks[check].details.failures;
        const classes = f.map((x) => classifyFailure(inst, schedule, x).catalogue);
        results[`classes:${check}`] = classes;
        assert(classes.some((c) => c.includes(cls)), `no ${check} failure classified ${cls}: ${JSON.stringify(classes)}`);
      }
      extra?.(r, results);
    },
  };
}

/**
 * A law-layer case: the records of a schedule (no final sync) as a law
 * configuration over the transaction-archive datatype, with visibility the
 * records' causal pasts. On the full set E: the join lemma holds for every
 * pair of the replicas' event sets (merge of the branches is can of the
 * union), and sequential conformance holds exactly when `conforms`, under
 * the visible-character observation. laws.js evaluates a named property only
 * on generated configurations, so conformance is decided here by the
 * witness search over the same linearizations (linear extensions of
 * visibility) and the specification of lawsFor.
 */
function lawCase({ name, defect, model, texts, schedule, conforms, observedBag, admittedBag }) {
  return {
    name,
    defect,
    model: model.variant,
    expected: conforms ? 'join lemma and conformance hold' : 'join lemma holds, sequential conformance fails',
    run(results) {
      const inst = notionInstance(model, { texts });
      const { datatype, instance } = lawsFor(model, { texts, observation: 'bag' });
      const ex = new Execution(inst, schedule.replicas, { checks: [] });
      for (const s of schedule.steps) ex.apply(s);
      const events = ex.ops.map((o) => ({
        id: o.key.replace('#', '_'),
        replica: String(o.replica),
        seq: Number(o.key.split('#')[1]) + 1,
        op: { key: o.update.key, tx: o.update.tx, commands: o.specOps[0].commands, request: o.request },
        vis: o.deps.map((d) => d.replace('#', '_')),
      }));
      const cfg = makeConfiguration(events);
      const ev = evaluator(datatype, instance, cfg);
      const ids = events.map((x) => x.id);
      const sets = Object.keys(ex.replicas).map((r) => [...ex.integrated[r]].map((k) => k.replace('#', '_')));
      for (const a of sets)
        for (const b of sets) {
          const l = a.filter((x) => b.includes(x));
          const u = [...new Set([...a, ...b])];
          assert(ev.eq(ev.merge(ev.can(l), ev.can(a), ev.can(b)), ev.can(u)), 'join lemma fails');
        }
      const shown = datatype.read(ev.can(ids));
      const bagSpec = { ...inst.spec, viewKey: (v) => JSON.stringify(textsOf(v).join('').split('').sort().join('')) };
      const wEvents = events.map((x) => ({ key: x.id, deps: x.vis, specOps: [x.op] }));
      const admitted = [...new Set(allFinalViews(bagSpec, wEvents).map((v) => textsOf(v).join('').split('').sort().join('')))];
      results.observed = shown;
      results.admitted = admitted;
      assert.equal(shown, observedBag);
      assert.deepEqual(admitted, admittedBag);
      assert.equal(admitted.includes(shown), conforms);
    },
  };
}

// ------------------------------------------------------------ cases

export async function cases() {
  const demo = await loadModel('demo');
  const fixed = await loadModel('anchor-absorb');
  const out = [];
  const both = (f) => {
    for (const m of [demo, fixed]) out.push(...f(m, m === demo));
  };

  /*
   * N-005: a delayed block merge hides a character. Seed `x`. A splits at 0
   * (a0: x moves to A's new block); B splits at 1 (b0) and merges the new
   * empty block back (b1, anchored at the end of the seed's slice before
   * B's marker, s/^B); A receives b0 only, shows `empty | empty | x`, and
   * merges the block holding x into its predecessor B's block (a1, anchored
   * at s/^end); b1 then arrives.
   * Linearizations (a0 < a1, b0 < b1, b0 < a1): in a0 b0 b1 a1 and b0 a0 b1 a1
   * b1's holder is A's block (it holds s/^B), which absorbs B's block, and a1
   * is the holder-is-source no-op; in a0 b0 a1 b1 and b0 a0 a1 b1 a1 moves x
   * into B's block, after which b1's holder is the source and b1 is a no-op;
   * in b0 b1 a0 a1, b1 folds B's block into the seed, a0 moves x to A's block
   * and a1 is a no-op. Each gives `empty | x`: admitted = { empty | x }.
   * The demo shows `empty` (x stored in a removed block), so no witness;
   * the corrected merge shows `empty | x`.
   */
  const n005 = {
    replicas: 2,
    steps: [split(1, 0, 0), split(2, 0, 1), merge(2, 1), send(2, 1, 0), merge(1, 2), send(2, 1, 1)],
  };
  both((m, isDemo) => {
    const inst = notionInstance(m, { texts: ['x'] });
    return [
      {
        name: `N-005 ${m.variant}: declared view at A after the delayed merge`,
        defect: 'N-005',
        model: m.variant,
        expected: isDemo ? 'raLinearizability fails (no witness)' : 'witness',
        run(results) {
          const c = {
            name: 'N-005 declared',
            schedule: n005,
            replicas: [1],
            observed: isDemo ? V('') : V('', 'x'),
            notObserved: isDemo ? [V('', 'x')] : [V('')],
            admitted: [V('', 'x')],
            witness: !isDemo,
          };
          checkDeclared(inst, c, results);
          results.observed = renderBlocks(results.observed);
          results.admitted = results.admitted.map(renderBlocks);
        },
      },
      verdictCase({
        name: `N-005 ${m.variant}: checks with the final sync`,
        defect: 'N-005',
        model: m.variant,
        inst,
        schedule: n005,
        failing: isDemo ? ['raLinearizability', 'conservation'] : [],
        classOf: isDemo ? { raLinearizability: 'N-005', conservation: 'N-005' } : undefined,
        extra(r) {
          // Both replicas converge on the loss: convergence alone does not catch it.
          const fin = r.trace.snapshots.slice(-1)[0].visible;
          assert.equal(r.trace.checks.convergence.pass, true);
          assert.deepEqual(textsOf(fin), isDemo ? [''] : ['', 'x']);
          assert.notDeepEqual(textsOf(fin), isDemo ? ['', 'x'] : ['']);
        },
      }),
    ];
  });
  // Law layer, N-005: the join lemma holds (merge is the union of
  // transaction sets); conformance fails on the demo, where can(E) shows no
  // character while every linearization shows x.
  for (const m of [demo, fixed])
    out.push(lawCase({ name: `N-005 ${m.variant}: law layer on the four records`, defect: 'N-005', model: m, texts: ['x'], schedule: n005,
      conforms: m === fixed, observedBag: m === demo ? '' : 'x', admittedBag: ['x'] }));
  // Controls of N-005 on the demo, each changing one ingredient: the held
  // merge never arrives (no final sync; A shows `empty | x`); A does not
  // merge (b1 folds B's empty block back: `empty | x`); the held merge
  // arrives before A's merge (A then merges block 1, the block holding x).
  {
    const inst = notionInstance(demo, { texts: ['x'] });
    const noDelivery = { replicas: 2, steps: n005.steps.slice(0, 5) };
    const noLocalMerge = { replicas: 2, steps: [split(1, 0, 0), split(2, 0, 1), merge(2, 1), send(2, 1, 0), send(2, 1, 1)] };
    const early = { replicas: 2, steps: [split(1, 0, 0), split(2, 0, 1), merge(2, 1), send(2, 1, 0), send(2, 1, 1), merge(1, 1)] };
    out.push(
      verdictCase({ name: 'N-005 control demo: held merge never arrives', defect: 'N-005', model: 'demo', inst, schedule: noDelivery, failing: [], finalSync: false,
        extra: () => assert.deepEqual(textsOf(shownAfter(inst, noDelivery, 5, 1)), ['', 'x']) }),
      verdictCase({ name: 'N-005 control demo: A does not merge', defect: 'N-005', model: 'demo', inst, schedule: noLocalMerge, failing: [],
        extra: (r) => {
          assert.deepEqual(textsOf(r.trace.snapshots.slice(-1)[0].visible), ['', 'x']);
          assert.notDeepEqual(textsOf(r.trace.snapshots.slice(-1)[0].visible), ['']);
        } }),
      verdictCase({ name: 'N-005 control demo: held merge arrives first', defect: 'N-005', model: 'demo', inst, schedule: early, failing: [],
        extra: (r) => assert.notDeepEqual(textsOf(r.trace.snapshots.slice(-1)[0].visible).join(''), '') }),
    );
  }

  /*
   * N-004: a block merge into a removed block hides the whole document.
   * Seed `a | b | c`. A: merge c into b (a0), split that block at 0 (a1),
   * merge it back (a2). B: merge b into a (b0), receives a0 and a1, merges
   * its block 1 into its predecessor (b1), then receives a2.
   * Split and merge commands of the specification never hide a visible slot
   * (a merge moves the source's slots to the holder; a split moves a suffix),
   * so every admitted view shows the multiset abc. The demo shows no block:
   * no witness, and conservation fails after the final sync. Convergence
   * holds. On the corrected merge, B's view before b1 is `a | bc`, B merges
   * block 1, and abc stays visible.
   * Separately, the demo's display `empty | abc` at B after a1 is not
   * admitted: in every linearization a1 splits b's slots, which b0 moved into
   * a, after b's start, giving `a | bc`; the demo creates a1's block in front
   * of the document (its predecessor b left the display order) and moves no
   * text. The classifier names this outside the catalogue.
   */
  const n004 = {
    replicas: 2,
    steps: [merge(1, 2), split(1, 1, 0), merge(1, 2), merge(2, 1), send(1, 2, 0), send(1, 2, 1), merge(2, 1), send(1, 2, 2)],
  };
  both((m, isDemo) => {
    const inst = notionInstance(m, { texts: ['a', 'b', 'c'] });
    return [
      {
        name: `N-004 ${m.variant}: admitted views at B keep abc`,
        defect: 'N-004',
        model: m.variant,
        expected: isDemo ? 'raLinearizability fails (no witness)' : 'witness',
        run(results) {
          const { admitted, witness } = admittedAt(inst, n004, 2);
          const shown = shownAfter(inst, n004, n004.steps.length, 2);
          results.observed = renderBlocks(shown);
          results.admitted = admitted.map(renderBlocks);
          assert(admitted.length > 0, 'the specification admits no view');
          for (const v of admitted) assert.equal(textsOf(v).join('').split('').sort().join(''), 'abc');
          assert.equal(witness, !isDemo);
          if (isDemo) {
            assert.deepEqual(textsOf(shown), []);
            assert.equal(textsOf(shownAfter(inst, n004, 6, 2)).join('|'), '|abc');
            assert.notEqual(textsOf(shownAfter(inst, n004, 6, 2)).join('|'), 'a|bc');
          } else {
            assert.equal(textsOf(shown).join(''), 'abc');
            assert.deepEqual(textsOf(shownAfter(inst, n004, 6, 2)), ['a', 'bc']);
          }
        },
      },
      verdictCase({
        name: `N-004 ${m.variant}: checks with the final sync`,
        defect: 'N-004',
        model: m.variant,
        inst,
        schedule: n004,
        failing: isDemo ? ['raLinearizability', 'conservation'] : [],
        classOf: isDemo ? { raLinearizability: 'N-004', conservation: 'N-004' } : undefined,
        extra(r, results) {
          assert.equal(r.trace.checks.convergence.pass, true);
          if (isDemo) {
            const classes = r.trace.checks.raLinearizability.details.failures.map((f) => classifyFailure(inst, n004, f).catalogue.join('+'));
            results.raLinearizabilityClasses = classes;
            assert(classes.includes('split-after-removal'), 'the empty | abc precondition is not reported');
          }
        },
      }),
    ];
  });
  // Law layer, N-004: as for N-005, with the visible multiset abc.
  for (const m of [demo, fixed])
    out.push(lawCase({ name: `N-004 ${m.variant}: law layer on the five records`, defect: 'N-004', model: m, texts: ['a', 'b', 'c'], schedule: n004,
      conforms: m === fixed, observedBag: m === demo ? '' : 'abc', admittedBag: ['abc'] }));
  // Controls of N-004 on the demo: B omits its first merge, or B receives a2
  // and issues no last merge. Both keep abc visible (conservation holds). In
  // the second, B still passes through `empty | abc`, so RA-linearizability
  // fails there with the split-after-removal class and no other.
  {
    const inst = notionInstance(demo, { texts: ['a', 'b', 'c'] });
    const noFirst = { replicas: 2, steps: [merge(1, 2), split(1, 1, 0), merge(1, 2), send(1, 2, 0), send(1, 2, 1), merge(2, 1), send(1, 2, 2)] };
    const lastEarly = { replicas: 2, steps: [merge(1, 2), split(1, 1, 0), merge(1, 2), merge(2, 1), send(1, 2, 0), send(1, 2, 1), send(1, 2, 2)] };
    const keepsAbc = (r) => {
      const fin = textsOf(r.trace.snapshots.slice(-1)[0].visible).join('');
      assert.equal(fin.split('').sort().join(''), 'abc');
      assert.notEqual(fin, '');
    };
    out.push(
      verdictCase({ name: 'N-004 control demo: B omits its first merge', defect: 'N-004', model: 'demo', inst, schedule: noFirst, failing: [], extra: keepsAbc }),
      verdictCase({
        name: 'N-004 control demo: a2 arrives before B merges, B does not merge',
        defect: 'N-004',
        model: 'demo',
        inst,
        schedule: lastEarly,
        failing: ['raLinearizability'],
        extra(r) {
          keepsAbc(r);
          const classes = r.trace.checks.raLinearizability.details.failures.map((f) => classifyFailure(inst, lastEarly, f).catalogue.join('+'));
          assert(classes.every((c) => c === 'split-after-removal'), JSON.stringify(classes));
        },
      }),
    );
  }

  /*
   * N-001: a split at zero moves only part of the displayed suffix. Sessions
   * S, A, B, C, D. Seed `a`. S splits at 0 and inserts X into the empty
   * first block (`X | a`); A and B both merge the second block (`Xa`), A
   * receives B's merge; C and D start from A's archive; C splits at 0, D at
   * 1; C receives D's split (`empty | a | X`); C merges block 2 into its
   * predecessor (`empty | aX`); C splits block 1 at 0.
   * Positional contract of the last request on `empty | aX`: split block 1
   * at 0 gives `empty | empty | aX`. The demo gives `empty | X | a`.
   * Sequential control: the seed `empty | aX` and the same request give
   * `empty | empty | aX` on the demo.
   */
  const n001 = {
    replicas: 5,
    steps: [
      split(1, 0, 0), insert(1, 0, 0, 'X'), deliver(1, 2), deliver(1, 3),
      merge(2, 1), merge(3, 1), deliver(3, 2), deliver(2, 4), deliver(2, 5),
      split(4, 0, 0), split(5, 0, 1), send(5, 4, 0), merge(4, 2), split(4, 1, 0),
    ],
  };
  const sessions = ['S', 'A', 'B', 'C', 'D'];
  both((m, isDemo) => {
    const inst = notionInstance(m, { texts: ['a'], sessions });
    return [
      verdictCase({
        name: `N-001 ${m.variant}: split after concurrent restructuring`,
        defect: 'N-001',
        model: m.variant,
        inst,
        schedule: n001,
        failing: isDemo ? ['raLinearizability', 'localMeaning'] : [],
        classOf: isDemo ? { localMeaning: 'N-001', raLinearizability: 'N-001' } : undefined,
        extra(r, results) {
          assert.deepEqual(textsOf(shownAfter(inst, n001, 13, 4)), ['', 'aX']);
          const after = textsOf(shownAfter(inst, n001, 14, 4));
          results.after = after;
          assert.deepEqual(after, isDemo ? ['', 'X', 'a'] : ['', '', 'aX']);
          assert.notDeepEqual(after, isDemo ? ['', '', 'aX'] : ['', 'X', 'a']);
          if (isDemo) {
            const f = r.trace.checks.localMeaning.details.failures[0];
            assert.equal(f.step, 13);
            assert.deepEqual(textsOf(f.expected), ['', '', 'aX']);
          }
        },
      }),
    ];
  });
  {
    const inst = notionInstance(demo, { texts: ['', 'aX'] });
    const control = { replicas: 1, steps: [split(1, 1, 0)] };
    out.push(
      verdictCase({
        name: 'N-001 control demo: the same split on empty | aX reached directly',
        defect: 'N-001',
        model: 'demo',
        inst,
        schedule: control,
        failing: [],
        extra: () => {
          assert.deepEqual(textsOf(shownAfter(inst, control, 1, 1)), ['', '', 'aX']);
          assert.notDeepEqual(textsOf(shownAfter(inst, control, 1, 1)), ['', 'X', 'a']);
        },
      }),
    );
  }
  /*
   * N-001, six-request variant (experiments/notion-correctness). Sessions
   * S, A, B, C. Seed `ab`. S splits block 0 at 0 twice (`empty | empty | ab`);
   * A splits block 2 at 1 and merges block 2 back; B merges block 2;
   * after exchange C merges block 2 (`empty | ab`) and splits block 1 at 0.
   * Contract: `empty | empty | ab`; the demo gives `empty | b | a`.
   */
  const six = {
    replicas: 4,
    steps: [
      split(1, 0, 0), split(1, 0, 0), deliver(1, 2), deliver(1, 3),
      split(2, 2, 1), merge(2, 2), merge(3, 2), deliver(2, 4), deliver(3, 4),
      merge(4, 2), split(4, 1, 0),
    ],
  };
  both((m, isDemo) => {
    const inst = notionInstance(m, { texts: ['ab'], sessions: ['S', 'A', 'B', 'C'] });
    return [
      verdictCase({
        name: `N-001 ${m.variant}: six-request variant`,
        defect: 'N-001',
        model: m.variant,
        inst,
        schedule: six,
        failing: isDemo ? ['raLinearizability', 'localMeaning'] : [],
        classOf: isDemo ? { localMeaning: 'N-001' } : undefined,
        extra(r, results) {
          const after = textsOf(shownAfter(inst, six, 11, 4));
          results.after = after;
          assert.deepEqual(textsOf(shownAfter(inst, six, 10, 4)), ['', 'ab']);
          assert.deepEqual(after, isDemo ? ['', 'b', 'a'] : ['', '', 'ab']);
          assert.notDeepEqual(after, isDemo ? ['', '', 'ab'] : ['', 'b', 'a']);
        },
      }),
    ];
  });

  /*
   * N-002: bold changes neither selected character. Seed `ab`. A splits at 0
   * (a0), B at 1 (b0); A receives b0 and shows `empty | b | a`; A merges
   * block 2 (holding a) into its predecessor (a1, anchored at s/^end in B's
   * block), showing `empty | ba`; A toggles bold on block 1 [0, 2) (a2: bold
   * b, a). In a0 b0 a1 and b0 a0 a1 the holder of s/^end is B's block, which
   * absorbs A's block: `empty | ba`; a2 sets both bold. Admitted =
   * { empty | [b][a] }. The demo shows `empty | ba` (no witness); local
   * meaning fails. The corrected merge does not change formatting: the same.
   * Control: merge block 1 instead (`b | a`) and bold block 0 [0, 1): the
   * demo shows `[b] | a`, as the contract requires.
   */
  const n002 = { replicas: 2, steps: [split(1, 0, 0), split(2, 0, 1), send(2, 1, 0), merge(1, 2), bold(1, 1, 0, 2)] };
  const boldControl = { replicas: 2, steps: [split(1, 0, 0), split(2, 0, 1), send(2, 1, 0), merge(1, 1), bold(1, 0, 0, 1)] };
  /*
   * N-003: bold changes an unselected character in another block. Seed
   * `abc`. A splits at 1 (a0), B at 2 (b0); A receives b0 and shows
   * `a | c | b`; A merges block 1 (c, B's block) into the seed block (a1,
   * anchored at s/^A, which stays in the seed block); A toggles bold on block
   * 0 [0, 2) (a2: bold a, c). In a0 b0 a1 and b0 a0 a1 the seed block absorbs
   * c: `ac | b`. Admitted = { [a][c] | b }. The demo shows `[a][c] | [b]`.
   * Control: on `ac | b`, bold only block 0 [0, 1): `[a]c | b`.
   */
  const n003 = { replicas: 2, steps: [split(1, 0, 1), split(2, 0, 2), send(2, 1, 0), merge(1, 1), bold(1, 0, 0, 2)] };
  const n003Control = { replicas: 2, steps: [split(1, 0, 1), split(2, 0, 2), send(2, 1, 0), merge(1, 1), bold(1, 0, 0, 1)] };
  both((m) => {
    const ab = notionInstance(m, { texts: ['ab'], format: true });
    const abc = notionInstance(m, { texts: ['abc'], format: true });
    return [
      {
        name: `N-002 ${m.variant}: declared view after the bold toggle`,
        defect: 'N-002',
        model: m.variant,
        expected: 'raLinearizability fails (no witness)',
        run(results) {
          checkDeclared(ab, { name: 'N-002', schedule: n002, replicas: [1], observed: V('', 'ba'), notObserved: [V('', '[b][a]')], admitted: [V('', '[b][a]')], witness: false }, results);
          results.observed = renderBlocks(results.observed);
          results.admitted = results.admitted.map(renderBlocks);
        },
      },
      verdictCase({ name: `N-002 ${m.variant}: checks`, defect: 'N-002', model: m.variant, inst: ab, schedule: n002,
        failing: ['raLinearizability', 'localMeaning'], classOf: { localMeaning: 'N-002', raLinearizability: 'N-002' } }),
      verdictCase({ name: `N-002 control ${m.variant}: bold the other merge's block`, defect: 'N-002', model: m.variant, inst: ab, schedule: boldControl, failing: [],
        extra: () => {
          const v = shownAfter(ab, boldControl, 5, 1);
          assert(sameKey(ab, v, V('[b]', 'a')));
          assert(!sameKey(ab, v, V('b', 'a')));
        } }),
      {
        name: `N-003 ${m.variant}: declared view after the bold toggle`,
        defect: 'N-003',
        model: m.variant,
        expected: 'raLinearizability fails (no witness)',
        run(results) {
          checkDeclared(abc, { name: 'N-003', schedule: n003, replicas: [1], observed: V('[a][c]', '[b]'), notObserved: [V('[a][c]', 'b')], admitted: [V('[a][c]', 'b')], witness: false }, results);
          results.observed = renderBlocks(results.observed);
          results.admitted = results.admitted.map(renderBlocks);
        },
      },
      verdictCase({ name: `N-003 ${m.variant}: checks`, defect: 'N-003', model: m.variant, inst: abc, schedule: n003,
        failing: ['raLinearizability', 'localMeaning'], classOf: { localMeaning: 'N-003', raLinearizability: 'N-003' } }),
      verdictCase({ name: `N-003 control ${m.variant}: bold one character`, defect: 'N-003', model: m.variant, inst: abc, schedule: n003Control, failing: [],
        extra: () => {
          const v = shownAfter(abc, n003Control, 5, 1);
          assert(sameKey(abc, v, V('[a]c', 'b')));
          assert(!sameKey(abc, v, V('[a][c]', '[b]')));
        } }),
    ];
  });
  return out;
}

export async function main() {
  const list = await cases();
  const results = runRegressions(list);
  const rows = list.map((c, i) => ({ name: c.name, defect: c.defect, model: c.model, expected: c.expected, pass: results[i].pass, ...(results[i].error ? { error: results[i].error } : {}), results: results[i].results }));
  for (const r of rows) console.log(`${r.pass ? 'ok  ' : 'FAIL'} ${r.name}${r.error ? '\n     ' + r.error : ''}`);
  const failed = rows.filter((r) => !r.pass).length;
  console.log(`${rows.length - failed}/${rows.length} regressions hold`);
  writeJson(join(here, 'results', 'regressions.json'), { cases: rows });
  return failed ? 1 : 0;
}

if (process.argv[1] === fileURLToPath(import.meta.url)) process.exit(await main());
