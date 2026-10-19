// Litmus histories for block merge. Run with `node --import ./ra-hook.mjs`:
// the hook folds the identity specification over every archive a replica
// reaches and compares it with the display (RA and conservation). This file
// adds hand-derived final displays for the base schedules, the positional
// local contract for every issued request, and convergence.
//
// Two replicas P and Q start from the same seed archive. Their session names
// are swapped between runs, which flips the replay order of their first
// concurrent transactions (equal counters order by session). Schedules:
//   exchange-pq   P issues, Q issues, Q receives P, P receives Q
//   exchange-qp   the same requests, P receives Q first
//   X-unaware     X issues one further request before receiving anything
//   X-aware       X receives the other request, then issues one further request
// Every valid positional request on X's view is tried as the further request.
import {Replica} from './replica.js';
import {iterateTextSliceTree} from './text-slice-tree.js';
import {request, splitDelete} from './positional-spec.mjs';
import {initial, view, obs, texts, valid, apply, queries} from './campaign-lib.mjs';

const state = globalThis.__raState;
if (!state) throw Error('run with --import ./ra-hook.mjs');
const shown = r => texts(obs(view(r)));
const bag = xs => xs.join('').split('').sort().join('');
const snapshot = () => JSON.parse(JSON.stringify({modes: state.modes, ex: state.replayExceptions}));
const delta = (a, b) => Object.fromEntries(Object.entries(b.modes).map(([m, c]) =>
  [m, Object.fromEntries(Object.entries(c).map(([k, v]) => [k, v - a.modes[m][k]]))]));

const merge = block => ({kind: 'merge', block});
const split = (block, index) => ({kind: 'split', block, index});
const insert = (block, index, text) => ({kind: 'insert', block, index, text});
const del = (block, start, end) => ({kind: 'delete', block, start, end});

// A step is a positional request or a function of the replica (for requests
// outside the positional vocabulary, such as createBlock).
const createAfter = (blockIndex, text = 'Z') => ({label: `create after block ${blockIndex}, then insert ${text}`, run: r => {
  const id = r.document().aliveBlocks()[blockIndex].id, {newBlockId} = r.createBlock(id);
  r.insertText(newBlockId, 0, text);
}});

// Expected final displays are hand-derived from the design's sequential
// meaning (absorb); `skip` gives the earlier meaning, `slice` the
// slice-following implementation and `anchor` anchor-absorb where they differ. `pFirst` says whether P's
// first transaction replays first; where both replicas' last transactions
// share a counter, it also decides their order.
const LITMUS = [];
for (const k of [0, 1, 2]) LITMUS.push({
  id: 'a', name: `split S at ${k} || merge S into T`, seed: ['ab', 'cd'], p: [split(1, k)], q: [merge(1)],
  expected: () => ['ab' + 'cd'.slice(0, k), 'cd'.slice(k)],
  wrong: () => ['cd'.slice(k), 'ab' + 'cd'.slice(0, k)]});
LITMUS.push({id: 'b', name: 'merge S into T || merge T into U', seed: ['a', 'b', 'c'], p: [merge(2)], q: [merge(1)],
  // P first: c joins b, then b (now bc) joins a. Q first: b joins a; c's
  // target b is held by a, so c joins a. Under skip, c's merge is then a no-op.
  expected: () => ['abc'], skip: pFirst => pFirst ? ['abc'] : ['ab', 'c'], wrong: () => ['ab']});
LITMUS.push({id: 'c', name: 'merge S into T || forged merge T into S', seed: ['a', 'b'], p: [merge(1)],
  q: [{label: 'forged mergeBlock a into b', forged: true, run: r => {
    const d = r.document(), [a, b] = d.aliveBlocks().map(x => x.id), id = r.clock.reserve();
    let last = d.blocks.get(b).title;
    for (const node of iterateTextSliceTree(d.blocks.get(b).title)) last = node;
    r.receive({id, operations: [{command: 'mergeBlock', pointer: {table: 'block', id: a}, path: [],
      args: {sourceBlockId: a, targetBlockId: b, targetTextInstanceId: last.textSlice.textInstanceId,
        targetTextSliceEndItemId: last.textSlice.endItemId}}]});
  }}],
  // P first: b joins a; the forged merge's target b is held by its own source a,
  // the cycle case, a no-op. Forged first: a joins b; then b's merge target a is
  // held by b itself, again a no-op. Skip gives the same finals. Under
  // slice-following the forged merge is anchored at the end of b's instance,
  // whose slice lies in a's tree when b's merge replays first: the same finals.
  // Anchor-absorb reads the same anchor; the anchored node's tree is rooted at
  // a, the forged merge's source: the same finals.
  expected: pFirst => pFirst ? ['ab'] : ['ba'], wrong: () => []});
for (const seed of [['ab', 'cd'], ['ab', '']]) LITMUS.push({
  id: 'd', name: `insert X at 0 of S || merge S into T, seed ${JSON.stringify(seed)}`, seed, p: [insert(1, 0, 'X')], q: [merge(1)],
  expected: () => [seed[0] + 'X' + seed[1]], wrong: () => [seed[0] + seed[1]]});
for (const k of [0, 1, 2, 3, 4]) LITMUS.push({
  id: 'e', name: `after merge: delete [1,3) across the boundary || split at ${k}`, seed: ['ab', 'cd'], setup: [merge(1)],
  p: [del(0, 1, 3)], q: [split(0, k)],
  expected: () => splitDelete('abcd', k, 1, 3), wrong: () => ['abcd'.slice(0, k), 'abcd'.slice(k)]});
LITMUS.push({id: 'f', name: 'create after S || merge S into T', seed: ['ab', 'cd'], p: [createAfter(1)], q: [merge(1)],
  // The new block lands where S was: after T, whichever replays first.
  expected: () => ['abcd', 'Z'], wrong: () => ['Z', 'abcd']});
LITMUS.push({id: 'g', name: 'split T after a || merge S into T', seed: ['ab', 'cd'], p: [split(0, 1)], q: [merge(1)],
  // P first: the split moves b to a new block F. Absorb attaches cd under T's
  // last node, giving acd and b. Slice-following follows the anchor, the end
  // of T's instance, which is now the slice holding b in F: a and bcd. Q
  // first: cd hangs under T's root, and the split moves b with cd below it.
  // Anchor-absorb, P first: the anchored node is F's root, a lone node, so cd
  // goes under it. The positional sequential result is a and bcd in both
  // orders.
  expected: pFirst => pFirst ? ['acd', 'b'] : ['a', 'bcd'], slice: () => ['a', 'bcd'], anchor: () => ['a', 'bcd'],
  wrong: () => ['a', 'b']});
LITMUS.push({id: 'h', name: 'merge U into T || merge S into T, both anchored at the end of T', seed: ['ab', 'cd'],
  p: [createAfter(0, 'Z'), merge(1)], q: [insert(1, 2, 'YW'), merge(1)],
  // Both merges have counter 9. P first: U hangs under T's root; S's anchor
  // is the same node, so S becomes its second child and renders after U. Q
  // first: S, then U. Absorb and skip chain the second source under the
  // first, with the same text; so does anchor-absorb, whose second merge
  // finds T's root and goes to the end of T's chain. Inserting S right after
  // its anchor instead
  // would give abcdYWZ when P replays first.
  expected: pFirst => pFirst ? ['abZcdYW'] : ['abcdYWZ'], wrong: pFirst => pFirst ? ['abcdYWZ'] : ['abZcdYW']});
LITMUS.push({id: 'i', name: 'then merge V into T anchored at the end of U', seed: ['ab', 'cd'],
  p: [createAfter(0, 'Z'), merge(1), createAfter(0, 'W'), merge(1)], q: [insert(1, 2, 'YX'), merge(1)],
  // P's second merge (counter 12) is issued after U joined T, so its anchor is
  // the end of U's instance. P first: T's root has children U then S, and V
  // hangs under U, rendering before S: abZWcdYX. Absorb and skip append V at
  // the end of T's chain: abZcdYXW. Q first: S, U, V under absorb and
  // slice-following alike. Anchor-absorb: V's anchored node, U's root, lies in
  // the tree rooted at T, so V goes to the end of T's chain, as under absorb.
  expected: pFirst => pFirst ? ['abZcdYXW'] : ['abcdYXZW'], slice: pFirst => pFirst ? ['abZWcdYX'] : ['abcdYXZW'],
  wrong: () => ['abZW', 'cdYX']});

const runs = [], summary = {runs: 0, localChecks: 0, localFailures: 0, finalChecks: 0, finalFailures: 0, finalSkipFailures: 0, finalSliceFailures: 0, finalAnchorFailures: 0, divergent: 0, exceptions: 0};
function issue(r, step, log) {
  if (step.run) { step.run(r); log.push({request: step.label}); return; }
  const before = obs(view(r));
  if (!valid(view(r), step)) throw Error('invalid litmus request ' + JSON.stringify(step));
  const expected = request(before, step);
  apply(r, step);
  let actual = obs(view(r));
  if (step.kind === 'insert') actual = actual.map((b, i) => i === step.block ?
    b.map((c, j) => j >= step.index && j < step.index + [...step.text].length ? {...c, bold: false} : c) : b);
  const ok = JSON.stringify(actual) === JSON.stringify(expected);
  summary.localChecks++; if (!ok) summary.localFailures++;
  log.push({request: step, local: ok ? 'agree' : {expected: texts(expected), actual: texts(actual)}});
}
const fresh = (r, prior) => r.transactions().filter(t => !prior.has(`${t.id.sessionId}:${t.id.counter}`));
const ids = r => new Set(r.transactions().map(t => `${t.id.sessionId}:${t.id.counter}`));

function run(lit, names, schedule, followup) {
  let txs = initial(lit.seed);
  if (lit.setup) { const s = new Replica('S', 'S', txs); for (const q of lit.setup) apply(s, q); txs = s.transactions(); }
  const P = new Replica(names[0], names[0], txs), Q = new Replica(names[1], names[1], txs), log = [];
  const pPrior = ids(P), qPrior = ids(Q);
  for (const s of lit.p) issue(P, s, log);
  for (const s of lit.q) issue(Q, s, log);
  const pTx = fresh(P, pPrior), qTx = fresh(Q, qPrior);
  const give = (r, list) => { for (const t of list) r.receive(t); };
  if (schedule === 'exchange-pq') { give(Q, pTx); give(P, qTx); }
  else if (schedule === 'exchange-qp') { give(P, qTx); give(Q, pTx); }
  else {
    const [X, Y, xTx, yTx] = schedule.startsWith('P') ? [P, Q, pTx, qTx] : [Q, P, qTx, pTx];
    if (schedule.endsWith('aware')) give(X, yTx);
    const prior = ids(X);
    issue(X, followup, log);
    const extra = fresh(X, prior);
    if (!schedule.endsWith('aware')) give(X, yTx);
    give(Y, xTx); give(Y, extra);
  }
  const final = [shown(P), shown(Q)];
  if (JSON.stringify(final[0]) !== JSON.stringify(final[1])) summary.divergent++;
  return {final: final[0], log};
}

const results = [];
for (const lit of LITMUS) {
  const before = snapshot(), entry = {id: lit.id, name: lit.name, base: [],
    followups: {runs: 0, localFailures: 0, divergent: 0, exceptions: 0, exceptionExample: null, localFailureExample: null}};
  for (const names of [['A', 'B'], ['B', 'A']]) {
    const pFirst = names[0] < names[1];
    for (const schedule of ['exchange-pq', 'exchange-qp']) {
      summary.runs++;
      try {
        const {final, log} = run(lit, names, schedule);
        const expected = lit.expected(pFirst), ok = JSON.stringify(final) === JSON.stringify(expected);
        const skip = (lit.skip ?? lit.expected)(pFirst), okSkip = JSON.stringify(final) === JSON.stringify(skip);
        const slice = (lit.slice ?? lit.expected)(pFirst), okSlice = JSON.stringify(final) === JSON.stringify(slice);
        const anchor = (lit.anchor ?? lit.expected)(pFirst), okAnchor = JSON.stringify(final) === JSON.stringify(anchor);
        summary.finalChecks++; if (!ok) summary.finalFailures++; if (!okSkip) summary.finalSkipFailures++;
        if (!okSlice) summary.finalSliceFailures++;
        if (!okAnchor) summary.finalAnchorFailures++;
        entry.base.push({sessions: names, pFirst, schedule, final, expected, matchesExpected: ok, matchesSkip: okSkip, matchesSlice: okSlice, matchesAnchor: okAnchor,
          avoidsDegenerate: JSON.stringify(final) !== JSON.stringify(lit.wrong(pFirst)),
          conserved: bag(final) === bag(expected), log});
      } catch (e) { summary.exceptions++; entry.base.push({sessions: names, schedule, exception: e.message}); }
    }
    for (const schedule of ['P-unaware', 'Q-unaware', 'P-aware', 'Q-aware']) {
      // Enumerate the further request on the issuing replica's actual view.
      let probe;
      try {
        let txs = initial(lit.seed);
        if (lit.setup) { const s = new Replica('S', 'S', txs); for (const q of lit.setup) apply(s, q); txs = s.transactions(); }
        const P = new Replica(names[0], names[0], txs), Q = new Replica(names[1], names[1], txs), scratch = [];
        const pPrior = ids(P), qPrior = ids(Q);
        for (const s of lit.p) issue(P, s, scratch);
        for (const s of lit.q) issue(Q, s, scratch);
        const [X, yTx] = schedule.startsWith('P') ? [P, fresh(Q, qPrior)] : [Q, fresh(P, pPrior)];
        if (schedule.endsWith('aware')) for (const t of yTx) X.receive(t);
        probe = queries(view(X));
      } catch (e) { summary.exceptions++; entry.followups.exceptions++; continue; }
      for (const f of probe) {
        summary.runs++; entry.followups.runs++;
        const localBefore = summary.localFailures, divBefore = summary.divergent;
        try {
          const {log} = run(lit, names, schedule, f), failed = log.find(x => x.local && x.local !== 'agree');
          if (failed) entry.followups.localFailureExample ??= {sessions: names, schedule, ...failed};
        }
        catch (e) { summary.exceptions++; entry.followups.exceptions++; entry.followups.exceptionExample ??= {schedule, followup: f, error: e.message}; }
        entry.followups.localFailures += summary.localFailures - localBefore;
        entry.followups.divergent += summary.divergent - divBefore;
      }
    }
  }
  entry.ra = delta(before, snapshot());
  results.push(entry);
}
console.log(JSON.stringify({summary, results}));
