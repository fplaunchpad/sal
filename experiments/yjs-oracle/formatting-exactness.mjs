/**
 * Formatting exactness: does a format request over a visible index range
 * mark exactly the characters in that range, on every reachable state?
 *
 * Reachable states come from seeded concurrent histories (`generate` with
 * formatting on). After every step, the acting replica is forked twice, once
 * created fresh and synced and once opened by loading its state, and every
 * nonempty visible range of each fork receives each attribute delta in turn
 * on a fresh copy. The oracle is `localEdit`: the characters in the range
 * carry the delta merged into their attributes, every other character is
 * unchanged. Two companions show that the comparison can fail: an
 * over-wide expectation (one extra character marked) and an under-wide one
 * (one selected character left as it was) are rejected whenever the range
 * leaves room for them. Results go to results/formatting-exactness.json.
 *
 *   node formatting-exactness.mjs [--seed S] [--trials N]
 */
import { mkdirSync, writeFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { verifySources, Replica, generate, Execution, localEdit, viewsEqual, normaliseAttrs } from '../../ra-pbt/instances/yjs/index.js';

const here = dirname(fileURLToPath(import.meta.url));
const args = process.argv.slice(2);
const arg = (name, fallback) => {
  const i = args.indexOf(name);
  return i === -1 ? fallback : Number(args[i + 1]);
};
const seed = arg('--seed', 41);
const trials = arg('--trials', 60);
const DELTAS = [{ bold: true }, { bold: null }, { italic: true }, { italic: null }];

const norm = (v) => v.map((c) => ({ ch: c.ch, attrs: normaliseAttrs(c.attrs) }));

/** A fresh replica holding `src`'s state, created or opened. */
function fork(src, clientID, opened) {
  const r = new Replica(clientID, { loaded: opened });
  if (opened) r.loadFrom(src);
  else r.syncFrom(src);
  return r;
}

verifySources();
const stats = { trials: 0, states: 0, probes: 0, characters: 0, failures: [], overWideRejected: 0, underWideRejected: 0, companionsPossible: 0 };
let nextClient = 5000;
for (let t = 0; t < trials; t++) {
  const schedule = generate((seed * 1000003 + t) >>> 0, { withFormat: true, openedReplicas: t % 2 === 1 });
  const ex = new Execution(schedule.replicas, { checks: [] });
  stats.trials++;
  schedule.steps.forEach((step, index) => {
    ex.apply(step);
    const actor = step.type === 'edit' ? step.replica : step.type === 'open' ? step.replica : step.to;
    const src = ex.replica(actor);
    if (src.visible().length === 0) return;
    stats.states++;
    for (const opened of [false, true]) {
      const base = fork(src, nextClient++, opened);
      const before = norm(base.visible());
      for (let from = 0; from < before.length; from++) {
        for (let len = 1; from + len <= before.length; len++) {
          for (const delta of DELTAS) {
            const request = { kind: 'format', index: from, len, attrs: delta };
            const expected = localEdit(before, request);
            const probe = fork(base, nextClient++, opened);
            let actual;
            try {
              probe.format(from, len, delta);
              actual = norm(probe.visible());
            } catch (e) {
              // A format that changes nothing emits no update; the view is unchanged.
              if (!/emitted no update/.test(e.message)) throw e;
              actual = norm(probe.visible());
            }
            stats.probes++;
            stats.characters += before.length;
            if (!viewsEqual(expected, actual)) {
              stats.failures.push({ trial: t, step: index, replica: actor, opened, before, request, expected, actual });
            }
            // Companions: the comparison rejects an expectation that marks one
            // character too many, and one that leaves a selected character as it was.
            if (from + len < before.length && viewsEqual(localEdit(before, { ...request, len: len + 1 }), localEdit(before, request)) === false) {
              stats.companionsPossible++;
              if (!viewsEqual(localEdit(before, { ...request, len: len + 1 }), actual)) stats.overWideRejected++;
            }
            if (len > 1 && !viewsEqual(localEdit(before, { ...request, len: len - 1 }), expected)) {
              if (!viewsEqual(localEdit(before, { ...request, len: len - 1 }), actual)) stats.underWideRejected++;
            }
          }
        }
      }
    }
  });
}
verifySources();

const out = {
  yjs: verifySources(),
  node: process.version,
  seed,
  trials: stats.trials,
  statesProbed: stats.states,
  formatProbes: stats.probes,
  characterChecks: stats.characters,
  failures: stats.failures.length,
  failureRecords: stats.failures.slice(0, 50),
  companions: {
    overWideExpectationsRejected: stats.overWideRejected,
    overWideExpectationsPossible: stats.companionsPossible,
    underWideExpectationsRejected: stats.underWideRejected,
  },
  status: 'measured on the pinned version; not proved',
};
mkdirSync(join(here, 'results'), { recursive: true });
writeFileSync(join(here, 'results', 'formatting-exactness.json'), JSON.stringify(out, null, 2) + '\n');
console.log(`formatting exactness: ${stats.probes} format probes over ${stats.states} reachable states (${stats.trials} trials, seed ${seed}), ${stats.failures.length} failures; over-wide expectations rejected ${stats.overWideRejected}/${stats.companionsPossible}, under-wide rejected ${stats.underWideRejected}`);
if (stats.failures.length || stats.overWideRejected !== stats.companionsPossible) process.exitCode = 1;
