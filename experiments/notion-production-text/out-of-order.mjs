/**
 * Probe, outside the main claims: delivery without causal buffering.
 *
 * The client applies an operation when it arrives. This probe replaces the
 * instance's transport by one that hands every received record to the
 * client at once, in arrival order (`send` steps deliver single records out
 * of causal order). A record whose application throws is kept and retried
 * after every later arrival; a record the client accepts is never
 * redelivered. Integration is read from the client's own state, not from
 * the transport: an insertion is integrated when all its characters are in
 * the item list, a delete when all its characters are present and deleted,
 * a bold when its operation id is in an annotation operation set.
 *
 *   node out-of-order.mjs [--seed S] [--trials N] [--output results/out-of-order.json]
 *
 * The shipped code has one out-of-order mechanism of its own: an insertion
 * whose origin is absent is preceded by a backfill of the items its
 * operation lists in `prevItems` (module 971340, backfillPrevItems),
 * annotation operations on those items included.
 */
import { resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { writeJson, Execution } from '../../ra-pbt/src/index.js';
import { notionTextAdapter, instanceFor, items, idKey, verifySources, describeVerification, renderStep } from '../../ra-pbt/instances/notion-production-text/index.js';
import { runSearch } from './search.mjs';
import { renderFailure } from './render.mjs';

/** Everything the client's item list records: present character ids, deleted ones, annotation operation ids. */
function contents(rep) {
  const present = new Set();
  const deleted = new Set();
  const annotations = new Set();
  for (const it of items(rep.client)) {
    if (it.kind === 'TextItem') for (let k = 0; k < it.len; k++) (it.deleted ? deleted : present).add(idKey([it.id[0], it.id[1] + k]));
    for (const side of ['before', 'after']) for (const o of it[side] ?? []) annotations.add(idKey(o.id));
  }
  return { present, deleted, annotations };
}

function effectPresent(record, c) {
  if (record.kind === 'insert') return record.chars.every((x) => c.present.has(idKey(x.id)) || c.deleted.has(idKey(x.id)));
  if (record.kind === 'delete') return record.deletedIds.every((x) => c.deleted.has(idKey(x)));
  return c.annotations.has(idKey(record.annotation.id));
}

export const counters = { refused: 0, refusedMessages: {}, backfilled: 0, earlyDeletes: 0 };

function receiveUnbuffered(rep, record) {
  if (rep.log.includes(record) || rep.pending.includes(record)) return;
  rep.pending.push(record);
  let progress = true;
  while (progress) {
    progress = false;
    for (const r of [...rep.pending]) {
      const before = contents(rep);
      try {
        rep.client.apply(r.update);
      } catch (e) {
        counters.refused++;
        counters.refusedMessages[e.message] = (counters.refusedMessages[e.message] ?? 0) + 1;
        continue;
      }
      const known = (id) => id === null || before.present.has(idKey(id)) || before.deleted.has(idKey(id));
      if (r.kind === 'insert' && !known(r.chars[0].origin)) counters.backfilled++;
      if (r.kind === 'delete' && !r.deletedIds.every(known)) {
        counters.earlyDeletes++;
        (rep.earlyDeletes ??= []).push(...r.deletedIds.filter((x) => !known(x)).map(idKey));
      }
      rep.pending = rep.pending.filter((p) => p !== r);
      rep.log.push(r);
      progress = true;
    }
  }
}

export const unbufferedAdapter = {
  ...notionTextAdapter,
  deliver(rep, record) {
    receiveUnbuffered(rep, record);
    return { pending: rep.pending.length > 0, emitted: [] };
  },
  sync(to, from) {
    for (const r of [...from.log, ...from.pending]) receiveUnbuffered(to, r);
    return { pending: to.pending.length > 0, emitted: [] };
  },
  integrated(rep, records) {
    const c = contents(rep);
    const integrated = new Set();
    const partial = [];
    for (const r of records) {
      if (effectPresent(r, c)) integrated.add(r.key);
      else if (rep.log.includes(r)) partial.push(r.key);
    }
    return { integrated, partial };
  },
};

export const unbuffered = { ...instanceFor({ local: 'inherit' }), adapter: unbufferedAdapter };

const CHECKED = ['convergence', 'conservation'];

/** Class of a failure: P-1 when a character the failing replica shows was named by a deletion applied before its insertion. */
function classify(schedule, trace) {
  const ex = new Execution(unbuffered, schedule.replicas, { checks: [] });
  for (const step of schedule.steps) ex.apply(step);
  ex.finish();
  return Object.values(trace.checks).flatMap((c) =>
    c.details.failures.map((f) => {
      const reps = Array.isArray(f.replica) ? f.replica : [f.replica];
      const early = reps.flatMap((r) => ex.replicas[r].earlyDeletes ?? []);
      const missing = reps.flatMap((r) => {
        const c = contents(ex.replicas[r]);
        return ex.replicas[r].log.filter((o) => o.kind === 'insert' && !effectPresent(o, c)).map((o) => o.key);
      });
      const cls = [early.length && 'P-1', missing.length && 'P-4'].filter(Boolean).join('+') || 'other';
      return { class: cls, step: f.step, early, missing };
    }),
  );
}

async function main() {
  const args = Object.fromEntries(process.argv.slice(2).reduce((acc, a, i, xs) => (a.startsWith('--') ? [...acc, [a.slice(2), xs[i + 1]]] : acc), []));
  console.log(describeVerification(verifySources()));
  const out = {};
  for (const [name, withBold] of [['plain', false], ['bold', true]]) {
    for (const k of Object.keys(counters)) counters[k] = k === 'refusedMessages' ? {} : 0;
    const res = await runSearch(unbuffered, { seed: Number(args.seed ?? 41), trials: Number(args.trials ?? 200), options: { withBold, partialDelivery: true, deliveryRate: 5 }, checks: CHECKED, classify, renderStep, renderFailure });
    res.summary.mechanisms = JSON.parse(JSON.stringify(counters));
    out[name] = res;
    const s = res.summary;
    console.log(`${name}: ${s.trials} trials, ${s.sends} sends, failing ${s.failingTrials}, ` + CHECKED.map((c) => `${c} ${s.failuresByCheck[c]}/${s.trialsFailingByCheck[c]}`).join(', ') + ` classes ${JSON.stringify(s.classes?.trials ?? {})} mechanisms ${JSON.stringify(s.mechanisms)}`);
    for (const x of res.shrunk) {
      console.log(`  ${x.signature} (trial ${x.trial}, ${x.originalSteps} -> ${x.schedule.steps.length} steps)`);
      for (const line of x.rendered) console.log('    ' + line);
      console.log('    failure: ' + JSON.stringify(x.renderedFailure));
    }
  }
  if (args.output) writeJson(args.output, out);
  verifySources();
  console.log('export verified after run');
}

if (process.argv[1] && fileURLToPath(import.meta.url) === resolve(process.argv[1])) await main();
