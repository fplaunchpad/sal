/**
 * Shared parts of the Notion ra-pbt runner: argument parsing, the law and
 * end-to-end runs, and compact renderings of counterexamples.
 */
import { checkAll, runCampaign, properties } from '../../ra-pbt/src/index.js';
import { loadModel, lawsFor, notionInstance, diagnose, classifyFailure, pathClasses, renderStep, renderBlocks, adapterStats } from '../../ra-pbt/instances/notion/index.js';

export function parseArgs(argv) {
  const out = {};
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (!a.startsWith('--')) throw new Error('unexpected argument ' + a);
    const k = a.slice(2);
    if (k === 'partial') out[k] = true;
    else out[k] = argv[++i];
  }
  return out;
}

/** Preserve unresolved law checks in JSON and terminal reports. */
export function lawReportRow(result) {
  return {
    name: result.name,
    verdict: result.status,
    pass: result.pass,
    runs: result.runs,
    vacuous: result.vacuous,
    inconclusive: result.inconclusive,
    inconclusiveExamples: result.inconclusiveExamples,
  };
}

export function lawReportCounts(properties) {
  const counts = { pass: 0, fail: 0, inconclusive: 0, vacuous: 0, 'not-applicable': 0 };
  for (const p of properties) counts[Object.hasOwn(counts, p.verdict) ? p.verdict : 'inconclusive']++;
  return counts;
}

/** Exit 1 for a failure, 2 for unresolved/no checked results, 0 for checked passes. */
export function lawReportExitCode(properties) {
  const counts = lawReportCounts(properties);
  return counts.fail ? 1 : counts.inconclusive || counts.vacuous || !counts.pass ? 2 : 0;
}

/** Law-layer counterexample: one line per event (request, transaction key, visibility). */
export function renderLawCounterexample(f) {
  return {
    kind: f.kind,
    size: f.size,
    events: f.events.map((e) => `${e.id}: ${renderStep({ type: 'edit', replica: e.replica, ...e.op.request })} = ${e.op.key} vis {${e.vis.join(',')}}`),
    sets: f.sets,
    picks: f.picks,
    detail: f.detail,
  };
}

/** The catalogue entries a law-layer failure exhibits, from the archive of its set E. */
export function classifyLaw(model, seed, f) {
  if (f.kind !== 'no-admitted-linear-extension') return { catalogue: ['unclassified'] };
  const byId = new Map(f.events.map((e) => [e.id, e]));
  const archive = [...seed.map((e) => e.tx), ...f.sets.E.map((id) => byId.get(id).op.tx)];
  const d = diagnose(model, archive);
  const catalogue = [];
  if (f.detail.closestAdmitted === null) catalogue.push('spec-stuck');
  for (const l of d.losses) catalogue.push(l.path === 'removed-target' ? 'N-004' : l.path === 'cycle-no-op' ? 'N-005' : 'loss-other');
  if (!d.losses.length && catalogue[0] !== 'spec-stuck') {
    if (d.branching) catalogue.push('N-001');
    if (d.frontCreates.length) catalogue.push('split-after-removal');
    catalogue.push(...boldClasses(model, seed, f));
    if (!catalogue.length) catalogue.push(...pathClasses(d));
  }
  return { catalogue: [...new Set(catalogue)].sort().concat(catalogue.length ? [] : ['unclassified']), losses: d.losses, branching: d.branching, frontCreates: d.frontCreates, paths: d.paths };
}

/**
 * N-002 and N-003 among the bold events of a law counterexample: an event
 * whose transaction, applied to its issuer's archive, leaves an intended
 * character with the wrong flag (missed) or changes a character outside the
 * intended selection (outside).
 */
function boldClasses(model, seed, f) {
  const out = [];
  const byId = new Map(f.events.map((e) => [e.id, e]));
  const flags = (txs) => {
    const d = new model.CrdtDocument(txs);
    const m = new Map();
    for (const b of d.aliveBlocks()) for (const c of d.blockCharacters(b.id)) m.set(`${c.textInstanceId}/${c.item.id.sessionId}:${c.item.id.counter}`, !!c.bold);
    return m;
  };
  for (const e of f.events) {
    const intent = e.op.commands.find((c) => c.kind === 'bold');
    if (!intent) continue;
    const prior = [...seed.map((x) => x.tx), ...e.vis.map((id) => byId.get(id).op.tx)];
    const before = flags(prior);
    const after = flags([...prior, e.op.tx]);
    const wanted = new Set(intent.addresses);
    if (intent.addresses.some((a) => after.get(a) !== intent.value)) out.push('N-002');
    if ([...after].some(([a, v]) => !wanted.has(a) && v !== before.get(a))) out.push('N-003');
  }
  return out;
}

/** One law-layer run of every property. */
export async function runLaws({ model: variant = 'demo', texts = ['x'], profile = 'structure', observation = 'view', replicas = 3, syncProbability = 0.3, seed = 1, trials = 150, size = 12 }) {
  const model = await loadModel(variant);
  const format = profile === 'format';
  const { datatype, instance, seed: seedEvents } = lawsFor(model, { texts, format, profile, observation, replicas, syncProbability });
  const t0 = Date.now();
  const results = checkAll(datatype, instance, { seed, trials, maxSize: size });
  return {
    model: variant,
    hashes: model.hashes,
    texts,
    profile,
    observation,
    replicas,
    syncProbability,
    seed,
    trials,
    size,
    ms: Date.now() - t0,
    properties: results.map((r) => ({
      ...lawReportRow(r),
      ...(r.failures.length ? { counterexample: renderLawCounterexample(r.failures[0]), classification: classifyLaw(model, seedEvents, r.failures[0]) } : {}),
    })),
  };
}

/** One end-to-end campaign with every failure signature shrunk and classified. */
export async function runEndToEnd({ model: variant = 'demo', texts = ['x'], profile = 'structure', seed = 1, trials = 50, steps = 12, replicas, partial = false, bound = 12 }) {
  const model = await loadModel(variant);
  const format = profile === 'format';
  const inst = notionInstance(model, { texts, format, profile });
  const rejectedBefore = adapterStats.rejected;
  const t0 = Date.now();
  const options = { steps, partialDelivery: partial, ...(replicas ? { replicas } : {}) };
  const res = runCampaign(inst, { seed, trials, bound, options, renderStep });
  const shrunk = res.shrunk.map((s) => {
    const c = s.failure ? classifyFailure(inst, s.schedule, s.failure) : { catalogue: ['not reproduced'] };
    return {
      signature: s.signature,
      trial: s.trial,
      originalSteps: s.originalSteps,
      steps: s.schedule.steps.length,
      edits: s.schedule.steps.filter((x) => x.type === 'edit').length,
      schedule: s.schedule,
      rendered: s.rendered,
      failure: s.failure && renderE2eFailure(s.failure),
      classification: c,
    };
  });
  const byCatalogue = {};
  for (const t of res.failing) {
    for (const [check, r] of Object.entries(t.checks)) {
      if (r.pass) continue;
      const f = r.details.failures[0];
      const c = classifyFailure(inst, t.schedule, f).catalogue.join('+');
      const k = `${check}:${c}`;
      byCatalogue[k] = (byCatalogue[k] ?? 0) + 1;
    }
  }
  return {
    model: variant,
    hashes: model.hashes,
    texts,
    profile,
    ms: Date.now() - t0,
    summary: { ...res.summary, rejectedRequests: adapterStats.rejected - rejectedBefore },
    failingTrialsByCheckAndClass: byCatalogue,
    shrunk,
  };
}

function renderE2eFailure(f) {
  const out = { check: f.check, replica: f.replica, step: f.step, signature: f.signature };
  if (f.request) out.request = f.request;
  if (f.before) out.before = renderBlocks(f.before);
  if (f.check === 'raLinearizability') {
    out.actual = renderBlocks(f.actual);
    out.admitted = f.expected.admittedViews.map(renderBlocks);
  } else if (f.check === 'conservation') {
    out.expected = f.expected;
    out.actual = f.actual;
  } else {
    out.expected = Array.isArray(f.expected) ? renderBlocks(f.expected) : f.expected;
    out.actual = Array.isArray(f.actual) ? renderBlocks(f.actual) : f.actual;
  }
  return out;
}

export { properties };
