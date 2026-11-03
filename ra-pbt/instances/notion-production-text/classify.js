/**
 * Mechanism classes of failures of the production Notion text instance.
 *
 *   NT-1  local meaning of an insertion: the inserted characters take the
 *         bold of the visible character to their left (plain at index 0),
 *         where positional-spec.mjs inserts plain characters. The origin is
 *         the visible left neighbour (getOriginItemForInsertionIndex,
 *         module 458789), the new item is placed immediately after it, and
 *         the rich-text walk (module 146739) gives a character the
 *         annotation set in force at the last anchor before it. Specification
 *         artefact of the positional request semantics, which has no
 *         inheritance rule.
 *   NT-2  the two-sided list rule refuted: no history inserting each
 *         character immediately before its visible right neighbour gives the
 *         displayed order. Integration (integrateItem / findInsertionPoint)
 *         is RGA: the new item goes after its origin, past every following
 *         item with a greater id, ids being [session, Lamport counter]
 *         compared counter first; the right neighbour is not consulted.
 *         Specification result about the list rule.
 *   NT-3  the interval reading refuted: a bold's end anchor is 'before' the
 *         item following the last selected character (the expanding branch
 *         of getTextSliceSpansForAnnotationOperation, module 300957), so a
 *         character placed into that gap concurrently, or later, is covered;
 *         the interval reading gives it the bold its issuer displayed.
 *         Specification artefact of the interval reading; the anchored
 *         reading admits these versions.
 *   other a failure none of the above explains: a candidate defect.
 *
 * `classifyFailure(instance, schedule, failure)` re-executes the schedule
 * up to the failing step and returns { class, evidence }.
 */
import { Execution, eventsAt, findWitness, finalSyncSteps, prepareInstance } from '../../src/index.js';
import { localEdit, renderView, normaliseView, viewKey, idKey, textSpec } from './spec.js';
import { items } from './adapter.js';

export const CLASSES = {
  'NT-1': 'insertion inherits the left neighbour’s bold (positional specification has no inheritance)',
  'NT-2': 'two-sided list rule refuted by RGA sibling order',
  'NT-3': 'bold end anchor before the next item covers characters placed into that gap (interval reading refuted)',
  other: 'unexplained: candidate defect',
};

/** The steps of an execution of `schedule` with its final synchronisation (at most eight rounds, as schedule.js). */
function allSteps(schedule) {
  const out = [...schedule.steps];
  for (let i = 0; i < 8; i++) out.push(...finalSyncSteps(schedule.replicas));
  return out;
}

/** Executes `schedule` (with final sync) without checks through step index `upTo`. */
export function executeTo(instance, schedule, upTo) {
  const ex = new Execution(prepareInstance(instance), schedule.replicas, { checks: [] });
  const steps = allSteps(schedule);
  for (let i = 0; i <= upTo && i < steps.length; i++) ex.apply(steps[i]);
  return ex;
}

/** Characters lying in the gap between a bold's last selected character and its end anchor, not known to its issuer. */
function endGapEvidence(ex, r) {
  const rep = ex.replicas[r];
  const order = items(rep.client)
    .filter((it) => it.kind === 'TextItem' || it.kind === 'EndItem')
    .flatMap((it) => (it.kind === 'EndItem' ? [{ key: 'end' }] : Array.from({ length: it.len }, (_, k) => ({ key: idKey([it.id[0], it.id[1] + k]), deleted: it.deleted, ch: it.content?.[k] }))));
  const position = new Map(order.map((e, i) => [e.key, i]));
  const known = (o) => {
    const past = new Set(o.deps);
    const ids = new Set();
    for (const p of ex.ops) if (past.has(p.key) && p.kind === 'insert') for (const c of p.chars) ids.add(idKey(c.id));
    return ids;
  };
  const out = [];
  for (const o of ex.ops) {
    if (o.kind !== 'bold' || !ex.integrated[r].has(o.key)) continue;
    const a = o.annotation;
    const endKey = a.end.id === 'end' ? 'end' : idKey(a.end.id);
    const from = position.get(idKey(a.right));
    const to = position.get(endKey) - (a.end.anchor === 'after' ? -1 : 0);
    const seen = known(o);
    const gap = order.slice(from + 1, to).filter((e) => e.key !== 'end' && !seen.has(e.key) && !e.deleted && e.key.split(':')[0] !== `s${o.replica}`);
    const own = order.slice(from + 1, to).filter((e) => e.key !== 'end' && !e.deleted);
    if (own.length) out.push({ annotation: o.key, value: a.value, last: idKey(a.right), end: `${a.end.anchor} ${endKey}`, inGap: own.map((e) => `${e.ch}(${e.key})`), unknownToIssuer: gap.map((e) => `${e.ch}(${e.key})`) });
  }
  return out;
}

const SPECS = {};
const specOf = (cfg) => (SPECS[JSON.stringify(cfg)] ??= textSpec(cfg));

/** Class of one failure record of an execution of `schedule` under `instance`. */
export function classifyFailure(instance, schedule, failure) {
  const inst = prepareInstance(instance);
  const { rule, reading } = inst.spec;
  if (failure.check === 'localMeaning' && failure.request?.kind === 'insert') {
    const inherit = normaliseView(localEdit(failure.before, failure.request, 'inherit'));
    if (viewKey(inherit) === viewKey(failure.actual)) return { class: 'NT-1', evidence: { before: renderView(failure.before), request: failure.request, positional: renderView(failure.expected), observed: renderView(failure.actual) } };
    return { class: 'other', evidence: { reason: 'local insertion differs from both local meanings' } };
  }
  if (failure.check !== 'raLinearizability') return { class: 'other', evidence: { reason: `${failure.check} failure` } };
  const ex = executeTo(inst, schedule, failure.step);
  const r = failure.replica;
  const { events } = eventsAt(ex, r);
  const target = inst.adapter.view(ex.replicas[r]);
  const witness = (cfg) => findWitness(specOf(cfg), events, target).found;
  const verdicts = {
    gapAnchored: witness({ rule: 'gap', reading: 'anchored' }),
    leftAnchored: witness({ rule: 'left', reading: 'anchored' }),
    bothAnchored: witness({ rule: 'both', reading: 'anchored' }),
    sameRuleAnchored: witness({ rule, reading: 'anchored' }),
    gapInterval: witness({ rule: 'gap', reading: 'interval' }),
  };
  const shown = renderView(normaliseView(target));
  if (rule === 'both' && !verdicts.bothAnchored && (verdicts.gapAnchored || verdicts.leftAnchored) && (reading === 'anchored' || verdicts.sameRuleAnchored || verdicts.gapInterval))
    return { class: 'NT-2', evidence: { shown, verdicts } };
  if (reading === 'interval' && verdicts.sameRuleAnchored) return { class: 'NT-3', evidence: { shown, verdicts, endGaps: endGapEvidence(ex, r) } };
  return { class: 'other', evidence: { shown, verdicts } };
}

/** Classes of every failure of a trace: [{ check, replica, step, signature, class, evidence }]. */
export function classifyTrace(instance, schedule, checks) {
  const out = [];
  for (const c of Object.values(checks)) for (const f of c.details.failures) out.push({ check: f.check, replica: f.replica, step: f.step, signature: f.signature, ...classifyFailure(instance, schedule, f) });
  return out;
}
