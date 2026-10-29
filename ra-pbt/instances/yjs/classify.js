/**
 * Mechanism classification of check failures in executed schedules.
 *
 * Classes (stable ids). A character depends on markers: the opener its
 * writer relied on (the governing marker at issue time, or for a format
 * whose identity interval contains the character, the opener at its left
 * endpoint) and the closer that ended the span it was outside of.
 *   Y-001 marker ownership             such a marker was deleted by a format op
 *                                      unaware of the dependency (concurrent with
 *                                      the writer, the span's owner, or the
 *                                      character's insert): formatText deletes every
 *                                      live marker of its key in its range and,
 *                                      absorbing an equal opener, emits no closer
 *   Y-002 opening marker judged        such a marker was deleted by a cleanup op
 *         redundant                    (cleanupYTextFormatting), as overwritten by a
 *                                      later marker of the same key in its gap
 *   Y-003 delete removes neighbour     such a marker was deleted by a delete op
 *         formatting                   (cleanupFormattingGap from deleteText)
 *                                      unaware of the dependency
 *   Y-004 boundary spread              no marker deleted; the opener or the closer
 *                                      of a live span lies beyond a concurrently
 *                                      inserted character its creator never wrote
 *   Y-005 overlapping same attribute   a live marker of the same key, created by an
 *                                      op concurrent with the writer that does not
 *                                      write the character (a format's closer or an
 *                                      insert's restoring marker), restores the
 *                                      value its creator saw inside the writer's
 *                                      span
 *   other                              none of the above; the record carries the
 *                                      item walk, and a `pattern` when it matches
 *                                      a recognised shape (character order outside
 *                                      the admitted orders; a format interval
 *                                      missing a concurrent insert inside it)
 *
 * Outside these classes: `Y-006`, the opened-document family (determinism
 * failures, which compare a created fork with an opened one), and `final-sync`
 * (conservation failures, and final convergence failures, in which every op
 * missing at a replica is a cleanup that replica never received; see
 * `diagnoseConservation`).
 *
 * Method. A schedule is re-executed step by step without checks. After each
 * edit, the issuing replica's governing marker (the last live format item of
 * each key to the left) is recorded for every character the edit wrote:
 * inserted characters, or the characters a format covered. At a failing
 * step, the replica's displayed view is compared with the nearest reference
 * view (the admitted view with the same character string and fewest
 * differing attributes, or the local-meaning expectation), character by
 * character and key by key. Each difference is explained from the replica's
 * item walk, the op that created each marker (from its update's structs) and
 * the ops that deleted it (from their updates' delete sets).
 */
import { readFileSync, writeFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { Execution, finalSyncSteps, allFinalViews, eventsAt, CHECKS } from './index.js';
import { DEFAULT_WITNESS_STATE_LIMIT } from '../../src/checks.js';
import { normaliseAttrs } from './spec.js';

export const CLASSES = {
  'Y-001': 'marker ownership',
  'Y-002': 'opening marker judged redundant',
  'Y-003': 'delete removes neighbour formatting',
  'Y-004': 'boundary spread',
  'Y-005': 'overlapping same attribute',
  'Y-006': 'opened document',
  other: 'other',
};

const k2 = (id) => id[0] + ':' + id[1];

/** Unit ids (client:clock) of an item. */
function unitKeys(it) {
  const out = [];
  for (let k = 0; k < it.len; k++) out.push(it.id[0] + ':' + (it.id[1] + k));
  return out;
}

/**
 * Governing markers of every string unit: Map unit -> { key: markerItem }
 * for the last live format item of each key to the left. Also returns the
 * unit order (deleted characters included).
 */
function governance(items) {
  const live = {};
  const gov = new Map();
  const order = [];
  for (const it of items) {
    if (it.kind === 'format') {
      if (!it.deleted) live[it.key] = it;
    } else if (it.kind === 'string') {
      for (const u of unitKeys(it)) {
        gov.set(u, { ...live });
        order.push(u);
      }
    }
  }
  return { gov, order };
}

/** Compact rendering of a view: characters, with attributes in brackets. */
export function renderView(v) {
  return v
    .map((e) => {
      const ks = Object.keys(normaliseAttrs(e.attrs)).sort();
      return ks.length ? `${e.ch}(${ks.join(',')})` : e.ch;
    })
    .join(' ');
}

/** Item walk rendered on one line: markers as [key=value@id], tombstones with x. */
export function renderItems(items) {
  return items
    .map((it) => {
      const id = k2(it.id);
      const x = it.deleted ? 'x' : '';
      if (it.kind === 'format') return `[${it.key}=${it.value}@${id}]${x}`;
      if (it.kind === 'string') return `"${it.str}"@${id}${x}`;
      return `?@${id}${x}`;
    })
    .join(' ');
}

/** Creator op of every struct unit, and deleter ops of every deleted unit. */
function provenance(ex) {
  const creator = new Map();
  const deleters = new Map();
  for (const o of ex.ops) {
    for (const s of o.effect.structs) for (let c = s.from; c < s.to; c++) creator.set(s.client + ':' + c, o);
    for (const d of o.effect.deletes)
      for (let c = d.clock; c < d.clock + d.len; c++) {
        const u = d.client + ':' + c;
        if (!deleters.has(u)) deleters.set(u, []);
        deleters.get(u).push(o);
      }
  }
  return { creator, deleters };
}

const precedes = (a, b) => b.deps.includes(a.key);
const concurrent = (a, b) => a !== b && !precedes(a, b) && !precedes(b, a);

/** The value op `o` writes for `key` on the characters it wrote, or undefined. */
function writes(o, key) {
  if (o.kind === 'format') return Object.prototype.hasOwnProperty.call(o.request.attrs, key) ? o.request.attrs[key] ?? null : undefined;
  if (o.kind === 'insert') return o.request.attrs?.[key] ?? null;
  return undefined;
}

const DELETER_CLASS = { format: 'Y-001', cleanup: 'Y-002', delete: 'Y-003' };

const opSummary = (o) => o && { key: o.key, kind: o.kind, request: o.request };

/**
 * Explains one difference: character unit `u` shows `actual` for `key` where
 * the reference has `wanted`. Returns { class, ... evidence }.
 */
function explain(ctx, u, key, actual, wanted) {
  const { ex, issue, items, gov, order, creator, deleters, integrated } = ctx;
  const itemById = new Map(items.map((it) => [k2(it.id), it]));
  const pos = new Map();
  items.forEach((it, i) => {
    for (const x of unitKeys(it)) pos.set(x, i);
  });
  const charOp = creator.get(u);
  const intOps = ex.ops.filter((o) => integrated.has(o.key));
  const writers = intOps.filter((o) => issue.get(o.key)?.wrote.has(u) && writes(o, key) !== undefined);
  const g = gov.get(u)?.[key] ?? null;
  const base = { char: u, ch: charOp?.chars?.find((c) => k2(c.id) === u)?.ch, key, actual, wanted, governingMarker: g && { id: k2(g.id), value: g.value, createdBy: creator.get(k2(g.id))?.key } };

  // A marker the reference value relies on was deleted by an op unaware of
  // the dependency (concurrent with the writer or with the character's
  // insert), or by a cleanup. Writers are the ops that wrote the character
  // at issue time, then formats whose identity interval contains it, which
  // rely on the opener governing their left endpoint.
  const inInterval = intOps.filter(
    (o) => o.kind === 'format' && !writers.includes(o) && writes(o, key) !== undefined && pos.get(k2(o.range.left)) <= pos.get(u) && pos.get(u) <= pos.get(k2(o.range.right)),
  );
  const relied = [
    ...writers.map((p) => ({ p, m: issue.get(p.key).reliedOn[u]?.[key], via: 'wrote the character' })),
    ...inInterval.map((p) => ({ p, m: issue.get(p.key).reliedOn[k2(p.range.left)]?.[key], via: 'interval contains the character' })),
  ];
  for (const { p, m, via } of relied.filter(({ p }) => (writes(p, key) ?? null) === (wanted ?? null))) {
    if (!m) continue;
    const it = itemById.get(m);
    if (!it || !it.deleted) continue;
    const ds = (deleters.get(m) ?? []).filter((d) => integrated.has(d.key) && d !== p);
    const d = ds.find((x) => x.kind === 'cleanup' || (DELETER_CLASS[x.kind] && (concurrent(x, p) || (charOp && concurrent(x, charOp)))));
    if (!d) continue;
    return {
      ...base,
      class: DELETER_CLASS[d.kind],
      direction: wanted === null ? 'closer lost' : 'opener lost',
      writer: opSummary(p),
      writerRelation: via,
      reliedMarker: { id: m, value: it.value, createdBy: creator.get(m)?.key },
      deletedBy: opSummary(d),
    };
  }

  // The character shows a value from a live marker whose span should have ended.
  if (actual !== null && g) {
    const cg = creator.get(k2(g.id));
    const between = items.slice(pos.get(k2(g.id)) + 1, pos.get(u)).filter((it) => it.kind === 'format' && it.key === key && it.deleted && it.value !== actual);
    for (const c of between) {
      const ds = (deleters.get(k2(c.id)) ?? []).filter((d) => integrated.has(d.key));
      const d = ds.find((x) => x !== cg && (x.kind === 'cleanup' || (DELETER_CLASS[x.kind] && cg && concurrent(x, cg))));
      if (!d) continue;
      return {
        ...base,
        class: DELETER_CLASS[d.kind],
        direction: 'span extended',
        spanOwner: opSummary(cg),
        ownerCreatedCloser: (cg?.markers ?? []).some((m) => m.key === key && m.value !== actual),
        lostCloser: { id: k2(c.id), value: c.value, createdBy: creator.get(k2(c.id))?.key },
        deletedBy: opSummary(d),
      };
    }
    if (between.length === 0 && charOp) {
      // The closer that ends the span on the right of the character.
      const after = items.slice(pos.get(u) + 1).find((it) => it.kind === 'format' && it.key === key && !it.deleted && it.value !== actual);
      const cc = after ? creator.get(k2(after.id)) : null;
      const outside = (o) => o && !issue.get(o.key)?.wrote.has(u);
      if (outside(cg) && concurrent(charOp, cg))
        return { ...base, class: 'Y-004', direction: 'spread into concurrent insert', boundary: 'after the opener', spanOwner: opSummary(cg), insertedBy: opSummary(charOp) };
      if (cc && outside(cc) && concurrent(charOp, cc))
        return { ...base, class: 'Y-004', direction: 'spread into concurrent insert', boundary: 'before the closer', spanOwner: opSummary(cg), closer: { id: k2(after.id), value: after.value, createdBy: cc.key }, insertedBy: opSummary(charOp) };
    }
  }

  // A live marker of the same key, created by an op concurrent with the
  // writer of the reference value and not writing this character, restores
  // the value its creator saw inside the writer's span.
  if (g && (g.value ?? null) !== (wanted ?? null)) {
    const cg = creator.get(k2(g.id));
    for (const p of writers.filter((o) => (writes(o, key) ?? null) === (wanted ?? null))) {
      if (!cg || !concurrent(cg, p) || issue.get(cg.key)?.wrote.has(u)) continue;
      return { ...base, class: 'Y-005', direction: 'span cut', writer: opSummary(p), reliedMarker: issue.get(p.key).reliedOn[u]?.[key] ?? null, interloper: opSummary(cg) };
    }
  }

  // A format whose identity interval contains a concurrently inserted
  // character does not reach the markers that character's insert created.
  if (g && charOp && creator.get(k2(g.id)) === charOp) {
    const f = intOps.find((o) => o.kind === 'format' && (writes(o, key) ?? null) === (wanted ?? null) && concurrent(o, charOp) && pos.get(k2(o.range.left)) < pos.get(u) && pos.get(u) < pos.get(k2(o.range.right)));
    if (f) return { ...base, class: 'other', pattern: 'format interval misses a concurrent insert inside it', format: opSummary(f), insertedBy: opSummary(charOp) };
  }

  return { ...base, class: 'other', writers: writers.map(opSummary) };
}

/** Per-character, per-key differences between two equal-string views (with ids on `actual`). */
function differences(actualWithIds, reference) {
  const out = [];
  actualWithIds.forEach((c, i) => {
    const a = normaliseAttrs(c.attrs);
    const w = normaliseAttrs(reference[i].attrs);
    for (const key of new Set([...Object.keys(a), ...Object.keys(w)]))
      if ((a[key] ?? null) !== (w[key] ?? null)) out.push({ u: k2(c.id), key, actual: a[key] ?? null, wanted: w[key] ?? null });
  });
  return out;
}

const chars = (v) => v.map((e) => e.ch).join('');

/** The reference view nearest to `actual`: same characters, fewest attribute differences. */
function nearest(actual, candidates) {
  let best = null;
  for (const c of candidates) {
    if (chars(c) !== chars(actual)) continue;
    const n = differences(actual.map((e) => ({ ...e, id: [0, 0] })), c).length;
    if (!best || n < best.n) best = { view: c, n };
  }
  return best?.view ?? null;
}

/** Analyses replica r of a live execution against reference views. */
/** Whether a failure record carries every admitted view (records keep only the nearest few). */
const completeAdmitted = (expected) => (expected?.admittedViews?.length ?? 0) > 0 && !((expected.admittedViewCount ?? 0) > expected.admittedViews.length);

function analyse(ex, issue, r, references) {
  const rep = ex.replica(r);
  const items = rep.items();
  const visible = rep.visibleWithIds();
  const { gov, order } = governance(items);
  const { creator, deleters } = provenance(ex);
  const ref = nearest(visible, references);
  const walk = renderItems(items);
  if (!ref) {
    const markerIds = new Set(items.filter((it) => it.kind === 'format').map((it) => k2(it.id)));
    const markerAnchored = ex.ops
      .filter((o) => o.kind === 'insert' && ex.integrated[r].has(o.key))
      .flatMap((o) => o.chars.filter((c) => (c.yOrigin && markerIds.has(k2(c.yOrigin))) || (c.yRightOrigin && markerIds.has(k2(c.yRightOrigin)))).map((c) => ({ op: o.key, char: k2(c.id), ch: c.ch, yOrigin: c.yOrigin, yRightOrigin: c.yRightOrigin })));
    return { class: 'other', pattern: 'character order outside the admitted orders', markerAnchoredInserts: markerAnchored, items: walk };
  }
  const ctx = { ex, issue, items, gov, order, creator, deleters, integrated: ex.integrated[r] };
  const diffs = differences(visible, ref).map((d) => explain(ctx, d.u, d.key, d.actual, d.wanted));
  if (diffs.length === 0) return { class: null, classes: [], reference: ref, differences: [] };
  const classes = [...new Set(diffs.map((d) => d.class))];
  const primary = classes.find((c) => c !== 'other') ?? 'other';
  const out = { class: primary, classes, reference: ref, differences: diffs };
  if (classes.includes('other')) out.items = walk;
  return out;
}

/** Steps of the run including the final-sync round. */
const allSteps = (schedule) => [...schedule.steps, ...finalSyncSteps(schedule.replicas)];

/**
 * Classifies the state of replica `r` after `schedule` (no final sync)
 * against the specification's admitted views. `class` is null when the
 * displayed view is itself a reference view.
 */
export function classifyAt(schedule, r, { finalSync = false, references } = {}) {
  const stopAt = finalSync ? Infinity : schedule.steps.length - 1;
  const { ex, issue } = reexecute(schedule, { stopAt });
  const refs = references ?? allFinalViews(eventsAt(ex, r).events, { target: ex.replica(r).visibleWithIds(), limit: DEFAULT_WITNESS_STATE_LIMIT });
  return analyse(ex, issue, r, refs);
}

/**
 * Re-executes `schedule` with its final-sync round, recording per edit op
 * the characters it wrote and their governing markers at the issuing
 * replica just after it (`issue`). Stops after step `stopAt`; calls
 * `onStep(ex, index, step, issue)` after every step.
 */
export function reexecute(schedule, opts = {}) {
  const ex = new Execution(schedule.replicas, { checks: [] });
  const steps = allSteps(schedule);
  const issue = new Map();
  const stopAt = opts.stopAt ?? Infinity;
  for (let i = 0; i < steps.length && i <= stopAt; i++) {
    const step = steps[i];
    const rec = ex.apply(step);
    if (step.type === 'edit') {
      const rep = ex.replica(step.replica);
      const { gov } = governance(rep.items());
      const wrote = rec.kind === 'insert' ? rec.chars.map((c) => k2(c.id)) : rec.kind === 'format' ? rec.range.covered.map(k2) : [];
      const reliedOn = {};
      for (const u of wrote) reliedOn[u] = Object.fromEntries(Object.entries(gov.get(u) ?? {}).map(([key, it]) => [key, k2(it.id)]));
      issue.set(rec.key, { wrote: new Set(wrote), reliedOn });
    }
    if (opts.onStep) opts.onStep(ex, i, step, issue);
  }
  return { ex, issue, steps };
}

/**
 * Conservation diagnosis after the final-sync round. For every replica and
 * every op not integrated there: whether the op was received, whether it is
 * a cleanup, whether every unit its update deletes is deleted at the
 * replica anyway, and which integrated ops delete those units. Also compares
 * displayed character multisets with inserted minus deleted.
 */
export function diagnoseConservation(schedule) {
  const { ex } = reexecute(schedule);
  const inserted = new Map();
  const deleted = new Set();
  for (const o of ex.ops) {
    if (o.kind === 'insert') for (const c of o.chars) inserted.set(k2(c.id), c.ch);
    if (o.kind === 'delete') for (const id of o.deleted) deleted.add(k2(id));
  }
  const expected = [...inserted.entries()].filter(([k]) => !deleted.has(k)).map(([k, ch]) => k + '=' + ch).sort();
  const out = [];
  for (let r = 1; r <= schedule.replicas; r++) {
    const rep = ex.replica(r);
    const actual = rep.visibleWithIds().map((c) => k2(c.id) + '=' + c.ch).sort();
    const dead = new Set(rep.items().filter((it) => it.deleted).flatMap(unitKeys));
    const missing = ex.ops.filter((o) => !ex.integrated[r].has(o.key));
    if (!missing.length && JSON.stringify(actual) === JSON.stringify(expected) && !rep.hasPending()) continue;
    out.push({
      replica: r,
      charactersConserved: JSON.stringify(actual) === JSON.stringify(expected),
      pending: rep.hasPending(),
      notIntegrated: missing.map((o) => {
        const units = o.effect.deletes.flatMap((d) => Array.from({ length: d.len }, (_, k) => d.client + ':' + (d.clock + k)));
        const alsoDeletedBy = ex.ops.filter((p) => p !== o && ex.integrated[r].has(p.key) && p.effect.deletes.some((d) => units.some((u) => u.split(':')[0] == d.client && +u.split(':')[1] >= d.clock && +u.split(':')[1] < d.clock + d.len)));
        return {
          key: o.key,
          kind: o.kind,
          received: ex.received[r].has(o.key),
          createsStructs: o.effect.structs.length > 0,
          deletes: units,
          allDeletesApplied: units.every((u) => dead.has(u)),
          sameDeletesByIntegratedOps: alsoDeletedBy.map((p) => p.key),
          issuedAtStep: o.step,
          lastDeliveryFromIssuerAfterIssue: ex.steps.some((s, i) => i > o.step && (s.type === 'deliver' || s.type === 'send') && s.from === o.replica && s.to === r),
        };
      }),
    });
  }
  return out;
}

/**
 * Classifies every failing trial of a search output. Per trial: `classes`
 * (every class among its failure records) and `onset` (the class of its
 * earliest view failure; later failures at a replica may inherit an earlier
 * anomaly's state).
 */
export function classifySearch(data) {
  return data.failing.map((t) => {
    const records = classifyTrace(t.schedule, t.checks);
    const views = records.filter((x) => x.check !== 'determinism' && x.check !== 'conservation' && !x.final);
    const first = views.reduce((m, x) => (m === null || x.step < m.step ? x : m), null);
    return { trial: t.trial, seed: t.seed, onset: first?.class ?? null, classes: [...new Set(records.map((x) => x.class))].sort(), records };
  });
}

/**
 * Classifies every kept failure of a trial: view failures (RA-linearizability,
 * local meaning, non-final convergence) by `analyse` at their step,
 * determinism failures as `Y-006`, the opened-document family, and
 * conservation and final convergence failures through `diagnoseConservation`.
 */
export function classifyTrace(schedule, checks) {
  const fs = CHECKS.flatMap((c) => checks[c]?.details.failures ?? []);
  const out = [];
  const byStep = new Map();
  for (const f of fs) {
    if (f.check === 'determinism') out.push({ check: f.check, replica: f.replica, step: f.step, class: 'Y-006', signature: f.signature });
    else if (f.check === 'conservation' || (f.check === 'convergence' && f.final)) continue;
    else {
      if (!byStep.has(f.step)) byStep.set(f.step, []);
      byStep.get(f.step).push(f);
    }
  }
  const finalConvergence = fs.filter((f) => f.check === 'convergence' && f.final);
  if (fs.some((f) => f.check === 'conservation') || finalConvergence.length) {
    const diag = diagnoseConservation(schedule);
    const tracking = diag.every((d) => d.charactersConserved && !d.pending && d.notIntegrated.every((o) => o.kind === 'cleanup' && !o.received));
    if (fs.some((f) => f.check === 'conservation'))
      for (const d of diag) out.push({ check: 'conservation', class: tracking ? 'final-sync' : 'other', ...d });
    for (const f of finalConvergence)
      out.push({ check: 'convergence', replica: f.replica, step: f.step, final: true, class: tracking ? 'final-sync' : 'other', expected: f.expected, actual: f.actual, diagnosis: diag });
  }
  if (byStep.size === 0) return out;
  const last = Math.max(...byStep.keys());
  reexecute(schedule, {
    stopAt: last,
    onStep(ex, i, _step, issue) {
      for (const f of byStep.get(i) ?? []) {
        let res;
        if (f.check === 'raLinearizability') res = analyse(ex, issue, f.replica, completeAdmitted(f.expected) ? f.expected.admittedViews : allFinalViews(eventsAt(ex, f.replica).events, { target: ex.replica(f.replica).visibleWithIds(), limit: DEFAULT_WITNESS_STATE_LIMIT }));
        else if (f.check === 'localMeaning') res = analyse(ex, issue, f.replica, [f.expected]);
        else res = { class: 'other', reason: 'check ' + f.check, expected: f.expected, actual: f.actual, items: renderItems(ex.replica(Array.isArray(f.replica) ? f.replica[0] : f.replica).items()) };
        out.push({ check: f.check, replica: f.replica, step: i, signature: f.signature, ...res });
      }
    },
  });
  return out;
}

if (process.argv[1] && fileURLToPath(import.meta.url) === process.argv[1]) {
  const [input, output] = process.argv.slice(2);
  if (!input) throw new Error('usage: node classify.js <search-output.json> [classified.json]');
  const data = JSON.parse(readFileSync(input, 'utf8'));
  const res = classifySearch(data);
  const hist = {};
  for (const t of res) for (const c of t.classes) hist[c] = (hist[c] ?? 0) + 1;
  console.log('trials by class:', JSON.stringify(hist));
  if (output) writeFileSync(output, JSON.stringify(res, null, 1) + '\n');
}
