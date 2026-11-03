/**
 * Seeded generation of concrete schedules (see schedule.js).
 *
 * The generator executes the replicas as it chooses steps, so every request
 * is chosen against the acting replica's displayed value at that point, and
 * the recorded schedule replays deterministically.
 *
 * Shape: rounds in which each active replica issues one to three requests,
 * then any replicas waiting to be opened join by an `open` step from an
 * active replica, then one to `deliveryRate` transfers between random
 * ordered pairs of active replicas. With `partialDelivery`, transfers are
 * `send` steps of individual records (each record sent at most once per
 * ordered pair, so some are held back until the final sync); otherwise they
 * are `deliver` steps. With `openedReplicas`, each replica other than
 * replica 1 waits to be opened with probability one half, and the last one
 * does when no other has.
 *
 * The instance provides
 *   nextRequest(rnd, view, options) -> request | null
 *       a request for a replica whose displayed value is `view`, or null to
 *       issue nothing this time; `rnd` is a `random` source;
 *   generateOptions?(options) -> options
 *       instance defaults for the options, applied first.
 * A step whose request the implementation rejects with a RangeError is
 * dropped.
 */
import { Execution, prepareInstance } from './schedule.js';

/** mulberry32: a 32-bit seeded PRNG returning floats in [0, 1). */
export function mulberry32(seed) {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

/** A seeded random source: `next()` in [0, 1), `int(lo, hi)` inclusive, `pick(xs)`. */
export function random(seed) {
  const next = mulberry32(seed);
  return {
    next,
    int: (lo, hi) => lo + Math.floor(next() * (hi - lo + 1)),
    pick: (xs) => xs[Math.floor(next() * xs.length)],
  };
}

/**
 * generate(instance, seed, { replicas = 2 or 3 chosen by seed, steps = 12,
 *          partialDelivery = false, openedReplicas = false,
 *          deliveryRate = 4 with partialDelivery, else 2, ...instance options })
 * returns { seed, options, replicas, steps }. `steps` bounds the number of
 * edits, opens and transfers (the final sync is not counted).
 */
export function generate(instance, seed, options = {}) {
  const inst = prepareInstance(instance);
  if (typeof inst.nextRequest !== 'function') throw new TypeError('the instance provides no nextRequest');
  const rnd = random(seed);
  const { int, pick } = rnd;
  const opts = inst.generateOptions ? inst.generateOptions({ ...options }) : { ...options };
  if (opts.steps === undefined) opts.steps = 12;
  if (opts.partialDelivery === undefined) opts.partialDelivery = false;
  const openedReplicas = !!opts.openedReplicas;
  const deliveryRate = opts.deliveryRate ?? (opts.partialDelivery ? 4 : 2);
  const n = opts.replicas ?? int(2, 3);
  const active = new Set([1]);
  const toOpen = [];
  for (let r = 2; r <= n; r++) {
    if (openedReplicas && (rnd.next() < 0.5 || (r === n && toOpen.length === 0))) toOpen.push(r);
    else active.add(r);
  }
  const ex = new Execution(inst, n, { checks: [] });
  const steps = [];
  const sent = new Set();

  const tryStep = (step) => {
    try {
      ex.apply(step);
      steps.push(step);
      return true;
    } catch (e) {
      if (e instanceof RangeError) return false;
      throw e;
    }
  };

  const edit = (r) => {
    const request = inst.nextRequest(rnd, inst.adapter.displayed(ex.replica(r)), opts);
    if (!request) return false;
    return tryStep({ type: 'edit', replica: r, ...request });
  };

  const transfer = () => {
    const live = [...active];
    if (live.length < 2) return false;
    const from = pick(live);
    const to = pick(live.filter((x) => x !== from));
    if (!opts.partialDelivery) return tryStep({ type: 'deliver', from, to });
    const candidates = ex.ownOps[from].map((o, i) => i).filter((i) => !sent.has(`${from}>${to}#${i}`));
    if (candidates.length === 0) return false;
    const op = pick(candidates);
    sent.add(`${from}>${to}#${op}`);
    return tryStep({ type: 'send', from, to, op });
  };

  let guard = 0;
  while (steps.length < opts.steps && guard++ < opts.steps * 20) {
    for (let r = 1; r <= n && steps.length < opts.steps; r++) {
      if (!active.has(r)) continue;
      const k = int(1, 3);
      for (let i = 0; i < k && steps.length < opts.steps; i++) edit(r);
    }
    while (toOpen.length && steps.length < opts.steps) {
      const r = toOpen.shift();
      if (tryStep({ type: 'open', replica: r, from: pick([...active]) })) active.add(r);
    }
    const d = int(1, deliveryRate);
    for (let i = 0; i < d && steps.length < opts.steps; i++) transfer();
  }
  return { seed, options: opts, replicas: n, steps };
}
