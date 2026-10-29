/**
 * Exact RA-linearizability witness search.
 *
 * An event is { key, deps: [key], specOps: [op] }. A witness for a target
 * view is a linear extension of the (transitively closed) causal order whose
 * fold of the events' specification operations from the initial state never
 * fails a precondition and ends in a state whose view equals the target
 * under the specification's `viewKey`.
 *
 * The search is dynamic programming over down-closed subsets of events
 * (bitmasks, at most 20 events). Each subset maps the serialised states it can
 * reach to one order reaching each; subsets are processed by cardinality so
 * only two layers are live at a time. Relational specifications are explored
 * through `applyAll`, or through `applyDirected` when the specification
 * `directs` the target.
 */
import { normaliseSpec } from './spec.js';

export const MAX_EVENTS = 20;

/** Transitively closed dependency masks; throws on unknown keys, duplicates and cycles. */
export function closedDepMasks(events) {
  if (events.length > MAX_EVENTS) throw new RangeError(`at most ${MAX_EVENTS} events are supported`);
  const index = new Map();
  events.forEach((e, i) => {
    if (index.has(e.key)) throw new Error('duplicate event key: ' + e.key);
    index.set(e.key, i);
  });
  const direct = events.map((e) =>
    (e.deps ?? []).reduce((m, d) => {
      if (!index.has(d)) throw new Error(`unknown dependency ${d} of ${e.key}`);
      return m | (1 << index.get(d));
    }, 0),
  );
  const closed = direct.slice();
  let changed = true;
  while (changed) {
    changed = false;
    for (let i = 0; i < events.length; i++) {
      let m = closed[i];
      for (let j = 0; j < events.length; j++) if (m & (1 << j)) m |= closed[j];
      if (m !== closed[i]) {
        closed[i] = m;
        changed = true;
      }
    }
  }
  closed.forEach((m, i) => {
    if (m & (1 << i)) throw new Error('causal cycle through ' + events[i].key);
  });
  return closed;
}

/** Every state the event's operations can lead to from `state`, in order. */
function foldEvent(spec, state, event, target) {
  let states = [state];
  for (const op of event.specOps) {
    const next = [];
    for (const s of states) next.push(...(target ? spec.applyDirected(s, op, target) : spec.applyAll(s, op)));
    if (next.length === 0) return [];
    states = next;
  }
  return states;
}

function orderOf(node, events) {
  const out = [];
  for (let n = node; n.prev !== null; n = n.prev) out.push(events[n.event].key);
  return out.reverse();
}

/**
 * Explores every linear extension, calling `onFinal(node)` for each distinct
 * final state; `onFinal` returning true stops the search. With `target`, the
 * search is directed by it. Throws a RangeError when more than `limit`
 * (subset, state) pairs are explored. Returns the number explored.
 */
function explore(spec, events, onFinal, target = null, limit = Infinity) {
  const deps = closedDepMasks(events);
  const n = events.length;
  const full = n === 0 ? 0 : (1 << n) - 1;
  const root = { state: spec.init(), prev: null, event: -1 };
  let layer = new Map([[0, new Map([[spec.serialise(root.state), root]])]]);
  let explored = 1;
  for (let size = 0; size < n; size++) {
    const next = new Map();
    for (const [mask, states] of layer) {
      for (let i = 0; i < n; i++) {
        const bit = 1 << i;
        if (mask & bit || (deps[i] & mask) !== deps[i]) continue;
        const nmask = mask | bit;
        let bucket = next.get(nmask);
        if (!bucket) next.set(nmask, (bucket = new Map()));
        for (const node of states.values()) {
          for (const s of foldEvent(spec, node.state, events[i], target)) {
            const k = spec.serialise(s);
            if (!bucket.has(k)) {
              bucket.set(k, { state: s, prev: node, event: i });
              explored++;
              if (explored > limit) throw new RangeError('state limit exceeded');
            }
          }
        }
      }
    }
    layer = next;
  }
  const finals = layer.get(full);
  if (finals) for (const node of finals.values()) if (onFinal(node)) break;
  return explored;
}

/**
 * Searches for a linear extension folding to `target`.
 * Returns { found: true, order: [key] } or
 * { found: false, explored, reachableViews } where `reachableViews` counts the
 * distinct final views of the (possibly directed) search.
 */
export function findWitness(spec, events, target) {
  const s = normaliseSpec(spec);
  const want = s.viewKey(target);
  const directed = s.directs(target) ? target : null;
  let hit = null;
  const views = new Set();
  const explored = explore(
    s,
    events,
    (node) => {
      const k = s.viewKey(s.view(node.state));
      views.add(k);
      if (k === want) {
        hit = node;
        return true;
      }
      return false;
    },
    directed,
  );
  if (hit) return { found: true, order: orderOf(hit, events) };
  return { found: false, explored, reachableViews: views.size };
}

/**
 * The distinct final views over all linear extensions, sorted by canonical
 * key. With a `target` the specification directs, only target-consistent
 * states are enumerated (the admitted views a failing version is compared
 * against). Otherwise the enumeration of a relational specification is
 * capped at `limit` (subset, state) pairs (a deterministic one has at most
 * one state per subset); when the cap is hit the result carries `truncated: true` and lists
 * the views found so far.
 */
export function allFinalViews(spec, events, { limit = 200000, target = null } = {}) {
  const s = normaliseSpec(spec);
  const views = new Map();
  let truncated = false;
  const directed = target !== null && s.directs(target) ? target : null;
  try {
    explore(
      s,
      events,
      (node) => {
        const v = s.view(node.state);
        views.set(s.viewKey(v), v);
        return false;
      },
      directed,
      directed || !s.relational ? Infinity : limit,
    );
  } catch (e) {
    if (!(e instanceof RangeError) || !/state limit/.test(e.message)) throw e;
    truncated = true;
  }
  const out = [...views.keys()].sort().map((k) => views.get(k));
  if (truncated) out.truncated = true;
  return out;
}
