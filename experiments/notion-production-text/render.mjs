/** Compact renderings of check failures for reports. */
import { renderView } from '../../ra-pbt/instances/notion-production-text/spec.js';

const isView = (x) => Array.isArray(x) && x.every((e) => e && typeof e === 'object' && 'ch' in e);

function renderValue(x) {
  if (isView(x)) return renderView(x);
  if (x && typeof x === 'object' && !Array.isArray(x))
    return Object.fromEntries(Object.entries(x).map(([k, v]) => [k, k === 'admittedViews' ? v.map(renderView) : renderValue(v)]));
  return x;
}

/** Compact rendering of a check failure. */
export function renderFailure(f) {
  const out = {};
  for (const k of ['replica', 'step', 'request', 'before', 'expected', 'actual', 'actorOutcome', 'opKeys']) if (f[k] !== undefined) out[k] = renderValue(f[k]);
  return out;
}

