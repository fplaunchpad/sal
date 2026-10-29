/** Compact renderings of views and check failures for reports. */

/** Compact rendering of a view: characters, with attributes in brackets. */
export function renderView(v) {
  return v
    .map((e) => {
      const ks = Object.keys(e.attrs ?? {}).filter((k) => e.attrs[k] !== null && e.attrs[k] !== undefined);
      return ks.length ? `${e.ch}(${ks.sort().join(',')})` : e.ch;
    })
    .join(' ');
}

const isView = (x) => Array.isArray(x) && x.every((e) => e && typeof e === 'object' && 'ch' in e);

/** Views inside a failure value rendered compactly; other values unchanged. */
function renderValue(x) {
  if (isView(x)) return renderView(x);
  if (x && typeof x === 'object' && !Array.isArray(x))
    return Object.fromEntries(Object.entries(x).map(([k, v]) => [k, Array.isArray(v) && v.every(isView) ? v.map(renderView) : renderValue(v)]));
  return x;
}

/** Compact rendering of a check failure. */
export function renderFailure(f) {
  const out = {};
  for (const k of ['replica', 'step', 'request', 'before', 'expected', 'actual', 'actorOutcome', 'actorOpened', 'opKeys'])
    if (f[k] !== undefined) out[k] = renderValue(f[k]);
  return out;
}
