// Shared loader and oracle for the issue 829 convergence experiments.
// load('14') is @y/y 14.0.0-rc.29, load('13') is yjs 13.6.31, both pinned under ../repro.
import { readFileSync } from 'node:fs';

export async function load(version) {
  const root = new URL(version === '14' ? '../repro/v14/node_modules/@y/y/' : '../repro/node_modules/yjs/', import.meta.url);
  const pkg = JSON.parse(readFileSync(new URL('package.json', root)));
  const Y = await import(new URL(version === '14' ? 'src/index.js' : 'dist/yjs.mjs', root));
  const text = (d) => (version === '14' ? d.get('t') : d.getText('t'));
  const stable = (o) => (Array.isArray(o) ? o.map(stable) : o && typeof o === 'object' ? Object.fromEntries(Object.keys(o).sort().map((k) => [k, stable(o[k])])) : o);
  /** Observable value: the text and its formatting runs, attribute keys sorted. */
  const view = (d) => {
    const delta = text(d).toDelta();
    const runs = version === '14' ? delta.children.map((c) => ({ insert: c.insert, attributes: c.format ?? {} })) : delta.map((c) => ({ insert: c.insert, attributes: c.attributes ?? {} }));
    return { text: text(d).toString(), delta: stable(runs) };
  };
  const key = (d) => JSON.stringify(view(d));
  const equal = (docs) => docs.every((d) => key(d) === key(docs[0]));
  const pending = (d) => ({ structs: d.store.pendingStructs != null, ds: d.store.pendingDs != null });
  const sv = (d) => JSON.stringify([...Y.decodeStateVector(Y.encodeStateVector(d)).entries()].sort((x, y) => x[0] - y[0]));
  /** The state re-encoded and loaded into a fresh document: catches a store that displays right but encodes wrong. */
  const reloaded = (d, gc = d.gc) => { const f = new Y.Doc({ gc }); Y.applyUpdate(f, Y.encodeStateAsUpdate(d)); return f; };
  const reloadedV2 = (d, gc = d.gc) => { const f = new Y.Doc({ gc }); Y.applyUpdateV2(f, Y.encodeStateAsUpdateV2(d)); return f; };
  /** State-vector exchange in both directions, as y-protocols sync does. */
  const sync = (from, to) => Y.applyUpdate(to, Y.encodeStateAsUpdate(from, Y.encodeStateVector(to)));
  const syncV2 = (from, to) => Y.applyUpdateV2(to, Y.encodeStateAsUpdateV2(from, Y.encodeStateVectorV2 ? Y.encodeStateVectorV2(to) : Y.encodeStateVector(to)));
  /** A document that records every update it emits. */
  const doc = (clientID, { gc = false } = {}) => { const d = new Y.Doc({ gc }); d.clientID = clientID; const updates = []; d.on('update', (u) => updates.push(u)); text(d); return { d, updates }; };
  /** The oracle verdict on a set of documents that received the same complete update set. */
  const verdict = (docs) => {
    const fresh = docs.map((d) => reloaded(d, false));
    const out = { divergence: !equal(docs), pending: docs.map(pending), svs: new Set(docs.map(sv)).size, reloadDivergence: !equal(fresh) || fresh.some((f, i) => key(f) !== key(docs[i])) };
    for (const f of fresh) f.destroy();
    out.unresolved = out.pending.some((p) => p.structs || p.ds);
    return out;
  };
  return { Y, pkg, version, text, view, key, equal, pending, sv, reloaded, reloadedV2, sync, syncV2, doc, verdict };
}

export function rng(seed) { let s = seed >>> 0 || 1; return () => { s ^= s << 13; s ^= s >>> 17; s ^= s << 5; return (s >>> 0) / 4294967296; }; }
export function shuffle(a, r) { a = a.slice(); for (let i = a.length - 1; i > 0; i--) { const j = Math.floor(r() * (i + 1)); [a[i], a[j]] = [a[j], a[i]]; } return a; }
export function* permutations(items) { if (items.length <= 1) { yield items.slice(); return; } for (let i = 0; i < items.length; i++) { const rest = items.slice(0, i).concat(items.slice(i + 1)); for (const p of permutations(rest)) yield [items[i], ...p]; } }
