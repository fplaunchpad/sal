// Deterministic binary codec for sync messages. This is deliberately small and
// browser-safe: it depends only on Uint8Array/TextEncoder/TextDecoder. Repeated
// strings (operation names, replica ids, object keys) are interned once, while
// SHA-256 content ids are stored as 32 raw bytes instead of 64 hex characters.

const enc = new TextEncoder();
const dec = new TextDecoder('utf-8', { fatal: true });
const MAGIC = [0x53, 0x41, 0x4c, 0x01]; // "SAL", binary-wire version 1
const HASH_HEX = /^(?:[0-9a-f]{40}|[0-9a-f]{64})$/;
const LOCAL_COMMIT = /^c([0-9]+)$/;

class Writer {
  constructor() { this.a = []; }
  byte(x) { this.a.push(x & 255); }
  bytes(xs) { for (const x of xs) this.a.push(x); }
  uint(n) {
    if (!Number.isSafeInteger(n) || n < 0) throw new TypeError(`wire uint: ${n}`);
    do { const b = n % 128; n = Math.floor(n / 128); this.byte(b | (n ? 128 : 0)); } while (n);
  }
  text(s) { const b = enc.encode(s); this.uint(b.length); this.bytes(b); }
  finish() { return Uint8Array.from(this.a); }
}

class Reader {
  constructor(bytes) { this.b = bytes; this.i = 0; }
  byte() { if (this.i >= this.b.length) throw new Error('wire: truncated input'); return this.b[this.i++]; }
  bytes(n) { if (this.i + n > this.b.length) throw new Error('wire: truncated input'); const x = this.b.subarray(this.i, this.i + n); this.i += n; return x; }
  uint() {
    let n = 0, scale = 1;
    for (let k = 0; k < 8; k++) { const b = this.byte(); n += (b & 127) * scale; if (!(b & 128)) { if (!Number.isSafeInteger(n)) throw new Error('wire: integer overflow'); return n; } scale *= 128; }
    throw new Error('wire: invalid varint');
  }
  text() { return dec.decode(this.bytes(this.uint())); }
}

function stringsIn(v, counts) {
  if (typeof v === 'string') counts.set(v, (counts.get(v) ?? 0) + 1);
  else if (Array.isArray(v)) for (const x of v) stringsIn(x, counts);
  else if (v && typeof v === 'object') for (const k of Object.keys(v)) {
    counts.set(k, (counts.get(k) ?? 0) + 1); stringsIn(v[k], counts);
  }
}

function dictionary(v) {
  const counts = new Map(); stringsIn(v, counts);
  return [...counts].filter(([s, n]) => n > 1 && !HASH_HEX.test(s) && !LOCAL_COMMIT.test(s))
    .sort((a, b) => b[1] - a[1] || a[0].localeCompare(b[0])).map(([s]) => s);
}

function putValue(w, v, dict) {
  if (v === null) return w.byte(0);
  if (v === false) return w.byte(1);
  if (v === true) return w.byte(2);
  if (typeof v === 'number') {
    if (Number.isSafeInteger(v)) { w.byte(3); w.uint(v >= 0 ? 2 * v : -2 * v - 1); return; }
    w.byte(4); const b = new Uint8Array(8); new DataView(b.buffer).setFloat64(0, v, true); w.bytes(b); return;
  }
  if (typeof v === 'string') {
    const di = dict.get(v);
    if (di !== undefined) { w.byte(5); w.uint(di); return; }
    if (HASH_HEX.test(v)) { w.byte(6); w.byte(v.length / 2); for (let i = 0; i < v.length; i += 2) w.byte(parseInt(v.slice(i, i + 2), 16)); return; }
    const local = LOCAL_COMMIT.exec(v);
    if (local) { w.byte(10); w.uint(Number(local[1])); return; }
    w.byte(7); w.text(v); return;
  }
  if (Array.isArray(v)) { w.byte(8); w.uint(v.length); for (const x of v) putValue(w, x, dict); return; }
  if (v && typeof v === 'object' && Object.getPrototypeOf(v) === Object.prototype) {
    const keys = Object.keys(v).sort(); w.byte(9); w.uint(keys.length);
    for (const k of keys) { putValue(w, k, dict); putValue(w, v[k], dict); }
    return;
  }
  throw new TypeError(`wire: unsupported value ${String(v)}`);
}

function getValue(r, dict) {
  switch (r.byte()) {
    case 0: return null;
    case 1: return false;
    case 2: return true;
    case 3: { const n = r.uint(); return n % 2 === 0 ? n / 2 : -(n + 1) / 2; }
    case 4: { const b = r.bytes(8); return new DataView(b.buffer, b.byteOffset, 8).getFloat64(0, true); }
    case 5: { const i = r.uint(); if (i >= dict.length) throw new Error('wire: bad dictionary reference'); return dict[i]; }
    case 6: return [...r.bytes(r.byte())].map((x) => x.toString(16).padStart(2, '0')).join('');
    case 7: return r.text();
    case 8: { const n = r.uint(), a = []; for (let i = 0; i < n; i++) a.push(getValue(r, dict)); return a; }
    case 9: { const n = r.uint(), o = {}; for (let i = 0; i < n; i++) { const k = getValue(r, dict); if (typeof k !== 'string') throw new Error('wire: non-string object key'); o[k] = getValue(r, dict); } return o; }
    case 10: return `c${r.uint()}`;
    default: throw new Error('wire: unknown value tag');
  }
}

const isDelta = (v) => v && v.t === 'delta' && Array.isArray(v.c);

function putPayload(w, p, dict) {
  if (p && !Array.isArray(p) && p.type === 'ins' &&
      Object.keys(p).every((k) => ['type', 'id', 'el', 'anchorId'].includes(k))) {
    w.byte(1); putValue(w, p.id, dict); putValue(w, p.el, dict); putValue(w, p.anchorId, dict); return;
  }
  if (p && !Array.isArray(p) && p.type === 'del' &&
      Object.keys(p).every((k) => ['type', 'id'].includes(k))) {
    w.byte(2); putValue(w, p.id, dict); return;
  }
  w.byte(0); putValue(w, p, dict);
}

function getPayload(r, dict) {
  const tag = r.byte();
  if (tag === 1) return { type: 'ins', id: getValue(r, dict), el: getValue(r, dict), anchorId: getValue(r, dict) };
  if (tag === 2) return { type: 'del', id: getValue(r, dict) };
  if (tag === 0) return getValue(r, dict);
  throw new Error('wire: unknown payload tag');
}

function putDelta(w, commits, dict) {
  w.uint(commits.length);
  let previous = null;
  for (let ci = 0; ci < commits.length; ci++) {
    const c = commits[ci], next = commits[ci + 1];
    // A linear child's authenticated gid commits recursively to this gid, so
    // intermediate ids need not travel. The run endpoint remains explicit and
    // authenticates the entire reconstructed chain.
    const authored = c.kind === 'op' || (c.kind === undefined && c.op !== null);
    const omitGid = authored && next?.parents?.length === 1 && next.parents[0] === c.gid;
    w.byte(omitGid ? 0 : 1); if (!omitGid) putValue(w, c.gid, dict);
    w.uint(c.parents.length);
    for (const p of c.parents) {
      if (p === previous) w.byte(0);
      else { w.byte(1); putValue(w, p, dict); }
    }
    if (c.kind === 'compact') {
      w.byte(4); putValue(w, c.cut, dict); putValue(w, c.state, dict);
    } else if (c.kind === 'base') {
      w.byte(5); putValue(w, c.epoch, dict); putValue(w, c.fp, dict);
      putValue(w, c.roster, dict); putValue(w, c.proof, dict); putValue(w, c.state, dict);
    } else if (c.kind === 'merge') w.byte(3);
    else if (c.kind === 'op') {
      w.byte(2); putValue(w, c.op.replica, dict); w.uint(c.op.seq); putPayload(w, c.payload, dict);
    } else if (c.op === null) w.byte(0);
    else {
      w.byte(1); putValue(w, c.op.replica, dict); w.uint(c.op.seq); putPayload(w, c.payload, dict);
    }
    previous = c.gid;
  }
}

function getDelta(r, dict) {
  const n = r.uint(), commits = [];
  let previous = null;
  for (let i = 0; i < n; i++) {
    const gid = r.byte() === 0 ? null : getValue(r, dict), pn = r.uint(), parents = [];
    // null is an authenticated-run back-reference: ingest substitutes the gid
    // it recomputed for the preceding commit.
    for (let j = 0; j < pn; j++) parents.push(r.byte() === 0 ? previous : getValue(r, dict));
    const shape = r.byte();
    let c;
    if (shape === 0) c = { gid, parents, op: null, payload: null };
    else if (shape === 1) c = { gid, parents, op: { replica: getValue(r, dict), seq: r.uint() }, payload: getPayload(r, dict) };
    else if (shape === 2) c = { gid, kind: 'op', parents, op: { replica: getValue(r, dict), seq: r.uint() }, payload: getPayload(r, dict) };
    else if (shape === 3) c = { gid, kind: 'merge', parents };
    else if (shape === 4) c = { gid, kind: 'compact', parents, cut: getValue(r, dict), state: getValue(r, dict) };
    else if (shape === 5) c = { gid, kind: 'base', parents,
      epoch: getValue(r, dict), fp: getValue(r, dict), roster: getValue(r, dict),
      proof: getValue(r, dict), state: getValue(r, dict) };
    else throw new Error('wire: unknown delta commit tag');
    commits.push(c); previous = gid;
  }
  return { t: 'delta', c: commits };
}

export function encodeWire(value) {
  const entries = dictionary(value), ids = new Map(entries.map((s, i) => [s, i]));
  const w = new Writer(); w.bytes(MAGIC); w.byte(isDelta(value) ? 1 : 0);
  w.uint(entries.length); for (const s of entries) w.text(s);
  if (isDelta(value)) putDelta(w, value.c, ids); else putValue(w, value, ids);
  return w.finish();
}

export function decodeWire(bytes) {
  const r = new Reader(bytes instanceof Uint8Array ? bytes : new Uint8Array(bytes));
  for (const x of MAGIC) if (r.byte() !== x) throw new Error('wire: bad magic or version');
  const mode = r.byte(); if (mode !== 0 && mode !== 1) throw new Error('wire: unknown message mode');
  const n = r.uint(), dict = []; for (let i = 0; i < n; i++) dict.push(r.text());
  const value = mode === 1 ? getDelta(r, dict) : getValue(r, dict);
  if (r.i !== r.b.length) throw new Error('wire: trailing bytes'); return value;
}

export const binaryWireBytes = (value) => encodeWire(value).length;
