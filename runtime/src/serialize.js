// Run-table serializer for the embed RGA (task #104, SERIALIZER item).
//
// Turns the run-table PROJECTION of whiteboard/litmus/run_table_measure.py
// (task #73) into a SHIPPED encoder/decoder. The state is the embed RGA's
//   Map id -> { coord, el }
// with absolute chain coordinates under the flipped Elias-delta code
// (src/datatypes/embedRGA.js; src/compact.js's decodeOne is reused). This
// serializer composes AFTER compaction (compact.js), where cuts are settled
// and the coordinate tree is at its smallest, but it is a pure function of
// the state and needs NO stability gate -- it applies to any state.
//
// THE REPRESENTATION (one-sided; the shipped runtime carries no side bit).
// Build the KEPT TREE: decode every live record's coordinate into its chain
// of deltas, sharing prefixes; internal nodes with no record are the dead
// ancestors that survive tombstone-free deletion (their level persists in
// every live descendant's coordinate). An edge p->c is FUSIBLE when c is p's
// unique kept child, delta(c)=1, and live(c)=live(p) (side is vacuously R).
// A RUN (table entry) is a maximal fusible chain; a record's address is
// (run-id, offset). By the tail-attachment lemma every entry attaches at its
// parent entry's LAST member, so the parent-offset is derivable and NOT
// stored, and records sit positionally in their run (run-id and offset are
// positional, also NOT stored) -- the section-9.1 positional saving over the
// model, which charges those recoverable fields. accountingBits() reproduces
// the model's charged total exactly for cross-check against the projection.
//
// LOSSLESS: from the entry headers alone (liveness, parent ref, head delta,
// length) every kept node's delta (head delta at offset 0, else 1) and hence
// every coordinate is recovered, so decode(encode(s)) reads identically to s.
// Ids are the (ts,agent) tie-break the representation does not encode (note
// section 4); decode assigns fresh ids -- coordinates are injective, so the
// read order is a function of coordinates alone and ids never break a tie.

import { embedRGA, eliasDeltaCode } from './datatypes/embedRGA.js';
import { decodeOne } from './compact.js';

const enc = eliasDeltaCode.enc;
const ONE = enc(1); // '0': every non-head run member has delta 1

/** Bit length of a nonneg int (Python int.bit_length): 0->0, 3->2, 8->4. */
export function bitLength(n) { let b = 0; while (n > 0) { b++; n = Math.floor(n / 2); } return b; }

/** |flipped-Elias-delta(d)| for d>=1, == enc(d).length == entropy_measure.bits_D. */
export function bitsD(d) { const L = bitLength(d); return (2 * bitLength(L) - 1) + (L - 1); }

const utf8 = new TextEncoder();
const dutf8 = new TextDecoder();

// ---------------------------------------------------------------- bit io
class BitWriter {
  constructor() { this.bytes = []; this.cur = 0; this.nbits = 0; this.total = 0; }
  bit(b) {
    this.cur = (this.cur << 1) | (b & 1); this.nbits++; this.total++;
    if (this.nbits === 8) { this.bytes.push(this.cur); this.cur = 0; this.nbits = 0; }
  }
  code(str) { for (let i = 0; i < str.length; i++) this.bit(str.charCodeAt(i) - 48); }
  uint(v, w) { for (let i = w - 1; i >= 0; i--) this.bit((v >>> i) & 1); }
  finish() { if (this.nbits) { this.cur <<= (8 - this.nbits); this.bytes.push(this.cur); this.cur = 0; this.nbits = 0; } return Uint8Array.from(this.bytes); }
}

class BitReader {
  constructor(u8, bitPos = 0) { this.u8 = u8; this.pos = bitPos; }
  bit() { const b = (this.u8[this.pos >> 3] >> (7 - (this.pos & 7))) & 1; this.pos++; return b; }
  uint(w) { let v = 0; for (let i = 0; i < w; i++) v = (v << 1) | this.bit(); return v >>> 0; }
  elias() { // inverse of enc, mirroring compact.js decodeOne at bit granularity
    let c = 0; while (this.bit() === 1) c++;            // header ones then the '0'
    let L = 1; for (let k = 0; k < c; k++) L = 2 * L + this.bit();
    let d = 1; for (let k = 0; k < L - 1; k++) d = 2 * d + this.bit();
    return d;
  }
  align() { if (this.pos & 7) this.pos = (this.pos + 7) & ~7; }
}

const writeVarint = (arr, n) => { while (n >= 128) { arr.push((n & 127) | 128); n = Math.floor(n / 128); } arr.push(n); };
const readVarint = (u8, c) => { let n = 0, s = 0, b; do { b = u8[c.i++]; n += (b & 127) * 2 ** s; s += 7; } while (b & 128); return n; };

// ------------------------------------------------------- table construction
/** Kept-tree of a state: root with children Map keyed by delta; a node is
 *  live iff it carries a record. Reuses compact.js's decodeOne. */
function coordTree(state) {
  const root = { children: new Map(), rid: null, el: undefined, delta: null };
  for (const [id, rec] of state) {
    let node = root, i = 0;
    const coord = rec.coord;
    while (i < coord.length) {
      const [d, j] = decodeOne(coord, i);
      let ch = node.children.get(d);
      if (!ch) { ch = { children: new Map(), rid: null, el: undefined, delta: d }; node.children.set(d, ch); }
      node = ch; i = j;
    }
    node.rid = id; node.el = rec.el;
  }
  return root;
}

/** Canonical partition into maximal fusible chains (mirrors
 *  run_table_measure.build_table). Returns entries in a parents-before-
 *  children order; each entry: { live, parent (eid|-1), poff, delta,
 *  members: node[] }. att[eid] = child eids, all attached at the tail. */
export function buildRunTable(state) {
  const root = coordTree(state);
  const entries = [];
  const att = [];
  const stack = [];
  for (const c of root.children.values()) stack.push({ node: c, parent: -1, poff: 0 });
  while (stack.length) {
    const { node, parent, poff } = stack.pop();
    const eid = entries.length;
    const live = node.rid !== null;
    const e = { live, parent, poff, delta: node.delta, members: [node] };
    entries.push(e); att.push([]);
    if (parent >= 0) att[parent].push(eid);
    let n = node;
    for (;;) {
      if (n.children.size === 1) {
        const k = n.children.values().next().value;
        if (k.delta === 1 && (k.rid !== null) === (n.rid !== null)) { e.members.push(k); n = k; continue; }
      }
      break;
    }
    const tailOff = e.members.length - 1;
    for (const k of n.children.values()) stack.push({ node: k, parent: eid, poff: tailOff });
  }
  // tail-attachment invariant, by construction: poff == parent length - 1
  for (const e of entries) {
    if (e.parent >= 0 && e.poff !== entries[e.parent].members.length - 1) {
      throw new Error('run table: interior attachment (tail-attachment lemma violated)');
    }
  }
  return { entries, att };
}

// -------------------------------------------------------------- accounting
/** The pre-registered bit accounting of run_table_measure.account(t, False):
 *  per record run-id (W) + offset D(off+1); per entry liveness + parent ref
 *  (W) + parent-offset D(poff+1) + head-delta D(delta) + length D(len).
 *  Reproduces the projection totals bit-for-bit on the same table. */
export function accountingBits(table) {
  const { entries } = table;
  const nEnt = entries.length;
  const w = Math.max(1, bitLength(nEnt));
  let nRec = 0, recOff = 0, hdrPoff = 0, hdrDelta = 0, hdrLen = 0, liveRuns = 0;
  for (const e of entries) {
    const len = e.members.length;
    if (e.live) { liveRuns++; nRec += len; for (let j = 0; j < len; j++) recOff += bitsD(j + 1); }
    hdrPoff += bitsD((e.parent < 0 ? 0 : e.poff) + 1);
    hdrDelta += bitsD(e.delta);
    hdrLen += bitsD(len);
  }
  const recId = nRec * w, hdrFlag = nEnt, hdrParent = nEnt * w;
  const total = recId + recOff + hdrFlag + hdrParent + hdrPoff + hdrDelta + hdrLen;
  return { total, rec_id: recId, rec_off: recOff, hdr_flag: hdrFlag, hdr_parent: hdrParent, hdr_poff: hdrPoff, hdr_delta: hdrDelta, hdr_len: hdrLen, n_ent: nEnt, n_rec: nRec, n_live_runs: liveRuns, w };
}

// ------------------------------------------------------------ display walk
/** Display order (elements) from the table alone, no coordinate
 *  materialization: pre-order over the contracted tree, live members in
 *  offset order (an anchor sorts above its subtree), branches at the tail
 *  newest-first = head-delta descending. Siblings have distinct deltas (the
 *  coordinate tree keys children by delta), so the order is total. Mirrors
 *  run_table_measure.table_walk for the one-sided family. */
export function tableWalk(table) {
  const { entries, att } = table;
  const kids = (list) => list.slice().sort((a, b) => entries[b].delta - entries[a].delta);
  const roots = kids(entries.map((_, i) => i).filter((i) => entries[i].parent < 0));
  const out = [];
  const stack = roots.reverse().map((i) => ({ eid: i }));
  while (stack.length) {
    const { eid } = stack.pop();
    const e = entries[eid];
    if (e.live) for (const m of e.members) out.push(m.el);
    const cs = kids(att[eid]);
    for (let i = cs.length - 1; i >= 0; i--) stack.push({ eid: cs[i] });
  }
  return out;
}

// ------------------------------------------------------------- encode/decode
/** encode(state) -> Uint8Array. Layout: varint(N_ent); mode byte; then a
 *  bit-packed metadata block, per entry in eid order: 1 liveness bit, W
 *  parent-ref bits (0 = root, else parentEid+1), Elias-delta(head delta),
 *  Elias-delta(length); byte-align; then the elements in storage order (each
 *  live entry, members in offset order). Element modes: mode 0 (every element
 *  a single Unicode code point, the text case) packs the code points as one
 *  self-delimiting UTF-8 blob at 1 byte/char for ASCII, matching the
 *  projection's text term exactly; mode 1 (general) writes varint(utf8
 *  len)++utf8 per element. The metadata bit count equals accountingBits.total
 *  minus the recoverable rec_id, rec_off and hdr_poff (asserted in the
 *  tests): the run-id/offset are positional and the parent-offset derivable,
 *  the section-9.1 saving the model charges but a real encoder drops. */
export function encode(state) {
  const table = buildRunTable(state);
  const { entries } = table;
  const nEnt = entries.length;
  const w = Math.max(1, bitLength(nEnt));
  const bw = new BitWriter();
  for (const e of entries) {
    bw.bit(e.live ? 1 : 0);
    bw.uint(e.parent < 0 ? 0 : e.parent + 1, w);
    bw.code(enc(e.delta));
    bw.code(enc(e.members.length));
  }
  const metaBits = bw.total;
  const meta = bw.finish();
  // elements: pick the packed-code-point mode when every element is a single
  // code point (the sequence-of-characters case), else the general mode.
  let packed = true, text = '';
  for (const e of entries) {
    if (!e.live) continue;
    for (const m of e.members) { const s = String(m.el); text += s; if ([...s].length !== 1) packed = false; }
  }
  const head = []; writeVarint(head, nEnt); head.push(packed ? 0 : 1);
  let els;
  if (packed) {
    els = utf8.encode(text);
  } else {
    const b = [];
    for (const e of entries) {
      if (!e.live) continue;
      for (const m of e.members) { const u = utf8.encode(String(m.el)); writeVarint(b, u.length); for (const x of u) b.push(x); }
    }
    els = Uint8Array.from(b);
  }
  const out = new Uint8Array(head.length + meta.length + els.length);
  out.set(head, 0); out.set(meta, head.length); out.set(els, head.length + meta.length);
  out.metaBits = metaBits; // annotation for the reconciliation test
  return out;
}

/** decode(bytes) -> Map id -> { coord, el } (a valid embed RGA state; ids
 *  are fresh sequential integers, coordinates reconstructed exactly). */
export function decode(u8) {
  const c = { i: 0 };
  const nEnt = readVarint(u8, c);
  const mode = u8[c.i++];
  const w = Math.max(1, bitLength(nEnt));
  const br = new BitReader(u8, c.i * 8);
  const es = [];
  let nRec = 0;
  for (let eid = 0; eid < nEnt; eid++) {
    const live = br.bit() === 1;
    const pref = br.uint(w);
    const delta = br.elias();
    const len = br.elias();
    if (live) nRec += len;
    es.push({ live, parent: pref - 1, delta, len, head: '', tail: '' });
  }
  br.align();
  // reconstruct coordinates: head = parentTail ++ enc(delta); tail = head ++ '0'*(len-1)
  for (const e of es) {
    const base = e.parent < 0 ? '' : es[e.parent].tail;
    e.head = base + enc(e.delta);
    e.tail = e.head + ONE.repeat(e.len - 1);
  }
  const state = new Map();
  const ec = { i: br.pos >> 3 };
  let id = 1;
  const cps = mode === 0 ? [...dutf8.decode(u8.subarray(ec.i))] : null;
  let cpi = 0;
  for (const e of es) {
    if (!e.live) continue;
    for (let j = 0; j < e.len; j++) {
      let el;
      if (mode === 0) { el = cps[cpi++]; }
      else { const blen = readVarint(u8, ec); el = dutf8.decode(u8.subarray(ec.i, ec.i + blen)); ec.i += blen; }
      state.set(id++, Object.freeze({ coord: e.head + ONE.repeat(j), el }));
    }
  }
  return state;
}

/** Losslessness gate helper: the multiset {coord -> el} of decode(encode(s))
 *  equals that of s (coordinates injective), i.e. the run table is a lossless
 *  re-representation. Returns true or throws with the first mismatch. */
export function roundTripReads(state) {
  const back = decode(encode(state));
  const a = embedRGA.read(state), b = embedRGA.read(back);
  if (a.length !== b.length) throw new Error(`read length ${a.length} != ${b.length}`);
  for (let i = 0; i < a.length; i++) if (a[i] !== b[i]) throw new Error(`read mismatch at ${i}: ${a[i]} != ${b[i]}`);
  return true;
}
