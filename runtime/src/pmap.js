// PMap: a dependency-free, browser-safe persistent hash-array-mapped trie
// (HAMT) for string/number keys -- the state container that kills the
// O(live-set) Map copy per op in the datatypes (task #111).
//
// API (the Map surface the runtime's consumers actually use):
//   PMap.empty()            the shared empty map
//   PMap.from(iterable)     bulk build from [k, v] pairs (one transient pass)
//   m.get(k) / m.has(k) / m.size
//   m.set(k, v)  -> a NEW PMap (O(log n) path copy, structural sharing)
//   m.delete(k)  -> a NEW PMap (O(log n); absent key returns m itself)
//   m.entries() / m.keys() / m.values() / m.forEach(cb) / [Symbol.iterator]
//   m.begin()    -> transient handle { get, has, set, delete, size, freeze }
//                   for batch building: set/delete mutate in place (token-
//                   owned nodes only; shared structure is copied on first
//                   touch), freeze() returns the persistent PMap.
//
// ITERATION POLICY (deliberate): full iteration is only used at read /
// serialize / fingerprint points, which sort anyway -- so the public
// iteration surface (entries/keys/values/forEach/iterator) is DETERMINISTIC:
// it collects the entries and sorts them by key ascending (numbers before
// strings). No consumer can accidentally depend on hash order, and twin
// replicas that reach the same key set through different histories iterate
// identically. forEachRaw is the one hash-order escape hatch, for
// order-INSENSITIVE bulk scans only (merge rebuilds, sums, tree building
// whose output is itself content-canonical); never let its order reach an
// observable (bytes, arrays, hashes).
//
// Hashing: 32-bit (FNV-1a for strings, a murmur3-finalized mix for
// integers), consumed 5 bits per trie level (7 levels max); full-hash
// collisions go to collision nodes keyed by ===. Keys of the runtime are
// integer timestamps/mids and string tags; non-integer numbers fall back to
// hashing their decimal string (correctness is unaffected: equality is ===).

const BITS = 5;
const MASK = 31;

// ---------------------------------------------------------------- hashing
const mix = (h) => {
  h ^= h >>> 16; h = Math.imul(h, 0x85ebca6b);
  h ^= h >>> 13; h = Math.imul(h, 0xc2b2ae35);
  h ^= h >>> 16; return h >>> 0;
};

const hashString = (s) => {
  let h = 0x811c9dc5;
  for (let i = 0; i < s.length; i++) {
    h ^= s.charCodeAt(i);
    h = Math.imul(h, 0x01000193);
  }
  return mix(h >>> 0);
};

export const hashKey = (k) => {
  if (typeof k === 'number' && Number.isInteger(k)) {
    const lo = (k % 0x100000000) >>> 0;
    const hi = Math.floor(k / 0x100000000) | 0;
    return mix(lo ^ Math.imul(hi, 0x9e3779b9));
  }
  return hashString(typeof k === 'string' ? k : String(k));
};

/** Deterministic public iteration order: numbers ascending, then strings
 *  ascending (keys are homogeneous per datatype in practice). */
export const cmpKeys = (a, b) => {
  const ta = typeof a, tb = typeof b;
  if (ta !== tb) return ta === 'number' ? -1 : 1;
  if (ta === 'number') return a - b;
  return a < b ? -1 : a > b ? 1 : 0;
};

const popcount = (x) => {
  x = x - ((x >>> 1) & 0x55555555);
  x = (x & 0x33333333) + ((x >>> 2) & 0x33333333);
  x = (x + (x >>> 4)) & 0x0f0f0f0f;
  return Math.imul(x, 0x01010101) >>> 24;
};

// ------------------------------------------------------------------ nodes
// Leaf: one entry. CNode: full-hash collision bucket. BNode: bitmap branch.
// `edit` is the transient ownership token (null on persistent nodes): a
// transient may mutate exactly the nodes carrying ITS token; everything
// else is copied on first touch (path copy, structural sharing).
class Leaf { constructor(edit, h, k, v) { this.edit = edit; this.h = h; this.k = k; this.v = v; } }
class CNode { constructor(edit, h, keys, vals) { this.edit = edit; this.h = h; this.keys = keys; this.vals = vals; } }
class BNode { constructor(edit, bitmap, arr) { this.edit = edit; this.bitmap = bitmap; this.arr = arr; } }

const editableB = (n, edit) =>
  (edit !== null && n.edit === edit) ? n : new BNode(edit, n.bitmap, n.arr.slice());
const editableC = (n, edit) =>
  (edit !== null && n.edit === edit) ? n : new CNode(edit, n.h, n.keys.slice(), n.vals.slice());

/** Two leaf-ish nodes (Leaf|CNode) with DIFFERENT hashes: branch at the
 *  first level where their hash chunks differ. */
function mergeLeaves(edit, shift, a, b) {
  const ia = (a.h >>> shift) & MASK, ib = (b.h >>> shift) & MASK;
  if (ia === ib) return new BNode(edit, 1 << ia, [mergeLeaves(edit, shift + BITS, a, b)]);
  const arr = ia < ib ? [a, b] : [b, a];
  return new BNode(edit, (1 << ia) | (1 << ib), arr);
}

function assoc(node, shift, h, k, v, edit, res) {
  if (node === null) { res.added = true; return new Leaf(edit, h, k, v); }
  if (node instanceof Leaf) {
    if (node.h === h && node.k === k) {
      if (node.v === v) return node;
      if (edit !== null && node.edit === edit) { node.v = v; return node; }
      return new Leaf(edit, h, k, v);
    }
    res.added = true;
    if (node.h === h) return new CNode(edit, h, [node.k, k], [node.v, v]);
    return mergeLeaves(edit, shift, node, new Leaf(edit, h, k, v));
  }
  if (node instanceof CNode) {
    if (node.h !== h) {
      res.added = true;
      return mergeLeaves(edit, shift, node, new Leaf(edit, h, k, v));
    }
    const i = node.keys.indexOf(k);
    if (i >= 0 && node.vals[i] === v) return node;
    const c = editableC(node, edit);
    if (i >= 0) { c.vals[i] = v; }
    else { c.keys.push(k); c.vals.push(v); res.added = true; }
    return c;
  }
  // BNode
  const bit = 1 << ((h >>> shift) & MASK);
  const pos = popcount(node.bitmap & (bit - 1));
  if (node.bitmap & bit) {
    const child = node.arr[pos];
    const nc = assoc(child, shift + BITS, h, k, v, edit, res);
    if (nc === child) return node;
    const b = editableB(node, edit);
    b.arr[pos] = nc;
    return b;
  }
  res.added = true;
  const leaf = new Leaf(edit, h, k, v);
  if (edit !== null && node.edit === edit) {
    node.arr.splice(pos, 0, leaf);
    node.bitmap |= bit;
    return node;
  }
  const arr = node.arr.slice(0, pos);
  arr.push(leaf);
  for (let i = pos; i < node.arr.length; i++) arr.push(node.arr[i]);
  return new BNode(edit, node.bitmap | bit, arr);
}

function dissoc(node, shift, h, k, edit, res) {
  if (node === null) return null;
  if (node instanceof Leaf) {
    if (node.h === h && node.k === k) { res.removed = true; return null; }
    return node;
  }
  if (node instanceof CNode) {
    if (node.h !== h) return node;
    const i = node.keys.indexOf(k);
    if (i < 0) return node;
    res.removed = true;
    if (node.keys.length === 2) {
      const j = 1 - i;
      return new Leaf(edit, h, node.keys[j], node.vals[j]);
    }
    const c = editableC(node, edit);
    c.keys.splice(i, 1); c.vals.splice(i, 1);
    return c;
  }
  // BNode
  const bit = 1 << ((h >>> shift) & MASK);
  if (!(node.bitmap & bit)) return node;
  const pos = popcount(node.bitmap & (bit - 1));
  const child = node.arr[pos];
  const nc = dissoc(child, shift + BITS, h, k, edit, res);
  if (nc === child) return node;
  if (nc === null) {
    if (node.arr.length === 1) return null;
    if (node.arr.length === 2) {
      const other = node.arr[1 - pos];
      if (!(other instanceof BNode)) return other; // lift the surviving leaf/bucket
    }
    if (edit !== null && node.edit === edit) {
      node.arr.splice(pos, 1);
      node.bitmap &= ~bit;
      return node;
    }
    const arr = node.arr.slice();
    arr.splice(pos, 1);
    return new BNode(edit, node.bitmap & ~bit, arr);
  }
  if (node.arr.length === 1 && !(nc instanceof BNode)) return nc; // canonical lift
  const b = editableB(node, edit);
  b.arr[pos] = nc;
  return b;
}

function nodeGet(node, h, k, notFound) {
  let shift = 0;
  while (node !== null) {
    if (node instanceof Leaf) return (node.h === h && node.k === k) ? node.v : notFound;
    if (node instanceof CNode) {
      if (node.h !== h) return notFound;
      const i = node.keys.indexOf(k);
      return i >= 0 ? node.vals[i] : notFound;
    }
    const bit = 1 << ((h >>> shift) & MASK);
    if (!(node.bitmap & bit)) return notFound;
    node = node.arr[popcount(node.bitmap & (bit - 1))];
    shift += BITS;
  }
  return notFound;
}

function forEachNode(node, fn) {
  if (node === null) return;
  if (node instanceof Leaf) { fn(node.k, node.v); return; }
  if (node instanceof CNode) {
    for (let i = 0; i < node.keys.length; i++) fn(node.keys[i], node.vals[i]);
    return;
  }
  for (let i = 0; i < node.arr.length; i++) forEachNode(node.arr[i], fn);
}

const NOT_FOUND = Symbol('pmap.notFound');

// ------------------------------------------------------------------- PMap
export class PMap {
  #root; #size;
  /** Internal: use PMap.empty() / PMap.from / set / delete / freeze. */
  constructor(root, size) { this.#root = root; this.#size = size; }

  static #EMPTY = new PMap(null, 0);
  static empty() { return PMap.#EMPTY; }
  static from(iterable) {
    const t = PMap.#EMPTY.begin();
    for (const [k, v] of iterable) t.set(k, v);
    return t.freeze();
  }

  get size() { return this.#size; }
  get(k) {
    const v = nodeGet(this.#root, hashKey(k), k, NOT_FOUND);
    return v === NOT_FOUND ? undefined : v;
  }
  has(k) { return nodeGet(this.#root, hashKey(k), k, NOT_FOUND) !== NOT_FOUND; }

  set(k, v) {
    const res = { added: false };
    const r = assoc(this.#root, 0, hashKey(k), k, v, null, res);
    if (r === this.#root) return this;
    return new PMap(r, this.#size + (res.added ? 1 : 0));
  }
  delete(k) {
    const res = { removed: false };
    const r = dissoc(this.#root, 0, hashKey(k), k, null, res);
    if (!res.removed) return this;
    return new PMap(r, this.#size - 1);
  }

  /** HASH-ORDER iteration (the escape hatch): order-insensitive bulk scans
   *  ONLY -- never let this order reach bytes, arrays, or hashes. */
  forEachRaw(fn) { forEachNode(this.#root, fn); }

  /** Sorted [k, v] pairs (key ascending: the deterministic public order). */
  entries() {
    const out = [];
    forEachNode(this.#root, (k, v) => out.push([k, v]));
    out.sort((a, b) => cmpKeys(a[0], b[0]));
    return out;
  }
  keys() { return this.entries().map((e) => e[0]); }
  values() { return this.entries().map((e) => e[1]); }
  forEach(cb, thisArg) { for (const [k, v] of this.entries()) cb.call(thisArg, v, k, this); }
  [Symbol.iterator]() { return this.entries()[Symbol.iterator](); }

  begin() { return new TransientPMap(this.#root, this.#size); }
}

/** Mutable batch-building handle (from pmap.begin()): set/delete in place
 *  on token-owned nodes, copy-on-first-touch for shared structure; freeze()
 *  seals it into a persistent PMap (the handle is dead afterwards). */
class TransientPMap {
  #edit; #root; #size;
  constructor(root, size) { this.#edit = {}; this.#root = root; this.#size = size; }
  #alive() { if (this.#edit === null) throw new Error('transient used after freeze()'); }

  get size() { this.#alive(); return this.#size; }
  get(k) {
    this.#alive();
    const v = nodeGet(this.#root, hashKey(k), k, NOT_FOUND);
    return v === NOT_FOUND ? undefined : v;
  }
  has(k) { this.#alive(); return nodeGet(this.#root, hashKey(k), k, NOT_FOUND) !== NOT_FOUND; }
  set(k, v) {
    this.#alive();
    const res = { added: false };
    this.#root = assoc(this.#root, 0, hashKey(k), k, v, this.#edit, res);
    if (res.added) this.#size++;
    return this;
  }
  delete(k) {
    this.#alive();
    const res = { removed: false };
    this.#root = dissoc(this.#root, 0, hashKey(k), k, this.#edit, res);
    if (res.removed) this.#size--;
    return this;
  }
  freeze() {
    this.#alive();
    this.#edit = null;
    return this.#size === 0 ? PMap.empty() : new PMap(this.#root, this.#size);
  }
}

// ------------------------------------------------------------------- PSet
/** Persistent set over PMap (value slot unused): peritext's grow-only
 *  deleted-ids container. Iteration is sorted (the PMap policy). */
export class PSet {
  #m;
  constructor(m) { this.#m = m; }
  static #EMPTY = new PSet(PMap.empty());
  static empty() { return PSet.#EMPTY; }
  static from(iterable) {
    const t = PSet.#EMPTY.begin();
    for (const k of iterable) t.add(k);
    return t.freeze();
  }
  get size() { return this.#m.size; }
  has(k) { return this.#m.has(k); }
  add(k) { const m2 = this.#m.set(k, true); return m2 === this.#m ? this : new PSet(m2); }
  delete(k) { const m2 = this.#m.delete(k); return m2 === this.#m ? this : new PSet(m2); }
  keys() { return this.#m.keys(); }
  values() { return this.#m.keys(); }
  forEachRaw(fn) { this.#m.forEachRaw((k) => fn(k)); }
  [Symbol.iterator]() { return this.#m.keys()[Symbol.iterator](); }
  begin() {
    const t = this.#m.begin();
    return {
      add: (k) => { t.set(k, true); },
      delete: (k) => { t.delete(k); },
      has: (k) => t.has(k),
      get size() { return t.size; },
      freeze: () => { const m = t.freeze(); return m.size === 0 ? PSet.empty() : new PSet(m); },
    };
  }
}

export const isPMap = (x) => x instanceof PMap;
export const isPSet = (x) => x instanceof PSet;

/** Iterate keys+values of a PMap (hash order) OR a plain Map (insertion
 *  order): the shared helper for order-insensitive bulk scans over states
 *  that may be either (legacy Map states appear in tests and tools). */
export const eachEntry = (m, fn) => {
  if (m instanceof PMap) m.forEachRaw(fn);
  else for (const [k, v] of m) fn(k, v);
};
