// Prefix-sharing representation of EmbedRGA coordinates.
//
// A live record points to an immutable path node { parent, delta, id }. Nodes
// are shared by descendants, so insertion allocates one node rather than
// copying the complete root-to-anchor bit string. Deleted anchors disappear
// from the live PMap while their path nodes remain reachable from descendants.
// This is a representation change only: `deltas(node)` is exactly the chain
// decoded from EmbedRGA's absolute coordinate.

import { PMap, isPMap, eachEntry } from '../pmap.js';

const node = (parent, delta, id, birthId = id, birthParentId = parent?.birthId ?? 0) =>
  Object.freeze({ parent, delta, id, birthId, birthParentId });

function deltas(n) {
  const out = [];
  while (n) { out.push(n.delta); n = n.parent; }
  out.reverse();
  return out;
}

function samePath(a, b) {
  if (a === b) return true;
  const x = deltas(a), y = deltas(b);
  return x.length === y.length && x.every((d, i) => d === y[i]);
}

/** Materialize the path only at compatibility/debug boundaries. */
export function pathDeltas(rec) { return deltas(rec.path); }

const utf8 = new TextEncoder(), dutf8 = new TextDecoder();
const putVar = (out, n) => {
  while (n >= 128) { out.push((n & 127) | 128); n = Math.floor(n / 128); }
  out.push(n);
};
const getVar = (u8, c) => {
  let n = 0, s = 0, b;
  do { b = u8[c.i++]; n += (b & 127) * 2 ** s; s += 7; } while (b & 128);
  return n;
};
const zig = (n) => n < 0 ? -2 * n - 1 : 2 * n;
const unzig = (n) => n & 1 ? -(n + 1) / 2 : n / 2;

function retainedGraph(state) {
  const nodes = new Map(), live = new Map(), children = new Map(), roots = new Map();
  eachEntry(state, (id, rec) => {
    live.set(rec.path.id, { id, el: String(rec.el) });
    let n = rec.path;
    while (n && !nodes.has(n.id)) { nodes.set(n.id, n); n = n.parent; }
  });
  for (const n of nodes.values()) {
    if (n.parent && nodes.has(n.parent.id)) {
      let cs = children.get(n.parent.id);
      if (!cs) children.set(n.parent.id, cs = new Map());
      cs.set(n.id, n);
    } else roots.set(n.id, n);
  }
  return { nodes, live, children, roots };
}

/** Native snapshot of the retained prefix DAG. Parent ids are insertion ids
 * and therefore smaller than children under the honesty contract. */
export function encodeSharedState(state) {
  const nodes = new Map(), live = new Map();
  eachEntry(state, (id, rec) => {
    live.set(rec.path.id, { id, el: String(rec.el) });
    let n = rec.path;
    while (n && !nodes.has(n.id)) { nodes.set(n.id, n); n = n.parent; }
  });
  const ordered = [...nodes.values()].sort((a, b) => a.id - b.id), out = [];
  putVar(out, ordered.length);
  let prev = 0;
  for (const n of ordered) {
    putVar(out, n.id - prev); prev = n.id;
    putVar(out, n.parent?.id ?? 0); putVar(out, n.delta);
    const r = live.get(n.id); out.push(r ? 1 : 0);
    if (r) {
      const bytes = utf8.encode(r.el); putVar(out, bytes.length);
      for (const b of bytes) out.push(b);
    }
  }
  return Uint8Array.from(out);
}

export function decodeSharedState(u8) {
  const c = { i: 0 }, count = getVar(u8, c), nodes = new Map();
  const t = PMap.empty().begin();
  let id = 0;
  for (let k = 0; k < count; k++) {
    id += getVar(u8, c);
    const parentId = getVar(u8, c), delta = getVar(u8, c);
    const n = node(parentId ? nodes.get(parentId) : null, delta, id);
    if (parentId && !n.parent) throw new Error(`shared snapshot: missing parent ${parentId}`);
    nodes.set(id, n);
    if (u8[c.i++]) {
      const len = getVar(u8, c), el = dutf8.decode(u8.subarray(c.i, c.i + len)); c.i += len;
      t.set(id, Object.freeze({ path: n, el }));
    }
  }
  if (c.i !== u8.length) throw new Error('shared snapshot: trailing bytes');
  return t.freeze();
}

/** Run-compressed continuation snapshot. A run is a maximal unique-child
 * chain whose non-head deltas are 1 and whose nodes have the same liveness.
 * Entry headers encode one parent and head delta for the whole chain. True
 * insertion IDs need no sidecar: honesty gives id = parent.id + delta (root
 * parent id 0), including every delta-1 non-head member. */
export function encodeSharedRuns(state) {
  const g = retainedGraph(state), entries = [], stack = [];
  for (const n of g.roots.values()) stack.push({ n, parent: -1 });
  while (stack.length) {
    const { n: head, parent } = stack.pop(), live = g.live.has(head.id);
    const e = { parent, delta: head.delta, live, members: [head] };
    const eid = entries.length; entries.push(e);
    let tail = head;
    for (;;) {
      const cs = g.children.get(tail.id);
      if (!cs || cs.size !== 1) break;
      const child = cs.values().next().value;
      if (child.delta !== 1 || g.live.has(child.id) !== live) break;
      e.members.push(child); tail = child;
    }
    for (const child of g.children.get(tail.id)?.values() ?? [])
      stack.push({ n: child, parent: eid });
  }
  let explicitIds = false;
  for (const e of entries) for (const n of e.members)
    if (n.id !== (n.parent?.id ?? 0) + n.delta) explicitIds = true;
  const out = []; putVar(out, entries.length); out.push(explicitIds ? 2 : 0);
  for (const e of entries) {
    out.push(e.live ? 1 : 0); putVar(out, e.parent + 1);
    putVar(out, e.delta); putVar(out, e.members.length);
  }
  const liveNodes = entries.flatMap((e) => e.live ? e.members : []);
  if (explicitIds) {
    const tags = [], exceptions = []; let prev = 0;
    for (const n of liveNodes) {
      const idExceptional = n.birthId !== prev + 1;
      const parentExceptional = n.birthParentId !== n.birthId - 1;
      tags.push((idExceptional ? 1 : 0) | (parentExceptional ? 2 : 0));
      if (idExceptional) putVar(exceptions, zig(n.birthId - prev));
      if (parentExceptional) putVar(exceptions, n.birthId - n.birthParentId);
      prev = n.birthId;
    }
    for (let i = 0; i < tags.length; i += 4) out.push(
      (tags[i] ?? 0) | ((tags[i + 1] ?? 0) << 2)
      | ((tags[i + 2] ?? 0) << 4) | ((tags[i + 3] ?? 0) << 6));
    out.push(...exceptions);
  }
  for (const e of entries) for (const n of e.members) {
    if (e.live) {
      const bytes = utf8.encode(g.live.get(n.id).el); putVar(out, bytes.length);
      for (const b of bytes) out.push(b);
    }
  }
  return Uint8Array.from(out);
}

export function decodeSharedRuns(u8) {
  const c = { i: 0 }, count = getVar(u8, c), mode = u8[c.i++], entries = [];
  for (let k = 0; k < count; k++) entries.push({
    live: u8[c.i++] === 1, parent: getVar(u8, c) - 1,
    delta: getVar(u8, c), len: getVar(u8, c), tail: null,
  });
  const liveCount = entries.reduce((n, e) => n + (e.live ? e.len : 0), 0);
  let provenance = null;
  if (mode === 2) {
    const tagBytes = u8.subarray(c.i, c.i + Math.ceil(liveCount / 4));
    c.i += tagBytes.length; provenance = []; let prev = 0;
    for (let i = 0; i < liveCount; i++) {
      const tag = (tagBytes[i >> 2] >> (2 * (i & 3))) & 3;
      const birthId = tag & 1 ? prev + unzig(getVar(u8, c)) : prev + 1;
      const birthParentId = tag & 2 ? birthId - getVar(u8, c) : birthId - 1;
      provenance.push([birthId, birthParentId]); prev = birthId;
    }
  }
  const t = PMap.empty().begin();
  let prevLiveId = 0, synthetic = -1, liveIndex = 0;
  for (const e of entries) {
    let parent = e.parent < 0 ? null : entries[e.parent].tail;
    if (e.parent >= 0 && !parent) throw new Error(`shared runs: parent ${e.parent} not decoded`);
    for (let j = 0; j < e.len; j++) {
      const delta = j === 0 ? e.delta : 1;
      let id, birthId, birthParentId;
      if (e.live && mode === 2) {
        [birthId, birthParentId] = provenance[liveIndex++]; id = birthId;
      } else if (e.live && mode === 1) {
        birthId = prevLiveId + unzig(getVar(u8, c)); prevLiveId = birthId;
        birthParentId = getVar(u8, c); id = birthId;
      } else if (mode !== 0) { id = synthetic--; birthId = null; birthParentId = null; }
      else { id = (parent?.id ?? 0) + delta; birthId = id; birthParentId = parent?.birthId ?? 0; }
      const n = node(parent, delta, id, birthId, birthParentId); parent = n; e.tail = n;
      if (e.live) {
        const len = getVar(u8, c), el = dutf8.decode(u8.subarray(c.i, c.i + len)); c.i += len;
        t.set(id, Object.freeze({ path: n, el }));
      }
    }
  }
  if (c.i !== u8.length) throw new Error('shared runs: trailing bytes');
  return t.freeze();
}

export const sharedEmbedRGA = {
  init() { return PMap.empty(); },

  apply(state, op) {
    const p = isPMap(state);
    if (op.type === 'ins') {
      if (state.has(op.id)) throw new Error(`duplicate insert id ${op.id}`);
      let parent = null, anchor = 0;
      if (op.anchorId !== null && op.anchorId !== undefined) {
        const a = state.get(op.anchorId);
        if (!a) throw new Error(`anchor ${op.anchorId} not live`);
        parent = a.path; anchor = op.anchorId;
      }
      const delta = op.id - anchor;
      if (!Number.isInteger(delta) || delta < 1)
        throw new Error(`delta must be positive, got ${delta}`);
      const rec = Object.freeze({
        path: node(parent, delta, op.id, op.id, op.anchorId ?? 0), el: op.el,
      });
      return p ? state.set(op.id, rec) : new Map(state).set(op.id, rec);
    }
    if (op.type === 'del') {
      if (p) return state.delete(op.id);
      const s = new Map(state); s.delete(op.id); return s;
    }
    throw new Error(`unknown sharedEmbedRGA op type: ${op.type}`);
  },

  applyBatch(state, ops) {
    let s = state;
    for (const op of ops) s = this.apply(s, op);
    return isPMap(s) ? s : PMap.from(s);
  },

  // Build the retained insertion tree from shared path-node identity. Every
  // live record contributes its ancestor chain, but the `seen` set visits a
  // shared node once. Children are ordered by descending delta, matching the
  // monotone prefix code; a live anchor is emitted before its descendants.
  readEntries(state) {
    const roots = new Map(), children = new Map(), live = new Map(), seen = new Set();
    eachEntry(state, (id, rec) => {
      live.set(rec.path.id, [id, rec]);
      let n = rec.path;
      while (n && !seen.has(n.id)) {
        seen.add(n.id);
        if (n.parent) {
          let cs = children.get(n.parent.id);
          if (!cs) children.set(n.parent.id, cs = new Map());
          cs.set(n.id, n);
        } else roots.set(n.id, n);
        n = n.parent;
      }
    });
    const ordered = (xs) => [...xs.values()].sort((a, b) => b.delta - a.delta);
    const out = [], stack = ordered(roots).reverse();
    while (stack.length) {
      const n = stack.pop(), item = live.get(n.id);
      if (item) out.push(item);
      const cs = ordered(children.get(n.id) ?? new Map());
      for (let i = cs.length - 1; i >= 0; i--) stack.push(cs[i]);
    }
    return out;
  },

  read(state) { return this.readEntries(state).map(([, r]) => r.el); },
  readIds(state) { return this.readEntries(state).map(([id]) => id); },

  merge3(l, a, b) {
    const t = (isPMap(a) ? a : PMap.from(a)).begin();
    // Canonical path nodes already reachable from A, including deleted
    // ancestors retained by descendants. Fresh B records are rebased onto
    // these nodes by insertion id, so independently decoded replicas recover
    // physical prefix sharing after merge.
    const nodes = new Map();
    eachEntry(a, (_id, rec) => {
      let n = rec.path;
      while (n) {
        if (n.birthId !== null && n.birthId !== undefined && !nodes.has(n.birthId))
          nodes.set(n.birthId, n);
        n = n.parent;
      }
    });
    const canonical = (n) => {
      if (!n) return null;
      const old = n.birthId === null || n.birthId === undefined ? undefined : nodes.get(n.birthId);
      if (old) {
        if (old.birthParentId !== n.birthParentId)
          throw new Error(`birth divergence at node ${n.birthId}`);
        return old;
      }
      const c = node(canonical(n.parent), n.delta, n.id, n.birthId, n.birthParentId);
      if (c.birthId !== null && c.birthId !== undefined) nodes.set(c.birthId, c);
      return c;
    };
    eachEntry(l, (id) => { if (!b.has(id)) t.delete(id); });
    eachEntry(b, (id, rb) => {
      const ra = a.get(id);
      if (ra !== undefined) {
        if (ra.path.birthId !== rb.path.birthId
            || ra.path.birthParentId !== rb.path.birthParentId)
          throw new Error(`birth divergence at id ${id}: provenance must agree`);
      } else if (!l.has(id)) t.set(id,
        Object.freeze({ path: canonical(rb.path), el: rb.el }));
    });
    return t.freeze();
  },

  /** Physical retained path nodes, as opposed to EmbedRGA logical symbols. */
  nodeCount(state) {
    const seen = new Set();
    eachEntry(state, (_id, rec) => {
      let n = rec.path;
      while (n && !seen.has(n)) { seen.add(n); n = n.parent; }
    });
    return seen.size;
  },

  fingerprint(state) {
    return JSON.stringify([...state.entries()]
      .sort(([a], [b]) => a - b)
      .map(([id, rec]) => [id, deltas(rec.path), rec.el]));
  },
};
