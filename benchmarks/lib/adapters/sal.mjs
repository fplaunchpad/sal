// Adapter for OUR system: the embed RGA of runtime/ (as shipped), plus its
// state compaction (runtime/src/compact.js) where the workload permits a
// settled cut.
//
// AS-SHIPPED means: the persistent datatype interface (apply returns a
// fresh Map: O(live-set) copy per op), records carrying ABSOLUTE chain
// coordinates as '0'/'1' bit-strings under the flipped Elias-delta code.
// Both are known representation choices; the save-size gap vs the
// run-table PROJECTION is reported separately and honestly.
//
// Position bookkeeping: the trace speaks positions, the datatype speaks
// (id, anchorId). The adapter maintains the display-order id list (view)
// incrementally; correctness rests on the RGA newest-first rule: a freshly
// minted id is larger than every id in the state, so it sorts first among
// its anchor's children, i.e. lands immediately after its anchor. The
// harness gate re-derives the text from datatype.read at the end and
// compares. Ids are dense Lamport ticks (deletes tick too), matching the
// litmus model (whiteboard/litmus/entropy_measure.py) so that the
// run-table projection is computed over the SAME id/delta stream.
//
// For the concurrent pair we use the shipped Runtime/Replica head-sync
// discipline (runtime/src/runtime.js) with commit GC after each sync.

import { embedRGA } from '../../../runtime/src/datatypes/embedRGA.js';
import { compactEliasDelta } from '../../../runtime/src/compact.js';
import { encode as rtEncode } from '../../../runtime/src/serialize.js';
import { Runtime } from '../../../runtime/src/runtime.js';
import { sharedDelta, wireBytes } from '../../../runtime/src/sync.js';
import { timed } from '../bench.mjs';

/** Task #104 SHIPPED run-table serializer: encode(state) -> Uint8Array.
 *  Realizes the task #73 run-table PROJECTION as actual bytes: entry headers
 *  (liveness, parent ref, head delta, length) bit-packed + records stored
 *  positionally (run-id and offset positional, parent-offset derivable by the
 *  tail-attachment lemma) + text packed at 1 byte/char. Lossless: decode
 *  reads identically (runtime/test/serialize.test.js). This is the shipped
 *  successor to the absolute-chain json-shipped/binary-estimate columns. */
export function saveRunTable(state) { return rtEncode(state); }

const dt = embedRGA;

const varintLen = (n) => {
  let b = 1;
  while (n >= 128) { n = Math.floor(n / 128); b++; }
  return b;
};

/** Shipped-native serialization: JSON of [[id, coord, el]...] sorted by id
 *  (the datatype's own fingerprint format). Coord is a '0'/'1' string:
 *  1 BYTE PER BIT. This is what the runtime can write today. */
export function saveJson(state) {
  return JSON.stringify(
    [...state.entries()].sort(([x], [y]) => x - y).map(([id, r]) => [id, r.coord, r.el])
  );
}

export function loadJson(str) {
  const s = new Map();
  for (const [id, coord, el] of JSON.parse(str)) {
    s.set(id, Object.freeze({ coord, el }));
  }
  // A load must re-derive the display order to render: include the sort.
  const view = dt.readIds(s);
  return { state: s, view };
}

/** Defined binary ESTIMATE (computed, no encoder shipped): records sorted
 *  by id; per record varint(id delta) + varint(coord bit-length) + packed
 *  coord bits (ceil(bits/8)) + UTF-8 bytes of the element; plus
 *  varint(count). The (ts,agent) tie-break is the id itself (charged);
 *  no framing/compression. */
export function binaryEstimate(state) {
  const ids = [...state.keys()].sort((a, b) => a - b);
  let bytes = varintLen(ids.length);
  let prev = 0;
  for (const id of ids) {
    const r = state.get(id);
    bytes += varintLen(id - prev) + varintLen(r.coord.length)
      + Math.ceil(r.coord.length / 8) + Buffer.byteLength(r.el, 'utf8');
    prev = id;
  }
  return bytes;
}

export function mkAdapter() {
  return {
    name: 'sal-embed-rga',
    version: 'runtime/ @ repo HEAD (unversioned)',
    create() { return { state: dt.init(), view: [], clock: 0 }; },
    ins(doc, pos, ch) {
      doc.clock += 1;
      const id = doc.clock;
      const anchorId = pos > 0 ? doc.view[pos - 1] : null;
      doc.state = dt.apply(doc.state, { type: 'ins', id, el: ch, anchorId });
      doc.view.splice(pos, 0, id);
    },
    del(doc, pos) {
      doc.clock += 1; // dense logical time, as in the litmus model
      const id = doc.view[pos];
      doc.state = dt.apply(doc.state, { type: 'del', id });
      doc.view.splice(pos, 1);
    },
    text(doc) { return dt.read(doc.state).join(''); },
    liveCount(doc) { return doc.state.size; },

    saveVariants(doc) {
      return [
        { label: 'json-shipped', mk: () => saveJson(doc.state),
          note: 'live state only; coord bit-strings at 1 byte/bit (shipped)' },
        { label: 'binary-estimate', estimate: () => binaryEstimate(doc.state),
          note: 'live state only; packed coord bits + varint ids (computed estimate, no shipped encoder)' },
        { label: 'run-table-serialized', mk: () => saveRunTable(doc.state),
          note: 'live state only; task #104 SHIPPED run-table binary (entry headers + positional records + packed text); lossless, decodes to the same read' },
      ];
    },
    load(data) { return loadJson(data); },

    /** Settled-cut compaction (single-writer or fully-synced states only).
     *  settledIds = every Lamport tick minted so far; insert ids are a
     *  subset, extra ids are never consulted. */
    compact(doc) {
      const settledIds = new Set();
      for (let i = 1; i <= doc.clock; i++) settledIds.add(i);
      const [res, ms] = timed(() =>
        compactEliasDelta(doc.state, { settledIds }, { fuseSpines: true }));
      return {
        ms, stats: res.stats,
        compacted: { state: res.state, view: doc.view, clock: doc.clock },
      };
    },

    /** Two replicas under the shipped Runtime head-sync discipline. */
    pair() {
      const runtime = new Runtime(dt);
      const rA = runtime.replica('A'), rB = runtime.replica('B');
      const p = {
        runtime, rA, rB,
        viewA: [], viewB: [], lamA: 0, lamB: 0, minted: [],
        gcMsTotal: 0,
        _ins(r, viewKey, lamKey, bit, pos, ch) {
          p[lamKey] += 1;
          const id = p[lamKey] * 2 + bit;
          p.minted.push(id);
          const view = p[viewKey];
          const anchorId = pos > 0 ? view[pos - 1] : null;
          r.commit({ type: 'ins', id, el: ch, anchorId });
          view.splice(pos, 0, id);
        },
        _del(r, viewKey, pos) {
          const view = p[viewKey];
          r.commit({ type: 'del', id: view[pos] });
          view.splice(pos, 1);
        },
        insA: (pos, ch) => p._ins(rA, 'viewA', 'lamA', 0, pos, ch),
        delA: (pos) => p._del(rA, 'viewA', pos),
        insB: (pos, ch) => p._ins(rB, 'viewB', 'lamB', 1, pos, ch),
        delB: (pos) => p._del(rB, 'viewB', pos),
        lenA: () => p.viewA.length,
        lenB: () => p.viewB.length,
        /** Timed portion: the head-sync (merge3 via unique LCA). Commit GC
         *  and view rebuild are outside the timed window, reported apart.
         *  payloadBytes = the bidirectional DELTA the wire protocol
         *  (runtime/src/sync.js) would ship for this sync: the commits each
         *  head lacks from the other, as op payloads + parent refs + author
         *  id (NOT whole state). Measured BEFORE the merge, when the heads
         *  still diverge; comparable to Yjs/Automerge's update-bytes column. */
        sync() {
          const aH = rA.head.id, bH = rB.head.id;
          const toB = sharedDelta(runtime.dag, aH, bH);
          const toA = sharedDelta(runtime.dag, bH, aH);
          const payloadBytes = wireBytes({ t: 'delta', c: toB }) + wireBytes({ t: 'delta', c: toA });
          const [, ms] = timed(() => rA.sync(rB));
          const [, gcMs] = timed(() => runtime.gc());
          p.gcMsTotal += gcMs;
          const lam = Math.max(p.lamA, p.lamB);
          p.lamA = lam; p.lamB = lam;
          const ids = dt.readIds(rA.head.state);
          p.viewA = [...ids]; p.viewB = [...ids];
          return { ms, payloadBytes };
        },
        textA: () => dt.read(rA.head.state).join(''),
        textB: () => dt.read(rB.head.state).join(''),
        saveVariants() {
          const st = rA.head.state;
          return [
            { label: 'json-shipped', mk: () => saveJson(st) },
            { label: 'binary-estimate', estimate: () => binaryEstimate(st) },
            { label: 'run-table-serialized', mk: () => saveRunTable(st),
              note: 'task #104 SHIPPED run-table binary (lossless)' },
          ];
        },
        compactFinal() {
          const settledIds = new Set(p.minted);
          const [res, ms] = timed(() =>
            compactEliasDelta(rA.head.state, { settledIds }, { fuseSpines: true }));
          return { ms, stats: res.stats, state: res.state };
        },
      };
      return p;
    },
  };
}
