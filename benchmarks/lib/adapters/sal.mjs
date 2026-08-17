// Adapter for OUR system: the embed RGA of runtime/ (as shipped), plus its
// state compaction (runtime/src/compact.js) where the workload permits a
// settled cut.
//
// AS-SHIPPED means: the persistent datatype interface (apply returns a
// fresh persistent-HAMT state, runtime/src/pmap.js: O(log n) path copy per
// op with structural sharing -- task #111 replaced the earlier
// O(live-set)-Map-copy-per-op interface cost), records carrying ABSOLUTE
// chain coordinates as '0'/'1' bit-strings under the flipped Elias-delta
// code. The save-size gap vs the run-table PROJECTION is reported
// separately and honestly.
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
import { rga } from '../../../runtime/src/datatypes/rga.js';
import { sharedEmbedRGA, encodeSharedRuns, decodeSharedRuns } from '../../../runtime/src/datatypes/sharedEmbedRGA.js';
import { sidedEmbedRGAExperimental, sharedSidedEmbedRGAExperimental } from '../../../runtime/src/datatypes/sidedEmbedRGA.js';
import { unifiedSidedEmbedRGAExperimental } from '../../../runtime/src/datatypes/unifiedSidedEmbedRGA.js';
import { PMap } from '../../../runtime/src/pmap.js';
import { compactEliasDelta } from '../../../runtime/src/compact.js';
import { compactSharedDirect } from '../../../runtime/src/shared-compact.js';
import { encode as rtEncode, decode as rtDecode } from '../../../runtime/src/serialize.js';
import { Runtime } from '../../../runtime/src/runtime.js';
import { sharedDelta, sharedContentGids, wireBytes } from '../../../runtime/src/sync.js';
import { timed } from '../bench.mjs';

/** Task #104 SHIPPED run-table serializer: encode(state) -> Uint8Array.
 *  Realizes the task #73 run-table PROJECTION as actual bytes: entry headers
 *  (liveness, parent ref, head delta, length) bit-packed + records stored
 *  positionally (run-id and offset positional, parent-offset derivable by the
 *  tail-attachment lemma) + text packed at 1 byte/char. Lossless: decode
 *  reads identically (runtime/test/serialize.test.js). This is the shipped
 *  successor to the absolute-chain json-shipped/binary-estimate columns. */
export function saveRunTable(state) { return rtEncode(state); }
export function loadRunTable(bytes) {
  const state = rtDecode(bytes);
  return { state, view: dt.readIds(state) };
}

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
  const t = PMap.empty().begin();
  for (const [id, coord, el] of JSON.parse(str)) {
    t.set(id, Object.freeze({ coord, el }));
  }
  const s = t.freeze();
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

export function mkAdapter({ shared = false, sided = false, unified = false, plainRGA = false } = {}) {
  const kernel = plainRGA ? rga : unified ? unifiedSidedEmbedRGAExperimental : sided
    ? (shared ? sharedSidedEmbedRGAExperimental : sidedEmbedRGAExperimental)
    : (shared ? sharedEmbedRGA : embedRGA);
  const candidateSave = (state) => kernel.encodeSnapshot(state);
  const candidateLoad = (bytes) => {
    const state = kernel.decodeSnapshot(bytes);
    return { state, view: kernel.readIds(state) };
  };
  const save = plainRGA || sided ? candidateSave : (shared ? encodeSharedRuns : saveRunTable);
  const load = plainRGA || sided ? candidateLoad : shared
    ? (bytes) => { const state = decodeSharedRuns(bytes); return { state, view: kernel.readIds(state) }; }
    : loadRunTable;
  const compactState = shared ? compactSharedDirect : compactEliasDelta;
  return {
    name: plainRGA ? 'RGA' : unified ? 'SidedEmbedRGA' : sided ? `sal-sided-${shared ? 'shared' : 'absolute'}-experimental`
      : (shared ? 'sal-shared-embed-rga' : 'sal-embed-rga'),
    version: 'runtime/ @ repo HEAD (unversioned)',
    create() { return { state: kernel.init(), view: [], clock: 0 }; },
    ins(doc, pos, ch) {
      doc.clock += 1;
      const id = doc.clock;
      const anchorId = pos > 0 ? doc.view[pos - 1] : null;
      doc.state = kernel.apply(doc.state, { type: 'ins', id, el: ch, anchorId });
      doc.view.splice(pos, 0, id);
    },
    del(doc, pos) {
      doc.clock += 1; // dense logical time, as in the litmus model
      const id = doc.view[pos];
      doc.state = kernel.apply(doc.state, { type: 'del', id });
      doc.view.splice(pos, 1);
    },
    text(doc) { return kernel.read(doc.state).join(''); },
    liveCount(doc) { return typeof kernel.liveCount === 'function' ? kernel.liveCount(doc.state)
      : sided ? doc.state.live.size : doc.state.size; },

    saveVariants(doc) {
      return [
        { label: plainRGA ? 'rga-binary' : sided ? 'sided-policy-binary' : (shared ? 'shared-runs-serialized' : 'run-table-serialized'), mk: () => save(doc.state),
          note: plainRGA ? 'continuation-capable packed insertion tree and tombstone set' : sided ? 'lossless binary parent-link snapshot including the Fugue policy summary' : (shared ? 'continuation-capable shared path graph with run-compressed provenance' : 'live state only; task #104 SHIPPED run-table binary (entry headers + positional records + packed text); lossless, decodes to the same read') },
      ];
    },
    load,
    compactedText(state) { return kernel.read(state).join(''); },
    saveCompacted(state) {
      return { label: shared ? 'shared-runs-serialized+compacted' : 'run-table-serialized+compacted',
        data: save(state), note: shared ? 'native shared-path continuation snapshot after direct guarded GC' : 'run-table binary over compacted state' };
    },

    /** Settled-cut compaction (single-writer or fully-synced states only).
     *  settledIds = every Lamport tick minted so far; insert ids are a
     *  subset, extra ids are never consulted. */
    compact: plainRGA || sided ? undefined : function compact(doc) {
      const settledIds = new Set();
      for (let i = 1; i <= doc.clock; i++) settledIds.add(i);
      const [res, ms] = timed(() =>
        compactState(doc.state, { settledIds }, { fuseSpines: true }));
      return {
        ms, stats: res.stats,
        compacted: { state: res.state, view: doc.view, clock: doc.clock },
      };
    },

    /** Two replicas under the shipped Runtime head-sync discipline. */
    pair() {
      const runtime = new Runtime(kernel);
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
          // Measure the separate-store protocol's real SHA identities, not the
          // shared harness's short local cN ids. Hash construction is outside
          // the timed merge but inside the payload accounting path.
          const gids = sharedContentGids(runtime.dag, kernel);
          const toB = sharedDelta(runtime.dag, aH, bH, gids);
          const toA = sharedDelta(runtime.dag, bH, aH, gids);
          const payloadBytes = wireBytes({ t: 'delta', c: toB }) + wireBytes({ t: 'delta', c: toA });
          const [, ms] = timed(() => rA.sync(rB));
          const [, gcMs] = timed(() => runtime.gc());
          p.gcMsTotal += gcMs;
          const lam = Math.max(p.lamA, p.lamB);
          p.lamA = lam; p.lamB = lam;
          const ids = kernel.readIds(rA.head.state);
          p.viewA = [...ids]; p.viewB = [...ids];
          return { ms, payloadBytes };
        },
        textA: () => kernel.read(rA.head.state).join(''),
        textB: () => kernel.read(rB.head.state).join(''),
        saveVariants() {
          const st = rA.head.state;
          return [
            { label: plainRGA ? 'rga-binary' : sided ? 'sided-policy-binary' : (shared ? 'shared-runs-serialized' : 'run-table-serialized'), mk: () => save(st),
              note: plainRGA ? 'packed insertion tree and tombstones' : sided ? 'lossless binary policy-state snapshot' : (shared ? 'native shared path graph (lossless)' : 'task #104 SHIPPED run-table binary (lossless)') },
          ];
        },
        compactFinal: plainRGA || sided ? undefined : function compactFinal() {
          const settledIds = new Set(p.minted);
          const [res, ms] = timed(() =>
            compactState(rA.head.state, { settledIds }, { fuseSpines: true }));
          const saved = save(res.state);
          return { ms, stats: res.stats, state: res.state,
            saves: [{ label: shared ? 'shared-runs-serialized+compacted' : 'run-table-serialized+compacted', bytes: saved.length }] };
        },
      };
      return p;
    },
  };
}
