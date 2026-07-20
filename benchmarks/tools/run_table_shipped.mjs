// Task #104 (SERIALIZER item): the SHIPPED run-table serializer measured on
// the sequential traces, next to the run-table PROJECTION it realizes.
//
// The save size is a pure function of the final state, which is deterministic,
// so we build the final state with a FAST mutable replay (avoiding the
// as-shipped datatype's O(live-set) Map copy per op that makes seq.mjs take
// minutes on the big traces) and serialize it with runtime/src/serialize.js.
// The state is byte-identical to what the seq.mjs harness builds: this tool's
// numbers were validated equal to a full seq.mjs run on friendsforever_flat
// (run-table-serialized 31457 B, +compacted 24126 B). The gates below re-derive
// the text from decode/read and confirm accountingBits reproduces
// results/projection.json (task #73's run_table_measure.py) bit-for-bit.
//
// Usage: node tools/run_table_shipped.mjs [trace ...]   -> results/run_table_shipped.json

import { writeFileSync, existsSync, readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';
import { loadTrace } from '../lib/traces.mjs';
import { embedRGA as D, eliasDeltaCode } from '../../runtime/src/datatypes/embedRGA.js';
import { compactEliasDelta } from '../../runtime/src/compact.js';
import { encode, decode, buildRunTable, accountingBits, tableWalk } from '../../runtime/src/serialize.js';

const enc = eliasDeltaCode.enc;
const HERE = dirname(fileURLToPath(import.meta.url));
const RESULTS = join(HERE, '..', 'results');
const TRACES = process.argv.slice(2).length
  ? process.argv.slice(2)
  : ['friendsforever_flat', 'clownschool_flat', 'seph-blog1', 'automerge-paper'];

/** Fast mutable sequential replay -> final state Map id -> {coord, el}. Same
 *  dense-Lamport id stream (deletes tick) as lib/adapters/sal.mjs, so the
 *  final state's coordinates are identical to the as-shipped adapter's. */
function buildState(doc) {
  const state = new Map(); const view = []; let clock = 0;
  for (const txn of doc.txns) for (const [pos, ndel, content] of txn.patches) {
    for (let k = 0; k < ndel; k++) { clock++; state.delete(view[pos]); view.splice(pos, 1); }
    for (let i = 0; i < content.length; i++) {
      clock++; const id = clock; const p = pos + i; const anchorId = p > 0 ? view[p - 1] : null;
      const coord = anchorId === null ? enc(id) : state.get(anchorId).coord + enc(id - anchorId);
      state.set(id, Object.freeze({ coord, el: content[i] })); view.splice(p, 0, id);
    }
  }
  return state;
}

const projection = existsSync(join(RESULTS, 'projection.json'))
  ? JSON.parse(readFileSync(join(RESULTS, 'projection.json'), 'utf8')) : null;

const out = {
  tool: 'run_table_shipped.mjs (task #104)',
  note: 'SHIPPED run-table serializer bytes (runtime/src/serialize.js) over the '
    + 'as-shipped final state and its settled-cut compaction; gates + projection '
    + 'cross-check. Save size is a function of the final state, built here by a '
    + 'fast mutable replay (identical to the seq.mjs harness state).',
  traces: {},
};

for (const name of TRACES) {
  const doc = loadTrace(name);
  const chars = doc.endContent.length;
  const state = buildState(doc);
  // settled cut = every Lamport tick minted (single-writer trace end), matching
  // lib/adapters/sal.mjs compact().
  let clock = 0;
  for (const txn of doc.txns) for (const [, ndel, content] of txn.patches) clock += ndel + content.length;
  const settledIds = new Set(); for (let i = 1; i <= clock; i++) settledIds.add(i);
  const { state: comp } = compactEliasDelta(state, { settledIds }, { fuseSpines: true });

  const tRaw = buildRunTable(state), aRaw = accountingBits(tRaw);
  const tCmp = buildRunTable(comp), aCmp = accountingBits(tCmp);
  const bRaw = encode(state), bCmp = encode(comp);

  // gates
  const readOk = D.read(state).join('') === doc.endContent;
  const walkRawOk = tableWalk(tRaw).join('') === doc.endContent;
  const walkCmpOk = tableWalk(tCmp).join('') === doc.endContent;
  const rtRawOk = D.read(decode(bRaw)).join('') === doc.endContent;
  const rtCmpOk = D.read(decode(bCmp)).join('') === doc.endContent;
  const compTextOk = D.read(comp).join('') === doc.endContent;

  // projection cross-check: accountingBits == run_table_measure.py, bit-for-bit
  const pj = projection?.traces?.[name]?.bits ?? null;
  const projMatchRaw = pj ? aRaw.total === pj.run_table_raw : null;
  const projMatchCmp = pj ? aCmp.total === pj.run_table_composed : null;

  // reconciliation: the shipped metadata bit count == model total minus the
  // recoverable positional fields (rec_id, rec_off, hdr_poff).
  const reconRaw = bRaw.metaBits === aRaw.total - aRaw.rec_id - aRaw.rec_off - aRaw.hdr_poff;
  const reconCmp = bCmp.metaBits === aCmp.total - aCmp.rec_id - aCmp.rec_off - aCmp.hdr_poff;

  out.traces[name] = {
    chars,
    shipped_bytes: { raw: bRaw.length, compacted: bCmp.length },
    shipped_bytes_per_char: { raw: bRaw.length / chars, compacted: bCmp.length / chars },
    model_bits: { raw: aRaw.total, composed: aCmp.total },
    projection_save_bytes: {
      raw: Math.ceil(aRaw.total / 8) + chars,
      composed: Math.ceil(aCmp.total / 8) + chars,
    },
    entries: { raw: aRaw.n_ent, composed: aCmp.n_ent },
    reconciliation: {
      recoverable_bits_raw: aRaw.rec_id + aRaw.rec_off + aRaw.hdr_poff,
      recoverable_bits_composed: aCmp.rec_id + aCmp.rec_off + aCmp.hdr_poff,
      shipped_meta_bits_raw: bRaw.metaBits,
      shipped_meta_bits_composed: bCmp.metaBits,
      identity_holds: reconRaw && reconCmp,
    },
    projection_match: { raw: projMatchRaw, composed: projMatchCmp },
    gates: { readOk, walkRawOk, walkCmpOk, roundTripRawOk: rtRawOk, roundTripCmpOk: rtCmpOk, compTextOk },
  };

  const g = out.traces[name].gates;
  const allGates = readOk && walkRawOk && walkCmpOk && rtRawOk && rtCmpOk && compTextOk && reconRaw && reconCmp;
  console.log(`${name}: chars=${chars} shipped raw=${bRaw.length}B (${(bRaw.length / chars).toFixed(2)} B/ch) `
    + `compacted=${bCmp.length}B (${(bCmp.length / chars).toFixed(2)} B/ch); `
    + `projection composed=${out.traces[name].projection_save_bytes.composed}B; `
    + `projMatch raw=${projMatchRaw} composed=${projMatchCmp}; gates=${allGates ? 'ALL PASS' : 'FAIL ' + JSON.stringify(g)}`);
}

const dst = join(RESULTS, 'run_table_shipped.json');
writeFileSync(dst, JSON.stringify(out, null, 1));
console.log('\nwrote', dst.replace(join(HERE, '..') + '/', ''));
