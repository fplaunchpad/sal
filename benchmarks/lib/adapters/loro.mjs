// Loro adapter (loro-crdt 1.x, wasm-backed). Saves: 'snapshot' (state +
// full op history) and 'shallow-snapshot' at the current frontiers (state,
// history truncated at the frontier: Loro's history-dropping mode). Sync =
// version-vector-delta update exchange.

import { LoroDoc } from 'loro-crdt';
import { createRequire } from 'node:module';
import { timed } from '../bench.mjs';

const version = createRequire(import.meta.url)('loro-crdt/package.json').version;

export function mkAdapter() {
  return {
    name: 'loro',
    version,
    create() {
      const doc = new LoroDoc();
      doc.setPeerId(1n);
      return { doc, text: doc.getText('text') };
    },
    ins(d, pos, ch) { d.text.insert(pos, ch); },
    del(d, pos) { d.text.delete(pos, 1); },
    text(d) { return d.text.toString(); },

    saveVariants(d) {
      d.doc.commit();
      return [
        { label: 'snapshot', mk: () => d.doc.export({ mode: 'snapshot' }),
          note: 'state + full history' },
        { label: 'shallow-snapshot',
          mk: () => d.doc.export({ mode: 'shallow-snapshot', frontiers: d.doc.frontiers() }),
          note: 'state with history dropped at current frontiers' },
      ];
    },
    load(data) {
      const doc = new LoroDoc();
      doc.import(data);
      const s = doc.getText('text').toString();
      return { doc, len: s.length };
    },

    pair() {
      const a = new LoroDoc(); a.setPeerId(1n);
      const b = new LoroDoc(); b.setPeerId(2n);
      const ta = a.getText('text'), tb = b.getText('text');
      const p = {
        insA: (pos, ch) => ta.insert(pos, ch),
        delA: (pos) => ta.delete(pos, 1),
        insB: (pos, ch) => tb.insert(pos, ch),
        delB: (pos) => tb.delete(pos, 1),
        lenA: () => ta.length,
        lenB: () => tb.length,
        sync() {
          let bytes = 0;
          const [, ms] = timed(() => {
            a.commit(); b.commit();
            const uB = b.export({ mode: 'update', from: a.version() });
            a.import(uB);
            const uA = a.export({ mode: 'update', from: b.version() });
            b.import(uA);
            bytes = uA.length + uB.length;
          });
          return { ms, payloadBytes: bytes };
        },
        textA: () => ta.toString(),
        textB: () => tb.toString(),
        saveVariants: () => {
          a.commit();
          return [
            { label: 'snapshot', mk: () => a.export({ mode: 'snapshot' }) },
            { label: 'shallow-snapshot',
              mk: () => a.export({ mode: 'shallow-snapshot', frontiers: a.frontiers() }) },
          ];
        },
      };
      return p;
    },
  };
}
