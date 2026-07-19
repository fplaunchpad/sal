// Yjs adapter. Save = encodeStateAsUpdate (v1) and V2. Yjs's "state"
// serialization keeps tombstone STRUCTURE (deleted item ids/ranges) but
// drops deleted CONTENT; it cannot drop the tombstone structure. Sync =
// state-vector diff exchange, the library's intended protocol.

import * as Y from 'yjs';
import { createRequire } from 'node:module';
import { timed } from '../bench.mjs';

const version = createRequire(import.meta.url)('yjs/package.json').version;

export function mkAdapter() {
  return {
    name: 'yjs',
    version,
    create() {
      const doc = new Y.Doc();
      return { doc, text: doc.getText('text') };
    },
    ins(d, pos, ch) { d.text.insert(pos, ch); },
    del(d, pos) { d.text.delete(pos, 1); },
    text(d) { return d.text.toString(); },

    saveVariants(d) {
      return [
        { label: 'update-v1', mk: () => Y.encodeStateAsUpdate(d.doc),
          note: 'full update encoding v1 (state incl. tombstone structure, no deleted content)' },
        { label: 'update-v2', mk: () => Y.encodeStateAsUpdateV2(d.doc),
          note: 'v2 encoding (run-length compressed)' },
      ];
    },
    load(data) {
      const doc = new Y.Doc();
      Y.applyUpdate(doc, data);
      // force materialization of the text (render cost parity)
      const s = doc.getText('text').toString();
      return { doc, len: s.length };
    },

    pair() {
      const a = new Y.Doc(), b = new Y.Doc();
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
            const uB = Y.encodeStateAsUpdate(b.doc ?? b, Y.encodeStateVector(a));
            Y.applyUpdate(a, uB);
            const uA = Y.encodeStateAsUpdate(a, Y.encodeStateVector(b));
            Y.applyUpdate(b, uA);
            bytes = uA.length + uB.length;
          });
          return { ms, payloadBytes: bytes };
        },
        textA: () => ta.toString(),
        textB: () => tb.toString(),
        saveVariants: () => [
          { label: 'update-v1', mk: () => Y.encodeStateAsUpdate(a) },
          { label: 'update-v2', mk: () => Y.encodeStateAsUpdateV2(a) },
        ],
      };
      return p;
    },
  };
}
