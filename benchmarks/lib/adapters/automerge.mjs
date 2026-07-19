// Automerge adapter (@automerge/automerge 3.x, wasm-backed). Save =
// Automerge.save: the FULL CHANGE HISTORY (compressed columnar); Automerge
// has no history-dropping state serialization -- that is the point of the
// churn workload's growth-on-delete cell. One change per char (the
// automerge-perf convention). Merge = Automerge.merge.

import * as Am from '@automerge/automerge';
import { createRequire } from 'node:module';
import { timed } from '../bench.mjs';

const require_ = createRequire(import.meta.url);
const version = require_(
  require_.resolve('@automerge/automerge').replace(/dist\/.*$/, 'package.json')
).version;

export function mkAdapter() {
  return {
    name: 'automerge',
    version,
    create() { return { doc: Am.from({ text: '' }) }; },
    ins(d, pos, ch) {
      d.doc = Am.change(d.doc, (m) => Am.splice(m, ['text'], pos, 0, ch));
    },
    del(d, pos) {
      d.doc = Am.change(d.doc, (m) => Am.splice(m, ['text'], pos, 1));
    },
    text(d) { return d.doc.text; },

    saveVariants(d) {
      return [
        { label: 'save-full-history', mk: () => Am.save(d.doc),
          note: 'full compressed change history; no state-only mode exists' },
      ];
    },
    load(data) {
      const doc = Am.load(data);
      return { doc, len: doc.text.length };
    },

    pair() {
      const base = Am.from({ text: '' });
      const p = {
        a: { doc: base },
        b: { doc: Am.clone(base) },
        insA(pos, ch) { p.a.doc = Am.change(p.a.doc, (m) => Am.splice(m, ['text'], pos, 0, ch)); },
        delA(pos) { p.a.doc = Am.change(p.a.doc, (m) => Am.splice(m, ['text'], pos, 1)); },
        insB(pos, ch) { p.b.doc = Am.change(p.b.doc, (m) => Am.splice(m, ['text'], pos, 0, ch)); },
        delB(pos) { p.b.doc = Am.change(p.b.doc, (m) => Am.splice(m, ['text'], pos, 1)); },
        lenA: () => p.a.doc.text.length,
        lenB: () => p.b.doc.text.length,
        sync() {
          const [, ms] = timed(() => {
            p.a.doc = Am.merge(p.a.doc, p.b.doc);
            p.b.doc = Am.merge(p.b.doc, p.a.doc);
          });
          return { ms, payloadBytes: null }; // in-process merge; wire cost not modeled
        },
        textA: () => p.a.doc.text,
        textB: () => p.b.doc.text,
        saveVariants: () => [
          { label: 'save-full-history', mk: () => Am.save(p.a.doc) },
        ],
      };
      return p;
    },
  };
}
