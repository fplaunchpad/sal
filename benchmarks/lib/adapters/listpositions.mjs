// list-positions adapter (Text class: chars at CRDT positions). NOT a
// full CRDT library: it ships positions + local data structure; op
// delivery/merge is left to the app (its documented integration pattern).
// Save = the library's own JSON saved states (Text.save + Order.save),
// serialized with JSON.stringify. For the pair workload each side keeps an
// op log {pos, ch, meta?}/{pos}; sync = apply the other's new ops in
// order (addMetas first), payload measured as the JSON bytes of those ops.

import { Text, Order } from 'list-positions';
import { createRequire } from 'node:module';
import { timed } from '../bench.mjs';

const version = createRequire(import.meta.url)('list-positions/package.json').version;

export function mkAdapter() {
  return {
    name: 'list-positions',
    version,
    create() { return { text: new Text() }; },
    ins(d, pos, ch) { d.text.insertAt(pos, ch); },
    del(d, pos) { d.text.deleteAt(pos); },
    text(d) { return d.text.toString(); },

    saveVariants(d) {
      return [
        { label: 'json-text+order',
          mk: () => JSON.stringify({ order: d.text.order.save(), text: d.text.save() }),
          note: 'library-native JSON saved states (Order metadata + char runs)' },
      ];
    },
    load(data) {
      const { order, text } = JSON.parse(data);
      const t = new Text();
      t.order.load(order);
      t.load(text);
      return { text: t, len: t.length };
    },

    pair() {
      const a = new Text(), b = new Text();
      const logA = [], logB = [];
      let syncedA = 0, syncedB = 0; // how much of each log the OTHER has seen
      const localIns = (t, log, pos, ch) => {
        const [p, meta] = t.insertAt(pos, ch);
        log.push({ k: 'i', p, ch, meta: meta ?? null });
      };
      const localDel = (t, log, pos) => {
        const p = t.positionAt(pos);
        t.deleteAt(pos);
        log.push({ k: 'd', p });
      };
      const applyOps = (t, ops) => {
        for (const op of ops) {
          if (op.k === 'i') {
            if (op.meta) t.order.addMetas([op.meta]);
            t.set(op.p, op.ch);
          } else {
            t.delete(op.p);
          }
        }
      };
      const p = {
        insA: (pos, ch) => localIns(a, logA, pos, ch),
        delA: (pos) => localDel(a, logA, pos),
        insB: (pos, ch) => localIns(b, logB, pos, ch),
        delB: (pos) => localDel(b, logB, pos),
        lenA: () => a.length,
        lenB: () => b.length,
        sync() {
          const newA = logA.slice(syncedA), newB = logB.slice(syncedB);
          const payloadBytes =
            Buffer.byteLength(JSON.stringify(newA)) + Buffer.byteLength(JSON.stringify(newB));
          const [, ms] = timed(() => {
            applyOps(a, newB);
            applyOps(b, newA);
          });
          syncedA = logA.length; syncedB = logB.length;
          return { ms, payloadBytes };
        },
        textA: () => a.toString(),
        textB: () => b.toString(),
        saveVariants: () => [
          { label: 'json-text+order',
            mk: () => JSON.stringify({ order: a.order.save(), text: a.save() }) },
        ],
      };
      return p;
    },
  };
}
