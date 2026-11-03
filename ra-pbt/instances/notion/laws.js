/**
 * A Notion block-editor model as a state-based datatype for the law layer.
 *
 * The model's replicated state is its transaction archive: `Replica.receive`
 * adds a whole transaction to a map, and a document is rebuilt from the
 * archive by sorting it and replaying every transaction. So
 *
 *   state       an archive: the seed transactions and a set of issued
 *               transactions, as an array sorted by key
 *   apply       adds the event's transaction
 *   merge3      the union of the two branches (the lowest common ancestor is
 *               not needed)
 *   read        the display of the document the model builds from the
 *               archive (block texts, and with `format` bold flags), in the
 *               specification's view format; a model exception is BOTTOM
 *
 * Events are issued honestly: the issuer is a model `Replica` holding
 * can(E) for its event set E, with session the law layer's replica name, and
 * the event is the transaction of a positional request on its display
 * (requests.js). The event also carries the specification operation of
 * spec.js.
 *
 * rc is empty: adding transactions to a set commutes, so the union carrier
 * relates no pair. Commutativity is declared false for every pair so that
 * lo_E is the visibility order and the conformance witness is a causal
 * linearization; with the paper's default (no rc, so every pair commutes)
 * lo_E would be empty and conformance would also admit non-causal orders.
 * The witness search tries events in replay order first (counter, then
 * session), the order in which the model rebuilds documents.
 *
 * Observation. `observation: 'view'` (default) observes the display;
 * `observation: 'bag'` observes only the sorted multiset of visible
 * characters, so sequential conformance then fails exactly when no causal
 * linearization explains the visible characters: text lost or duplicated, or
 * a history the specification gives no meaning.
 */
import { specFor, textsOf, blocksOf } from './spec.js';
import { nextRequest } from './requests.js';
import { issueOn, viewOf, seedTransactions } from './adapter.js';
import { decodeTx } from './spec.js';

const txKey = (tx) => `${tx.id.sessionId}:${tx.id.counter}`;
const byKey = (a, b) => (a.key < b.key ? -1 : a.key > b.key ? 1 : 0);

/** The datatype and law instance of a model over a seed document given as block texts. */
export function lawsFor(model, { texts, format = false, profile, observation = 'view', replicas = 3, syncProbability = 0.3, maxBlocks = 6 }) {
  const seed = seedTransactions(model, texts).map((tx) => ({ key: txKey(tx), tx }));
  const spec = specFor({ seedTransactions: seed.map((e) => e.tx), format });
  const observe =
    observation === 'bag'
      ? (v) => textsOf(v).join('').split('').sort().join('')
      : (v) => (format ? blocksOf(v).map((cs) => cs.map((c) => [c.text, c.bold])) : textsOf(v));
  const replicaOf = (session, state) => new model.Replica(session, session, state.map((e) => e.tx));
  const datatype = {
    name: `notion-${model.variant}-${profile ?? (format ? 'format' : 'text')}-${observation}`,
    init: () => seed,
    apply(s, op) {
      if (s.some((e) => e.key === op.key)) return s;
      return [...s, { key: op.key, tx: op.tx }].sort(byKey);
    },
    merge3(_l, a, b) {
      const out = new Map(a.map((e) => [e.key, e]));
      for (const e of b) out.set(e.key, e);
      return [...out.values()].sort(byKey);
    },
    read(s) {
      const d = new model.CrdtDocument(s.map((e) => e.tx));
      return observe(d.aliveBlocks().map((b) => ({ id: b.id, chars: d.blockCharacters(b.id).map((c) => ({ text: c.text, bold: !!c.bold })) })));
    },
    serialise: (s) => s.map((e) => e.key).join(','),
  };
  const rndOf = (rnd) => ({ next: rnd, int: (lo, hi) => lo + Math.floor(rnd() * (hi - lo + 1)), pick: (xs) => xs[Math.floor(rnd() * xs.length)] });
  const instance = {
    name: datatype.name,
    replicas,
    syncProbability,
    genEvent(rnd, state, ctx) {
      const rep = replicaOf(ctx.replica.toUpperCase(), state);
      let view;
      try {
        view = viewOf(rep);
      } catch {
        return null;
      }
      const q = nextRequest(rndOf(rnd), view, { format, profile, maxBlocks });
      if (!q) return null;
      let res;
      try {
        res = issueOn(rep, q);
      } catch {
        return null;
      }
      if (res.txs.length !== 1) return null;
      const tx = res.txs[0];
      const commands = decodeTx(tx);
      if (res.bold) commands.push(res.bold);
      return { key: txKey(tx), request: q, tx, commands };
    },
    label: (op) => `${op.request.kind}@${op.key}`,
    commutes: () => false,
    spec: {
      init: () => spec.init(),
      step(phi, op) {
        const next = spec.apply(phi, op);
        return next === null ? undefined : next;
      },
      observe: (phi) => observe(spec.view(phi)),
    },
    observe: (s) => datatype.read(s),
    witnessOrder: (a, b) => a.op.tx.id.counter - b.op.tx.id.counter || (a.op.tx.id.sessionId < b.op.tx.id.sessionId ? -1 : 1),
  };
  return { datatype, instance, seed };
}
