/**
 * ra-pbt adapter over replicas of a Notion block-editor model.
 *
 * Replicas. Replica r is the model's `Replica` with session `sessions[r - 1]`
 * (default `A`, `B`, ...), constructed holding the seed transactions. A fork
 * of the determinism check (id 1000 + r) has session `F<id>`. Sessions
 * matter: concurrent identifiers are ordered by counter, then session.
 *
 * Records. Every valid request emits exactly one transaction. A record's
 * update is `{ tx, prior }`: the transaction and the keys of every
 * transaction the issuer held, which are its causal predecessors.
 *
 * Delivery. `deliver` holds a record until all its predecessors are held
 * (the demo itself does not buffer), then the replica receives the whole
 * transaction. `sync(to, from)` gives `to` every transaction `from` holds and
 * hands on the records `from` is holding. A record is integrated when its
 * transaction is held. An opened replica is constructed from the source's
 * transactions, as `new Replica(session, name, transactions)` does.
 *
 * Specification operations. One per record: `{ tx, commands }`, the decoded
 * command group of the transaction, plus for a bold request the `bold`
 * command of the issuer's selection (see spec.js).
 *
 * Element accounting. Characters are keyed by specification address and
 * labelled `text@address`. The seed's characters are reported as inserted by
 * every record, so the expected final set is seed and insertions minus
 * deletions; a schedule without records has no expected set.
 *
 * A request the model throws on while issuing is reported as a RangeError
 * (the step is dropped) and counted in `adapterStats.rejected`.
 */
import { decodeTx, addressOf, blocksOf } from './spec.js';
import { validOn } from './requests.js';

export const DEFAULT_SESSIONS = ['A', 'B', 'C', 'D', 'E', 'F'];
export const adapterStats = { rejected: 0, rejections: [] };

const txKey = (tx) => `${tx.id.sessionId}:${tx.id.counter}`;

/** Seed transactions for a document given as block texts. */
export function seedTransactions(model, texts) {
  const r = new model.Replica('seed', 'seed', []);
  let previous;
  for (const t of texts) {
    previous = r.createBlock(previous).newBlockId;
    r.insertText(previous, 0, t);
  }
  return r.transactions();
}

/** The displayed view of a model replica: alive blocks with characters and bold flags. */
export function viewOf(rep) {
  const d = rep.document();
  return d.aliveBlocks().map((b) => ({ id: b.id, chars: d.blockCharacters(b.id).map((c) => ({ text: c.text, bold: !!c.bold })) }));
}

/** Labels of the visible characters of a model replica. */
export function presentOf(rep) {
  const d = rep.document();
  return d.aliveBlocks().flatMap((b) => d.blockCharacters(b.id).map((c) => `${c.text}@${addressOf(c.textInstanceId, c.item.id)}`));
}

function insertedOf(tx) {
  const out = [];
  for (const op of tx.operations)
    if (op.command === 'insertText') {
      const a = op.args;
      [...a.content].forEach((ch, i) => {
        const addr = addressOf(a.textInstanceId, { sessionId: a.id.sessionId, counter: a.id.counter + i });
        out.push([addr, `${ch}@${addr}`]);
      });
    }
  return out;
}

function deletedOf(tx) {
  const out = [];
  for (const op of tx.operations)
    if (op.command === 'deleteText')
      for (const [first, n] of op.args.idRanges)
        for (let i = 0; i < n; i++) out.push(addressOf(op.args.textInstanceId, { sessionId: first.sessionId, counter: first.counter + i }));
  return out;
}

/** Issues a positional request on a model replica; returns the new transactions. */
export function issueOn(rep, q) {
  const view = viewOf(rep);
  if (!validOn(view, q)) throw new RangeError(`invalid request ${JSON.stringify(q)}`);
  const id = view[q.block].id;
  const before = new Set(rep.transactions().map(txKey));
  const bold = q.kind === 'bold' ? boldCommand(rep, id, q) : null;
  if (q.kind === 'insert') rep.insertText(id, q.index, q.text);
  else if (q.kind === 'delete') rep.deleteText(id, q.start, q.end);
  else if (q.kind === 'split') rep.splitBlock(id, q.index);
  else if (q.kind === 'merge') rep.mergeBlock(id);
  else if (q.kind === 'bold') rep.toggleBold(id, q.start, q.end);
  return { view, blockId: id, before, bold, txs: rep.transactions().filter((t) => !before.has(txKey(t))) };
}

/** The bold command of a toggle request, from the issuer's view before issuing. */
export function boldCommand(rep, blockId, q) {
  const selected = rep.document().blockCharacters(blockId).slice(q.start, q.end);
  return { kind: 'bold', addresses: selected.map((c) => addressOf(c.textInstanceId, c.item.id)), value: !selected.every((c) => c.bold) };
}

export function makeAdapter(model, { seed, sessions = DEFAULT_SESSIONS }) {
  const sessionOf = (id) => (id >= 1000 ? `F${id}` : sessions[id - 1] ?? `R${id}`);
  const seedInserted = seed.flatMap(insertedOf);
  const fresh = (id) => ({ id, session: sessionOf(id), rep: new model.Replica(sessionOf(id), sessionOf(id), seed), held: new Map() });
  const holds = (x, key) => x.rep.transactionMap.has(key);

  const drain = (x) => {
    let progress = true;
    while (progress) {
      progress = false;
      for (const [key, rec] of x.held) {
        if (holds(x, key)) x.held.delete(key);
        else if (rec.update.prior.every((k) => holds(x, k))) {
          x.rep.receive(rec.update.tx);
          x.held.delete(key);
        } else continue;
        progress = true;
      }
    }
  };
  const take = (x, rec) => {
    const key = rec.update.key;
    if (!holds(x, key) && !x.held.has(key)) x.held.set(key, rec);
    drain(x);
  };

  return {
    createReplica: (id) => fresh(id),
    loadInto(x, source) {
      x.rep = new model.Replica(x.session, x.session, source.rep.transactions());
    },
    validRequest: (x, q) => validOn(viewOf(x.rep), q),
    issue(x, q) {
      let res;
      try {
        res = issueOn(x.rep, q);
      } catch (e) {
        if (e instanceof RangeError) throw e;
        adapterStats.rejected++;
        if (adapterStats.rejections.length < 20) adapterStats.rejections.push({ request: q, message: e.message });
        throw new RangeError(`the model rejected ${JSON.stringify(q)}: ${e.message}`);
      }
      if (res.txs.length !== 1) throw new Error(`request ${JSON.stringify(q)} emitted ${res.txs.length} transactions`);
      const tx = res.txs[0];
      const commands = decodeTx(tx);
      if (res.bold) commands.push(res.bold);
      return {
        replica: x.id,
        kind: q.kind,
        request: q,
        update: { key: txKey(tx), tx, prior: [...res.before].sort() },
        specOps: [{ tx: txKey(tx), commands }],
      };
    },
    deliver(x, rec) {
      take(x, rec);
      return { pending: x.held.size > 0, emitted: [] };
    },
    sync(to, from) {
      for (const tx of from.rep.transactions()) if (!holds(to, txKey(tx))) to.rep.receive(tx);
      for (const rec of from.held.values()) take(to, rec);
      drain(to);
      return { pending: to.held.size > 0, emitted: [] };
    },
    view: (x) => viewOf(x.rep),
    stateVector: (x) => ({ transactions: [...x.rep.transactionMap.keys()].sort() }),
    integrated: (x, records) => new Set(records.filter((r) => holds(x, r.update.key)).map((r) => r.key)),
    hasPending: (x) => x.held.size > 0,
    inserted: (rec) => [...seedInserted, ...insertedOf(rec.update.tx)],
    deleted: (rec) => deletedOf(rec.update.tx),
    present: (x) => presentOf(x.rep),
    traceRecord: (rec) => ({ tx: rec.update.key, commands: rec.specOps[0].commands.map((c) => c.kind) }),
  };
}

export { blocksOf };
