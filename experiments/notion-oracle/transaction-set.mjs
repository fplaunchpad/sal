// Research adapter, not a second implementation of the demo document semantics.
// State contains immutable, uniquely identified transactions. Issuance delegates
// to the pinned client; observation delegates to the pinned document interpreter.
import {Replica} from './replica.js';
const clone = value => JSON.parse(JSON.stringify(value));
const key = tx => JSON.stringify([tx.id.sessionId, tx.id.counter]);
export class TransactionSet {
  constructor(transactions = []) {
    this.byId = new Map();
    for (const tx of transactions) {
      const prior = this.byId.get(key(tx));
      if (prior && JSON.stringify(prior) !== JSON.stringify(tx)) throw Error('conflicting transaction identity');
      this.byId.set(key(tx), clone(tx));
    }
  }
  transactions() { return [...this.byId.values()].map(clone); }
  replica(session = 'observer') { return new Replica(session, session, this.transactions()); }
  issue(session, method, ...args) {
    const replica = this.replica(session);
    const result = replica[method](...args);
    return {state: new TransactionSet(replica.transactions()), result};
  }
  static merge(base, left, right) {
    for (const branch of [left, right]) for (const tx of base.transactions()) {
      if (JSON.stringify(branch.byId.get(key(tx))) !== JSON.stringify(tx)) throw Error('base must be a payload-preserving subset');
    }
    return new TransactionSet([...base.transactions(), ...left.transactions(), ...right.transactions()]);
  }
}
