// RA check: fold the identity specification over an archive in replay order
// and compare its view with a replica's rendered display. Imports no demo code;
// `installHook` receives the replica class from its caller (ra-hook.mjs).
import {createHash} from 'node:crypto';
import {fold, replayOrder} from './identity-spec.mjs';

const bag = view => view.map(([, text]) => [...text]).flat().sort().join('');
// Distinct histories can reuse transaction identifiers (a probe session issues
// different requests on the same base), so archives are keyed by content.
const archiveKey = txs => createHash('sha256').update(JSON.stringify(replayOrder(txs))).digest('hex');
// A block is identified by its creating transaction, for the same reason.
const blockKeys = txs => {
  const out = new Map();
  for (const t of txs) for (const o of t.operations)
    if (o.command === 'createBlock') out.set(o.args.blockId, createHash('sha256').update(JSON.stringify(t)).digest('hex').slice(0, 16));
  return out;
};

// The specification (absorb), the earlier merge meaning (skip: a no-op unless
// the target itself is alive), the reading in which a merged source leaves the
// block list instead of staying as a tombstone (removed), and the meaning of
// the demo's targeting (sliceFollow: append at the end of the block holding
// the recorded anchor; sliceFollowAnchor: insert right after the anchor; see
// identity-spec.mjs).
export const MODES = {absorb: {}, skip: {merge: 'skip'}, removed: {removeMergedSource: true},
  sliceFollow: {merge: 'sliceFollow'}, sliceFollowAnchor: {merge: 'sliceFollow', placement: 'anchor'}};

// Outcome categories: agree; stuck (the specification gives the archive no
// meaning); conservation (visible character multisets differ, H2); placement
// (same characters, different blocks or order, H1 only).
export function compare(transactions, display, options = {}, Spec) {
  const folded = fold(transactions, options, Spec);
  if (folded.stuck) return {category: 'stuck', stuck: folded.stuck, display};
  const spec = folded.view;
  if (JSON.stringify(spec) === JSON.stringify(display)) return {category: 'agree'};
  return {category: bag(spec) === bag(display) ? 'placement' : 'conservation', spec, display};
}

export const displayOf = document => document.aliveBlocks().map(b => [b.id, document.blockText(b.id)]);

const emptyCounts = () => ({agree: 0, stuck: 0, conservation: 0, placement: 0});

// Every distinct archive whose document is built is checked once in each mode.
// The hook also records, across all archives of the run, whether two alive
// blocks (identified by their creating transactions) are ever displayed in
// opposite orders (an order inversion).
export function installHook(Replica, {keepFailures = 3, keepTransactions = 40} = {}) {
  const state = {archives: 0, documentCalls: 0, replayExceptions: 0, replayExceptionMessages: {},
    modes: Object.fromEntries(Object.keys(MODES).map(m => [m, emptyCounts()])),
    failures: Object.fromEntries(Object.keys(MODES).map(m => [m, {}])),
    orderInversions: 0, orderInversionExample: null, pairOrder: new Map(),
    seen: new Set(), listeners: [], archiveListeners: []};
  const original = Replica.prototype.document;
  Replica.prototype.document = function () {
    state.documentCalls++;
    let document;
    try { document = original.call(this); }
    catch (e) {
      state.replayExceptions++;
      state.replayExceptionMessages[e.message] = (state.replayExceptionMessages[e.message] ?? 0) + 1;
      throw e;
    }
    const txs = this.transactions(), k = archiveKey(txs);
    if (state.seen.has(k)) return document;
    state.seen.add(k); state.archives++;
    for (const f of state.archiveListeners) f(txs, document);
    const display = displayOf(document), names = blockKeys(txs), ids = display.map(([id]) => id + '#' + names.get(id));
    for (let i = 0; i < ids.length; i++) for (let j = i + 1; j < ids.length; j++) {
      const [x, y] = ids[i] < ids[j] ? [ids[i], ids[j]] : [ids[j], ids[i]], sign = ids[i] === x ? 1 : -1;
      const prior = state.pairOrder.get(x + '|' + y);
      if (prior === undefined) state.pairOrder.set(x + '|' + y, sign);
      else if (prior !== sign) {
        state.orderInversions++;
        state.orderInversionExample ??= {pair: [x, y], display, transactions: structuredClone(txs)};
      }
    }
    for (const [mode, options] of Object.entries(MODES)) {
      const r = compare(txs, display, options);
      state.modes[mode][r.category]++;
      if (r.category === 'agree') continue;
      const list = state.failures[mode][r.category] ??= [];
      // Keep the smallest archives seen; they are the cheapest to read.
      list.push({size: txs.length, result: r, transactions: txs.length <= keepTransactions ? structuredClone(txs) : null});
      list.sort((a, b) => a.size - b.size);
      if (list.length > keepFailures) list.length = keepFailures;
      for (const f of state.listeners) f(mode, r, txs);
    }
    return document;
  };
  return state;
}

export function summary(state) {
  const {seen, pairOrder, listeners, archiveListeners, ...rest} = state;
  return rest;
}
